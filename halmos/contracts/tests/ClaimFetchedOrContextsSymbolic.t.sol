// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../Assertions.sol";
import {ClaimResolveGetHost} from "./ClaimResolveGetExtensionsSymbolic.t.sol";

/**
 * @notice Finite fetched OR/type combinations. Structural prevalidation and
 *         selected leaf evaluation have separate expected outcomes. Original
 *         OR bytes are retained in full failure oracles. These cases do not
 *         establish arbitrary OR/list lengths or nesting/resource guarantees.
 */
contract ClaimFetchedOrContextsSymbolicTest is Test {
    struct OrCase {
        bytes32 value;
        bytes32 firstRef;
        bytes32 lower;
        bytes32 upper;
        uint8 family;
        uint8 route;
        uint8 paramType;
        uint8 entry;
        bool late;
        bool extra;
    }

    Assertions core;
    ClaimResolveGetHost host;

    function setUp() public {
        core = new Assertions();
        host = new ClaimResolveGetHost();
    }

    function check_fetchedFlatOrVerdicts(OrCase memory x) public {
        assumeCase(x);
        vm.warp(1000);
        (InputParam memory p, bytes memory value) = fetched(x);
        Constraint[] memory alternatives = new Constraint[](2);
        alternatives[0] = Constraint(ConstraintType.EQ, abi.encode(x.firstRef));
        alternatives[1] = leaf(x.family, x.lower, x.upper);
        Constraint memory c = Constraint(ConstraintType.OR, abi.encode(alternatives));
        // solc's OR-array decoder accepts a trailing byte. Retaining it in
        // ConstraintFailed distinguishes the original wire reference from a
        // newly encoded copy of the decoded alternatives.
        if (x.extra) {
            c.referenceData = bytes.concat(c.referenceData, hex"7f");
        }
        attach(p, c, x.late);
        (bool leafHolds, bool badRange) = verdict(x.value, x.lower, x.upper, alternatives[1].constraintType);
        bool early = x.value == x.firstRef;
        bool succeeds = early || (leafHolds && !badRange);
        (bool ok, bytes memory out) = judge(p, x.entry);
        assertEq(ok, succeeds);
        bytes memory expected = early || !badRange
            ? succeeds ? successResult(value, x.entry) : failed(x, c)
            : abi.encodeWithSelector(InvalidConstraintRange.selector, uint256(0), uint256(0), outerIndex(x));
        assertEq(out, expected);
        assertEq(host.count(), x.route == 1 ? 0 : 1);
    }

    function check_fetchedFlatOrErrorPriority(OrCase memory x, uint8 shape, uint8 size, bool early) public {
        assumeCase(x);
        vm.assume(shape < 3 && size < 8);
        // Empty/nested shapes have no second scalar kind or arbitrary size.
        vm.assume(shape == 2 || (x.family == 0 && (shape == 0 ? size == 0 : size < 2)));
        vm.warp(1000);
        (InputParam memory p, bytes memory value) = fetched(x);
        Constraint[] memory alternatives = new Constraint[](shape == 0 ? 0 : 2);
        uint256 length;
        if (shape != 0) {
            alternatives[0] = Constraint(ConstraintType.EQ, abi.encode(early ? x.value : x.value ^ bytes32(uint256(1))));
            if (shape == 1) {
                if (size == 1) {
                    alternatives[0].referenceData = prefix(abi.encode(x.value), 31);
                }
                alternatives[1] = Constraint(ConstraintType.OR, abi.encode(new Constraint[](0)));
            } else {
                alternatives[1] = leaf(x.family, x.lower, x.upper);
                length = byteLength(size);
                uint256 canonical = alternatives[1].constraintType == ConstraintType.SKIP
                    ? 0
                    : alternatives[1].constraintType == ConstraintType.IN
                        || alternatives[1].constraintType == ConstraintType.IN_SIGNED
                        ? 64
                        : 32;
                vm.assume(length != canonical);
                alternatives[1].referenceData = prefix(bytes.concat(abi.encode(x.lower, x.upper), hex"7f"), length);
            }
        }
        Constraint memory c = Constraint(ConstraintType.OR, abi.encode(alternatives));
        attach(p, c, x.late);
        (bool ok, bytes memory out) = judge(p, x.entry);
        bool succeeds = shape == 2 && early;
        assertEq(ok, succeeds);
        bytes memory expected =
            shape < 2 ? invalidStructure(x) : succeeds ? successResult(value, x.entry) : invalidReference(x, length);
        assertEq(out, expected);
        assertEq(host.count(), x.route == 1 ? 0 : 1);
    }

    function check_fetchedOrStructureAfterWordBounds(OrCase memory x, uint8 size, bool nested) public {
        vm.assume(x.route < 3 && x.paramType < 3 && x.entry < 3 && size < 5);
        vm.assume(!x.late && !x.extra);
        vm.warp(1000);
        (InputParam memory p, bytes memory value) = fetched(x);
        uint256 length = size == 0 ? 0 : size == 1 ? 1 : size == 2 ? 31 : size == 3 ? 32 : 33;
        if (x.route == 0) {
            value = prefix(bytes.concat(value, hex"7f"), length);
            p.paramData = abi.encode(address(host), abi.encodeCall(ClaimResolveGetHost.reply, (value, address(core))));
        } else {
            vm.assume(size == 3);
            length = 32;
        }
        Constraint[] memory alternatives = new Constraint[](nested ? 2 : 0);
        if (nested) {
            alternatives[0] = Constraint(ConstraintType.EQ, abi.encode(x.value));
            alternatives[1] = Constraint(ConstraintType.OR, abi.encode(new Constraint[](0)));
        }
        p.constraints = new Constraint[](length < 32 ? 1 : 2);
        p.constraints[0] = Constraint(ConstraintType.OR, abi.encode(alternatives));
        if (length >= 32) {
            p.constraints[1] = Constraint(ConstraintType.SKIP, "");
        }
        (bool ok, bytes memory out) = judge(p, x.entry);
        assertFalse(ok);
        assertEq(out, abi.encodeWithSelector(ReturnDataOutOfBounds.selector, int256(length / 32), length));
        assertEq(host.count(), x.route == 1 ? 0 : 1);
    }

    function test_fetchedFlatOrVerdictSamples() public {
        fixtureGuards();
        vm.expectCall(address(host), abi.encodePacked(ClaimResolveGetHost.reply.selector), uint64(288));
        vm.expectCall(address(host), abi.encodePacked(ClaimResolveGetHost.balanceOf.selector), uint64(72));
        OrCase memory x = sample();
        for (uint8 kind; kind < 8; kind++) {
            x.family = kind;
            for (uint8 route; route < 3; route++) {
                x.route = route;
                for (uint8 paramType; paramType < 3; paramType++) {
                    x.paramType = paramType;
                    for (uint8 entry; entry < 3; entry++) {
                        x.entry = entry;
                        check_fetchedFlatOrVerdicts(x);
                    }
                }
            }
        }
        x.route = 0;
        for (uint8 flags; flags < 3; flags++) {
            x.late = flags != 0;
            x.extra = flags == 2;
            for (uint8 kind; kind < 8; kind++) {
                x.family = kind;
                for (uint8 paramType; paramType < 3; paramType++) {
                    x.paramType = paramType;
                    for (uint8 entry; entry < 3; entry++) {
                        x.entry = entry;
                        check_fetchedFlatOrVerdicts(x);
                    }
                }
            }
        }
    }

    function test_fetchedFlatOrErrorSamples() public {
        fixtureGuards();
        vm.expectCall(address(host), abi.encodePacked(ClaimResolveGetHost.reply.selector), uint64(171));
        vm.expectCall(address(host), abi.encodePacked(ClaimResolveGetHost.balanceOf.selector), uint64(63));
        OrCase memory x = sample();
        x.family = 0;
        for (uint8 route; route < 3; route++) {
            x.route = route;
            for (uint8 paramType; paramType < 3; paramType++) {
                x.paramType = paramType;
                check_fetchedFlatOrErrorPriority(x, 0, 0, true);
                check_fetchedFlatOrErrorPriority(x, 1, 1, true);
                check_fetchedFlatOrErrorPriority(x, 2, 4, false);
            }
        }
        for (uint8 route; route < 3; route++) {
            x.route = route;
            for (uint8 paramType; paramType < 3; paramType++) {
                x.paramType = paramType;
                for (uint8 size; size < 8; size++) {
                    x.family = size == 3 ? 3 : 0;
                    check_fetchedFlatOrErrorPriority(x, 2, size, false);
                    check_fetchedFlatOrErrorPriority(x, 2, size, true);
                }
                x.family = 6;
                check_fetchedFlatOrErrorPriority(x, 2, 1, false);
                check_fetchedFlatOrErrorPriority(x, 2, 1, true);
            }
        }
        x.route = 0;
        x.late = true;
        for (uint8 flags; flags < 2; flags++) {
            x.extra = flags == 1;
            for (uint8 paramType; paramType < 3; paramType++) {
                x.paramType = paramType;
                x.family = 0;
                check_fetchedFlatOrErrorPriority(x, 0, 0, true);
                check_fetchedFlatOrErrorPriority(x, 1, 1, true);
                for (uint8 size; size < 8; size++) {
                    x.family = size == 3 ? 3 : 0;
                    check_fetchedFlatOrErrorPriority(x, 2, size, false);
                    check_fetchedFlatOrErrorPriority(x, 2, size, true);
                }
            }
        }
    }

    function test_fetchedOrStructureBoundsSamples() public {
        fixtureGuards();
        vm.expectCall(address(host), abi.encodePacked(ClaimResolveGetHost.reply.selector), uint64(90));
        vm.expectCall(address(host), abi.encodePacked(ClaimResolveGetHost.balanceOf.selector), uint64(18));
        OrCase memory x = sample();
        x.extra = false;
        for (uint8 route; route < 3; route++) {
            x.route = route;
            for (uint8 paramType; paramType < 3; paramType++) {
                x.paramType = paramType;
                for (uint8 entry; entry < 3; entry++) {
                    x.entry = entry;
                    for (uint8 size; size < 5; size++) {
                        if (route != 0 && size != 3) {
                            continue;
                        }
                        check_fetchedOrStructureAfterWordBounds(x, size, true);
                        check_fetchedOrStructureAfterWordBounds(x, size, false);
                    }
                }
            }
        }
    }

    function sample() internal pure returns (OrCase memory x) {
        x.value = bytes32(uint256(7));
        x.firstRef = bytes32(uint256(93));
        x.lower = bytes32(uint256(5));
        x.upper = bytes32(uint256(9));
        x.extra = true;
    }

    function fixtureGuards() internal {
        (bool ok, bytes memory out) =
            address(host).call(abi.encodeCall(ClaimResolveGetHost.reply, (hex"11", address(core))));
        assertFalse(ok, "host must refuse a caller other than core");
        assertEq(out, bytes(""));
        host.configure(7, 65, address(core), address(this));
        (ok, out) = address(host).call(abi.encodeCall(ClaimResolveGetHost.balanceOf, (address(this))));
        assertFalse(ok, "token host must refuse a caller other than core");
        assertEq(out, bytes(""));
    }

    function assumeCase(OrCase memory x) internal pure {
        vm.assume(x.family < 8 && x.route < 3 && x.paramType < 3 && x.entry < 3);
        vm.assume(!x.late || x.route == 0);
    }

    function fetched(OrCase memory x) internal returns (InputParam memory p, bytes memory value) {
        value = x.late ? abi.encode(uint256(42), x.value) : abi.encode(x.value);
        if (x.route == 0) {
            if (x.extra) {
                value = bytes.concat(value, hex"7f");
            }
            p = InputParam(
                InputParamType(x.paramType),
                InputParamFetcherType.STATIC_CALL,
                abi.encode(address(host), abi.encodeCall(ClaimResolveGetHost.reply, (value, address(core)))),
                new Constraint[](0)
            );
        } else {
            vm.deal(address(this), uint256(x.value));
            host.configure(uint256(x.value), 65, address(core), address(this));
            p = InputParam(
                InputParamType(x.paramType),
                InputParamFetcherType.BALANCE,
                abi.encodePacked(x.route == 1 ? address(0) : address(host), address(this)),
                new Constraint[](0)
            );
        }
    }

    function attach(InputParam memory p, Constraint memory c, bool late) internal pure {
        p.constraints = new Constraint[](late ? 2 : 1);
        if (late) {
            p.constraints[0] = Constraint(ConstraintType.SKIP, "");
        }
        p.constraints[late ? 1 : 0] = c;
    }

    function invalidStructure(OrCase memory x) internal pure returns (bytes memory) {
        return abi.encodeWithSelector(InvalidOrConstraint.selector, uint256(0), uint256(0), outerIndex(x));
    }

    function invalidReference(OrCase memory x, uint256 length) internal pure returns (bytes memory) {
        return abi.encodeWithSelector(InvalidConstraintData.selector, uint256(0), uint256(0), outerIndex(x), length);
    }

    function outerIndex(OrCase memory x) internal pure returns (uint256) {
        return x.late ? 1 : 0;
    }

    function judge(InputParam memory p, uint8 entry) internal view returns (bool ok, bytes memory out) {
        if (entry == 0) {
            return address(core).staticcall(abi.encodeCall(Assertions.resolve, (p)));
        }
        if (entry == 1) {
            return
                address(core).staticcall(abi.encodeWithSignature("assertParam((uint8,uint8,bytes,(uint8,bytes)[]))", p));
        }
        return address(core)
            .staticcall(
                abi.encodeWithSignature("assertParam((uint8,uint8,bytes,(uint8,bytes)[]),string)", p, "fetched-or")
            );
    }

    function successResult(bytes memory value, uint8 entry) internal pure returns (bytes memory) {
        return entry == 0 ? value : bytes("");
    }

    function failed(OrCase memory x, Constraint memory c) internal pure returns (bytes memory) {
        return abi.encodeWithSelector(
            ConstraintFailed.selector,
            x.entry == 0 ? "" : x.entry == 1 ? "PARAM" : "fetched-or",
            uint256(0),
            uint256(0),
            outerIndex(x),
            ConstraintType.OR,
            x.value,
            c.referenceData
        );
    }

    function leaf(uint8 family, bytes32 lower, bytes32 upper) internal pure returns (Constraint memory) {
        ConstraintType kind = family == 0
            ? ConstraintType.EQ
            : family == 1
                ? ConstraintType.GTE
                : family == 2
                    ? ConstraintType.LTE
                    : family == 3
                        ? ConstraintType.IN
                        : family == 4
                            ? ConstraintType.GTE_SIGNED
                            : family == 5
                                ? ConstraintType.LTE_SIGNED
                                : family == 6 ? ConstraintType.SKIP : ConstraintType.IN_SIGNED;
        bytes memory data = kind == ConstraintType.SKIP
            ? bytes("")
            : kind == ConstraintType.IN || kind == ConstraintType.IN_SIGNED
                ? abi.encode(lower, upper)
                : abi.encode(lower);
        return Constraint(kind, data);
    }

    function verdict(bytes32 value, bytes32 lower, bytes32 upper, ConstraintType kind)
        internal
        pure
        returns (bool, bool)
    {
        if (kind == ConstraintType.EQ) {
            return (value == lower, false);
        }
        if (kind == ConstraintType.GTE) {
            return (uint256(value) >= uint256(lower), false);
        }
        if (kind == ConstraintType.LTE) {
            return (uint256(value) <= uint256(lower), false);
        }
        if (kind == ConstraintType.IN) {
            return
                (uint256(lower) <= uint256(value) && uint256(value) <= uint256(upper), uint256(lower) > uint256(upper));
        }
        if (kind == ConstraintType.GTE_SIGNED) {
            return (int256(uint256(value)) >= int256(uint256(lower)), false);
        }
        if (kind == ConstraintType.LTE_SIGNED) {
            return (int256(uint256(value)) <= int256(uint256(lower)), false);
        }
        if (kind == ConstraintType.SKIP) {
            return (true, false);
        }
        return (
            int256(uint256(lower)) <= int256(uint256(value)) && int256(uint256(value)) <= int256(uint256(upper)),
            int256(uint256(lower)) > int256(uint256(upper))
        );
    }

    function byteLength(uint8 size) internal pure returns (uint256) {
        if (size == 0) {
            return 0;
        }
        if (size == 1) {
            return 1;
        }
        if (size == 2) {
            return 31;
        }
        if (size == 3) {
            return 32;
        }
        if (size == 4) {
            return 33;
        }
        if (size == 5) {
            return 63;
        }
        if (size == 6) {
            return 64;
        }
        return 65;
    }

    function prefix(bytes memory data, uint256 length) internal pure returns (bytes memory out) {
        out = new bytes(length);
        for (uint256 i; i < length; i++) {
            out[i] = data[i];
        }
    }
}
