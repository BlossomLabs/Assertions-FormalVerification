// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../Assertions.sol";
import {ClaimCoreConstraintHost} from "./ClaimCoreConstraintsSymbolic.t.sol";

/**
 * @notice C2/C21: all eight non-OR kinds on symbolic full words, four fetch
 * routes for assertParam, and one/two positional words for resolve. Separate
 * canonical OR structures pin short-circuiting and structural error priority.
 * References compare directly with signed/unsigned Solidity comparisons, not
 * the production verdict implementation or an encode/decode round trip.
 */
contract ClaimDirectConstraintsSymbolicTest is Test {
    struct LeafInput {
        bytes32 value;
        bytes32 lower;
        bytes32 upper;
        uint8 family;
        uint8 fetcher;
        bool message;
    }

    struct OrInput {
        bytes32 value;
        bytes32 ref;
        int256 lower;
        int256 upper;
        uint8 shape;
        bool resolving;
        bool fetchedCall;
    }

    Assertions core;
    ClaimCoreConstraintHost host;

    function setUp() public {
        core = new Assertions();
        host = new ClaimCoreConstraintHost();
    }

    function check_directAssertLeafFetchers(LeafInput memory x) public {
        vm.assume(x.family < 8 && x.fetcher < 4);
        host.configure(uint256(x.value));
        vm.deal(address(host), uint256(x.value));
        InputParam memory p = fetched(x.value, x.fetcher);
        Constraint memory c = leaf(x.family, x.lower, x.upper);
        p.constraints = new Constraint[](1);
        p.constraints[0] = c;
        (bool ok, bytes memory out) = address(core)
            .staticcall(
                x.message
                    ? abi.encodeWithSignature("assertParam((uint8,uint8,bytes,(uint8,bytes)[]),string)", p, "direct")
                    : abi.encodeWithSignature("assertParam((uint8,uint8,bytes,(uint8,bytes)[]))", p)
            );
        (bool holds, bool invalidRange) = verdict(x.value, x.lower, x.upper, c.constraintType);
        assertEq(ok, holds && !invalidRange);
        assertEq(
            out,
            invalidRange
                ? abi.encodeWithSelector(InvalidConstraintRange.selector, uint256(0), uint256(0), uint256(0))
                : holds ? bytes("") : failed(x.message ? "direct" : "PARAM", 0, x.value, c)
        );
    }

    function check_directResolveLeafPositions(LeafInput memory x, bool fetchedCall, bool late) public view {
        vm.assume(x.family < 8);
        InputParam memory p = fetchedCall
            ? operand(abi.encodeCall(ClaimCoreConstraintHost.two, (bytes32(uint256(42)), x.value)))
            : raw(abi.encode(bytes32(uint256(42)), x.value));
        if (!late) p = fetchedCall ? fetched(x.value, 1) : raw(abi.encode(x.value));
        p.constraints = new Constraint[](late ? 2 : 1);
        if (late) p.constraints[0] = Constraint(ConstraintType.SKIP, "");
        Constraint memory c = leaf(x.family, x.lower, x.upper);
        p.constraints[late ? 1 : 0] = c;
        (bool ok, bytes memory out) = address(core).staticcall(abi.encodeCall(Assertions.resolve, (p)));
        (bool holds, bool invalidRange) = verdict(x.value, x.lower, x.upper, c.constraintType);
        assertEq(ok, holds && !invalidRange);
        assertEq(
            out,
            invalidRange
                ? abi.encodeWithSelector(InvalidConstraintRange.selector, uint256(0), uint256(0), late ? uint256(1) : 0)
                : holds
                    ? (late ? abi.encode(bytes32(uint256(42)), x.value) : abi.encode(x.value))
                    : failed("", late ? 1 : 0, x.value, c)
        );
    }

    function check_directOrStructureAndVerdict(OrInput memory x) public view {
        vm.assume(x.shape < 4);
        Constraint[] memory alternatives = new Constraint[](x.shape == 0 ? 0 : 2);
        if (x.shape != 0) {
            alternatives[0] = Constraint(ConstraintType.EQ, abi.encode(x.ref));
            alternatives[1] = x.shape == 2
                ? Constraint(ConstraintType.OR, abi.encode(new Constraint[](0)))
                : x.shape == 3
                    ? Constraint(ConstraintType.IN_SIGNED, abi.encode(x.lower, x.upper, x.ref))
                    : Constraint(ConstraintType.IN_SIGNED, abi.encode(x.lower, x.upper));
        }
        Constraint memory c = Constraint(ConstraintType.OR, abi.encode(alternatives));
        InputParam memory p = x.fetchedCall ? fetched(x.value, 1) : raw(abi.encode(x.value));
        p.constraints = new Constraint[](1);
        p.constraints[0] = c;
        (bool ok, bytes memory out) = address(core)
            .staticcall(
                x.resolving
                    ? abi.encodeCall(Assertions.resolve, (p))
                    : abi.encodeWithSignature("assertParam((uint8,uint8,bytes,(uint8,bytes)[]))", p)
            );
        if (x.shape == 0 || x.shape == 2) {
            assertFalse(ok);
            assertEq(out, abi.encodeWithSelector(InvalidOrConstraint.selector, uint256(0), uint256(0), uint256(0)));
        } else if (x.shape == 3 && x.value != x.ref) {
            assertFalse(ok);
            assertEq(
                out,
                abi.encodeWithSelector(InvalidConstraintData.selector, uint256(0), uint256(0), uint256(0), uint256(96))
            );
        } else if (x.shape == 1 && x.value != x.ref && x.lower > x.upper) {
            assertFalse(ok);
            assertEq(out, abi.encodeWithSelector(InvalidConstraintRange.selector, uint256(0), uint256(0), uint256(0)));
        } else {
            bool holds = x.value == x.ref
                || (x.shape == 1 && x.lower <= int256(uint256(x.value)) && int256(uint256(x.value)) <= x.upper);
            assertEq(ok, holds);
            assertEq(
                out,
                holds
                    ? (x.resolving ? abi.encode(x.value) : bytes(""))
                    : failed(x.resolving ? "" : "PARAM", 0, x.value, c)
            );
        }
    }

    function check_directLeafReferenceLengths(bytes32 value, uint8 family, uint8 size, bool resolving) public view {
        vm.assume(family < 8 && size < 6);
        Constraint memory c = leaf(family, bytes32(uint256(7)), bytes32(uint256(93)));
        uint256 n = size == 0 ? 0 : size == 1 ? 1 : size == 2 ? 31 : size == 3 ? 32 : size == 4 ? 64 : 65;
        c.referenceData = new bytes(n);
        uint256 canonical = c.constraintType == ConstraintType.SKIP
            ? 0
            : c.constraintType == ConstraintType.IN || c.constraintType == ConstraintType.IN_SIGNED ? 64 : 32;
        vm.assume(n != canonical);
        InputParam memory p = raw(abi.encode(value));
        p.constraints = new Constraint[](1);
        p.constraints[0] = c;
        (bool ok, bytes memory out) = address(core)
            .staticcall(
                resolving
                    ? abi.encodeCall(Assertions.resolve, (p))
                    : abi.encodeWithSignature("assertParam((uint8,uint8,bytes,(uint8,bytes)[]))", p)
            );
        assertFalse(ok);
        assertEq(out, abi.encodeWithSelector(InvalidConstraintData.selector, uint256(0), uint256(0), uint256(0), n));
    }

    function fetched(bytes32 value, uint8 route) internal view returns (InputParam memory) {
        if (route == 0) return raw(abi.encode(value));
        if (route == 1) return operand(abi.encodeCall(ClaimCoreConstraintHost.word, (value)));
        return InputParam(
            InputParamType.CALL_DATA,
            InputParamFetcherType.BALANCE,
            abi.encodePacked(route == 2 ? address(0) : address(host), address(host)),
            new Constraint[](0)
        );
    }

    function operand(bytes memory data) internal view returns (InputParam memory) {
        return InputParam(
            InputParamType.CALL_DATA,
            InputParamFetcherType.STATIC_CALL,
            abi.encode(address(host), data),
            new Constraint[](0)
        );
    }

    function raw(bytes memory data) internal pure returns (InputParam memory) {
        return InputParam(InputParamType.CALL_DATA, InputParamFetcherType.RAW_BYTES, data, new Constraint[](0));
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
        if (kind == ConstraintType.EQ) return (value == lower, false);
        if (kind == ConstraintType.GTE) return (uint256(value) >= uint256(lower), false);
        if (kind == ConstraintType.LTE) return (uint256(value) <= uint256(lower), false);
        if (kind == ConstraintType.IN) {
            return
                (uint256(lower) <= uint256(value) && uint256(value) <= uint256(upper), uint256(lower) > uint256(upper));
        }
        if (kind == ConstraintType.GTE_SIGNED) return (int256(uint256(value)) >= int256(uint256(lower)), false);
        if (kind == ConstraintType.LTE_SIGNED) return (int256(uint256(value)) <= int256(uint256(lower)), false);
        if (kind == ConstraintType.SKIP) return (true, false);
        return (
            int256(uint256(lower)) <= int256(uint256(value)) && int256(uint256(value)) <= int256(uint256(upper)),
            int256(uint256(lower)) > int256(uint256(upper))
        );
    }

    function failed(string memory message, uint256 index, bytes32 actual, Constraint memory c)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encodeWithSelector(
            ConstraintFailed.selector, message, uint256(0), uint256(0), index, c.constraintType, actual, c.referenceData
        );
    }

    function test_directLeafSamples() public {
        for (uint8 f; f < 8; f++) {
            for (uint8 route; route < 4; route++) {
                check_directAssertLeafFetchers(
                    LeafInput(bytes32(uint256(42)), bytes32(uint256(7)), bytes32(uint256(93)), f, route, false)
                );
                check_directAssertLeafFetchers(
                    LeafInput(bytes32(uint256(42)), bytes32(uint256(93)), bytes32(uint256(7)), f, route, true)
                );
            }
            check_directResolveLeafPositions(
                LeafInput(bytes32(uint256(42)), bytes32(uint256(7)), bytes32(uint256(93)), f, 0, false), false, false
            );
            check_directResolveLeafPositions(
                LeafInput(bytes32(uint256(42)), bytes32(uint256(93)), bytes32(uint256(7)), f, 0, false), true, true
            );
        }
    }

    function test_directOrSamples() public view {
        for (uint8 i; i < 4; i++) {
            check_directOrStructureAndVerdict(
                OrInput(bytes32(uint256(42)), bytes32(uint256(42)), 7, 93, i, false, false)
            );
            check_directOrStructureAndVerdict(OrInput(bytes32(uint256(42)), bytes32(uint256(7)), 7, 93, i, true, true));
            check_directOrStructureAndVerdict(OrInput(bytes32(uint256(42)), bytes32(uint256(7)), 93, 7, i, false, true));
        }
        check_directLeafReferenceLengths(bytes32(uint256(42)), 0, 2, false);
        check_directLeafReferenceLengths(bytes32(uint256(42)), 3, 5, true);
        check_directLeafReferenceLengths(bytes32(uint256(42)), 6, 1, false);
    }
}
