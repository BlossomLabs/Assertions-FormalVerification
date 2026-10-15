// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../Assertions.sol";
import {AbiCodec} from "../lib/AbiCodec.sol";
import {ClaimResolveGetHost} from "./ClaimResolveGetExtensionsSymbolic.t.sol";

/**
 * @notice Finite fetched-kind/type cross-products and selected dynamic-array
 *         get layouts. Typed solc encodings are independent of AbiCodec; leaf
 *         verdicts use ordinary signed/unsigned comparisons. No arbitrary
 *         lengths, nesting or gas behavior are inferred from these fixtures.
 */
contract ClaimFetchedKindsDynamicArraysSymbolicTest is Test {
    struct LeafCase {
        bytes32 value;
        bytes32 lower;
        bytes32 upper;
        uint8 family;
        uint8 route;
        uint8 paramType;
        uint8 entry;
        bool extra;
    }

    struct Item {
        uint8 tag;
        bytes data;
    }

    struct WideItem {
        uint256 tag;
        bytes data;
    }

    Assertions core;
    ClaimResolveGetHost host;
    bytes4 constant ECHO = 0xcafef00d;
    bytes32 constant FIRST = bytes32(uint256(0xa11ce));
    bytes32 constant SECOND = bytes32(uint256(0xb0b));

    function setUp() public {
        core = new Assertions();
        host = new ClaimResolveGetHost();
    }

    function check_fetchedLeafKindsParamTypes(LeafCase memory x) public {
        vm.assume(x.family < 8 && x.route < 3 && x.paramType < 3 && x.entry < 3);
        vm.warp(1000);
        (InputParam memory p, bytes memory value) = fetched(x);
        Constraint memory c = leaf(x.family, x.lower, x.upper);
        p.constraints = new Constraint[](1);
        p.constraints[0] = c;
        (bool ok, bytes memory out) = judge(p, x.entry);
        (bool holds, bool invalidRange) = verdict(x.value, x.lower, x.upper, c.constraintType);
        assertEq(ok, holds && !invalidRange);
        assertEq(
            out,
            invalidRange
                ? abi.encodeWithSelector(InvalidConstraintRange.selector, uint256(0), uint256(0), uint256(0))
                : holds
                    ? (x.entry == 0 ? value : bytes(""))
                    : abi.encodeWithSelector(
                        ConstraintFailed.selector,
                        x.entry == 0 ? "" : x.entry == 1 ? "PARAM" : "fetched-kind",
                        uint256(0),
                        uint256(0),
                        uint256(0),
                        c.constraintType,
                        x.value,
                        c.referenceData
                    )
        );
        assertEq(host.count(), x.route == 1 ? 0 : 1);
    }

    function check_fetchedLeafReferenceParamTypes(LeafCase memory x, uint8 size) public {
        vm.assume(x.family < 8 && x.route < 3 && x.paramType < 3 && size < 8);
        vm.warp(1000);
        (InputParam memory p,) = fetched(x);
        Constraint memory c = leaf(x.family, x.lower, x.upper);
        uint256 length = byteLength(size);
        uint256 canonical = c.constraintType == ConstraintType.SKIP
            ? 0
            : c.constraintType == ConstraintType.IN || c.constraintType == ConstraintType.IN_SIGNED ? 64 : 32;
        vm.assume(length != canonical);
        bytes memory referenceBytes = bytes.concat(abi.encode(x.lower, x.upper), hex"7f");
        c.referenceData = new bytes(length);
        for (uint256 i; i < length; i++) {
            c.referenceData[i] = referenceBytes[i];
        }
        p.constraints = new Constraint[](1);
        p.constraints[0] = c;
        bytes memory expected =
            abi.encodeWithSelector(InvalidConstraintData.selector, uint256(0), uint256(0), uint256(0), length);
        (bool ok, bytes memory out) = judge(p, 0);
        assertFalse(ok);
        assertEq(out, expected);
        (ok, out) = judge(p, 2);
        assertFalse(ok);
        assertEq(out, expected);
        assertEq(host.count(), x.route == 1 ? 0 : 2);
    }

    function check_getDynamicTupleArrayArguments(
        bytes32[2] memory aw,
        bytes32[2] memory bw,
        uint8 sa,
        uint8 sb,
        uint8 countCase,
        uint8 first,
        uint8 second
    ) public {
        vm.assume(sa < 5 && sb < 5 && countCase < 3);
        vm.warp(1000);
        bytes memory a = payload(aw, sa);
        bytes memory b = payload(bw, sb);
        Item[] memory items = countCase == 0 ? new Item[](0) : countCase == 1 ? new Item[](1) : new Item[](2);
        if (countCase != 0) {
            items[0] = Item(first, a);
        }
        if (countCase == 2) {
            items[1] = Item(second, b);
        }
        InputParam[] memory args = new InputParam[](2);
        args[0] = raw(abi.encode(items));
        args[1] = raw(abi.encode(b));
        (bool ok, bytes memory out) = get("((uint8,bytes)[],bytes)", args);
        assertTrue(ok);
        assertEq(out, bytes.concat(bytes32(uint256(uint160(address(core)))), ECHO, abi.encode(items, b)));
        assertEq(host.count(), 10);
    }

    function check_getArrayOfFixedDynamicArguments(
        bytes32[2] memory aw,
        bytes32[2] memory bw,
        uint8 sa,
        uint8 sb,
        uint8 countCase
    ) public {
        vm.assume(sa < 5 && sb < 5 && countCase < 3);
        vm.warp(1000);
        bytes memory a = payload(aw, sa);
        bytes memory b = payload(bw, sb);
        bytes[2][] memory rows =
            countCase == 0 ? new bytes[2][](0) : countCase == 1 ? new bytes[2][](1) : new bytes[2][](2);
        if (countCase != 0) {
            rows[0][0] = a;
            rows[0][1] = b;
        }
        if (countCase == 2) {
            rows[1][0] = b;
            rows[1][1] = a;
        }
        InputParam[] memory args = new InputParam[](2);
        args[0] = raw(abi.encode(rows));
        args[1] = raw(abi.encode(b));
        (bool ok, bytes memory out) = get("(bytes[2][],bytes)", args);
        assertTrue(ok);
        assertEq(out, bytes.concat(bytes32(uint256(uint160(address(core)))), ECHO, abi.encode(rows, b)));
        assertEq(host.count(), 10);
    }

    function check_getTupleArrayComponentPriority(bytes32 dirty, uint8 badComponent, uint8 element, uint8 fault)
        public
    {
        vm.assume(uint256(dirty) > 255 && badComponent < 2 && element < 2 && fault < 2);
        vm.warp(1000);
        (bytes memory damaged, uint256 offset) = tupleArrayFault(dirty, element, fault);
        WideItem[] memory later = wideItems(false);
        later[0].tag = 313;
        InputParam[] memory args = new InputParam[](2);
        args[0] = raw(badComponent == 0 ? damaged : abi.encode(wideItems(false)));
        args[1] = raw(badComponent == 1 ? damaged : abi.encode(later));
        (bool ok, bytes memory out) = get("((uint8,bytes)[],(uint8,bytes)[])", args);
        assertFalse(ok);
        assertEq(out, abi.encodeWithSelector(AbiCodec.InvalidComponentValue.selector, uint256(badComponent), offset));
        assertEq(host.count(), 0);
    }

    function check_getFixedDynamicArrayComponentPriority(uint8 badComponent, uint8 fault) public {
        vm.assume(badComponent < 2 && fault < 4);
        vm.warp(1000);
        bytes memory fixture = abi.encode(fixedRows());
        uint256 head = fault == 0 ? 64 : fault == 1 ? 96 : fault == 2 ? 128 : 160;
        // Literal positions/values are independently checked against the solc
        // fixture. They are not computed with the codec's frame formula.
        uint256 headValue = fault == 1 ? 256 : fault == 3 ? 128 : 64;
        assertEq(readWord(fixture, head), headValue, "independent fixed-array geometry");
        uint256 padding = findWord(fixture, bytes32(bytes1(0x11))) + 1;
        bytes memory damaged = abi.encode(fixedRows());
        putWord(damaged, head, headValue + 32);
        damaged[padding] = 0x7f;
        // body visits an element's complete tail before the next element's
        // head. Thus earlier padding wins over heads at 96/160 despite those
        // head bytes appearing numerically earlier in the wire encoding.
        uint256 offset = fault == 0 || fault == 2 ? head : padding;
        bytes memory later = abi.encode(fixedRows());
        putWord(later, 64, 96);
        InputParam[] memory args = new InputParam[](2);
        args[0] = raw(badComponent == 0 ? damaged : fixture);
        args[1] = raw(badComponent == 1 ? damaged : later);
        (bool ok, bytes memory out) = get("(bytes[2][],bytes[2][])", args);
        assertFalse(ok);
        assertEq(out, abi.encodeWithSelector(AbiCodec.InvalidComponentValue.selector, uint256(badComponent), offset));
        assertEq(host.count(), 0);
    }

    function tupleArrayFault(bytes32 dirty, uint8 element, uint8 fault)
        internal
        pure
        returns (bytes memory data, uint256 offset)
    {
        bytes memory fixture = abi.encode(wideItems(true));
        WideItem[] memory items = wideItems(false);
        if (fault == 0) {
            offset = findWord(fixture, element == 0 ? FIRST : SECOND);
            if (element == 0) {
                items[0].tag = uint256(dirty);
            } else {
                items[1].tag = uint256(dirty);
            }
        } else {
            offset = findWord(fixture, element == 0 ? bytes32(bytes1(0x11)) : bytes32(bytes1(0x22))) + 1;
            if (element == 0) {
                items[1].tag = uint256(dirty);
            }
        }
        data = abi.encode(items);
        if (fault == 1) {
            data[offset] = 0x7f;
        }
    }

    function wideItems(bool marker) internal pure returns (WideItem[] memory items) {
        items = new WideItem[](2);
        items[0] = WideItem(marker ? uint256(FIRST) : 7, hex"11");
        items[1] = WideItem(marker ? uint256(SECOND) : 9, hex"22");
    }

    function fixedRows() internal pure returns (bytes[2][] memory rows) {
        rows = new bytes[2][](2);
        rows[0][0] = hex"11";
        rows[0][1] = hex"22";
        rows[1][0] = hex"33";
        rows[1][1] = hex"44";
    }

    function findWord(bytes memory data, bytes32 marker) internal pure returns (uint256 offset) {
        uint256 matches;
        for (uint256 i; i + 32 <= data.length; i += 32) {
            if (bytes32(readWord(data, i)) == marker) {
                offset = i;
                matches++;
            }
        }
        assertEq(matches, 1, "independent marker must be unique");
    }

    function readWord(bytes memory data, uint256 offset) internal pure returns (uint256 word) {
        assertTrue(offset <= data.length && data.length - offset >= 32);
        assembly ("memory-safe") { word := mload(add(add(data, 32), offset)) }
    }

    function putWord(bytes memory data, uint256 offset, uint256 word) internal pure {
        assertTrue(offset <= data.length && data.length - offset >= 32);
        assembly ("memory-safe") { mstore(add(add(data, 32), offset), word) }
    }

    function get(string memory descriptor, InputParam[] memory args) internal view returns (bool ok, bytes memory out) {
        return address(core)
            .staticcall(abi.encodeCall(Assertions.get, (raw(abi.encode(address(host))), ECHO, descriptor, args)));
    }

    function raw(bytes memory data) internal pure returns (InputParam memory) {
        return InputParam(InputParamType.CALL_DATA, InputParamFetcherType.RAW_BYTES, data, new Constraint[](0));
    }

    function payload(bytes32[2] memory words, uint8 size) internal pure returns (bytes memory data) {
        uint256 length = byteLength(size);
        bytes memory full = abi.encode(words);
        data = new bytes(length);
        for (uint256 i; i < length; i++) {
            data[i] = full[i];
        }
    }

    function fetched(LeafCase memory x) internal returns (InputParam memory p, bytes memory value) {
        value = abi.encode(x.value);
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
                abi.encodeWithSignature("assertParam((uint8,uint8,bytes,(uint8,bytes)[]),string)", p, "fetched-kind")
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
        if (size == 0) return 0;
        if (size == 1) return 1;
        if (size == 2) return 31;
        if (size == 3) return 32;
        if (size == 4) return 33;
        if (size == 5) return 63;
        if (size == 6) return 64;
        return 65;
    }

    function test_fetchedLeafKindsSamples() public {
        for (uint8 kind; kind < 8; kind++) {
            for (uint8 route; route < 3; route++) {
                for (uint8 paramType; paramType < 3; paramType++) {
                    for (uint8 entry; entry < 3; entry++) {
                        check_fetchedLeafKindsParamTypes(
                            LeafCase(
                                bytes32(uint256(42)),
                                bytes32(uint256(42)),
                                bytes32(uint256(93)),
                                kind,
                                route,
                                paramType,
                                entry,
                                false
                            )
                        );
                        check_fetchedLeafKindsParamTypes(
                            LeafCase(
                                bytes32(uint256(42)),
                                bytes32(uint256(93)),
                                bytes32(uint256(7)),
                                kind,
                                route,
                                paramType,
                                entry,
                                true
                            )
                        );
                        check_fetchedLeafKindsParamTypes(
                            LeafCase(
                                bytes32(type(uint256).max),
                                bytes32(uint256(7)),
                                bytes32(uint256(93)),
                                kind,
                                route,
                                paramType,
                                entry,
                                true
                            )
                        );
                    }
                }
            }
        }
    }

    function test_fetchedLeafReferenceSamples() public {
        for (uint8 kind; kind < 8; kind++) {
            for (uint8 route; route < 3; route++) {
                for (uint8 paramType; paramType < 3; paramType++) {
                    for (uint8 size; size < 8; size++) {
                        uint256 canonical = kind == 6 ? 0 : kind == 3 || kind == 7 ? 64 : 32;
                        if (byteLength(size) != canonical) {
                            check_fetchedLeafReferenceParamTypes(
                                LeafCase(
                                    bytes32(uint256(42)),
                                    bytes32(uint256(93)),
                                    bytes32(uint256(7)),
                                    kind,
                                    route,
                                    paramType,
                                    0,
                                    true
                                ),
                                size
                            );
                        }
                    }
                }
            }
        }
    }

    function test_getDynamicTupleArraySamples() public {
        bytes32[2] memory a = [bytes32(uint256(0x93)), bytes32(uint256(0x7f))];
        bytes32[2] memory b = [bytes32(type(uint256).max), bytes32(uint256(0x42))];
        vm.expectCall(address(host), abi.encodePacked(ECHO), uint64(75));
        for (uint8 count; count < 3; count++) {
            for (uint8 sa; sa < 5; sa++) {
                for (uint8 sb; sb < 5; sb++) {
                    check_getDynamicTupleArrayArguments(a, b, sa, sb, count, 7, 255);
                }
            }
        }
    }

    function test_getArrayOfFixedDynamicSamples() public {
        bytes32[2] memory a = [bytes32(uint256(0x93)), bytes32(uint256(0x7f))];
        bytes32[2] memory b = [bytes32(type(uint256).max), bytes32(uint256(0x42))];
        vm.expectCall(address(host), abi.encodePacked(ECHO), uint64(75));
        for (uint8 count; count < 3; count++) {
            for (uint8 sa; sa < 5; sa++) {
                for (uint8 sb; sb < 5; sb++) {
                    check_getArrayOfFixedDynamicArguments(a, b, sa, sb, count);
                }
            }
        }
    }

    function test_getTupleArrayComponentPrioritySamples() public {
        vm.expectCall(address(host), abi.encodePacked(ECHO), uint64(0));
        for (uint8 component; component < 2; component++) {
            for (uint8 element; element < 2; element++) {
                for (uint8 fault; fault < 2; fault++) {
                    check_getTupleArrayComponentPriority(bytes32(uint256(313)), component, element, fault);
                }
            }
        }
    }

    function test_getFixedDynamicArrayComponentPrioritySamples() public {
        vm.expectCall(address(host), abi.encodePacked(ECHO), uint64(0));
        for (uint8 component; component < 2; component++) {
            for (uint8 fault; fault < 4; fault++) {
                check_getFixedDynamicArrayComponentPriority(component, fault);
            }
        }
    }
}
