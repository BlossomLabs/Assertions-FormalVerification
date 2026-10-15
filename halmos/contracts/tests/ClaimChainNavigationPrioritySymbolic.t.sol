// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../Assertions.sol";
import "../lib/AbiCodec.sol";
import {ClaimCallerRelay} from "./ClaimConstructionSymbolic.t.sol";

/**
 * @dev A lane-specific caller guard plus test-only clock observations. Each
 *      lane has its own target and weight; totals alone do not prove order.
 */
contract ClaimChainPriorityHost {
    Vm constant VM = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    uint256 immutable lane;
    uint256 immutable weight;

    constructor(uint256 lane_) {
        lane = lane_;
        weight = uint256(1) << (lane_ * 2);
    }

    function supply(address caller_) external returns (address) {
        VM.warp(block.timestamp + weight);
        require(msg.sender == caller_ && lane == 0);
        return address(this);
    }

    function step(uint256 lane_, bytes calldata data, bool failing, address caller_) external {
        VM.warp(block.timestamp + weight);
        require(lane == lane_ && msg.sender == caller_);
        if (failing) {
            assembly ("memory-safe") {
                calldatacopy(0, data.offset, data.length)
                revert(0, data.length)
            }
        }
        assembly ("memory-safe") {
            calldatacopy(0, data.offset, data.length)
            return(0, data.length)
        }
    }

    function trace() external view returns (uint256) {
        return block.timestamp - 1000;
    }
}

/**
 * @notice Three/four-hop chain prefixes and competing navigation faults.
 *         Addresses/lengths/path geometries are literal; contents are symbolic.
 *         Canonical navigation controls come from solc. Expected failures use
 *         the source's documented validation order, with complete error data.
 */
contract ClaimChainNavigationPrioritySymbolicTest is Test {
    Assertions core;
    ClaimChainPriorityHost h0;
    ClaimChainPriorityHost h1;
    ClaimChainPriorityHost h2;
    ClaimChainPriorityHost h3;
    address constant EMPTY = address(0xE0A);
    bytes32 constant A = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa;
    bytes32 constant B = 0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb;

    function setUp() public {
        core = new Assertions();
        h0 = new ClaimChainPriorityHost(0);
        h1 = new ClaimChainPriorityHost(1);
        h2 = new ClaimChainPriorityHost(2);
        h3 = new ClaimChainPriorityHost(3);
        vm.etch(EMPTY, "");
        vm.etch(address(0xCA11E2), address(new ClaimCallerRelay()).code);
    }

    function check_chainThreeFourSuccess(
        bytes32[2] memory words,
        uint8 size,
        bool four,
        bool longMiddle,
        bool fetchedStart
    ) public {
        vm.assume(size < 5);
        vm.warp(1000);
        uint256 n = four ? 4 : 3;
        bytes memory finalData = payload(words, size);
        bytes[] memory calls = chainCalls(n, finalData, longMiddle);
        InputParam memory start = fetchedStart
            ? operand(address(h0), abi.encodeCall(ClaimChainPriorityHost.supply, (address(core))))
            : raw(abi.encode(address(h0)));
        (bool ok, bytes memory out) = address(core).staticcall(abi.encodeCall(Assertions.chain, (start, calls)));
        assertTrue(ok);
        assertEq(out, finalData);
        assertEq(h0.trace(), prefix(n) + (fetchedStart ? 1 : 0));
    }

    function check_chainDirtyWordStops(uint96 upper, uint8 position, bool four) public {
        uint256 n = four ? 4 : 3;
        vm.assume(upper != 0 && position < n);
        uint256 bad = literalPosition(position);
        vm.warp(1000);
        bytes32 dirty = bytes32((uint256(upper) << 160) | uint160(hop(bad)));
        bytes[] memory calls = chainCalls(n, abi.encode(uint256(93)), true);
        InputParam memory start = raw(abi.encode(address(h0)));
        if (bad == 0) start = raw(abi.encode(dirty));
        else calls[bad - 1] = step(bad - 1, abi.encode(dirty), false);
        (bool ok, bytes memory out) = address(core).staticcall(abi.encodeCall(Assertions.chain, (start, calls)));
        assertFalse(ok);
        assertEq(out, abi.encodeWithSelector(InvalidAddressWord.selector, bad, dirty));
        assertEq(h0.trace(), prefix(bad), "no hop after the rejected address may execute");
    }

    function check_chainIntermediateLengths(bytes32[2] memory words, uint8 size, uint8 position, bool four) public {
        uint256 n = four ? 4 : 3;
        vm.assume(size < 5 && position < n - 1);
        uint256 bad = literalPosition(position);
        vm.warp(1000);
        bytes memory shortData = abi.encodePacked(abi.encode(hop(bad + 1)), bytes1(0x7f));
        uint256 length = byteLength(size);
        assembly ("memory-safe") { mstore(shortData, length) }
        bytes memory finalData = abi.encodePacked(words);
        bytes[] memory calls = chainCalls(n, finalData, false);
        calls[bad] = step(bad, shortData, false);
        (bool ok, bytes memory out) =
            address(core).staticcall(abi.encodeCall(Assertions.chain, (raw(abi.encode(address(h0))), calls)));
        assertEq(ok, length >= 32);
        assertEq(
            out, length >= 32 ? finalData : abi.encodeWithSelector(ReturnDataOutOfBounds.selector, int256(0), length)
        );
        assertEq(h0.trace(), prefix(length >= 32 ? n : bad + 1));
    }

    function check_chainFailedHopStops(bytes32[2] memory words, uint8 size, uint8 position, bool four, bool codeless)
        public
    {
        uint256 n = four ? 4 : 3;
        vm.assume(size < 5 && position < n);
        uint256 bad = literalPosition(position);
        vm.warp(1000);
        bytes[] memory calls = chainCalls(n, abi.encode(uint256(93)), true);
        calls[bad] = step(bad, payload(words, size), true);
        InputParam memory start = raw(abi.encode(address(h0)));
        if (codeless) {
            if (bad == 0) start = raw(abi.encode(EMPTY));
            else calls[bad - 1] = step(bad - 1, abi.encode(EMPTY), false);
        }
        (bool ok, bytes memory out) = address(core).staticcall(abi.encodeCall(Assertions.chain, (start, calls)));
        // A normal reverting subcall can take Halmos's symbolic exhaustion
        // branch. There is no concrete gas model; that output is excluded.
        if (!codeless) ordinary(ok, out);
        assertFalse(ok);
        assertEq(out, abi.encodeWithSelector(CallFailed.selector, codeless ? EMPTY : hop(bad), calls[bad]));
        assertEq(h0.trace(), prefix(codeless ? bad : bad + 1));
    }

    function check_chainEmptyBeforeInvalidStart(bytes32 word, uint8 fault) public {
        vm.assume(fault < 5);
        vm.warp(1000);
        InputParam memory start = raw(fault == 0 ? bytes("") : abi.encode(word | bytes32(uint256(1) << 255)));
        if (fault == 2) {
            start.constraints = new Constraint[](1);
            start.constraints[0] = Constraint(ConstraintType.OR, hex"ff");
        } else if (fault == 3) {
            start.fetcherType = InputParamFetcherType.STATIC_CALL;
            start.paramData = hex"ff";
        } else if (fault == 4) {
            start = operand(address(h0), abi.encodeCall(ClaimChainPriorityHost.supply, (address(core))));
        }
        (bool ok, bytes memory out) =
            address(core).staticcall(abi.encodeCall(Assertions.chain, (start, new bytes[](0))));
        assertFalse(ok);
        assertEq(out, abi.encodeWithSelector(Assertions.EmptyCallChain.selector));
        assertEq(h0.trace(), 0);
    }

    function check_navDescriptorBeforeInvalidIndex(uint8 fault, bool negative, bool malformed) public view {
        vm.assume(fault < 4);
        string memory t = !malformed
            ? "(uint8,uint8)"
            : fault == 0
                ? "(uint8[0],uint8)"
                : fault == 1 ? "(uint8,uint8[0])" : fault == 2 ? "(uint8 uint8)" : "((uint8,uint8))junk)";
        int256 index = negative ? int256(-1) : int256(2);
        (bool ok, bytes memory out) = nav("", t, path1(index));
        assertFalse(ok);
        assertEq(
            out,
            malformed
                ? abi.encodeWithSelector(
                    InvalidTypeDescriptor.selector,
                    fault == 0 ? uint256(8) : fault == 1 ? uint256(14) : fault == 2 ? uint256(6) : uint256(15)
                )
                : abi.encodeWithSelector(ElementIndexOutOfBounds.selector, index, uint256(2))
        );
    }

    function check_navMissingAncestorBeforeChildIndex(uint8 size, bool negative, bool rootInvalid) public view {
        vm.assume(size < 5);
        uint8[] memory values = new uint8[](1);
        values[0] = 7;
        bytes memory data = abi.encode(values);
        uint256 length = byteLength(size);
        assembly ("memory-safe") { mstore(data, length) }
        int256[] memory path = new int256[](2);
        path[0] = rootInvalid ? int256(1) : int256(0);
        path[1] = negative ? int256(-2) : int256(1);
        (bool ok, bytes memory out) = nav(data, "(uint8[])", path);
        assertFalse(ok);
        assertEq(
            out,
            rootInvalid
                ? abi.encodeWithSelector(ElementIndexOutOfBounds.selector, int256(1), uint256(1))
                : abi.encodeWithSelector(ReturnDataOutOfBounds.selector, length < 32 ? int256(0) : int256(1), length)
        );
    }

    function check_navArrayLengthBeforeInvalidIndex(uint8 size, bool negative) public view {
        vm.assume(size < 5);
        uint256 count = size == 0 ? 0 : size == 1 ? 1 : size == 2 ? 2 : size == 3 ? 3 : type(uint256).max;
        int256 index = negative ? int256(-99) : int256(99);
        (bool ok, bytes memory out) = nav(abi.encode(uint256(32), count), "(uint8[])", path2(0, index));
        assertFalse(ok);
        assertEq(
            out,
            size >= 3
                ? abi.encodeWithSelector(ReturnDataOutOfBounds.selector, int256(1), uint256(64))
                : abi.encodeWithSelector(ElementIndexOutOfBounds.selector, index, count)
        );
    }

    function check_navSelectedNarrowIgnoresSibling(bytes32 selected, bytes32 first, bytes32 second) public view {
        bytes memory fixture = abi.encode(A, B);
        uint256 selectedOffset = findWord(fixture, A);
        uint256 siblingOffset = findWord(fixture, B);
        bytes memory data = abi.encode(uint8(7), uint8(9));
        setWord(data, selectedOffset, selected);
        setWord(data, siblingOffset, first);
        (bool ok, bytes memory one) = nav(data, "(uint8,uint8)", path1(0));
        setWord(data, siblingOffset, second);
        (bool otherOk, bytes memory two) = nav(data, "(uint8,uint8)", path1(0));
        bool clean = uint256(selected) <= type(uint8).max;
        assertEq(ok, clean);
        assertEq(otherOk, clean);
        assertEq(one, two, "skipped sibling bytes must not change the selected result");
        assertEq(
            one,
            clean
                ? abi.encode(uint8(uint256(selected)))
                : abi.encodeWithSelector(AbiCodec.InvalidValue.selector, selectedOffset)
        );
    }

    function check_navSelectedArrayIgnoresSibling(bytes32 selected, bytes32 first, bytes32 second, bool invalidIndex)
        public
        view
    {
        (bytes memory data, uint256 selectedOffset, uint256 siblingOffset) = arrayFixture();
        setWord(data, selectedOffset, selected);
        setWord(data, siblingOffset, first);
        int256[] memory path = path2(0, invalidIndex ? int256(1) : int256(-1));
        (bool ok, bytes memory one) = nav(data, "(uint8[],uint8[])", path);
        setWord(data, siblingOffset, second);
        (bool otherOk, bytes memory two) = nav(data, "(uint8[],uint8[])", path);
        bool clean = !invalidIndex && uint256(selected) <= type(uint8).max;
        assertEq(ok, clean);
        assertEq(otherOk, clean);
        assertEq(one, two);
        assertEq(
            one,
            invalidIndex
                ? abi.encodeWithSelector(ElementIndexOutOfBounds.selector, int256(1), uint256(1))
                : clean
                    ? abi.encode(uint8(uint256(selected)))
                    : abi.encodeWithSelector(AbiCodec.InvalidValue.selector, selectedOffset)
        );
    }

    function arrayFixture() internal pure returns (bytes memory data, uint256 selectedOffset, uint256 siblingOffset) {
        uint256[] memory ma = new uint256[](1);
        uint256[] memory mb = new uint256[](1);
        ma[0] = uint256(A);
        mb[0] = uint256(B);
        bytes memory fixture = abi.encode(ma, mb);
        selectedOffset = findWord(fixture, A);
        siblingOffset = findWord(fixture, B);
        uint8[] memory a = new uint8[](1);
        uint8[] memory b = new uint8[](1);
        a[0] = 7;
        b[0] = 9;
        data = abi.encode(a, b);
    }

    function chainCalls(uint256 n, bytes memory finalData, bool longMiddle)
        internal
        view
        returns (bytes[] memory calls)
    {
        calls = new bytes[](n);
        calls[0] = step(0, middle(address(h1), longMiddle), false);
        calls[1] = step(1, middle(address(h2), longMiddle), false);
        if (n == 3) {
            calls[2] = step(2, finalData, false);
        } else {
            calls[2] = step(2, middle(address(h3), longMiddle), false);
            calls[3] = step(3, finalData, false);
        }
    }

    function step(uint256 lane, bytes memory data, bool failing) internal view returns (bytes memory) {
        return abi.encodeCall(ClaimChainPriorityHost.step, (lane, data, failing, address(core)));
    }

    function middle(address next, bool longMiddle) internal pure returns (bytes memory) {
        return longMiddle ? abi.encodePacked(abi.encode(next), bytes1(0x7f)) : abi.encode(next);
    }

    function hop(uint256 lane) internal view returns (address) {
        if (lane == 0) return address(h0);
        if (lane == 1) return address(h1);
        if (lane == 2) return address(h2);
        return address(h3);
    }

    function prefix(uint256 length) internal pure returns (uint256) {
        if (length == 0) return 0;
        if (length == 1) return 1;
        if (length == 2) return 5;
        if (length == 3) return 21;
        return 85;
    }

    function literalPosition(uint8 position) internal pure returns (uint256) {
        if (position == 0) return 0;
        if (position == 1) return 1;
        if (position == 2) return 2;
        return 3;
    }

    function byteLength(uint8 size) internal pure returns (uint256) {
        if (size == 0) return 0;
        if (size == 1) return 1;
        if (size == 2) return 31;
        if (size == 3) return 32;
        return 33;
    }

    function payload(bytes32[2] memory words, uint8 size) internal pure returns (bytes memory out) {
        out = abi.encodePacked(words[0], words[1]);
        uint256 n = byteLength(size);
        assembly ("memory-safe") { mstore(out, n) }
    }

    function raw(bytes memory data) internal pure returns (InputParam memory) {
        return InputParam(InputParamType.CALL_DATA, InputParamFetcherType.RAW_BYTES, data, new Constraint[](0));
    }

    function operand(address target, bytes memory data) internal pure returns (InputParam memory) {
        return InputParam(
            InputParamType.CALL_DATA, InputParamFetcherType.STATIC_CALL, abi.encode(target, data), new Constraint[](0)
        );
    }

    function nav(bytes memory data, string memory t, int256[] memory path) internal view returns (bool, bytes memory) {
        return address(core).staticcall(abi.encodeCall(Assertions.nav, (raw(data), t, path)));
    }

    function path1(int256 first) internal pure returns (int256[] memory path) {
        path = new int256[](1);
        path[0] = first;
    }

    function path2(int256 first, int256 second) internal pure returns (int256[] memory path) {
        path = new int256[](2);
        path[0] = first;
        path[1] = second;
    }

    function findWord(bytes memory data, bytes32 marker) internal pure returns (uint256 offset) {
        uint256 matches;
        for (uint256 i; i < data.length; i += 32) {
            bytes32 got;
            assembly ("memory-safe") { got := mload(add(add(data, 32), i)) }
            if (got == marker) {
                offset = i;
                matches++;
            }
        }
        assertEq(matches, 1, "independent marker must be unique");
    }

    function setWord(bytes memory data, uint256 offset, bytes32 value) internal pure {
        assembly ("memory-safe") { mstore(add(add(data, 32), offset), value) }
    }

    function ordinary(bool ok, bytes memory out) internal pure {
        vm.assume(ok || out.length != 4 || bytes4(out) != Assertions.SubcallOutOfGas.selector);
    }

    function expectSteps(uint64 a, uint64 b, uint64 c, uint64 d) internal {
        bytes memory selector = abi.encodePacked(ClaimChainPriorityHost.step.selector);
        vm.expectCall(address(h0), selector, a);
        vm.expectCall(address(h1), selector, b);
        vm.expectCall(address(h2), selector, c);
        vm.expectCall(address(h3), selector, d);
    }

    function test_chainSuccessAndLengthSamples() public {
        bytes32[2] memory words = [bytes32(uint256(42)), bytes32(uint256(93))];
        expectSteps(65, 59, 53, 26);
        vm.expectCall(address(h0), abi.encodeCall(ClaimChainPriorityHost.supply, (address(core))), uint64(20));
        for (uint8 f; f < 2; f++) {
            for (uint8 s; s < 5; s++) {
                check_chainThreeFourSuccess(words, s, f == 1, false, false);
                check_chainThreeFourSuccess(words, s, f == 1, false, true);
                check_chainThreeFourSuccess(words, s, f == 1, true, false);
                check_chainThreeFourSuccess(words, s, f == 1, true, true);
                for (uint8 p; p < (f == 1 ? 3 : 2); p++) {
                    check_chainIntermediateLengths(words, s, p, f == 1);
                }
            }
        }
    }

    function test_chainDirtyAndEmptySamples() public {
        expectSteps(5, 3, 1, 0);
        vm.expectCall(address(h0), abi.encodeCall(ClaimChainPriorityHost.supply, (address(core))), uint64(0));
        for (uint8 f; f < 2; f++) {
            for (uint8 p; p < (f == 1 ? 4 : 3); p++) {
                check_chainDirtyWordStops(7, p, f == 1);
            }
        }
        for (uint8 f; f < 5; f++) {
            check_chainEmptyBeforeInvalidStart(bytes32(uint256(42)), f);
        }
    }

    function test_chainOrdinaryFailureSamples() public {
        bytes32[2] memory words = [bytes32(uint256(42)), bytes32(uint256(93))];
        expectSteps(60, 40, 20, 5);
        for (uint8 f; f < 2; f++) {
            for (uint8 p; p < (f == 1 ? 4 : 3); p++) {
                for (uint8 s; s < 5; s++) {
                    check_chainFailedHopStops(words, s, p, f == 1, false);
                    check_chainFailedHopStops(words, s, p, f == 1, true);
                }
            }
        }
    }

    function test_navCompetingPrioritySamples() public view {
        for (uint8 f; f < 4; f++) {
            check_navDescriptorBeforeInvalidIndex(f, false, true);
            check_navDescriptorBeforeInvalidIndex(f, true, true);
            check_navDescriptorBeforeInvalidIndex(f, false, false);
            check_navDescriptorBeforeInvalidIndex(f, true, false);
        }
        for (uint8 s; s < 5; s++) {
            check_navMissingAncestorBeforeChildIndex(s, false, false);
            check_navMissingAncestorBeforeChildIndex(s, true, false);
            check_navMissingAncestorBeforeChildIndex(s, false, true);
            check_navArrayLengthBeforeInvalidIndex(s, false);
            check_navArrayLengthBeforeInvalidIndex(s, true);
        }
    }

    function test_navSelectedSiblingSamples() public view {
        check_navSelectedNarrowIgnoresSibling(bytes32(uint256(7)), bytes32(uint256(9)), bytes32(type(uint256).max));
        check_navSelectedNarrowIgnoresSibling(bytes32(uint256(256)), bytes32(uint256(9)), bytes32(type(uint256).max));
        check_navSelectedArrayIgnoresSibling(
            bytes32(uint256(7)), bytes32(uint256(9)), bytes32(type(uint256).max), false
        );
        check_navSelectedArrayIgnoresSibling(
            bytes32(uint256(256)), bytes32(uint256(9)), bytes32(type(uint256).max), false
        );
        check_navSelectedArrayIgnoresSibling(
            bytes32(uint256(256)), bytes32(uint256(9)), bytes32(type(uint256).max), true
        );
    }
}
