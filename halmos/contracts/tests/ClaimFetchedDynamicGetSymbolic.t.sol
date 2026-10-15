// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../Assertions.sol";
import "../lib/AbiCodec.sol";

/**
 * @dev Independent stored replies and complete input/caller guards. The clock
 *      observes bounded fixture executions through cheatcodes, not real gas or
 *      deployable staticcall state. The destination echoes caller and receiver.
 */
contract ClaimFetchedDynamicGetHost {
    Vm constant VM = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    uint256 immutable weight;
    address coreCaller;
    bytes replyValue;
    bytes32 inputHash;

    constructor(uint256 weight_) {
        weight = weight_;
    }

    function configure(address caller_, bytes calldata value) external {
        coreCaller = caller_;
        replyValue = value;
        inputHash = keccak256(abi.encodeCall(this.reply, (value)));
    }

    function reply(bytes calldata) external {
        require(msg.sender == coreCaller && keccak256(msg.data) == inputHash);
        VM.warp(block.timestamp + weight);
        bytes memory value = replyValue;
        assembly ("memory-safe") { return(add(value, 32), mload(value)) }
    }

    function count() external view returns (uint256) {
        return block.timestamp - 1000;
    }

    fallback() external {
        require(msg.sender == coreCaller && msg.sig == bytes4(0xcafef00d));
        VM.warp(block.timestamp + 1000);
        assembly ("memory-safe") {
            mstore(0, caller())
            mstore(32, address())
            calldatacopy(64, 0, calldatasize())
            return(0, add(64, calldatasize()))
        }
    }
}

/**
 * @notice Exactly two STATIC bytes leaves with independent lengths 0/1/31/32/33
 *         and independent legal paramTypes. Solc encodes original bytes values;
 *         full outputs/errors, reached prefixes and low-level success are checked.
 *         No arbitrary lengths, counts, nesting, gas or native proof is claimed.
 */
contract ClaimFetchedDynamicGetSymbolicTest is Test {
    struct Pair {
        bytes32[2] a;
        bytes32[2] b;
        uint8 sa;
        uint8 sb;
        uint8 ta;
        uint8 tb;
        bool twoA;
        bool twoB;
    }

    struct LateCase {
        Pair pair;
        bytes32 referenceWord;
        uint8 selected;
        uint8 cut;
        bool truncated;
    }

    struct CodecCase {
        Pair pair;
        bytes32 referenceWord;
        uint8 selected;
        uint8 mode;
        bool padding;
    }

    Assertions core;
    ClaimFetchedDynamicGetHost first;
    ClaimFetchedDynamicGetHost second;
    ClaimFetchedDynamicGetHost destination;
    ClaimFetchedDynamicGetHost unvisited;
    bytes4 constant ECHO = 0xcafef00d;

    function setUp() public {
        core = new Assertions();
        first = new ClaimFetchedDynamicGetHost(1);
        second = new ClaimFetchedDynamicGetHost(3);
        destination = new ClaimFetchedDynamicGetHost(1000);
        unvisited = new ClaimFetchedDynamicGetHost(9);
        destination.configure(address(core), bytes(""));
        unvisited.configure(address(core), abi.encode(uint256(0xbadc0de)));
    }

    function check_getFetchedDynamicBytesCalldata(Pair memory x) public {
        assumePair(x);
        bytes memory a = payload(x.a, x.sa);
        bytes memory b = payload(x.b, x.sb);
        InputParam[] memory args = new InputParam[](2);
        args[0] = fetched(first, abi.encode(a), x.ta, constraints(x.twoA, a.length));
        args[1] = fetched(second, abi.encode(b), x.tb, constraints(x.twoB, b.length));
        vm.warp(1000);
        (bool ok, bytes memory out) = invoke(args);
        assertTrue(ok);
        assertEq(out, bytes.concat(abi.encode(address(core), address(destination)), ECHO, abi.encode(a, b)));
        assertEq(first.count(), uint256(1004));
    }

    function check_getFetchedDynamicBytesLateWordFirstFailure(LateCase memory x) public {
        assumePair(x.pair);
        vm.assume(x.selected < 2 && x.cut < 6);
        bytes memory a = abi.encode(payload(x.pair.a, x.pair.sa));
        bytes memory b = abi.encode(payload(x.pair.b, x.pair.sb));
        uint256 actual = x.selected == 0 ? byteLength(x.pair.sa) : byteLength(x.pair.sb);
        if (!x.truncated) vm.assume(x.referenceWord != bytes32(actual));
        bytes memory selectedValue = x.selected == 0 ? a : b;
        if (x.truncated) selectedValue = prefix(selectedValue, cutLength(x.cut));
        Constraint[] memory cs = constraints(true, actual);
        cs[1].referenceData = x.truncated ? new bytes(31) : abi.encode(x.referenceWord);
        InputParam[] memory args = new InputParam[](2);
        if (x.selected == 0) {
            args[0] = fetched(first, selectedValue, x.pair.ta, cs);
            args[1] = skipped(x.pair.tb);
        } else {
            args[0] = fetched(first, a, x.pair.ta, constraints(true, byteLength(x.pair.sa)));
            args[1] = fetched(second, selectedValue, x.pair.tb, cs);
        }
        vm.warp(1000);
        (bool ok, bytes memory out) = invoke(args);
        assertFalse(ok);
        assertEq(
            out,
            x.truncated
                ? abi.encodeWithSelector(
                    ReturnDataOutOfBounds.selector, int256(selectedValue.length / 32), selectedValue.length
                )
                : failed(x.selected + 1, actual, x.referenceWord)
        );
        assertEq(first.count(), x.selected == 0 ? uint256(1) : uint256(4));
    }

    function check_getFetchedDynamicBytesConstraintCodecPriority(CodecCase memory x) public {
        assumePair(x.pair);
        vm.assume(x.selected < 2 && x.mode < 3);
        // mode0: own constraint beats codec; mode1: later constraint beats the
        // first component's codec; mode2: constraints pass, codec must reject.
        if (x.mode == 1) vm.assume(x.selected == 0);
        uint8 size = x.selected == 0 ? x.pair.sa : x.pair.sb;
        if (x.padding) vm.assume(size == 1 || size == 2 || size == 4);
        bytes memory a = abi.encode(payload(x.pair.a, x.pair.sa));
        bytes memory b = abi.encode(payload(x.pair.b, x.pair.sb));
        uint256 dirtyOffset;
        if (x.selected == 0) dirtyOffset = corrupt(a, size, x.padding);
        else dirtyOffset = corrupt(b, size, x.padding);
        uint256 failIndex = x.mode == 1 ? 1 : x.selected;
        uint256 actual = failIndex == 0 ? byteLength(x.pair.sa) : byteLength(x.pair.sb);
        if (x.mode != 2) vm.assume(x.referenceWord != bytes32(actual));
        Constraint[] memory ca = constraints(true, byteLength(x.pair.sa));
        Constraint[] memory cb = constraints(true, byteLength(x.pair.sb));
        if (x.mode != 2) {
            if (failIndex == 0) ca[1].referenceData = abi.encode(x.referenceWord);
            else cb[1].referenceData = abi.encode(x.referenceWord);
        }
        InputParam[] memory args = new InputParam[](2);
        args[0] = fetched(first, a, x.pair.ta, ca);
        args[1] = x.mode == 0 && x.selected == 0 ? skipped(x.pair.tb) : fetched(second, b, x.pair.tb, cb);
        vm.warp(1000);
        (bool ok, bytes memory out) = invoke(args);
        assertFalse(ok);
        bytes memory want = x.mode != 2
            ? failed(failIndex + 1, actual, x.referenceWord)
            : x.padding
                ? abi.encodeWithSelector(AbiCodec.InvalidComponentValue.selector, uint256(x.selected), dirtyOffset)
                : abi.encodeWithSelector(
                    AbiCodec.InvalidComponentEnvelope.selector,
                    uint256(x.selected),
                    x.selected == 0 ? a.length : b.length,
                    bytes32(uint256(64))
                );
        assertEq(out, want);
        assertEq(first.count(), x.mode == 0 && x.selected == 0 ? uint256(1) : uint256(4));
    }

    function assumePair(Pair memory x) internal pure {
        vm.assume(x.sa < 5 && x.sb < 5 && x.ta < 3 && x.tb < 3);
    }

    function constraints(bool two, uint256 n) internal pure returns (Constraint[] memory cs) {
        cs = new Constraint[](two ? 2 : 1);
        cs[0] = Constraint(two ? ConstraintType.SKIP : ConstraintType.EQ, two ? bytes("") : abi.encode(uint256(32)));
        if (two) cs[1] = Constraint(ConstraintType.EQ, abi.encode(n));
    }

    function fetched(ClaimFetchedDynamicGetHost h, bytes memory value, uint8 paramType, Constraint[] memory cs)
        internal
        returns (InputParam memory)
    {
        h.configure(address(core), value);
        return InputParam(
            InputParamType(paramType),
            InputParamFetcherType.STATIC_CALL,
            abi.encode(address(h), abi.encodeCall(ClaimFetchedDynamicGetHost.reply, (value))),
            cs
        );
    }

    function skipped(uint8 paramType) internal view returns (InputParam memory p) {
        p = InputParam(
            InputParamType(paramType),
            InputParamFetcherType.STATIC_CALL,
            abi.encode(
                address(unvisited), abi.encodeCall(ClaimFetchedDynamicGetHost.reply, (abi.encode(uint256(0xbadc0de))))
            ),
            new Constraint[](1)
        );
        p.constraints[0] = Constraint(ConstraintType.OR, hex"ff");
    }

    function invoke(InputParam[] memory args) internal view returns (bool, bytes memory) {
        InputParam memory target = InputParam(
            InputParamType.TARGET,
            InputParamFetcherType.RAW_BYTES,
            abi.encode(address(destination)),
            new Constraint[](0)
        );
        return address(core).staticcall(abi.encodeCall(Assertions.get, (target, ECHO, "(bytes,bytes)", args)));
    }

    function failed(uint256 param, uint256 actual, bytes32 referenceWord) internal pure returns (bytes memory) {
        return abi.encodeWithSelector(
            ConstraintFailed.selector,
            "",
            uint256(0),
            param,
            uint256(1),
            ConstraintType.EQ,
            bytes32(actual),
            abi.encode(referenceWord)
        );
    }

    function byteLength(uint8 size) internal pure returns (uint256) {
        if (size == 0) return 0;
        if (size == 1) return 1;
        if (size == 2) return 31;
        if (size == 3) return 32;
        return 33;
    }

    function cutLength(uint8 size) internal pure returns (uint256) {
        if (size == 0) return 0;
        if (size == 1) return 1;
        if (size == 2) return 31;
        if (size == 3) return 32;
        if (size == 4) return 33;
        return 63;
    }

    function payload(bytes32[2] memory words, uint8 size) internal pure returns (bytes memory out) {
        out = abi.encodePacked(words[0], words[1]);
        uint256 n = byteLength(size);
        assembly ("memory-safe") { mstore(out, n) }
    }

    function prefix(bytes memory value, uint256 n) internal pure returns (bytes memory out) {
        out = new bytes(n);
        for (uint256 i; i < n; i++) {
            out[i] = value[i];
        }
    }

    function corrupt(bytes memory value, uint8 size, bool padding) internal pure returns (uint256 offset) {
        if (!padding) {
            assembly ("memory-safe") { mstore(add(value, 32), 64) }
            return 0;
        }
        // Scan an independent solc encoding of a typed all-marker payload.
        // The first zero after that marker run is the first padding byte.
        bytes memory markers = new bytes(byteLength(size));
        for (uint256 i; i < markers.length; i++) {
            markers[i] = 0xa7;
        }
        bytes memory encoded = abi.encode(markers);
        bool seen;
        for (uint256 start; start < encoded.length; start += 32) {
            if (encoded[start] != 0xa7) continue;
            seen = true;
            for (uint256 i = start; i < encoded.length; i++) {
                if (encoded[i] == 0xa7) continue;
                offset = i;
                break;
            }
            break;
        }
        assert(seen && offset < encoded.length && encoded[offset] == 0);
        value[offset] = 0x7f;
    }

    function sample() internal pure returns (Pair memory x) {
        x.a = [bytes32(uint256(0x1234)), bytes32(uint256(0x117f))];
        x.b = [bytes32(uint256(0x7788)), bytes32(uint256(0x9911))];
        x.twoA = true;
        x.twoB = true;
    }

    function test_fetchedDynamicFixtureGuards() public {
        bytes memory value = abi.encode(bytes("sample"));
        first.configure(address(core), value);
        vm.warp(1000);
        (bool ok, bytes memory out) =
            address(first).staticcall(abi.encodeCall(ClaimFetchedDynamicGetHost.reply, (value)));
        assertFalse(ok);
        assertEq(out, bytes(""));
        vm.prank(address(core));
        (ok, out) = address(first).staticcall(abi.encodeCall(ClaimFetchedDynamicGetHost.reply, (bytes("wrong"))));
        assertFalse(ok);
        assertEq(out, bytes(""));
        assertEq(first.count(), uint256(0));
        vm.prank(address(core));
        (ok, out) = address(first).staticcall(abi.encodeCall(ClaimFetchedDynamicGetHost.reply, (value)));
        assertTrue(ok);
        assertEq(out, value);
        assertEq(first.count(), uint256(1));
        vm.warp(1000);
        (ok, out) = address(destination).staticcall(abi.encodePacked(ECHO, hex"117f"));
        assertFalse(ok);
        assertEq(out, bytes(""));
        vm.prank(address(core));
        (ok, out) = address(destination).staticcall(hex"deadbeef117f");
        assertFalse(ok);
        assertEq(out, bytes(""));
        assertEq(first.count(), uint256(0));
        vm.prank(address(core));
        (ok, out) = address(destination).staticcall(abi.encodePacked(ECHO, hex"117f"));
        assertTrue(ok);
        assertEq(out, bytes.concat(abi.encode(address(core), address(destination)), ECHO, hex"117f"));
        assertEq(first.count(), uint256(1000));
    }

    function test_fetchedDynamicCalldataSamples() public {
        vm.expectCall(address(first), abi.encodePacked(ClaimFetchedDynamicGetHost.reply.selector), uint64(225));
        vm.expectCall(address(second), abi.encodePacked(ClaimFetchedDynamicGetHost.reply.selector), uint64(225));
        vm.expectCall(address(destination), abi.encodePacked(ECHO), uint64(225));
        vm.expectCall(address(unvisited), abi.encodePacked(ClaimFetchedDynamicGetHost.reply.selector), uint64(0));
        Pair memory x = sample();
        for (uint8 a; a < 5; a++) {
            for (uint8 b; b < 5; b++) {
                for (uint8 t; t < 3; t++) {
                    for (uint8 u; u < 3; u++) {
                        x.sa = a;
                        x.sb = b;
                        x.ta = t;
                        x.tb = u;
                        x.twoA = t != 0;
                        x.twoB = u != 0;
                        check_getFetchedDynamicBytesCalldata(x);
                    }
                }
            }
        }
    }

    function test_fetchedDynamicLateWordSamples() public {
        vm.expectCall(address(first), abi.encodePacked(ClaimFetchedDynamicGetHost.reply.selector), uint64(350));
        vm.expectCall(address(second), abi.encodePacked(ClaimFetchedDynamicGetHost.reply.selector), uint64(175));
        vm.expectCall(address(destination), abi.encodePacked(ECHO), uint64(0));
        vm.expectCall(address(unvisited), abi.encodePacked(ClaimFetchedDynamicGetHost.reply.selector), uint64(0));
        LateCase memory x;
        x.pair = sample();
        x.referenceWord = bytes32(uint256(99));
        for (uint8 a; a < 5; a++) {
            for (uint8 b; b < 5; b++) {
                x.pair.sa = a;
                x.pair.sb = b;
                x.pair.ta = a % 3;
                x.pair.tb = b % 3;
                for (uint8 selected; selected < 2; selected++) {
                    x.selected = selected;
                    x.truncated = false;
                    check_getFetchedDynamicBytesLateWordFirstFailure(x);
                    x.truncated = true;
                    for (uint8 cut; cut < 6; cut++) {
                        x.cut = cut;
                        check_getFetchedDynamicBytesLateWordFirstFailure(x);
                    }
                }
            }
        }
    }

    function test_fetchedDynamicCodecPrioritySamples() public {
        vm.expectCall(address(first), abi.encodePacked(ClaimFetchedDynamicGetHost.reply.selector), uint64(200));
        vm.expectCall(address(second), abi.encodePacked(ClaimFetchedDynamicGetHost.reply.selector), uint64(160));
        vm.expectCall(address(destination), abi.encodePacked(ECHO), uint64(0));
        vm.expectCall(address(unvisited), abi.encodePacked(ClaimFetchedDynamicGetHost.reply.selector), uint64(0));
        CodecCase memory x;
        x.pair = sample();
        x.referenceWord = bytes32(uint256(99));
        for (uint8 a; a < 5; a++) {
            for (uint8 b; b < 5; b++) {
                x.pair.sa = a;
                x.pair.sb = b;
                x.pair.ta = a % 3;
                x.pair.tb = b % 3;
                for (uint8 selected; selected < 2; selected++) {
                    x.selected = selected;
                    for (uint8 mode; mode < 3; mode++) {
                        if (mode == 1 && selected == 1) continue;
                        x.mode = mode;
                        x.padding = false;
                        check_getFetchedDynamicBytesConstraintCodecPriority(x);
                        uint8 size = selected == 0 ? a : b;
                        if (size == 1 || size == 2 || size == 4) {
                            x.padding = true;
                            check_getFetchedDynamicBytesConstraintCodecPriority(x);
                        }
                    }
                }
            }
        }
    }
}
