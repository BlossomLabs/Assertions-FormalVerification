// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../Assertions.sol";
import "../Operations.sol";
import "../lib/AbiCodec.sol";
import "./ClaimFetchedMixedNarrowGetSymbolic.t.sol";

/**
 *  @dev Exact typed native regression fixture; no production API is added.
 */
contract ClaimFetchedMixedNarrowNativeTarget {
    Vm constant VM = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    address expectedCaller;
    bytes32 expectedPayloadHash;
    bytes32 expectedScalarHash;

    function configure(address caller_, bytes calldata originalPayload, bytes calldata originalScalar) external {
        expectedCaller = caller_;
        expectedPayloadHash = keccak256(originalPayload);
        expectedScalarHash = keccak256(originalScalar);
    }

    function guard(bytes calldata data, bytes memory scalar) internal {
        require(msg.sender == expectedCaller && keccak256(data) == expectedPayloadHash);
        require(keccak256(scalar) == expectedScalarHash);
        VM.warp(block.timestamp + 1000);
    }

    function bytesUint(bytes calldata data, uint8 value) external returns (address, address, bytes memory, uint8) {
        guard(data, abi.encode(value));
        return (msg.sender, address(this), data, value);
    }

    function uintBytes(uint8 value, bytes calldata data) external returns (address, address, bytes memory, uint8) {
        guard(data, abi.encode(value));
        return (msg.sender, address(this), data, value);
    }

    function bytesInt(bytes calldata data, int8 value) external returns (address, address, bytes memory, int8) {
        guard(data, abi.encode(value));
        return (msg.sender, address(this), data, value);
    }

    function intBytes(int8 value, bytes calldata data) external returns (address, address, bytes memory, int8) {
        guard(data, abi.encode(value));
        return (msg.sender, address(this), data, value);
    }
}

/**
 * @notice Native companions for the four bounded mixed narrow geometries.
 *         Exact native calls complement the commutative symbolic clock.
 *         Operations.byteAt is separately exercised with its real int256 ABI.
 * @dev These test declarations have not been executed at source-review time.
 *      No arbitrary lengths/counts, gas, order or native-bytecode credit follows.
 */
contract ClaimFetchedMixedNarrowGetTest is Test {
    struct Row {
        uint8 lengthCase;
        uint8 firstType;
        uint8 secondType;
        bool signedScalar;
        bool scalarFirst;
    }

    Assertions core;
    Operations ops;
    ClaimFetchedMixedNarrowGetHost first;
    ClaimFetchedMixedNarrowGetHost second;
    ClaimFetchedMixedNarrowGetHost rawDestination;
    ClaimFetchedMixedNarrowNativeTarget typedDestination;
    bytes4 constant ECHO = 0xcafef00d;
    bytes32 constant MARKERS = 0xa7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7;

    function setUp() public {
        core = new Assertions();
        ops = new Operations();
        first = new ClaimFetchedMixedNarrowGetHost(1);
        second = new ClaimFetchedMixedNarrowGetHost(3);
        rawDestination = new ClaimFetchedMixedNarrowGetHost(1000);
        typedDestination = new ClaimFetchedMixedNarrowNativeTarget();
        rawDestination.configure(address(core), bytes(""));
    }

    function test_mixedNarrowCanonicalSamples() public {
        // 900 independently selected rows, each sent to typed and raw fixtures.
        // Totals are declared once per matcher, never re-armed inside a loop.
        vm.expectCall(address(first), abi.encodePacked(ClaimFetchedMixedNarrowGetHost.reply.selector), uint64(1800));
        vm.expectCall(address(second), abi.encodePacked(ClaimFetchedMixedNarrowGetHost.reply.selector), uint64(1800));
        vm.expectCall(address(rawDestination), abi.encodePacked(ECHO), uint64(900));
        expectTypedTotals(225);
        Row memory r;
        for (uint8 family; family < 2; family++) {
            r.signedScalar = family == 1;
            for (uint8 order; order < 2; order++) {
                r.scalarFirst = order == 1;
                for (uint8 length; length < 5; length++) {
                    r.lengthCase = length;
                    for (uint8 a; a < 3; a++) {
                        r.firstType = a;
                        for (uint8 b; b < 3; b++) {
                            r.secondType = b;
                            for (uint8 value; value < 5; value++) {
                                canonicalSample(r, unsignedSample(value), signedSample(value));
                            }
                        }
                    }
                }
            }
        }
    }

    function test_mixedNarrowCanonicalitySamples() public {
        vm.expectCall(address(first), abi.encodePacked(ClaimFetchedMixedNarrowGetHost.reply.selector), uint64(120));
        vm.expectCall(address(second), abi.encodePacked(ClaimFetchedMixedNarrowGetHost.reply.selector), uint64(120));
        vm.expectCall(address(rawDestination), abi.encodePacked(ECHO), uint64(60));
        expectTypedTotals(0);
        Row memory r;
        r.secondType = 2;
        for (uint8 family; family < 2; family++) {
            r.signedScalar = family == 1;
            for (uint8 order; order < 2; order++) {
                r.scalarFirst = order == 1;
                for (uint8 length; length < 5; length++) {
                    r.lengthCase = length;
                    for (uint8 sample; sample < 6; sample++) {
                        canonicalitySample(r, wordSample(r.signedScalar, sample), sample < 3);
                    }
                }
            }
        }
    }

    function test_mixedNarrowCompetingFaultSamples() public {
        vm.expectCall(address(first), abi.encodePacked(ClaimFetchedMixedNarrowGetHost.reply.selector), uint64(64));
        vm.expectCall(address(second), abi.encodePacked(ClaimFetchedMixedNarrowGetHost.reply.selector), uint64(64));
        vm.expectCall(address(rawDestination), abi.encodePacked(ECHO), uint64(0));
        expectTypedTotals(0);
        Row memory r;
        r.firstType = 1;
        r.secondType = 2;
        for (uint8 family; family < 2; family++) {
            r.signedScalar = family == 1;
            for (uint8 order; order < 2; order++) {
                r.scalarFirst = order == 1;
                for (uint8 length; length < 5; length++) {
                    r.lengthCase = length;
                    competingSample(r, false, false);
                    competingSample(r, false, true);
                    if (length == 1 || length == 2 || length == 4) {
                        competingSample(r, true, false);
                        competingSample(r, true, true);
                    }
                }
            }
        }
    }

    function test_mixedExactCallsBytesUint() public {
        exactSample(false, false);
    }

    function test_mixedExactCallsUintBytes() public {
        exactSample(false, true);
    }

    function test_mixedExactCallsBytesInt() public {
        exactSample(true, false);
    }

    function test_mixedExactCallsIntBytes() public {
        exactSample(true, true);
    }

    function test_mixedFixtureGuards() public {
        bytes memory value = abi.encode(bytes("guard"));
        first.configure(address(core), value);
        vm.expectCall(address(first), abi.encodePacked(ClaimFetchedMixedNarrowGetHost.reply.selector), uint64(3));
        vm.expectCall(address(first), hex"deadbeef", uint64(1));
        vm.warp(1000);
        (bool ok, bytes memory out) =
            address(first).staticcall(abi.encodeCall(ClaimFetchedMixedNarrowGetHost.reply, (value)));
        assertFalse(ok);
        assertEq(out, bytes(""));
        vm.prank(address(core));
        (ok, out) = address(first).staticcall(abi.encodeCall(ClaimFetchedMixedNarrowGetHost.reply, (bytes("wrong"))));
        assertFalse(ok);
        assertEq(out, bytes(""));
        vm.prank(address(core));
        (ok, out) = address(first).staticcall(hex"deadbeef");
        assertFalse(ok);
        assertEq(out, bytes(""));
        assertEq(first.observedWeight(), uint256(0));
        vm.prank(address(core));
        (ok, out) = address(first).staticcall(abi.encodeCall(ClaimFetchedMixedNarrowGetHost.reply, (value)));
        assertTrue(ok);
        assertEq(out, value);
        assertEq(first.observedWeight(), uint256(1));
        rawGuards();
        expectTypedTotals(4);
        vm.expectCall(address(typedDestination), hex"deadbeef", uint64(4));
        Row memory r;
        for (uint8 family; family < 2; family++) {
            r.signedScalar = family == 1;
            for (uint8 order; order < 2; order++) {
                r.scalarFirst = order == 1;
                typedGuards(r);
            }
        }
    }

    function test_mixedByteAtActualInt256() public {
        // The actual operation takes int256. Narrow validation is covered by
        // exact typed fixtures, not by misnaming the production operation ABI.
        vm.expectCall(address(first), abi.encodePacked(ClaimFetchedMixedNarrowGetHost.reply.selector), uint64(72));
        vm.expectCall(address(second), abi.encodePacked(ClaimFetchedMixedNarrowGetHost.reply.selector), uint64(72));
        vm.expectCall(address(ops), abi.encodePacked(Operations.byteAt.selector), uint64(72));
        vm.expectCall(address(rawDestination), abi.encodePacked(ECHO), uint64(0));
        expectTypedTotals(0);
        Row memory r;
        for (uint8 length = 1; length < 5; length++) {
            r.lengthCase = length;
            bytes memory data = samplePayload(length);
            for (uint8 a; a < 3; a++) {
                r.firstType = a;
                for (uint8 b; b < 3; b++) {
                    r.secondType = b;
                    byteAtSample(r, data, int256(0));
                    byteAtSample(r, data, int256(-1));
                }
            }
        }
    }

    function canonicalSample(Row memory r, uint8 originalUnsigned, int8 originalSigned) internal {
        bytes memory data = samplePayload(r.lengthCase);
        bytes memory scalar = r.signedScalar ? abi.encode(originalSigned) : abi.encode(originalUnsigned);
        typedDestination.configure(address(core), data, scalar);
        InputParam[] memory args = arguments(r, abi.encode(data), firstWord(scalar), false, bytes32(0));
        vm.warp(1000);
        (bool ok, bytes memory out) = get(address(typedDestination), typedSelector(r), descriptor(r), args);
        assertTrue(ok);
        assertDecoded(r, data, originalUnsigned, originalSigned, out);
        assertEq(first.observedWeight(), uint256(1004));
        vm.warp(1000);
        (ok, out) = get(address(rawDestination), ECHO, descriptor(r), args);
        assertTrue(ok);
        assertEq(out, rawEcho(tuple(r, data, originalUnsigned, originalSigned)));
        assertEq(first.observedWeight(), uint256(1004));
    }

    function canonicalitySample(Row memory r, bytes32 originalWord, bool canonical) internal {
        (bool solcOk, bytes memory solcOut) = r.signedScalar
            ? address(this).staticcall(abi.encodeCall(this.solcInt8, (abi.encode(originalWord))))
            : address(this).staticcall(abi.encodeCall(this.solcUint8, (abi.encode(originalWord))));
        assertEq(solcOk, canonical);
        if (canonical) {
            assertEq(solcOut, abi.encode(originalWord));
        }
        bytes memory data = samplePayload(r.lengthCase);
        InputParam[] memory args = arguments(r, abi.encode(data), originalWord, false, bytes32(0));
        vm.warp(1000);
        (bool ok, bytes memory out) = get(address(rawDestination), ECHO, descriptor(r), args);
        assertEq(ok, canonical);
        if (canonical) {
            assertTrue(ok);
            assertEq(out, rawEcho(tuple(r, data, uint8(uint256(originalWord)), int8(uint8(uint256(originalWord))))));
            assertEq(first.observedWeight(), uint256(1004));
        } else {
            assertFalse(ok);
            assertEq(
                out,
                abi.encodeWithSelector(
                    AbiCodec.InvalidComponentValue.selector, r.scalarFirst ? uint256(0) : uint256(1), uint256(0)
                )
            );
            assertEq(first.observedWeight(), uint256(4));
        }
    }

    function competingSample(Row memory r, bool padding, bool laterConstraint) internal {
        bytes32 scalarWord = r.signedScalar ? bytes32(uint256(255)) : bytes32(uint256(256));
        bytes memory dynamicValue = abi.encode(samplePayload(r.lengthCase));
        uint256 dirtyOffset = corruptDynamic(dynamicValue, r.lengthCase, padding);
        bytes32 actual = r.scalarFirst ? bytes32(byteLength(r.lengthCase)) : scalarWord;
        bytes32 referenceWord = actual ^ bytes32(uint256(1));
        InputParam[] memory args = arguments(r, dynamicValue, scalarWord, laterConstraint, referenceWord);
        vm.warp(1000);
        (bool ok, bytes memory out) = get(address(rawDestination), ECHO, descriptor(r), args);
        assertFalse(ok);
        bytes memory want;
        if (laterConstraint) {
            want = abi.encodeWithSelector(
                ConstraintFailed.selector,
                "",
                uint256(0),
                uint256(2),
                r.scalarFirst ? uint256(1) : uint256(0),
                ConstraintType.EQ,
                actual,
                abi.encode(referenceWord)
            );
        } else if (r.scalarFirst) {
            want = abi.encodeWithSelector(AbiCodec.InvalidComponentValue.selector, uint256(0), uint256(0));
        } else if (padding) {
            want = abi.encodeWithSelector(AbiCodec.InvalidComponentValue.selector, uint256(0), dirtyOffset);
        } else {
            want = abi.encodeWithSelector(
                AbiCodec.InvalidComponentEnvelope.selector, uint256(0), dynamicValue.length, bytes32(uint256(64))
            );
        }
        assertEq(out, want);
        assertEq(first.observedWeight(), uint256(4));
    }

    function exactSample(bool signedScalar, bool scalarFirst) internal {
        Row memory r = Row(4, 0, 2, signedScalar, scalarFirst);
        bytes memory data = samplePayload(4);
        bytes memory scalar = signedScalar ? abi.encode(int8(-1)) : abi.encode(uint8(128));
        typedDestination.configure(address(core), data, scalar);
        bytes memory dynamicValue = abi.encode(data);
        vm.expectCall(
            address(first),
            abi.encodeCall(ClaimFetchedMixedNarrowGetHost.reply, (scalarFirst ? scalar : dynamicValue)),
            uint64(1)
        );
        vm.expectCall(
            address(second),
            abi.encodeCall(ClaimFetchedMixedNarrowGetHost.reply, (scalarFirst ? dynamicValue : scalar)),
            uint64(1)
        );
        vm.expectCall(address(typedDestination), bytes.concat(typedSelector(r), tuple(r, data, 128, -1)), uint64(1));
        vm.expectCall(address(rawDestination), abi.encodePacked(ECHO), uint64(0));
        InputParam[] memory args = arguments(r, dynamicValue, firstWord(scalar), false, bytes32(0));
        vm.warp(1000);
        (bool ok, bytes memory out) = get(address(typedDestination), typedSelector(r), descriptor(r), args);
        assertTrue(ok);
        assertDecoded(r, data, 128, -1, out);
        assertEq(first.observedWeight(), uint256(1004));
    }

    function rawGuards() internal {
        vm.expectCall(address(rawDestination), abi.encodePacked(ECHO), uint64(2));
        vm.expectCall(address(rawDestination), hex"deadbeef", uint64(1));
        vm.warp(1000);
        (bool ok, bytes memory out) = address(rawDestination).staticcall(abi.encodePacked(ECHO, hex"117f"));
        assertFalse(ok);
        assertEq(out, bytes(""));
        vm.prank(address(core));
        (ok, out) = address(rawDestination).staticcall(hex"deadbeef");
        assertFalse(ok);
        assertEq(out, bytes(""));
        assertEq(first.observedWeight(), uint256(0));
        vm.prank(address(core));
        (ok, out) = address(rawDestination).staticcall(abi.encodePacked(ECHO, hex"117f"));
        assertTrue(ok);
        assertEq(out, rawEcho(hex"117f"));
        assertEq(first.observedWeight(), uint256(1000));
    }

    function typedGuards(Row memory r) internal {
        bytes memory data = bytes("guard");
        bytes memory scalar = r.signedScalar ? abi.encode(int8(-1)) : abi.encode(uint8(128));
        typedDestination.configure(address(core), data, scalar);
        bytes memory callData = bytes.concat(typedSelector(r), tuple(r, data, 128, -1));
        vm.warp(1000);
        (bool ok, bytes memory out) = address(typedDestination).staticcall(callData);
        assertFalse(ok);
        assertEq(out, bytes(""));
        vm.prank(address(core));
        (ok, out) =
            address(typedDestination).staticcall(bytes.concat(typedSelector(r), tuple(r, bytes("wrong"), 128, -1)));
        assertFalse(ok);
        assertEq(out, bytes(""));
        vm.prank(address(core));
        (ok, out) = address(typedDestination).staticcall(bytes.concat(typedSelector(r), tuple(r, data, 129, 1)));
        assertFalse(ok);
        assertEq(out, bytes(""));
        vm.prank(address(core));
        (ok, out) = address(typedDestination).staticcall(hex"deadbeef");
        assertFalse(ok);
        assertEq(out, bytes(""));
        assertEq(first.observedWeight(), uint256(0));
        vm.prank(address(core));
        (ok, out) = address(typedDestination).staticcall(callData);
        assertTrue(ok);
        assertDecoded(r, data, 128, -1, out);
        assertEq(first.observedWeight(), uint256(1000));
    }

    function byteAtSample(Row memory r, bytes memory data, int256 index) internal {
        InputParam[] memory args = arguments(r, abi.encode(data), firstWord(abi.encode(index)), false, bytes32(0));
        bytes memory expectedByte = new bytes(1);
        expectedByte[0] = index == 0 ? data[0] : data[data.length - 1];
        vm.warp(1000);
        (bool ok, bytes memory out) = get(address(ops), Operations.byteAt.selector, "(bytes,int256)", args);
        assertTrue(ok);
        assertEq(out, abi.encode(expectedByte));
        assertEq(abi.decode(out, (bytes)), expectedByte);
        assertEq(first.observedWeight(), uint256(4));
    }

    function solcUint8(bytes calldata data) external pure returns (uint8) {
        return abi.decode(data, (uint8));
    }

    function solcInt8(bytes calldata data) external pure returns (int8) {
        return abi.decode(data, (int8));
    }

    function assertDecoded(
        Row memory r,
        bytes memory originalPayload,
        uint8 originalUnsigned,
        int8 originalSigned,
        bytes memory out
    ) internal view {
        if (r.signedScalar) {
            assertEq(out, abi.encode(address(core), address(typedDestination), originalPayload, originalSigned));
            (address caller_, address receiver_, bytes memory data, int8 scalar) =
                abi.decode(out, (address, address, bytes, int8));
            assertEq(caller_, address(core));
            assertEq(receiver_, address(typedDestination));
            assertEq(data, originalPayload);
            assertEq(scalar, originalSigned);
        } else {
            assertEq(out, abi.encode(address(core), address(typedDestination), originalPayload, originalUnsigned));
            (address caller_, address receiver_, bytes memory data, uint8 scalar) =
                abi.decode(out, (address, address, bytes, uint8));
            assertEq(caller_, address(core));
            assertEq(receiver_, address(typedDestination));
            assertEq(data, originalPayload);
            assertEq(scalar, originalUnsigned);
        }
    }

    function expectTypedTotals(uint64 perShape) internal {
        vm.expectCall(
            address(typedDestination),
            abi.encodePacked(ClaimFetchedMixedNarrowNativeTarget.bytesUint.selector),
            perShape
        );
        vm.expectCall(
            address(typedDestination),
            abi.encodePacked(ClaimFetchedMixedNarrowNativeTarget.uintBytes.selector),
            perShape
        );
        vm.expectCall(
            address(typedDestination), abi.encodePacked(ClaimFetchedMixedNarrowNativeTarget.bytesInt.selector), perShape
        );
        vm.expectCall(
            address(typedDestination), abi.encodePacked(ClaimFetchedMixedNarrowNativeTarget.intBytes.selector), perShape
        );
    }

    function typedSelector(Row memory r) internal pure returns (bytes4) {
        if (r.signedScalar) {
            if (r.scalarFirst) {
                return ClaimFetchedMixedNarrowNativeTarget.intBytes.selector;
            }
            return ClaimFetchedMixedNarrowNativeTarget.bytesInt.selector;
        }
        if (r.scalarFirst) {
            return ClaimFetchedMixedNarrowNativeTarget.uintBytes.selector;
        }
        return ClaimFetchedMixedNarrowNativeTarget.bytesUint.selector;
    }

    function descriptor(Row memory r) internal pure returns (string memory) {
        if (r.signedScalar) {
            if (r.scalarFirst) {
                return "(int8,bytes)";
            }
            return "(bytes,int8)";
        }
        if (r.scalarFirst) {
            return "(uint8,bytes)";
        }
        return "(bytes,uint8)";
    }

    function tuple(Row memory r, bytes memory data, uint8 unsignedValue, int8 signedValue)
        internal
        pure
        returns (bytes memory)
    {
        if (r.signedScalar) {
            if (r.scalarFirst) {
                return abi.encode(signedValue, data);
            }
            return abi.encode(data, signedValue);
        }
        if (r.scalarFirst) {
            return abi.encode(unsignedValue, data);
        }
        return abi.encode(data, unsignedValue);
    }

    function arguments(
        Row memory r,
        bytes memory dynamicValue,
        bytes32 scalarWord,
        bool laterConstraint,
        bytes32 referenceWord
    ) internal returns (InputParam[] memory args) {
        Constraint[] memory dynamicConstraints = new Constraint[](2);
        dynamicConstraints[0] = Constraint(ConstraintType.SKIP, bytes(""));
        dynamicConstraints[1] = Constraint(ConstraintType.EQ, abi.encode(byteLength(r.lengthCase)));
        Constraint[] memory scalarConstraints = new Constraint[](1);
        scalarConstraints[0] = Constraint(ConstraintType.EQ, abi.encode(scalarWord));
        args = new InputParam[](2);
        if (r.scalarFirst) {
            if (laterConstraint) {
                dynamicConstraints[1].referenceData = abi.encode(referenceWord);
            }
            args[0] = fetched(first, abi.encode(scalarWord), r.firstType, scalarConstraints);
            args[1] = fetched(second, dynamicValue, r.secondType, dynamicConstraints);
        } else {
            if (laterConstraint) {
                scalarConstraints[0].referenceData = abi.encode(referenceWord);
            }
            args[0] = fetched(first, dynamicValue, r.firstType, dynamicConstraints);
            args[1] = fetched(second, abi.encode(scalarWord), r.secondType, scalarConstraints);
        }
    }

    function fetched(
        ClaimFetchedMixedNarrowGetHost host,
        bytes memory value,
        uint8 paramType,
        Constraint[] memory constraints
    ) internal returns (InputParam memory) {
        host.configure(address(core), value);
        return InputParam(
            InputParamType(paramType),
            InputParamFetcherType.STATIC_CALL,
            abi.encode(address(host), abi.encodeCall(ClaimFetchedMixedNarrowGetHost.reply, (value))),
            constraints
        );
    }

    function get(address targetAddress, bytes4 selector, string memory argumentTypes, InputParam[] memory args)
        internal
        view
        returns (bool, bytes memory)
    {
        InputParam memory target = InputParam(
            InputParamType.TARGET, InputParamFetcherType.RAW_BYTES, abi.encode(targetAddress), new Constraint[](0)
        );
        return address(core).staticcall(abi.encodeCall(Assertions.get, (target, selector, argumentTypes, args)));
    }

    function rawEcho(bytes memory data) internal view returns (bytes memory) {
        return bytes.concat(abi.encode(address(core), address(rawDestination)), ECHO, data);
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
        return 33;
    }

    function samplePayload(uint8 size) internal pure returns (bytes memory data) {
        data = new bytes(byteLength(size));
        for (uint256 i; i < data.length; i++) {
            data[i] = bytes1(uint8(17 + 3 * i));
        }
    }

    function unsignedSample(uint8 sample) internal pure returns (uint8) {
        if (sample == 0) {
            return 0;
        }
        if (sample == 1) {
            return 1;
        }
        if (sample == 2) {
            return 127;
        }
        if (sample == 3) {
            return 128;
        }
        return 255;
    }

    function signedSample(uint8 sample) internal pure returns (int8) {
        if (sample == 0) {
            return -128;
        }
        if (sample == 1) {
            return -1;
        }
        if (sample == 2) {
            return 0;
        }
        if (sample == 3) {
            return 1;
        }
        return 127;
    }

    function wordSample(bool signedScalar, uint8 sample) internal pure returns (bytes32) {
        if (signedScalar) {
            if (sample == 0) {
                return firstWord(abi.encode(int8(-128)));
            }
            if (sample == 1) {
                return firstWord(abi.encode(int8(-1)));
            }
            if (sample == 2) {
                return bytes32(uint256(127));
            }
            if (sample == 3) {
                return bytes32(uint256(255));
            }
            if (sample == 4) {
                return bytes32((type(uint256).max & ~uint256(255)) | uint256(127));
            }
            return bytes32(uint256(128));
        }
        if (sample == 0) {
            return bytes32(0);
        }
        if (sample == 1) {
            return bytes32(uint256(255));
        }
        if (sample == 2) {
            return bytes32(uint256(128));
        }
        if (sample == 3) {
            return bytes32(uint256(256));
        }
        if (sample == 4) {
            return bytes32(type(uint256).max);
        }
        return bytes32(uint256(1) << 255);
    }

    function firstWord(bytes memory value) internal pure returns (bytes32 word) {
        assert(value.length >= 32);
        assembly ("memory-safe") {
            word := mload(add(value, 32))
        }
    }

    function corruptDynamic(bytes memory value, uint8 size, bool padding) internal pure returns (uint256 offset) {
        if (!padding) {
            assembly ("memory-safe") {
                mstore(add(value, 32), 64)
            }
            return 0;
        }
        bytes memory markers = new bytes(byteLength(size));
        for (uint256 i; i < markers.length; i++) {
            markers[i] = 0xa7;
        }
        bytes memory independentlyEncoded = abi.encode(markers);
        for (uint256 start; start < independentlyEncoded.length; start += 32) {
            bytes32 candidate;
            assembly ("memory-safe") {
                candidate := mload(add(add(independentlyEncoded, 32), start))
            }
            if (candidate == MARKERS || bytes1(candidate) != bytes1(0xa7)) {
                continue;
            }
            for (uint256 i; i < 32; i++) {
                if (independentlyEncoded[start + i] == 0xa7) {
                    continue;
                }
                offset = start + i;
                assert(offset > 0 && offset < independentlyEncoded.length);
                assert(independentlyEncoded[offset] == 0 && independentlyEncoded[offset - 1] == 0xa7);
                assert(offset < value.length);
                value[offset] = 0x7f;
                return offset;
            }
        }
        assert(false);
    }
}
