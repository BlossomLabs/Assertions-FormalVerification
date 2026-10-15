// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../Assertions.sol";
import "../lib/AbiCodec.sol";

/**
 * @dev Stored raw replies have independent complete-input and core-caller
 *      guards. The test-only weighted clock is commutative and has multiplicity
 *      aliases; it supplies no exact count, order, gas or native proof credit.
 *      Concrete exact-call companions are required separately.
 */
contract ClaimFetchedMixedNarrowGetHost {
    Vm constant VM = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    uint256 immutable weight;
    address expectedCaller;
    bytes storedReply;
    bytes32 expectedInputHash;

    constructor(uint256 weight_) {
        weight = weight_;
    }

    function configure(address caller_, bytes calldata value) external {
        expectedCaller = caller_;
        storedReply = value;
        expectedInputHash = keccak256(abi.encodeCall(this.reply, (value)));
    }

    function reply(bytes calldata) external {
        require(msg.sender == expectedCaller && keccak256(msg.data) == expectedInputHash);
        VM.warp(block.timestamp + weight);
        bytes memory value = storedReply;
        assembly ("memory-safe") {
            return(add(value, 32), mload(value))
        }
    }

    function observedWeight() external view returns (uint256) {
        return block.timestamp - 1000;
    }

    fallback() external {
        require(msg.sender == expectedCaller && msg.sig == bytes4(0xcafef00d));
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
 * @notice Exactly two constrained STATIC leaves: bytes of length 0/1/31/32/33
 *         beside a uint8 or int8 scalar, in either order. Independent solc
 *         encoding/decoding, complete raw outputs and exact errors are checked.
 *         The three declarations grant no proof credit before reviewed runs.
 * @dev No arbitrary lengths/counts, other shapes/fetchers, signed predicate
 *      family, bounds, duplicate-entry, gas or native-bytecode claim is added.
 *      Operations.byteAt's real ABI is (bytes,int256), not these narrow fixtures.
 */
contract ClaimFetchedMixedNarrowGetSymbolicTest is Test {
    struct Geometry {
        bytes32[2] payloadWords;
        uint8 lengthCase;
        uint8 firstType;
        uint8 secondType;
        bool signedScalar;
        bool scalarFirst;
    }

    struct CanonicalCase {
        Geometry geometry;
        uint8 unsignedValue;
        int8 signedValue;
    }

    struct WordCase {
        Geometry geometry;
        bytes32 scalarWord;
    }

    struct FaultCase {
        WordCase pair;
        bytes32 referenceWord;
        bool padding;
        bool laterConstraint;
    }

    Assertions core;
    ClaimFetchedMixedNarrowGetHost first;
    ClaimFetchedMixedNarrowGetHost second;
    ClaimFetchedMixedNarrowGetHost destination;
    bytes4 constant ECHO = 0xcafef00d;
    bytes32 constant MARKERS = 0xa7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7;

    function setUp() public {
        core = new Assertions();
        first = new ClaimFetchedMixedNarrowGetHost(1);
        second = new ClaimFetchedMixedNarrowGetHost(3);
        destination = new ClaimFetchedMixedNarrowGetHost(1000);
        destination.configure(address(core), bytes(""));
    }

    function check_getFetchedMixedNarrowCalldata(CanonicalCase memory x) public {
        assumeGeometry(x.geometry);
        bytes memory data = payload(x.geometry);
        bytes32 scalarWord =
            x.geometry.signedScalar ? firstWord(abi.encode(x.signedValue)) : firstWord(abi.encode(x.unsignedValue));
        assertTrue(assertSolcCanonicality(scalarWord, x.geometry.signedScalar));
        InputParam[] memory args = arguments(x.geometry, abi.encode(data), scalarWord, false, bytes32(0));
        vm.warp(1000);
        (bool ok, bytes memory out) = invoke(x.geometry, args);
        assertTrue(ok, "get must succeed on original canonical mixed values");
        assertEq(out, echoed(typedTuple(x.geometry, data, x.unsignedValue, x.signedValue)));
        assertEq(first.observedWeight(), uint256(1004), "finite weighted observation only");
    }

    function check_getFetchedMixedNarrowCanonicality(WordCase memory x) public {
        assumeGeometry(x.geometry);
        bytes memory data = payload(x.geometry);
        bool canonical = assertSolcCanonicality(x.scalarWord, x.geometry.signedScalar);
        InputParam[] memory args = arguments(x.geometry, abi.encode(data), x.scalarWord, false, bytes32(0));
        vm.warp(1000);
        (bool ok, bytes memory out) = invoke(x.geometry, args);
        assertEq(ok, canonical, "mixed get acceptance must agree with independent solc canonicality");
        if (canonical) {
            assertTrue(ok, "valid-case core reverts cannot be discarded");
            assertEq(
                out,
                echoed(typedTuple(x.geometry, data, uint8(uint256(x.scalarWord)), int8(uint8(uint256(x.scalarWord)))))
            );
            assertEq(first.observedWeight(), uint256(1004), "finite weighted observation only");
        } else {
            assertFalse(ok);
            assertEq(
                out,
                abi.encodeWithSelector(
                    AbiCodec.InvalidComponentValue.selector,
                    x.geometry.scalarFirst ? uint256(0) : uint256(1),
                    uint256(0)
                )
            );
            assertEq(first.observedWeight(), uint256(4), "finite weighted observation only");
        }
    }

    function check_getFetchedMixedCompetingFaults(FaultCase memory x) public {
        assumeGeometry(x.pair.geometry);
        // Select dirty original words using independent solc typed encoding,
        // then check the caught decoder. No code-under-test refusal filters them.
        vm.assume(
            x.pair.scalarWord != firstWord(independentScalarEncoding(x.pair.scalarWord, x.pair.geometry.signedScalar))
        );
        assertFalse(assertSolcCanonicality(x.pair.scalarWord, x.pair.geometry.signedScalar));
        if (x.padding) {
            vm.assume(
                x.pair.geometry.lengthCase == 1 || x.pair.geometry.lengthCase == 2 || x.pair.geometry.lengthCase == 4
            );
        }
        bytes memory dynamicValue = abi.encode(payload(x.pair.geometry));
        uint256 dirtyOffset = corruptDynamic(dynamicValue, x.pair.geometry.lengthCase, x.padding);
        bytes32 laterActual =
            x.pair.geometry.scalarFirst ? bytes32(byteLength(x.pair.geometry.lengthCase)) : x.pair.scalarWord;
        if (x.laterConstraint) {
            vm.assume(x.referenceWord != laterActual);
        }
        InputParam[] memory args =
            arguments(x.pair.geometry, dynamicValue, x.pair.scalarWord, x.laterConstraint, x.referenceWord);
        vm.warp(1000);
        (bool ok, bytes memory out) = invoke(x.pair.geometry, args);
        assertFalse(ok);
        bytes memory want;
        if (x.laterConstraint) {
            want = failed(x.pair.geometry.scalarFirst ? uint256(1) : uint256(0), laterActual, x.referenceWord);
        } else if (x.pair.geometry.scalarFirst) {
            want = abi.encodeWithSelector(AbiCodec.InvalidComponentValue.selector, uint256(0), uint256(0));
        } else if (x.padding) {
            want = abi.encodeWithSelector(AbiCodec.InvalidComponentValue.selector, uint256(0), dirtyOffset);
        } else {
            want = abi.encodeWithSelector(
                AbiCodec.InvalidComponentEnvelope.selector, uint256(0), dynamicValue.length, bytes32(uint256(64))
            );
        }
        assertEq(out, want);
        assertEq(first.observedWeight(), uint256(4), "finite weighted observation only");
    }

    function solcUint8(bytes calldata data) external pure returns (uint8) {
        return abi.decode(data, (uint8));
    }

    function solcInt8(bytes calldata data) external pure returns (int8) {
        return abi.decode(data, (int8));
    }

    function independentScalarEncoding(bytes32 originalWord, bool signedScalar) internal pure returns (bytes memory) {
        if (signedScalar) {
            return abi.encode(int8(uint8(uint256(originalWord))));
        }
        return abi.encode(uint8(uint256(originalWord)));
    }

    function assertSolcCanonicality(bytes32 originalWord, bool signedScalar) internal view returns (bool canonical) {
        bytes memory independentEncoding = independentScalarEncoding(originalWord, signedScalar);
        canonical = abi.encode(originalWord).length == independentEncoding.length
            && originalWord == firstWord(independentEncoding);
        (bool solcOk, bytes memory solcOutput) = signedScalar
            ? address(this).staticcall(abi.encodeCall(this.solcInt8, (abi.encode(originalWord))))
            : address(this).staticcall(abi.encodeCall(this.solcUint8, (abi.encode(originalWord))));
        assertEq(solcOk, canonical, "caught solc decoder must agree with complete typed encoding");
        if (canonical) {
            assertTrue(solcOk, "unexpected valid-case oracle revert must fail");
            assertEq(solcOutput, independentEncoding, "complete independent solc output");
        }
    }

    function assumeGeometry(Geometry memory g) internal pure {
        vm.assume(g.lengthCase < 5 && g.firstType < 3 && g.secondType < 3);
    }

    function descriptor(Geometry memory g) internal pure returns (string memory) {
        if (g.signedScalar) {
            if (g.scalarFirst) {
                return "(int8,bytes)";
            }
            return "(bytes,int8)";
        }
        if (g.scalarFirst) {
            return "(uint8,bytes)";
        }
        return "(bytes,uint8)";
    }

    function typedTuple(Geometry memory g, bytes memory data, uint8 originalUnsigned, int8 originalSigned)
        internal
        pure
        returns (bytes memory)
    {
        if (g.signedScalar) {
            if (g.scalarFirst) {
                return abi.encode(originalSigned, data);
            }
            return abi.encode(data, originalSigned);
        }
        if (g.scalarFirst) {
            return abi.encode(originalUnsigned, data);
        }
        return abi.encode(data, originalUnsigned);
    }

    function arguments(
        Geometry memory g,
        bytes memory dynamicValue,
        bytes32 scalarWord,
        bool laterConstraint,
        bytes32 referenceWord
    ) internal returns (InputParam[] memory args) {
        Constraint[] memory dynamicConstraints = new Constraint[](2);
        dynamicConstraints[0] = Constraint(ConstraintType.SKIP, bytes(""));
        dynamicConstraints[1] = Constraint(ConstraintType.EQ, abi.encode(byteLength(g.lengthCase)));
        Constraint[] memory scalarConstraints = new Constraint[](1);
        scalarConstraints[0] = Constraint(ConstraintType.EQ, abi.encode(scalarWord));
        args = new InputParam[](2);
        if (g.scalarFirst) {
            if (laterConstraint) {
                dynamicConstraints[1].referenceData = abi.encode(referenceWord);
            }
            args[0] = fetched(first, abi.encode(scalarWord), g.firstType, scalarConstraints);
            args[1] = fetched(second, dynamicValue, g.secondType, dynamicConstraints);
        } else {
            if (laterConstraint) {
                scalarConstraints[0].referenceData = abi.encode(referenceWord);
            }
            args[0] = fetched(first, dynamicValue, g.firstType, dynamicConstraints);
            args[1] = fetched(second, abi.encode(scalarWord), g.secondType, scalarConstraints);
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

    function invoke(Geometry memory g, InputParam[] memory args) internal view returns (bool, bytes memory) {
        InputParam memory target = InputParam(
            InputParamType.TARGET,
            InputParamFetcherType.RAW_BYTES,
            abi.encode(address(destination)),
            new Constraint[](0)
        );
        return address(core).staticcall(abi.encodeCall(Assertions.get, (target, ECHO, descriptor(g), args)));
    }

    function echoed(bytes memory independentTuple) internal view returns (bytes memory) {
        return bytes.concat(abi.encode(address(core), address(destination)), ECHO, independentTuple);
    }

    function failed(uint256 constraintIndex, bytes32 actual, bytes32 referenceWord)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encodeWithSelector(
            ConstraintFailed.selector,
            "",
            uint256(0),
            uint256(2),
            constraintIndex,
            ConstraintType.EQ,
            actual,
            abi.encode(referenceWord)
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
        return 33;
    }

    function payload(Geometry memory g) internal pure returns (bytes memory out) {
        out = abi.encodePacked(g.payloadWords[0], g.payloadWords[1]);
        uint256 n = byteLength(g.lengthCase);
        assembly ("memory-safe") {
            mstore(out, n)
        }
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
        // At most four words, then at most 32 bytes in a partial marker word.
        // The all-marker word is skipped as a word, so the 33-byte case does
        // not scan its full ABI encoding byte by byte past global loop70.
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
