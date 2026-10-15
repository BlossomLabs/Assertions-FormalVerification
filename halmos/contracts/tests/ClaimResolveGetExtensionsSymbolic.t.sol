// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../Assertions.sol";
import "../lib/AbiCodec.sol";

/**
 * @dev Exact raw replies and a caller/calldata echo. The test-only clock counts
 *      external executions under Halmos's retained cheatcode semantics; it is
 *      not deployable staticcall state and supplies no gas evidence.
 */
contract ClaimResolveGetHost {
    Vm constant VM = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    uint256 amount;
    uint256 returnLength;
    address expectedCaller;
    address expectedAccount;

    function configure(uint256 value, uint256 length, address caller_, address account_) external {
        amount = value;
        returnLength = length;
        expectedCaller = caller_;
        expectedAccount = account_;
    }

    function reply(bytes calldata data, address caller_) external {
        VM.warp(block.timestamp + 1);
        require(msg.sender == caller_);
        assembly ("memory-safe") {
            calldatacopy(0, data.offset, data.length)
            return(0, data.length)
        }
    }

    function balanceOf(address account) external {
        VM.warp(block.timestamp + 1);
        require(msg.sender == expectedCaller && account == expectedAccount);
        bytes memory data = abi.encode(amount, bytes32(uint256(0x93)), bytes32(uint256(0x7f)));
        uint256 length = returnLength;
        assembly ("memory-safe") { return(add(data, 32), length) }
    }

    function count() external view returns (uint256) {
        return block.timestamp - 1000;
    }

    fallback() external {
        VM.warp(block.timestamp + 10);
        assembly ("memory-safe") {
            mstore(0, caller())
            calldatacopy(32, 0, calldatasize())
            return(0, add(32, calldatasize()))
        }
    }
}

/**
 * @notice Bounded C14/C18/C21/W8 and C58/C59 extensions. Payload words are
 *         unrestricted, while byte lengths, argument counts and ABI layouts are
 *         literal cases. Solc independently encodes the COMPLETE destination
 *         calldata. Expected successful calls assert success before decoding.
 */
contract ClaimResolveGetExtensionsSymbolicTest is Test {
    struct Inner {
        uint8 number;
        bytes content;
    }

    struct Outer {
        uint256 marker;
        Inner inner;
    }

    Assertions core;
    ClaimResolveGetHost host;
    bytes4 constant ECHO = 0xcafef00d;

    function setUp() public {
        core = new Assertions();
        host = new ClaimResolveGetHost();
    }

    function check_resolveExactByteBoundaries(bytes32[3] memory words, uint8 size, uint8 paramType, bool fetched)
        public
    {
        vm.assume(size < 8 && paramType < 3);
        vm.warp(1000);
        bytes memory data = payload(words, size);
        InputParam memory p = fetched ? reply(data) : raw(data);
        p.paramType = InputParamType(paramType);
        (bool ok, bytes memory out) = address(core).staticcall(abi.encodeCall(Assertions.resolve, (p)));
        assertTrue(ok);
        assertEq(out, data);
        assertEq(host.count(), fetched ? 1 : 0);
    }

    function check_resolveFetchedConstraints(
        bytes32[3] memory words,
        bytes32[2] memory refs,
        uint8 size,
        uint8 paramType,
        bool two
    ) public {
        vm.assume(size < 8 && paramType < 3);
        vm.warp(1000);
        bytes memory data = payload(words, size);
        InputParam memory p = reply(data);
        p.paramType = InputParamType(paramType);
        p.constraints = new Constraint[](two ? 2 : 1);
        p.constraints[0] = Constraint(ConstraintType.EQ, abi.encode(refs[0]));
        if (two) p.constraints[1] = Constraint(ConstraintType.EQ, abi.encode(refs[1]));
        (bool ok, bytes memory out) = address(core).staticcall(abi.encodeCall(Assertions.resolve, (p)));
        uint256 n = byteLength(size);
        if (n < (two ? 64 : 32)) {
            assertFalse(ok);
            assertEq(out, abi.encodeWithSelector(ReturnDataOutOfBounds.selector, int256(n / 32), n));
        } else {
            bool firstBad = words[0] != refs[0];
            bool holds = !firstBad && (!two || words[1] == refs[1]);
            assertEq(ok, holds);
            assertEq(
                out,
                holds ? data : failed(firstBad ? 0 : 1, firstBad ? words[0] : words[1], firstBad ? refs[0] : refs[1])
            );
        }
        assertEq(host.count(), 1);
    }

    function check_resolveBalanceConstrained(uint256 value, bytes32 referenceWord, uint8 paramType, bool native)
        public
    {
        vm.assume(paramType < 3);
        vm.warp(1000);
        host.configure(value, 65, address(core), address(this));
        vm.deal(address(this), value);
        InputParam memory p = balance(native);
        p.paramType = InputParamType(paramType);
        p.constraints = new Constraint[](1);
        p.constraints[0] = Constraint(ConstraintType.EQ, abi.encode(referenceWord));
        (bool ok, bytes memory out) = address(core).staticcall(abi.encodeCall(Assertions.resolve, (p)));
        assertEq(ok, bytes32(value) == referenceWord);
        assertEq(out, ok ? abi.encode(value) : failed(0, bytes32(value), referenceWord));
        assertEq(host.count(), native ? 0 : 1);
    }

    function check_resolveBalanceBoundsBeforeMalformedPredicates(
        uint256 value,
        uint8 paramType,
        uint8 malformed,
        bool native
    ) public {
        vm.assume(paramType < 3 && malformed < 3);
        vm.warp(1000);
        host.configure(value, 65, address(core), address(this));
        vm.deal(address(this), value);
        InputParam memory p = balance(native);
        p.paramType = InputParamType(paramType);
        p.constraints = new Constraint[](2);
        p.constraints[0] = Constraint(
            malformed == 0 ? ConstraintType.EQ : malformed == 1 ? ConstraintType.IN : ConstraintType.OR, hex"ff"
        );
        (bool ok, bytes memory out) = address(core).staticcall(abi.encodeCall(Assertions.resolve, (p)));
        assertFalse(ok);
        assertEq(out, abi.encodeWithSelector(ReturnDataOutOfBounds.selector, int256(1), uint256(32)));
        assertEq(host.count(), native ? 0 : 1);
    }

    function check_resolveTokenReturnBoundaries(uint256 value, uint8 size, uint8 paramType, bool constrained) public {
        vm.assume(size < 8 && paramType < 3);
        vm.warp(1000);
        uint256 n = byteLength(size);
        host.configure(value, n, address(core), address(this));
        InputParam memory p = balance(false);
        p.paramType = InputParamType(paramType);
        if (constrained) {
            p.constraints = new Constraint[](1);
            p.constraints[0] = Constraint(ConstraintType.EQ, abi.encode(value));
        }
        (bool ok, bytes memory out) = address(core).staticcall(abi.encodeCall(Assertions.resolve, (p)));
        assertEq(ok, n >= 32);
        assertEq(
            out, n >= 32 ? abi.encode(value) : abi.encodeWithSelector(ReturnDataOutOfBounds.selector, int256(0), n)
        );
        assertEq(host.count(), 1);
    }

    function check_resolveBalanceDataLengths(bytes32[3] memory words, uint8 size, uint8 paramType) public view {
        vm.assume(size < 8 && paramType < 3);
        InputParam memory p = raw(payload(words, size));
        p.fetcherType = InputParamFetcherType.BALANCE;
        p.paramType = InputParamType(paramType);
        p.constraints = new Constraint[](1);
        p.constraints[0] = Constraint(ConstraintType.OR, hex"ff");
        (bool ok, bytes memory out) = address(core).staticcall(abi.encodeCall(Assertions.resolve, (p)));
        assertFalse(ok);
        assertEq(out, abi.encodeWithSelector(InvalidBalanceData.selector, uint256(0), uint256(0), byteLength(size)));
    }

    function check_resolveBoundsBeforeMalformedPredicates(
        bytes32[3] memory words,
        uint8 size,
        uint8 paramType,
        uint8 malformed,
        bool fetched
    ) public {
        vm.assume(size < 8 && paramType < 3 && malformed < 3);
        vm.warp(1000);
        bytes memory data = payload(words, size);
        uint256 n = byteLength(size);
        InputParam memory p = fetched ? reply(data) : raw(data);
        p.paramType = InputParamType(paramType);
        p.constraints = new Constraint[](n < 32 ? 1 : n < 64 ? 2 : 3);
        p.constraints[0] = Constraint(
            malformed == 0 ? ConstraintType.EQ : malformed == 1 ? ConstraintType.IN : ConstraintType.OR, hex"ff"
        );
        (bool ok, bytes memory out) = address(core).staticcall(abi.encodeCall(Assertions.resolve, (p)));
        assertFalse(ok);
        assertEq(out, abi.encodeWithSelector(ReturnDataOutOfBounds.selector, int256(n / 32), n));
        assertEq(host.count(), fetched ? 1 : 0);
    }

    function check_getIndependentDynamicArguments(bytes32[3] memory a, bytes32[3] memory b, uint8 sa, uint8 sb) public {
        vm.assume(sa < 8 && sb < 8);
        bytes memory x = payload(a, sa);
        bytes memory y = payload(b, sb);
        InputParam[] memory args = new InputParam[](2);
        args[0] = raw(abi.encode(x));
        args[1] = raw(abi.encode(y));
        getMatches("(bytes,bytes)", args, abi.encode(x, y));
    }

    function check_getNestedTupleArguments(
        uint256 marker,
        uint8 number,
        bytes32[3] memory a,
        bytes32[3] memory b,
        uint8 sa,
        uint8 sb
    ) public {
        vm.assume(sa < 5 && sb < 5);
        Outer memory item = Outer(marker, Inner(number, payload(a, sa)));
        bytes memory y = payload(b, sb);
        InputParam[] memory args = new InputParam[](2);
        args[0] = raw(abi.encode(item));
        args[1] = raw(abi.encode(y));
        getMatches("((uint256,(uint8,bytes)),bytes)", args, abi.encode(item, y));
    }

    function check_getFixedDynamicArrayArguments(
        bytes32[3] memory a,
        bytes32[3] memory b,
        uint8 sa,
        uint8 sb,
        bytes32 word
    ) public {
        vm.assume(sa < 5 && sb < 5);
        bytes[2] memory values = [payload(a, sa), payload(b, sb)];
        InputParam[] memory args = new InputParam[](2);
        args[0] = raw(abi.encode(values));
        args[1] = raw(abi.encode(word));
        getMatches("(bytes[2],bytes32)", args, abi.encode(values, word));
    }

    function check_getUnknownScalarNames(bytes32[4] memory words) public {
        InputParam[] memory args = new InputParam[](4);
        for (uint256 i; i < 4; i++) {
            args[i] = raw(abi.encode(words[i]));
        }
        // The fictitious names use the unrestricted one-word wire shape. Solc
        // encodes the independently known bytes32 values, not those names.
        getMatches("(foo,uint7,uint08,bytes33)", args, abi.encode(words[0], words[1], words[2], words[3]));
    }

    function check_getComponentErrorPriority(bytes32 word, uint8 badCase, uint8 faultCase) public {
        vm.assume(badCase < 3 && faultCase < 4);
        vm.warp(1000);
        uint256 bad = badCase == 0 ? 0 : badCase == 1 ? 1 : 2;
        InputParam[] memory args = new InputParam[](3);
        bool dynamic = faultCase >= 2;
        for (uint256 i; i < 3; i++) {
            if (i < bad) {
                args[i] = raw(dynamic ? abi.encode(bytes("a")) : abi.encode(uint8(7)));
            } else if (faultCase == 0) {
                args[i] = raw(abi.encodePacked(word, bytes1(0x7f)));
            } else if (faultCase == 1) {
                args[i] = raw(abi.encode(word | bytes32(uint256(1) << 255)));
            } else if (faultCase == 2) {
                args[i] = raw(abi.encode(word | bytes32(uint256(1))));
            } else {
                args[i] = raw(
                    abi.encode(
                        uint256(32), uint256(1), (word & bytes32(uint256(0xff) << 248)) | bytes32(uint256(1) << 240)
                    )
                );
            }
        }
        (bool ok, bytes memory out) = address(core)
            .staticcall(
                abi.encodeCall(
                    Assertions.get,
                    (
                        raw(abi.encode(address(host))),
                        ECHO,
                        dynamic ? "(bytes,bytes,bytes)" : "(uint8,uint8,uint8)",
                        args
                    )
                )
            );
        assertFalse(ok);
        bytes memory want;
        if (faultCase == 0) {
            want = abi.encodeWithSelector(AbiCodec.InvalidComponentLength.selector, bad, uint256(32), uint256(33));
        } else if (faultCase == 1) {
            want = abi.encodeWithSelector(AbiCodec.InvalidComponentValue.selector, bad, uint256(0));
        } else if (faultCase == 2) {
            want = abi.encodeWithSelector(
                AbiCodec.InvalidComponentEnvelope.selector, bad, uint256(32), word | bytes32(uint256(1))
            );
        } else {
            want = abi.encodeWithSelector(AbiCodec.InvalidComponentValue.selector, bad, uint256(65));
        }
        assertEq(out, want);
        assertEq(host.count(), 0, "codec rejection precedes destination execution");
    }

    function check_getDescriptorCountErrorPriority(bytes32 word, bool malformed, bool extra) public {
        vm.warp(1000);
        InputParam[] memory args = new InputParam[](extra ? 3 : 1);
        for (uint256 i; i < args.length; i++) {
            args[i] = raw(abi.encode(word | bytes32(uint256(1) << 255)));
        }
        (bool ok, bytes memory out) = address(core)
            .staticcall(
                abi.encodeCall(
                    Assertions.get,
                    (raw(abi.encode(address(host))), ECHO, malformed ? "(uint8[0],bytes)" : "(uint8,bytes)", args)
                )
            );
        assertFalse(ok);
        assertEq(
            out,
            malformed
                ? abi.encodeWithSelector(InvalidTypeDescriptor.selector, uint256(8))
                : abi.encodeWithSelector(
                    AbiCodec.ComponentCountMismatch.selector, uint256(2), extra ? uint256(3) : uint256(1)
                )
        );
        assertEq(host.count(), 0);
    }

    function getMatches(string memory descriptor, InputParam[] memory args, bytes memory encoded) internal {
        vm.warp(1000);
        (bool ok, bytes memory out) = address(core)
            .staticcall(abi.encodeCall(Assertions.get, (raw(abi.encode(address(host))), ECHO, descriptor, args)));
        assertTrue(ok);
        assertEq(out, bytes.concat(abi.encode(address(core)), ECHO, encoded));
        assertEq(host.count(), 10);
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

    function payload(bytes32[3] memory words, uint8 size) internal pure returns (bytes memory out) {
        out = abi.encodePacked(words[0], words[1], words[2]);
        uint256 n = byteLength(size);
        assembly ("memory-safe") { mstore(out, n) }
    }

    function raw(bytes memory data) internal pure returns (InputParam memory) {
        return InputParam(InputParamType.CALL_DATA, InputParamFetcherType.RAW_BYTES, data, new Constraint[](0));
    }

    function reply(bytes memory data) internal view returns (InputParam memory) {
        return InputParam(
            InputParamType.CALL_DATA,
            InputParamFetcherType.STATIC_CALL,
            abi.encode(address(host), abi.encodeCall(ClaimResolveGetHost.reply, (data, address(core)))),
            new Constraint[](0)
        );
    }

    function balance(bool native) internal view returns (InputParam memory) {
        return InputParam(
            InputParamType.CALL_DATA,
            InputParamFetcherType.BALANCE,
            abi.encodePacked(native ? address(0) : address(host), address(this)),
            new Constraint[](0)
        );
    }

    function failed(uint256 index, bytes32 actual, bytes32 referenceWord) internal pure returns (bytes memory) {
        return abi.encodeWithSelector(
            ConstraintFailed.selector,
            "",
            uint256(0),
            uint256(0),
            index,
            ConstraintType.EQ,
            actual,
            abi.encode(referenceWord)
        );
    }

    function test_resolveByteBoundarySamples() public {
        vm.expectCall(address(host), abi.encodePacked(ClaimResolveGetHost.reply.selector), uint64(72));
        vm.expectCall(address(host), abi.encodeCall(ClaimResolveGetHost.balanceOf, (address(this))), uint64(48));
        bytes32[3] memory words = [bytes32(uint256(42)), bytes32(uint256(93)), bytes32(uint256(7))];
        for (uint8 s; s < 8; s++) {
            for (uint8 p; p < 3; p++) {
                check_resolveExactByteBoundaries(words, s, p, false);
                check_resolveExactByteBoundaries(words, s, p, true);
                check_resolveFetchedConstraints(words, [words[0], words[1]], s, p, true);
                check_resolveFetchedConstraints(words, [words[0] ^ bytes32(uint256(1)), words[1]], s, p, false);
                check_resolveTokenReturnBoundaries(42, s, p, false);
                check_resolveTokenReturnBoundaries(93, s, p, true);
                check_resolveBalanceDataLengths(words, s, p);
            }
        }
    }

    function test_resolvePredicatePrioritySamples() public {
        vm.expectCall(address(host), abi.encodePacked(ClaimResolveGetHost.reply.selector), uint64(72));
        vm.expectCall(address(host), abi.encodeCall(ClaimResolveGetHost.balanceOf, (address(this))), uint64(15));
        bytes32[3] memory words = [bytes32(uint256(42)), bytes32(uint256(93)), bytes32(uint256(7))];
        for (uint8 s; s < 8; s++) {
            for (uint8 p; p < 3; p++) {
                for (uint8 f; f < 3; f++) {
                    check_resolveBoundsBeforeMalformedPredicates(words, s, p, f, false);
                    check_resolveBoundsBeforeMalformedPredicates(words, s, p, f, true);
                }
            }
        }
        for (uint8 p; p < 3; p++) {
            check_resolveBalanceConstrained(42, bytes32(uint256(42)), p, true);
            check_resolveBalanceConstrained(42, bytes32(uint256(93)), p, false);
            check_resolveBalanceConstrained(42, bytes32(uint256(93)), p, true);
            check_resolveBalanceConstrained(42, bytes32(uint256(42)), p, false);
            for (uint8 f; f < 3; f++) {
                check_resolveBalanceBoundsBeforeMalformedPredicates(42, p, f, false);
                check_resolveBalanceBoundsBeforeMalformedPredicates(42, p, f, true);
            }
        }
    }

    function test_getDynamicGeometries() public {
        vm.expectCall(address(host), abi.encodePacked(ECHO), uint64(115));
        bytes32[3] memory a = [bytes32(uint256(42)), bytes32(uint256(93)), bytes32(uint256(7))];
        bytes32[3] memory b = [bytes32(uint256(19)), bytes32(uint256(73)), bytes32(uint256(5))];
        for (uint8 sa; sa < 8; sa++) {
            for (uint8 sb; sb < 8; sb++) {
                check_getIndependentDynamicArguments(a, b, sa, sb);
                if (sa < 5 && sb < 5) {
                    check_getNestedTupleArguments(123, 7, a, b, sa, sb);
                    check_getFixedDynamicArrayArguments(a, b, sa, sb, bytes32(uint256(93)));
                }
            }
        }
        bytes32[4] memory words =
            [bytes32(type(uint256).max), bytes32(uint256(1) << 255), bytes32(uint256(42)), bytes32(uint256(7))];
        check_getUnknownScalarNames(words);
    }

    function test_getExactErrorPriorities() public {
        vm.expectCall(address(host), abi.encodePacked(ECHO), uint64(0));
        for (uint8 i; i < 3; i++) {
            for (uint8 f; f < 4; f++) {
                check_getComponentErrorPriority(bytes32(uint256(42)), i, f);
            }
        }
        check_getDescriptorCountErrorPriority(bytes32(uint256(42)), false, false);
        check_getDescriptorCountErrorPriority(bytes32(uint256(42)), false, true);
        check_getDescriptorCountErrorPriority(bytes32(uint256(42)), true, false);
        check_getDescriptorCountErrorPriority(bytes32(uint256(42)), true, true);
    }
}
