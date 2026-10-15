// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../Assertions.sol";

/**
 * @dev Test-only clock events survive reverted subcalls in Halmos. Reply costs
 * one event, fail ten, and the destination one hundred. No production source
 * in these properties reads time. Foundry samples cross-check exact call counts.
 */
contract ClaimCoreControlHost {
    Vm constant VM = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    function reply(bytes calldata data) external {
        VM.warp(block.timestamp + 1);
        assembly ("memory-safe") {
            calldatacopy(0, data.offset, data.length)
            return(0, data.length)
        }
    }

    function fail(bytes calldata data) external {
        VM.warp(block.timestamp + 10);
        assembly ("memory-safe") {
            calldatacopy(0, data.offset, data.length)
            revert(0, data.length)
        }
    }

    function destination(uint256, uint256, uint256) external {
        VM.warp(block.timestamp + 100);
    }

    function ping() external {
        VM.warp(block.timestamp + 100);
    }

    function count() external view returns (uint256) {
        return block.timestamp - 1000;
    }
}

/**
 * @notice C56/C64/C74/C76: exact get operand errors, bounded dynamic branch
 * results, probe guard precedence, and selected nested core errors. Calls that
 * should succeed assert success; ordinary failures explicitly exclude Halmos's
 * gas artifact. The reserved signal property has no such exclusion.
 */
contract ClaimCoreControlExtensionsSymbolicTest is Test {
    Assertions core;
    ClaimCoreControlHost host;

    function setUp() public {
        core = new Assertions();
        host = new ClaimCoreControlHost();
    }

    function check_controlGetTargetError(uint96 upper, bytes32 referenceWord) public {
        vm.warp(1000);
        bytes32 word = bytes32((uint256(upper) << 160) | uint160(address(host)));
        InputParam memory target = eq(abi.encode(word), referenceWord);
        InputParam[] memory args = new InputParam[](0);
        (bool ok, bytes memory out) = address(core)
            .staticcall(abi.encodeCall(Assertions.get, (target, ClaimCoreControlHost.ping.selector, "()", args)));
        if (word != referenceWord) {
            assertFalse(ok);
            assertEq(out, failed(0, 0, word, referenceWord));
        } else if (upper != 0) {
            assertFalse(ok);
            assertEq(out, abi.encodeWithSelector(InvalidAddressWord.selector, uint256(0), word));
        } else {
            assertTrue(ok);
            assertEq(out, bytes(""));
        }
        assertEq(host.count(), word == referenceWord && upper == 0 ? 100 : 0);
    }

    function check_controlGetFirstArgumentError(bytes32[3] memory words, uint8 badCase, bool fetched) public {
        vm.assume(badCase < 3);
        vm.warp(1000);
        uint256 bad = badCase == 0 ? 0 : badCase == 1 ? 1 : 2;
        InputParam[] memory args = new InputParam[](3);
        for (uint256 i; i < 3; i++) {
            args[i] = fetched ? reply(abi.encode(words[i])) : raw(abi.encode(words[i]));
            args[i].constraints = new Constraint[](1);
            // Every later operand also fails, so the exact first failure is
            // observable; no ABI codec or destination call may precede it.
            args[i].constraints[0] =
                Constraint(ConstraintType.EQ, abi.encode(i >= bad ? words[i] ^ bytes32(uint256(1)) : words[i]));
        }
        (bool ok, bytes memory out) = address(core)
            .staticcall(
                abi.encodeCall(
                    Assertions.get,
                    (
                        raw(abi.encode(address(host))),
                        ClaimCoreControlHost.destination.selector,
                        "(uint256,uint256,uint256)",
                        args
                    )
                )
            );
        bytes32 actual = bad == 0 ? words[0] : bad == 1 ? words[1] : words[2];
        assertFalse(ok);
        assertEq(out, failed(bad + 1, 0, actual, actual ^ bytes32(uint256(1))));
        assertEq(host.count(), fetched ? bad + 1 : 0);
    }

    function check_controlCondRawBytes(bytes32[3] memory words, uint8 size, bool truth, bool fetched) public {
        vm.assume(size < 7);
        vm.warp(1000);
        bytes memory value = payload(words, size);
        InputParam memory winner = fetched ? reply(value) : raw(value);
        InputParam memory loser =
            operand(address(host), abi.encodeCall(ClaimCoreControlHost.fail, (abi.encode(words[2]))));
        (bool ok, bytes memory out) = address(core)
            .staticcall(
                abi.encodeCall(
                    Assertions.cond,
                    (raw(abi.encode(truth ? uint256(7) : 0)), truth ? winner : loser, truth ? loser : winner)
                )
            );
        assertTrue(ok);
        assertEq(out, value);
        assertEq(host.count(), fetched ? 1 : 0, "losing branch must not execute");
    }

    function check_controlCondDynamicConstraints(
        bytes32[3] memory words,
        uint8 size,
        bool truth,
        bool fetched,
        bytes32 ref
    ) public {
        vm.assume(size < 7);
        vm.warp(1000);
        bytes memory value = abi.encode(payload(words, size));
        InputParam memory winner = fetched ? reply(value) : raw(value);
        winner.constraints = new Constraint[](2);
        winner.constraints[0] = Constraint(ConstraintType.EQ, abi.encode(uint256(32)));
        winner.constraints[1] = Constraint(ConstraintType.EQ, abi.encode(ref));
        InputParam memory loser =
            operand(address(host), abi.encodeCall(ClaimCoreControlHost.fail, (abi.encode(words[2]))));
        (bool ok, bytes memory out) = address(core)
            .staticcall(
                abi.encodeCall(
                    Assertions.cond,
                    (raw(abi.encode(truth ? uint256(7) : 0)), truth ? winner : loser, truth ? loser : winner)
                )
            );
        bytes32 actual = bytes32(payloadLength(size));
        assertEq(ok, actual == ref);
        assertEq(out, actual == ref ? value : failed(truth ? 1 : 2, 1, actual, ref));
        assertEq(host.count(), fetched ? 1 : 0);
    }

    function check_controlProbeNonCallGuards(
        bool balance,
        uint8 countCase,
        bool malformed,
        uint8 paramType,
        bytes4 selector
    ) public {
        vm.assume(countCase < 4 && paramType < 3);
        vm.warp(1000);
        InputParam memory p = reply(abi.encode(uint256(42)));
        p.fetcherType = balance ? InputParamFetcherType.BALANCE : InputParamFetcherType.RAW_BYTES;
        p.paramType = InputParamType(paramType);
        p.constraints = new Constraint[](countCase == 0 ? 0 : countCase == 1 ? 1 : countCase == 2 ? 2 : 3);
        if (malformed) p.paramData = hex"ff";
        (bool ok, bytes memory out) = address(core).staticcall(abi.encodeCall(Assertions.revertData, (p, selector)));
        assertFalse(ok);
        assertEq(out, abi.encodeWithSelector(Assertions.RevertProbeNotACall.selector, uint8(p.fetcherType)));
        assertEq(host.count(), 0);
    }

    function check_controlProbeConstraintGuards(uint8 countCase, bool malformed, bytes4 selector) public {
        vm.assume(countCase < 3);
        vm.warp(1000);
        InputParam memory p = reply(abi.encode(uint256(42)));
        uint256 n = countCase == 0 ? 1 : countCase == 1 ? 2 : 3;
        p.constraints = new Constraint[](n);
        if (malformed) p.paramData = hex"ff";
        (bool ok, bytes memory out) = address(core).staticcall(abi.encodeCall(Assertions.revertData, (p, selector)));
        assertFalse(ok);
        assertEq(out, abi.encodeWithSelector(Assertions.RevertProbeConstrained.selector, n));
        assertEq(host.count(), 0);
    }

    function check_controlProbeNestedConstraint(bytes32 value, bytes32 ref, bool wrap, uint8 selectorCase) public view {
        vm.assume(value != ref && selectorCase < 3);
        bytes memory inner = abi.encodeCall(Assertions.resolve, (eq(abi.encode(value), ref)));
        bytes memory reason = failed(0, 0, value, ref);
        if (wrap) {
            reason = abi.encodeWithSelector(CallFailed.selector, address(core), inner);
            inner = abi.encodeCall(Assertions.resolve, (operand(address(core), inner)));
        }
        probe(operand(address(core), inner), reason, selectorCase);
    }

    function check_controlProbeNestedCallFailure(bytes32 value, bool wrap, uint8 selectorCase) public {
        vm.assume(selectorCase < 3);
        vm.warp(1000);
        bytes memory data = abi.encodeCall(ClaimCoreControlHost.fail, (abi.encode(value)));
        bytes memory reason = abi.encodeWithSelector(CallFailed.selector, address(host), data);
        bytes memory inner = abi.encodeCall(Assertions.resolve, (operand(address(host), data)));
        if (wrap) {
            reason = abi.encodeWithSelector(CallFailed.selector, address(core), inner);
            inner = abi.encodeCall(Assertions.resolve, (operand(address(core), inner)));
        }
        probe(operand(address(core), inner), reason, selectorCase);
        assertEq(host.count(), 10);
    }

    function check_controlProbeNestedReservedSignal(uint8 depthCase) public {
        vm.assume(depthCase < 3);
        vm.warp(1000);
        InputParam memory p = operand(address(host), abi.encodeCall(ClaimCoreControlHost.fail, (signal())));
        uint256 depth = depthCase == 0 ? 0 : depthCase == 1 ? 1 : 2;
        for (uint256 i; i < depth; i++) {
            p = operand(address(core), abi.encodeCall(Assertions.resolve, (p)));
        }
        (bool ok, bytes memory out) = address(core).staticcall(abi.encodeCall(Assertions.revertData, (p, bytes4(0))));
        assertFalse(ok);
        assertEq(out, signal());
        assertEq(host.count(), 10);
    }

    function probe(InputParam memory p, bytes memory reason, uint8 selectorCase) internal view {
        bytes4 actual = bytes4(reason);
        bytes4 selector = selectorCase == 0 ? bytes4(0) : selectorCase == 1 ? actual : bytes4(0xdeadbeef);
        (bool ok, bytes memory out) = address(core).staticcall(abi.encodeCall(Assertions.revertData, (p, selector)));
        vm.assume(ok || keccak256(out) != keccak256(signal()));
        assertEq(ok, selectorCase != 2);
        bytes memory want = selectorCase == 0
            ? reason
            : selectorCase == 1
                ? withoutSelector(reason)
                : abi.encodeWithSelector(Assertions.UnexpectedRevertData.selector, selector, actual);
        assertEq(out, want);
    }

    function raw(bytes memory data) internal pure returns (InputParam memory) {
        return InputParam(InputParamType.CALL_DATA, InputParamFetcherType.RAW_BYTES, data, new Constraint[](0));
    }

    function operand(address target, bytes memory data) internal pure returns (InputParam memory) {
        return InputParam(
            InputParamType.CALL_DATA, InputParamFetcherType.STATIC_CALL, abi.encode(target, data), new Constraint[](0)
        );
    }

    function reply(bytes memory data) internal view returns (InputParam memory) {
        return operand(address(host), abi.encodeCall(ClaimCoreControlHost.reply, (data)));
    }

    function eq(bytes memory data, bytes32 ref) internal pure returns (InputParam memory p) {
        p = raw(data);
        p.constraints = new Constraint[](1);
        p.constraints[0] = Constraint(ConstraintType.EQ, abi.encode(ref));
    }

    function failed(uint256 operandIndex, uint256 constraintIndex, bytes32 actual, bytes32 ref)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encodeWithSelector(
            ConstraintFailed.selector,
            "",
            uint256(0),
            operandIndex,
            constraintIndex,
            ConstraintType.EQ,
            actual,
            abi.encode(ref)
        );
    }

    function signal() internal pure returns (bytes memory) {
        return abi.encodeWithSelector(Assertions.SubcallOutOfGas.selector);
    }

    function payloadLength(uint8 size) internal pure returns (uint256) {
        return size == 0 ? 0 : size == 1 ? 1 : size == 2 ? 31 : size == 3 ? 32 : size == 4 ? 33 : size == 5 ? 64 : 65;
    }

    function payload(bytes32[3] memory words, uint8 size) internal pure returns (bytes memory data) {
        data = abi.encodePacked(words);
        uint256 n = payloadLength(size);
        assembly ("memory-safe") { mstore(data, n) }
    }

    function withoutSelector(bytes memory reason) internal pure returns (bytes memory out) {
        out = new bytes(reason.length - 4);
        assembly ("memory-safe") { mcopy(add(out, 32), add(reason, 36), mload(out)) }
    }

    function test_controlGetSamples() public {
        check_controlGetTargetError(7, bytes32(uint256(42)));
        check_controlGetTargetError(7, bytes32((uint256(7) << 160) | uint160(address(host))));
        check_controlGetTargetError(0, bytes32(uint256(uint160(address(host)))));
        bytes32[3] memory words = [bytes32(uint256(42)), bytes32(uint256(93)), bytes32(uint256(7))];
        vm.expectCall(address(host), abi.encodeCall(ClaimCoreControlHost.reply, (abi.encode(words[0]))), uint64(3));
        vm.expectCall(address(host), abi.encodeCall(ClaimCoreControlHost.reply, (abi.encode(words[1]))), uint64(2));
        vm.expectCall(address(host), abi.encodeCall(ClaimCoreControlHost.reply, (abi.encode(words[2]))), uint64(1));
        for (uint8 i; i < 3; i++) {
            check_controlGetFirstArgumentError(words, i, false);
            check_controlGetFirstArgumentError(words, i, true);
        }
    }

    function test_controlCondSamples() public {
        bytes32[3] memory words = [bytes32(uint256(42)), bytes32(uint256(93)), bytes32(uint256(7))];
        vm.expectCall(address(host), abi.encodeCall(ClaimCoreControlHost.fail, (abi.encode(words[2]))), uint64(0));
        for (uint8 i; i < 7; i++) {
            check_controlCondRawBytes(words, i, false, false);
            vm.expectCall(address(host), abi.encodeCall(ClaimCoreControlHost.reply, (payload(words, i))), uint64(1));
            check_controlCondRawBytes(words, i, true, true);
            check_controlCondDynamicConstraints(words, i, true, false, bytes32(payloadLength(i)));
            check_controlCondDynamicConstraints(words, i, false, true, bytes32(uint256(99)));
        }
    }

    function test_controlProbeGuardSamples() public {
        for (uint8 i; i < 4; i++) {
            check_controlProbeNonCallGuards(false, i, false, 0, bytes4(0));
            check_controlProbeNonCallGuards(true, i, true, 2, bytes4(0x11223344));
        }
        for (uint8 i; i < 3; i++) {
            check_controlProbeConstraintGuards(i, false, bytes4(0));
            check_controlProbeConstraintGuards(i, true, bytes4(0x11223344));
        }
    }

    function test_controlProbeNestedSamples() public {
        for (uint8 i; i < 3; i++) {
            check_controlProbeNestedConstraint(bytes32(uint256(42)), bytes32(uint256(93)), false, i);
            check_controlProbeNestedConstraint(bytes32(uint256(42)), bytes32(uint256(93)), true, i);
            check_controlProbeNestedCallFailure(bytes32(uint256(42)), false, i);
            check_controlProbeNestedCallFailure(bytes32(uint256(42)), true, i);
            check_controlProbeNestedReservedSignal(i);
        }
    }
}
