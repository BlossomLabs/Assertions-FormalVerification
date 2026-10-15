// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../Assertions.sol";
import "../lib/AbiCodec.sol";

/**
 * @dev Core-caller guards and test-only observations. A leaf costs one clock
 *      event even if it reverts; the destination costs ten and echoes its
 *      actual caller/calldata. No production closure here reads the clock.
 */
contract ClaimNestedPriorityHost {
    Vm constant VM = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    function reply(bytes calldata data, address caller_) external {
        VM.warp(block.timestamp + 1);
        require(msg.sender == caller_);
        assembly ("memory-safe") {
            calldatacopy(0, data.offset, data.length)
            return(0, data.length)
        }
    }

    function fail(bytes calldata data, address caller_) external {
        VM.warp(block.timestamp + 1);
        require(msg.sender == caller_);
        assembly ("memory-safe") {
            calldatacopy(0, data.offset, data.length)
            revert(0, data.length)
        }
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
 * @notice Fixed three-operand gather/get trees, resolve depths 0/1/2,
 *         duplicate entries, failure wrappers and resolution-before-codec
 *         priority. Ordinary nested core failures become CallFailed around
 *         the outer STATIC_CALL; deep reasons are not transparently forwarded.
 */
contract ClaimNestedOperandsPrioritySymbolicTest is Test {
    Assertions core;
    ClaimNestedPriorityHost host;
    bytes4 constant ECHO = 0xcafef00d;

    function setUp() public {
        core = new Assertions();
        host = new ClaimNestedPriorityHost();
    }

    function check_nestedConstructedSuccess(bytes32 a, bytes32 b, bool getRoute) public {
        vm.warp(1000);
        InputParam[] memory args = new InputParam[](3);
        args[0] = nested(reply(abi.encode(a)), 2);
        args[1] = nested(reply(abi.encode(b)), 1);
        args[2] = args[0];
        (bool ok, bytes memory out) = construct(args, getRoute, "(bytes32,bytes32,bytes32)");
        assertTrue(ok);
        if (getRoute) {
            assertEq(out, bytes.concat(abi.encode(address(core)), ECHO, abi.encode(a, b, a)));
            assertEq(host.count(), 14, "target, three independent leaves and one destination");
        } else {
            bytes[] memory values = new bytes[](3);
            values[0] = abi.encode(a);
            values[1] = abi.encode(b);
            values[2] = abi.encode(a);
            assertEq(out, abi.encode(values));
            assertEq(host.count(), 3, "repeated nested entries are independent");
        }
    }

    function check_nestedOuterConstraintOrder(bytes32[3] memory words, uint8 position, uint8 depth, bool getRoute)
        public
    {
        vm.assume(position < 3 && depth < 3);
        uint256 bad = literal(position);
        vm.warp(1000);
        InputParam[] memory args = new InputParam[](3);
        for (uint256 i; i < 3; i++) {
            args[i] = nested(reply(abi.encode(words[i])), i == bad ? literal(depth) : i == 0 ? 2 : i == 1 ? 1 : 0);
            args[i].constraints = new Constraint[](1);
            args[i].constraints[0] =
                Constraint(ConstraintType.EQ, abi.encode(i >= bad ? words[i] ^ bytes32(uint256(1)) : words[i]));
        }
        (bool ok, bytes memory out) = construct(args, getRoute, "(uint8[0])");
        assertFalse(ok);
        assertEq(out, failed(bad + (getRoute ? 1 : 0), words[bad], words[bad] ^ bytes32(uint256(1))));
        assertEq(host.count(), bad + 1 + (getRoute ? 1 : 0));
    }

    function check_nestedInnerFailureStops(
        bytes32[3] memory words,
        uint8 position,
        uint8 depth,
        uint8 fault,
        bool getRoute
    ) public {
        vm.assume(position < 3 && depth < 3 && fault < 3);
        uint256 bad = literal(position);
        vm.warp(1000);
        InputParam[] memory args = successfulArgs(words);
        args[bad] = failing(words[bad], fault);
        args[bad] = nested(args[bad], literal(depth));
        bytes memory want;
        if (fault == 1 && depth == 0) {
            want = failed(bad + (getRoute ? 1 : 0), words[bad], words[bad] ^ bytes32(uint256(1)));
        } else {
            // _staticCall wraps the failure of the OUTERMOST fetched call.
            // Its exact target/calldata is the public wrapper context; the
            // error inside a deeper resolve/get is intentionally discarded.
            (address target, bytes memory data) = abi.decode(args[bad].paramData, (address, bytes));
            want = abi.encodeWithSelector(CallFailed.selector, target, data);
        }
        (bool ok, bytes memory out) = construct(args, getRoute, "(bytes32,bytes32,bytes32)");
        if (!(fault == 1 && depth == 0)) ordinary(ok, out);
        assertFalse(ok);
        assertEq(out, want);
        assertEq(host.count(), bad + (fault < 2 ? 1 : 0) + (getRoute ? 1 : 0));
    }

    function check_nestedGetCodecAfterResolution(bytes32 word, uint8 position, uint8 depth, bool laterConstraint)
        public
    {
        vm.assume(position < 3 && depth < 3);
        uint256 bad = literal(position);
        vm.warp(1000);
        InputParam[] memory args = new InputParam[](3);
        bytes32 last;
        for (uint256 i; i < 3; i++) {
            bytes32 value = i >= bad ? word | bytes32(uint256(1) << 255) : bytes32(uint256(7));
            args[i] = nested(reply(abi.encode(value)), i == bad ? literal(depth) : i == 0 ? 2 : i == 1 ? 1 : 0);
            if (i == 2) last = value;
        }
        if (laterConstraint) {
            args[2].constraints = new Constraint[](1);
            args[2].constraints[0] = Constraint(ConstraintType.EQ, abi.encode(last ^ bytes32(uint256(1))));
        }
        (bool ok, bytes memory out) = construct(args, true, "(uint8,uint8,uint8)");
        assertFalse(ok);
        assertEq(
            out,
            laterConstraint
                ? failed(3, last, last ^ bytes32(uint256(1)))
                : abi.encodeWithSelector(AbiCodec.InvalidComponentValue.selector, bad, uint256(0))
        );
        assertEq(host.count(), 4, "all arguments resolve before codec validation; destination never executes");
    }

    function successfulArgs(bytes32[3] memory words) internal view returns (InputParam[] memory args) {
        args = new InputParam[](3);
        args[0] = nested(reply(abi.encode(words[0])), 2);
        args[1] = nested(reply(abi.encode(words[1])), 1);
        args[2] = reply(abi.encode(words[2]));
    }

    function failing(bytes32 word, uint8 fault) internal view returns (InputParam memory p) {
        if (fault == 0) {
            return
                operand(address(host), abi.encodeCall(ClaimNestedPriorityHost.fail, (abi.encode(word), address(core))));
        }
        if (fault == 1) {
            p = reply(abi.encode(word));
            p.constraints = new Constraint[](1);
            p.constraints[0] = Constraint(ConstraintType.EQ, abi.encode(word ^ bytes32(uint256(1))));
            return p;
        }
        InputParam[] memory args = new InputParam[](1);
        args[0] = raw(abi.encode(word | bytes32(uint256(1) << 255)));
        return
            operand(
                address(core), abi.encodeCall(Assertions.get, (raw(abi.encode(address(host))), ECHO, "(uint8)", args))
            );
    }

    function construct(InputParam[] memory args, bool getRoute, string memory t)
        internal
        view
        returns (bool, bytes memory)
    {
        if (!getRoute) return address(core).staticcall(abi.encodeCall(Assertions.gather, (args)));
        InputParam memory target = nested(reply(abi.encode(address(host))), 2);
        return address(core).staticcall(abi.encodeCall(Assertions.get, (target, ECHO, t, args)));
    }

    function nested(InputParam memory p, uint256 depth) internal view returns (InputParam memory) {
        for (uint256 i; i < depth; i++) {
            p = operand(address(core), abi.encodeCall(Assertions.resolve, (p)));
        }
        return p;
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
        return operand(address(host), abi.encodeCall(ClaimNestedPriorityHost.reply, (data, address(core))));
    }

    function failed(uint256 index, bytes32 actual, bytes32 ref) internal pure returns (bytes memory) {
        return abi.encodeWithSelector(
            ConstraintFailed.selector, "", uint256(0), index, uint256(0), ConstraintType.EQ, actual, abi.encode(ref)
        );
    }

    function literal(uint8 value) internal pure returns (uint256) {
        if (value == 0) return 0;
        if (value == 1) return 1;
        return 2;
    }

    function ordinary(bool ok, bytes memory out) internal pure {
        vm.assume(ok || out.length != 4 || bytes4(out) != Assertions.SubcallOutOfGas.selector);
    }

    function test_nestedSuccessSamples() public {
        bytes32 a = bytes32(uint256(42));
        bytes32 b = bytes32(uint256(93));
        vm.expectCall(
            address(host), abi.encodeCall(ClaimNestedPriorityHost.reply, (abi.encode(a), address(core))), uint64(4)
        );
        vm.expectCall(
            address(host), abi.encodeCall(ClaimNestedPriorityHost.reply, (abi.encode(b), address(core))), uint64(2)
        );
        vm.expectCall(
            address(host),
            abi.encodeCall(ClaimNestedPriorityHost.reply, (abi.encode(address(host)), address(core))),
            uint64(1)
        );
        vm.expectCall(address(host), abi.encodePacked(ECHO), uint64(1));
        check_nestedConstructedSuccess(a, b, false);
        check_nestedConstructedSuccess(a, b, true);
    }

    function test_nestedOuterConstraintSamples() public {
        bytes32[3] memory words = [bytes32(uint256(42)), bytes32(uint256(93)), bytes32(uint256(7))];
        vm.expectCall(address(host), abi.encodePacked(ClaimNestedPriorityHost.reply.selector), uint64(45));
        vm.expectCall(address(host), abi.encodePacked(ECHO), uint64(0));
        for (uint8 p; p < 3; p++) {
            for (uint8 d; d < 3; d++) {
                check_nestedOuterConstraintOrder(words, p, d, false);
                check_nestedOuterConstraintOrder(words, p, d, true);
            }
        }
    }

    function test_nestedInnerFailureSamples() public {
        bytes32[3] memory words = [bytes32(uint256(42)), bytes32(uint256(93)), bytes32(uint256(7))];
        vm.expectCall(address(host), abi.encodePacked(ClaimNestedPriorityHost.reply.selector), uint64(99));
        vm.expectCall(address(host), abi.encodePacked(ClaimNestedPriorityHost.fail.selector), uint64(18));
        vm.expectCall(address(host), abi.encodePacked(ECHO), uint64(0));
        for (uint8 p; p < 3; p++) {
            for (uint8 d; d < 3; d++) {
                for (uint8 f; f < 3; f++) {
                    check_nestedInnerFailureStops(words, p, d, f, false);
                    check_nestedInnerFailureStops(words, p, d, f, true);
                }
            }
        }
    }

    function test_nestedGetCodecPrioritySamples() public {
        vm.expectCall(address(host), abi.encodePacked(ClaimNestedPriorityHost.reply.selector), uint64(72));
        vm.expectCall(address(host), abi.encodePacked(ECHO), uint64(0));
        for (uint8 p; p < 3; p++) {
            for (uint8 d; d < 3; d++) {
                check_nestedGetCodecAfterResolution(bytes32(uint256(42)), p, d, false);
                check_nestedGetCodecAfterResolution(bytes32(uint256(42)), p, d, true);
            }
        }
    }
}
