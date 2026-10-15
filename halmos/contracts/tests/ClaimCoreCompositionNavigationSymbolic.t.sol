// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../Assertions.sol";

contract ClaimCompositionHost {
    Vm constant VM = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    function context(bytes32 word) external returns (address, bytes32) {
        VM.warp(block.timestamp + 1);
        return (msg.sender, word);
    }

    function count() external view returns (uint256) {
        return block.timestamp - 1000;
    }
}

/**
 * @notice C22 selected finite composition trees and C39 four-level dynamic
 * arrays / mixed recursive tuples. ABI results come from solc abi.encode;
 * rejection offsets are located by a unique marker scan. No arbitrary-depth,
 * resource, gas-sensitive target or induction claim is made.
 */
contract ClaimCoreCompositionNavigationSymbolicTest is Test {
    struct Item {
        uint8[] numbers;
        bytes blob;
    }

    struct Root {
        uint256 tag;
        Item[] items;
    }

    Assertions core;
    ClaimCompositionHost host;

    function setUp() public {
        core = new Assertions();
        host = new ClaimCompositionHost();
    }

    function check_compositionCondReadGetResolve(bytes32 a, bytes32 b, bytes32 condition) public {
        vm.warp(1000);
        InputParam memory then_ = constructed(a, true);
        InputParam memory else_ = constructed(b, false);
        InputParam memory tree =
            operand(address(core), abi.encodeCall(Assertions.cond, (raw(abi.encode(condition)), then_, else_)));
        (bool ok, bytes memory out) = address(core).staticcall(abi.encodeCall(Assertions.resolve, (tree)));
        assertTrue(ok);
        assertEq(out, abi.encode(address(core), condition != 0 ? a : b));
        assertEq(host.count(), 1);
    }

    function check_compositionOrElseGuardedReadGet(bytes32 value, bytes32 ref, bytes32 fallbackValue) public {
        vm.warp(1000);
        InputParam memory attempt = constructed(value, false);
        attempt.constraints = new Constraint[](2);
        attempt.constraints[0] = Constraint(ConstraintType.EQ, abi.encode(address(core)));
        attempt.constraints[1] = Constraint(ConstraintType.EQ, abi.encode(ref));
        InputParam memory tree =
            operand(address(core), abi.encodeCall(Assertions.orElse, (attempt, constructed(fallbackValue, true))));
        (bool ok, bytes memory out) = address(core).staticcall(abi.encodeCall(Assertions.resolve, (tree)));
        vm.assume(ok || keccak256(out) != keccak256(abi.encodeWithSelector(Assertions.SubcallOutOfGas.selector)));
        assertTrue(ok);
        assertEq(out, abi.encode(address(core), value == ref ? value : fallbackValue));
        assertEq(host.count(), value == ref ? 1 : 2);
    }

    function constructed(bytes32 value, bool useGet) internal view returns (InputParam memory) {
        InputParam memory target =
            operand(address(core), abi.encodeCall(Assertions.resolve, (raw(abi.encode(address(host))))));
        InputParam[] memory args = new InputParam[](1);
        args[0] = operand(
            address(core), abi.encodeCall(Assertions.pick, (raw(abi.encode(value, bytes32(uint256(93)))), int256(0)))
        );
        bytes memory data = useGet
            ? abi.encodeCall(Assertions.get, (target, ClaimCompositionHost.context.selector, "(bytes32)", args))
            : abi.encodeCall(Assertions.read, (target, ClaimCompositionHost.context.selector, args));
        return operand(address(core), data);
    }

    function check_recursiveFourLevelArray(uint8 a, uint8 b, bool last, bool terminal) public view {
        uint8[][][][] memory tree = narrowTree(a, b);
        int256[] memory path = arrayPath(last, terminal);
        (bool ok, bytes memory out) =
            address(core).staticcall(abi.encodeCall(Assertions.nav, (raw(abi.encode(tree)), "(uint8[][][][])", path)));
        assertTrue(ok);
        assertEq(out, terminal ? abi.encode(tree[0][0][0]) : abi.encode(last ? b : a));
    }

    function check_recursiveFourLevelDirtyWord(bytes32 word, bool last) public view {
        uint256[][][][] memory tree = wideTree();
        bytes32 marker = bytes32(uint256(0x123456789abcdef123456789abcdef));
        tree[0][0][0][last ? 1 : 0] = uint256(marker);
        bytes memory encoding = abi.encode(tree);
        uint256 offset = replaceMarker(encoding, marker, word);
        (bool ok, bytes memory out) = address(core)
            .staticcall(abi.encodeCall(Assertions.nav, (raw(encoding), "(uint8[][][][])", arrayPath(last, false))));
        assertEq(ok, uint256(word) <= type(uint8).max);
        assertEq(
            out,
            uint256(word) <= type(uint8).max
                ? abi.encode(word)
                : abi.encodeWithSelector(AbiCodec.InvalidValue.selector, offset)
        );
    }

    function check_recursiveMixedTupleTerminals(
        uint256 tag,
        uint8 a,
        uint8 b,
        bytes32[2] memory words,
        uint8 size,
        uint8 terminal
    ) public view {
        vm.assume(size < 5 && terminal < 3);
        Root memory tree;
        tree.tag = tag;
        tree.items = new Item[](1);
        tree.items[0].numbers = new uint8[](2);
        tree.items[0].numbers[0] = a;
        tree.items[0].numbers[1] = b;
        tree.items[0].blob = abi.encodePacked(words);
        uint256 n = size == 0 ? 0 : size == 1 ? 1 : size == 2 ? 31 : size == 3 ? 32 : 33;
        bytes memory blob = tree.items[0].blob;
        assembly ("memory-safe") { mstore(blob, n) }
        int256[] memory path = new int256[](terminal == 0 ? 4 : terminal == 1 ? 3 : 2);
        path[0] = 1;
        path[1] = 0;
        if (terminal == 0) {
            path[2] = 0;
            path[3] = -1;
        } else if (terminal == 1) {
            path[2] = 1;
        }
        (bool ok, bytes memory out) = address(core)
            .staticcall(
                abi.encodeCall(
                    Assertions.nav, (raw(abi.encode(tree.tag, tree.items)), "(uint256,(uint8[],bytes)[])", path)
                )
            );
        assertTrue(ok);
        assertEq(out, terminal == 0 ? abi.encode(b) : terminal == 1 ? abi.encode(blob) : abi.encode(tree.items[0]));
    }

    function narrowTree(uint8 a, uint8 b) internal pure returns (uint8[][][][] memory tree) {
        tree = new uint8[][][][](1);
        tree[0] = new uint8[][][](1);
        tree[0][0] = new uint8[][](1);
        tree[0][0][0] = new uint8[](2);
        tree[0][0][0][0] = a;
        tree[0][0][0][1] = b;
    }

    function wideTree() internal pure returns (uint256[][][][] memory tree) {
        tree = new uint256[][][][](1);
        tree[0] = new uint256[][][](1);
        tree[0][0] = new uint256[][](1);
        tree[0][0][0] = new uint256[](2);
        tree[0][0][0][0] = 42;
        tree[0][0][0][1] = 93;
    }

    function arrayPath(bool last, bool terminal) internal pure returns (int256[] memory path) {
        path = new int256[](terminal ? 4 : 5);
        if (!terminal) path[4] = last ? int256(-1) : int256(0);
    }

    function replaceMarker(bytes memory data, bytes32 marker, bytes32 word) internal pure returns (uint256 offset) {
        uint256 matches;
        for (uint256 i; i < data.length; i += 32) {
            bytes32 got;
            assembly ("memory-safe") { got := mload(add(add(data, 32), i)) }
            if (got == marker) {
                offset = i;
                matches++;
                assembly ("memory-safe") { mstore(add(add(data, 32), i), word) }
            }
        }
        assertEq(matches, 1, "reference marker must be unique");
    }

    function raw(bytes memory data) internal pure returns (InputParam memory) {
        return InputParam(InputParamType.CALL_DATA, InputParamFetcherType.RAW_BYTES, data, new Constraint[](0));
    }

    function operand(address target, bytes memory data) internal pure returns (InputParam memory) {
        return InputParam(
            InputParamType.CALL_DATA, InputParamFetcherType.STATIC_CALL, abi.encode(target, data), new Constraint[](0)
        );
    }

    function test_compositionSamples() public {
        bytes32 a = bytes32(uint256(42));
        bytes32 b = bytes32(uint256(93));
        check_compositionCondReadGetResolve(a, b, bytes32(uint256(7)));
        check_compositionCondReadGetResolve(a, b, bytes32(0));
        check_compositionOrElseGuardedReadGet(a, a, b);
        check_compositionOrElseGuardedReadGet(a, b, b);
    }

    function test_compositionExactCallCounts() public {
        bytes32 a = bytes32(uint256(42));
        bytes32 b = bytes32(uint256(93));
        vm.expectCall(address(host), abi.encodeCall(ClaimCompositionHost.context, (a)), uint64(1));
        vm.expectCall(address(host), abi.encodeCall(ClaimCompositionHost.context, (b)), uint64(0));
        check_compositionCondReadGetResolve(a, b, bytes32(uint256(7)));
    }

    function test_recursiveArraySamples() public view {
        check_recursiveFourLevelArray(42, 93, false, false);
        check_recursiveFourLevelArray(42, 93, true, false);
        check_recursiveFourLevelArray(42, 93, false, true);
        check_recursiveFourLevelDirtyWord(bytes32(uint256(255)), false);
        check_recursiveFourLevelDirtyWord(bytes32(uint256(256)), false);
        check_recursiveFourLevelDirtyWord(bytes32(type(uint256).max), true);
    }

    function test_recursiveTupleSamples() public view {
        bytes32[2] memory words = [bytes32(uint256(42)), bytes32(uint256(93))];
        for (uint8 size; size < 5; size++) {
            for (uint8 terminal; terminal < 3; terminal++) {
                check_recursiveMixedTupleTerminals(7, 42, 93, words, size, terminal);
            }
        }
    }
}
