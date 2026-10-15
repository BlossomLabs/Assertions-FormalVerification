// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../Assertions.sol";
import {ClaimOrContextHost} from "./ClaimOrOperandContextsSymbolic.t.sol";

/**
 * @dev Distinct hop lanes check core caller and independent input words before
 *      replying. They prevent commuting target swaps from hiding behind totals.
 */
contract ClaimOrTraversalHop {
    Vm constant VM = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    uint256 immutable lane;
    address caller;
    address next;
    bytes32 input;
    bytes finalValue;

    constructor(uint256 lane_) {
        lane = lane_;
    }

    function configure(address caller_, address next_, bytes32 input_, bytes calldata value_) external {
        caller = caller_;
        next = next_;
        input = input_;
        finalValue = value_;
    }

    function intermediate(bytes32 word) external {
        require(lane == 1 && msg.sender == caller && word == input);
        VM.warp(block.timestamp + 3);
        bytes memory value = abi.encode(next, input);
        assembly ("memory-safe") { return(add(value, 32), mload(value)) }
    }

    function terminal(bytes32 word) external {
        require(lane == 2 && msg.sender == caller && word == input);
        VM.warp(block.timestamp + 9);
        bytes memory value = finalValue;
        assembly ("memory-safe") { return(add(value, 32), mload(value)) }
    }
}

/**
 * @notice Three finite OR composition contexts: gather indices0/1/2,
 *         two-hop chain start priority, and one selected nav uint8 word.
 *         Independent error/solc oracles and low-level bool checks are required.
 *         Visited hosts must succeed; no OOG artifact is excluded. Weights
 *         observe bounded STATIC/token calls, not native BALANCE reads or
 *         arbitrary order, real gas, state effects, lists or navigation trees.
 */
contract ClaimOrGatherChainNavSymbolicTest is Test {
    struct LeafCase {
        bytes32 firstRef;
        bytes32 lower;
        bytes32 upper;
        uint8 fault;
    }

    struct Outcome {
        bool passes;
        bytes failure;
        Constraint constraint;
    }

    struct GatherCase {
        bytes32[3] words;
        LeafCase leaf;
        uint8 route;
        uint8 paramType;
        uint8 selected;
        uint8 size;
    }

    struct ChainCase {
        bytes32 finalWord;
        bytes32 middleWord;
        LeafCase leaf;
        uint96 upper;
        uint8 route;
        uint8 paramType;
        uint8 size;
        uint8 finalSize;
    }

    struct NavCase {
        bytes32 word;
        LeafCase leaf;
        uint8 route;
        uint8 paramType;
        uint8 size;
        uint8 indexCase;
        bool descriptorFault;
    }
    Assertions core;
    ClaimOrContextHost[7] hosts;
    ClaimOrTraversalHop[2] hops;
    bytes4 constant ECHO = 0xcafef00d;

    function setUp() public {
        core = new Assertions();
        hops[0] = new ClaimOrTraversalHop(1);
        hops[1] = new ClaimOrTraversalHop(2);
        for (uint256 i; i < 7; i++) {
            hosts[i] = new ClaimOrContextHost(weight(i));
            hosts[i].configure(7, address(core), account(i));
        }
    }

    function check_gatherFetchedOrZeroBasedContext(GatherCase memory x) public {
        vm.assume(x.route < 3 && x.paramType < 3 && x.selected < 3 && x.size < 5 && x.leaf.fault < 5);
        vm.assume(x.route == 0 || x.size == 3);
        vm.warp(1000);
        bytes32 word = x.selected == 0 ? x.words[0] : x.selected == 1 ? x.words[1] : x.words[2];
        Outcome memory expected = outcome(word, x.leaf, byteLength(x.size), "", 0, x.selected);
        InputParam[] memory args = new InputParam[](3);
        bytes[] memory values = new bytes[](3);
        uint256 total;
        for (uint256 i; i < 3; i++) {
            values[i] = i == x.selected ? payload(x.words[i], byteLength(x.size)) : abi.encode(x.words[i]);
            args[i] =
                !expected.passes && i > x.selected ? skipped(x.paramType) : fetched(i, values[i], x.route, x.paramType);
            if (i == x.selected) args[i].constraints = one(expected.constraint);
            if (x.route != 1 && (expected.passes || i <= x.selected)) total += weight(i);
        }
        (bool ok, bytes memory out) = address(core).staticcall(abi.encodeCall(Assertions.gather, (args)));
        assertEq(ok, expected.passes);
        assertEq(out, expected.passes ? abi.encode(values) : expected.failure);
        assertEq(hosts[0].count(), total);
    }

    function check_chainFetchedOrStartBeforeAddress(ChainCase memory x) public {
        vm.assume(x.route < 3 && x.paramType < 3 && x.size < 5 && x.finalSize < 5 && x.leaf.fault < 5);
        vm.assume(x.route == 0 || x.size == 3);
        vm.warp(1000);
        bytes32 word = bytes32((uint256(x.upper) << 160) | uint160(address(hops[0])));
        Outcome memory expected = outcome(word, x.leaf, byteLength(x.size), "", 0, 0);
        InputParam memory start = fetched(0, payload(word, byteLength(x.size)), x.route, x.paramType);
        start.constraints = one(expected.constraint);
        bytes[] memory calls = new bytes[](2);
        hops[0].configure(address(core), address(hops[1]), x.middleWord, bytes(""));
        calls[0] = abi.encodeCall(ClaimOrTraversalHop.intermediate, (x.middleWord));
        bytes memory finalValue = payload(x.finalWord, byteLength(x.finalSize));
        hops[1].configure(address(core), address(0), x.finalWord, finalValue);
        calls[1] = abi.encodeCall(ClaimOrTraversalHop.terminal, (x.finalWord));
        (bool ok, bytes memory out) = address(core).staticcall(abi.encodeCall(Assertions.chain, (start, calls)));
        bool success = expected.passes && x.upper == 0;
        assertEq(ok, success);
        assertEq(
            out,
            !expected.passes
                ? expected.failure
                : x.upper != 0 ? abi.encodeWithSelector(InvalidAddressWord.selector, uint256(0), word) : finalValue
        );
        assertEq(hosts[0].count(), (x.route == 1 ? 0 : 1) + (success ? 12 : 0));
    }

    function check_navFetchedOrBeforeTypeIndexAndWord(NavCase memory x) public {
        vm.assume(x.route < 3 && x.paramType < 3 && x.size < 5 && x.indexCase < 3 && x.leaf.fault < 5);
        vm.assume(x.route == 0 || x.size == 3);
        vm.warp(1000);
        Outcome memory expected = outcome(x.word, x.leaf, byteLength(x.size), "", 0, 0);
        InputParam memory a = fetched(0, payload(x.word, byteLength(x.size)), x.route, x.paramType);
        a.constraints = one(expected.constraint);
        int256[] memory path = new int256[](1);
        path[0] = x.indexCase == 0 ? int256(0) : x.indexCase == 1 ? int256(1) : int256(-1);
        (bool ok, bytes memory out) = address(core)
            .staticcall(abi.encodeCall(Assertions.nav, (a, x.descriptorFault ? "(uint8[0])" : "(uint8)", path)));
        bool success = expected.passes && !x.descriptorFault && x.indexCase == 0 && uint256(x.word) < 256;
        assertEq(ok, success);
        bytes memory wanted = !expected.passes
            ? expected.failure
            : x.descriptorFault
                ? abi.encodeWithSelector(InvalidTypeDescriptor.selector, uint256(8))
                : x.indexCase != 0
                    ? abi.encodeWithSelector(ElementIndexOutOfBounds.selector, path[0], uint256(1))
                    : uint256(x.word) >= 256
                        ? abi.encodeWithSelector(AbiCodec.InvalidValue.selector, uint256(0))
                        : abi.encode(uint8(uint256(x.word)));
        assertEq(out, wanted);
        assertEq(hosts[0].count(), x.route == 1 ? 0 : 1);
    }

    function outcome(
        bytes32 word,
        LeafCase memory x,
        uint256 length,
        string memory message,
        uint256 entry,
        uint256 param
    ) internal pure returns (Outcome memory out) {
        out.constraint = disjunction(word, x);
        if (length < 32) {
            out.failure = abi.encodeWithSelector(ReturnDataOutOfBounds.selector, int256(0), length);
        } else if (x.fault == 2 || x.fault == 3) {
            out.failure = abi.encodeWithSelector(InvalidOrConstraint.selector, entry, param, uint256(0));
        } else if (x.fault == 4) {
            out.failure = abi.encodeWithSelector(InvalidConstraintData.selector, entry, param, uint256(0), uint256(31));
        } else if (word == x.firstRef) {
            out.passes = true;
        } else if (x.fault == 1) {
            out.failure = abi.encodeWithSelector(InvalidConstraintData.selector, entry, param, uint256(0), uint256(33));
        } else if (int256(uint256(x.lower)) > int256(uint256(x.upper))) {
            out.failure = abi.encodeWithSelector(InvalidConstraintRange.selector, entry, param, uint256(0));
        } else if (
            int256(uint256(x.lower)) <= int256(uint256(word)) && int256(uint256(word)) <= int256(uint256(x.upper))
        ) {
            out.passes = true;
        } else {
            out.failure = abi.encodeWithSelector(
                ConstraintFailed.selector,
                message,
                entry,
                param,
                uint256(0),
                ConstraintType.OR,
                word,
                out.constraint.referenceData
            );
        }
    }

    function disjunction(bytes32 word, LeafCase memory x) internal pure returns (Constraint memory) {
        Constraint[] memory alternatives = new Constraint[](x.fault == 3 ? 0 : 2);
        if (x.fault != 3) {
            alternatives[0] = Constraint(ConstraintType.EQ, abi.encode(x.fault == 2 ? word : x.firstRef));
            alternatives[1] = Constraint(ConstraintType.IN_SIGNED, abi.encode(x.lower, x.upper));
            if (x.fault == 1) {
                alternatives[1].referenceData = prefix(alternatives[1].referenceData, 33);
            } else if (x.fault == 2) {
                alternatives[1] = Constraint(ConstraintType.OR, abi.encode(new Constraint[](0)));
            } else if (x.fault == 4) {
                alternatives[0].referenceData = prefix(alternatives[0].referenceData, 31);
            }
        }
        return Constraint(ConstraintType.OR, bytes.concat(abi.encode(alternatives), hex"7f"));
    }

    function sampleLeaf(uint8 which, bytes32 word) internal pure returns (LeafCase memory x) {
        x.firstRef = word ^ bytes32(uint256(1));
        x.lower = word;
        x.upper = word;
        if (which == 1) {
            x.lower = word ^ bytes32(uint256(2));
            x.upper = x.lower;
        } else if (which == 2 || which == 3) {
            x.lower = bytes32(uint256(type(int256).max));
            x.upper = bytes32(uint256(1) << 255);
            if (which == 3) x.firstRef = word;
        } else if (which == 4 || which == 5) {
            x.fault = 1;
            if (which == 5) x.firstRef = word;
        } else if (which == 6) {
            x.fault = 2;
        } else if (which == 7) {
            x.fault = 3;
        } else if (which == 8) {
            x.fault = 4;
        }
    }

    function test_gatherOrZeroBasedSamples() public {
        fixtureGuards();
        vm.expectCall(address(hosts[0]), abi.encodePacked(ClaimOrContextHost.reply.selector), uint64(405));
        vm.expectCall(address(hosts[1]), abi.encodePacked(ClaimOrContextHost.reply.selector), uint64(288));
        vm.expectCall(address(hosts[2]), abi.encodePacked(ClaimOrContextHost.reply.selector), uint64(171));
        vm.expectCall(address(hosts[0]), abi.encodePacked(ClaimOrContextHost.balanceOf.selector), uint64(81));
        vm.expectCall(address(hosts[1]), abi.encodePacked(ClaimOrContextHost.balanceOf.selector), uint64(63));
        vm.expectCall(address(hosts[2]), abi.encodePacked(ClaimOrContextHost.balanceOf.selector), uint64(45));
        vm.expectCall(address(hosts[6]), abi.encodePacked(ClaimOrContextHost.reply.selector), uint64(0));
        vm.expectCall(address(hosts[5]), abi.encodePacked(ECHO), uint64(0));
        GatherCase memory x;
        x.words = [bytes32(uint256(7)), bytes32(uint256(93)), bytes32(uint256(81))];
        for (uint8 route; route < 3; route++) {
            x.route = route;
            for (uint8 typ; typ < 3; typ++) {
                x.paramType = typ;
                for (uint8 selected; selected < 3; selected++) {
                    x.selected = selected;
                    bytes32 word = selected == 0 ? x.words[0] : selected == 1 ? x.words[1] : x.words[2];
                    for (uint8 size; size < 5; size++) {
                        if (route != 0 && size != 3) continue;
                        x.size = size;
                        for (uint8 leaf; leaf < 9; leaf++) {
                            x.leaf = sampleLeaf(leaf, word);
                            check_gatherFetchedOrZeroBasedContext(x);
                        }
                    }
                }
            }
        }
    }

    function test_chainOrStartPrioritySamples() public {
        fixtureGuards();
        hopGuards();
        vm.expectCall(address(hosts[0]), abi.encodePacked(ClaimOrContextHost.reply.selector), uint64(342));
        vm.expectCall(address(hosts[0]), abi.encodePacked(ClaimOrContextHost.balanceOf.selector), uint64(90));
        vm.expectCall(address(hops[0]), abi.encodePacked(ClaimOrTraversalHop.intermediate.selector), uint64(180));
        vm.expectCall(address(hops[0]), abi.encodePacked(ClaimOrTraversalHop.terminal.selector), uint64(0));
        vm.expectCall(address(hops[1]), abi.encodePacked(ClaimOrTraversalHop.terminal.selector), uint64(180));
        vm.expectCall(address(hops[1]), abi.encodePacked(ClaimOrTraversalHop.intermediate.selector), uint64(0));
        vm.expectCall(address(hosts[6]), abi.encodePacked(ClaimOrContextHost.reply.selector), uint64(0));
        vm.expectCall(address(hosts[5]), abi.encodePacked(ECHO), uint64(0));
        ChainCase memory x;
        x.finalWord = bytes32(uint256(93));
        x.middleWord = bytes32(uint256(81));
        for (uint8 route; route < 3; route++) {
            x.route = route;
            for (uint8 typ; typ < 3; typ++) {
                x.paramType = typ;
                for (uint8 dirty; dirty < 2; dirty++) {
                    x.upper = dirty == 0 ? 0 : 1;
                    bytes32 word = bytes32((uint256(x.upper) << 160) | uint160(address(hops[0])));
                    for (uint8 size; size < 5; size++) {
                        if (route != 0 && size != 3) continue;
                        x.size = size;
                        for (uint8 leaf; leaf < 9; leaf++) {
                            x.leaf = sampleLeaf(leaf, word);
                            for (uint8 last; last < 5; last++) {
                                bool passing = leaf == 0 || leaf == 3 || leaf == 5;
                                if (!(dirty == 0 && size >= 3 && passing) && last != 3) continue;
                                x.finalSize = last;
                                check_chainFetchedOrStartBeforeAddress(x);
                            }
                        }
                    }
                }
            }
        }
    }

    function test_navOrBeforeValidationSamples() public {
        fixtureGuards();
        vm.expectCall(address(hosts[0]), abi.encodePacked(ClaimOrContextHost.reply.selector), uint64(1620));
        vm.expectCall(address(hosts[0]), abi.encodePacked(ClaimOrContextHost.balanceOf.selector), uint64(324));
        vm.expectCall(address(hosts[6]), abi.encodePacked(ClaimOrContextHost.reply.selector), uint64(0));
        vm.expectCall(address(hosts[5]), abi.encodePacked(ECHO), uint64(0));
        NavCase memory x;
        for (uint8 route; route < 3; route++) {
            x.route = route;
            for (uint8 typ; typ < 3; typ++) {
                x.paramType = typ;
                for (uint8 dirty; dirty < 2; dirty++) {
                    x.word = dirty == 0 ? bytes32(uint256(7)) : bytes32(uint256(256));
                    for (uint8 descriptor; descriptor < 2; descriptor++) {
                        x.descriptorFault = descriptor == 1;
                        for (uint8 index; index < 3; index++) {
                            x.indexCase = index;
                            for (uint8 size; size < 5; size++) {
                                if (route != 0 && size != 3) continue;
                                x.size = size;
                                for (uint8 leaf; leaf < 9; leaf++) {
                                    x.leaf = sampleLeaf(leaf, x.word);
                                    check_navFetchedOrBeforeTypeIndexAndWord(x);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    function hopGuards() internal {
        hops[0].configure(address(core), address(hops[1]), bytes32(uint256(81)), bytes(""));
        hops[1].configure(address(core), address(0), bytes32(uint256(93)), hex"117f");
        bytes memory middleCall = abi.encodeCall(ClaimOrTraversalHop.intermediate, (bytes32(uint256(81))));
        bytes memory lastCall = abi.encodeCall(ClaimOrTraversalHop.terminal, (bytes32(uint256(93))));
        (bool ok, bytes memory out) = address(hops[0]).call(middleCall);
        assertFalse(ok);
        assertEq(out, bytes(""));
        (ok, out) = address(hops[1]).call(lastCall);
        assertFalse(ok);
        assertEq(out, bytes(""));
        vm.prank(address(core));
        (ok, out) = address(hops[0]).call(abi.encodeCall(ClaimOrTraversalHop.intermediate, (bytes32(uint256(80)))));
        assertFalse(ok);
        assertEq(out, bytes(""));
        vm.prank(address(core));
        (ok, out) = address(hops[1]).call(abi.encodeCall(ClaimOrTraversalHop.terminal, (bytes32(uint256(92)))));
        assertFalse(ok);
        assertEq(out, bytes(""));
        vm.prank(address(core));
        (ok, out) = address(hops[0]).call(lastCall);
        assertFalse(ok);
        assertEq(out, bytes(""));
        vm.prank(address(core));
        (ok, out) = address(hops[1]).call(middleCall);
        assertFalse(ok);
        assertEq(out, bytes(""));
        vm.warp(1000);
        vm.prank(address(core));
        (ok, out) = address(hops[0]).call(middleCall);
        assertTrue(ok);
        assertEq(out, abi.encode(address(hops[1]), bytes32(uint256(81))));
        assertEq(hosts[0].count(), uint256(3));
        vm.warp(1000);
        vm.prank(address(core));
        (ok, out) = address(hops[1]).call(lastCall);
        assertTrue(ok);
        assertEq(out, hex"117f");
        assertEq(hosts[0].count(), uint256(9));
    }

    function fixtureGuards() internal {
        for (uint256 i; i < 7; i++) {
            ClaimOrContextHost h = host(i);
            (bool ok, bytes memory out) = address(h).call(abi.encodeCall(ClaimOrContextHost.reply, (hex"11")));
            assertFalse(ok);
            assertEq(out, bytes(""));
            vm.warp(1000);
            vm.prank(address(core));
            (ok, out) = address(h).call(abi.encodeCall(ClaimOrContextHost.reply, (hex"117f")));
            assertTrue(ok);
            assertEq(out, hex"117f");
            assertEq(h.count(), weight(i));
            h.configure(7, address(core), account(i));
            (ok, out) = address(h).call(abi.encodeCall(ClaimOrContextHost.balanceOf, (account(i))));
            assertFalse(ok);
            assertEq(out, bytes(""));
            vm.prank(address(core));
            (ok, out) = address(h).call(abi.encodeCall(ClaimOrContextHost.balanceOf, (address(0xdead))));
            assertFalse(ok);
            assertEq(out, bytes(""));
            vm.warp(1000);
            vm.prank(address(core));
            (ok, out) = address(h).call(abi.encodeCall(ClaimOrContextHost.balanceOf, (account(i))));
            assertTrue(ok);
            assertEq(out, prefix(abi.encode(uint256(7), bytes32(uint256(0x93)), bytes32(uint256(0x7f))), 65));
            assertEq(h.count(), weight(i));
            (ok, out) = address(h).call(abi.encodePacked(ECHO, hex"117f"));
            assertFalse(ok);
            assertEq(out, bytes(""));
            vm.warp(1000);
            vm.prank(address(core));
            (ok, out) = address(h).call(abi.encodePacked(ECHO, hex"117f"));
            assertTrue(ok);
            assertEq(out, abi.encodePacked(abi.encode(address(core), address(h)), ECHO, hex"117f"));
            assertEq(h.count(), uint256(1000));
        }
    }

    function fetched(uint256 slot, bytes memory value, uint8 route, uint8 paramType)
        internal
        returns (InputParam memory p)
    {
        ClaimOrContextHost h = host(slot);
        if (route == 0) {
            p = InputParam(
                InputParamType(paramType),
                InputParamFetcherType.STATIC_CALL,
                abi.encode(address(h), abi.encodeCall(ClaimOrContextHost.reply, (value))),
                new Constraint[](0)
            );
        } else {
            assertTrue(value.length >= 32);
            uint256 amount;
            assembly ("memory-safe") { amount := mload(add(value, 32)) }
            address a = account(slot);
            vm.deal(a, amount);
            h.configure(amount, address(core), a);
            p = InputParam(
                InputParamType(paramType),
                InputParamFetcherType.BALANCE,
                abi.encodePacked(route == 1 ? address(0) : address(h), a),
                new Constraint[](0)
            );
        }
    }

    function skipped(uint8 paramType) internal view returns (InputParam memory p) {
        p = InputParam(
            InputParamType(paramType),
            InputParamFetcherType.STATIC_CALL,
            abi.encode(address(hosts[6]), abi.encodeCall(ClaimOrContextHost.reply, (abi.encode(uint256(0xbadc0de))))),
            new Constraint[](1)
        );
        p.constraints[0] = Constraint(ConstraintType.OR, hex"ff");
    }

    function one(Constraint memory c) internal pure returns (Constraint[] memory out) {
        out = new Constraint[](1);
        out[0] = c;
    }

    function payload(bytes32 word, uint256 length) internal pure returns (bytes memory) {
        return prefix(bytes.concat(abi.encode(word), hex"7f"), length);
    }

    function prefix(bytes memory data, uint256 length) internal pure returns (bytes memory out) {
        out = new bytes(length);
        for (uint256 i; i < length; i++) {
            out[i] = data[i];
        }
    }

    function byteLength(uint8 size) internal pure returns (uint256) {
        if (size == 0) return 0;
        if (size == 1) return 1;
        if (size == 2) return 31;
        if (size == 3) return 32;
        return 33;
    }

    function host(uint256 slot) internal view returns (ClaimOrContextHost) {
        if (slot == 0) return hosts[0];
        if (slot == 1) return hosts[1];
        if (slot == 2) return hosts[2];
        if (slot == 3) return hosts[3];
        if (slot == 4) return hosts[4];
        if (slot == 5) return hosts[5];
        return hosts[6];
    }

    function weight(uint256 slot) internal pure returns (uint256) {
        if (slot == 0) return 1;
        if (slot == 1) return 3;
        if (slot == 2) return 9;
        if (slot == 3) return 27;
        if (slot == 4) return 81;
        if (slot == 5) return 243;
        return 729;
    }

    function account(uint256 slot) internal pure returns (address) {
        return address(uint160(0xa210 + slot));
    }
}
