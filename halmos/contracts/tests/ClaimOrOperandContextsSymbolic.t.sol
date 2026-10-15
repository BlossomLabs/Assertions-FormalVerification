// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../Assertions.sol";
import {OutputParam} from "../lib/ERC8211.sol";

/**
 * @dev Test-only clock and caller/account guards. Echo prefixes caller and
 *      receiver separately from the complete calldata. Counts describe finite
 *      test traces, not arbitrary ordering or real gas/state semantics.
 */
contract ClaimOrContextHost {
    Vm constant VM = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    uint256 immutable weight;
    uint256 amount;
    address coreCaller;
    address account;

    constructor(uint256 weight_) {
        weight = weight_;
    }

    function configure(uint256 amount_, address core_, address account_) external {
        amount = amount_;
        coreCaller = core_;
        account = account_;
    }

    function reply(bytes calldata data) external {
        VM.warp(block.timestamp + weight);
        require(msg.sender == coreCaller);
        assembly ("memory-safe") {
            calldatacopy(0, data.offset, data.length)
            return(0, data.length)
        }
    }

    function balanceOf(address account_) external {
        VM.warp(block.timestamp + weight);
        require(msg.sender == coreCaller && account_ == account);
        bytes memory data = abi.encode(amount, bytes32(uint256(0x93)), bytes32(uint256(0x7f)));
        assembly ("memory-safe") { return(add(data, 32), 65) }
    }

    function count() external view returns (uint256) {
        return block.timestamp - 1000;
    }

    fallback() external {
        VM.warp(block.timestamp + 1000);
        require(msg.sender == coreCaller);
        assembly ("memory-safe") {
            mstore(0, caller())
            mstore(32, address())
            calldatacopy(64, 0, calldatasize())
            return(0, add(64, calldatasize()))
        }
    }
}

/**
 * @notice Exactly three selected OR/nonzero-operand contexts. Fixed structures
 *         and independent signed verdicts pin full first errors and original
 *         references. Every external fixture is expected to succeed when
 *         visited, so no failed-subcall gas artifact is excluded.
 */
contract ClaimOrOperandContextsSymbolicTest is Test {
    struct LeafCase {
        bytes32 firstRef;
        bytes32 lower;
        bytes32 upper;
        uint8 fault;
    }

    struct CondCase {
        bytes32 condition;
        bytes32 winner;
        LeafCase leaf;
        uint8 conditionRoute;
        uint8 winnerRoute;
        uint8 paramType;
        uint8 size;
    }

    struct CallCase {
        bytes32[3] words;
        LeafCase leaf;
        uint8 route;
        uint8 paramType;
        uint8 bad;
        uint8 size;
        bool getRoute;
    }

    struct BatchCase {
        bytes32[6] words;
        LeafCase leaf;
        uint8 route;
        uint8 entry;
        uint8 paramCase;
        uint8 size;
        bool message;
    }

    struct Outcome {
        bool passes;
        bytes failure;
        Constraint constraint;
    }

    Assertions core;
    ClaimOrContextHost[7] hosts;
    bytes4 constant ECHO = 0xcafef00d;

    function setUp() public {
        core = new Assertions();
        for (uint256 i; i < 7; i++) {
            hosts[i] = new ClaimOrContextHost(weight(i));
            hosts[i].configure(7, address(core), account(i));
        }
    }

    function check_condFetchedOrWinnerContext(CondCase memory x) public {
        vm.assume(x.conditionRoute < 3 && x.winnerRoute < 3 && x.paramType < 3 && x.size < 5 && x.leaf.fault < 5);
        vm.assume(x.winnerRoute == 0 || x.size == 3);
        vm.warp(1000);
        bool truth = x.condition != bytes32(0);
        uint256 length = byteLength(x.size);
        bytes memory value = payload(x.winner, length);
        Outcome memory expected = outcome(x.winner, x.leaf, length, "", 0, truth ? 1 : 2);
        InputParam memory condition = fetched(0, abi.encode(x.condition), x.conditionRoute, x.paramType);
        InputParam memory winner = fetched(1, value, x.winnerRoute, x.paramType);
        winner.constraints = one(expected.constraint);
        InputParam memory ignored = skipped(x.paramType);
        (bool ok, bytes memory out) = address(core)
            .staticcall(
                abi.encodeCall(Assertions.cond, (condition, truth ? winner : ignored, truth ? ignored : winner))
            );
        assertEq(ok, expected.passes);
        assertEq(out, expected.passes ? value : expected.failure);
        assertEq(hosts[0].count(), (x.conditionRoute == 1 ? 0 : 1) + (x.winnerRoute == 1 ? 0 : 3));
    }

    function check_readGetFetchedOrArgumentContext(CallCase memory x) public {
        vm.assume(x.route < 3 && x.paramType < 3 && x.bad < 3 && x.size < 4 && x.leaf.fault < 5);
        vm.assume(x.route == 0 || x.size == 3);
        vm.warp(1000);
        bytes32 selected = x.bad == 0 ? x.words[0] : x.bad == 1 ? x.words[1] : x.words[2];
        Outcome memory expected = outcome(selected, x.leaf, byteLength(x.size), "", 0, uint256(x.bad) + 1);
        InputParam[] memory args = callArguments(x, expected);
        InputParam memory target = fetched(0, abi.encode(address(hosts[5])), 0, x.paramType);
        (bool ok, bytes memory out) = address(core)
            .staticcall(
                x.getRoute
                    ? abi.encodeCall(Assertions.get, (target, ECHO, "(bytes32,bytes32,bytes32)", args))
                    : abi.encodeCall(Assertions.read, (target, ECHO, args))
            );
        assertEq(ok, expected.passes);
        // Caller and receiver are fixture echo context; destination calldata
        // itself is the selector followed by independent solc ABI words.
        bytes memory success = bytes.concat(
            abi.encode(address(core), address(hosts[5])), ECHO, abi.encode(x.words[0], x.words[1], x.words[2])
        );
        assertEq(out, expected.passes ? success : expected.failure);
        uint256 calls = 1;
        for (uint256 i; i < 3; i++) {
            if (x.route != 1 && (i <= x.bad || expected.passes)) {
                calls += weight(i + 1);
            }
        }
        assertEq(hosts[0].count(), calls + (expected.passes ? 1000 : 0));
    }

    function callArguments(CallCase memory x, Outcome memory expected) internal returns (InputParam[] memory args) {
        args = new InputParam[](3);
        for (uint256 i; i < 3; i++) {
            if (i > x.bad && !expected.passes) {
                args[i] = skipped(x.paramType);
            } else {
                bytes memory value = i == x.bad ? payload(x.words[i], byteLength(x.size)) : abi.encode(x.words[i]);
                args[i] = fetched(i + 1, value, x.route, x.paramType);
                if (i == x.bad) {
                    args[i].constraints = one(expected.constraint);
                }
            }
        }
    }

    function check_batchFetchedOrParamContext(BatchCase memory x) public {
        vm.assume(x.route < 3 && x.entry < 2 && x.paramCase < 2 && x.size < 5 && x.leaf.fault < 5);
        vm.assume(x.route == 0 || x.size == 3);
        vm.warp(1000);
        uint256 param = x.paramCase == 0 ? 1 : 2;
        bytes32 selected =
            x.entry == 0 ? x.paramCase == 0 ? x.words[1] : x.words[2] : x.paramCase == 0 ? x.words[4] : x.words[5];
        Outcome memory expected =
            outcome(selected, x.leaf, byteLength(x.size), x.message ? "or-batch" : "COMPOSABLE", x.entry, param);
        ComposableExecution[] memory entries = batchEntries(x, expected);
        (bool ok, bytes memory out) = address(core)
            .staticcall(
                x.message
                    ? abi.encodeWithSignature(
                        "assertBatch((bytes4,(uint8,uint8,bytes,(uint8,bytes)[])[],(uint8,bytes)[])[],string)",
                        entries,
                        "or-batch"
                    )
                    : abi.encodeWithSignature(
                        "assertBatch((bytes4,(uint8,uint8,bytes,(uint8,bytes)[])[],(uint8,bytes)[])[])", entries
                    )
            );
        assertEq(ok, expected.passes);
        assertEq(out, expected.passes ? bytes("") : expected.failure);
        uint256 calls;
        for (uint256 i; i < 6; i++) {
            if (x.route != 1 && (i <= uint256(x.entry) * 3 + param || expected.passes)) {
                calls += weight(i);
            }
        }
        assertEq(hosts[0].count(), calls);
    }

    function batchEntries(BatchCase memory x, Outcome memory expected)
        internal
        returns (ComposableExecution[] memory entries)
    {
        entries = new ComposableExecution[](2);
        uint256 param = x.paramCase == 0 ? 1 : 2;
        uint256 selected = uint256(x.entry) * 3 + param;
        for (uint256 e; e < 2; e++) {
            entries[e].functionSig = ECHO;
            entries[e].inputParams = new InputParam[](3);
            entries[e].outputParams = new OutputParam[](0);
            for (uint256 p; p < 3; p++) {
                uint256 i = e * 3 + p;
                if (i > selected && !expected.passes) {
                    entries[e].inputParams[p] = skipped(2);
                } else {
                    bytes memory value =
                        i == selected ? payload(x.words[i], byteLength(x.size)) : abi.encode(x.words[i]);
                    entries[e].inputParams[p] = fetched(i, value, x.route, 2);
                    if (i == selected) {
                        entries[e].inputParams[p].constraints = one(expected.constraint);
                    }
                }
            }
        }
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

    function test_condOrWinnerContextSamples() public {
        fixtureGuards();
        vm.expectCall(address(hosts[0]), abi.encodePacked(ClaimOrContextHost.reply.selector), uint64(378));
        vm.expectCall(address(hosts[0]), abi.encodePacked(ClaimOrContextHost.balanceOf.selector), uint64(378));
        vm.expectCall(address(hosts[1]), abi.encodePacked(ClaimOrContextHost.reply.selector), uint64(810));
        vm.expectCall(address(hosts[1]), abi.encodePacked(ClaimOrContextHost.balanceOf.selector), uint64(162));
        vm.expectCall(address(hosts[6]), abi.encodePacked(ClaimOrContextHost.reply.selector), uint64(0));
        vm.expectCall(address(hosts[5]), abi.encodePacked(ECHO), uint64(0));
        CondCase memory x;
        x.winner = bytes32(uint256(7));
        for (uint8 cRoute; cRoute < 3; cRoute++) {
            x.conditionRoute = cRoute;
            for (uint8 wRoute; wRoute < 3; wRoute++) {
                x.winnerRoute = wRoute;
                for (uint8 paramType; paramType < 3; paramType++) {
                    x.paramType = paramType;
                    for (uint8 truth; truth < 2; truth++) {
                        x.condition = bytes32(uint256(truth == 0 ? 0 : 7));
                        for (uint8 size; size < 5; size++) {
                            if (wRoute != 0 && size != 3) {
                                continue;
                            }
                            x.size = size;
                            for (uint8 leafCase; leafCase < 9; leafCase++) {
                                x.leaf = sampleLeaf(leafCase);
                                check_condFetchedOrWinnerContext(x);
                            }
                        }
                    }
                }
            }
        }
    }

    function test_readGetOrArgumentContextSamples() public {
        fixtureGuards();
        vm.expectCall(address(hosts[0]), abi.encodePacked(ClaimOrContextHost.reply.selector), uint64(972));
        vm.expectCall(address(hosts[1]), abi.encodePacked(ClaimOrContextHost.reply.selector), uint64(648));
        vm.expectCall(address(hosts[2]), abi.encodePacked(ClaimOrContextHost.reply.selector), uint64(450));
        vm.expectCall(address(hosts[3]), abi.encodePacked(ClaimOrContextHost.reply.selector), uint64(252));
        vm.expectCall(address(hosts[1]), abi.encodePacked(ClaimOrContextHost.balanceOf.selector), uint64(162));
        vm.expectCall(address(hosts[2]), abi.encodePacked(ClaimOrContextHost.balanceOf.selector), uint64(126));
        vm.expectCall(address(hosts[3]), abi.encodePacked(ClaimOrContextHost.balanceOf.selector), uint64(90));
        vm.expectCall(address(hosts[5]), abi.encodePacked(ECHO), uint64(162));
        vm.expectCall(address(hosts[6]), abi.encodePacked(ClaimOrContextHost.reply.selector), uint64(0));
        CallCase memory x;
        for (uint8 bad; bad < 3; bad++) {
            x.bad = bad;
            x.words = [bytes32(uint256(11)), bytes32(uint256(13)), bytes32(uint256(15))];
            x.words[bad] = bytes32(uint256(7));
            for (uint8 route; route < 3; route++) {
                x.route = route;
                for (uint8 paramType; paramType < 3; paramType++) {
                    x.paramType = paramType;
                    for (uint8 mode; mode < 2; mode++) {
                        x.getRoute = mode == 1;
                        for (uint8 size; size < 4; size++) {
                            if (route != 0 && size != 3) {
                                continue;
                            }
                            x.size = size;
                            for (uint8 leafCase; leafCase < 9; leafCase++) {
                                x.leaf = sampleLeaf(leafCase);
                                check_readGetFetchedOrArgumentContext(x);
                            }
                        }
                    }
                }
            }
        }
    }

    function test_batchOrParamContextSamples() public {
        fixtureGuards();
        vm.expectCall(address(hosts[0]), abi.encodePacked(ClaimOrContextHost.reply.selector), uint64(360));
        vm.expectCall(address(hosts[1]), abi.encodePacked(ClaimOrContextHost.reply.selector), uint64(360));
        vm.expectCall(address(hosts[2]), abi.encodePacked(ClaimOrContextHost.reply.selector), uint64(282));
        vm.expectCall(address(hosts[3]), abi.encodePacked(ClaimOrContextHost.reply.selector), uint64(204));
        vm.expectCall(address(hosts[4]), abi.encodePacked(ClaimOrContextHost.reply.selector), uint64(204));
        vm.expectCall(address(hosts[5]), abi.encodePacked(ClaimOrContextHost.reply.selector), uint64(126));
        vm.expectCall(address(hosts[0]), abi.encodePacked(ClaimOrContextHost.balanceOf.selector), uint64(72));
        vm.expectCall(address(hosts[1]), abi.encodePacked(ClaimOrContextHost.balanceOf.selector), uint64(72));
        vm.expectCall(address(hosts[2]), abi.encodePacked(ClaimOrContextHost.balanceOf.selector), uint64(60));
        vm.expectCall(address(hosts[3]), abi.encodePacked(ClaimOrContextHost.balanceOf.selector), uint64(48));
        vm.expectCall(address(hosts[4]), abi.encodePacked(ClaimOrContextHost.balanceOf.selector), uint64(48));
        vm.expectCall(address(hosts[5]), abi.encodePacked(ClaimOrContextHost.balanceOf.selector), uint64(36));
        vm.expectCall(address(hosts[5]), abi.encodePacked(ECHO), uint64(0));
        vm.expectCall(address(hosts[6]), abi.encodePacked(ClaimOrContextHost.reply.selector), uint64(0));
        BatchCase memory x;
        for (uint8 entry; entry < 2; entry++) {
            x.entry = entry;
            for (uint8 paramCase; paramCase < 2; paramCase++) {
                x.paramCase = paramCase;
                for (uint256 i; i < 6; i++) {
                    x.words[i] = bytes32(uint256(11 + i * 2));
                }
                x.words[uint256(entry) * 3 + (paramCase == 0 ? 1 : 2)] = bytes32(uint256(7));
                for (uint8 route; route < 3; route++) {
                    x.route = route;
                    for (uint8 message; message < 2; message++) {
                        x.message = message == 1;
                        for (uint8 size; size < 5; size++) {
                            if (route != 0 && size != 3) {
                                continue;
                            }
                            x.size = size;
                            for (uint8 leafCase; leafCase < 9; leafCase++) {
                                x.leaf = sampleLeaf(leafCase);
                                check_batchFetchedOrParamContext(x);
                            }
                        }
                    }
                }
            }
        }
    }

    function sampleLeaf(uint8 which) internal pure returns (LeafCase memory x) {
        x.firstRef = bytes32(uint256(99));
        x.lower = bytes32(uint256(5));
        x.upper = bytes32(uint256(9));
        if (which == 1) {
            x.lower = bytes32(uint256(10));
            x.upper = bytes32(uint256(11));
        } else if (which == 2 || which == 3) {
            x.lower = bytes32(uint256(9));
            x.upper = bytes32(uint256(5));
            if (which == 3) {
                x.firstRef = bytes32(uint256(7));
            }
        } else if (which == 4 || which == 5) {
            x.fault = 1;
            if (which == 5) {
                x.firstRef = bytes32(uint256(7));
            }
        } else if (which == 6) {
            x.fault = 2;
        } else if (which == 7) {
            x.fault = 3;
        } else if (which == 8) {
            x.fault = 4;
        }
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
        return address(uint160(0xa110 + slot));
    }
}
