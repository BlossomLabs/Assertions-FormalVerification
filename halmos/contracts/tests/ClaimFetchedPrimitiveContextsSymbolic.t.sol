// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../Assertions.sol";

/**
 * @dev Test-only weighted clock. Guarded replies and balances require the core
 *      caller; concrete samples independently test the guards/counts. This is
 *      bounded instrumentation, not a real staticcall gas or state model.
 */
contract ClaimPrimitiveContextHost {
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

    function reply(bytes calldata data, address caller_) external {
        VM.warp(block.timestamp + weight);
        require(msg.sender == caller_);
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
            calldatacopy(32, 0, calldatasize())
            return(0, add(32, calldatasize()))
        }
    }
}

/**
 * @notice Selected fetched primitive contexts. Targets resolve before args;
 *         cond validates the condition before the selected branch; pick
 *         resolves/validates before indexing. Fixtures are required to succeed,
 *         so no failed-subcall gas exclusion hides a fixture/caller error.
 */
contract ClaimFetchedPrimitiveContextsSymbolicTest is Test {
    struct TargetCase {
        uint96 upper;
        bytes32 argument;
        uint8 fault;
        uint8 size;
        uint8 paramType;
        bool getRoute;
        bool wrap;
    }

    struct CondCase {
        bytes32 condition;
        bytes32 winner;
        uint8 conditionRoute;
        uint8 winnerRoute;
        uint8 paramType;
        uint8 fault;
        uint8 size;
        bool extra;
    }

    struct PickCase {
        bytes32[2] words;
        uint8 route;
        uint8 paramType;
        uint8 size;
        uint8 fault;
        uint8 indexCase;
    }

    Assertions core;
    ClaimPrimitiveContextHost first;
    ClaimPrimitiveContextHost second;
    ClaimPrimitiveContextHost loser;
    address constant FIRST_ACCOUNT = address(0xa11ce);
    address constant SECOND_ACCOUNT = address(0xb0b);
    bytes4 constant ECHO = 0xcafef00d;

    function setUp() public {
        core = new Assertions();
        first = new ClaimPrimitiveContextHost(1);
        second = new ClaimPrimitiveContextHost(10);
        loser = new ClaimPrimitiveContextHost(100);
        first.configure(7, address(core), FIRST_ACCOUNT);
        second.configure(9, address(core), SECOND_ACCOUNT);
        loser.configure(11, address(core), address(0xbeef));
    }

    function check_fetchedReadGetTargetPrecedence(TargetCase memory x) public {
        vm.assume(x.fault < 5 && x.size < 3 && x.paramType < 3);
        vm.assume(x.fault != 2 || x.upper != 0);
        vm.assume(x.fault != 4 || x.upper == 0);
        vm.warp(1000);
        bytes32 word = bytes32((uint256(x.upper) << 160) | uint160(address(first)));
        bytes memory value = abi.encode(word);
        uint256 length = x.size == 0 ? 0 : x.size == 1 ? 1 : 31;
        if (x.fault == 3) {
            value = prefix(value, length);
        }
        InputParam memory target = reply(first, value, x.paramType);
        if (x.wrap) {
            target = InputParam(
                InputParamType(x.paramType),
                InputParamFetcherType.STATIC_CALL,
                abi.encode(address(core), abi.encodeCall(Assertions.resolve, (target))),
                new Constraint[](0)
            );
        }
        if (x.fault != 3) {
            target.constraints = new Constraint[](1);
            target.constraints[0] = Constraint(
                ConstraintType.EQ,
                x.fault == 1 ? bytes(hex"ff") : abi.encode(x.fault == 0 ? word ^ bytes32(uint256(1)) : word)
            );
        }
        InputParam[] memory args = new InputParam[](3);
        args[0] = reply(second, abi.encode(x.argument), x.paramType);
        args[0].constraints = new Constraint[](1);
        args[0].constraints[0] = Constraint(ConstraintType.EQ, abi.encode(x.argument ^ bytes32(uint256(1))));
        args[1] = skippedLoser(x.paramType);
        args[2] = args[1];
        (bool ok, bytes memory out) = address(core)
            .staticcall(
                x.getRoute
                    ? abi.encodeCall(Assertions.get, (target, ECHO, "(uint8[0])", args))
                    : abi.encodeCall(Assertions.read, (target, ECHO, args))
            );
        assertFalse(ok);
        bytes memory expected = x.fault == 0
            ? failed(0, word, word ^ bytes32(uint256(1)))
            : x.fault == 1
                ? badReference(0)
                : x.fault == 2
                    ? abi.encodeWithSelector(InvalidAddressWord.selector, uint256(0), word)
                    : x.fault == 3
                        ? abi.encodeWithSelector(ReturnDataOutOfBounds.selector, int256(0), length)
                        : failed(1, x.argument, x.argument ^ bytes32(uint256(1)));
        assertEq(out, expected);
        assertEq(first.count(), x.fault == 4 ? 11 : 1);
    }

    function check_condFetchedConditionWinnerContexts(CondCase memory x) public {
        vm.assume(x.conditionRoute < 3 && x.winnerRoute < 3 && x.paramType < 3 && x.fault < 6 && x.size < 5);
        vm.assume(x.conditionRoute == 0 || x.size == 3);
        vm.warp(1000);
        uint256 length = byteLength(x.size);
        (bool ok, bytes memory out, bytes memory actualWinner) = callCond(x, length);
        (bool succeeds, bytes memory expected, bool reachedWinner) = condExpected(x, length, actualWinner);
        assertEq(ok, succeeds);
        assertEq(out, expected);
        assertEq(first.count(), (x.conditionRoute == 1 ? 0 : 1) + (reachedWinner && x.winnerRoute != 1 ? 10 : 0));
    }

    function callCond(CondCase memory x, uint256 length)
        internal
        returns (bool ok, bytes memory out, bytes memory actualWinner)
    {
        bytes memory cValue = prefix(bytes.concat(abi.encode(x.condition), hex"7f"), length);
        (InputParam memory condition,) = fetch(first, FIRST_ACCOUNT, cValue, x.conditionRoute, x.paramType);
        if (x.fault == 1 || x.fault == 2) {
            condition.constraints = new Constraint[](1);
            condition.constraints[0] = Constraint(
                ConstraintType.EQ, x.fault == 1 ? abi.encode(x.condition ^ bytes32(uint256(1))) : bytes(hex"ff")
            );
        }
        bytes memory wValue =
            x.extra && x.winnerRoute == 0 ? bytes.concat(abi.encode(x.winner), hex"7f") : abi.encode(x.winner);
        InputParam memory winner;
        (winner, actualWinner) = fetch(second, SECOND_ACCOUNT, wValue, x.winnerRoute, x.paramType);
        if (x.fault >= 3) {
            winner.constraints = new Constraint[](1);
            winner.constraints[0] = Constraint(
                ConstraintType.EQ,
                x.fault == 4 ? bytes(hex"ff") : abi.encode(x.fault == 3 ? x.winner ^ bytes32(uint256(1)) : x.winner)
            );
        }
        bool truth = x.condition != bytes32(0);
        InputParam memory ignored = skippedLoser(x.paramType);
        (ok, out) = address(core)
            .staticcall(
                abi.encodeCall(Assertions.cond, (condition, truth ? winner : ignored, truth ? ignored : winner))
            );
    }

    function condExpected(CondCase memory x, uint256 length, bytes memory actualWinner)
        internal
        pure
        returns (bool succeeds, bytes memory expected, bool reachedWinner)
    {
        if (length < 32) {
            expected = abi.encodeWithSelector(ReturnDataOutOfBounds.selector, int256(0), length);
        } else if (x.fault == 1) {
            expected = failed(0, x.condition, x.condition ^ bytes32(uint256(1)));
        } else if (x.fault == 2) {
            expected = badReference(0);
        } else {
            reachedWinner = true;
            uint256 operand = x.condition != bytes32(0) ? 1 : 2;
            if (x.fault == 3) {
                expected = failed(operand, x.winner, x.winner ^ bytes32(uint256(1)));
            } else if (x.fault == 4) {
                expected = badReference(operand);
            } else {
                succeeds = true;
                expected = actualWinner;
            }
        }
    }

    function check_pickFetchedConstraintBeforeIndex(PickCase memory x) public {
        vm.assume(x.route < 3 && x.paramType < 3 && x.size < 8 && x.fault < 4 && x.indexCase < 6);
        vm.assume(x.route == 0 || x.size == 3);
        vm.warp(1000);
        uint256 length = byteLength(x.size);
        bytes memory value = prefix(bytes.concat(abi.encode(x.words), hex"7f"), length);
        (InputParam memory p, bytes memory actual) = fetch(first, FIRST_ACCOUNT, value, x.route, x.paramType);
        if (x.fault != 3) {
            p.constraints = new Constraint[](1);
            p.constraints[0] = Constraint(
                ConstraintType.EQ,
                x.fault == 2 ? bytes(hex"ff") : abi.encode(x.fault == 1 ? x.words[0] ^ bytes32(uint256(1)) : x.words[0])
            );
        }
        int256 index = x.indexCase == 0
            ? int256(0)
            : x.indexCase == 1
                ? int256(1)
                : x.indexCase == 2
                    ? int256(-1)
                    : x.indexCase == 3 ? int256(-2) : x.indexCase == 4 ? int256(2) : type(int256).min;
        (bool ok, bytes memory out) = address(core).staticcall(abi.encodeCall(Assertions.pick, (p, index)));
        bytes memory expected;
        bool succeeds;
        if (x.fault != 3 && length < 32) {
            expected = abi.encodeWithSelector(ReturnDataOutOfBounds.selector, int256(0), length);
        } else if (x.fault == 1) {
            expected = failed(0, x.words[0], x.words[0] ^ bytes32(uint256(1)));
        } else if (x.fault == 2) {
            expected = badReference(0);
        } else {
            uint256 words = actual.length / 32;
            bool inRange = index >= 0 ? uint256(index) < words : index >= -int256(words);
            if (inRange) {
                succeeds = true;
                int256 wanted = index < 0 ? int256(words) + index : index;
                expected = abi.encode(wanted == 0 ? x.words[0] : x.words[1]);
            } else {
                expected = abi.encodeWithSelector(ReturnDataOutOfBounds.selector, index, actual.length);
            }
        }
        assertEq(ok, succeeds);
        assertEq(out, expected);
        assertEq(first.count(), x.route == 1 ? 0 : 1);
    }

    function test_fetchedReadGetTargetSamples() public {
        fixtureGuards();
        vm.expectCall(address(first), abi.encodePacked(ClaimPrimitiveContextHost.reply.selector), uint64(84));
        vm.expectCall(address(second), abi.encodePacked(ClaimPrimitiveContextHost.reply.selector), uint64(12));
        vm.expectCall(address(loser), abi.encodePacked(ClaimPrimitiveContextHost.reply.selector), uint64(0));
        vm.expectCall(address(first), abi.encodePacked(ECHO), uint64(0));
        TargetCase memory x;
        x.argument = bytes32(uint256(7));
        for (uint8 paramType; paramType < 3; paramType++) {
            x.paramType = paramType;
            for (uint8 flags; flags < 4; flags++) {
                x.getRoute = flags >= 2;
                x.wrap = flags % 2 == 1;
                for (uint8 fault; fault < 5; fault++) {
                    x.fault = fault;
                    x.upper = fault == 2 ? 1 : 0;
                    for (uint8 size; size < (fault == 3 ? 3 : 1); size++) {
                        x.size = size;
                        check_fetchedReadGetTargetPrecedence(x);
                    }
                }
            }
        }
    }

    function test_condFetchedContextSamples() public {
        fixtureGuards();
        vm.expectCall(address(first), abi.encodePacked(ClaimPrimitiveContextHost.reply.selector), uint64(720));
        vm.expectCall(address(first), abi.encodePacked(ClaimPrimitiveContextHost.balanceOf.selector), uint64(144));
        vm.expectCall(address(second), abi.encodePacked(ClaimPrimitiveContextHost.reply.selector), uint64(192));
        vm.expectCall(address(second), abi.encodePacked(ClaimPrimitiveContextHost.balanceOf.selector), uint64(96));
        vm.expectCall(address(loser), abi.encodePacked(ClaimPrimitiveContextHost.reply.selector), uint64(0));
        vm.expectCall(address(first), abi.encodePacked(ECHO), uint64(0));
        CondCase memory x;
        x.winner = bytes32(uint256(9));
        for (uint8 cRoute; cRoute < 3; cRoute++) {
            x.conditionRoute = cRoute;
            for (uint8 wRoute; wRoute < 3; wRoute++) {
                x.winnerRoute = wRoute;
                for (uint8 paramType; paramType < 3; paramType++) {
                    x.paramType = paramType;
                    for (uint8 fault; fault < 6; fault++) {
                        x.fault = fault;
                        for (uint8 truth; truth < 2; truth++) {
                            x.condition = bytes32(uint256(truth == 0 ? 0 : 7));
                            for (uint8 size; size < 5; size++) {
                                if (cRoute != 0 && size != 3) {
                                    continue;
                                }
                                x.size = size;
                                for (uint8 extra; extra < (wRoute == 0 ? 2 : 1); extra++) {
                                    x.extra = extra == 1;
                                    check_condFetchedConditionWinnerContexts(x);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    function test_pickFetchedPrioritySamples() public {
        fixtureGuards();
        vm.expectCall(address(first), abi.encodePacked(ClaimPrimitiveContextHost.reply.selector), uint64(576));
        vm.expectCall(address(first), abi.encodePacked(ClaimPrimitiveContextHost.balanceOf.selector), uint64(72));
        vm.expectCall(address(second), abi.encodePacked(ClaimPrimitiveContextHost.reply.selector), uint64(0));
        vm.expectCall(address(loser), abi.encodePacked(ClaimPrimitiveContextHost.reply.selector), uint64(0));
        vm.expectCall(address(first), abi.encodePacked(ECHO), uint64(0));
        PickCase memory x;
        x.words[0] = bytes32(uint256(7));
        x.words[1] = bytes32(uint256(9));
        for (uint8 route; route < 3; route++) {
            x.route = route;
            for (uint8 paramType; paramType < 3; paramType++) {
                x.paramType = paramType;
                for (uint8 size; size < 8; size++) {
                    if (route != 0 && size != 3) {
                        continue;
                    }
                    x.size = size;
                    for (uint8 fault; fault < 4; fault++) {
                        x.fault = fault;
                        for (uint8 indexCase; indexCase < 6; indexCase++) {
                            x.indexCase = indexCase;
                            check_pickFetchedConstraintBeforeIndex(x);
                        }
                    }
                }
            }
        }
    }

    function fixtureGuards() internal {
        fixtureGuard(first, FIRST_ACCOUNT, 7, 1);
        fixtureGuard(second, SECOND_ACCOUNT, 9, 10);
        fixtureGuard(loser, address(0xbeef), 11, 100);
    }

    function fixtureGuard(ClaimPrimitiveContextHost h, address account, uint256 amount, uint256 weight) internal {
        (bool ok, bytes memory out) =
            address(h).call(abi.encodeCall(ClaimPrimitiveContextHost.reply, (hex"11", address(core))));
        assertFalse(ok, "reply refuses a non-core caller");
        assertEq(out, bytes(""));
        vm.warp(1000);
        vm.prank(address(core));
        (ok, out) = address(h).call(abi.encodeCall(ClaimPrimitiveContextHost.reply, (hex"117f", address(core))));
        assertTrue(ok);
        assertEq(out, hex"117f");
        assertEq(h.count(), weight);
        h.configure(amount, address(core), account);
        (ok, out) = address(h).call(abi.encodeCall(ClaimPrimitiveContextHost.balanceOf, (account)));
        assertFalse(ok, "balance refuses a non-core caller");
        assertEq(out, bytes(""));
        vm.prank(address(core));
        (ok, out) = address(h).call(abi.encodeCall(ClaimPrimitiveContextHost.balanceOf, (address(0xdead))));
        assertFalse(ok, "balance refuses a different account");
        assertEq(out, bytes(""));
        vm.warp(1000);
        vm.prank(address(core));
        (ok, out) = address(h).call(abi.encodeCall(ClaimPrimitiveContextHost.balanceOf, (account)));
        assertTrue(ok);
        assertEq(out, prefix(abi.encode(amount, bytes32(uint256(0x93)), bytes32(uint256(0x7f))), 65));
        assertEq(h.count(), weight);
        (ok, out) = address(h).call(abi.encodePacked(ECHO, hex"117f"));
        assertFalse(ok, "destination refuses a non-core caller");
        assertEq(out, bytes(""));
        vm.warp(1000);
        vm.prank(address(core));
        (ok, out) = address(h).call(abi.encodePacked(ECHO, hex"117f"));
        assertTrue(ok);
        assertEq(out, abi.encodePacked(bytes32(uint256(uint160(address(core)))), ECHO, hex"117f"));
        assertEq(h.count(), uint256(1000));
    }

    function fetch(ClaimPrimitiveContextHost h, address account, bytes memory value, uint8 route, uint8 paramType)
        internal
        returns (InputParam memory p, bytes memory actual)
    {
        if (route == 0) {
            return (reply(h, value, paramType), value);
        }
        assertTrue(value.length >= 32);
        uint256 amount;
        assembly ("memory-safe") { amount := mload(add(value, 32)) }
        vm.deal(account, amount);
        h.configure(amount, address(core), account);
        p = InputParam(
            InputParamType(paramType),
            InputParamFetcherType.BALANCE,
            abi.encodePacked(route == 1 ? address(0) : address(h), account),
            new Constraint[](0)
        );
        actual = abi.encode(amount);
    }

    function reply(ClaimPrimitiveContextHost h, bytes memory value, uint8 paramType)
        internal
        view
        returns (InputParam memory)
    {
        return InputParam(
            InputParamType(paramType),
            InputParamFetcherType.STATIC_CALL,
            abi.encode(address(h), abi.encodeCall(ClaimPrimitiveContextHost.reply, (value, address(core)))),
            new Constraint[](0)
        );
    }

    function skippedLoser(uint8 paramType) internal view returns (InputParam memory p) {
        p = reply(loser, abi.encode(uint256(0xbadc0de)), paramType);
        p.constraints = new Constraint[](1);
        p.constraints[0] = Constraint(ConstraintType.OR, hex"ff");
    }

    function failed(uint256 operand, bytes32 word, bytes32 referenceWord) internal pure returns (bytes memory) {
        return abi.encodeWithSelector(
            ConstraintFailed.selector,
            "",
            uint256(0),
            operand,
            uint256(0),
            ConstraintType.EQ,
            word,
            abi.encode(referenceWord)
        );
    }

    function badReference(uint256 operand) internal pure returns (bytes memory) {
        return abi.encodeWithSelector(InvalidConstraintData.selector, uint256(0), operand, uint256(0), uint256(1));
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
        if (size == 4) {
            return 33;
        }
        if (size == 5) {
            return 63;
        }
        if (size == 6) {
            return 64;
        }
        return 65;
    }

    function prefix(bytes memory data, uint256 length) internal pure returns (bytes memory out) {
        out = new bytes(length);
        for (uint256 i; i < length; i++) {
            out[i] = data[i];
        }
    }
}
