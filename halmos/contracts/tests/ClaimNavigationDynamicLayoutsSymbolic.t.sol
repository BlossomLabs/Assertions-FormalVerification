// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../Assertions.sol";
import {AbiCodec} from "../lib/AbiCodec.sol";

/**
 * @notice Finite typed dynamic-array navigation and consumer/error priorities.
 *         solc encodes every independent terminal oracle. Counts and copying
 *         lengths are literal cases; selected element paths require an element.
 *         Sibling relations change terminal words with canonical structure.
 *         These fixtures establish no arbitrary-count, nesting or gas result.
 */
contract ClaimNavigationDynamicLayoutsSymbolicTest is Test {
    struct Item {
        uint8 tag;
        bytes data;
    }

    struct WideItem {
        uint256 tag;
        bytes data;
    }

    struct CanonicalCase {
        bytes32[2] a;
        bytes32[2] b;
        uint8 first;
        uint8 second;
        uint8 sizeA;
        uint8 sizeB;
        uint8 count;
        uint8 mode;
        uint8 selection;
        bool child;
    }

    struct TagCase {
        bytes32 selected;
        bytes32[2] beforeWords;
        bytes32[2] afterWords;
        bool second;
    }

    struct TupleFaultCase {
        bytes32[2] words;
        bytes32 skippedTag;
        bytes32 skippedBlob;
        uint8 size;
        uint8 mode;
        bool second;
        bool dirtyPadding;
    }

    struct FixedFaultCase {
        bytes4 content;
        bytes32 otherRowFirst;
        bytes32 otherRowSecond;
        bool second;
        bool child;
        bool selectedDirty;
        bool siblingDirty;
        uint8 mode;
    }

    Assertions core;
    int256 constant LEN = type(int256).min;
    int256 constant PAYLOAD = type(int256).min + 1;
    bytes32 constant FIRST = bytes32(uint256(0xa11ce));
    bytes32 constant SECOND = bytes32(uint256(0xb0b));
    string constant TUPLES = "((uint8,bytes)[])";
    string constant FIXED = "(bytes[2][])";

    function setUp() public {
        core = new Assertions();
    }

    function check_navTupleArraySolcTerminals(CanonicalCase memory x) public view {
        vm.assume(x.count < 3 && x.mode < 7 && x.selection < 4 && x.sizeA < 5 && x.sizeB < 5);
        vm.assume(x.count != 0 || x.mode == 0 || x.mode == 4);
        bytes memory a = payload(x.a, x.sizeA);
        bytes memory b = payload(x.b, x.sizeB);
        Item[] memory items = x.count == 0 ? new Item[](0) : x.count == 1 ? new Item[](1) : new Item[](2);
        if (x.count != 0) {
            items[0] = Item(x.first, a);
        }
        if (x.count == 2) {
            items[1] = Item(x.second, b);
        }
        Item memory selected =
            x.count == 2 && (x.selection == 1 || x.selection == 2) ? Item(x.second, b) : Item(x.first, a);
        int256[] memory path = tuplePath(x.count, x.selection, x.mode);
        bytes memory expected;
        if (x.mode == 0) {
            expected = abi.encode(items);
        } else if (x.mode == 1) {
            expected = abi.encode(selected);
        } else if (x.mode == 2) {
            expected = abi.encode(selected.tag);
        } else if (x.mode == 3) {
            expected = abi.encode(selected.data);
        } else if (x.mode == 4) {
            expected = abi.encode(items.length);
        } else if (x.mode == 5) {
            expected = abi.encode(selected.data.length);
        } else {
            expected = selected.data;
        }
        success(abi.encode(items), TUPLES, path, expected);
    }

    function check_navFixedDynamicArraySolcTerminals(CanonicalCase memory x) public view {
        vm.assume(x.count < 3 && x.mode < 6 && x.selection < 4 && x.sizeA < 5 && x.sizeB < 5);
        vm.assume(x.count != 0 || x.mode == 0 || x.mode == 3);
        bytes memory a = payload(x.a, x.sizeA);
        bytes memory b = payload(x.b, x.sizeB);
        bytes[2][] memory rows = x.count == 0 ? new bytes[2][](0) : x.count == 1 ? new bytes[2][](1) : new bytes[2][](2);
        if (x.count != 0) {
            rows[0] = [a, b];
        }
        if (x.count == 2) {
            rows[1] = [b, a];
        }
        bool secondRow = x.count == 2 && (x.selection == 1 || x.selection == 2);
        bytes[2] memory selected = secondRow ? [b, a] : [a, b];
        bytes memory selectedBytes = x.child ? selected[1] : selected[0];
        int256[] memory path = fixedPath(x.count, x.selection, x.child, x.mode);
        bytes memory expected;
        if (x.mode == 0) {
            expected = abi.encode(rows);
        } else if (x.mode == 1) {
            expected = abi.encode(selected);
        } else if (x.mode == 2) {
            expected = abi.encode(selectedBytes);
        } else if (x.mode == 3) {
            expected = abi.encode(rows.length);
        } else if (x.mode == 4) {
            expected = abi.encode(selectedBytes.length);
        } else {
            expected = selectedBytes;
        }
        success(abi.encode(rows), FIXED, path, expected);
    }

    function check_navTupleTagIgnoresBytes(TagCase memory x) public view {
        WideItem[] memory items = wideItems();
        bytes memory markers = abi.encode(items);
        uint256 tagOffset = findWord(markers, x.second ? SECOND : FIRST);
        uint256 firstBlob = findWord(markers, bytes32(bytes1(0x11)));
        uint256 secondBlob = findWord(markers, bytes32(bytes1(0x22)));
        bytes memory beforeData = abi.encode(items);
        putWord(beforeData, tagOffset, x.selected);
        putWord(beforeData, firstBlob, x.beforeWords[0]);
        putWord(beforeData, secondBlob, x.beforeWords[1]);
        bytes memory afterData = abi.encode(items);
        putWord(afterData, tagOffset, x.selected);
        putWord(afterData, firstBlob, x.afterWords[0]);
        putWord(afterData, secondBlob, x.afterWords[1]);
        int256[] memory path = path3(0, x.second ? int256(-1) : int256(0), 0);
        (bool beforeOk, bytes memory beforeOut) = nav(beforeData, TUPLES, path);
        (bool afterOk, bytes memory afterOut) = nav(afterData, TUPLES, path);
        bool clean = uint256(x.selected) <= 255;
        assertEq(beforeOk, clean);
        assertEq(afterOk, clean);
        bytes memory expected = clean
            ? abi.encode(uint8(uint256(x.selected)))
            : abi.encodeWithSelector(AbiCodec.InvalidValue.selector, tagOffset);
        assertEq(beforeOut, expected);
        assertEq(afterOut, expected);
    }

    function check_navTupleBytesConsumerFaults(TupleFaultCase memory x) public view {
        vm.assume(x.size < 3 && x.mode < 3);
        uint256 length = paddingLength(x.size);
        bytes memory value = prefix(abi.encode(x.words), length);
        WideItem[] memory markers = wideItems();
        markers[0].data = markerPayload(x.second ? 1 : length, 0x11);
        markers[1].data = markerPayload(x.second ? length : 1, 0x22);
        bytes memory fixture = abi.encode(markers);
        uint256 tagOffset = findWord(fixture, x.second ? SECOND : FIRST);
        uint256 blobOffset = findWord(fixture, x.second ? bytes32(bytes1(0x22)) : bytes32(bytes1(0x11)));
        uint256 siblingOffset = findWord(fixture, x.second ? bytes32(bytes1(0x11)) : bytes32(bytes1(0x22)));
        WideItem[] memory items = wideItems();
        if (x.second) {
            items[1].data = value;
        } else {
            items[0].data = value;
        }
        bytes memory data = abi.encode(items);
        putWord(data, tagOffset, x.skippedTag);
        putWord(data, siblingOffset, x.skippedBlob);
        if (x.dirtyPadding) {
            data[blobOffset + length] = 0x7f;
        }
        int256[] memory path = new int256[](x.mode == 0 ? 3 : 4);
        path[0] = 0;
        path[1] = x.second ? int256(-1) : int256(0);
        path[2] = 1;
        if (x.mode != 0) {
            path[3] = x.mode == 1 ? LEN : PAYLOAD;
        }
        if (x.mode == 0 && x.dirtyPadding) {
            failure(data, TUPLES, path, abi.encodeWithSelector(AbiCodec.InvalidValue.selector, blobOffset + length));
        } else {
            bytes memory expected = x.mode == 0 ? abi.encode(value) : x.mode == 1 ? abi.encode(length) : value;
            success(data, TUPLES, path, expected);
        }
    }

    function check_navFixedArrayBytesConsumerFaults(FixedFaultCase memory x) public view {
        vm.assume(x.mode < 4);
        bytes[2][] memory markers = fixedRows(hex"11223344");
        bytes memory fixture = abi.encode(markers);
        uint256 firstOffset = findWord(fixture, x.second ? bytes32(bytes1(0x33)) : bytes32(bytes1(0x11)));
        uint256 secondOffset = findWord(fixture, x.second ? bytes32(bytes1(0x44)) : bytes32(bytes1(0x22)));
        bytes[2][] memory rows = fixedRows(x.content);
        bytes memory data = abi.encode(rows);
        putWord(data, findWord(fixture, x.second ? bytes32(bytes1(0x11)) : bytes32(bytes1(0x33))), x.otherRowFirst);
        putWord(data, findWord(fixture, x.second ? bytes32(bytes1(0x22)) : bytes32(bytes1(0x44))), x.otherRowSecond);
        if (x.selectedDirty) {
            data[(x.child ? secondOffset : firstOffset) + 1] = 0x7f;
        }
        if (x.siblingDirty) {
            data[(x.child ? firstOffset : secondOffset) + 1] = 0x7f;
        }
        int256[] memory path = new int256[](x.mode == 1 ? 2 : x.mode == 0 ? 3 : 4);
        path[0] = 0;
        path[1] = x.second ? int256(-1) : int256(0);
        if (x.mode != 1) {
            path[2] = x.child ? int256(-1) : int256(0);
        }
        if (x.mode > 1) {
            path[3] = x.mode == 2 ? LEN : PAYLOAD;
        }
        bytes[2] memory selected = x.second ? rows[1] : rows[0];
        bytes memory selectedBytes = x.child ? selected[1] : selected[0];
        if (x.mode == 1 && (x.selectedDirty || x.siblingDirty)) {
            bool firstDirty = x.child ? x.siblingDirty : x.selectedDirty;
            failure(
                data,
                FIXED,
                path,
                abi.encodeWithSelector(AbiCodec.InvalidValue.selector, (firstDirty ? firstOffset : secondOffset) + 1)
            );
        } else if (x.mode == 0 && x.selectedDirty) {
            failure(
                data,
                FIXED,
                path,
                abi.encodeWithSelector(AbiCodec.InvalidValue.selector, (x.child ? secondOffset : firstOffset) + 1)
            );
        } else {
            bytes memory expected = x.mode == 1
                ? abi.encode(selected)
                : x.mode == 0 ? abi.encode(selectedBytes) : x.mode == 2 ? abi.encode(uint256(1)) : selectedBytes;
            success(data, FIXED, path, expected);
        }
    }

    function check_navDynamicElementMissingOffsetPriority(uint8 size, uint8 indexCase) public view {
        vm.assume(size < 3 && indexCase < 4);
        uint256 length = size == 0 ? 64 : size == 1 ? 65 : 95;
        bytes memory data = prefix(abi.encode(wideItems()), length);
        // Root offset/count fit, and count 2 passes the production coarse
        // count <= whole result.length / 32 guard. _normalizeIndex runs before
        // the selected element offset word is read at byte 64 or byte 96.
        assertEq(readWord(data, 0), 32);
        assertEq(readWord(data, 32), 2);
        int256 index =
            indexCase == 0 ? int256(2) : indexCase == 1 ? int256(-3) : indexCase == 2 ? int256(0) : int256(-1);
        int256[] memory path = new int256[](2);
        path[0] = 0;
        path[1] = index;
        bytes memory expected = indexCase < 2
            ? abi.encodeWithSelector(ElementIndexOutOfBounds.selector, index, uint256(2))
            : abi.encodeWithSelector(ReturnDataOutOfBounds.selector, indexCase == 2 ? int256(2) : int256(3), length);
        failure(data, TUPLES, path, expected);
    }

    function test_navTupleArraySolcGeometryMatrix() public view {
        CanonicalCase memory x = concreteCase();
        for (uint8 count; count < 3; count++) {
            x.count = count;
            for (uint8 a; a < 5; a++) {
                x.sizeA = a;
                for (uint8 b; b < 5; b++) {
                    x.sizeB = b;
                    for (uint8 mode; mode < 7; mode++) {
                        if (count == 0 && mode != 0 && mode != 4) {
                            continue;
                        }
                        x.mode = mode;
                        x.selection = 2;
                        check_navTupleArraySolcTerminals(x);
                    }
                }
            }
        }
        x.count = 2;
        for (uint8 selection; selection < 4; selection++) {
            x.selection = selection;
            for (uint8 mode = 1; mode < 7; mode++) {
                x.mode = mode;
                check_navTupleArraySolcTerminals(x);
            }
        }
    }

    function test_navFixedDynamicArraySolcGeometryMatrix() public view {
        CanonicalCase memory x = concreteCase();
        for (uint8 count; count < 3; count++) {
            x.count = count;
            for (uint8 a; a < 5; a++) {
                x.sizeA = a;
                for (uint8 b; b < 5; b++) {
                    x.sizeB = b;
                    for (uint8 mode; mode < 6; mode++) {
                        if (count == 0 && mode != 0 && mode != 3) {
                            continue;
                        }
                        x.mode = mode;
                        x.selection = 2;
                        x.child = false;
                        check_navFixedDynamicArraySolcTerminals(x);
                        x.child = true;
                        check_navFixedDynamicArraySolcTerminals(x);
                    }
                }
            }
        }
        x.count = 2;
        for (uint8 selection; selection < 4; selection++) {
            x.selection = selection;
            for (uint8 mode = 1; mode < 6; mode++) {
                x.mode = mode;
                check_navFixedDynamicArraySolcTerminals(x);
            }
        }
    }

    function test_navTupleTagSiblingRelationSamples() public view {
        TagCase memory x;
        x.beforeWords = [bytes32(uint256(7)), bytes32(uint256(9))];
        x.afterWords = [bytes32(type(uint256).max), bytes32(uint256(256))];
        for (uint8 element; element < 2; element++) {
            x.second = element == 1;
            x.selected = bytes32(uint256(255));
            check_navTupleTagIgnoresBytes(x);
            x.selected = bytes32(uint256(256));
            check_navTupleTagIgnoresBytes(x);
        }
    }

    function test_navTupleBytesConsumerFaultMatrix() public view {
        TupleFaultCase memory x;
        x.words = [bytes32(uint256(0x1234)), bytes32(type(uint256).max)];
        x.skippedTag = bytes32(type(uint256).max);
        x.skippedBlob = bytes32(type(uint256).max);
        for (uint8 size; size < 3; size++) {
            x.size = size;
            for (uint8 mode; mode < 3; mode++) {
                x.mode = mode;
                for (uint8 flags; flags < 4; flags++) {
                    x.second = flags & 1 != 0;
                    x.dirtyPadding = flags & 2 != 0;
                    check_navTupleBytesConsumerFaults(x);
                }
            }
        }
    }

    function test_navFixedBytesConsumerFaultMatrix() public view {
        FixedFaultCase memory x;
        x.content = hex"abcd0123";
        x.otherRowFirst = bytes32(type(uint256).max);
        x.otherRowSecond = bytes32(uint256(256));
        for (uint8 flags; flags < 16; flags++) {
            x.second = flags & 1 != 0;
            x.child = flags & 2 != 0;
            x.selectedDirty = flags & 4 != 0;
            x.siblingDirty = flags & 8 != 0;
            for (uint8 mode; mode < 4; mode++) {
                x.mode = mode;
                check_navFixedArrayBytesConsumerFaults(x);
            }
        }
    }

    function test_navMissingElementOffsetPriorityMatrix() public view {
        for (uint8 size; size < 3; size++) {
            for (uint8 indexCase; indexCase < 4; indexCase++) {
                check_navDynamicElementMissingOffsetPriority(size, indexCase);
            }
        }
    }

    function concreteCase() internal pure returns (CanonicalCase memory x) {
        x.a = [bytes32(type(uint256).max), bytes32(uint256(0x1234))];
        x.b = [bytes32(uint256(0xabcd)), bytes32(uint256(0x5678))];
        x.first = 7;
        x.second = 255;
    }

    function tuplePath(uint8 count, uint8 selection, uint8 mode) internal pure returns (int256[] memory path) {
        path = new int256[](mode == 0 ? 1 : mode == 1 || mode == 4 ? 2 : mode < 4 ? 3 : 4);
        path[0] = 0;
        if (mode == 4) {
            path[1] = LEN;
        } else if (mode != 0) {
            path[1] = selectedIndex(count, selection);
            if (mode > 1) {
                path[2] = mode == 2 ? int256(0) : int256(1);
            }
            if (mode > 4) {
                path[3] = mode == 5 ? LEN : PAYLOAD;
            }
        }
    }

    function fixedPath(uint8 count, uint8 selection, bool child, uint8 mode)
        internal
        pure
        returns (int256[] memory path)
    {
        path = new int256[](mode == 0 ? 1 : mode == 1 || mode == 3 ? 2 : mode == 2 ? 3 : 4);
        path[0] = 0;
        if (mode == 3) {
            path[1] = LEN;
        } else if (mode != 0) {
            path[1] = selectedIndex(count, selection);
            if (mode > 1) {
                path[2] = child ? int256(-1) : int256(0);
            }
            if (mode > 3) {
                path[3] = mode == 4 ? LEN : PAYLOAD;
            }
        }
    }

    function selectedIndex(uint8 count, uint8 selection) internal pure returns (int256) {
        if (selection == 0) {
            return 0;
        }
        if (selection == 1) {
            return count == 2 ? int256(1) : int256(0);
        }
        if (selection == 2) {
            return -1;
        }
        return count == 2 ? int256(-2) : int256(-1);
    }

    function wideItems() internal pure returns (WideItem[] memory items) {
        items = new WideItem[](2);
        items[0] = WideItem(uint256(FIRST), hex"11");
        items[1] = WideItem(uint256(SECOND), hex"22");
    }

    function fixedRows(bytes4 content) internal pure returns (bytes[2][] memory rows) {
        rows = new bytes[2][](2);
        rows[0][0] = abi.encodePacked(content[0]);
        rows[0][1] = abi.encodePacked(content[1]);
        rows[1][0] = abi.encodePacked(content[2]);
        rows[1][1] = abi.encodePacked(content[3]);
    }

    function markerPayload(uint256 length, bytes1 marker) internal pure returns (bytes memory data) {
        data = new bytes(length);
        data[0] = marker;
    }

    function payload(bytes32[2] memory words, uint8 size) internal pure returns (bytes memory) {
        return prefix(abi.encode(words), size == 0 ? 0 : size == 1 ? 1 : size == 2 ? 31 : size == 3 ? 32 : 33);
    }

    function paddingLength(uint8 size) internal pure returns (uint256) {
        if (size == 0) {
            return 1;
        }
        if (size == 1) {
            return 31;
        }
        return 33;
    }

    function prefix(bytes memory data, uint256 length) internal pure returns (bytes memory out) {
        out = new bytes(length);
        for (uint256 i; i < length; i++) {
            out[i] = data[i];
        }
    }

    function path3(int256 first, int256 second, int256 third) internal pure returns (int256[] memory path) {
        path = new int256[](3);
        path[0] = first;
        path[1] = second;
        path[2] = third;
    }

    function readWord(bytes memory data, uint256 offset) internal pure returns (uint256 word) {
        assertTrue(offset <= data.length && data.length - offset >= 32);
        assembly ("memory-safe") { word := mload(add(add(data, 32), offset)) }
    }

    function putWord(bytes memory data, uint256 offset, bytes32 word) internal pure {
        assertTrue(offset <= data.length && data.length - offset >= 32);
        assembly ("memory-safe") { mstore(add(add(data, 32), offset), word) }
    }

    function findWord(bytes memory data, bytes32 marker) internal pure returns (uint256 offset) {
        uint256 matches;
        for (uint256 i; i + 32 <= data.length; i += 32) {
            if (bytes32(readWord(data, i)) == marker) {
                offset = i;
                matches++;
            }
        }
        assertEq(matches, 1, "independent marker must be unique");
    }

    function nav(bytes memory data, string memory descriptor, int256[] memory path)
        internal
        view
        returns (bool ok, bytes memory out)
    {
        InputParam memory p =
            InputParam(InputParamType.CALL_DATA, InputParamFetcherType.RAW_BYTES, data, new Constraint[](0));
        return address(core).staticcall(abi.encodeCall(Assertions.nav, (p, descriptor, path)));
    }

    function success(bytes memory data, string memory descriptor, int256[] memory path, bytes memory expected)
        internal
        view
    {
        (bool ok, bytes memory out) = nav(data, descriptor, path);
        assertTrue(ok, "canonical selected terminal must succeed");
        assertEq(out, expected);
    }

    function failure(bytes memory data, string memory descriptor, int256[] memory path, bytes memory expected)
        internal
        view
    {
        (bool ok, bytes memory out) = nav(data, descriptor, path);
        assertFalse(ok);
        assertEq(out, expected);
    }
}
