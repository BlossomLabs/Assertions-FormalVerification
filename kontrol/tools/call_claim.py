#!/usr/bin/env python3
"""Prepare one actual cold-target finite-gas STATICCALL; no mocked outcome."""
from pathlib import Path
import hashlib
import json

ROOT=Path(__file__).resolve().parents[2]
DRAFT=ROOT/'gas-pilot-draft'
MARKER=0xd271060e
CORE=42334
TARGET=4369


def literal(data):
    return 'b"'+''.join(f'\\x{x:02x}' for x in data)+'"'


def main():
    runtime=(ROOT/'target/runtime.bin').read_bytes()
    bitmap=(ROOT/'.generated/specs/jump-map.bin').read_bytes()
    assert hashlib.sha256(runtime).hexdigest()=='1a6a15fe275b0e8cc0e3ce02db213ccde722165142c2946fb5a94ddbbfc0eed1'
    callee=bytes.fromhex('63d271060e5f526004601cfd')
    memory=b''.join(x.to_bytes(32,'big') for x in [0,0,128,0])
    spec=f'''requires "../../out/kompiled/foundry.k"

module GAS-PILOT-CALLMARKER
    imports KONTROL-MAIN
    // Conditional internal _staticCall frame, exact finite initialgas50000.
    // The target is real native EVM code: PUSH4 marker/PUSH0/MSTORE/
    // PUSH1 4/PUSH1 28/REVERT. It consumes17 gas and returns exactly4 bytes.
    // No callee status/returndata/post-call-gas is assumed or mocked.
    claim [cold-staticcall-reserved-marker]:
        <k> #execute => #halt </k>
        <program> {literal(runtime)} </program>
        <jumpDests> {literal(bitmap)} </jumpDests>
        <pc> 4152 => 6481 </pc>
        <wordStack> 96 : {TARGET} : 4292 : .WordStack => ?FINAL_STACK:WordStack </wordStack>
        <localMem> {literal(memory)} => ?FINAL_MEM:Bytes </localMem>
        <memoryUsed> 4 => ?FINAL_MEMORY_USED:Int </memoryUsed>
        <gas> 50000 => ?FINAL_GAS:Int </gas>
        <callGas> 0 => ?FINAL_CALL_GAS:Gas </callGas>
        <callData> .Bytes </callData>
        <output> .Bytes => {literal(MARKER.to_bytes(4,'big'))} </output>
        <statusCode> EVMC_SUCCESS => EVMC_REVERT </statusCode>
        <id> {CORE} </id>
        <codeAddr> {CORE} </codeAddr>
        <caller> 1 </caller>
        <origin> 1 </origin>
        <callStack> .List </callStack>
        <interimStates> .List </interimStates>
        <touchedAccounts> .Set </touchedAccounts>
        <accessedAccounts> SetItem({CORE}) => SetItem({CORE}) SetItem({TARGET}) </accessedAccounts>
        <accounts>
            <account>
                <acctID> {CORE} </acctID>
                <balance> 0 </balance>
                <code> {literal(runtime)} </code>
                <storage> .Map </storage><origStorage> .Map </origStorage>
                <transientStorage> .Map </transientStorage><nonce> 1 </nonce>
            </account>
            <account>
                <acctID> {TARGET} </acctID>
                <balance> 0 </balance>
                <code> {literal(callee)} </code>
                <storage> .Map </storage><origStorage> .Map </origStorage>
                <transientStorage> .Map </transientStorage><nonce> 1 </nonce>
            </account>
        </accounts>
        <prank>
            <prevCaller> .Account </prevCaller><prevOrigin> .Account </prevOrigin>
            <newCaller> .Account </newCaller><newOrigin> .Account </newOrigin>
            <active> false </active><depth> 0 </depth><singleCall> false </singleCall>
        </prank>
        <expectedRevert>
            <isRevertExpected> false </isRevertExpected><expectedReason> .Bytes </expectedReason>
            <expectedDepth> 0 </expectedDepth>
        </expectedRevert>
        <expectedOpcode>
            <isOpcodeExpected> false </isOpcodeExpected><expectedAddress> .Account </expectedAddress>
            <expectedValue> 0 </expectedValue><expectedData> .Bytes </expectedData>
            <opcodeType> .OpcodeType </opcodeType>
        </expectedOpcode>
        <expectEmit>
            <recordEvent> false </recordEvent><isEventExpected> false </isEventExpected>
            <checkedTopics> .List </checkedTopics><checkedData> false </checkedData>
            <expectedEventAddress> .Account </expectedEventAddress>
        </expectEmit>
        <whitelist>
            <isCallWhitelistActive> false </isCallWhitelistActive><allowedCallsList> .List </allowedCallsList>
            <isStorageWhitelistActive> false </isStorageWhitelistActive><storageSlotList> .List </storageSlotList>
        </whitelist>
        <mockCalls> .Bag </mockCalls>
        <mockFunctions> .Bag </mockFunctions>
        <useGas> true </useGas>
        <stackChecks> true </stackChecks>
        <schedule> CANCUN </schedule>
        <mode> NORMAL </mode>
        <callValue> 0 </callValue>
        <static> true </static>
        <callDepth> 0 </callDepth>
endmodule
'''
    (DRAFT/'specs/callmarker.k').write_text(spec)
    (DRAFT/'generated/callmarker-binding.json').write_text(json.dumps({
        'entryPC':4152,'initialGas':50000,'core':CORE,'target':TARGET,'targetInitiallyCold':True,
        'calleeCodeHex':callee.hex(),'calleeSha256':hashlib.sha256(callee).hexdigest(),
        'calleeJumpMapSha256':hashlib.sha256(bytes(len(callee))).hexdigest(),
        'runtimeSha256':hashlib.sha256(runtime).hexdigest(),'jumpMapSha256':hashlib.sha256(bitmap).hexdigest(),
        'scope':'UNRUN draft; one concrete finite gas/caller/account/empty-calldata geometry, no general gas or OOG detector claim',
        'cheatcodes':'explicitly inactive; empty mockCalls/mockFunctions; no gas manipulation',
        'hiddenUnconstrainedFinalFields':['wordStack','localMem','memoryUsed','gas','callGas'],
        'constrainedConsequentOnlyVariables':[]},indent=2)+'\n')


if __name__=='__main__':
    main()
