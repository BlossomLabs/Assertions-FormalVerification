#!/usr/bin/env python3
"""Emit finite-gas guard obligations bound to frozen exact runtime."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DRAFT = ROOT / 'gas-pilot-draft'
MARKER = 0xd271060e


def literal(data):
    return 'b"' + ''.join(f'\\x{x:02x}' for x in data) + '"'


def word(x):
    return x.to_bytes(32, 'big')


def main():
    runtime = (ROOT / 'target/runtime.bin').read_bytes()
    bitmap = (ROOT / '.generated/specs/jump-map.bin').read_bytes()
    assert hashlib.sha256(runtime).hexdigest() == '1a6a15fe275b0e8cc0e3ce02db213ccde722165142c2946fb5a94ddbbfc0eed1'
    assert hashlib.sha256(bitmap).hexdigest() == 'dd88c1231eb06cc02bd2a36bea2ab5eb5b95b0c50eb72a3654a39f18cd9c8aa5'
    # Eight allocated words, bytes object at128, free pointer224. Its last
    # allocated word provides the exact error-write window without expansion.
    memory = b''.join(word(x) for x in [0,0,224,0,0,0,0,0])
    final = memory[:224] + word(MARKER << 224)
    spec = f'''requires "../../out/kompiled/foundry.k"

module GAS-PILOT-THRESHOLD0
    imports KONTROL-MAIN
    // Actual private guard entry; initial gas is finite Int, never #gas/infGas.
    // GAS atPC6423 observes ENTRY-90 after its own2-gas charge. This theorem
    // assumes an already established caller frame/memory and ample parent gas.
    claim [empty-ret-threshold-revert]:
        <k> #execute => #halt </k>
        <program> {literal(runtime)} </program>
        <jumpDests> {literal(bitmap)} </jumpDests>
        <pc> 6394 => 6482 </pc>
        <wordStack> 128 : BEFORE : 4292 : .WordStack => 0 : 128 : BEFORE : 4292 : .WordStack </wordStack>
        <localMem> {literal(memory)} => {literal(final)} </localMem>
        <memoryUsed> 8 </memoryUsed>
        <gas> ENTRY => ENTRY -Int 174 </gas>
        <callGas> 0 </callGas>
        <output> .Bytes => {literal(MARKER.to_bytes(4,'big'))} </output>
        <statusCode> EVMC_SUCCESS => EVMC_REVERT </statusCode>
        <useGas> true </useGas>
        <stackChecks> true </stackChecks>
        <schedule> CANCUN </schedule>
        <mode> NORMAL </mode>
        <callValue> 0 </callValue>
        <static> true </static>
        <callDepth> 0 </callDepth>
      requires 300 <=Int ENTRY andBool ENTRY <=Int BEFORE
       andBool BEFORE <Int 18446744073709551616
       andBool ENTRY -Int 90 <=Int BEFORE /Int 63
endmodule
'''
    (DRAFT / 'specs/threshold0.k').write_text(spec)
    (DRAFT / 'generated/initial-scope.json').write_text(json.dumps({
        'entryPC':6394,'sourceGasPC':6423,'returnPC':4292,'literalReturnLength':0,
        'finiteInitialGas':'ENTRY:Int','observedGas':'ENTRY-90','proposedRevertGas':'ENTRY-174',
        'memoryGeometry':'256 literal bytes; bytes object128, FMP224, memoryUsed8',
        'scope':'Conditional exact internal guard only; caller establishment/failed STATICCALL not yet proved',
        'arbitraryHelpers':False,'runtimeSha256':hashlib.sha256(runtime).hexdigest(),
        'jumpMapSha256':hashlib.sha256(bitmap).hexdigest()},indent=2)+'\n')


if __name__ == '__main__':
    main()
