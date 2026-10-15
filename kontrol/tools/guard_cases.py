#!/usr/bin/env python3
"""Bounded, loop-free literal guard geometries with symbolic finite gas."""
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DRAFT = ROOT / 'gas-pilot-draft'
MARKER = 0xd271060e


def literal(data):
    return 'b"' + ''.join(f'\\x{x:02x}' for x in data) + '"'


def words(values):
    return b''.join(x.to_bytes(32,'big') for x in values)


def main():
    runtime = (ROOT / 'target/runtime.bin').read_bytes()
    bitmap = (ROOT / '.generated/specs/jump-map.bin').read_bytes()
    assert hashlib.sha256(runtime).hexdigest() == '1a6a15fe275b0e8cc0e3ce02db213ccde722165142c2946fb5a94ddbbfc0eed1'
    assert hashlib.sha256(bitmap).hexdigest() == 'dd88c1231eb06cc02bd2a36bea2ab5eb5b95b0c50eb72a3654a39f18cd9c8aa5'
    def memory(n, final=False):
        prefix = literal(words([0,0,224,0,n]))
        body = 'Int2Bytes(32, HEAD *Int (2 ^Int 224), BE)' if n == 4 else literal(words([MARKER << 224 if n == 36 else 0]))
        payload = 'Int2Bytes(32, PAYLOAD, BE)' if n == 36 else literal(words([0]))
        end = literal(words([MARKER << 224 if final else 0]))
        return f'({prefix} +Bytes {body} +Bytes {payload} +Bytes {end})'
    def claim(label,n,kind,negative=False):
        delta = 104 if n == 4 else 90
        gas_condition = f'ENTRY -Int {delta} <=Int BEFORE /Int 63' if kind == 'threshold' else f'BEFORE /Int 63 <Int ENTRY -Int {delta}'
        if kind == 'marker':
            gas_condition += f' andBool HEAD ==Int {MARKER}'
        elif kind == 'ordinary' and n == 4:
            gas_condition += f' andBool HEAD =/=Int {MARKER}'
        is_return = kind == 'ordinary' or negative
        k = 'JUMP 4292 ~> #pc [ JUMP ] ~> #execute' if is_return else '#halt'
        pc = 6486 if is_return else 6481
        post_stack = '.WordStack' if is_return else f'{"HEAD *Int (2 ^Int 224)" if n == 4 else "0"} : 128 : BEFORE : 4292 : .WordStack'
        gas_cost = delta + (92 if is_return else 84 if kind == 'threshold' else 122)
        fields = f'''        <k> #execute => {k} </k>
        <program> {literal(runtime)} </program>
        <jumpDests> {literal(bitmap)} </jumpDests>
        <pc> 6394 => {pc} </pc>
        <wordStack> 128 : BEFORE : 4292 : .WordStack => {post_stack} </wordStack>
        <localMem> {memory(n)}{'' if is_return else ' => '+memory(n,True)} </localMem>
        <memoryUsed> 8 </memoryUsed>
        <gas> ENTRY => ENTRY -Int {gas_cost} </gas>
        <callGas> 0 </callGas>
        <output> .Bytes{'' if is_return else ' => '+literal(MARKER.to_bytes(4,'big'))} </output>
        <statusCode> EVMC_SUCCESS{'' if is_return else ' => EVMC_REVERT'} </statusCode>
        <useGas> true </useGas>
        <stackChecks> true </stackChecks>
        <schedule> CANCUN </schedule>
        <mode> NORMAL </mode>
        <callValue> 0 </callValue>
        <static> true </static>
        <callDepth> 0 </callDepth>
      requires 300 <=Int ENTRY andBool ENTRY <=Int BEFORE
       andBool BEFORE <Int 18446744073709551616
       andBool {gas_condition}'''
        if n == 4:
            fields += '\n       andBool 0 <=Int HEAD andBool HEAD <Int 4294967296'
        if n == 36:
            fields += '\n       andBool 0 <=Int PAYLOAD andBool PAYLOAD <Int 2 ^Int 256'
        return '    claim ['+label+']:\n'+fields+'\n'
    cases = {
        'threshold0correct': [('empty-ret-threshold-revert',0,'threshold',False)],
        'guard4': [('four-byte-threshold-revert',4,'threshold',False),
                   ('four-byte-marker-revert',4,'marker',False),
                   ('four-byte-ordinary-returns',4,'ordinary',False)],
        'guard36': [('marker-plus-payload-threshold-revert',36,'threshold',False),
                    ('marker-plus-payload-ordinary-returns',36,'ordinary',False)],
        'negative': [('false-threshold-accepts',0,'threshold',True),
                     ('false-marker-accepts',4,'marker',True)],
    }
    for name, claims in cases.items():
        content = 'requires "../../out/kompiled/foundry.k"\n\nmodule GAS-PILOT-'+name.upper()+'\n    imports KONTROL-MAIN\n\n'
        content += '\n'.join(claim(*args) for args in claims) + 'endmodule\n'
        (DRAFT / 'specs' / (name+'.k')).write_text(content)


if __name__ == '__main__':
    main()
