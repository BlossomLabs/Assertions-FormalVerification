#!/usr/bin/env python3
"""Fresh exact-post OOG target from native discovery; unchanged input premises."""
import ast
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
DRAFT = ROOT / 'gas-pilot-draft'
sys.path.insert(0, str(ROOT / 'tools'))
from inspect_nodes import cells


def literal(data):
    return 'b"' + ''.join(f'\\x{x:02x}' for x in data) + '"'


def main():
    source = DRAFT / 'specs/calloog.k'
    node = DRAFT / 'generated/calloog/GAS-PILOT-CALLOOG.cold-staticcall-memory-exhaustion/kcfg/nodes/40.json'
    c = {}
    cells(json.loads(node.read_text()), c)
    stack = []
    term = c['<wordStack>']
    while term['label']['name'] == '_:__EVM-TYPES_WordStack_Int_WordStack':
        value, term = term['args']
        assert value['node'] == 'KToken' and value['sort']['name'] == 'Int'
        stack.append(int(value['token']))
    assert term['label']['name'] == '.WordStack_EVM-TYPES_WordStack'
    memory = ast.literal_eval(c['<localMem>']['token'])
    gas = int(c['<gas>']['token'])
    call_gas = int(c['<callGas>']['token'])
    used = int(c['<memoryUsed>']['token'])
    assert gas == 470 and call_gas == 46320 and used == 5 and len(memory) == 160
    assert ast.literal_eval(c['<output>']['token']) == bytes.fromhex('d271060e')
    spec = source.read_text().replace('module GAS-PILOT-CALLOOG', 'module GAS-PILOT-CALLOOG2')
    replacements = {
        '?FINAL_STACK:WordStack': ' : '.join(map(str, stack)) + ' : .WordStack',
        '?FINAL_MEM:Bytes': literal(memory), '?FINAL_MEMORY_USED:Int': str(used),
        '?FINAL_GAS:Int': str(gas), '?FINAL_CALL_GAS:Gas': str(call_gas),
        '?FINAL_TOUCH:Set': 'SetItem(42334) SetItem(4369)',
    }
    for before, after in replacements.items():
        assert spec.count(before) == 1, before
        spec = spec.replace(before, after)
    with (DRAFT / 'specs/calloog2.k').open('x') as f:
        f.write(spec)
    record = {
        'sourceSpecSha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'retainedNativeNode': str(node.relative_to(DRAFT)),
        'retainedNativeNodeSha256': hashlib.sha256(node.read_bytes()).hexdigest(),
        'inputPremisesChanged': False, 'outputTargetGas': gas, 'outputCallGas': call_gas,
        'outputMemoryUsed': used, 'outputStack': stack,
        'outputMemorySha256': hashlib.sha256(memory).hexdigest(),
        'outputTouchSet': [42334, 4369], 'hiddenFinalFields': [],
        'scope': 'Fresh fixed-case consequent; complete native reexecution/cover required. No outcome/post-call-gas premise added.',
    }
    with (DRAFT / 'generated/calloog2-target-binding.json').open('x') as f:
        json.dump(record, f, indent=2)
        f.write('\n')
    print(json.dumps(record, indent=2))


if __name__ == '__main__':
    main()
