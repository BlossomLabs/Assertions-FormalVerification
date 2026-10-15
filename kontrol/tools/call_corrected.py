#!/usr/bin/env python3
"""Fresh exact-post target from retained native outcome; no input change."""
import ast
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT=Path(__file__).resolve().parents[2]
DRAFT=ROOT/'gas-pilot-draft'
sys.path.insert(0,str(ROOT/'tools'))
from inspect_nodes import cells


def literal(data):
    return 'b"'+''.join(f'\\x{x:02x}' for x in data)+'"'


def main():
    source=DRAFT/'specs/callmarker.k'
    node=DRAFT/'generated/callmarker/GAS-PILOT-CALLMARKER.cold-staticcall-reserved-marker/kcfg/nodes/41.json'
    c={};cells(json.loads(node.read_text()),c)
    stack=[]
    term=c['<wordStack>']
    while term['label']['name']=='_:__EVM-TYPES_WordStack_Int_WordStack':
        value,term=term['args']
        assert value['node']=='KToken' and value['sort']['name']=='Int'
        stack.append(int(value['token']))
    assert term['label']['name']=='.WordStack_EVM-TYPES_WordStack'
    memory=ast.literal_eval(c['<localMem>']['token'])
    gas=int(c['<gas>']['token']);call_gas=int(c['<callGas>']['token']);used=int(c['<memoryUsed>']['token'])
    assert gas==46646 and call_gas==46320 and used==7 and len(memory)==224
    spec=source.read_text().replace('module GAS-PILOT-CALLMARKER','module GAS-PILOT-CALLMARKER2')
    replacements={
        '?FINAL_STACK:WordStack': ' : '.join(map(str,stack))+' : .WordStack',
        '?FINAL_MEM:Bytes':literal(memory),'?FINAL_MEMORY_USED:Int':str(used),
        '?FINAL_GAS:Int':str(gas),'?FINAL_CALL_GAS:Gas':str(call_gas),
        '<touchedAccounts> .Set </touchedAccounts>':'<touchedAccounts> .Set => SetItem(42334) SetItem(4369) </touchedAccounts>',
    }
    for before,after in replacements.items():
        assert spec.count(before)==1,before
        spec=spec.replace(before,after)
    (DRAFT/'specs/callmarker2.k').write_text(spec)
    (DRAFT/'generated/callmarker2-target-binding.json').write_text(json.dumps({
        'sourceSpecSha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'retainedNativeNode':str(node.relative_to(DRAFT)),'retainedNativeNodeSha256':hashlib.sha256(node.read_bytes()).hexdigest(),
        'inputPremisesChanged':False,'outputTargetGas':gas,'outputCallGas':call_gas,'outputMemoryUsed':used,
        'outputStack':stack,'outputMemorySha256':hashlib.sha256(memory).hexdigest(),
        'correctedPostTouchSet':[42334,4369],'hiddenFinalFields':[],
        'scope':'Fresh candidate consequent only; actual execution/complete cover still required. No outcome or post-call gas added to antecedent.'},indent=2)+'\n')


if __name__=='__main__':
    main()
