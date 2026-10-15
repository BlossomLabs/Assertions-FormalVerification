#!/usr/bin/env python3
"""Extract immutable compiler/source correspondence, not an EVM evaluator."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DRAFT = ROOT / 'gas-pilot-draft'


def main():
    compiled = json.loads((ROOT / '.generated/exact-artifact.json').read_text())
    inputs = json.loads((ROOT / '.generated/compiler-input.json').read_text())
    outputs = json.loads((ROOT / '.generated/compiler-output.json').read_text())
    source = inputs['sources']['project/contracts/Assertions.sol']['content']
    source_ast = outputs['sources']['project/contracts/Assertions.sol']['ast']
    def visit(value):
        if isinstance(value, dict):
            yield value
            for x in value.values():
                yield from visit(x)
        elif isinstance(value, list):
            for x in value:
                yield from visit(x)
    guard = next(x for x in visit(source_ast) if x.get('nodeType') == 'FunctionDefinition' and x.get('name') == '_rejectOutOfGas')
    static = next(x for x in visit(source_ast) if x.get('nodeType') == 'FunctionDefinition' and x.get('name') == '_staticCall')
    starts, length, _ = map(int, guard['src'].split(':'))
    obj = compiled['evm']['deployedBytecode']
    code = bytes.fromhex(obj['object'])
    assert code == (ROOT / 'target/runtime.bin').read_bytes()
    prev = ['', '', '', '', '']
    source_map = []
    for segment in obj['sourceMap'].split(';'):
        for i, value in enumerate(segment.split(':')):
            if value != '':
                prev[i] = value
        source_map.append(list(prev))
    pc = 0
    i = 0
    rows = []
    opcode_tokens = obj['opcodes'].split()
    token_index = 0
    while pc < len(code):
        opcode = code[pc]
        width = opcode - 0x5f if 0x60 <= opcode <= 0x7f else 0
        if 4152 <= pc <= 4310 or 6394 <= pc <= 6486 or 17874 <= pc <= 17892:
            mapping = source_map[i]
            rows.append({'pc': pc, 'opcode': opcode_tokens[token_index],
                         'immediateHex': code[pc+1:pc+1+width].hex(), 'sourceMap': mapping,
                         'sourceText': source[int(mapping[0]):int(mapping[0])+int(mapping[1])]
                         if mapping[2] == '0' else None})
        pc += width + 1
        i += 1
        token_index += 2 if width else 1
    result = {'revision':'6a497132c59731535fa405162d0212bccec66f2f',
              'runtimeBytes':len(code),'runtimeSha256':hashlib.sha256(code).hexdigest(),
              'sourceSha256':hashlib.sha256(source.encode()).hexdigest(),
              'guardSource':source[starts:starts+length], 'guardAST':guard, 'callerAST':static,
              'functionDebugData':{k:v for k,v in obj['functionDebugData'].items()
                                   if any(s in k for s in ['rejectOut', 'staticCall', 'callFailed'])},
              'disassemblySourceCorrespondence':rows,
              'entryPC':6394,'observationGasPC':6423,'callerBeforeGasPC':4183,'callForwardGasPC':4221,
              'staticCallPC':4222,'revertPC':6481,'callerGuardReturnPC':4292,
              'scope':'Compiler/source/runtime identity and disassembly only; no behavior proof.'}
    (DRAFT / 'generated/guard-binding.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['runtimeBytes','runtimeSha256','sourceSha256','entryPC','observationGasPC','revertPC']},indent=2))


if __name__ == '__main__':
    main()
