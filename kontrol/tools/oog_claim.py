#!/usr/bin/env python3
"""Prepare one real huge-offset MLOAD callee under unchanged fixed caller inputs."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DRAFT = ROOT / 'gas-pilot-draft'


def literal(data):
    return 'b"' + ''.join(f'\\x{x:02x}' for x in data) + '"'


def main():
    original = DRAFT / 'specs/callmarker.k'
    spec = original.read_text()
    old = bytes.fromhex('63d271060e5f526004601cfd')
    callee = bytes.fromhex('63ffffffff5100')
    assert spec.count(literal(old)) == 1
    spec = spec.replace('module GAS-PILOT-CALLMARKER', 'module GAS-PILOT-CALLOOG')
    spec = spec.replace('[cold-staticcall-reserved-marker]', '[cold-staticcall-memory-exhaustion]')
    spec = spec.replace(literal(old), literal(callee))
    spec = spec.replace('    // The target is real native EVM code: PUSH4 marker/PUSH0/MSTORE/\n'
                        '    // PUSH1 4/PUSH1 28/REVERT. It consumes17 gas and returns exactly4 bytes.\n',
                        '    // The real loop-free target is PUSH4 0xffffffff/MLOAD/STOP.\n'
                        '    // Its memory-expansion gas charge must be evaluated by native semantics.\n')
    spec = spec.replace('<touchedAccounts> .Set </touchedAccounts>',
                        '<touchedAccounts> .Set => ?FINAL_TOUCH:Set </touchedAccounts>')
    output = DRAFT / 'specs/calloog.k'
    with output.open('x') as f:
        f.write(spec)
    binding = {
        'sourceFixture': str(original.relative_to(DRAFT)),
        'sourceFixtureSha256': hashlib.sha256(original.read_bytes()).hexdigest(),
        'onlyInputChange': 'target code; caller gas/context/accounts/calldata unchanged',
        'entryPC': 4152, 'initialGas': 50000, 'core': 42334, 'target': 4369,
        'targetInitiallyCold': True, 'calleeCodeHex': callee.hex(),
        'calleeSha256': hashlib.sha256(callee).hexdigest(),
        'calleeJumpMapSha256': hashlib.sha256(bytes(len(callee))).hexdigest(),
        'runtimeSha256': hashlib.sha256((ROOT / 'target/runtime.bin').read_bytes()).hexdigest(),
        'jumpMapSha256': hashlib.sha256((ROOT / '.generated/specs/jump-map.bin').read_bytes()).hexdigest(),
        'scope': 'UNRUN discovery formulation; fixed50000gas coldtarget internal fixture only. No OOG status/result/post-call gas premise.',
        'hiddenUnconstrainedFinalFields': ['wordStack', 'localMem', 'memoryUsed', 'gas', 'callGas', 'touchedAccounts'],
        'constrainedConsequentOnlyVariables': [],
        'parentOutcomeToCheck': 'exact four-byte SubcallOutOfGas marker via actual remaining-gas threshold',
    }
    with (DRAFT / 'generated/calloog-binding.json').open('x') as f:
        json.dump(binding, f, indent=2)
        f.write('\n')
    print(json.dumps(binding, indent=2))


if __name__ == '__main__':
    main()
