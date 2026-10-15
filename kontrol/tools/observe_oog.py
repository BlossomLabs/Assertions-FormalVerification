#!/usr/bin/env python3
"""Ground native fee simplification and instruction-precise guard GAS replay."""
import json
from pathlib import Path
import sys

from kevm_pyk.kevm import KEVM, KEVMSemantics
from kevm_pyk.utils import legacy_explore
from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KSort, KToken
from pyk.kast.manip import bottom_up
from pyk.proof.proof import Proof

ROOT = Path('/workspace')
DRAFT = ROOT / 'gas-pilot-draft'
sys.path.insert(0, str(ROOT / 'tools'))
from inspect_nodes import cells, text


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def int_token(value):
    return KToken(str(value), KSort('Int'))


def main():
    out = DRAFT / 'generated/observe-oog'
    out.mkdir(exist_ok=False)
    source = DRAFT / 'generated/calloog2'
    proof = Proof.read_proof_data(source, 'GAS-PILOT-CALLOOG2.cold-staticcall-memory-exhaustion')
    kevm = KEVM(ROOT / 'out/kompiled', use_directory=out)
    with legacy_explore(kevm, kcfg_semantics=KEVMSemantics(auto_abstract_gas=False),
                        id='observe-oog', smt_timeout=5000, smt_retry_limit=1,
                        log_succ_rewrites=True) as explore:
        fee = KApply('Cmem', [KApply('CANCUN_EVM'), int_token(134217729)])
        initial = proof.kcfg.node(proof.init).cterm
        def fee_in_int_slot(term):
            return KApply('<pc>', [fee]) if isinstance(term, KApply) and term.label.name == '<pc>' else term
        query = CTerm(bottom_up(fee_in_int_slot, initial.config), initial.constraints)
        result, logs = explore.cterm_symbolic.simplify(query)
        c = {}
        cells(result.to_dict(), c)
        save(out / 'native-memory-fee.json', {
            'queryKind': 'Ground official Cmem simplification in an Int configuration slot; no execution, proof premise or promoted rule',
            'input': query.to_dict(), 'output': result.to_dict(), 'logCount': len(logs),
            'memoryWords': 134217729, 'previousMemoryWords': 0,
            'memoryFee': text(c['<pc>']), 'availableGasAtFailure': 46317,
        })
        assert not result.is_bottom and c['<pc>'] == int_token(35184775266307).to_dict()
        state = proof.kcfg.node(34).cterm
        snapshots = []
        observed = False
        for step in range(50):
            raw = state.to_dict()
            sc = {}
            cells(raw, sc)
            snapshots.append({'step': step, 'state': raw})
            if text(sc['<pc>']) == '6424':
                assert text(sc['<gas>']) == '554'
                assert sc['<wordStack>']['args'][0] == int_token(554).to_dict()
                observed = True
                break
            execution = explore.cterm_symbolic.execute(state, depth=1)
            assert not execution.vacuous and not execution.next_states
            state = execution.state
            assert not state.is_bottom
        save(out / 'native-guard-gas-steps.json', {
            'sourceNode': 34, 'steps': snapshots, 'gasPC': 6423, 'observedGas': 554,
            'threshold': 751, 'thresholdTrue': True, 'observedDirectly': observed,
        })
        assert observed
    print(json.dumps({'nativeFee': 35184775266307, 'guardObservedGas': 554,
                      'threshold': 751, 'nativeGasSnapshotCount': len(snapshots)}, indent=2))


if __name__ == '__main__':
    main()
