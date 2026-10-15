#!/usr/bin/env python3
"""One native finite-gas APR proof; no custom rules or gas abstraction."""
import json
from pathlib import Path
import sys

from kevm_pyk.kevm import KEVM, KEVMSemantics
from kevm_pyk.utils import legacy_explore, run_prover
from kevm_pyk.__main__ import initialize_apr_proof
from pyk.proof.reachability import APRProof
from pyk.cterm import CTermSymbolic
from pyk.kcfg.explore import KCFGExplore
from pyk.kore.rpc import KoreClient

ROOT = Path('/workspace')
DRAFT = ROOT / 'gas-pilot-draft'


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def main():
    name = sys.argv[1]
    output = DRAFT / 'generated' / name
    output.mkdir(exist_ok=False)
    kevm = KEVM(ROOT / 'out/kompiled', use_directory=output)
    includes = [Path('/home/user/.local/lib/python3.10/site-packages') / p for p in
                ['kontrol/kdist', 'kevm_pyk/kproj/evm-semantics', 'kevm_pyk/kproj/plugin']]
    claims = kevm.get_claims(DRAFT / 'specs' / (name + '.k'), spec_module_name='GAS-PILOT-' + name.upper(),
                            include_dirs=includes, md_selector='k')
    semantics = KEVMSemantics(auto_abstract_gas=False)
    records = []
    with legacy_explore(kevm, kcfg_semantics=semantics, id=name, smt_timeout=5000,
                        smt_retry_limit=1, log_succ_rewrites=True, log_fail_rewrites=False) as explore:
        for claim in claims:
            proof = APRProof.from_claim(kevm.definition, claim, {}, proof_dir=output)
            source = proof.kcfg.node(proof.init).cterm
            target = proof.kcfg.node(proof.target).cterm
            save(output / (claim.label + '-pre-initialization.json'), source.to_dict())
            save(output / (claim.label + '-target.json'), target.to_dict())
            initialize_apr_proof(explore.cterm_symbolic, proof)
            simplified, _ = explore.cterm_symbolic.simplify(proof.kcfg.node(proof.init).cterm)
            assert not simplified.is_bottom
            save(output / (claim.label + '-initialized.json'), proof.kcfg.node(proof.init).cterm.to_dict())
            def create_explore():
                client = KoreClient('localhost', explore.cterm_symbolic._kore_client.port)
                symbolic = CTermSymbolic(client, kevm.definition, log_succ_rewrites=True, log_fail_rewrites=False)
                return KCFGExplore(symbolic, kcfg_semantics=semantics, id=proof.id)
            passed = run_prover(proof, create_kcfg_explore=create_explore, max_depth=100, max_iterations=150,
                cut_point_rules=KEVMSemantics.cut_point_rules(True, True, False, False, False, False),
                terminal_rules=KEVMSemantics.terminal_rules(False), max_frontier_parallel=1,
                force_sequential=True, assume_defined=False, optimize_kcfg=False)
            proof.write_proof_data()
            record = {'id': proof.id, 'passed': passed, 'status': proof.status.name, 'admitted': proof.admitted,
                      'subproofIds': list(proof.subproof_ids), 'circularity': proof.circularity,
                      'pending': [n.id for n in proof.pending], 'failing': [n.id for n in proof.failing],
                      'bounded': [n.id for n in proof.bounded], 'terminal': [n.id for n in proof.terminal],
                      'vacuous': [n.id for n in proof.kcfg.vacuous], 'stuck': [n.id for n in proof.kcfg.stuck],
                      'initialNonbottom': True, 'autoAbstractGas': False, 'assumeDefinedProver': False}
            records.append(record)
            save(output / 'result.json', records)
            print(json.dumps(record), flush=True)
    if not all(r['passed'] for r in records):
        raise SystemExit(2)


if __name__ == '__main__':
    main()
