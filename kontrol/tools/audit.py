#!/usr/bin/env python3
"""Audit native graph/runtime/gas/scopes with raw nonbottom evidence."""
import ast
import hashlib
import json
from pathlib import Path
import sys

from kevm_pyk.kevm import KEVM, KEVMSemantics
from kevm_pyk.utils import legacy_explore
from pyk.kast.inner import KApply, KToken, KSort, Subst
from pyk.kast.manip import free_vars
from pyk.cterm import CTerm
from pyk.proof.reachability import APRProof
from pyk.proof.proof import Proof

ROOT = Path('/workspace')
DRAFT = ROOT / 'gas-pilot-draft'
sys.path.insert(0,str(ROOT/'tools'))
from inspect_nodes import cells, text


def save(path,value):
    path.write_text(json.dumps(value,indent=2)+'\n')


def walk(value):
    if isinstance(value,dict):
        yield value
        for x in value.values():
            yield from walk(x)
    elif isinstance(value,list):
        for x in value:
            yield from walk(x)


def main():
    name = sys.argv[1]
    out = DRAFT/'generated'/('audit-'+name)
    out.mkdir(exist_ok=False)
    kevm = KEVM(ROOT/'out/kompiled',use_directory=out)
    source = DRAFT/'generated'/name
    parsed_file = next(source.glob('*.parsed.json.*'))
    parsed = json.loads(parsed_file.read_text())['term']
    module = next(m for m in parsed['term'] if m['name']=='GAS-PILOT-'+name.upper())
    assert [x['name'] for x in module['imports']] == ['KONTROL-MAIN']
    assert all(x['node']=='KClaim' for x in module['localSentences'])
    assert not any('trusted' in x['att']['att'] for x in module['localSentences'])
    save(out/'compiled-typed-claims.json',module)
    engine = json.loads((ROOT/'out/kompiled/parsed.json').read_text())['term']
    engine_modules = engine['modules'] if 'modules' in engine else engine.get('term',[])
    main_module = next(m for m in engine_modules if m.get('name')=='KONTROL-MAIN')
    assert [x['name'] for x in main_module['imports']] == ['KONTROL-FULL']
    assert not main_module['localSentences']
    save(out/'engine-main-module.json',main_module)
    previous_imports=json.loads((ROOT/'.generated/audit-final-3/imports.json').read_text())
    for path,digest in previous_imports.items():
        assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==digest,path
    save(out/'pinned-imports-rechecked.json',previous_imports)
    records=[]
    with legacy_explore(kevm,kcfg_semantics=KEVMSemantics(auto_abstract_gas=False),id='audit-'+name,
                        smt_timeout=5000,smt_retry_limit=1) as explore:
        for p in sorted(source.glob('*/proof.json')):
            proof=Proof.read_proof_data(source,p.parent.name)
            assert isinstance(proof,APRProof)
            assert not proof.admitted and not proof.subproof_ids and not proof.circularity
            initial=proof.kcfg.node(proof.init).cterm
            target=proof.kcfg.node(proof.target).cterm
            target_only=target.free_vars-initial.free_vars
            constrained_vars=set().union(*(free_vars(x) for x in target.constraints)) if target.constraints else set()
            assert not (target_only & constrained_vars)
            low='threshold' in proof.id
            marker='marker-revert' in proof.id or 'false-marker' in proof.id
            witness_values={'ENTRY':300 if low else 10000,'BEFORE':20000 if low else 10000,
                            'HEAD':0xd271060e if marker else 0,'PAYLOAD':7}
            substitution=Subst({k:KToken(str(v),KSort('Int')) for k,v in witness_values.items()
                                if k in initial.free_vars})
            witness=CTerm.from_kast(substitution(initial.kast))
            simplified_witness,witness_logs=explore.cterm_symbolic.simplify(witness)
            assert not simplified_witness.is_bottom
            save(out/(proof.id+'-antecedent-witness.json'),{'values':witness_values,
                 'input':witness.to_dict(),'simplified':simplified_witness.to_dict(),
                 'nonbottom':True,'logCount':len(witness_logs)})
            summaries=[]
            for node in proof.kcfg.nodes:
                c={};cells(node.cterm.to_dict(),c)
                code=ast.literal_eval(c['<program>']['token'])
                bitmap=ast.literal_eval(c['<jumpDests>']['token'])
                assert hashlib.sha256(code).hexdigest()=='1a6a15fe275b0e8cc0e3ce02db213ccde722165142c2946fb5a94ddbbfc0eed1'
                assert hashlib.sha256(bitmap).hexdigest()=='dd88c1231eb06cc02bd2a36bea2ab5eb5b95b0c50eb72a3654a39f18cd9c8aa5'
                assert text(c['<useGas>'])=='true'
                assert text(c['<stackChecks>'])=='true'
                assert 'CANCUN' in text(c['<schedule>'])
                assert not any(x.get('label',{}).get('name')=='infGas' for x in walk(c['<gas>']))
                simplified,logs=explore.cterm_symbolic.simplify(node.cterm)
                assert not simplified.is_bottom
                save(out/(proof.id+'-node-'+str(node.id)+'-nonbottom.json'),
                     {'input':node.cterm.to_dict(),'simplified':simplified.to_dict(),'logCount':len(logs)})
                summaries.append({'id':node.id,'pc':text(c['<pc>']),'k':text(c['<k>']),
                                  'gas':text(c['<gas>']),'wordStack':text(c['<wordStack>']),
                                  'output':text(c['<output>']),'statusCode':text(c['<statusCode>']),
                                  'nonbottom':True,'runtimeSha256':hashlib.sha256(code).hexdigest(),
                                  'jumpMapSha256':hashlib.sha256(bitmap).hexdigest()})
            record={'id':proof.id,'status':proof.status.name,'admitted':proof.admitted,
                    'subproofIds':list(proof.subproof_ids),'circularity':proof.circularity,
                    'target':proof.target,'pending':[x.id for x in proof.pending],
                    'failing':[x.id for x in proof.failing],'bounded':[x.id for x in proof.bounded],
                    'terminal':[x.id for x in proof.terminal],'vacuous':[x.id for x in proof.kcfg.vacuous],
                    'stuck':[x.id for x in proof.kcfg.stuck],
                    'initialVariables':sorted(initial.free_vars),'targetOnlyVariables':sorted(target_only),
                    'constrainedTargetOnlyVariables':sorted(target_only & constrained_vars),'nodes':summaries}
            graph=json.loads((p.parent/'kcfg/kcfg.json').read_text())
            covers=[]
            for cover in graph.get('covers',[]):
                a=proof.kcfg.node(cover['source']).cterm
                b=proof.kcfg.node(cover['target']).cterm
                response=explore.cterm_symbolic.implies(a,b,assume_defined=False,failure_reason=False)
                assert response.csubst is not None
                assert not response.csubst.constraints
                covers.append({'source':cover['source'],'target':cover['target'],
                               'rawRecheckedCsubst':response.csubst.to_dict(), 'logCount':len(response.logs)})
            record['recheckedCovers']=covers
            if proof.status.name=='PASSED':
                assert not any(record[x] for x in ['pending','failing','bounded','vacuous','stuck'])
                # Actual successful REVERT leaves are terminal AND covered by
                # the declared exact halt target. They are completed executions,
                # not excluded paths. Keep both facts explicit.
                covered_to_target={x['source'] for x in covers if x['target']==proof.target}
                assert set(record['terminal']) <= covered_to_target|{proof.target}
                record['uncoveredTerminalNodes']=sorted(set(record['terminal'])-covered_to_target-{proof.target})
            records.append(record)
    save(out/'proofs.json',records)
    print(json.dumps([{k:v for k,v in r.items() if k not in ['nodes','initialVariables']} for r in records],indent=2))


if __name__=='__main__':
    main()
