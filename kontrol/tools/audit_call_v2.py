#!/usr/bin/env python3
"""Audit active/saved native call frames and real finite-gas call trace."""
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys

from kevm_pyk.kevm import KEVM, KEVMSemantics
from kevm_pyk.utils import legacy_explore
from pyk.kast.manip import free_vars
from pyk.proof.proof import Proof
from pyk.proof.reachability import APRProof

ROOT=Path('/workspace');DRAFT=ROOT/'gas-pilot-draft'
sys.path.insert(0,str(ROOT/'tools'))
from inspect_nodes import cells,text


def save(path,value):
    path.write_text(json.dumps(value,indent=2)+'\n')


def walk(value):
    if isinstance(value,dict):
        yield value
        for x in value.values():yield from walk(x)
    elif isinstance(value,list):
        for x in value:yield from walk(x)


def label(value):
    return value.get('label',{}).get('name') if isinstance(value,dict) else None


def main():
    out=DRAFT/'generated/audit-call2';out.mkdir(exist_ok=False)
    binding=json.loads((DRAFT/'generated/callmarker-binding.json').read_text())
    code_hashes={binding['runtimeSha256']:binding['jumpMapSha256'],
                 binding['calleeSha256']:binding['calleeJumpMapSha256']}
    engine=json.loads((ROOT/'out/kompiled/compiled.json').read_text())
    rules={}
    for item in walk(engine):
        if item.get('node')=='KRule':
            att=item.get('att',{}).get('att',{})
            if 'UNIQUE_ID' in att:rules[att['UNIQUE_ID']]=att
    kevm=KEVM(ROOT/'out/kompiled',use_directory=out)
    records=[]
    with legacy_explore(kevm,kcfg_semantics=KEVMSemantics(auto_abstract_gas=False),id='audit-call',
                        smt_timeout=5000,smt_retry_limit=1) as explore:
        for name in ['callmarker','callmarker2']:
            source=DRAFT/'generated'/name
            parsed=json.loads(next(source.glob('*.parsed.json.*')).read_text())['term']
            module=next(m for m in parsed['term'] if m['name']=='GAS-PILOT-'+name.upper())
            assert [x['name'] for x in module['imports']]==['KONTROL-MAIN']
            assert len(module['localSentences'])==1 and module['localSentences'][0]['node']=='KClaim'
            assert not any('trusted' in x['att']['att'] for x in module['localSentences'])
            save(out/(name+'-compiled-typed-claims.json'),module)
            p=next(source.glob('*/proof.json'));proof=Proof.read_proof_data(source,p.parent.name)
            assert isinstance(proof,APRProof) and not proof.admitted and not proof.subproof_ids and not proof.circularity
            initial=proof.kcfg.node(proof.init).cterm;target=proof.kcfg.node(proof.target).cterm
            only=target.free_vars-initial.free_vars
            constrained=set().union(*(free_vars(x) for x in target.constraints)) if target.constraints else set()
            assert not only&constrained
            summaries=[]
            for node in proof.kcfg.nodes:
                raw=node.cterm.to_dict();c={};cells(raw,c)
                assert text(c['<useGas>'])=='true' and text(c['<stackChecks>'])=='true'
                assert 'CANCUN' in text(c['<schedule>'])
                assert text(c['<active>'])==text(c['<isRevertExpected>'])==text(c['<isOpcodeExpected>'])=='false'
                assert text(c['<isCallWhitelistActive>'])==text(c['<isStorageWhitelistActive>'])=='false'
                # Empty typed cell maps exclude both kinds of mock dispatch.
                assert not any(label(x) in ['<mockCall>','<mockFunction>'] for x in walk(c['<mockCalls>']))
                assert not any(label(x) in ['<mockCall>','<mockFunction>'] for x in walk(c['<mockFunctions>']))
                evm=next(x for x in walk(raw['config']) if label(x)=='<evm>')
                active=next(x for x in evm['args'] if label(x)=='<callState>')
                frames=[]
                for frame in [x for x in walk(raw['config']) if label(x)=='<callState>']:
                    f={};cells(frame,f)
                    code=ast.literal_eval(f['<program>']['token']);bitmap=ast.literal_eval(f['<jumpDests>']['token'])
                    ch=hashlib.sha256(code).hexdigest();mh=hashlib.sha256(bitmap).hexdigest()
                    assert ch in code_hashes and mh==code_hashes[ch]
                    unaccepted_symbolic_target = name=='callmarker' and node.id==proof.target
                    if not unaccepted_symbolic_target:
                        assert f['<gas>']['node']=='KToken' and f['<gas>']['sort']['name']=='Int'
                        assert f['<callGas>']['node']=='KToken' and f['<callGas>']['sort']['name']=='Int'
                        assert int(f['<gas>']['token'])>=0 and int(f['<callGas>']['token'])>=0
                    else:
                        assert f['<gas>']['node']=='KVariable' and f['<callGas>']['node']=='KVariable'
                    # Unaccepted call1's declared target hides these values.
                    # Every executing/observed frame and every call2 target is
                    # still required to be an explicit finite native Int.
                    frames.append({'active':frame==active,'unacceptedDeclaredSymbolicTarget':unaccepted_symbolic_target,'runtimeSha256':ch,'jumpMapSha256':mh,
                                   'pc':text(f['<pc>']),'gas':text(f['<gas>']),'callGas':text(f['<callGas>']),
                                   'callDepth':text(f['<callDepth>']),'caller':text(f['<caller>']),
                                   'id':text(f['<id>']),'memoryUsed':text(f['<memoryUsed>'])})
                simplified,logs=explore.cterm_symbolic.simplify(node.cterm)
                assert not simplified.is_bottom
                save(out/(name+'-node-'+str(node.id)+'-nonbottom.json'),
                     {'input':raw,'simplified':simplified.to_dict(),'logCount':len(logs),'nonbottom':True})
                summaries.append({'id':node.id,'pc':text(c['<pc>']),'k':text(c['<k>']),
                                  'gas':text(c['<gas>']),'callGas':text(c['<callGas>']),
                                  'wordStack':text(c['<wordStack>']),'memoryUsed':text(c['<memoryUsed>']),
                                  'output':text(c['<output>']),'statusCode':text(c['<statusCode>']),
                                  'frames':frames,'nonbottom':True})
            graph=json.loads((p.parent/'kcfg/kcfg.json').read_text());covers=[]
            for cover in graph.get('covers',[]):
                a=proof.kcfg.node(cover['source']).cterm;b=proof.kcfg.node(cover['target']).cterm
                response=explore.cterm_symbolic.implies(a,b,assume_defined=False,failure_reason=False)
                assert response.csubst is not None and not response.csubst.constraints
                covers.append({'source':cover['source'],'target':cover['target'],'rawCsubst':response.csubst.to_dict()})
            serialized=json.loads(p.read_text());used=Counter()
            for entries in serialized['logs'].values():
                for entry in entries:
                    result=entry.get('result',{})
                    if result.get('tag')=='success' and 'rule-id' in result:used[result['rule-id']]+=1
            used_records=[]
            for uid,count in sorted(used.items()):
                assert uid in rules,uid
                used_records.append({'ruleId':uid,'count':count,'attributes':rules[uid]})
            save(out/(name+'-executed-rule-bindings.json'),used_records)
            labels={r['attributes'].get('label') for r in used_records}
            assert {'EVM.staticcall','EVM.call.true','EVM.return.revert','EVM.refund'}<=labels
            assert not any(x and ('mockCall' in x or 'mockFunction' in x or 'cheatcode.call.setGas' in x or 'cheatcode.call.infiniteGas' in x) for x in labels)
            record={'id':proof.id,'status':proof.status.name,'admitted':False,'subproofIds':[],
                    'circularity':False,'pending':[x.id for x in proof.pending],'failing':[x.id for x in proof.failing],
                    'bounded':[x.id for x in proof.bounded],'terminal':[x.id for x in proof.terminal],
                    'vacuous':[x.id for x in proof.kcfg.vacuous],'stuck':[x.id for x in proof.kcfg.stuck],
                    'target':proof.target,'targetOnlyVariables':sorted(only),'constrainedTargetOnlyVariables':sorted(only&constrained),
                    'covers':covers,'nodes':summaries,'executedRuleCount':len(used_records),'criticalNativeCallRulesConfirmed':True}
            if name=='callmarker2':
                assert record['status']=='PASSED'
                assert not any(record[k] for k in ['pending','failing','bounded','vacuous','stuck'])
                assert only=={next(v for v in only if v.startswith('GENERATEDCOUNTER_'))}
                assert set(record['terminal'])<={proof.target}|{x['source'] for x in covers if x['target']==proof.target}
                child_start=next(x for x in summaries if any(f['active'] and f['runtimeSha256']==binding['calleeSha256'] and f['pc']=='0' for f in x['frames']))
                child_end=next(x for x in summaries if any(f['active'] and f['runtimeSha256']==binding['calleeSha256'] and f['pc']=='11' for f in x['frames']))
                assert child_start['gas']=='46320' and child_end['gas']=='46303'
                record['calleeGasUsed']=17
            else:
                assert record['status']=='FAILED' and record['failing']==[41]
            records.append(record)
            save(out/'proofs.json',records)
    print(json.dumps([{k:v for k,v in r.items() if k!='nodes'} for r in records],indent=2))


if __name__=='__main__':
    main()
