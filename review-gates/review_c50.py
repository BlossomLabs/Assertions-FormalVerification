"""Independent exact-runtime C50 acceptance, distinct from source acceptance."""
import argparse,csv,hashlib,json,re,subprocess,sys
from pathlib import Path
from check import ROOT,LIBRARY,digest
from declarations import declarations

compact=lambda s:re.sub(r'\s+','',s)

def validate(capture_dir,native_dir,native_review,concrete_dir,faults_dir,binding=None):
    binding=binding or LIBRARY/'bytecode/c50/runtime-binding.json'
    fixed=json.loads(binding.read_text());cap=json.loads((capture_dir/'manifest.json').read_text())
    ledger=json.loads((ROOT/'docs/claim-evidence.json').read_text())['claims']['C50']
    assert fixed['claim']=='C50' and fixed['recordedClaim']==ledger['recordedClaim']
    assert hashlib.sha256(ledger['recordedClaim'].encode()).hexdigest()==fixed['statementSha256']
    for key in ['runtimeSha256','runtimeLength','selector','compilerSha256','sources','settings']:
        assert cap[key]==fixed[key], 'Current compiler/runtime binding drift: '+key
    assert cap['status']=='exact-current-runtime-captured'
    assert digest(ROOT/'formal/tools/capture_c50.py')==cap['captureScriptSha256']
    for name in ['input','output']:
        assert digest(capture_dir/('solc-'+name+'.json'))==cap[name+'Sha256']
    code=bytes.fromhex((capture_dir/'runtime.hex').read_text())
    assert len(code)==fixed['runtimeLength'] and hashlib.sha256(code).hexdigest()==fixed['runtimeSha256']
    artifact=json.loads((ROOT/'artifacts/contracts/Assertions.sol/Assertions.json').read_text())
    assert code.hex()==artifact['deployedBytecode'][2:] and digest(ROOT/'artifacts/contracts/Assertions.sol/Assertions.json')==cap['artifactSha256']
    request=json.loads((capture_dir/'solc-input.json').read_text())
    assert request['settings']==fixed['settings']
    assert digest(ROOT/'proof-tools/assertions/solc-0.8.36')==fixed['compilerSha256']
    # Recompile independently from the reviewed compiler request, not its receipt flag.
    replay=subprocess.run([str(ROOT/'proof-tools/assertions/solc-0.8.36'),'--standard-json'],input=json.dumps(request),capture_output=True,text=True,cwd=ROOT)
    assert replay.returncode==0,replay.stderr
    compiled=json.loads(replay.stdout);assert not any(e['severity']=='error' for e in compiled.get('errors',[]))
    contract=compiled['contracts']['project/contracts/Assertions.sol']['Assertions']
    assert contract['evm']['deployedBytecode']['object']==code.hex()
    assert contract['evm']['bytecode']['object']==artifact['bytecode'][2:]
    assert not contract['evm']['deployedBytecode']['immutableReferences']
    assert contract['evm']['methodIdentifiers']['chain((uint8,uint8,bytes,(uint8,bytes)[]),bytes[])']==fixed['selector']
    for name,source in request['sources'].items():
        assert hashlib.sha256(source['content'].encode()).hexdigest()==fixed['sources'][name]
        if name.startswith('project/'):
            local=ROOT/name[len('project/'):]
        else:
            assert name.startswith('npm/@openzeppelin/contracts@5.6.1/')
            local=ROOT/'node_modules/@openzeppelin/contracts'/name[len('npm/@openzeppelin/contracts@5.6.1/'):]
        assert digest(local)==fixed['sources'][name], 'Current source changed: '+name
    mapping=json.loads((LIBRARY/'claims.json').read_text())['claims']['C50']['bytecodeProofs']
    assert len(mapping)==1 and mapping[0]['coverage']=='full' and mapping[0]['package']==fixed['package']
    assert mapping[0]['assumptions']==fixed['scope']
    assert mapping[0]['theorems']==[{'declaration':fixed['proofSource']+'::'+n,'fullSha256':fixed['declarations'][n]['fullSha256']} for n in ['FullC50','RunMatchesKernel']]
    entry=ROOT/fixed['proofSource'];items=declarations(entry)
    assert digest(entry)==fixed['proofSourceSha256']
    for name,record in fixed['declarations'].items():
        assert hashlib.sha256(items[name]['interface'].encode()).hexdigest()==record['interfaceSha256']
        assert hashlib.sha256(items[name]['full'].encode()).hexdigest()==record['fullSha256']
    # Reject a rebound certificate that silently narrows the public-entry domain.
    expected_domain='''{ ctx.callValue == 0 && 68 <= |ctx.callData| <= MAX_I256 &&
      H(ctx) as int / TWO_224 == 0xa5c16924 &&
      A(ctx) as int <= MAX_U64 && (A(ctx) as nat)+132 <= |ctx.callData| &&
      B(ctx) as int <= MAX_U64 && (B(ctx) as nat)+36 <= |ctx.callData| &&
      ctx.CallDataRead(((B(ctx) as nat)+4) as u256) == 0 }'''
    assert compact(items['ValidEmptyCall']['body'])==compact(expected_domain),'Narrowed or changed input domain'
    assert compact(items['Ready']['body'])==compact('{ st.evm.fork == EvmFork.CANCUN && Runtime(st.evm.code) && ValidEmptyCall(st.evm.context) }')
    assert compact(items['Step']['body'])==compact('{ EVM.Execute(st) }'),'Execution is not the actual pinned kernel'
    for name,offset in [('A',4),('B',36),('H',0)]:
        assert compact(items[name]['body'])==compact('{ ctx.CallDataRead('+str(offset)+') }')
    assert compact(items['L']['body'])==compact('{ ctx.CallDataSize() }')
    expected_entry='''ghost method FullC50(st:ExecutingState) returns(out:State)
      requires Ready(st)
      requires st.PC()==0 && st.evm.stack.contents==[] && st.evm.memory.contents==[]
      requires st.Gas()>=693
      ensures out == Run(st,204)
      ensures out == EVM.ExecuteN(st,204)
      ensures out == ERROR(REVERTS,gas:=st.Gas()-693,data:=[57,85,175,170])'''
    assert compact(items['FullC50']['interface'])==compact(expected_entry),'Changed theorem scope or result'
    native=json.loads((native_dir/'manifest.json').read_text());review=json.loads(native_review.read_text())
    assert native['package']==fixed['package'] and native['status']=='native-gates-passed'
    assert review['status']=='independently-reviewed-native-closure' and review['manifestSha256']==digest(native_dir/'manifest.json')
    assert native['sources']==json.loads((LIBRARY/'packages/c50-current-bytecode/canonical.json').read_text())['closureSha256']
    observed=set();batches=0
    for gate in native['commands']:
        label,command=gate['gate'],gate['command'];log=(native_dir/(label+'.log')).read_text()
        if label.startswith('proof-'):
            assert '--verify-included-files' in command and '--filter-symbol' not in command
            assert '--manual-lemma-induction' in command and '--isolate-assertions' in command
            assert command[command.index('--verification-time-limit')+1]=='30'
            rows=list(csv.DictReader((native_dir/(label+'.csv')).open()));summary=re.search(r'finished with (\d+) verified, (\d+) errors?',log)
            assert rows and summary and int(summary[1])==len(rows) and int(summary[2])==0
            assert not re.search(r'Error:|timed out|inconclusive',log,re.I)
            assert all(r['TestResult.Outcome']=='Passed' for r in rows)
            observed.update(r['TestResult.DisplayName'].split(' (')[0] for r in rows);batches+=len(rows)
        elif label.startswith('audit-'):assert 'auditor completed with 0 findings' in log
        elif label=='format':assert log.strip()=='All files are correctly formatted'
    assert {'C50Bytecode.FullC50','C50Bytecode.RunMatchesKernel'}<=observed
    for relative,value in native['sources'].items():assert digest(ROOT/relative)==digest(native_dir/'snapshot'/relative)==value
    for relative,value in native['evidenceSha256'].items():assert digest(native_dir/relative)==value
    concrete=json.loads((concrete_dir/'concrete.json').read_text())
    assert concrete['status']=='passed' and concrete['runtimeSha256']==fixed['runtimeSha256']
    assert concrete['groundRuntimeAndDomainPredicates']=='satisfied'
    assert len(concrete['cases'])==41 and all(row['agree'] and row['dafny']==row['independent'] for row in concrete['cases'])
    assert len(concrete['mutants'])==2 and all(m['killed'] and m['dafny']==m['independent'] for m in concrete['mutants'])
    assert concrete['scriptSha256']==digest(ROOT/'formal/tools/validate_c50.py')
    faults=json.loads((faults_dir/'manifest.json').read_text())
    assert faults['status']=='passed' and faults['scriptSha256']==digest(ROOT/'formal/tools/fault_c50_native.py')
    assert faults['originalSources']==native['sources'] and len(faults['results'])==2
    for fault in faults['results']:
        assert fault['killedByNativeProof'] and fault['exitCode']!=0
        path=faults_dir/fault['name']
        log=(path/'native.log').read_text();summary=re.search(r'finished with (\d+) verified, (\d+) errors?',log)
        assert summary and int(summary[2])>0 and 'timed out' not in log
        assert digest(path/'native.log')==fault['logSha256'] and digest(path/'native.csv')==fault['csvSha256']
        for relative,value in fault['snapshotSha256'].items():assert digest(path/'snapshot'/relative)==value
    # Byte windows and full-code PUSH-aware jump boundaries are checked independently.
    windows=re.findall(r'code.contents\[(\d+)\.\.(\d+)\]\s*==\s*\[([\d,\s]+)\]',items['Runtime']['body'])
    assert windows
    for lo,hi,values in windows:
        assert list(code[int(lo):int(hi)])==[int(v) for v in values.split(',')]
    targets=[int(x) for x in re.findall(r'Code.IsInstructionStart\(code,\s*0,\s*(\d+)\)',items['Runtime']['body'])]
    boundaries=set();pc=0
    while pc<len(code):
        boundaries.add(pc);op=code[pc];pc+=1+(op-0x5f if 0x60<=op<=0x7f else 0)
    assert set(targets)==set(concrete['verifiedModelJumpBoundaries']) and all(t in boundaries and code[t]==0x5b for t in targets)
    return {'status':'independently-reviewed-exact-bytecode','claim':'C50','coverage':'full','bytecodeCredit':True,'recordedClaim':ledger['recordedClaim'],'statementSha256':fixed['statementSha256'],'runtimeSha256':fixed['runtimeSha256'],'runtimeLength':len(code),'package':fixed['package'],'nativeManifest':str((native_dir/'manifest.json').relative_to(ROOT)),'nativeManifestSha256':digest(native_dir/'manifest.json'),'nativeReview':str(native_review.relative_to(ROOT)),'nativeReviewSha256':digest(native_review),'nativeRows':batches,'binding':str(binding.relative_to(ROOT)),'bindingSha256':digest(binding),'captureManifest':str((capture_dir/'manifest.json').relative_to(ROOT)),'captureManifestSha256':digest(capture_dir/'manifest.json'),'concrete':str((concrete_dir/'concrete.json').relative_to(ROOT)),'concreteSha256':digest(concrete_dir/'concrete.json'),'nativeFaults':str((faults_dir/'manifest.json').relative_to(ROOT)),'nativeFaultsSha256':digest(faults_dir/'manifest.json'),'scope':fixed['scope'],'reviewerSha256':digest(Path(__file__))}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['capture','native','native-review','concrete','native-faults','output']:p.add_argument('--'+name,type=Path,required=True)
    args=p.parse_args();assert not args.output.exists(),'Review receipt must be fresh'
    result=validate(args.capture.resolve(),args.native.resolve(),args.native_review.resolve(),args.concrete.resolve(),args.native_faults.resolve())
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS exact current C50 bytecode:',result['nativeRows'],'native batches; runtime',result['runtimeSha256'])
if __name__=='__main__':main()
