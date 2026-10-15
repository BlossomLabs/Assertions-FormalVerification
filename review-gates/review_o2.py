"""Independent exact-runtime O2 acceptance, distinct from source acceptance."""
import argparse,csv,hashlib,json,re,subprocess,sys,tempfile
from pathlib import Path
from check import ROOT,LIBRARY,digest
from declarations import declarations

STATEMENT='Unsigned `div`/`mod` truncate; zero divisor reverts with Panic(0x12)'
SCOPE='Whole public div/mod entries from PC 0 of the exact current Operations runtime. Arbitrary uint256 dividend and divisor; zero divisor reverts with exact Panic(0x12) data, nonzero divisor returns unsigned integer quotient/remainder. Cancun; call value zero; two-word ABI decoder domain (68 through 2^255+3 bytes) with arbitrary trailing calldata; initial empty stack/memory; at least 483 execution gas for div and 526 for mod. No compiler-correctness or source-to-model premise; no external backend call.'

compact=lambda s:re.sub(r'\s+','',s)

def validate(capture_dir,native_dir,native_review,concrete_dir,faults_dir,binding=None):
    binding=binding or LIBRARY/'bytecode/o2/runtime-binding.json'
    fixed=json.loads(binding.read_text());cap=json.loads((capture_dir/'manifest.json').read_text())
    ledger=json.loads((ROOT/'docs/claim-evidence.json').read_text())['claims']['O2']
    assert fixed['claim']=='O2' and fixed['recordedClaim']==ledger['recordedClaim']==STATEMENT
    assert fixed['scope']==SCOPE, 'Changed O2 execution premises'
    assert hashlib.sha256(ledger['recordedClaim'].encode()).hexdigest()==fixed['statementSha256']
    for key in ['runtimeSha256','runtimeLength','selectors','compilerSha256','sources','settings']:
        assert cap[key]==fixed[key], 'Current compiler/runtime binding drift: '+key
    assert cap['status']=='exact-current-runtime-captured'
    assert digest(ROOT/'formal/tools/capture_o2.py')==cap['captureScriptSha256']
    for name in ['input','output']:
        assert digest(capture_dir/('solc-'+name+'.json'))==cap[name+'Sha256']
    code=bytes.fromhex((capture_dir/'runtime.hex').read_text())
    assert len(code)==fixed['runtimeLength'] and hashlib.sha256(code).hexdigest()==fixed['runtimeSha256']
    artifact=json.loads((ROOT/'artifacts/contracts/Operations.sol/Operations.json').read_text())
    assert code.hex()==artifact['deployedBytecode'][2:] and digest(ROOT/'artifacts/contracts/Operations.sol/Operations.json')==cap['artifactSha256']
    request=json.loads((capture_dir/'solc-input.json').read_text())
    assert request['settings']==fixed['settings']
    assert digest(ROOT/'proof-tools/assertions/solc-0.8.36')==fixed['compilerSha256']
    # Recompile independently from the reviewed compiler request, not its receipt flag.
    replay=subprocess.run([str(ROOT/'proof-tools/assertions/solc-0.8.36'),'--standard-json'],input=json.dumps(request),capture_output=True,text=True,cwd=ROOT)
    assert replay.returncode==0,replay.stderr
    compiled=json.loads(replay.stdout);assert not any(e['severity']=='error' for e in compiled.get('errors',[]))
    contract=compiled['contracts']['project/contracts/Operations.sol']['Operations']
    assert contract['evm']['deployedBytecode']['object']==code.hex()
    assert contract['evm']['bytecode']['object']==artifact['bytecode'][2:]
    assert not contract['evm']['deployedBytecode']['immutableReferences']
    assert {name:contract['evm']['methodIdentifiers'][name] for name in ['div(uint256,uint256)','mod(uint256,uint256)']}==fixed['selectors']
    for name,source in request['sources'].items():
        assert hashlib.sha256(source['content'].encode()).hexdigest()==fixed['sources'][name]
        if name.startswith('project/'):
            local=ROOT/name[len('project/'):]
        else:
            assert name.startswith('npm/@openzeppelin/contracts@5.6.1/')
            local=ROOT/'node_modules/@openzeppelin/contracts'/name[len('npm/@openzeppelin/contracts@5.6.1/'):]
        assert digest(local)==fixed['sources'][name], 'Current source changed: '+name
    mapping=json.loads((LIBRARY/'claims.json').read_text())['claims']['O2']['bytecodeProofs']
    assert len(mapping)==1 and mapping[0]['coverage']=='full' and mapping[0]['package']==fixed['package']
    assert mapping[0]['assumptions']==fixed['scope']
    assert mapping[0]['theorems']==[{'declaration':fixed['proofSource']+'::'+n,'fullSha256':fixed['declarations'][n]['fullSha256']} for n in ['FullDiv','FullMod','WordResult','RunMatchesKernel']]
    entry=ROOT/fixed['proofSource'];items=declarations(entry)
    assert digest(entry)==fixed['proofSourceSha256']
    for name,record in fixed['declarations'].items():
        assert hashlib.sha256(items[name]['interface'].encode()).hexdigest()==record['interfaceSha256']
        assert hashlib.sha256(items[name]['full'].encode()).hexdigest()==record['fullSha256']
    # Freeze the public domain, mathematical result and actual kernel connection.
    expected_domain='{ ctx.callValue==0 && 68<=|ctx.callData|<=MAX_I256+4 && H(ctx) as int/TWO_224==(Selector(rem) as int) }'
    assert compact(items['ValidCall']['body'])==compact(expected_domain),'Narrowed or changed input domain'
    assert compact(items['Ready']['body'])==compact('{ st.evm.fork==EvmFork.CANCUN && Runtime(st.evm.code) && ValidCall(st.evm.context,rem) }')
    assert compact(items['Step']['body'])==compact('{ EVM.Execute(st) }'),'Execution is not the actual pinned kernel'
    assert compact(items['Selector']['body'])==compact('{ if rem then 0xf43f523a else 0xa391c15b }')
    for name,offset in [('A',4),('B',36),('H',0)]:
        assert compact(items[name]['body'])==compact('{ ctx.CallDataRead('+str(offset)+') }')
    assert compact(items['L']['body'])==compact('{ ctx.CallDataSize() }')
    assert compact(items['R']['body'])==compact('{ S.Value(rem,A(ctx),B(ctx)) }')
    primitives=ROOT/fixed['primitivesSource'];pitems=declarations(primitives)
    assert digest(primitives)==fixed['primitivesSourceSha256']
    for name,record in fixed['primitiveDeclarations'].items():
        assert hashlib.sha256(pitems[name]['interface'].encode()).hexdigest()==record['interfaceSha256']
        assert hashlib.sha256(pitems[name]['full'].encode()).hexdigest()==record['fullSha256']
    assert compact(pitems['Value']['body'])==compact('{ if b==0 then 0 else (if rem then a%b else a/b) }'),'Changed unsigned arithmetic'
    assert compact(pitems['PanicData']['body'])==compact('{ [78,72,123,113]+U256.ToBytes(18) }'),'Wrong Panic(0x12) bytes'
    for rem in [False,True]:
        mode=str(rem).lower();name='Mod' if rem else 'Div'
        zero_steps,success_steps,zero_gas,success_gas=(127,142,471,526) if rem else (118,133,428,483)
        expected_entry=f'''ghost method Full{name}(st:ExecutingState) returns(out:State)
          requires Ready(st,{mode})
          requires st.PC()==0 && st.evm.stack.contents==[] && st.evm.memory.contents==[]
          requires st.Gas()>={success_gas}
          ensures out==EVM.ExecuteN(st,if B(st.evm.context)==0 then {zero_steps} else {success_steps})
          ensures out==(if B(st.evm.context)==0 then ERROR(REVERTS,gas:=st.Gas()-{zero_gas},data:=S.PanicData()) else RETURNS(st.Gas()-{success_gas},U256.ToBytes(S.Value({mode},A(st.evm.context),B(st.evm.context))),st.evm.world,st.evm.transient,st.evm.substate))'''
        assert compact(items['Full'+name]['interface'])==compact(expected_entry),'Changed theorem scope or result'
    assert compact(items['WordResult']['interface'])==compact('lemma WordResult(ctx:Context.T,rem:bool) requires B(ctx)>0 ensures R(ctx,rem)==(if rem then (A(ctx) as int)%(B(ctx) as int) else (A(ctx) as int)/(B(ctx) as int)) as u256'), 'Changed mathematical result'
    assert compact(pitems['ValueEquation']['interface'])==compact('lemma ValueEquation(rem:bool,a:u256,b:u256) requires b>0 ensures Value(rem,a,b)==(if rem then (a as int)%(b as int) else (a as int)/(b as int)) as u256'), 'Changed arithmetic equation'
    native=json.loads((native_dir/'manifest.json').read_text());review=json.loads(native_review.read_text())
    assert native['package']==fixed['package'] and native['status']=='native-gates-passed'
    assert review['status']=='independently-reviewed-native-closure' and review['manifestSha256']==digest(native_dir/'manifest.json')
    assert native['sources']==json.loads((LIBRARY/'packages/o2-current-bytecode/canonical.json').read_text())['closureSha256']
    descriptor=json.loads((LIBRARY/'packages/o2-current-bytecode/canonical.json').read_text())
    assert descriptor['resourcePolicy']=={'cores':16,'secondsPerObligation':120,'manualLemmaInduction':True,'isolateAssertions':True}
    assert descriptor['verificationEntries']==[fixed['proofSource']]
    assert len(native['commands'])==3 and len(native['results'])==3
    first=native['commands'][0]['command'];suffix='/snapshot/'+fixed['proofSource']
    assert first[2].endswith(suffix)
    directory=first[2][:-len(suffix)];dafny=str(ROOT/'proof-tools/assertions/dafny/dafny')
    expected=[{'gate':'proof-000','command':[dafny,'verify',directory+suffix,
        '--verify-included-files','--manual-lemma-induction','--isolate-assertions','--cores','16',
        '--verification-time-limit','120','--solver-path',str(ROOT/'proof-tools/assertions/dafny/z3/bin/z3-4.12.1'),
        '--log-format','csv;LogFileName='+directory+'/proof-000.csv','--progress','Symbol']},
        {'gate':'audit-000','command':[dafny,'audit',directory+suffix]},
        {'gate':'format','command':[dafny,'format','--check']+[directory+'/snapshot/'+p for p in descriptor['closureSha256']]}]
    assert native['commands']==expected, 'Changed native command scope or policy'
    assert [r['gate'] for r in native['results']]==[g['gate'] for g in expected]
    assert all(r['exitCode']==0 and r['passed'] for r in native['results'])
    observed=set();batches=0
    for gate in native['commands']:
        label,command=gate['gate'],gate['command'];log=(native_dir/(label+'.log')).read_text()
        if label.startswith('proof-'):
            assert '--verify-included-files' in command and '--filter-symbol' not in command
            assert '--manual-lemma-induction' in command and '--isolate-assertions' in command
            assert command[command.index('--verification-time-limit')+1]=='120'
            with (native_dir/(label+'.csv')).open() as stream:rows=list(csv.DictReader(stream))
            summary=re.search(r'finished with (\d+) verified, (\d+) errors?',log)
            assert rows and summary and int(summary[1])==len(rows) and int(summary[2])==0
            assert not re.search(r'Error:|timed out|inconclusive',log,re.I)
            assert all(r['TestResult.Outcome']=='Passed' for r in rows)
            observed.update(r['TestResult.DisplayName'].split(' (')[0] for r in rows);batches+=len(rows)
        elif label.startswith('audit-'):assert 'auditor completed with 0 findings' in log
        elif label=='format':assert log.strip()=='All files are correctly formatted'
    assert {'O2Bytecode.FullDiv','O2Bytecode.FullMod','O2Bytecode.RunMatchesKernel','O2Bytecode.DivZero','O2Bytecode.DivNonzero','O2Bytecode.ModZero','O2Bytecode.ModNonzero','O2Primitives.Pure','O2Primitives.ValueEquation'}<=observed
    from evm_dependency import external_sources, file_inventory
    external=external_sources();inventory={}
    for relative in native['sources']:
        inventory.update(file_inventory(ROOT/relative,external))
    assert {name for name,kind in inventory.items() if kind in ['lemma','method']}<=observed, 'Unverified proof or executable declaration'
    assert review['nativeRows']==batches and review['declarations']==len(inventory)
    for name,path in {'dafny':ROOT/'proof-tools/assertions/dafny/dafny','Dafny.dll':ROOT/'proof-tools/assertions/dafny/Dafny.dll','z3':ROOT/'proof-tools/assertions/dafny/z3/bin/z3-4.12.1'}.items():
        assert native['tools'][name]==digest(path), 'Native tool drift'
    assert native['sourceHashesUnchanged'] and native['snapshotHashesMatch'] and native['toolHashesUnchanged'] and native['producerInputsUnchanged']
    for relative,value in native['producerInputs'].items():assert digest(native_dir/'producer'/relative)==value
    for relative,value in native['sources'].items():assert digest(ROOT/relative)==digest(native_dir/'snapshot'/relative)==value
    for relative,value in native['evidenceSha256'].items():assert digest(native_dir/relative)==value
    concrete=json.loads((concrete_dir/'concrete.json').read_text())
    assert concrete['status']=='passed' and concrete['runtimeSha256']==fixed['runtimeSha256']
    assert concrete['groundRuntimeAndDomainPredicates']=='satisfied'
    assert len(concrete['cases'])==106 and all(row['agree'] and row['dafny']==row['independent'] for row in concrete['cases'])
    assert len(concrete['mutants'])==3 and all(m['killed'] and m['dafny']==m['independent'] for m in concrete['mutants'])
    assert concrete['scriptSha256']==digest(ROOT/'formal/tools/validate_o2.py')
    # Rebuild from the native-verified snapshot and replay ground predicates and
    # concrete cases independently. A producer's 'passed' flag is insufficient.
    from bootstrap_evm import validate_python
    lock=json.loads((LIBRARY/'dependencies/dafnyevm/lock.json').read_text())
    python_files=validate_python(ROOT/'proof-tools/evm-python',lock['requirementsSha256'])
    with tempfile.TemporaryDirectory(prefix='o2-review-',dir=ROOT/'formal/evidence') as temporary:
        replay_dir=Path(temporary)
        commands=[
            [str(ROOT/'proof-tools/assertions/dafny/dafny'),'build','--target','py','--no-verify',str(native_dir/'snapshot'/fixed['proofSource']),'--output',str(replay_dir/'entry')],
            [sys.executable,'-B',str(LIBRARY/'tools/validate_o2.py'),'--capture',str(capture_dir),'--interpreter',str(replay_dir/'entry-py'),'--python-deps',str(ROOT/'proof-tools/evm-python'),'--output',str(replay_dir/'concrete')]]
        for command in commands:
            result=subprocess.run(command,cwd=ROOT,capture_output=True,text=True)
            assert result.returncode==0,result.stdout+result.stderr
        assert json.loads((replay_dir/'concrete/concrete.json').read_text())==concrete,'Independent concrete replay differs'
    assert validate_python(ROOT/'proof-tools/evm-python',lock['requirementsSha256'])==python_files
    faults=json.loads((faults_dir/'manifest.json').read_text())
    assert faults['status']=='passed' and faults['scriptSha256']==digest(ROOT/'formal/tools/fault_o2_native.py')
    assert faults['originalSources']==native['sources'] and len(faults['results'])==3
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
    return {'status':'independently-reviewed-exact-bytecode','claim':'O2','coverage':'full','bytecodeCredit':True,'recordedClaim':ledger['recordedClaim'],'statementSha256':fixed['statementSha256'],'runtimeSha256':fixed['runtimeSha256'],'runtimeLength':len(code),'package':fixed['package'],'nativeManifest':str((native_dir/'manifest.json').relative_to(ROOT)),'nativeManifestSha256':digest(native_dir/'manifest.json'),'nativeReview':str(native_review.relative_to(ROOT)),'nativeReviewSha256':digest(native_review),'nativeRows':batches,'concreteReplay':'matched','pythonDependenciesSha256':hashlib.sha256(json.dumps(python_files,sort_keys=True).encode()).hexdigest(),'binding':str(binding.relative_to(ROOT)),'bindingSha256':digest(binding),'captureManifest':str((capture_dir/'manifest.json').relative_to(ROOT)),'captureManifestSha256':digest(capture_dir/'manifest.json'),'concrete':str((concrete_dir/'concrete.json').relative_to(ROOT)),'concreteSha256':digest(concrete_dir/'concrete.json'),'nativeFaults':str((faults_dir/'manifest.json').relative_to(ROOT)),'nativeFaultsSha256':digest(faults_dir/'manifest.json'),'scope':fixed['scope'],'reviewerSha256':digest(Path(__file__))}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['capture','native','native-review','concrete','native-faults','output']:p.add_argument('--'+name,type=Path,required=True)
    args=p.parse_args();assert not args.output.exists(),'Review receipt must be fresh'
    result=validate(args.capture.resolve(),args.native.resolve(),args.native_review.resolve(),args.concrete.resolve(),args.native_faults.resolve())
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS exact current O2 bytecode:',result['nativeRows'],'native batches; runtime',result['runtimeSha256'])
if __name__=='__main__':main()
