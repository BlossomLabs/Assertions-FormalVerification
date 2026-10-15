"""Fresh exact Hardhat runtime capture; this gate grants no execution proof."""
import argparse,hashlib,json,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);args=p.parse_args()
out=args.output.resolve();assert not out.exists();out.mkdir(parents=True)
artifact_path=ROOT/'artifacts/contracts/Operations.sol/Operations.json'
artifact=json.loads(artifact_path.read_text());bid=artifact['buildInfoId']
info_path=ROOT/'artifacts/build-info'/(bid+'.json');info=json.loads(info_path.read_text())
assert info['solcVersion']=='0.8.36'
request=info['input'];compiler=ROOT/'proof-tools/assertions/solc-0.8.36'
assert sha(compiler)=='c8d35afdddc3cd2743ee88b8f25e0fecd16e2bdd5f2120f37e52cd9cc45ae0e6'
assert request['settings']['optimizer']=={'enabled':True,'runs':200}
assert request['settings']['evmVersion']=='cancun'
source_hashes={}
for name,source in request['sources'].items():
    assert 'content' in source
    source_hashes[name]=hashlib.sha256(source['content'].encode()).hexdigest()
    if name.startswith('npm/@openzeppelin/contracts@5.6.1/'):
        local=ROOT/'node_modules/@openzeppelin/contracts'/name[len('npm/@openzeppelin/contracts@5.6.1/'):]
        assert sha(local)==source_hashes[name],name
    if name.startswith('project/'):
        local=ROOT/name[len('project/'):]
        assert sha(local)==source_hashes[name],name
        assert sha(ROOT.parent/'.review-latest'/name[len('project/'):])==source_hashes[name],name
(out/'solc-input.json').write_text(json.dumps(request,indent=2)+'\n')
with (out/'solc-input.json').open() as inp,(out/'solc-output.json').open('w') as stdout:
    result=subprocess.run([str(compiler),'--standard-json'],stdin=inp,stdout=stdout,stderr=subprocess.PIPE,text=True,cwd=ROOT)
assert result.returncode==0,result.stderr
compiled=json.loads((out/'solc-output.json').read_text())
assert not any(e['severity']=='error' for e in compiled.get('errors',[]))
contract=compiled['contracts']['project/contracts/Operations.sol']['Operations']
runtime=bytes.fromhex(contract['evm']['deployedBytecode']['object'])
assert runtime.hex()==artifact['deployedBytecode'][2:]
assert contract['evm']['bytecode']['object']==artifact['bytecode'][2:]
assert not contract['evm']['deployedBytecode']['immutableReferences']
shared=json.loads((ROOT.parent/'.review-latest/artifacts/contracts/Operations.sol/Operations.json').read_text())
assert shared['deployedBytecode']==artifact['deployedBytecode'] and shared['bytecode']==artifact['bytecode']
(out/'runtime.hex').write_text(runtime.hex()+'\n')
manifest={'status':'exact-current-runtime-captured','runtimeSha256':hashlib.sha256(runtime).hexdigest(),'runtimeLength':len(runtime),'selectors':{name:contract['evm']['methodIdentifiers'][name] for name in ['addMod(uint256,uint256,uint256)','mulMod(uint256,uint256,uint256)']},'compilerSha256':sha(compiler),'sources':source_hashes,'settings':request['settings'],'hardhatBuildInfoSha256':sha(info_path),'artifactSha256':sha(artifact_path),'inputSha256':sha(out/'solc-input.json'),'outputSha256':sha(out/'solc-output.json'),'captureScriptSha256':sha(Path(__file__)),'bytecodeCredit':False}
(out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('Exact current Operations runtime captured:',len(runtime),'bytes; selector',manifest['selectors'])
