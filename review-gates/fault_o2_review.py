"""Private adversarial checks of the frozen O2 acceptance reader."""
from pathlib import Path
import argparse,csv,hashlib,json,re,shutil,sys
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT/'formal/tools'))
import review_o2
from declarations import declarations
p=argparse.ArgumentParser(description=__doc__)
for name in ['capture','native','native-review','concrete','native-faults','output']:p.add_argument('--'+name,type=Path,required=True)
args=p.parse_args()
out=args.output.resolve();assert not out.exists();out.mkdir(parents=True)
cap=args.capture.resolve();native=args.native.resolve();nreview=args.native_review.resolve();concrete=args.concrete.resolve();faults=args.native_faults.resolve();binding=ROOT/'formal/bytecode/o2/runtime-binding.json'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
write=lambda p,v:p.write_text(json.dumps(v,indent=2)+'\n')
results=[]
def reject(name,**kw):
 try:review_o2.validate(kw.get('capture',cap),kw.get('native',native),kw.get('native_review',nreview),concrete,faults,kw.get('binding',binding))
 except AssertionError as error:results.append({'name':name,'rejected':True,'reason':str(error)});return
 raise AssertionError('Reader accepted faulty evidence: '+name)
trial=out/'stale-runtime';shutil.copytree(cap,trial);m=json.loads((trial/'manifest.json').read_text());m['runtimeSha256']='0'*64;write(trial/'manifest.json',m);reject('stale-runtime',capture=trial)
trial=out/'changed-claim.json';b=json.loads(binding.read_text());b['recordedClaim']='A different claim';b['statementSha256']=hashlib.sha256(b['recordedClaim'].encode()).hexdigest();write(trial,b);reject('changed-claim',binding=trial)
# Rebind hashes in a private root, preserving all original production dependencies.
for name in ['narrowed-domain','helper-pc-only','swapped-arithmetic','omitted-zero-divisor']:
 fake=out/name;fake.mkdir()
 for folder in ['contracts','node_modules','artifacts','proof-tools']:(fake/folder).symlink_to(ROOT/folder,target_is_directory=True)
 (fake/'docs').mkdir();shutil.copy2(ROOT/'docs/claim-evidence.json',fake/'docs/claim-evidence.json')
 (fake/'formal/tools').mkdir(parents=True);(fake/'formal/tools/capture_o2.py').symlink_to(ROOT/'formal/tools/capture_o2.py')
 (fake/'formal/bytecode/o2').mkdir(parents=True);shutil.copy2(binding,fake/'formal/bytecode/o2/runtime-binding.json');shutil.copy2(ROOT/'formal/bytecode/o2/Primitives.dfy',fake/'formal/bytecode/o2/Primitives.dfy')
 text=(ROOT/'formal/bytecode/o2/Entry.dfy').read_text()
 if name=='narrowed-domain':text=re.sub(r'ctx.callValue\s*==\s*0\s*&&\s*68','A(ctx)==0 && ctx.callValue==0 && 68',text,count=1)
 elif name=='helper-pc-only':
  i=text.index('ghost method FullDiv(');text=text[:i]+re.sub(r'requires st.PC\(\)\s*==\s*0','requires st.PC()==7691',text[i:],count=1)
 elif name=='omitted-zero-divisor':
  i=text.index('ghost method FullDiv(');text=text[:i]+re.sub(r'requires st.Gas\(\)\s*>=\s*483',lambda m:'requires B(st.evm.context)>0\n    '+m[0],text[i:],count=1)
 elif name=='swapped-arithmetic':
  prim=fake/'formal/bytecode/o2/Primitives.dfy';t=prim.read_text();changed=t.replace('if rem then a%b else a/b','if rem then a/b else a%b',1);assert changed!=t;prim.write_text(changed)
 entry=fake/'formal/bytecode/o2/Entry.dfy';entry.write_text(text);b=json.loads(binding.read_text());b['proofSourceSha256']=sha(entry);items=declarations(entry)
 for symbol,record in b['declarations'].items():
  record['interfaceSha256']=hashlib.sha256(items[symbol]['interface'].encode()).hexdigest();record['fullSha256']=hashlib.sha256(items[symbol]['full'].encode()).hexdigest()
 prim=fake/'formal/bytecode/o2/Primitives.dfy';b['primitivesSourceSha256']=sha(prim);pitems=declarations(prim)
 for symbol,record in b['primitiveDeclarations'].items():
  record['interfaceSha256']=hashlib.sha256(pitems[symbol]['interface'].encode()).hexdigest();record['fullSha256']=hashlib.sha256(pitems[symbol]['full'].encode()).hexdigest()
 write(fake/'formal/bytecode/o2/runtime-binding.json',b)
 c=json.loads((ROOT/'formal/claims.json').read_text())
 c['claims']['O2']['bytecodeProofs'][0]['theorems']=[{'declaration':b['proofSource']+'::'+n,'fullSha256':b['declarations'][n]['fullSha256']} for n in ['FullDiv','FullMod','WordResult','RunMatchesKernel']]
 write(fake/'formal/claims.json',c)
 old_root,old_library=review_o2.ROOT,review_o2.LIBRARY;review_o2.ROOT=fake;review_o2.LIBRARY=fake/'formal'
 try:reject(name,binding=fake/'formal/bytecode/o2/runtime-binding.json')
 finally:review_o2.ROOT,review_o2.LIBRARY=old_root,old_library
# Remove public-entry proof rows, rebind evidence hashes and the fake review flag.
trial=out/'missing-entry-rows';shutil.copytree(native,trial);m=json.loads((trial/'manifest.json').read_text());csvpath=trial/'proof-000.csv'
with csvpath.open() as stream:reader=csv.DictReader(stream);fields=reader.fieldnames;rows=list(reader)
rows=[r for r in rows if not r['TestResult.DisplayName'].startswith('O2Bytecode.FullMod ')]
with csvpath.open('w') as stream:writer=csv.DictWriter(stream,fieldnames=fields);writer.writeheader();writer.writerows(rows)
log=trial/'proof-000.log';text=re.sub(r'finished with \d+ verified, 0 errors','finished with '+str(len(rows))+' verified, 0 errors',log.read_text());log.write_text(text)
m['evidenceSha256']['proof-000.csv']=sha(csvpath);m['evidenceSha256']['proof-000.log']=sha(log);write(trial/'manifest.json',m)
r=json.loads(nreview.read_text());r['manifestSha256']=sha(trial/'manifest.json');fake_review=out/'fake-native-review.json';write(fake_review,r)
reject('missing-entry-rows',native=trial,native_review=fake_review)
# Rebound native command and gate omissions must fail independently of pass flags.
for name in ['filtered-proof-command','missing-audit-gate','missing-import-closure']:
 trial=out/name;shutil.copytree(native,trial);m=json.loads((trial/'manifest.json').read_text())
 if name=='filtered-proof-command':m['commands'][0]['command']+=['--filter-symbol','O2Bytecode.FullDiv']
 elif name=='missing-audit-gate':m['commands']=[c for c in m['commands'] if c['gate']!='audit-000'];m['results']=[r for r in m['results'] if r['gate']!='audit-000']
 else:m['sources'].pop('formal/bytecode/c50/Steps.dfy')
 write(trial/'manifest.json',m);r=json.loads(nreview.read_text());r['manifestSha256']=sha(trial/'manifest.json');fake_review=out/(name+'-review.json');write(fake_review,r)
 reject(name,native=trial,native_review=fake_review)
write(out/'manifest.json',{'status':'passed','scriptSha256':sha(Path(__file__)),'results':results});print('Passed',len(results),'acceptance-reader fault controls')
