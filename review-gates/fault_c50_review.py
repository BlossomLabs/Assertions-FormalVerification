"""Private adversarial checks of the frozen C50 acceptance reader."""
from pathlib import Path
import argparse,csv,hashlib,json,re,shutil,sys
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT/'formal/tools'))
import review_c50
from declarations import declarations
p=argparse.ArgumentParser(description=__doc__)
for name in ['capture','native','native-review','concrete','native-faults','output']:p.add_argument('--'+name,type=Path,required=True)
args=p.parse_args()
out=args.output.resolve();assert not out.exists();out.mkdir(parents=True)
cap=args.capture.resolve();native=args.native.resolve();nreview=args.native_review.resolve();concrete=args.concrete.resolve();faults=args.native_faults.resolve();binding=ROOT/'formal/bytecode/c50/runtime-binding.json'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
write=lambda p,v:p.write_text(json.dumps(v,indent=2)+'\n')
results=[]
def reject(name,**kw):
 try:review_c50.validate(kw.get('capture',cap),kw.get('native',native),kw.get('native_review',nreview),concrete,faults,kw.get('binding',binding))
 except AssertionError as error:results.append({'name':name,'rejected':True,'reason':str(error)});return
 raise AssertionError('Reader accepted faulty evidence: '+name)
trial=out/'stale-runtime';shutil.copytree(cap,trial);m=json.loads((trial/'manifest.json').read_text());m['runtimeSha256']='0'*64;write(trial/'manifest.json',m);reject('stale-runtime',capture=trial)
trial=out/'changed-claim.json';b=json.loads(binding.read_text());b['recordedClaim']='A different claim';b['statementSha256']=hashlib.sha256(b['recordedClaim'].encode()).hexdigest();write(trial,b);reject('changed-claim',binding=trial)
# Rebind hashes in a private root, preserving all original production dependencies.
for name in ['narrowed-domain','helper-pc-only']:
 fake=out/name;fake.mkdir()
 for folder in ['contracts','node_modules','artifacts','proof-tools']:(fake/folder).symlink_to(ROOT/folder,target_is_directory=True)
 (fake/'docs').mkdir();shutil.copy2(ROOT/'docs/claim-evidence.json',fake/'docs/claim-evidence.json')
 (fake/'formal/tools').mkdir(parents=True);(fake/'formal/tools/capture_c50.py').symlink_to(ROOT/'formal/tools/capture_c50.py')
 (fake/'formal/bytecode/c50').mkdir(parents=True);shutil.copy2(binding,fake/'formal/bytecode/c50/runtime-binding.json')
 text=(ROOT/'formal/bytecode/c50/Entry.dfy').read_text()
 if name=='narrowed-domain':text=text.replace('ctx.callValue == 0 && 68','A(ctx)==64 && ctx.callValue == 0 && 68',1)
 else:text=text.replace('requires st.PC()==0 && st.evm.stack.contents==[]','requires st.PC()==2601 && st.evm.stack.contents==[]',1)
 entry=fake/'formal/bytecode/c50/Entry.dfy';entry.write_text(text);b=json.loads(binding.read_text());b['proofSourceSha256']=sha(entry);items=declarations(entry)
 for symbol,record in b['declarations'].items():
  record['interfaceSha256']=hashlib.sha256(items[symbol]['interface'].encode()).hexdigest();record['fullSha256']=hashlib.sha256(items[symbol]['full'].encode()).hexdigest()
 write(fake/'formal/bytecode/c50/runtime-binding.json',b)
 c=json.loads((ROOT/'formal/claims.json').read_text())
 c['claims']['C50']['bytecodeProofs'][0]['theorems']=[{'declaration':b['proofSource']+'::'+n,'fullSha256':b['declarations'][n]['fullSha256']} for n in ['FullC50','RunMatchesKernel']]
 write(fake/'formal/claims.json',c)
 old_root,old_library=review_c50.ROOT,review_c50.LIBRARY;review_c50.ROOT=fake;review_c50.LIBRARY=fake/'formal'
 try:reject(name,binding=fake/'formal/bytecode/c50/runtime-binding.json')
 finally:review_c50.ROOT,review_c50.LIBRARY=old_root,old_library
# Remove public-entry proof rows, rebind evidence hashes and the fake review flag.
trial=out/'missing-entry-rows';shutil.copytree(native,trial);m=json.loads((trial/'manifest.json').read_text());csvpath=trial/'proof-000.csv'
with csvpath.open() as stream:reader=csv.DictReader(stream);fields=reader.fieldnames;rows=list(reader)
rows=[r for r in rows if not r['TestResult.DisplayName'].startswith('C50Bytecode.FullC50 ')]
with csvpath.open('w') as stream:writer=csv.DictWriter(stream,fieldnames=fields);writer.writeheader();writer.writerows(rows)
log=trial/'proof-000.log';text=re.sub(r'finished with \d+ verified, 0 errors','finished with '+str(len(rows))+' verified, 0 errors',log.read_text());log.write_text(text)
m['evidenceSha256']['proof-000.csv']=sha(csvpath);m['evidenceSha256']['proof-000.log']=sha(log);write(trial/'manifest.json',m)
r=json.loads(nreview.read_text());r['manifestSha256']=sha(trial/'manifest.json');fake_review=out/'fake-native-review.json';write(fake_review,r)
reject('missing-entry-rows',native=trial,native_review=fake_review)
write(out/'manifest.json',{'status':'passed','scriptSha256':sha(Path(__file__)),'results':results});print('Passed',len(results),'acceptance-reader fault controls')
