"""Negative native controls for the C50 execution certificate in private snapshots."""
import argparse,csv,hashlib,json,re,shutil,subprocess
from pathlib import Path
from check import ROOT,LIBRARY,digest
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);args=p.parse_args()
out=args.output.resolve();assert not out.exists();out.mkdir(parents=True)
package=json.loads((LIBRARY/'packages/c50-current-bytecode/canonical.json').read_text());results=[]
for name,symbol in [('wrong-revert-selector','Block050'),('empty-guard-opcode','Block046')]:
 trial=out/name;trial.mkdir();snapshot=trial/'snapshot'
 for relative,expected in package['closureSha256'].items():
  assert digest(ROOT/relative)==expected
  target=snapshot/relative;target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(ROOT/relative,target)
 entry=snapshot/'formal/bytecode/c50/Entry.dfy';text=entry.read_text()
 if name=='wrong-revert-selector':
  start=text.index('  ghost method Block050(');end=text.index('  ghost method FullC50(',start)
  changed=text[start:end].replace('[57,85,175,170]','[57,85,175,171]');assert changed!=text[start:end]
  text=text[:start]+changed+text[end:]
 else:
  # Change actual opcode and all runtime byte facts consistently. No stale-hash failure.
  assert '91,95,129,144,3,97,10,74' in text
  text=text.replace('91,95,129,144,3,97,10,74','91,95,129,144,20,97,10,74')
  text=text.replace('ensures code.contents[2605]==3','ensures code.contents[2605]==20')
  text=text.replace('assert code.contents[2601..2617][4]==3;','assert code.contents[2601..2617][4]==20;')
 entry.write_text(text)
 command=[str(ROOT/'proof-tools/assertions/dafny/dafny'),'verify',str(entry),'--filter-symbol','C50Bytecode.'+symbol,'--manual-lemma-induction','--isolate-assertions','--cores','2','--verification-time-limit','30','--solver-path',str(ROOT/'proof-tools/assertions/dafny/z3/bin/z3-4.12.1'),'--log-format','csv;LogFileName='+str(trial/'native.csv')]
 with (trial/'native.log').open('w') as stream:proc=subprocess.run(command,stdout=stream,stderr=subprocess.STDOUT,cwd=ROOT)
 log=(trial/'native.log').read_text();rows=list(csv.DictReader((trial/'native.csv').open()));summary=re.search(r'finished with (\d+) verified, (\d+) errors?',log)
 killed=proc.returncode!=0 and bool(summary) and int(summary[2])>0 and 'timed out' not in log and any(row['TestResult.Outcome']=='Failed' for row in rows)
 results.append({'name':name,'symbol':symbol,'command':command,'exitCode':proc.returncode,'killedByNativeProof':killed,'snapshotSha256':{relative:digest(snapshot/relative) for relative in package['closureSha256']},'logSha256':digest(trial/'native.log'),'csvSha256':digest(trial/'native.csv')})
 (out/'manifest.json').write_text(json.dumps({'status':'running','results':results},indent=2)+'\n')
 assert killed,name
print('Passed',len(results),'native fault controls; real verification errors, no timeout credit')
(out/'manifest.json').write_text(json.dumps({'status':'passed','scriptSha256':digest(Path(__file__)),'originalSources':package['closureSha256'],'results':results},indent=2)+'\n')
