"""Negative native controls for O12, in isolated complete-closure snapshots."""
import argparse,csv,json,re,shutil,subprocess
from pathlib import Path
from check import ROOT,LIBRARY,digest
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
out=a.output.resolve();assert not out.exists();out.mkdir(parents=True)
package=json.loads((LIBRARY/'packages/o12-current-bytecode/canonical.json').read_text());results=[]
for name,pc,new in [('addmod-to-mulmod',7709,9),('mulmod-to-addmod',7295,8),('wrong-panic-code',19748,19)]:
 trial=out/name;trial.mkdir();snapshot=trial/'snapshot'
 for relative,expected in package['closureSha256'].items():
  assert digest(ROOT/relative)==expected
  target=snapshot/relative;target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(ROOT/relative,target)
 entry=snapshot/'formal/bytecode/o12/Entry.dfy';text=entry.read_text()
 match=re.search(r'ensures code.contents\['+str(pc)+r'\]\s*==\s*(\d+)',text);assert match;old=int(match[1]);assert old!=new
 methods=list(re.finditer(r'ghost method (Block\d+)\(',text));symbol=None
 for i,m in enumerate(methods):
  body=text[m.start():methods[i+1].start() if i+1<len(methods) else text.index('ghost method AddZero(')]
  if re.search(r'assert s.evm.code.contents\['+str(pc)+r'\]\s*==',body):symbol=m[1];break
 assert symbol
 # Rebind all runtime windows and facts to the mutant, preserving expected transitions.
 def window(m):
  lo,hi=int(m[1]),int(m[2]);values=[int(x) for x in m[3].split(',')]
  if lo<=pc<hi:values[pc-lo]=new;return 'code.contents['+str(lo)+'..'+str(hi)+']=='+str(values)
  return m[0]
 text=re.sub(r'code.contents\[(\d+)\.\.(\d+)\]\s*==\s*\[([\d,\s]+)\]',window,text)
 text=re.sub(r'(ensures code.contents\['+str(pc)+r'\]\s*==\s*)'+str(old)+r'\b',lambda m:m[1]+str(new),text)
 def fact(m):
  lo,hi,index,value=map(int,m.groups())
  return re.sub(r'==\s*'+str(value)+r';','== '+str(new)+';',m[0]) if lo+index==pc else m[0]
 text=re.sub(r'assert code.contents\[(\d+)\.\.(\d+)\]\[(\d+)\]\s*==\s*(\d+);',fact,text)
 entry.write_text(text)
 command=[str(ROOT/'proof-tools/assertions/dafny/dafny'),'verify',str(entry),'--filter-symbol','O12Bytecode.'+symbol,'--manual-lemma-induction','--isolate-assertions','--cores','2','--verification-time-limit','30','--solver-path',str(ROOT/'proof-tools/assertions/dafny/z3/bin/z3-4.12.1'),'--log-format','csv;LogFileName='+str(trial/'native.csv')]
 with (trial/'native.log').open('w') as stream:proc=subprocess.run(command,stdout=stream,stderr=subprocess.STDOUT,cwd=ROOT)
 log=(trial/'native.log').read_text();rows=list(csv.DictReader((trial/'native.csv').open()));summary=re.search(r'finished with (\d+) verified, (\d+) errors?',log)
 killed=proc.returncode!=0 and bool(summary) and int(summary[2])>0 and 'timed out' not in log and any(row['TestResult.Outcome']=='Failed' for row in rows)
 results.append({'name':name,'pc':pc,'symbol':symbol,'command':command,'exitCode':proc.returncode,'killedByNativeProof':killed,'snapshotSha256':{relative:digest(snapshot/relative) for relative in package['closureSha256']},'logSha256':digest(trial/'native.log'),'csvSha256':digest(trial/'native.csv')})
 (out/'manifest.json').write_text(json.dumps({'status':'running','results':results},indent=2)+'\n');assert killed,name
(out/'manifest.json').write_text(json.dumps({'status':'passed','scriptSha256':digest(Path(__file__)),'originalSources':package['closureSha256'],'results':results},indent=2)+'\n')
print('Passed',len(results),'native bytecode fault controls, with actual verification errors and no timeouts')
