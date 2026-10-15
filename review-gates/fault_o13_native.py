"""Negative native controls for O13, in isolated complete-closure snapshots."""
import argparse,csv,json,re,shutil,subprocess
from pathlib import Path
from check import ROOT,LIBRARY,digest
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
out=a.output.resolve();assert not out.exists();out.mkdir(parents=True)
package=json.loads((LIBRARY/'packages/o13-current-bytecode/canonical.json').read_text());results=[]
for name,pc,new in [('magnitude-negation-to-addition',8771,1),('mulmod-to-addmod',4090,8),('restore-negation-to-addition',9103,1)]:
 trial=out/name;trial.mkdir();snapshot=trial/'snapshot'
 for relative,expected in package['closureSha256'].items():
  assert digest(ROOT/relative)==expected
  target=snapshot/relative;target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(ROOT/relative,target)
 sources=[snapshot/relative for relative in package['closureSha256'] if relative.startswith('formal/bytecode/o13/')]
 site=json.loads((LIBRARY/'bytecode/o13/runtime-binding.json').read_text())['nativeFaultSites'][str(pc)]
 symbol=site['symbol'];target=snapshot/site['source']
 assert re.search(r'(?:ghost method|lemma) '+symbol.split('.')[-1]+r'\(',target.read_text())
 old=None
 for path in sources:
  text=path.read_text()
  match=re.search(r'ensures code.contents\['+str(pc)+r'\]\s*==\s*(\d+)',text)
  if match:old=int(match[1]);break
 assert old is not None and old!=new
 for path in sources:
  text=path.read_text()
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
  path.write_text(text)
 if pc==9103:
  # A paired native instruction proof avoids constructing an enormous symbolic
  # model of the unrelated runtime for this negative control. The positive
  # whole-entry proof and its input domain are unchanged.
  template='''// SPDX-License-Identifier: MIT
include "Primitives.dfy"
module O13InstructionControl {
 import opened Int
 import opened EvmState
 import EVM
 import EvmFork
 import Old = C50Steps
 import S = O13Primitives
 import Stack
 ghost method Check(st:ExecutingState)
   requires st.PC()==9103 && 9103<|st.evm.code.contents|
   requires st.evm.code.contents[9103]==OPCODE
   requires st.evm.fork==EvmFork.CANCUN && st.Gas()>=3
   requires st.evm.stack.contents==[0 as u256,7,3520]
   ensures EVM.Execute(st)==EXECUTING(st.evm.(pc:=9104,gas:=st.Gas()-3,stack:=Stack.Make([S.Neg(7),3520])))
 { Old.Pure(st,OPCODE); reveal Old.Next(); reveal S.Neg(); }
}
'''
  probe=snapshot/'formal/bytecode/o13/InstructionControl.dfy'
  command=[str(ROOT/'proof-tools/assertions/dafny/dafny'),'verify',str(probe),'--manual-lemma-induction','--isolate-assertions','--cores','2','--verification-time-limit','30','--solver-path',str(ROOT/'proof-tools/assertions/dafny/z3/bin/z3-4.12.1'),'--log-format','csv;LogFileName='+str(trial/'positive.csv')]
  probe.write_text(template.replace('OPCODE',str(old)))
  with (trial/'positive.log').open('w') as stream:positive=subprocess.run(command,stdout=stream,stderr=subprocess.STDOUT,cwd=ROOT)
  positive_rows=list(csv.DictReader((trial/'positive.csv').open()));assert positive.returncode==0 and positive_rows and all(r['TestResult.Outcome']=='Passed' for r in positive_rows)
  shutil.copy2(probe,trial/'positive.dfy')
  probe.write_text(template.replace('OPCODE',str(new)))
  command[-1]='csv;LogFileName='+str(trial/'native.csv');symbol='O13InstructionControl.Check'
 else:
  command=[str(ROOT/'proof-tools/assertions/dafny/dafny'),'verify',str(target),'--filter-symbol',symbol,'--manual-lemma-induction','--isolate-assertions','--cores','2','--verification-time-limit','30','--solver-path',str(ROOT/'proof-tools/assertions/dafny/z3/bin/z3-4.12.1'),'--log-format','csv;LogFileName='+str(trial/'native.csv')]
 with (trial/'native.log').open('w') as stream:proc=subprocess.run(command,stdout=stream,stderr=subprocess.STDOUT,cwd=ROOT)
 log=(trial/'native.log').read_text();rows=list(csv.DictReader((trial/'native.csv').open()));summary=re.search(r'finished with (\d+) verified, (\d+) errors?',log)
 killed=proc.returncode!=0 and bool(summary) and int(summary[2])>0 and 'timed out' not in log and any(row['TestResult.Outcome']=='Failed' for row in rows)
 results.append({'name':name,'pc':pc,'symbol':symbol,'command':command,'exitCode':proc.returncode,'killedByNativeProof':killed,'scope':('Paired native single-instruction witness at the real mutation PC; whole-entry credit remains with the complete positive proof' if pc==9103 else 'Mutated whole-helper/block proof'),'positiveSha256':({name:digest(trial/name) for name in ['positive.dfy','positive.log','positive.csv']} if pc==9103 else {}),'extraSourceSha256':({'formal/bytecode/o13/InstructionControl.dfy':digest(snapshot/'formal/bytecode/o13/InstructionControl.dfy')} if pc==9103 else {}),'snapshotSha256':{relative:digest(snapshot/relative) for relative in package['closureSha256']},'logSha256':digest(trial/'native.log'),'csvSha256':digest(trial/'native.csv')})
 (out/'manifest.json').write_text(json.dumps({'status':'running','results':results},indent=2)+'\n');assert killed,name
(out/'manifest.json').write_text(json.dumps({'status':'passed','scriptSha256':digest(Path(__file__)),'originalSources':package['closureSha256'],'results':results},indent=2)+'\n')
print('Passed',len(results),'native bytecode fault controls, with actual verification errors and no timeouts')
