"""Make every actual instruction and cumulative interpreter state explicit."""
from pathlib import Path
import sys,re
sys.path.insert(0,'formal/tools');from declarations import declarations
raw=declarations(Path('proofs/o13-bytecode/MacroEntry.dfy'));core=declarations(Path('formal/bytecode/o13/Core.dfy'))
windows=[]
for name,d in core.items():
 if re.fullmatch('Window[0-9]+',name):
  m=re.search(r'code.contents\[(\d+)\.\.(\d+)\]',d['body']);windows.append((name,int(m[1]),int(m[2])))
compact=lambda s:re.sub(r'\s+','',s)
planned={};total=0;casts=0
for p in sorted(Path('formal/bytecode/o13').glob('Blocks*.dfy')):
 text=p.read_text()
 for name,d in declarations(p).items():
  r=raw[name];assert compact(r['interface'])==compact(d['interface']),name
  new=r['full'];byte=raw['Bytes'+name]['full'];pcs=list(map(int,re.findall(r'ensures code.contents\[(\d+)\]',byte)))
  needed=sorted({w for w,lo,hi in windows if any(lo<=pc<hi for pc in pcs)})
  targets=list(map(int,re.findall(r'ensures Start\(code,(\d+)\)',byte)))
  calls=' '.join(w+'Facts(st.evm.code);' for w in needed)+' '+' '.join('TargetFacts(st.evm.code,'+str(pc)+');' for pc in targets)
  assert 'Bytes'+name+'(st.evm.code);' in new
  new=new.replace('Bytes'+name+'(st.evm.code);',calls)
  i=new.index('  {');body=new[i:];exprs=set()
  for m in re.finditer(r'\) as u256',body):
   depth=1;j=m.start()-1
   while depth:
    if body[j]==')':depth+=1
    if body[j]=='(':depth-=1
    j-=1
   e=body[j+1:m.end()]
   if 'st.evm.context' in e and body.count(e)>1:exprs.add(e)
  assignments=[]
  for k,e in enumerate(sorted(exprs,key=lambda e:(-len(e),e))):
   v=f'word{k}';body=body.replace(e,v);assignments.append(f'    var {v}:u256 := {e};')
  if assignments:
   assert 'var s:=st;' in body,name
   body=body.replace('var s:=st;', '\n'.join(assignments)+'\n    var s:=st;',1)
  new=new[:i]+body
  n=len(re.findall(r'next:=Step\(s\);',body));assert n==len(re.findall(r'next:=Step\(s\);\s*assert next==',body)),name
  total+=n;casts+=len(exprs);text=text.replace(d['full'],new)
 planned[p]=text
assert total==1683
for p,text in planned.items():p.write_text(text)
print('Explicit states for',total,'actual kernel instructions; shared',casts,'word conversions; all 501 block interfaces preserved')
