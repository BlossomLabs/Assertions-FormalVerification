"""Split candidate modules and runtime windows; theorem domains stay unchanged."""
from pathlib import Path
import re,sys,json
ROOT=Path.cwd();sys.path.insert(0,str(ROOT/'formal/tools'));from declarations import declarations
src=ROOT/'proofs/o13-bytecode/MacroEntry.dfy';items=declarations(src);raw=src.read_text()
imports=raw[raw.index('  import opened Int'):raw.index('  opaque function A(')]
out=ROOT/'formal/bytecode/o13'
core={k:v['full'] for k,v in items.items() if not re.fullmatch(r'(?:Bytes)?Block\d+|Case\d+|Path\d+|FullAdd|FullMul',k)}
runtime=core['Runtime'];windows=re.findall(r'code.contents\[(\d+)\.\.(\d+)\]==\[([\d, ]+)\]',runtime);starts=re.findall(r'Start\(code,(\d+)\)',runtime);assert windows and starts
bounds=max(int(b) for a,b,_ in windows)
wnames=[]
for i,(a,b,vs) in enumerate(windows):
 name=f'Window{i:03}';wnames.append(name);core[name]=f'opaque predicate {name}(code:Code.T) {{ {b}<=|code.contents| && code.contents[{a}..{b}]==[{vs}] }}'
for i,(a,b,vs) in enumerate(windows):
 name=wnames[i]
 vals=[int(v) for v in vs.split(',')]
 specs=' '.join(f'ensures code.contents[{int(a)+j}]=={v}' for j,v in enumerate(vals))
 assertions=' '.join(f'assert code.contents[{a}..{b}][{j}]=={v};' for j,v in enumerate(vals))
 core[name+'Facts']=f'lemma {name}Facts(code:Code.T) requires Runtime(code) ensures {b}<=|code.contents| && code.contents[{a}..{b}]==[{vs}] '+specs+f' {{ reveal Runtime(); reveal {name}(); '+assertions+' }'

target='lemma TargetFacts(code:Code.T,p:nat) requires Runtime(code) && p in {'+','.join(starts)+'} ensures Start(code,p) ensures p<|code.contents| && code.contents[p]==91 { reveal Runtime();\n'
for j,pc in enumerate(starts):
 i=next(i for i,(a,b,vs) in enumerate(windows) if int(a)<=int(pc)<int(b))
 target+=('if' if j==0 else 'else if')+' p=='+pc+' { '+wnames[i]+'Facts(code); }\n'
target+='else { assert false; } }';core['TargetFacts']=target
core['Runtime']='opaque predicate Runtime(code:Code.T) { '+str(bounds)+'<=|code.contents| && '+' && '.join(n+'(code)' for n in wnames)+' && '+' && '.join('Start(code,'+p+')' for p in starts)+' }'
(out/'Core.dfy').write_text('// SPDX-License-Identifier: MIT\ninclude "Primitives.dfy"\nmodule O13Core {\n'+imports+'\n'.join(core.values())+'\n}\n')
blocksyms=sorted([k for k in items if re.fullmatch('Block\\d+',k)]);block_map={}
for group in range((len(blocksyms)+19)//20):
 module=f'O13Blocks{group:02}';defs=[]
 for name in blocksyms[group*20:(group+1)*20]:
  block_map[name]=module;byte=items['Bytes'+name]['full'];pcs=list(map(int,re.findall(r'ensures code.contents\[(\d+)\]',byte)));needed={wnames[i] for i,(a,b,_) in enumerate(windows) if any(int(a)<=p<int(b) for p in pcs)}
  byte=byte.replace('reveal Runtime();','reveal Runtime(); '+''.join('reveal '+n+'(); ' for n in sorted(needed)))
  block=items[name]['full']
  targetpcs=list(map(int,re.findall(r'ensures Start\(code,(\d+)\)',byte)))
  calls=' '.join(n+'Facts(st.evm.code);' for n in sorted(needed))+' '+ ' '.join('TargetFacts(st.evm.code,'+str(p)+');' for p in targetpcs)
  block=block.replace('Bytes'+name+'(st.evm.code);',calls)
  defs.append(block)
 (out/f'Blocks{group:02}.dfy').write_text('// SPDX-License-Identifier: MIT\ninclude "Core.dfy"\nmodule '+module+' {\n'+imports+'  import Helpers = O13Helpers\n  import Stacks = O13Stacks\n  import opened Common = O13Core\n'+'\n'.join(defs)+'\n}\n')
end={k:v['full'] for k,v in items.items() if re.fullmatch('Case\\d+|Path\\d+|FullAdd|FullMul',k)}
for k,s in end.items():
 for b,m in block_map.items():s=re.sub(r'\b'+b+r'\(',m+'.'+b+'(',s)
 end[k]=s
inc=''.join(f'include "Blocks{g:02}.dfy"\n' for g in range((len(blocksyms)+19)//20));imp=''.join('  import '+m+'\n' for m in sorted(set(block_map.values())))
(out/'Entry.dfy').write_text('// SPDX-License-Identifier: MIT\n'+inc+'module O13Bytecode {\n'+imports+'  import Helpers = O13Helpers\n  import Stacks = O13Stacks\n  import opened Common = O13Core\n'+imp+'\n'.join(end.values())+'\n}\n')
print(len(block_map),'blocks split into',len(set(block_map.values())),'modules;',len(windows),'opaque runtime windows')
