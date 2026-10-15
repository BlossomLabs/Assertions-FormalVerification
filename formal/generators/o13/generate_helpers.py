from pathlib import Path
import json,re
R=Path.cwd();P=R/'proofs/o13-bytecode';paths=json.load(open(P/'exploration.json'))['paths'];code=bytes.fromhex((R/'formal/evidence/o13-current-capture-20261015-v2/runtime.hex').read_text())
imports=(R/'formal/bytecode/o13/Core.dfy').read_text();imports=imports[imports.index('  import opened Int'):imports.index('opaque function A(')]
W=1<<256
c=lambda n:(n,0,0,0)
v=lambda n:tuple(int(i==n) for i in range(4))
constant=lambda x:not any(x[1:])
def fmt(x):
 if constant(x):return str(x[0])
 if x in [v(1),v(2),v(3)]:return {v(1):'w',v(2):'ret',v(3):'S.Neg(w)'}[x]
 terms=[]
 for i,n in enumerate(x):
  if n:terms.append(('+' if n>0 else '-')+'('+str(abs(n))*(i==0)+(('w as int' if i==1 else 'ret as int') if i else '')+')')
 return '('+''.join(terms).lstrip('+')+') as u256'
def stk(xs):return '['+','.join(fmt(x) for x in xs)+']+tail'
windows=[]
core=(R/'formal/bytecode/o13/Core.dfy').read_text()
for m in re.finditer(r'opaque predicate (Window\d+)\(code:Code.T\).*?code.contents\[(\d+)\.\.(\d+)\]',core,re.S):windows.append((m[1],int(m[2]),int(m[3])))
layout=['// SPDX-License-Identifier: MIT','include "../../formal/bytecode/o13/Core.dfy"','module O13Stacks {',imports,'  import opened Common = O13Core']
text=['// SPDX-License-Identifier: MIT','include "Stacks.dfy"','module O13Helpers {',imports,'  import L = O13Stacks','  import opened Common = O13Core','  lemma Power255() ensures MathUtils.Pow(2,255)==TWO_255 {']
# The exponent decomposition follows the library's recursive power equation.
for n in [1,3,7,15,31,63,127,255]:text.append(f'    assert MathUtils.Pow(2,{n})=={1<<n};')
text+=['  }','  lemma Shift255() ensures U256.Shl(1,255)==TWO_255 as u256 { Power255(); reveal U256.Shl(); }']
for name,start,example,negative in [('MagPos',8754,1,False),('MagNeg',8754,4,True),('RestorePos',9046,1,False),('RestoreNeg',9046,4,True)]:
 trace=paths[example]['trace'];lo=next(i for i,t in enumerate(trace) if t['pc']==start and ((t['stack'][0]>=(1<<255))==negative if start==8754 else (t['stack'][0]!=0)==negative))
 ret=trace[lo]['stack'][1 if start==8754 else 2];hi=next(i for i in range(lo+1,len(trace)) if trace[i]['pc']==ret);seg=trace[lo:hi];stack=([v(1),v(2)] if start==8754 else [c(int(negative)),v(1),v(2)]);before=[];after=[];touched=set();targets=set()
 for i,t in enumerate(seg):
  pc,op=t['pc'],t['opcode'];before.append(stack.copy());width=op-95 if 96<=op<=127 else 0;touched.update(range(pc,pc+width+1))
  if width:stack.insert(0,c(int.from_bytes(code[pc+1:pc+width+1],'big')))
  elif op==95:stack.insert(0,c(0))
  elif 128<=op<=143:stack.insert(0,stack[op-128])
  elif 144<=op<=159:j=op-143;stack[0],stack[j]=stack[j],stack[0]
  elif op==80:stack.pop(0)
  elif op in [1,3]:
   a,b=stack[:2];stack=stack[2:]
   if op==3 and a==c(0) and b==v(1):result=v(3)
   else:result=tuple(x+(y if op==1 else -y) for x,y in zip(a,b))
   stack.insert(0,result)
  elif op in [18,17]:stack=stack[2:];stack.insert(0,c(trace[lo+i+1]['stack'][0]))
  elif op==21:a=stack.pop(0);assert constant(a);stack.insert(0,c(int(a[0]==0)))
  elif op==27:a,b=stack[:2];assert constant(a) and constant(b);stack=stack[2:];stack.insert(0,c((b[0]<<a[0])%W))
  elif op==87:
   dest,cond=stack[:2];stack=stack[2:];assert constant(dest)
   if trace[lo+i+1]['pc']==dest[0]:targets.add(dest[0]);touched.add(dest[0])
  elif op==86:
   dest=stack.pop(0)
   if constant(dest):targets.add(dest[0]);touched.add(dest[0])
   else:assert dest==v(2) and i==len(seg)-1
  elif op!=91:raise AssertionError(op)
  after.append(stack.copy())
 assert stack==[v(3) if negative else v(1)],stack
 domain=('Word.asI256(w)<0' if negative else 'Word.asI256(w)>=0') if start==8754 else 'w as int<TWO_255'
 states=before+[after[-1]]
 for j,xs in enumerate(states):
  fn=f'{name}{j:02}'
  layout += [f'  opaque function {fn}(w:u256,ret:u256,tail:seq<u256>):seq<u256>',f'    ensures |{fn}(w,ret,tail)|=={len(xs)}+|tail|']+[f'    ensures {fn}(w,ret,tail)[{k}]=={fmt(x)}' for k,x in enumerate(xs)]+['  { '+stk(xs)+' }']
  if j==0 or j==len(seg):layout += [f'  lemma Open{fn}(w:u256,ret:u256,tail:seq<u256>) ensures {fn}(w,ret,tail)=={stk(xs)} {{ reveal {fn}(); }}']
 for j,t in enumerate(seg):
  op=t['opcode'];pi=f'{name}{j:02}(w,ret,tail)';po=f'{name}{j+1:02}(w,ret,tail)';xs=before[j]
  if 96<=op<=127 or op==95:expr='['+fmt(after[j][0])+']+'+pi
  elif 128<=op<=143:expr=f'[{pi}[{op-128}]]+{pi}'
  elif op==80 or op==86:expr=pi+'[1..]'
  elif op==87:expr=pi+'[2..]'
  elif 144<=op<=159:k=op-143;expr=f'{pi}[0:={pi}[{k}]][{k}:={pi}[0]]'
  elif op==91:expr=pi
  else:expr='['+fmt(after[j][0])+']+'+pi+'['+('1' if op==21 else '2')+'..]'
  layout += [f'  lemma Next{name}{j:02}(w:u256,ret:u256,tail:seq<u256>)',f'    ensures {po}=={expr}','  { reveal '+name+f'{j:02}(); reveal '+name+f'{j+1:02}(); }}']
 usedwindows={n for n,a,b in windows if any(a<=p<b for p in touched)}
 text += [f'  lemma Bytes{name}(code:Code.T)','    requires Runtime(code)',f'    requires 19832<=|code.contents|']+[f'    ensures code.contents[{p}]=={code[p]}' for p in sorted(touched)]+[f'    ensures Start(code,{p})' for p in sorted(targets)]+['  { reveal Runtime();']+['    reveal '+n+'();' for n in sorted(usedwindows)]
 for pc in sorted(touched):_,a,b=next(x for x in windows if x[1]<=pc<x[2]);text.append(f'    assert code.contents[{a}..{b}][{pc-a}]=={code[pc]};')
 gas=trace[lo]['gas']-trace[hi]['gas'];n=len(seg);result='S.Mag(w)' if start==8754 else ('S.Neg(w)' if negative else 'w')
 text+=['  }',f'  ghost method {name}(st:ExecutingState,w:u256,ret:u256,tail:seq<u256>) returns(out:ExecutingState)', '    requires Runtime(st.evm.code) && 19832<=|st.evm.code.contents| && st.evm.fork==EvmFork.CANCUN',f'    requires st.PC()=={start} && st.evm.memory.contents==Base.Mem1()',f'    requires st.evm.stack.contents==L.{name}00(w,ret,tail)','    requires |tail|<=980 && ret as nat<|st.evm.code.contents| && st.evm.code.contents[ret as nat]==91 && Start(st.evm.code,ret as nat)',f'    requires st.Gas()>={gas}']
 text += [('    requires Word.asI256(w)<0' if negative else '    requires Word.asI256(w)>=0') if start==8754 else '    requires w as int<TWO_255']
 text += [f'    ensures out==Run(st,{n})',f'    ensures out==EXECUTING(st.evm.(pc:=ret as nat,gas:=st.Gas()-{gas},stack:=Stack.Make([{result}]+tail)))','  {',f'    Bytes{name}(st.evm.code); S.Magnitude(w); Power255();', '    reveal S.Safe(); reveal Base.Safe(); reveal Old.Safe(); reveal Old.Supported(); reveal Old.Cost(); reveal Old.Arity(); reveal Old.Adds();','    reveal S.Next(); reveal Base.Next(); reveal Old.Next(); reveal S.Neg();','    reveal Code.Slice(); reveal Arrays.SliceAndPad(); reveal ByteUtils.ConvertBytesTo256(); reveal ByteUtils.ReadUint16(); reveal ByteUtils.ReadUint32();','    var s:=st; var next:State; Zero(st);']
 for i,t in enumerate(seg):
  pc,op=t['pc'],t['opcode']
  if op==86 and before[i][0]==v(2):text.append('    Jump(s.evm.code,ret as nat);')
  if op in [86,87] and constant(before[i][0]) and before[i][0][0] in targets:text.append(f'    Jump(s.evm.code,{before[i][0][0]});')
  if 96<=op<=127:text.append(f'    assert Code.Slice(s.evm.code,{pc+1},{op-95})==['+','.join(str(b)+' as u8' for b in code[pc+1:pc+op-94])+'];')
  if op==27:text.append('    Shift255();')
  text += [f'    PureStep(s,{op});','    next:=Step(s);']
  npc='ret as nat' if i+1==n else str(seg[i+1]['pc']);cost=trace[lo]['gas']-trace[lo+i+1]['gas']
  text.append(f'    L.Next{name}{i:02}(w,ret,tail);')
  text.append(f'    assert next==EXECUTING(st.evm.(pc:={npc},gas:=st.Gas()-{cost},stack:=Stack.Make(L.{name}{i+1:02}(w,ret,tail))));')
  text += ['    One(s);',f'    Compose(st,{i},1);',f'    assert next==Run(st,{i+1});','    s:=next;']
 text += [f'    L.Open{name}{n:02}(w,ret,tail);','    out:=s;','  }'];print(name,'steps',n,'gas',gas)
layout+=['}'];(P/'Stacks.dfy').write_text('\n'.join(layout)+'\n')
text+=['}'];(P/'Helpers.dfy').write_text('\n'.join(text)+'\n')
