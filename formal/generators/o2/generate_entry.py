"""Generate native-checked candidate traces. This script grants no proof credit."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[2];BASE=ROOT/'proofs/o2-bytecode'
paths=json.loads((BASE/'exploration.json').read_text())['paths'];CODE=bytes.fromhex((ROOT/'formal/evidence/o2-runtime-capture-20261015-v1/runtime.hex').read_text())
def c(v):return (v,0,0,0,0,0,0)
def v(i):return tuple(int(k==i) for k in range(7))
def plus(a,b):return tuple(x+y for x,y in zip(a,b))
def minus(a,b):return tuple(x-y for x,y in zip(a,b))
def isconst(a):return not any(a[1:])
def fmt(a,ctx='st.evm.context',rem=False):
 if isconst(a):return str(a[0])
 names=['','A','B','M','L','H','R']
 if a[0]==0 and sum(abs(x) for x in a[1:])==1 and max(a[1:])==1:
  i=a.index(1);return f'R({ctx},{str(rem).lower()})' if i==6 else f'{names[i]}({ctx})'
 pieces=[]
 for i,n in enumerate(a):
  if n:
   term=str(abs(n)) if i==0 else (f'R({ctx},{str(rem).lower()}) as int' if i==6 else f'{names[i]}({ctx}) as int')
   if i and abs(n)!=1:term=f'{abs(n)}*({term})'
   pieces.append(('+' if n>0 else '-')+'('+term+')')
 return '('+''.join(pieces).removeprefix('+')+') as u256'
def stk(a,ctx='st.evm.context',rem=False):return '['+','.join(fmt(x,ctx,rem) for x in a)+']'
def mem(n,ctx='st.evm.context',rem=False):return ['S.Mem0()','S.Mem1()','S.Panic1()','S.Panic2()',f'S.ResultMem(R({ctx},{str(rem).lower()}))'][n]
touched=set();targets=set();programs=[]
for path in paths:
 trace=path['trace'];rem=path['name']=='mod';selector=int(path['selector'],16);before=[];after=[];phases=[];stack=[];phase=0
 for i,row in enumerate(trace):
  pc,op=row['pc'],row['opcode'];before.append(stack.copy());phases.append(phase);width=op-0x5f if 0x60<=op<=0x7f else 0;touched.update(range(pc,pc+1+width))
  if width:stack.insert(0,c(int.from_bytes(CODE[pc+1:pc+1+width],'big')))
  elif op==0x5f:stack.insert(0,c(0))
  elif op==0x34:stack.insert(0,c(0))
  elif op==0x36:stack.insert(0,v(4))
  elif op==0x35:
   off=stack.pop(0);assert isconst(off);stack.insert(0,v({0:5,4:1,36:2,68:3}[off[0]]))
  elif op in [1,3]:a,b=stack[:2];stack=stack[2:];stack.insert(0,(plus if op==1 else minus)(a,b))
  elif op in [4,6]:
   assert stack[:2]==[v(1),v(2)];stack=stack[2:];stack.insert(0,v(6))
  elif op in [16,17,18,20]:stack=stack[2:];stack.insert(0,c(trace[i+1]['stack'][0]))
  elif op==21:
   a=stack.pop(0);assert isconst(a);stack.insert(0,c(int(a[0]==0)))
  elif op in [27,28]:
   n,a=stack[:2];stack=stack[2:];assert isconst(n)
   if op==28 and a==v(5):res=c(selector)
   else:
    assert isconst(a);res=c((a[0]<<n[0])%(1<<256) if op==27 else a[0]>>n[0])
   stack.insert(0,res)
  elif 0x80<=op<=0x8f:stack.insert(0,stack[op-0x80])
  elif 0x90<=op<=0x9f:j=op-0x8f;stack[0],stack[j]=stack[j],stack[0]
  elif op==80:stack.pop(0)
  elif op==81:assert stack.pop(0)==c(64);stack.insert(0,c(128))
  elif op==82:
   a,b=stack[:2];stack=stack[2:];assert isconst(a)
   phase={64:1,0:2,4:3,128:4}[a[0]]
  elif op==86:
   dest=stack.pop(0);assert isconst(dest);targets.add(dest[0])
  elif op==87:
   dest,cond=stack[:2];stack=stack[2:];assert isconst(dest)
   if trace[i+1]['pc']==dest[0]:targets.add(dest[0])
  elif op in [0xfd,0xf3]:stack=stack[2:]
  elif op!=0x5b:raise AssertionError((pc,op))
  after.append(stack.copy())
 path.update(before=before,after=after,phases=phases,rem=rem);programs.append(path)
spans=[]
for pc in sorted(touched):
 if spans and spans[-1][1]==pc:spans[-1]=(spans[-1][0],pc+1)
 else:spans.append((pc,pc+1))
spans=[(i,min(i+16,hi)) for lo,hi in spans for i in range(lo,hi,16)]
lines=['// SPDX-License-Identifier: MIT','include "Primitives.dfy"','module O2Bytecode {','  import opened Int','  import opened EvmState','  import EVM','  import S = O2Primitives','  import Old = C50Steps','  import EvmFork','  import Context','  import Code','  import Stack','  import Memory','  import Gas','  import ByteUtils','  import Arrays','  import U256','  import Word','  import MathUtils = EvmArithmetic']
for name,off in [('A',4),('B',36),('H',0)]:lines += [f'  opaque function {name}(ctx:Context.T):u256 {{ ctx.CallDataRead({off}) }}',f'  lemma Read{name}(ctx:Context.T) ensures {name}(ctx)==ctx.CallDataRead({off}) {{ reveal {name}(); }}']
lines += ['  opaque function L(ctx:Context.T):u256 { ctx.CallDataSize() }','  lemma ReadL(ctx:Context.T) ensures L(ctx)==ctx.CallDataSize() { reveal L(); }','  opaque function R(ctx:Context.T,rem:bool):u256 { S.Value(rem,A(ctx),B(ctx)) }','  lemma ReadR(ctx:Context.T,rem:bool) ensures R(ctx,rem)==S.Value(rem,A(ctx),B(ctx)) { reveal R(); }','  function Selector(rem:bool):u256 { if rem then 0xf43f523a else 0xa391c15b }','  opaque predicate ValidCall(ctx:Context.T,rem:bool) { ctx.callValue==0 && 68<=|ctx.callData|<=MAX_I256+4 && H(ctx) as int/TWO_224==(Selector(rem) as int) }','  predicate Bounds(ctx:Context.T) { 68<=L(ctx) as int<=MAX_I256+4 }','  opaque predicate Runtime(code:Code.T) {',f'    {max(touched)+1}<=|code.contents| &&']
for lo,hi in spans:lines.append(f'    code.contents[{lo}..{hi}]=='+str(list(CODE[lo:hi]))+' &&')
lines += ['    '+' && '.join(f'Code.IsInstructionStart(code,0,{p})' for p in sorted(targets)),'  }','  lemma RuntimeFacts(code:Code.T)','    requires Runtime(code)',f'    requires {max(touched)+1}<=|code.contents|']
for pc in sorted(touched):lines.append(f'    ensures code.contents[{pc}]=={CODE[pc]}')
lines+=['  { reveal Runtime();']
for lo,hi in spans:
 for pc in range(lo,hi):lines.append(f'    assert code.contents[{lo}..{hi}][{pc-lo}]=={CODE[pc]};')
lines += ['  }','  opaque predicate Ready(st:ExecutingState,rem:bool) { st.evm.fork==EvmFork.CANCUN && Runtime(st.evm.code) && ValidCall(st.evm.context,rem) }','  lemma ReadyFacts(st:ExecutingState,rem:bool)','    requires Ready(st,rem)','    ensures Runtime(st.evm.code)',f'    ensures {max(touched)+1}<=|st.evm.code.contents|','    ensures st.evm.fork==EvmFork.CANCUN && st.evm.context.callValue==0','    ensures Bounds(st.evm.context) && L(st.evm.context)==st.evm.context.CallDataSize()','    ensures H(st.evm.context) as int/TWO_224==(Selector(rem) as int)']
for dest in sorted(targets):lines.append(f'    ensures Code.IsInstructionStart(st.evm.code,0,{dest})')
lines += ['  { reveal Ready(); reveal Runtime(); reveal ValidCall(); ReadL(st.evm.context); }','  opaque function Step(st:ExecutingState):State { EVM.Execute(st) }','  lemma PureStep(st:ExecutingState,op:u8) requires S.Safe(st,op) ensures Step(st)==S.Next(st,op) { reveal Step(); S.Pure(st,op); }','  lemma MemoryStep(st:ExecutingState) ensures Step(st)==EVM.Execute(st) { reveal Step(); }','  opaque function Run(st:State,n:nat):State decreases n { if n==0 || !st.EXECUTING? then st else Run(Step(st),n-1) }','  lemma Zero(st:State) ensures Run(st,0)==st { reveal Run(); }','  lemma One(st:State) ensures Run(st,1)==(if st.EXECUTING? then Step(st) else st) { reveal Run(); }','  lemma Compose(st:State,a:nat,b:nat) ensures Run(Run(st,a),b)==Run(st,a+b) decreases a { reveal Run(); if a>0 && st.EXECUTING? { Compose(Step(st),a-1,b); } }','  lemma RunMatchesKernel(st:ExecutingState,n:nat) requires n>0 ensures Run(st,n)==EVM.ExecuteN(st,n) decreases n { reveal Run(); reveal Step(); reveal EVM.ExecuteN(); var next:=EVM.Execute(st); if n>1 && next.EXECUTING? { RunMatchesKernel(next,n-1); } }','  lemma Powers() ensures MathUtils.Pow(2,224)==TWO_224 {']
for n in [1,2,4,7,14,28,56,112,224]:lines.append(f'    assert MathUtils.Pow(2,{n})=={1<<n};')
lines+=['  }']
lines += ['  lemma WordResult(ctx:Context.T,rem:bool)', '    requires B(ctx)>0', '    ensures R(ctx,rem)==(if rem then (A(ctx) as int)%(B(ctx) as int) else (A(ctx) as int)/(B(ctx) as int)) as u256', '  { ReadR(ctx,rem); S.ValueEquation(rem,A(ctx),B(ctx)); }']
blocks={};plans=[]
for path in programs:
 trace=path['trace'];rem=path['rem'];mode=str(rem).lower();zero=path['zero'];plan=[]
 boundaries=[0]
 while boundaries[-1]<len(trace):
  lo=boundaries[-1];hi=min(lo+4,len(trace))
  stores=[i for i in range(lo,hi) if trace[i]['opcode']==82]
  if stores:hi=stores[0]+1
  boundaries.append(hi)
 for lo,hi in zip(boundaries,boundaries[1:]):
  entry=trace[lo];islast=hi==len(trace);end=trace[hi] if not islast else None
  branch=any(t['opcode']==87 and path['before'][i][1]==v(2) for i,t in enumerate(trace[lo:hi],lo))
  # After the divisor guard, retain its case premise to justify terminal paths.
  guardindex=next(i for i,t in enumerate(trace) if t['opcode']==87 and path['before'][i][1]==v(2))
  case=zero if hi>guardindex else None
  key=(rem,case,tuple((t['pc'],t['opcode']) for t in trace[lo:hi]),tuple(path['before'][lo]),tuple(path['after'][hi-1]),path['phases'][lo],islast)
  if key in blocks:plan.append((blocks[key],lo,hi));continue
  name=f'Block{len(blocks):03}';blocks[key]=name;plan.append((name,lo,hi));used0=100000-entry['gas'];used1=path['gasUsed'] if islast else 100000-end['gas'];cost=used1-used0
  used=sorted({pc for row in trace[lo:hi] for pc in range(row['pc'],row['pc']+1+(row['opcode']-0x5f if 0x60<=row['opcode']<=0x7f else 0))})
  for i in range(lo,hi):
   row=trace[i]
   if row['opcode'] in [86,87]:
    dest=path['before'][i][0];assert isconst(dest)
    if row['opcode']==86 or trace[i+1]['pc']==dest[0]:used=sorted(set(used)|{dest[0]})
  lines += [f'  lemma Bytes{name}(code:Code.T)', '    requires Runtime(code)',f'    requires {max(touched)+1}<=|code.contents|']
  lines += [f'    ensures code.contents[{pc}]=={CODE[pc]}' for pc in used]
  lines += ['  { reveal Runtime();']
  for pc in used:
   spanlo,spanhi=next((a,b) for a,b in spans if a<=pc<b)
   lines.append(f'    assert code.contents[{spanlo}..{spanhi}][{pc-spanlo}]=={CODE[pc]};')
  lines += ['  }']
  lines += [f'  ghost method {name}(st:ExecutingState) returns(out:State)',f'    requires Ready(st,{mode})','    requires Bounds(st.evm.context)']
  if case is not None:lines.append('    requires B(st.evm.context)'+('==0' if case else '>0'))
  lines += [f"    requires st.PC()=={entry['pc']}",f'    requires st.evm.stack.contents=={stk(path["before"][lo],rem=rem)}',f'    requires st.evm.memory.contents=={mem(path["phases"][lo],rem=rem)}',f'    requires st.Gas()>={cost}',f'    ensures out==Run(st,{hi-lo})']
  def state_at(i,cost):
   if i==len(trace):
    if zero:return f'ERROR(REVERTS,gas:=st.Gas()-{cost},data:=S.PanicData())'
    return f'RETURNS(st.Gas()-{cost},U256.ToBytes(R(st.evm.context,{mode})),st.evm.world,st.evm.transient,st.evm.substate)'
   return f'EXECUTING(st.evm.(pc:={trace[i]["pc"]},gas:=st.Gas()-{cost},stack:=Stack.Make({stk(path["before"][i],rem=rem)}),memory:=Memory.Memory({mem(path["phases"][i],rem=rem)})))'
  lines += ['    ensures out=='+state_at(hi,cost),'  {','    Powers();',f'    ReadyFacts(st,{mode}); Bytes{name}(st.evm.code);','    reveal S.Safe(); reveal Old.Safe(); reveal Old.Supported(); reveal Old.Cost(); reveal Old.Arity(); reveal Old.Adds();','    reveal Code.Slice(); reveal Arrays.SliceAndPad(); reveal ByteUtils.ConvertBytesTo256(); reveal ByteUtils.ReadUint16(); reveal ByteUtils.ReadUint32();','    var s:=st; var next:State; Zero(st);']
  for i in range(lo,hi):
   row=trace[i];pc,op=row['pc'],row['opcode'];lines.append(f'    assert s.evm.code.contents[{pc}]=={op};')
   if 0x60<=op<=0x7f:
    size=op-0x5f
    for j in range(1,size+1):lines.append(f'    assert s.evm.code.contents[{pc+j}]=={CODE[pc+j]};')
    lines.append(f'    assert Code.Slice(s.evm.code,{pc+1},{size})==['+','.join(str(b)+' as u8' for b in CODE[pc+1:pc+1+size])+'];')
   if op==53:lines.append('    Read'+{0:'H',4:'A',36:'B',68:'M'}[path['before'][i][0][0]]+'(s.evm.context);')
   if op==54:lines.append('    ReadL(s.evm.context);')
   if op in [4,6]:lines.append(f'    ReadR(s.evm.context,{mode});')
   if op==82:
    a,val=path['before'][i][:2]
    if a==c(64):lines.append('    Old.StoreInitial(s,s.evm.stack.contents[2..]);')
    else:
     nextphase=path['phases'][i+1];addr=a[0];coststore=100000-trace[i+1]['gas']-(100000-row['gas'])
     lines += ['    S.Facts(0);','    reveal S.Panic1(); reveal S.Panic2(); reveal S.ResultMem(); reveal Memory.ExpandMem(); reveal Memory.Expand();',f'    S.Store(s,{addr},{fmt(val,"s.evm.context",rem)},{mem(path["phases"][i],"s.evm.context",rem)},{mem(nextphase,"s.evm.context",rem)},{coststore});']
    lines.append('    MemoryStep(s);')
   elif op==81:lines += [f'    S.Load(s,R(s.evm.context,{mode}));','    MemoryStep(s);']
   elif op in [243,253]:lines += [f'    S.Exit(s,R(s.evm.context,{mode}),{str(zero).lower()});','    MemoryStep(s);']
   else:lines.append(f'    PureStep(s,{op});')
   consumed=path['gasUsed']-used0 if i+1==len(trace) else 100000-trace[i+1]['gas']-used0
   lines += ['    next:=Step(s);','    assert next=='+state_at(i+1,consumed)+' by { reveal S.Next(); reveal Old.Next(); }','    One(s);',f'    Compose(st,{i-lo},1);',f'    assert next==Run(st,{i-lo+1});']
   lines.append('    s:=next;' if i+1<len(trace) else '    out:=next;')
  if not islast:lines.append('    out:=s;')
  lines+=['  }']
 plans.append((path,plan))
for path,plan in plans:
 mode=str(path['rem']).lower();zero=path['zero'];name=('Mod' if path['rem'] else 'Div')+('Zero' if zero else 'Nonzero');n=path['steps'];gas=path['gasUsed']
 lines += [f'  ghost method {name}(st:ExecutingState) returns(out:State)',f'    requires Ready(st,{mode})','    requires st.PC()==0 && st.evm.stack.contents==[] && st.evm.memory.contents==[]',f'    requires st.Gas()>={gas}','    requires B(st.evm.context)'+('==0' if zero else '>0'),f'    ensures out==EVM.ExecuteN(st,{n})',('    ensures out==ERROR(REVERTS,gas:=st.Gas()-'+str(gas)+',data:=S.PanicData())' if zero else f'    ensures out==RETURNS(st.Gas()-{gas},U256.ToBytes(R(st.evm.context,{mode})),st.evm.world,st.evm.transient,st.evm.substate)'), '  {',f'    ReadyFacts(st,{mode}); reveal Ready();','    var s:State:=st; var next:State; Zero(st);']
 for b,lo,hi in plan:
  lines += [f'    next:={b}(s);',f'    Compose(st,{lo},{hi-lo});',f'    assert next==Run(st,{hi});']
  if hi<n:lines.append('    s:=next;')
 lines += [f'    RunMatchesKernel(st,{n});','    out:=next;','  }']
for rem in [False,True]:
 mode=str(rem).lower();name='Mod' if rem else 'Div';zero_steps,success_steps,zero_gas,success_gas=(127,142,471,526) if rem else (118,133,428,483)
 value=f'S.Value({mode},A(st.evm.context),B(st.evm.context))'
 lines += [f'  ghost method Full{name}(st:ExecutingState) returns(out:State)',f'    requires Ready(st,{mode})','    requires st.PC()==0 && st.evm.stack.contents==[] && st.evm.memory.contents==[]',f'    requires st.Gas()>={success_gas}',f'    ensures out==EVM.ExecuteN(st,if B(st.evm.context)==0 then {zero_steps} else {success_steps})',f'    ensures out==(if B(st.evm.context)==0 then ERROR(REVERTS,gas:=st.Gas()-{zero_gas},data:=S.PanicData()) else RETURNS(st.Gas()-{success_gas},U256.ToBytes({value}),st.evm.world,st.evm.transient,st.evm.substate))','  {',f'    if B(st.evm.context)==0 {{ out:={name}Zero(st); }} else {{ out:={name}Nonzero(st); ReadR(st.evm.context,{mode}); }}','  }']
lines+=['}'];(BASE/'Entry.dfy').write_text('\n'.join(lines)+'\n')
(BASE/'structure.json').write_text(json.dumps({'blocks':len(blocks),'touched':sorted(touched),'targets':sorted(targets),'paths':[{'name':p['name'],'zero':p['zero'],'steps':p['steps'],'gas':p['gasUsed'],'blocks':[b for b,_,_ in plan]} for p,plan in plans]},indent=2)+'\n')
print('Generated',len(blocks),'shared blocks;',len(touched),'bound runtime bytes;',len(lines),'lines')
