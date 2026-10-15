"""Candidate straight-line proofs; only fresh native verification grants proof evidence."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[2];BASE=ROOT/'proofs/o13-bytecode'
CODE=bytes.fromhex((ROOT/'formal/evidence/o13-current-capture-20261015-v1/runtime.hex').read_text())
paths=json.loads((BASE/'exploration.json').read_text())['paths']
W=1<<256
def c(x):return (x,0,0,0,0,0,0,0)
def v(i):return tuple(int(k==i) for k in range(8))
def const(x):return not any(x[1:])
def fmt(x,ctx='st.evm.context',mul=False):
 if const(x):return str(x[0])
 names=['','A','B','M','L','H','R','N'];mode=str(mul).lower()
 def term(i):return f'{names[i]}({ctx},{mode})' if i>=6 else f'{names[i]}({ctx})'
 if x[0]==0 and sum(abs(n) for n in x[1:])==1 and max(x[1:])==1:return term(x.index(1))
 pieces=[]
 for i,n in enumerate(x):
  if n:
   t=str(abs(n)) if i==0 else term(i)+' as int'
   if i and abs(n)!=1:t=f'{abs(n)}*({t})'
   pieces.append(('+' if n>0 else '-')+'('+t+')')
 return '('+''.join(pieces).removeprefix('+')+') as u256'
def stack(xs,ctx='st.evm.context',mul=False):return '['+','.join(fmt(x,ctx,mul) for x in xs)+']'
def mem(n,ctx='st.evm.context',mul=False):return ['Base.Mem0()','Base.Mem1()','Base.Panic1()','Base.Panic2()',f'Base.ResultMem(V({ctx},{str(mul).lower()}))'][n]
def ev(x,r):
 vals=[1]+[(a%W) for a in r['arguments']]+[100,(int(r['selector'],16)<<224)|((r['arguments'][0]%W)>>32)]+[0,0]
 aa,bb,mm=r['arguments'];val=aa*bb if r['mul'] else aa+bb;vals[6]=abs(val)%abs(mm) if mm else 0;vals[7]=(-vals[6])%W
 return sum(a*b for a,b in zip(x,vals))
touched=set();targets=set()
for r in paths:
 r['mul']=r['name']=='mulMod';s=[];phase=0;conds=[];r.update(before=[],after=[],phases=[],conditions=[])
 for i,t in enumerate(r['trace']):
  pc,op=t['pc'],t['opcode'];r['before'].append(s.copy());r['phases'].append(phase);width=op-95 if 96<=op<=127 else 0;touched.update(range(pc,pc+1+width))
  if width:s.insert(0,c(int.from_bytes(CODE[pc+1:pc+1+width],'big')))
  elif op in [95,52]:s.insert(0,c(0))
  elif op==54:s.insert(0,v(4))
  elif op==53:off=s.pop(0);assert const(off);s.insert(0,v({0:5,4:1,36:2,68:3}[off[0]]))
  elif op in [1,3]:
   a,b=s[:2];s=s[2:]
   if op==3 and a==c(0) and b==v(6):out=v(7)
   else:
    out=tuple(x+(y if op==1 else -y) for x,y in zip(a,b));actual=ev(out,r);offset=-(actual//W)*W;out=(out[0]+offset,)+out[1:]
   s.insert(0,out)
  elif op in [6,8,9]:s=s[2 if op==6 else 3:];s.insert(0,v(6))
  elif op in [16,17,18,20]:
   a,b=s[:2];s=s[2:];value=r['trace'][i+1]['stack'][0]
   if not(const(a) and const(b)) and not any(a[j] or b[j] for j in [4,5,6,7]):
    fa,fb=fmt(a,'ctx',r['mul']),fmt(b,'ctx',r['mul']);cmp={16:'<',17:'>',18:'<',20:'=='}[op]
    if op==18:fa=f'Word.asI256({fa})';fb=f'Word.asI256({fb})'
    cond=f'({fa}{cmp}{fb})';cond=cond if value else '!'+cond
    if cond not in conds:conds.append(cond)
   s.insert(0,c(value))
  elif op==21:
   a=s.pop(0)
   if const(a):value=int(a[0]==0)
   else:
    value=r['trace'][i+1]['stack'][0];cond=fmt(a,'ctx',r['mul'])+('==0' if value else '!=0')
    if cond not in conds:conds.append(cond)
   s.insert(0,c(value))
  elif op in [27,28]:
   a,b=s[:2];s=s[2:];assert const(a)
   if op==28 and b==v(5):out=c(int(r['selector'],16))
   else:assert const(b);out=c((b[0]<<a[0])%W if op==27 else b[0]>>a[0])
   s.insert(0,out)
  elif 128<=op<=143:s.insert(0,s[op-128])
  elif 144<=op<=159:j=op-143;s[0],s[j]=s[j],s[0]
  elif op==80:s.pop(0)
  elif op==81:assert s.pop(0)==c(64);s.insert(0,c(128))
  elif op==82:addr,val=s[:2];s=s[2:];assert const(addr);phase={64:1,0:2,4:3,128:4}[addr[0]]
  elif op==86:dest=s.pop(0);assert const(dest);targets.add(dest[0])
  elif op==87:
   dest,cond=s[:2];s=s[2:];assert const(dest);taken=r['trace'][i+1]['pc']==dest[0]
   if taken:targets.add(dest[0])
   if not const(cond):
    expr=fmt(cond,'ctx',r['mul'])+('!=0' if taken else '==0')
    if expr not in conds:conds.append(expr)
  elif op in [243,253]:s=s[2:]
  elif op!=91:raise AssertionError((pc,op))
  r['after'].append(s.copy());r['conditions'].append(tuple(conds))
  if i+1<len(r['trace']):
   for j,x in enumerate(s):assert ev(x,r)%W==r['trace'][i+1]['stack'][j],(r['arguments'],pc,j,x,ev(x,r),r['trace'][i+1]['stack'][j])
 r['case']=tuple(conds)
spans=[]
for pc in sorted(touched):
 if spans and spans[-1][1]==pc:spans[-1]=(spans[-1][0],pc+1)
 else:spans.append((pc,pc+1))
spans=[(i,min(i+16,b)) for a,b in spans for i in range(a,b,16)];length=max(touched)+1
old=(ROOT/'formal/bytecode/o12/Entry.dfy').read_text();header=old[:old.index('  opaque predicate Runtime(')].replace('O12Bytecode','O13Bytecode').replace('import S = O12Primitives','import S = O13Primitives\n  import Base = O12Primitives').replace('S.Value(mul,A(ctx),B(ctx),M(ctx))','S.Rem(mul,A(ctx),B(ctx),M(ctx))').replace('0xa4ad2ee9 else 0xb12fe826','0x3daa08a5 else 0x289b860c')
lines=header.splitlines()+['  opaque function N(ctx:Context.T,mul:bool):u256 { S.Neg(R(ctx,mul)) }','  opaque function V(ctx:Context.T,mul:bool):u256 { S.Value(mul,A(ctx),B(ctx),M(ctx)) }','  lemma MathFacts(ctx:Context.T,mul:bool)','    ensures R(ctx,mul) as int<TWO_255','    ensures N(ctx,mul)==S.Neg(R(ctx,mul))','    ensures R(ctx,mul)==S.Rem(mul,A(ctx),B(ctx),M(ctx))','  { ReadR(ctx,mul); reveal N(); S.RemBounds(mul,A(ctx),B(ctx),M(ctx)); S.Magnitude(A(ctx)); S.Magnitude(B(ctx)); S.Magnitude(M(ctx)); }','  lemma Reduction(ctx:Context.T,mul:bool)','    requires M(ctx)>0','    ensures mul ==> R(ctx,mul)==Base.Value(true,S.Mag(A(ctx)),S.Mag(B(ctx)),S.Mag(M(ctx)))','    ensures !mul && (S.Signed(A(ctx))<0)==(S.Signed(B(ctx))<0) ==> R(ctx,mul)==Base.Value(false,S.Mag(A(ctx)),S.Mag(B(ctx)),S.Mag(M(ctx)))','    ensures !mul && (S.Signed(A(ctx))<0)!=(S.Signed(B(ctx))<0) && S.Mag(A(ctx))>=S.Mag(B(ctx)) ==> R(ctx,mul)==((S.Mag(A(ctx)) as int-S.Mag(B(ctx)) as int)%(S.Mag(M(ctx)) as int)) as u256','    ensures !mul && (S.Signed(A(ctx))<0)!=(S.Signed(B(ctx))<0) && S.Mag(A(ctx))<S.Mag(B(ctx)) ==> R(ctx,mul)==((S.Mag(B(ctx)) as int-S.Mag(A(ctx)) as int)%(S.Mag(M(ctx)) as int)) as u256','  { ReadR(ctx,mul); S.Remainder(mul,A(ctx),B(ctx),M(ctx)); }','  opaque predicate Start(code:Code.T,p:nat) { Code.IsInstructionStart(code,0,p) }','  lemma Jump(code:Code.T,p:nat) requires Start(code,p) ensures Code.IsInstructionStart(code,0,p) { reveal Start(); }','  opaque predicate Runtime(code:Code.T) {',f'    {length}<=|code.contents| &&']
for lo,hi in spans:lines.append(f'    code.contents[{lo}..{hi}]=={list(CODE[lo:hi])} &&')
lines+=['    '+' && '.join(f'Start(code,{p})' for p in sorted(targets)),'  }']
start=old.index('  opaque predicate Ready(');end=old.index('  lemma WordResult(')
rest=old[start:end].replace('19756',str(length))
# Rebuild jump-start postconditions for this runtime.
a=rest.index('    ensures Code.IsInstructionStart');b=rest.index('  { reveal Ready();',a)
rest=rest[:a]+rest[b:]
lines+=rest.splitlines()+['  lemma Terminal(st:State,n:nat) requires !st.EXECUTING? ensures Run(st,n)==st { reveal Run(); }']
blocks={};plans=[]
for ix,r in enumerate(paths):
 trace=r['trace'];mul=r['mul'];mode=str(mul).lower();plan=[];bounds=[0]
 while bounds[-1]<len(trace):
  lo=bounds[-1]
  if trace[lo]['pc'] in [8754,9046]:
   slot=1 if trace[lo]['pc']==8754 else 2;ret=r['before'][lo][slot];assert const(ret)
   hi=next(i for i in range(lo+1,len(trace)) if trace[i]['pc']==ret[0])
  else:
   hi=min(lo+4,len(trace));special=[i for i in range(lo+1,hi) if trace[i]['pc'] in [8754,9046]]
   if special:hi=special[0]
   stores=[i for i in range(lo,hi) if trace[i]['opcode']==82]
   if stores:hi=stores[0]+1
  bounds.append(hi)
 for lo,hi in zip(bounds,bounds[1:]):
  entry=trace[lo];last=hi==len(trace);conds=r['conditions'][hi-1]
  key=(mul,conds,tuple((t['pc'],t['opcode']) for t in trace[lo:hi]),tuple(r['before'][lo]),tuple(r['after'][hi-1]),r['phases'][lo],last)
  if key in blocks:plan.append((blocks[key],lo,hi));continue
  name=f'Block{len(blocks):03}';blocks[key]=name;plan.append((name,lo,hi));used0=100000-entry['gas'];used1=r['gasUsed'] if last else 100000-trace[hi]['gas'];cost=used1-used0
  macro=entry['pc'] in [8754,9046]
  localtargets=set()
  used={pc for t in trace[lo:hi] for pc in range(t['pc'],t['pc']+1+(t['opcode']-95 if 96<=t['opcode']<=127 else 0))}
  for i in range(lo,hi):
   t=trace[i]
   if t['opcode'] in [86,87] and (t['opcode']==86 or trace[i+1]['pc']==r['before'][i][0][0]):used.add(r['before'][i][0][0]);localtargets.add(r['before'][i][0][0])
  if macro:
   ret=r['before'][lo][1 if entry['pc']==8754 else 2][0];used={ret};localtargets={ret}
  lines += [f'  lemma Bytes{name}(code:Code.T)','    requires Runtime(code)',f'    requires {length}<=|code.contents|']+[f'    ensures code.contents[{p}]=={CODE[p]}' for p in sorted(used)]+[f'    ensures Start(code,{p})' for p in sorted(localtargets)]+['  { reveal Runtime();']
  for p in sorted(used):a,b=next((a,b) for a,b in spans if a<=p<b);lines.append(f'    assert code.contents[{a}..{b}][{p-a}]=={CODE[p]};')
  lines+=['  }',f'  ghost method {name}(st:ExecutingState) returns(out:State)',f'    requires Ready(st,{mode})','    requires Bounds(st.evm.context)']+['    requires '+x.replace('ctx','st.evm.context') for x in conds]
  lines += [f'    requires st.PC()=={entry["pc"]}',f'    requires st.evm.stack.contents=={stack(r["before"][lo],mul=mul)}',f'    requires st.evm.memory.contents=={mem(r["phases"][lo],mul=mul)}',f'    requires st.Gas()>={cost}',f'    ensures out==Run(st,{hi-lo})']
  def state(i,cost):
   if i==len(trace):return f'ERROR(REVERTS,gas:=st.Gas()-{cost},data:=Base.PanicData())' if r['error'] else f'RETURNS(st.Gas()-{cost},U256.ToBytes(V(st.evm.context,{mode})),st.evm.world,st.evm.transient,st.evm.substate)'
   return f'EXECUTING(st.evm.(pc:={trace[i]["pc"]},gas:=st.Gas()-{cost},stack:=Stack.Make({stack(r["before"][i],mul=mul)}),memory:=Memory.Memory({mem(r["phases"][i],mul=mul)})))'
  if macro:
   mag=entry['pc']==8754;slot=0 if mag else 1;arg=r['before'][lo][slot];word=fmt(arg,mul=mul)
   negative=(trace[lo]['stack'][0]>=(1<<255)) if mag else trace[lo]['stack'][0]!=0
   helper=('Mag' if mag else 'Restore')+('Neg' if negative else 'Pos')
   lines += ['    ensures out=='+state(hi,cost),'  {',f'    ReadyFacts(st,{mode}); Bytes{name}(st.evm.code); Jump(st.evm.code,{ret});']
   if mag:lines.append(f'    S.Magnitude({word});')
   else:lines.append(f'    MathFacts(st.evm.context,{mode});')
   lines += [f'    Stacks.Open{helper}00({word},{ret},st.evm.stack.contents[{2 if mag else 3}..]);']
   lines += [f'    out:=Helpers.{helper}(st,{word},{ret},st.evm.stack.contents[{2 if mag else 3}..]);','  }']
   continue
  lines+=['    ensures out=='+state(hi,cost),'  {','    Powers();',f'    ReadyFacts(st,{mode}); Bytes{name}(st.evm.code);', '    reveal S.Safe(); reveal Base.Safe(); reveal Old.Safe(); reveal Old.Supported(); reveal Old.Cost(); reveal Old.Arity(); reveal Old.Adds();','    reveal Code.Slice(); reveal Arrays.SliceAndPad(); reveal ByteUtils.ConvertBytesTo256(); reveal ByteUtils.ReadUint16(); reveal ByteUtils.ReadUint32();','    var s:=st; var next:State; Zero(st);']
  for i in range(lo,hi):
   t=trace[i];pc,op=t['pc'],t['opcode'];lines.append(f'    assert s.evm.code.contents[{pc}]=={op};')
   if 96<=op<=127:
    size=op-95;lines += [f'    assert s.evm.code.contents[{pc+j}]=={CODE[pc+j]};' for j in range(1,size+1)]+[f'    assert Code.Slice(s.evm.code,{pc+1},{size})==['+','.join(str(b)+' as u8' for b in CODE[pc+1:pc+1+size])+'];']
   if any(any(x[j] for j in [6,7]) for x in r['before'][i]+r['after'][i]):lines.append(f'    MathFacts(s.evm.context,{mode});')
   if op in [86,87] and r['before'][i][0][0] in localtargets:lines.append(f'    Jump(s.evm.code,{r["before"][i][0][0]});')
   if op in [6,8,9] or (op==82 and r['before'][i][0]==c(128)):lines.append('    S.Magnitude(A(s.evm.context)); S.Magnitude(B(s.evm.context)); S.Magnitude(M(s.evm.context));')
   if op==53:lines.append('    Read'+{0:'H',4:'A',36:'B',68:'M'}[r['before'][i][0][0]]+'(s.evm.context);')
   if op==54:lines.append('    ReadL(s.evm.context);')
   if op in [6,8,9]:lines.append(f'    Reduction(s.evm.context,{mode});')
   if pc==9103:lines.append(f'    reveal S.Neg();')
   if op==82:
    addr,val=r['before'][i][:2]
    if addr==c(64):lines.append('    Old.StoreInitial(s,s.evm.stack.contents[2..]);')
    else:
     if addr==c(128):lines += [f'    S.Restore({mode},A(s.evm.context),B(s.evm.context),M(s.evm.context)); reveal V();']
     coststore=trace[i]['gas']-trace[i+1]['gas'];lines += [f'    Base.Facts(V(s.evm.context,{mode}));','    reveal Base.Panic1(); reveal Base.Panic2(); reveal Base.ResultMem(); reveal Memory.ExpandMem(); reveal Memory.Expand();',f'    Base.Store(s,{addr[0]},{fmt(val,"s.evm.context",mul)},{mem(r["phases"][i],"s.evm.context",mul)},{mem(r["phases"][i+1],"s.evm.context",mul)},{coststore});']
    lines.append('    MemoryStep(s);')
   elif op==81:lines += [f'    Base.Load(s,V(s.evm.context,{mode}));','    MemoryStep(s);']
   elif op in [243,253]:lines += [f'    Base.Exit(s,V(s.evm.context,{mode}),{str(r["error"]).lower()});','    MemoryStep(s);']
   else:lines.append(f'    PureStep(s,{op});')
   consumed=r['gasUsed']-used0 if i+1==len(trace) else 100000-trace[i+1]['gas']-used0
   lines += ['    next:=Step(s);','    assert next=='+state(i+1,consumed)+' by { reveal S.Next(); reveal Base.Next(); reveal Old.Next(); }','    One(s);',f'    Compose(st,{i-lo},1);',f'    assert next==Run(st,{i-lo+1});',('    s:=next;' if i+1<len(trace) else '    out:=next;')]
  if not last:lines.append('    out:=s;')
  lines+=['  }']
 plans.append((r,plan))
for ix,(r,plan) in enumerate(plans):
 mode=str(r['mul']).lower();n=r['steps'];gas=r['gasUsed']
 lines += [f'  predicate Case{ix}(ctx:Context.T) {{ '+(' && '.join(r['case']) or 'true')+' }',f'  ghost method Path{ix}(st:ExecutingState) returns(out:State)',f'    requires Ready(st,{mode})',f'    requires Case{ix}(st.evm.context)','    requires st.PC()==0 && st.evm.stack.contents==[] && st.evm.memory.contents==[]',f'    requires st.Gas()>={gas}',f'    ensures out==Run(st,400)',('    ensures out==ERROR(REVERTS,gas:=st.Gas()-'+str(gas)+',data:=Base.PanicData())' if r['error'] else f'    ensures out==RETURNS(st.Gas()-{gas},U256.ToBytes(V(st.evm.context,{mode})),st.evm.world,st.evm.transient,st.evm.substate)'), '  {',f'    ReadyFacts(st,{mode}); reveal Ready();','    var s:State:=st; var next:State; Zero(st);']
 for b,lo,hi in plan:lines += [f'    next:={b}(s);',f'    Compose(st,{lo},{hi-lo});',f'    assert next==Run(st,{hi});']+(['    s:=next;'] if hi<n else [])
 lines += [f'    Terminal(next,{400-n}); Compose(st,{n},{400-n});','    out:=next;','  }']
for mul in [False,True]:
 mode=str(mul).lower();name='Mul' if mul else 'Add';subset=[(ix,r) for ix,r in enumerate(paths) if r['mul']==mul]
 lines += [f'  ghost method Full{name}(st:ExecutingState) returns(out:State)',f'    requires Ready(st,{mode})','    requires st.PC()==0 && st.evm.stack.contents==[] && st.evm.memory.contents==[]','    requires st.Gas()>=1100','    ensures out==EVM.ExecuteN(st,400)',f'    ensures M(st.evm.context)==0 ==> out.ERROR? && out.error==REVERTS && out.data==Base.PanicData()',f'    ensures M(st.evm.context)>0 ==> out.RETURNS? && out.data==U256.ToBytes(S.Value({mode},A(st.evm.context),B(st.evm.context),M(st.evm.context))) && out.world==st.evm.world && out.transient==st.evm.transient && out.substate==st.evm.substate','  {',f'    MathFacts(st.evm.context,{mode}); reveal V();']
 for j,(ix,r) in enumerate(subset):lines.append(('    if' if j==0 else '    else if')+f' Case{ix}(st.evm.context) {{ out:=Path{ix}(st); }}')
 lines += ['    else { assert false; }','    RunMatchesKernel(st,400);','  }']
lines += ['}'];(BASE/'MacroEntry.dfy').write_text('\n'.join(lines)+'\n');(BASE/'structure.json').write_text(json.dumps({'blocks':len(blocks),'touched':sorted(touched),'targets':sorted(targets),'cases':[list(r['case']) for r in paths]},indent=2)+'\n');print(len(blocks),'blocks',len(lines),'lines',len(touched),'runtime bytes')
