"""Generate a candidate C50 execution proof; native verification grants credit."""
from pathlib import Path
import json
root=Path(__file__).resolve().parents[2]
trace=json.loads((root/'proofs/c50-bytecode/exploration.json').read_text())['trace']
code=bytes.fromhex(json.loads((root/'artifacts/contracts/Assertions.sol/Assertions.json').read_text())['deployedBytecode'][2:])
# Affine expressions in the two ABI offsets, calldata length and first word.
def c(v):return (v,0,0,0,0)
def var(i):return tuple(1 if k==i else 0 for k in range(5))
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def constant(a):return not any(a[1:])
def fmt(a,ctx='st.evm.context'):
    if constant(a):return str(a[0])
    names=['','A','B','L','H']; parts=[]
    for i,n in enumerate(a):
        if not n:continue
        term=str(abs(n)) if i==0 else f'{names[i]}({ctx}) as int'
        if i and abs(n)!=1:term=f'{abs(n)} * ({term})'
        parts.append(('+' if n>0 else '-')+' ('+term+')')
    value=' '.join(parts).removeprefix('+ ')
    return '('+value+') as u256'
def stk(values,ctx='st.evm.context'):return '['+','.join(fmt(v,ctx) for v in values)+']'
memories=list(dict.fromkeys(r['memory'] for r in trace))
stack=[];before=[];after=[];destinations=set(); touched=set()
for i,row in enumerate(trace):
    pc,op=row['pc'],row['opcode']; before.append(stack.copy())
    size=op-0x5f if 0x60<=op<=0x7f else 0
    touched.update(range(pc,pc+1+size))
    if size:stack.insert(0,c(int.from_bytes(code[pc+1:pc+1+size],'big')))
    elif op==0x5f:stack.insert(0,c(0))
    elif op==0x34:stack.insert(0,c(0))
    elif op==0x36:stack.insert(0,var(3))
    elif op==0x35:
        offset=stack.pop(0)
        if offset==c(0):value=var(4)
        elif offset==c(4):value=var(1)
        elif offset==c(36):value=var(2)
        elif offset==add(var(2),c(4)):value=c(0)
        else:raise ValueError(('unrecognized read',pc,offset))
        stack.insert(0,value)
    elif op in (0x01,0x03):
        lhs,rhs=stack[:2];stack=stack[2:];stack.insert(0,(add if op==1 else sub)(lhs,rhs))
    elif op in (0x10,0x11,0x12,0x14):
        stack=stack[2:];stack.insert(0,c(trace[i+1]['stack'][0]))
    elif op==0x15:
        value=stack.pop(0);assert constant(value);stack.insert(0,c(int(value[0]==0)))
    elif op in (0x1b,0x1c):
        shift,value=stack[:2];stack=stack[2:];assert constant(shift)
        if op==0x1c and value==var(4):result=c(0xa5c16924)
        else:
            assert constant(value)
            result=c((value[0]<<shift[0])%(1<<256) if op==0x1b else value[0]>>shift[0])
        stack.insert(0,result)
    elif 0x80<=op<=0x8f:stack.insert(0,stack[op-0x80])
    elif 0x90<=op<=0x9f:
        j=op-0x8f;stack[0],stack[j]=stack[j],stack[0]
    elif op==0x50:stack.pop(0)
    elif op==0x51:
        assert stack.pop(0)==c(64);stack.insert(0,c(128))
    elif op==0x52:stack=stack[2:]
    elif op==0x56:
        dest=stack.pop(0);assert constant(dest);destinations.add(dest[0]);assert dest[0]==trace[i+1]['pc']
    elif op==0x57:
        dest,condition=stack[:2];stack=stack[2:];assert constant(dest) and constant(condition)
        if condition[0]:destinations.add(dest[0]);assert dest[0]==trace[i+1]['pc']
    elif op==0xfd:stack=stack[2:]
    elif op!=0x5b:raise ValueError(('unsupported opcode',op))
    after.append(stack.copy())
    if i+1<len(trace):
        values=[sum(a*b for a,b in zip(v,(1,64,192,228,trace[16]['stack'][0] if False else int.from_bytes(bytes.fromhex('a5c16924')+(64).to_bytes(32,'big')[:28],'big')))) for v in stack]
        # Ground comparison checks only the affine non-selector words.
        assert all(v==sample for v,sample,expr in zip(values,trace[i+1]['stack'],stack) if not expr[4]),(pc,values,trace[i+1]['stack'])
spans=[]
for pc in sorted(touched):
    if spans and pc==spans[-1][1]:spans[-1]=(spans[-1][0],pc+1)
    else:spans.append((pc,pc+1))
spans=[(start,min(start+16,hi)) for lo,hi in spans for start in range(lo,hi,16)]
chunks=[]
for start in range(0,len(trace),4):chunks.append((start,min(start+4,len(trace))))
lines=['// SPDX-License-Identifier: MIT','include "Steps.dfy"','module C50Bytecode {',
 '  import opened Int','  import opened EvmState','  import EVM','  import S = C50Steps','  import EvmFork','  import Bytecode','  import Context','  import Code','  import Stack','  import Memory','  import Gas','  import ByteUtils','  import Arrays','  import U256','  import Word','  import MathUtils = EvmArithmetic',
 '  opaque function A(ctx:Context.T):u256 { ctx.CallDataRead(4) }',
 '  opaque function B(ctx:Context.T):u256 { ctx.CallDataRead(36) }',
 '  opaque function L(ctx:Context.T):u256 { ctx.CallDataSize() }',
 '  lemma ReadL(ctx:Context.T) ensures L(ctx)==ctx.CallDataSize() { reveal L(); }',
 '  opaque function H(ctx:Context.T):u256 { ctx.CallDataRead(0) }',
 '  lemma ReadA(ctx:Context.T) ensures A(ctx)==ctx.CallDataRead(4) { reveal A(); }',
 '  lemma ReadB(ctx:Context.T) ensures B(ctx)==ctx.CallDataRead(36) { reveal B(); }',
 '  lemma ReadH(ctx:Context.T) ensures H(ctx)==ctx.CallDataRead(0) { reveal H(); }',
 '  opaque predicate ValidEmptyCall(ctx:Context.T) {',
 '    ctx.callValue == 0 && 68 <= |ctx.callData| <= MAX_I256 &&',
 '    H(ctx) as int / TWO_224 == 0xa5c16924 &&',
 '    A(ctx) as int <= MAX_U64 && (A(ctx) as nat)+132 <= |ctx.callData| &&',
 '    B(ctx) as int <= MAX_U64 && (B(ctx) as nat)+36 <= |ctx.callData| &&',
 '    ctx.CallDataRead(((B(ctx) as nat)+4) as u256) == 0',
 '  }',
 '  opaque predicate Runtime(code:Code.T) {',f'    {max(touched)+1} <= |code.contents| &&']
for lo,hi in spans:lines.append(f'    code.contents[{lo}..{hi}] == ['+','.join(str(v) for v in code[lo:hi])+'] &&')
lines += ['    '+' && '.join(f'Code.IsInstructionStart(code,0,{x})' for x in sorted(destinations)), '  }']
lines += ['  lemma RuntimeFacts(code:Code.T)', '    requires Runtime(code)', '    requires 17430<=|code.contents|']
for pc in sorted(touched):lines.append(f'    ensures code.contents[{pc}]=={code[pc]}')
lines += ['  { reveal Runtime();']
for lo,hi in spans:
    for pc in range(lo,hi):lines.append(f'    assert code.contents[{lo}..{hi}][{pc-lo}]=={code[pc]};')
lines += ['  }']
for index,mem in enumerate(memories):lines.append(f'  function Mem{index}():seq<u8> {{ S.Mem{index}() }}')
lines+=['  opaque function Step(st:ExecutingState):State { EVM.Execute(st) }',
 '  lemma PureStep(st:ExecutingState,op:u8) requires S.Safe(st,op) ensures Step(st)==S.Next(st,op) { reveal Step(); S.Pure(st,op); }',
 '  lemma MemoryStep(st:ExecutingState) ensures Step(st)==EVM.Execute(st) { reveal Step(); }',
 '  lemma SubtractStep(st:ExecutingState)',
 '    requires S.Safe(st,3) && st.Peek(0)>=st.Peek(1)',
 '    ensures Step(st)==EXECUTING(st.evm.(pc:=st.PC()+1,gas:=st.Gas()-3,stack:=Stack.Make([((st.Peek(0) as int)-(st.Peek(1) as int)) as u256]+st.evm.stack.contents[2..])))',
 '  { PureStep(st,3); reveal S.Next(); assert 0<=st.Peek(0) as int-st.Peek(1) as int<TWO_256; }',
 '  lemma AddStep(st:ExecutingState)',
 '    requires S.Safe(st,1) && st.Peek(0) as int+st.Peek(1) as int<TWO_256',
 '    ensures Step(st)==EXECUTING(st.evm.(pc:=st.PC()+1,gas:=st.Gas()-3,stack:=Stack.Make([((st.Peek(0) as int)+(st.Peek(1) as int)) as u256]+st.evm.stack.contents[2..])))',
 '  { PureStep(st,1); reveal S.Next(); reveal U256.Add(); }',

 '  opaque function Run(st:State,steps:nat):State','    decreases steps','  { if steps == 0 || !st.EXECUTING? then st else Run(Step(st),steps-1) }',
 '  lemma Zero(st:State) ensures Run(st,0)==st { reveal Run(); }',
 '  lemma One(st:State) ensures Run(st,1)==(if st.EXECUTING? then Step(st) else st) { reveal Run(); }',
 '  lemma Compose(st:State,a:nat,b:nat)','    ensures Run(Run(st,a),b) == Run(st,a+b)','    decreases a','  { reveal Run(); if a > 0 && st.EXECUTING? { Compose(Step(st),a-1,b); } }',
 '  lemma RunMatchesKernel(st:ExecutingState,steps:nat)',
 '    requires steps>0',
 '    ensures Run(st,steps)==EVM.ExecuteN(st,steps)',
 '    decreases steps',
 '  { reveal Run(); reveal Step(); reveal EVM.ExecuteN(); var next:=EVM.Execute(st); if steps>1 && next.EXECUTING? { RunMatchesKernel(next,steps-1); } }',
 '  lemma Powers()','    ensures MathUtils.Pow(2,64)==TWO_64','    ensures MathUtils.Pow(2,224)==TWO_224','    ensures MathUtils.Pow(2,225)==2*TWO_224','  {']
for n in [1,2,4,8,16,32,64,7,14,28,56,112,224,225]:lines.append(f'    assert MathUtils.Pow(2,{n}) == {1<<n};')
lines+=['  }',
 '  predicate Bounds(ctx:Context.T) { 68<=L(ctx) as int<=MAX_I256 && A(ctx) as int<=MAX_U64 && A(ctx) as int+132<=L(ctx) as int && B(ctx) as int<=MAX_U64 && B(ctx) as int+36<=L(ctx) as int }',
 '  opaque predicate Ready(st:ExecutingState) { st.evm.fork == EvmFork.CANCUN && Runtime(st.evm.code) && ValidEmptyCall(st.evm.context) }']
lines += ['  lemma ReadyFacts(st:ExecutingState)',
 '    requires Ready(st)',
 '    ensures Runtime(st.evm.code) && 17430<=|st.evm.code.contents|',
 '    ensures L(st.evm.context)==st.evm.context.CallDataSize()',
 '    ensures st.evm.fork==EvmFork.CANCUN && st.evm.context.callValue==0',
 '    ensures 68<=L(st.evm.context) as int<=MAX_I256',
 '    ensures H(st.evm.context) as int/TWO_224==0xa5c16924',
 '    ensures A(st.evm.context) as int<=MAX_U64 && A(st.evm.context) as int+132<=L(st.evm.context) as int',
 '    ensures B(st.evm.context) as int<=MAX_U64 && B(st.evm.context) as int+36<=L(st.evm.context) as int',
 '    ensures st.evm.context.CallDataRead(((B(st.evm.context) as nat)+4) as u256)==0']
for x in sorted(destinations):lines.append(f'    ensures Code.IsInstructionStart(st.evm.code,0,{x})')
lines += ['  { reveal Ready(); reveal Runtime(); reveal ValidEmptyCall(); ReadL(st.evm.context); }']
reveals=['EVM.Execute','EVM.DeductGas','EVM.ExecuteBytecode','Bytecode.Push','Bytecode.Push0','Bytecode.Dup','Bytecode.Swap','Bytecode.JumpDest','Bytecode.Jump','Bytecode.JumpI','Bytecode.CallValue','Bytecode.CallDataLoad','Bytecode.CallDataSize','Bytecode.Lt','Bytecode.Gt','Bytecode.SLt','Bytecode.Eq','Bytecode.IsZero','Bytecode.Add','Bytecode.Sub','Bytecode.Shl','Bytecode.Shr','Bytecode.Pop','Bytecode.MLoad','Bytecode.MStore','Bytecode.Revert','S.Next','S.Safe','S.Supported','S.Cost','S.Arity','S.Adds','Mem0','Mem1','Mem2','Code.Slice','Arrays.SliceAndPad','ByteUtils.ConvertBytesTo256','ByteUtils.ReadUint16','Memory.ExpandMem','Memory.Expand','Gas.CostExpandBytes','Gas.CostExpandRange','Gas.ExpansionSize']
for block,(lo,hi) in enumerate(chunks):
    first=trace[lo];used0=100000-first['gas'];used1=100000-trace[hi]['gas'] if hi<len(trace) else 693
    inp_mem=memories.index(first['memory']); last=hi==len(trace)
    lines += [f'  ghost method Block{block:03}(st:ExecutingState) returns(out:State)',
       '    requires Ready(st)', '    requires Bounds(st.evm.context)',f"    requires st.PC() == {first['pc']}",f'    requires st.evm.stack.contents == {stk(before[lo])}',f'    requires st.evm.memory.contents == Mem{inp_mem}()',f'    requires st.Gas() >= {693-used0}',f'    ensures out == Run(st,{hi-lo})']
    if last:lines += ['    ensures out == ERROR(REVERTS,gas:=st.Gas()-'+str(used1-used0)+',data:=[57,85,175,170])']
    else:
        nxt=trace[hi];outmem=memories.index(nxt['memory'])
        lines += [f"    ensures out == EXECUTING(st.evm.(pc:={nxt['pc']},stack:=Stack.Make({stk(before[hi])}),memory:=Memory.Memory(Mem{outmem}()),gas:=st.Gas()-{used1-used0}))"]
    lines+=['  {','    Powers();']
    lines += ['    reveal '+name+'();' for name in ['S.Safe','S.Supported','S.Cost','S.Arity','S.Adds','Mem0','Mem1','Mem2','Code.Slice','Arrays.SliceAndPad','ByteUtils.ConvertBytesTo256','ByteUtils.ReadUint16','ByteUtils.ReadUint32']]
    lines += ['    ReadyFacts(st); RuntimeFacts(st.evm.code);', '    reveal EvmFork.CANCUN; reveal EvmFork.CANCUN_BYTECODES; reveal EvmFork.GENISIS_BYTECODES;', '    EvmFork.EipSet(EvmFork.CANCUN_EIPS,EvmFork.GENISIS_BYTECODES);','    var s := st; var next:State; Zero(st);']
    for i in range(lo,hi):
        pc=trace[i]['pc'];op=trace[i]['opcode']
        if op==0x52: hint=f'S.{"StoreInitial" if pc==4 else "StoreError"}(s,s.evm.stack.contents[2..]);'
        elif op==0x51: hint=f'S.{"LoadPointer" if pc==2612 else "LoadPointerAfter"}(s,s.evm.stack.contents[1..]);'
        elif op==0xfd: hint='S.RevertError(s,s.evm.stack.contents[2..]);'
        elif op==3:hint='SubtractStep(s);'
        elif op==1:hint='AddStep(s);'
        else:hint=f'PureStep(s,{op});'
        if 0x60<=op<=0x7f:
            size=op-0x5f
            for offset in range(1,size+1):lines.append(f'    assert s.evm.code.contents[{pc+offset}]=={code[pc+offset]};')
            sequence='['+','.join(str(v)+' as u8' for v in code[pc+1:pc+1+size])+']'
            lines.append(f'    assert Code.Slice(s.evm.code,{pc+1},{size})=={sequence};')
        lines.append(f'    assert s.evm.code.contents[{pc}]=={op};')
        if op==0x36:lines.append('    ReadL(s.evm.context);')
        if op==0x35:
            offset=before[i][0]
            if offset==c(0):lines.append('    ReadH(s.evm.context);')
            elif offset==c(4):lines.append('    ReadA(s.evm.context);')
            elif offset==c(36):lines.append('    ReadB(s.evm.context);')
        lines.append('    '+hint)
        if op in [0x51,0x52,0xfd]:lines.append('    MemoryStep(s);')
        lines += ['    next := Step(s);']
        if i+1<len(trace):
            nxt=trace[i+1];phase=memories.index(nxt['memory']);use=100000-nxt['gas']-used0
            lines += [f"    assert next == EXECUTING(st.evm.(pc:={nxt['pc']},stack:=Stack.Make({stk(after[i])}),memory:=Memory.Memory(Mem{phase}()),gas:=st.Gas()-{use})) by {{ reveal S.Next(); }}",'    One(s);',f'    Compose(st,{i-lo},1);',f'    assert next == Run(st,{i-lo+1});','    s := next;']
        else:
            lines += ['    assert next == ERROR(REVERTS,gas:=st.Gas()-'+str(used1-used0)+',data:=[57,85,175,170]);','    One(s);',f'    Compose(st,{i-lo},1);',f'    assert next == Run(st,{i-lo+1});','    out := next;']
    if not last:lines+=['    out := s;']
    lines+=['  }']
lines += ['  ghost method FullC50(st:ExecutingState) returns(out:State)',
 '    requires Ready(st)','    requires st.PC()==0 && st.evm.stack.contents==[] && st.evm.memory.contents==[]',
 '    requires st.Gas()>=693','    ensures out == Run(st,204)', '    ensures out == EVM.ExecuteN(st,204)',
 '    ensures out == ERROR(REVERTS,gas:=st.Gas()-693,data:=[57,85,175,170])',
 '  {','    ReadyFacts(st); reveal Ready();','    var s:State := st; var next:State; Zero(st);']
for block,(lo,hi) in enumerate(chunks):
    lines += [f'    next := Block{block:03}(s);',f'    Compose(st,{lo},{hi-lo});',f'    assert next == Run(st,{hi});']
    if hi<len(trace):lines+=['    s := next;']
    else:lines+=['    RunMatchesKernel(st,204);','    out := next;']
lines += ['  }','}']
(root/'proofs/c50-bytecode/Entry.dfy').write_text('\n'.join(lines)+'\n')
print('Generated',len(trace),'actual opcode steps;',len(chunks),'blocks;',len(lines),'lines')
print('jump targets',sorted(destinations))
