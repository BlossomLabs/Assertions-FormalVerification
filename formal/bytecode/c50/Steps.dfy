include "../../../proof-tools/dafnyevm/src/dafny/evm.dfy"
include "Stores.dfy"
module C50Steps {
  import opened Int
  import opened EvmState
  import EVM
  import Bytecode
  import EvmFork
  import Opcode
  import Code
  import Context
  import Stack
  import Memory
  import Gas
  import Arrays
  import ByteUtils
  import U16
  import U32
  import U64
  import U128
  import U256
  import Word
  import Stores = C50Stores
  predicate Supported(op:u8) { op in {1,3,16,17,18,20,21,27,28,52,53,54,80,86,87,91,95,96,97,99,128,129,130,131,132,133,134,135,144,145,146,147,148,150,151} }
  function Cost(op:u8):nat { if op==0x5b then 1 else if op in {0x34,0x36,0x50,0x5f} then 2 else if op==0x56 then 8 else if op==0x57 then 10 else 3 }
  function Arity(op:u8):nat { if 0x80<=op<=0x8f then (op as nat)-0x80+1 else if 0x90<=op<=0x9f then (op as nat)-0x8f+1 else if op in {0x35,0x50,0x56,0x15} then 1 else if op in {0x01,0x03,0x10,0x11,0x12,0x14,0x1b,0x1c,0x57} then 2 else 0 }
  function Adds(op:u8):bool { op in {0x34,0x36,0x5f,0x60,0x61,0x63} || 0x80<=op<=0x8f }
  predicate Safe(st:ExecutingState,op:u8) {
    Supported(op) && st.PC()<|st.evm.code.contents| && st.evm.code.contents[st.PC()]==op &&
    st.evm.fork==EvmFork.CANCUN && st.Gas()>=Cost(op) && st.Operands()>=Arity(op) &&
    (Adds(op) ==> st.Capacity()>=1) &&
    (op in {0x60,0x61,0x63} ==> st.PC()+((op as nat)-0x5f)<|st.evm.code.contents|) &&
    (op==0x56 ==> st.IsJumpDest(st.Peek(0))) &&
    (op==0x57 ==> st.Peek(1)==0 || st.IsJumpDest(st.Peek(0)))
  }
  function Next(st:ExecutingState,op:u8):ExecutingState
    requires Safe(st,op)
  {
    var xs:=st.evm.stack.contents;
    var stack :=
      if op==0x01 then [U256.Add(xs[0],xs[1])]+xs[2..]
      else if op==0x03 then [((xs[0] as int-xs[1] as int)%TWO_256) as u256]+xs[2..]
      else if op==0x10 then [if xs[0]<xs[1] then 1 as u256 else 0 as u256]+xs[2..]
      else if op==0x11 then [if xs[0]>xs[1] then 1 as u256 else 0 as u256]+xs[2..]
      else if op==0x12 then [if Word.asI256(xs[0])<Word.asI256(xs[1]) then 1 as u256 else 0 as u256]+xs[2..]
      else if op==0x14 then [if xs[0]==xs[1] then 1 as u256 else 0 as u256]+xs[2..]
      else if op==0x15 then [if xs[0]==0 then 1 as u256 else 0 as u256]+xs[1..]
      else if op==0x1b then [U256.Shl(xs[1],xs[0])]+xs[2..]
      else if op==0x1c then [U256.Shr(xs[1],xs[0])]+xs[2..]
      else if op==0x34 then [st.evm.context.callValue]+xs
      else if op==0x35 then [if xs[0]>=st.evm.context.CallDataSize() then 0 as u256 else st.evm.context.CallDataRead(xs[0])]+xs[1..]
      else if op==0x36 then [st.evm.context.CallDataSize()]+xs
      else if op==0x50 then xs[1..]
      else if op==0x56 then xs[1..]
      else if op==0x57 then xs[2..]
      else if op==0x5f then [0 as u256]+xs
      else if op in {0x60,0x61,0x63} then [ByteUtils.ConvertBytesTo256(Code.Slice(st.evm.code,st.PC()+1,(op as nat)-0x5f))]+xs
      else if 0x80<=op<=0x8f then [xs[(op as nat)-0x80]]+xs
      else if 0x90<=op<=0x9f then xs[0:=xs[(op as nat)-0x8f]][(op as nat)-0x8f:=xs[0]]
      else xs;
    var pc := if op==0x56 then xs[0] as nat else if op==0x57 && xs[1]!=0 then xs[0] as nat else if op in {0x60,0x61,0x63} then st.PC()+1+(op as nat)-0x5f else st.PC()+1;
    EXECUTING(st.evm.(stack:=Stack.Make(stack),pc:=pc,gas:=st.Gas()-Cost(op)))
  }
  lemma Pure(st:ExecutingState,op:u8)
    requires Safe(st,op)
    ensures EVM.Execute(st)==Next(st,op)
  {
    reveal EvmFork.CANCUN; reveal EvmFork.CANCUN_BYTECODES; reveal EvmFork.GENISIS_BYTECODES; EvmFork.EipSet(EvmFork.CANCUN_EIPS,EvmFork.GENISIS_BYTECODES);
    reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode();
    reveal Bytecode.Add();
    reveal Bytecode.Sub();
    reveal Bytecode.Lt();
    reveal Bytecode.Gt();
    reveal Bytecode.SLt();
    reveal Bytecode.Eq();
    reveal Bytecode.IsZero();
    reveal Bytecode.Shl();
    reveal Bytecode.Shr();
    reveal Bytecode.CallValue();
    reveal Bytecode.CallDataLoad();
    reveal Bytecode.CallDataSize();
    reveal Bytecode.Pop();
    reveal Bytecode.Jump();
    reveal Bytecode.JumpI();
    reveal Bytecode.Push0();
    reveal Bytecode.Push();
    reveal Bytecode.Dup();
    reveal Bytecode.Swap();
    reveal Bytecode.JumpDest();
  }
  function Mem0():seq<u8> { [] }
  function Mem1():seq<u8> { ByteUtils.Padding(64)+U256.ToBytes(128) }
  function Mem2():seq<u8> { Mem1()+ByteUtils.Padding(32)+U256.ToBytes(25933226758553968569565623594072278329591374616828141097895289445724687695872) }
  lemma PaddingSlice(n:nat,a:nat,b:nat)
    requires a<=b<=n
    ensures ByteUtils.Padding(n)[a..b]==ByteUtils.Padding(b-a)
  { reveal ByteUtils.Padding(); }
  lemma MemoryFacts()
    ensures |Mem1()|==96 && |Mem2()|==160
    ensures Memory.ReadUint256(Memory.Memory(Mem1()),64)==128
    ensures Memory.ReadUint256(Memory.Memory(Mem2()),64)==128
    ensures Memory.Slice(Memory.Memory(Mem2()),128,4)==[57 as u8,85,175,170]
  {
    reveal Mem1(); reveal Mem2(); reveal Memory.Slice(); reveal Arrays.SliceAndPad();
    U256.BytesValue(128);
    assert Mem1()[64..96]==U256.ToBytes(128);
    assert Mem2()[64..96]==U256.ToBytes(128);
    ByteUtils.FullWordValue(Mem1(),64); ByteUtils.FullWordValue(Mem2(),64);
    assert U16.ToBytes(0x3955)==[57 as u8,85];
    assert U16.ToBytes(0xafaa)==[175 as u8,170];
    assert U32.ToBytes(0x3955afaa)==[57 as u8,85,175,170];
    assert U64.ToBytes(0x3955afaa00000000)[..4]==[57 as u8,85,175,170];
    assert U128.ToBytes(0x3955afaa000000000000000000000000)[..4]==[57 as u8,85,175,170];
    assert U256.ToBytes(25933226758553968569565623594072278329591374616828141097895289445724687695872)[..4]==[57 as u8,85,175,170];
    assert Mem2()[128..132]==[57 as u8,85,175,170];
  }
  lemma StoreAny(st:ExecutingState)
    requires st.PC()<|st.evm.code.contents| && st.evm.code.contents[st.PC()]==0x52
    requires st.evm.fork==EvmFork.CANCUN && st.Operands()>=2
    requires st.Gas()>=3+Gas.ExpansionSize(st.evm.memory,st.Peek(0) as nat,32)
    ensures EVM.Execute(st)==EXECUTING(st.evm.(pc:=st.PC()+1,stack:=Stack.Make(st.evm.stack.contents[2..]),memory:=Memory.WriteUint256(Memory.ExpandMem(st.evm.memory,st.Peek(0) as nat,32),st.Peek(0) as nat,st.Peek(1)),gas:=st.Gas()-3-Gas.ExpansionSize(st.evm.memory,st.Peek(0) as nat,32)))
  {
    reveal EvmFork.CANCUN; reveal EvmFork.CANCUN_BYTECODES; reveal EvmFork.GENISIS_BYTECODES; EvmFork.EipSet(EvmFork.CANCUN_EIPS,EvmFork.GENISIS_BYTECODES);
    reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.MStore(); reveal Gas.CostExpandBytes();
  }
  lemma StoreInitial(st:ExecutingState,tail:seq<u256>)
    requires st.PC()==4 && 4<|st.evm.code.contents| && st.evm.code.contents[4]==82
    requires st.evm.fork==EvmFork.CANCUN
    requires st.evm.stack.contents==[64 as u256,128 as u256]+tail
    requires st.evm.memory.contents==Mem0()
    requires st.Gas()>=12
    ensures EVM.Execute(st)==EXECUTING(st.evm.(pc:=5,stack:=Stack.Make(tail),memory:=Memory.Memory(Mem1()),gas:=st.Gas()-12))
  {
    MemoryFacts(); reveal Memory.ExpandMem(); reveal Memory.Expand(); reveal Memory.WriteUint256();
    assert Gas.ExpansionSize(st.evm.memory,64,32)==9;
    StoreAny(st);
    Stores.Store256(Memory.ExpandMem(st.evm.memory,64,32).contents,64,128);
    PaddingSlice(96,0,64);
    assert Memory.WriteUint256(Memory.ExpandMem(st.evm.memory,64,32),64,128).contents==Mem1();
  }
  lemma StoreError(st:ExecutingState,tail:seq<u256>)
    requires st.PC()==2622 && 2622<|st.evm.code.contents| && st.evm.code.contents[2622]==82
    requires st.evm.fork==EvmFork.CANCUN
    requires st.evm.stack.contents==[128 as u256,25933226758553968569565623594072278329591374616828141097895289445724687695872 as u256]+tail
    requires st.evm.memory.contents==Mem1()
    requires st.Gas()>=9
    ensures EVM.Execute(st)==EXECUTING(st.evm.(pc:=2623,stack:=Stack.Make(tail),memory:=Memory.Memory(Mem2()),gas:=st.Gas()-9))
  {
    MemoryFacts(); reveal Memory.ExpandMem(); reveal Memory.Expand(); reveal Memory.WriteUint256();
    assert Gas.ExpansionSize(st.evm.memory,128,32)==6;
    StoreAny(st);
    Stores.Store256(Memory.ExpandMem(st.evm.memory,128,32).contents,128,25933226758553968569565623594072278329591374616828141097895289445724687695872);
    PaddingSlice(64,0,32);
    assert Memory.WriteUint256(Memory.ExpandMem(st.evm.memory,128,32),128,25933226758553968569565623594072278329591374616828141097895289445724687695872).contents==Mem2();
  }
  lemma LoadPointer(st:ExecutingState,tail:seq<u256>)
    requires st.PC()==2612 && 2612<|st.evm.code.contents| && st.evm.code.contents[2612]==81
    requires st.evm.fork==EvmFork.CANCUN
    requires st.evm.stack.contents==[64 as u256]+tail
    requires st.evm.memory.contents==Mem1()
    requires st.Gas()>=3
    ensures EVM.Execute(st)==EXECUTING(st.evm.(pc:=2613,stack:=Stack.Make([128 as u256]+tail),memory:=Memory.Memory(Mem1()),gas:=st.Gas()-3))
  {
    reveal EvmFork.CANCUN; reveal EvmFork.CANCUN_BYTECODES; reveal EvmFork.GENISIS_BYTECODES; EvmFork.EipSet(EvmFork.CANCUN_EIPS,EvmFork.GENISIS_BYTECODES);
    MemoryFacts();
    reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode();
    reveal Bytecode.MLoad(); reveal Bytecode.Revert();
    reveal Memory.ExpandMem(); reveal Memory.Expand(); reveal Gas.CostExpandBytes(); reveal Gas.CostExpandRange(); reveal Gas.ExpansionSize();
  }
  lemma LoadPointerAfter(st:ExecutingState,tail:seq<u256>)
    requires st.PC()==2628 && 2628<|st.evm.code.contents| && st.evm.code.contents[2628]==81
    requires st.evm.fork==EvmFork.CANCUN
    requires st.evm.stack.contents==[64 as u256]+tail
    requires st.evm.memory.contents==Mem2()
    requires st.Gas()>=3
    ensures EVM.Execute(st)==EXECUTING(st.evm.(pc:=2629,stack:=Stack.Make([128 as u256]+tail),memory:=Memory.Memory(Mem2()),gas:=st.Gas()-3))
  {
    reveal EvmFork.CANCUN; reveal EvmFork.CANCUN_BYTECODES; reveal EvmFork.GENISIS_BYTECODES; EvmFork.EipSet(EvmFork.CANCUN_EIPS,EvmFork.GENISIS_BYTECODES);
    MemoryFacts();
    reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode();
    reveal Bytecode.MLoad(); reveal Bytecode.Revert();
    reveal Memory.ExpandMem(); reveal Memory.Expand(); reveal Gas.CostExpandBytes(); reveal Gas.CostExpandRange(); reveal Gas.ExpansionSize();
  }
  lemma RevertError(st:ExecutingState,tail:seq<u256>)
    requires st.PC()==2633 && 2633<|st.evm.code.contents| && st.evm.code.contents[2633]==253
    requires st.evm.fork==EvmFork.CANCUN
    requires st.evm.stack.contents==[128 as u256,4 as u256]+tail
    requires st.evm.memory.contents==Mem2()
    requires st.Gas()>=0
    ensures EVM.Execute(st)==ERROR(REVERTS,gas:=st.Gas(),data:=[57,85,175,170])
  {
    reveal EvmFork.CANCUN; reveal EvmFork.CANCUN_BYTECODES; reveal EvmFork.GENISIS_BYTECODES; EvmFork.EipSet(EvmFork.CANCUN_EIPS,EvmFork.GENISIS_BYTECODES);
    MemoryFacts();
    reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode();
    reveal Bytecode.MLoad(); reveal Bytecode.Revert();
    reveal Memory.ExpandMem(); reveal Memory.Expand(); reveal Gas.CostExpandBytes(); reveal Gas.CostExpandRange(); reveal Gas.ExpansionSize();
  }
}
