// SPDX-License-Identifier: MIT
include "../c50/Steps.dfy"
module O12Primitives {
  import opened Int
  import opened EvmState
  import Old = C50Steps
  import Stores = C50Stores
  import EVM
  import Bytecode
  import EvmFork
  import Code
  import Stack
  import Memory
  import Gas
  import U256
  import ByteUtils
  import Arrays
  opaque function Value(mul:bool,a:u256,b:u256,m:u256):u256 {
    if m==0 then 0 else ((if mul then a as int*b as int else a as int+b as int)%(m as int)) as u256
  }
  lemma ValueEquation(mul:bool,a:u256,b:u256,m:u256)
    ensures Value(mul,a,b,m)==(if m==0 then 0 else ((if mul then a as int*b as int else a as int+b as int)%(m as int)) as u256)
  { reveal Value(); }
  predicate Safe(st:ExecutingState,op:u8) {
    if Old.Supported(op) then Old.Safe(st,op) else
    op in {8,9} && st.PC()<|st.evm.code.contents| && st.evm.code.contents[st.PC()]==op &&
    st.evm.fork==EvmFork.CANCUN && st.Gas()>=8 && st.Operands()>=3
  }
  function Next(st:ExecutingState,op:u8):ExecutingState
    requires Safe(st,op)
  {
    if Old.Supported(op) then Old.Next(st,op) else
    EXECUTING(st.evm.(pc:=st.PC()+1,gas:=st.Gas()-8,
              stack:=Stack.Make([Value(op==9,st.Peek(0),st.Peek(1),st.Peek(2))]+st.evm.stack.contents[3..])))
  }
  lemma Pure(st:ExecutingState,op:u8)
    requires Safe(st,op)
    ensures EVM.Execute(st)==Next(st,op)
  {
    if Old.Supported(op) { Old.Pure(st,op); }
    else {
      reveal EvmFork.CANCUN; reveal EvmFork.CANCUN_BYTECODES; reveal EvmFork.GENISIS_BYTECODES;
      EvmFork.EipSet(EvmFork.CANCUN_EIPS,EvmFork.GENISIS_BYTECODES);
      reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode();
      reveal Bytecode.AddMod(); reveal Bytecode.MulMod(); reveal Value();
    }
  }
  function Mem0():seq<u8> { [] }
  function Mem1():seq<u8> { Old.Mem1() }
  opaque function Panic1():seq<u8> { U256.ToBytes(0x4e487b7100000000000000000000000000000000000000000000000000000000)+Mem1()[32..] }
  opaque function Panic2():seq<u8> { reveal Panic1(); Panic1()[..4]+U256.ToBytes(18)+Panic1()[36..] }
  opaque function ResultMem(v:u256):seq<u8> { Mem1()+ByteUtils.Padding(32)+U256.ToBytes(v) }
  function PanicData():seq<u8> { [78,72,123,113]+U256.ToBytes(18) }
  lemma Facts(v:u256)
    ensures |Mem1()|==96 && |Panic1()|==96 && |Panic2()|==96 && |ResultMem(v)|==160
    ensures Memory.ReadUint256(Memory.Memory(Mem1()),64)==128
    ensures Memory.ReadUint256(Memory.Memory(ResultMem(v)),64)==128
    ensures Panic2()[..36]==PanicData()
    ensures ResultMem(v)[128..160]==U256.ToBytes(v)
  {
    reveal Panic1(); reveal Panic2(); reveal ResultMem(); Old.MemoryFacts();
    assert U256.ToBytes(0x4e487b7100000000000000000000000000000000000000000000000000000000)[..4]==[78 as u8,72,123,113];
    assert ResultMem(v)[64..96]==U256.ToBytes(128);
    U256.BytesValue(128); ByteUtils.FullWordValue(ResultMem(v),64);
  }
  lemma Store(st:ExecutingState,a:nat,v:u256,mem:seq<u8>,out:seq<u8>,cost:nat)
    requires st.PC()<|st.evm.code.contents| && st.evm.code.contents[st.PC()]==0x52
    requires st.evm.fork==EvmFork.CANCUN && st.Operands()>=2
    requires st.Peek(0) as nat==a && st.Peek(1)==v && st.evm.memory.contents==mem
    requires cost==3+Gas.ExpansionSize(st.evm.memory,a,32) && st.Gas()>=cost
    requires out==Memory.ExpandMem(st.evm.memory,a,32).contents[..a]+U256.ToBytes(v)+Memory.ExpandMem(st.evm.memory,a,32).contents[a+32..]
    ensures EVM.Execute(st)==EXECUTING(st.evm.(pc:=st.PC()+1,gas:=st.Gas()-cost,stack:=Stack.Make(st.evm.stack.contents[2..]),memory:=Memory.Memory(out)))
  {
    Old.StoreAny(st); reveal Memory.WriteUint256();
    Stores.Store256(Memory.ExpandMem(st.evm.memory,a,32).contents,a,v);
  }
  lemma Load(st:ExecutingState,v:u256)
    requires st.PC()<|st.evm.code.contents| && st.evm.code.contents[st.PC()]==0x51
    requires st.evm.fork==EvmFork.CANCUN && st.Operands()>=1 && st.Peek(0)==64
    requires st.evm.memory.contents==Mem1() || st.evm.memory.contents==ResultMem(v)
    requires st.Gas()>=3
    ensures EVM.Execute(st)==EXECUTING(st.evm.(pc:=st.PC()+1,gas:=st.Gas()-3,stack:=Stack.Make([128 as u256]+st.evm.stack.contents[1..])))
  {
    Facts(v); reveal EvmFork.CANCUN; reveal EvmFork.CANCUN_BYTECODES; reveal EvmFork.GENISIS_BYTECODES;
    EvmFork.EipSet(EvmFork.CANCUN_EIPS,EvmFork.GENISIS_BYTECODES);
    reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.MLoad();
    reveal Gas.CostExpandBytes(); reveal Gas.ExpansionSize(); reveal Memory.ExpandMem(); reveal Memory.Expand();
  }
  lemma Exit(st:ExecutingState,v:u256,reverts:bool)
    requires st.PC()<|st.evm.code.contents| && st.evm.code.contents[st.PC()]==(if reverts then 0xfd else 0xf3)
    requires st.evm.fork==EvmFork.CANCUN && st.Operands()>=2
    requires st.Peek(0)==(if reverts then 0 else 128) && st.Peek(1)==(if reverts then 36 else 32)
    requires st.evm.memory.contents==(if reverts then Panic2() else ResultMem(v))
    ensures EVM.Execute(st)==(if reverts then ERROR(REVERTS,gas:=st.Gas(),data:=PanicData()) else
                              RETURNS(st.Gas(),U256.ToBytes(v),st.evm.world,st.evm.transient,st.evm.substate))
  {
    Facts(v); reveal EvmFork.CANCUN; reveal EvmFork.CANCUN_BYTECODES; reveal EvmFork.GENISIS_BYTECODES;
    EvmFork.EipSet(EvmFork.CANCUN_EIPS,EvmFork.GENISIS_BYTECODES);
    reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.Return(); reveal Bytecode.Revert();
    reveal Memory.Slice(); reveal Arrays.SliceAndPad(); reveal Memory.ExpandMem(); reveal Memory.Expand();
    reveal Gas.CostExpandRange(); reveal Gas.ExpansionSize();
  }
}
