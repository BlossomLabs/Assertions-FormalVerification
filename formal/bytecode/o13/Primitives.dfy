// SPDX-License-Identifier: MIT
include "../o12/Primitives.dfy"
module O13Primitives {
  import opened Int
  import opened EvmState
  import Base = O12Primitives
  import Old = C50Steps
  import EVM
  import Bytecode
  import EvmFork
  import Stack
  import Word
  function Abs(v:int):nat { if v<0 then -v else v }
  function Signed(w:u256):int { Word.asI256(w) as int }
  function Mag(w:u256):u256 { Abs(Signed(w)) as u256 }
  function Neg(w:u256):u256 { ((-(w as int))%TWO_256) as u256 }
  opaque function Rem(mul:bool,a:u256,b:u256,m:u256):u256 {
    if m==0 then 0 else (Abs(if mul then Signed(a)*Signed(b) else Signed(a)+Signed(b))%(Mag(m) as int)) as u256
  }
  opaque function Value(mul:bool,a:u256,b:u256,m:u256):u256 {
    var v:=if mul then Signed(a)*Signed(b) else Signed(a)+Signed(b);
    var r:=if m==0 then 0 else Abs(v)%(Mag(m) as int);
    ((if v<0 then -r else r)%TWO_256) as u256
  }
  lemma Magnitude(w:u256)
    ensures 0<=Mag(w) as int<=TWO_255
    ensures Mag(w)==(if w as int<TWO_255 then w else (TWO_256-w as int) as u256)
    ensures (Mag(w)==0)<==>(w==0)
    ensures (Signed(w)<0)<==>(w as int>=TWO_255)
  { }
  lemma RemBounds(mul:bool,a:u256,b:u256,m:u256)
    ensures Rem(mul,a,b,m) as int<TWO_255
    ensures m>0 ==> Rem(mul,a,b,m)<Mag(m)
  { Magnitude(m); reveal Rem(); }
  lemma Remainder(mul:bool,a:u256,b:u256,m:u256)
    requires m>0
    ensures mul ==> Rem(mul,a,b,m)==Base.Value(true,Mag(a),Mag(b),Mag(m))
    ensures !mul && (Signed(a)<0)==(Signed(b)<0) ==> Rem(mul,a,b,m)==Base.Value(false,Mag(a),Mag(b),Mag(m))
    ensures !mul && (Signed(a)<0)!=(Signed(b)<0) && Mag(a)>=Mag(b) ==> Rem(mul,a,b,m)==((Mag(a) as int-Mag(b) as int)%(Mag(m) as int)) as u256
    ensures !mul && (Signed(a)<0)!=(Signed(b)<0) && Mag(a)<Mag(b) ==> Rem(mul,a,b,m)==((Mag(b) as int-Mag(a) as int)%(Mag(m) as int)) as u256
  {
    Magnitude(a); Magnitude(b); Magnitude(m); reveal Rem();
    Base.ValueEquation(mul,Mag(a),Mag(b),Mag(m));
  }
  lemma Restore(mul:bool,a:u256,b:u256,m:u256)
    ensures mul ==> Value(mul,a,b,m)==(if (Signed(a)<0)!=(Signed(b)<0) then Neg(Rem(mul,a,b,m)) else Rem(mul,a,b,m))
    ensures !mul && (Signed(a)<0)==(Signed(b)<0) ==> Value(mul,a,b,m)==(if Signed(a)<0 then Neg(Rem(mul,a,b,m)) else Rem(mul,a,b,m))
    ensures !mul && (Signed(a)<0)!=(Signed(b)<0) && Mag(a)>=Mag(b) ==> Value(mul,a,b,m)==(if Signed(a)<0 then Neg(Rem(mul,a,b,m)) else Rem(mul,a,b,m))
    ensures !mul && (Signed(a)<0)!=(Signed(b)<0) && Mag(a)<Mag(b) ==> Value(mul,a,b,m)==(if Signed(b)<0 then Neg(Rem(mul,a,b,m)) else Rem(mul,a,b,m))
  {
    Magnitude(a); Magnitude(b); Magnitude(m); reveal Rem(); reveal Value();
  }
  predicate Safe(st:ExecutingState,op:u8) {
    if Old.Supported(op) || op in {8,9} then Base.Safe(st,op) else
    op in {6,136,137} && st.PC()<|st.evm.code.contents| && st.evm.code.contents[st.PC()]==op &&
    st.evm.fork==EvmFork.CANCUN && st.Gas()>=(if op==6 then 5 else 3) &&
    st.Operands()>=(if op==6 then 2 else (op as nat)-0x80+1) && (op==6 || st.Capacity()>=1)
  }
  function Next(st:ExecutingState,op:u8):ExecutingState
    requires Safe(st,op)
  {
    if Old.Supported(op) || op in {8,9} then Base.Next(st,op) else
    var xs:=st.evm.stack.contents;
    EXECUTING(st.evm.(pc:=st.PC()+1,gas:=st.Gas()-(if op==6 then 5 else 3),
              stack:=Stack.Make(if op==6 then [if xs[1]==0 then 0 as u256 else (xs[0]%xs[1]) as u256]+xs[2..] else [xs[(op as nat)-0x80]]+xs)))
  }
  lemma Pure(st:ExecutingState,op:u8)
    requires Safe(st,op)
    ensures EVM.Execute(st)==Next(st,op)
  {
    if Old.Supported(op) || op in {8,9} { Base.Pure(st,op); }
    else {
      reveal EvmFork.CANCUN; reveal EvmFork.CANCUN_BYTECODES; reveal EvmFork.GENISIS_BYTECODES;
      EvmFork.EipSet(EvmFork.CANCUN_EIPS,EvmFork.GENISIS_BYTECODES);
      reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode();
      reveal Bytecode.Mod(); reveal Bytecode.Dup();
    }
  }
}
