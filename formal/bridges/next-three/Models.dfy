// SPDX-License-Identifier: MIT
// Restricted source-prefix equations. The source gate binds every retained
// branch and call site; these equations do not model later execution.
module NextThreeSourceModels {
  const WordLimit: nat := 115792089237316195423570985008687907853269984665640564039457584007913129639936
  const SignedLimit: int := 57896044618658097711785492504343953926634992332820282019728792003956564819968
  const AddressLimit: nat := 1461501637330902918203684832716283019655932542976

  datatype Outcome = Continue | EmptyCallChain | InvalidNode(index: nat) | Addressed(address: nat) | Panic(code: nat)
  datatype CallKind = Call | ProbeCall

  function ChainEntry<T>(start: T, callsLength: nat): Outcome {
    if callsLength == 0 then EmptyCallChain else Continue
  }

  function AddressSource(length: nat, loadedWord: nat, index: nat): Outcome
    requires loadedWord < WordLimit
  {
    if length != 32 || loadedWord > AddressLimit - 1 then InvalidNode(index)
    else Addressed(loadedWord % AddressLimit)
  }

  function CallTargetSource(kind: CallKind, length: nat, loadedWord: nat, index: nat): Outcome
    requires loadedWord < WordLimit
  {
    match kind
    case Call => AddressSource(length, loadedWord, index)
    case ProbeCall => AddressSource(length, loadedWord, index)
  }

  function MagnitudeSource(value: int): nat
    requires -SignedLimit <= value < SignedLimit
  {
    if value < 0 then -(value + 1) + 1 else value
  }

  function MathMulDivPrefix(high: nat, low: nat, denominator: nat): Outcome
    requires high < WordLimit && low < WordLimit && denominator < WordLimit
  {
    if high == 0 then
      if denominator == 0 then Panic(18) else Continue
    else if denominator <= high then
      Panic(if denominator == 0 then 18 else 17)
    else Continue
  }

  function UnsignedMulDivSource(a: nat, b: nat, high: nat, low: nat, denominator: nat, rounding: nat): Outcome
    requires a < WordLimit && b < WordLimit
    requires high < WordLimit && low < WordLimit && denominator < WordLimit
    requires rounding < 3
  {
    MathMulDivPrefix(high, low, denominator)
  }

  function SignedMulDivSource(a: int, b: int, high: nat, low: nat, denominator: int, rounding: nat): Outcome
    requires -SignedLimit <= a < SignedLimit && -SignedLimit <= b < SignedLimit
    requires -SignedLimit <= denominator < SignedLimit
    requires high < WordLimit && low < WordLimit && rounding < 3
  {
    var x := MagnitudeSource(a);
    var y := MagnitudeSource(b);
    var d := MagnitudeSource(denominator);
    MathMulDivPrefix(high, low, d)
  }
}
