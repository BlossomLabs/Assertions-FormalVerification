// SPDX-License-Identifier: MIT
include "../../../bridges/next-three/Models.dfy"
module NextThreeZeroDenominatorClaims {
  import opened NextThreeSourceModels

  lemma MagnitudesAreTotal(value: int)
    requires -SignedLimit <= value < SignedLimit
    ensures 0 <= MagnitudeSource(value) <= SignedLimit < WordLimit
    ensures value < 0 ==> 0 <= -(value + 1) < SignedLimit
    ensures MagnitudeSource(value) == (if value < 0 then -value else value)
  {}

  lemma MathZeroDenominator(high: nat, low: nat)
    requires high < WordLimit && low < WordLimit
    ensures MathMulDivPrefix(high, low, 0) == Panic(18)
  {}

  lemma O9Unsigned(a: nat, b: nat, high: nat, low: nat, rounding: nat)
    requires a < WordLimit && b < WordLimit
    requires high < WordLimit && low < WordLimit && rounding < 3
    ensures UnsignedMulDivSource(a, b, high, low, 0, rounding) == Panic(18)
  {}

  lemma O9Signed(a: int, b: int, high: nat, low: nat, rounding: nat)
    requires -SignedLimit <= a < SignedLimit && -SignedLimit <= b < SignedLimit
    requires high < WordLimit && low < WordLimit && rounding < 3
    ensures SignedMulDivSource(a, b, high, low, 0, rounding) == Panic(18)
  {}
}
