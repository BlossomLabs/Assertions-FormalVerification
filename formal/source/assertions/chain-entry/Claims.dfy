// SPDX-License-Identifier: MIT
include "../../../bridges/next-three/Models.dfy"
module NextThreeChainClaims {
  import opened NextThreeSourceModels

  lemma C50<T>(start: T)
    ensures ChainEntry(start, 0) == EmptyCallChain
  {}

  lemma StartIndependence<A, B>(first: A, second: B, length: nat)
    ensures ChainEntry(first, length) == ChainEntry(second, length)
  {}

  lemma Nonempty<T>(start: T, length: nat)
    requires length > 0
    ensures ChainEntry(start, length) == Continue
  {}
}
