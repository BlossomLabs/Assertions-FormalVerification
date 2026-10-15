// SPDX-License-Identifier: MIT
include "../../../bridges/next-three/Models.dfy"
module NextThreeAddressClaims {
  import opened NextThreeSourceModels

  lemma E21(kind: CallKind, length: nat, word: nat, index: nat)
    requires word < WordLimit && index < WordLimit
    requires word >= AddressLimit
    ensures CallTargetSource(kind, length, word, index) == InvalidNode(index)
  {}

  lemma ExactAddressGuard(kind: CallKind, length: nat, word: nat, index: nat)
    requires word < WordLimit && index < WordLimit
    ensures CallTargetSource(kind, length, word, index).InvalidNode? <==>
            length != 32 || word >= AddressLimit
    ensures CallTargetSource(kind, length, word, index).InvalidNode? ==>
              CallTargetSource(kind, length, word, index).index == index
  {}

  lemma CleanTarget(kind: CallKind, word: nat, index: nat)
    requires word < AddressLimit && index < WordLimit
    ensures CallTargetSource(kind, 32, word, index) == Addressed(word)
  {}
}
