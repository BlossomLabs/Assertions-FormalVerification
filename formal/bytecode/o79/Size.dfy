// SPDX-License-Identifier: MIT
module O79Bytecode {
  function Eip170Limit(): nat { 24576 }
  function RuntimeLength(): nat { 20894 }

  lemma FitsEip170(code: seq<bv8>)
    requires |code| == RuntimeLength()
    ensures |code| <= Eip170Limit()
    ensures Eip170Limit() - |code| == 3682
  {}
}
