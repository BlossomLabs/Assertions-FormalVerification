# O2: unsigned division and remainder

`FullDiv` and `FullMod` start at PC 0 of the exact pinned Operations runtime.
For arbitrary uint256 dividend and divisor words, a nonzero divisor returns the
mathematical unsigned quotient/remainder. A zero divisor reverts with exactly
`4e487b71 || uint256(0x12)`. `WordResult` states the integer arithmetic equation;
`RunMatchesKernel` connects the composed proof to the pinned DafnyEVM interpreter.

The premises are Cancun, zero call value, empty initial stack and memory, the
selected selector, calldata length 68 through 2^255+3 inclusive with arbitrary
trailing bytes, and at least 483 execution gas for `div` or 526 for `mod`.
Transaction intrinsic gas is outside this frame theorem.

The accepted complete 25-input native closure passed 28,189 verification batches,
audit and formatting. Independent acceptance recompiled the complete runtime
and rebuilt the interpreter snapshot, reproducing 106 concrete cases and three
byte mutants. Three native faults and ten acceptance-reader faults were rejected.
The earlier native attempt timed out on three shared C50 obligations; it is
retained as incomplete and grants no credit.

From the verification repository root, after preparing the pinned workspace:

```sh
python3 formal/tools/generate.py --project workspace
python3 formal/tools/check.py
python3 formal/tools/verify.py o2-current-bytecode --output evidence/fresh-o2 --run
```

`Entry.dfy` is an ignored expansion of the frozen producer in
`formal/generators/o2/`; regeneration must match its accepted hash exactly.
`Primitives.dfy` and `runtime-binding.json` remain pinned sources and metadata.
`claims.json` links the four named theorems; `evidence-index.json` binds the
immutable acceptance and supporting receipts. Original acceptance gates are
preserved in `review-gates/`, with their original frozen-workspace requirements.
Fresh native verification remains separate from fresh runtime/claim acceptance.
