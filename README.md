# Assertions Formal Verification

This repository owns the public claims, Halmos harnesses, claim-specific Dafny
proofs and verification tooling for Assertions. [project.json](project.json)
identifies the validated contract versions, Assertions revision and every
source/configuration input that ran.
[CLAIMS.md](CLAIMS.md) is the readable claim index at the repository root.
[claims.json](claims.json) retains the precise wording, classification, scope
and named theorems. `python3 tools/render.py` regenerates the tracked index
without requiring installed proof tools. CI regenerates it on every run and
commits updates on branch pushes, including every change to `claims.json`.
Tracked theorems link to their source; generated theorems link to their declarations
and accepted hashes, with full sources in the CI artifacts.

The validated target is Assertions package **2.0.0**, with Assertions,
Operations, Collections and Expressions each at contract version **2.0**, from
[source commit b6c7bc28](https://github.com/blossomlabs/assertions/tree/b6c7bc282fd6cea97c62017f468c7ecfd6dc37aa).
Source and exact-runtime hashes further identify the inputs for each result.
Assertions builds independently; verification tracks the contracts it validates.

The selected library supports C50, O2, O12, O13, O14 and O79 through reviewed
bytecode/artifact results, and O9, E21 and C50 through reviewed source mappings.
O14 follows from O13 without an additional native run. The Halmos baseline has
382 passing properties. C69 has nine separately accepted finite-gas Kontrol
results; its broader propagation guarantee remains partially verified.

CI regenerates proof sources and the claim index, and checks package/source bindings. The manual
verification workflow accepts an exact candidate Assertions commit, executes the
concrete and Halmos suites, and optionally reproduces a native package. Runs and
generated artifacts are available in [GitHub Actions](https://github.com/BlossomLabs/Assertions-FormalVerification/actions).

Every result has its stated ABI, resource, observer and execution premises.
The size theorem is a static artifact property. Neither counts nor native
verification alone establish unrestricted contract correctness.

## Reproduce

Inspect the validated target or compare local contract versions and source hashes:

```sh
python3 tools/check_project.py
python3 tools/check_project.py --source ../assertions
```

Create a clean workspace from the pinned Assertions commit. All 62 symbolic
harnesses and their concrete companion tests are installed at their original
paths so existing imports and the frozen runner remain unchanged:

```sh
python3 tools/prepare.py --source ../assertions --output workspace
cd workspace
pnpm install --frozen-lockfile
pnpm test
forge test
python3 scripts/verify-claims.py --output docs/verification/fresh
cd ..
```

`--candidate <exact-commit>` tests a new Assertions revision. That creates fresh
regression evidence; it does not carry the old source/runtime acceptance forward.
Use the candidate mode for changes before updating the pin and reviewed results.

For the selected Dafny packages, using the pinned workspace prepared above:

```sh
python3 formal/tools/bootstrap_evm.py --fetch
python3 formal/tools/generate.py --project workspace
python3 formal/tools/check.py
python3 tools/render.py
python3 formal/tools/verify.py o13-current-bytecode --output evidence/fresh-o13 --run
```

Without `--run`, the runner prints its exact native plan. It preserves each
package's core count and per-obligation time limit, verifies the entire import
closure, audits for admissions and checks formatting. Fresh native results
remain separate from claim implication and exact-runtime acceptance.

The 33 expanded bytecode proof files are ignored outputs.
[formal/generators](formal/generators/README.md) contains the frozen generators,
small concrete input recipes and final proof repair. Generation recompiles the
pinned Solidity sources, replays the discovery traces and checks every expanded
file against its original accepted hash. It requires no historical worktree or
raw evidence archive. CI publishes the expanded theorem sources and readable
claim index together as an artifact. Keep the arithmetic specifications, source
guards and shared instruction lemmas as tracked sources.

## Evidence and maintenance

[evidence-index.json](evidence-index.json) records the hashes and scope of the
original accepted receipts. Raw logs, snapshots, compiler outputs, solver tools
and old report exports remain ignored under `evidence/` or in CI artifacts.
The imported local archive is byte-for-byte preserved; relocation is not a new
verification run. Archive paths in receipts retain their original provenance.
The original handwritten claim-specific acceptance gates are preserved under
`review-gates/`. They retain their frozen-workspace assumptions; the smaller
native reproduction runner does not replace their implication/runtime review.

The finite-gas Kontrol generators/auditors are under `kontrol/`; their original
engine, runtime and context bindings are in the imported packet. They establish
the listed finite guard/call cases, not symbolic gas intervals or a whole-C69
theorem. The unfinished backend-source research is not adopted. O2's accepted
unsigned division/remainder result and its earlier incomplete native attempt
are recorded separately in `evidence-index.json`.

An ID names one statement. Do not reuse retired IDs, rewrite receipts, promote a
bounded scope to a whole claim, or transfer an old result across changed inputs.
New native, compiler/runtime and implication reviews remain separate gates.
