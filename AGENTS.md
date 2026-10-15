# Verification repository

Claims live in claims.json; the root CLAIMS.md is a tracked, generated index.
Run tools/render.py after editing claims.json; CI regenerates it on every run
and commits changes on branch pushes. Never edit CLAIMS.md by hand. project.json
binds the production revision and complete accepted Halmos source/configuration
snapshot, including explicit package and contract versions. Run
tools/check_project.py to identify that target; --source compares local contracts
without requiring an Assertions checkout to pin this repository's commit.
All symbolic harnesses live under halmos/contracts/tests, including
their concrete companion tests. tools/prepare.py installs them in a fresh source
checkout; never overwrite or clean another session's checkout.

formal/ contains only accepted claim-supporting packages and complete dependencies.
Restore tools with formal/tools/bootstrap_evm.py --fetch, prepare the pinned
Assertions workspace and install its dependencies, then run
formal/tools/generate.py before check.py. Expanded bytecode proofs are ignored.
formal/generators contains the frozen recipes, concrete discovery inputs and
accepted output hashes. Regeneration must reproduce every accepted byte; never
update acceptance hashes to accommodate a generator difference. Preserve the
original receipts. Generation is not a new native verification run.
Preserve theorem bodies and declared native verification policies. Native passes,
source implication and exact-runtime acceptance are separate. Do not reprove O13
or O14 merely because the repository has moved.

Raw evidence and tools stay ignored or in CI artifacts. Original receipts are
immutable; imported evidence is not fresh acceptance. Keep statement identities,
scope, source hashes, tool versions and failed/incomplete results. Retain the old
archive before pruning. Kontrol credit is limited to its nine accepted finite-gas
cases; unfinished backend investigations grant no extra credit. O2 has accepted
public-entry bytecode proofs for arbitrary unsigned dividends and divisors;
its previous incomplete native attempt is retained without proof credit.
