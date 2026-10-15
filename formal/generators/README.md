# Bytecode proof generation

`python3 formal/tools/generate.py --project workspace` reproduces 33 expanded
Dafny files at their original `formal/bytecode/` paths. `--output DIRECTORY`
exports the same repository-shaped tree elsewhere. `--check` validates the
recipe and existing outputs without rebuilding them.

The project checkout must contain the pinned production sources, shared test
fixtures and installed OpenZeppelin dependency. Prepare it with `tools/prepare.py`
and install its dependencies with `pnpm install --frozen-lockfile`. Restore the
checksummed compiler, formatter and Python EVM using `bootstrap_evm.py --fetch`.

The recipe recompiles the two runtime artifacts using the original compiler
settings, checks their accepted hashes, and recreates the discovery traces from
the 36 concrete inputs in `cases.json`. Those trace hashes pin the original
generator inputs; concrete paths are generation aids, not universal proofs.
No expanded trace, bytecode artifact or historical checkout is a tracked input.

The seven campaign generator scripts are frozen copies of the original C50,
O2, O12 and O13 producers. They execute only in a temporary repository layout.
O13 additionally needs the pinned formatter before its final explicit-state
pass, removal of redundant entry composition assertions, and `o13/repairs.patch`
for the accepted negation helper. These steps preserve the accepted theorem
bodies, including the final proof repairs.

`manifest.json` binds the recipes and runner. `outputs.json` binds every expansion
to the unchanged package closure hashes. Generation refuses modified existing
outputs and installs results only after all 33 files match. The complete native
verification, runtime binding and implication reviews remain separate gates.
Original acceptance receipts are immutable. A regeneration mismatch is an error;
changing an output hash would require a separately reviewed proof-source change.
