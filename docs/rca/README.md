# Root-cause analysis (RCA)

User directive (2026-11-06, binding), verbatim:

> Whenever there's a bug or issue, I'd like you to do root cause analysis and reason about why it was able to occur in the first place, and then I'd like you to implement robust systems to catch them.

Earlier directive, also binding: prove as much as possible, so the project assumes only what Verus assumes (rustc, LLVM, Z3), and take no shortcuts.

## Entry format

One file per RCA, `docs/rca/<date>-<slug>.md`, or one bullet in `catalog.md` for a batch. Each entry has:

- **Defect**: what was wrong, where, and the fix commit if any.
- **Escape**: which check should have caught it and why it did not.
- **Class**: a catalog class (C1..C18), or a new one.
- **Catch**: the check that now fails on the whole class, not only on the instance.
- **Evidence**: proof that the catch fires on the original bug (a gate demo in `scripts/gate-demos.sh`, a mutant that fails, or the failing output).

## Order of preference for a catch

1. A proof obligation (an `ensures` or lemma Verus checks).
2. A verified checker.
3. A fail-closed `scripts/verify.sh` gate (missing input, empty list, or a tool that did not run is a failure).
4. A test.

A catch lower in the list needs a stated reason why a higher one is not possible yet.

## Files

- `catalog.md`: root causes of every bug found by review so far, the 18 classes with their catches and owners.
- `2026-11-06-empty-crypto.md`: first RCA entry.
- Tools: `tools/check_quotes.py`, `tools/rl.py`, `tools/mut.py`, `tools/mutants.py`; gates: `scripts/lint-scripts.sh`, `scripts/check-quotes.sh`, `scripts/escape-gate.sh`, `scripts/acceptance.sh`, `scripts/rlimit-gate.sh`, `scripts/rlimit-ceilings.sh`, `scripts/mutants.sh`, `scripts/gate-demos.sh`.
- Mutant registry (C6): `tools/mutants.tsv` and `tools/mutants/<id>.patch`. A mutation that a review or plan runs by hand is added as a row (id, crate, module, the fn whose verification it must break, tests that must fail, the expected-failure regex, origin) with its `git diff` as the patch, so it is re-run mechanically instead of once.

## Before merging a branch

On main, every commit at main's tip (a merge, a fast-forward or a squash) must carry a `tools/mutants-last-run.txt` written for exactly its tree: `scripts/verify.sh` fails unless the file names this commit's `crates/` tree and its `tree` hash (crates/ plus the root Cargo.toml, Cargo.lock and rust-toolchain.toml), the committed tsv's blob, and every registry id as `pass` with its patch's blob. On a branch verify.sh runs only `scripts/mutants.sh check`: every patch still applies, with no line offset, and every `allowed_*err`/`*_allowed_err` spec fn under crates/ is named by some row. So the last steps on a branch are:

1. Merge main into the branch, so the merge into main changes nothing.
2. Run `scripts/mutants.sh run` after the last commit that touches crates/ or the root Cargo files. It applies each patch alone in a throwaway git worktree and needs every mutant killed; rlimit is not a kill.
3. Commit `tools/mutants-last-run.txt`.
4. `git merge --no-ff` the branch into main. The merge commit's tree equals the branch tip's when main has no new changes, so the run file holds.

If a change to crates/ makes a patch stop applying, or apply only at an offset, regenerate it: `git apply` what still applies, redo the edit, `git diff > tools/mutants/<id>.patch`. Then re-run.

Trust boundary (accepted): the run file is plain text. Nothing ties a `pass` line to an actual run except the run's own log (keep it in the branch's evidence). The gate catches a stale or partial file, not a forged one.
