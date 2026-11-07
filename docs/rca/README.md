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

`scripts/mutants.sh run` is the last step on a branch before merging, after the last commit that touches `crates/`. It applies each patch alone in a throwaway git worktree, needs every mutant killed (rlimit is not a kill), and writes `tools/mutants-last-run.txt`; commit that file. On main at the merge commit, `scripts/verify.sh` fails unless the file names the merged branch's `crates/` tree (`HEAD^2:crates`) with every registry id passing. On a branch verify.sh runs only `scripts/mutants.sh check` (every patch still applies). If a change to `crates/` makes a patch stop applying, regenerate it (`git apply` what still applies, redo the edit, `git diff > tools/mutants/<id>.patch`) and re-run.
- `2026-11-06-acceptance-parser.md`: RCA of the R4 parser's own bugs.
- `2026-11-06-phase-9a-night.md`: RCAs of the bugs Phase 9a found on 2026-11-06, plus the open CRYPTO span item.
- `2026-11-07-audit.md`: the 2026-11-07 repo audit (tests not gated; reviewed fixes left off main).
