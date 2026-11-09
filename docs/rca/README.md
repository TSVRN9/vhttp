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

## What the RFC-quantity gate guarantees (C8)

`scripts/rfc-quantity.sh` (tools/rfc_quantity.py) flags every bookkeeping read (a struct field, a non-vstd method, a name outside a call argument) in an `allowed_*err` predicate and the spec fns it reaches, unless a cited vouch covers it, and it forces a re-review of every vouch for a predicate whenever any text those vouches rest on changes: the predicate, the fns it reaches or calls (transitively), its pinned fns and the constants they name are pinned by a per-predicate sha256. The hash does not cover: exec ensures that pass a predicate its arguments beyond the pinned fns (`on_crypto`, `RecvStream::on_data`, `data_gate`; the rest is the refinement proof's job), the callees of pinned fns, re-exports (`pub use .. as`) in files that hold no hashed text, and constants named only by other constants (parked by ruling, 9r2 T4 re-review 2 R1-R3). It does not check meaning. Whether a vouch's reason is true is the reviewer's to judge, and the semantic catches are the proofs, rule 1c's non-vacuity lemmas and rule 1d's registered re-anchoring mutants (tools/mutants.tsv). That boundary is the ruling (9r2 T4): a residual of the same class past it is parked for those catches, not fixed by widening the gate.

## Files

- `catalog.md`: root causes of every bug found by review so far, the 18 classes with their catches and owners.
- `2026-11-06-empty-crypto.md`: first RCA entry.
- `2026-11-06-acceptance-parser.md`: RCA of the R4 parser's own bugs; the baseline history walk (closed, 9r2 R5).
- `2026-11-06-phase-9a-night.md`: RCAs of the bugs Phase 9a found on 2026-11-06, plus the open CRYPTO span item.
- `2026-11-07-audit.md`: the 2026-11-07 repo audit (tests not gated; reviewed fixes left off main).
- `2026-11-07-grep-exit-2.md`: a missing crypto report passed ct-check's reject check (grep exit 2 read as no match); grep_hits and the lint rule.
- `2026-11-09-audit.md`: RCAs of the 2026-11-09 audit's findings fixed in Phase 9r3 (F5: a green run names its commit and its Verus; F17; F13: interop in verify.sh and a shrink-proof test floor).
- Tools: `tools/check_quotes.py`, `tools/citations.py`, `tools/rfc_quantity.py`, `tools/ratchet_walk.py`, `tools/rl.py`, `tools/verus-pin.txt`, `tools/test-floor.txt`, `tools/mut.py`, `tools/mutants.py`; gates: `scripts/lint-scripts.sh`, `scripts/clean-tree.sh`, `scripts/check-quotes.sh`, `scripts/escape-gate.sh`, `scripts/acceptance.sh`, `scripts/rfc-quantity.sh`, `scripts/rlimit-gate.sh`, `scripts/rlimit-ceilings.sh`, `scripts/declassify-gate.sh`, `scripts/deps-gate.sh` (with `tools/deps-allow.txt`), `scripts/test-gate.sh`, `scripts/test-floor.sh`, `scripts/interop.sh`, `scripts/ct-report.sh`, `scripts/ct-lib.sh`, `scripts/mutants.sh`, `scripts/gate-demos.sh`.
- Mutant registry (C6): `tools/mutants.tsv` and `tools/mutants/<id>.patch`. A mutation that a review or plan runs by hand is added as a row (id, crate, module, the fn whose verification it must break, tests that must fail, the expected-failure regex, origin) with its `git diff` as the patch, so it is re-run mechanically instead of once.

## The ratchet files and the history walk (R5)

`tools/acceptance-baseline.txt`, `tools/rlimit-ceilings.txt` and `tools/rfc-quantity-open.txt` only shrink; `tools/test-floor.txt` only grows (`scripts/test-floor.sh`, `ratchet_walk.py` floors mode: the floor is each crate's highest value in history and a line once present stays). On a branch each is compared with the merge-base's copy. On main `tools/ratchet_walk.py` walks the first-parent history from the commit that introduced the file: the floor is the keys present in every copy, each at its lowest value, and HEAD's copy and the working tree must lie within it. Growth that was shrunk back before HEAD passes (a fast-forwarded WIP commit, a reverted mistake); growth that persists, or a shrink followed by a re-grow, fails. A git error or a shallow clone fails.

There is no reset. Open item: a toolchain upgrade that raises measured rlimits cannot land on main while the ceilings floor holds; design the upgrade path in the phase that upgrades the toolchain.

## Before merging a branch

On main, every commit at main's tip (merges to main are `--no-ff` only; anything else that lands there is gated the same) must carry a `tools/mutants-last-run.txt` written for exactly its tree: `scripts/verify.sh` fails unless the file names this commit's `crates/` tree and its `tree` hash (crates/ plus the root Cargo.toml, Cargo.lock and rust-toolchain.toml), the committed tsv's blob, and every registry id as `pass` with its patch's blob. On a branch verify.sh runs `scripts/mutants.sh check` (every patch still applies, with no line offset, and every `allowed_*err`/`*_allowed_err` spec fn under crates/ is named by some row) and, once crates/, the root Cargo files or the registry differ from the merge-base's, the same run-file gate (`python3 -I tools/mutants.py gate-branch .`), so a stale run file shows before the merge; while they equal the merge-base's no run file is demanded. So the last steps on a branch are:

1. Merge main into the branch, so the merge into main changes nothing.
2. Run `scripts/mutants.sh run` after the last commit that touches crates/, the root Cargo files, `tools/mutants.tsv` or a patch. It applies each patch alone in a throwaway git worktree and needs every mutant killed; rlimit is not a kill.
3. Commit `tools/mutants-last-run.txt`.
4. On the clean branch tip, `python3 -I tools/mutants.py gate .` must pass.
5. `git merge --no-ff` the branch into main. The merge commit's tree equals the branch tip's when main has no new changes, so the run file holds.
6. Run `scripts/verify.sh` on main after the merge: it is the only run of the main gate and of the three history walks.

If a change to crates/ makes a patch stop applying, or apply only at an offset, regenerate it: `git apply` what still applies, redo the edit, `git diff > tools/mutants/<id>.patch`. Then re-run.

Trust boundary (accepted): the run file is plain text. Nothing ties a `pass` line to an actual run except the run's own log (keep it in the branch's evidence). The gate catches a stale or partial file, not a forged one.
