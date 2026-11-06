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
- Tools: `tools/check_quotes.py`, `tools/rl.py`, `tools/mut.py`; gates: `scripts/lint-scripts.sh`, `scripts/check-quotes.sh`, `scripts/escape-gate.sh`, `scripts/acceptance.sh`, `scripts/gate-demos.sh`.
- `2026-11-06-acceptance-parser.md`: RCA of the R4 parser's own bugs.
