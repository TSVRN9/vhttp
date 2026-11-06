# Phase 9r: Root-Cause Catalog and First Class Catches — Plan

**Goal:** record the root cause of every bug the reviews found so far, and ship the first mechanical catches for the cheapest, highest-yield classes. Each catch comes with evidence that it fails on the original bug.

**User directive (2026-11-06, binding):** "Whenever there's a bug or issue, I'd like you to do root cause analysis and reason about why it was able to occur in the first place, and then I'd like you to implement robust systems to catch them." Earlier directive, also binding: prove as much as possible, so the project assumes only what Verus assumes (rustc, LLVM, Z3), and take no shortcuts.

**Input:** `.worktrees/vt-rca/catalog.md` (109 entries, 18 classes, built from ledger summaries). Branch `phase-9r` in `.worktrees/wt-9r`, from main 73cc244. Evidence goes in `.worktrees/vt-9r-evidence/rN/`.

## Global Constraints
- Touch no file under crates/quic or crates/quictls; Phase 9a is editing them in parallel. Never edit crates/crypto/src, crates/ctcore/src or crates/ctmir/src/sem.rs.
- verify.sh's final line stays byte-identical: `verify.sh: all crates verified, duvet ok, ct ok (10 declassify), cost 19/36, escapes accounted (0), binary ok (49 fns)`. A new gate prints its own line before it and exits non-zero on failure.
- Every new gate fails closed:
  - a missing input, an empty list, or a tool that didn't run is a failure, never a pass;
  - each gate gets a demo in `scripts/gate-demos.sh` that feeds it a canned bad input and asserts a non-zero exit.
- No full workspace verify and no rlimit-4 run while 9a Task 0 is measuring. Test each gate standalone on canned inputs. The full verify.sh and cargo test runs happen once, after the controller says so.
- No new dependencies, and no downloaded binaries. shellcheck is not installed; installing it needs the user's sudo, so it is out of scope.
- No attribution lines in commits.

## Tasks

### R1: record and tools
- `docs/rca/README.md` holds:
  - the user directive, verbatim;
  - the entry format: defect, escape (which check should have caught it and why it didn't), class, catch, and evidence that the catch fires on the original bug;
  - the order of preference for catches: a proof obligation, then a verified checker, then a fail-closed verify.sh gate, then a test.
- `docs/rca/catalog.md` is the catalog, spot-checked:
  - Check at least 8 entries, spread across classes, against the archived review files in `/home/tavern/Projects/rust/web-server/.superpowers/archive/`. Fix any wrong entries.
  - Add a status column: caught now / scheduled (with owner phase) / open.
  - The 18 classes stay, with the catalog's proposed catch for each.
  - Classes not caught by this phase get an owner. Owners:
    - C5 and C7: 9a, 9b, 9c.
    - C12 and C14: design §7 of 9a.
    - C6, C8, C10, C11: a named later phase, "9r2".
- `docs/rca/2026-11-06-empty-crypto.md` is the first RCA entry:
  - **Defect:** crypto_stream.rs checks the window before the empty filter (crypto_stream.rs:89-98 on main).
  - **Escape:** the ensures prove buffer bounds but say nothing about which errors are allowed. It is a sibling of fix 753ec2d, which closed only the instance.
  - **Class:** C5.
  - **Catch:** 9a Task 3's `crypto_allowed_err`, plus R4's ratchet.
- Move the untracked tools into `tools/` as single canonical copies. Each gets a 2-line header saying what it does.
  - Copy `.worktrees/vt-4c-evidence/t3/rl.py` to `tools/rl.py`.
  - Copy `.worktrees/qchk/check_quotes.py` to `tools/check_quotes.py`.
  - The newest `mut.py` goes to `tools/mut.py`. Compare `.worktrees/vt-4c-evidence/t3/mut.py` with `.worktrees/vt-8c-evidence/rev8/zm/mut.py` and keep the more general one.
  - All of them stay runnable as `python3 -I tools/X.py`.

### R2: script hygiene (C4)
- Add `scripts/lint-scripts.sh`. It requires that every `scripts/*.sh` has `set -eu` and `set -o pipefail` before its first command.
- Add pipefail to ct-check.sh, ct-binary.sh and verify.sh:
  - Audit every pipeline in them.
  - Where a stage's non-zero exit is the expected outcome (grep with no match, `head` closing early), make that explicit, e.g. `{ grep … || [ $? -eq 1 ]; }`. Never use a blanket `|| true`.
  - List each pipeline you changed in the report, with why.
- Run lint-scripts.sh from verify.sh, before the final line.
- Test-skip policy: grep the tests for an early `return` on a missing env var or tool. Each one must `panic!` when `STRICT=1` (the `INTEROP_STRICT` pattern). List the ones you find. Fix them only outside crates/quic and crates/quictls; list those inside for 9a.

### R3: quote check in verify.sh (C1, the duvet gap)
- Problem: `duvet report` exits 0 even when a `//#` quote isn't in the RFC text.
- Fix: run `tools/check_quotes.py` over every `.rs` under crates/ from verify.sh, and fail if any citation is bad.
  - It needs `.duvet/specifications`, which is git-ignored. A missing directory is a failure, not a skip.
- Before wiring it in, run it on main's tree:
  - Every bad quote found is a real finding. Fix each one outside quic and quictls, and list the ones inside them for 9a.
  - Record the before/after counts.

### R4: acceptance ratchet (C5)
- Add `scripts/acceptance.sh`. It lists every exec fn inside `verus!` in crates/ (excluding crates/crypto/src) whose return type mentions `Result` or a known error-signalling type, and checks whether its ensures mention an `allowed_` spec name.
  - Use a simple, documented parser. State its limits in the script header.
  - Fns lacking the clause must be listed in `tools/acceptance-baseline.txt`, one `crate::path::fn` per line.
  - The gate fails if an unannotated fn is not in the baseline. A new error path can't land without its clause.
  - It also fails if a baseline line names a fn that now carries the clause, or that no longer exists. The baseline only shrinks.
  - It prints `acceptance: N/M error-returning fns carry allowed_ clauses` before verify.sh's final line.
- **Non-vacuity:** the gate fails if any `spec fn allowed_*` body is literally `true`, or is a match whose arms are all `true`.
  - The proof-side non-vacuity lemmas are 9a's job.
- Wire it into verify.sh.

### R5: gate demos (C4)
- Add `scripts/gate-demos.sh`. For each cheap gate, it makes a temp copy of the input, applies a canned bad change, runs the gate, and asserts a non-zero exit plus the expected message. It cleans up with a trap.
  - Gates covered: lint-scripts (a script without pipefail); the quote check (a quote altered by one word); the acceptance ratchet (a new unannotated `Result` fn; an `allowed_x_err` with body `true`; a stale baseline line); verify.sh's escape gate (an `assume(` in a temp crate copy, if that can run without a full verify; otherwise factor the escape check into a function the demo can call).
  - Fixtures go in `tools/gate-demos/`.
- Run gate-demos.sh from verify.sh, before the final line. It must take under 30 s.

## Verification (after the controller's go)
- `cargo build && cargo test --workspace`: 902 passed, 0 warnings.
- `scripts/verify.sh`: the exact final line, preceded by the new gates' lines.
- `scripts/gate-demos.sh`: every demo reports "fails as expected".
