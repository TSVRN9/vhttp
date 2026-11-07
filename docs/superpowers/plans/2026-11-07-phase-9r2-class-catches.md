# Phase 9r2: the remaining class catches — Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** ship the mechanical catches that 9r left open and that the 9a reviews and the 2026-11-07 audit added, each with evidence that it fails on the original bug.

**Architecture:** each catch is a fail-closed gate script under `scripts/`, called from `scripts/verify.sh` before its final line, with a demo in `scripts/gate-demos.sh` that feeds it a canned bad input. Python checkers live in `tools/` and run with `python3 -I`.

**Spec:** `docs/rca/catalog.md` (classes, proposed catches, owners), `docs/rca/2026-11-06-phase-9a-night.md` §8, `docs/rca/2026-11-06-acceptance-parser.md` (open item), `docs/rca/2026-11-07-audit.md`.

## Global Constraints

- User directive (binding): "Whenever there's a bug or issue, I'd like you to do root cause analysis and reason about why it was able to occur in the first place, and then I'd like you to implement robust systems to catch them." Also binding: "The entire point of this project is to try and prove as much as possible st it only assumes the same things as verus, ie rustc llvm z3 correctness. Do not take shortcuts."
- Touch no file under crates/quic/src or crates/quictls/src (Phase 9a continues there in parallel). Never edit crates/crypto/src, crates/ctcore/src or crates/ctmir/src/sem.rs.
- verify.sh's final line stays byte-identical: `verify.sh: all crates verified, duvet ok, ct ok (10 declassify), cost 19/36, escapes accounted (0), binary ok (49 fns)`. A new gate prints its own line before it and exits non-zero on failure.
- Every gate fails closed: a missing input, an empty list, or a tool that didn't run is a failure. Each gate gets a demo in `scripts/gate-demos.sh` (canned bad input, asserts non-zero exit and the expected message).
- Every new script passes `scripts/lint-scripts.sh` (set -eu, pipefail). No new dependencies, no downloaded binaries. shellcheck needs the user's sudo: out of scope.
- No attribution lines in commits. Evidence in `.worktrees/vt-9r2-evidence/<task>/` with a three-line HEAD.txt (HEAD, tree, `git status --porcelain | wc -l`) from a clean committed tree.
- Each task updates the catalog row of its class (status column) and the RCA entry it closes, citing the demo or failing output as evidence.

## Tasks

### Task 1 (R1): rlimit gate (C11 PROOF-BUDGET FRAGILITY)
- Every crate under crates/ is verified at `--rlimit 4` with `--output-json` inside verify.sh, and `tools/rl.py` (extended with a `--max N` mode) fails when any fn of quic or quictls is above 8,000,000 or any fn anywhere fails. Print `rlimit-gate: ok (max <fn> <n>)`.
- A fresh target dir must work: if vstd fails at rlimit 4 on a fresh target (seen in 9a), pass the limit to the crate under verification only, or warm with a default run first; measure and say which in the task report.
- verify.sh must not verify every crate twice: the rlimit-4 run replaces the default `cargo verus verify` loop, unless measurement shows a crate cannot verify at 4 (then that crate keeps the default and the gate names it explicitly in an allowlist file that can only shrink, as the acceptance baseline does).
- Demo: a canned JSON with a quic fn at 8,000,001 fails; one with a FAIL row fails; an empty JSON fails.

### Task 2 (R2): mutant registry (C6 MUST ONLY TEST-PINNED)
- `tools/mutants/<id>.patch` (one unified diff each) and `tools/mutants.tsv` (`id`, crate, expected failure regex, origin: plan task + mutation name). Seed it with every mutation named in the merged 9a tasks' Mutations steps (T1 M4-M7, T3 D1-D3/M1-M4, T4 M1-M3, T6 M1-M2 and the rest in those plan sections), regenerated against the current tree.
- Each row also names the fn(s) whose verification the mutant must break; `run` passes them to Verus's `--verify-function` (or `--verify-only-module`) so one mutant costs one fn's verification, not the crate's. Check Verus 0.2026.10.04's exact flag spelling with `verus --help` and record it.
- `scripts/mutants.sh check` (cheap, in verify.sh): every row has a patch, every patch `git apply --check`s against the tree, no duplicate ids, the tsv is non-empty.
- `scripts/mutants.sh run [id...]`: applies each patch alone in a throwaway `git worktree` (never the caller's tree), runs that crate's `cargo verus verify` (and the tests the row names), and passes only if verification fails matching the row's regex (not on rlimit: a `rlimit` match is a failure of the mutant run). Writes `tools/mutants-last-run.txt`: the crates tree hash (`git rev-parse HEAD:crates`) and one line per id.
- Merge gate: on main, when HEAD is a merge commit, verify.sh requires `tools/mutants-last-run.txt` to name `HEAD^2:crates`'s tree hash with every id passing. Document in the RCA README that `mutants.sh run` is the last step on a branch before merging.
- Demos: a patch that doesn't apply fails `check`; a stale run file on a canned merge fails; a canned mutant that still verifies fails `run` (use the acceptance demo crate under tools/gate-demos/ so the run is seconds).

### Task 3 (R3): citation gate (C1, from 9a T2 I1)
- Every `allowed_*err` / `*_allowed_err` spec fn, and every exec fn whose ensures mention `close_spec` with a literal code or a codes.rs constant, carries a `//= https://www.rfc-editor.org/rfc/...` line with a `//#` quote in the contiguous comment block above it (or above its doc comment). Reuse tools/acceptance.py's fn scanner; don't write a second Rust scanner.
- Demo: the acceptance demo crate with one predicate's citation stripped fails.

### Task 4 (R4): RFC-quantity gate for allowed_*err bodies (C8, recurred 3x in 9a)
- A predicate body may not read exec or model bookkeeping: calls of `.reassembly()`, `*_spec()` accessors, `.rfc()`, struct fields, or `self.` unless the line carries `// rfc-quantity: <why this is the RFC's quantity>`. RFC spec fns (`rfc_*`, `largest_received_offset`, `crypto_contiguous` and others defined over RFC histories) are allowed; the allowlist is a file of fn names, each with a one-line reason.
- Run it on the current tree: every hit is either fixed (if 9a left one, report it, don't edit quic) or annotated with a reason the reviewer can check.
- Demos: T6's original `recv_allowed_err` (reading `rfc_recv`'s running `high`) and T4's original duplicate rule (reading the `seen` mask), as canned files, both fail.

### Task 5 (R5): baseline history walk (open item of 2026-11-06-acceptance-parser.md)
- On main, `tools/acceptance.py` walks the first-parent history from the commit that introduced `tools/acceptance-baseline.txt` to HEAD and fails if any step grows it (today it compares only HEAD^1).
- Demo: a throwaway git repo (as the existing merge-base demo does) with growth spread over two direct commits fails.

### Task 6 (R6): demos for the remaining gates (C4)
- Factor the declassify gate and the deps gate out of verify.sh into `scripts/declassify-gate.sh` and `scripts/deps-gate.sh` taking their inputs as arguments; verify.sh calls them with today's inputs and prints the same final line.
- Demos: declassify gate with a report site missing its TRUSTED.md row; deps gate with a canned `cargo tree` output listing a second dep; ct-binary with a canned digest file that differs by one byte (if ct-binary.sh cannot take canned inputs without a rebuild, add an argument for the digest file and the dump, not a skip flag); ct-check's report reader with a canned report containing a `rejected` root.

## Review Focus
1. A gate that passes when its tool did not run (missing JSON, empty tsv, git error) — every demo must include that case.
2. The rlimit gate on a fresh clone (no target dir).
3. mutants.sh touching the caller's tree.
4. R4's allowlist growing without review: it is a ratchet like the acceptance baseline.
5. verify.sh's final line changing.
