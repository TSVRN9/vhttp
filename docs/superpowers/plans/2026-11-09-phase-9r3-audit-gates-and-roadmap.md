# Phase 9r3: audit gates and the roadmap — Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** close the gate holes and the missing roadmap that the 2026-11-09 audit found (F3, F4, F5, F9, F10, F12, F13, F17, F18, plus the dangling-evidence item from the owner's F19 decision), each with an RCA and a fail-closed demo.

**Architecture:** same as 9r/9r2. Each catch is a fail-closed gate under `scripts/` (Python checkers in `tools/`, run with `python3 -I`), called from `scripts/verify.sh`, with a demo in `scripts/gate-demos.sh`. The roadmap is a committed doc, `docs/roadmap.md`, plus a tracked `docs/carryovers.tsv` whose gate is the C3 catch.

**Tech Stack:** POSIX sh (`set -eu`, `pipefail`), Python 3 stdlib, git, cargo, Verus 0.2026.10.04.

**Spec:** `docs/audit-2026-11-09.md` (findings and the owner's decisions), `docs/rca/README.md`, `docs/rca/catalog.md` (classes C1-C18; C3 and C4 proposed catches).

## Global Constraints

- Binding owner rules (see the audit's "Project rules"): no proof shortcuts; every bug gets an RCA, a catalog class and a mechanical catch with evidence that it fires; ratchet files only shrink; merges to main are `--no-ff` only; toolchain pinned (Verus 0.2026.10.04.426d8b0, rustc 1.98.1, vest_lib 0.2.2), do not upgrade.
- Touch nothing under `crates/*/src`. The only `crates/` edit allowed is the two comments in `crates/ctmir/tests/eval.rs` (Task 5). Never edit `crates/crypto`.
- On a clean tree, verify.sh's final line stays byte-identical: `verify.sh: all crates verified, duvet ok, ct ok (10 declassify), cost 19/36, escapes accounted (0), binary ok (49 fns)`. A new gate prints its own line before it.
- Every gate fails closed (missing input, empty list, tool did not run, git error). Every gate gets demos in `scripts/gate-demos.sh`, including its tool-did-not-run case. Every new script passes `scripts/lint-scripts.sh`.
- No new dependencies. No `git push`. No attribution lines in commits.
- RCAs for this phase go in one file, `docs/rca/2026-11-09-audit.md`, one `##` section per finding in the README's entry format (Defect, Escape, Class, Catch, Evidence). Evidence cites a demo name, a mutant id, a test name or a commit — never a path under `.worktrees/`, `.superpowers/` or `/tmp` (Task 5 makes that a gate). Each task updates its class row in `docs/rca/catalog.md` and adds its file to the README's Files list.
- Work in `.worktrees/wt-9r3` on branch `phase-9r3`. Scratch output in `.worktrees/vt-9r3/<task>/`.

## Review Focus

1. A gate that passes when its tool did not run or its input is empty: each demo set must include that case.
2. verify.sh run from a dirty tree, or with `VERUS_HOME` pointing at another Verus: must not print the clean final line.
3. A ratchet that can be loosened in one commit (the test floor dropping, a carryover row deleted instead of closed, a TRUSTED row's removal phase changed to `never`).
4. The roadmap and carryovers going stale after this phase: the gate must tie a merged phase to zero open rows.
5. Gate demos that need the network or a client binary: they must run offline with canned inputs.

---

### Task 1: a green run names its commit and its Verus (F5, class C4)

**Files:** Create `tools/verus-pin.txt`, `scripts/clean-tree.sh`. Modify `scripts/verify.sh`, `scripts/rlimit-gate.sh`, `scripts/mutants.sh`, `tools/rl.py`, `scripts/gate-demos.sh`, `docs/rca/2026-11-09-audit.md` (create), `docs/rca/catalog.md`, `docs/rca/README.md`.

**Produces:** `tools/verus-pin.txt` with exactly three lines: `version 0.2026.10.04.426d8b0`, `commit 426d8b01e7ffb910a36c15e1f870ff985bb61eef`, `toolchain 1.98.1`. The three scripts derive their default `VERUS_HOME` from the `version` line (`$HOME/.local/opt/verus/<version>/verus-x86-linux`) instead of hardcoding it. `scripts/clean-tree.sh ROOT` exits 0 iff `git -C ROOT status --porcelain` is empty, else prints `clean-tree: tree dirty (N paths)` and exits 1; a git error exits 1.

- [ ] verify.sh calls `clean-tree.sh` first. If it fails and `VERIFY_DIRTY=1` is not set, verify.sh stops with that message. With `VERIFY_DIRTY=1` it prints `verify.sh: tree dirty, not a main-tip run` first and its final line starts with `verify.sh (DIRTY TREE, vouches for no commit):` instead of `verify.sh:`.
- [ ] Also first in verify.sh: `cargo metadata --locked --format-version 1 > /dev/null`, so a `Cargo.lock` that cargo would rewrite fails (covers F17's `--locked` point for every later cargo call).
- [ ] `tools/rl.py --gate NAME --pin FILE [--max N] JSON`: for every results object, `verus.version` and `verus.commit` equal the pin's, `verus.toolchain` starts with the pin's `toolchain` followed by `-`, and `verification-results.is-verifying-entire-crate` is `true`; otherwise `rlimit-gate: NAME: ...` naming the field, exit 1. A missing or malformed pin file fails. `rlimit-gate.sh` passes `--pin "$root/tools/verus-pin.txt"`.
- [ ] Demos (gate-demos.sh): clean-tree on a throwaway git repo with an untracked file, with a modified tracked file, and on a non-repo dir (all fail), clean repo passes; rl.py on a canned JSON with a wrong version, a wrong commit, a wrong toolchain, `is-verifying-entire-crate: false`, and with a missing pin file (all fail); the existing passing rl.py fixtures gain a matching `verus` object.
- [ ] RCA section "F5: a green verify run did not name its tree or its Verus" (escape: verify.sh read the working tree and trusted `VERUS_HOME`; class C4). Catalog C4 status gains it.
- [ ] Run `VERIFY_DIRTY=1 scripts/verify.sh` while the tree is dirty, then commit and run `scripts/verify.sh` on the clean tree; record both final lines in the task report.
- [ ] Commit.

### Task 2: the mutant run at main's tip is a real run (F4, class C6/C4)

**Files:** Modify `scripts/mutants.sh`, `tools/mutants.py`, `scripts/gate-demos.sh`, `docs/rca/README.md` (the "Trust boundary (accepted)" paragraph and "Before merging" list), `docs/rca/2026-11-09-audit.md`, `docs/rca/catalog.md`, `TRUSTED.md` if it mentions the run file.

**Consumes:** Task 1's `verus-pin.txt` default `VERUS_HOME`.
**Produces:** `scripts/mutants.sh run --out FILE [id..]` writes the run file to FILE instead of `tools/mutants-last-run.txt` (default unchanged). `python3 -I tools/mutants.py same COMMITTED FRESH` exits 0 iff the two files are equal after dropping `#` lines, else prints the differing lines and exits 1.

- [ ] In `mutants.sh verify`, at main's tip only (the branch where `gate` runs today), after `gate` passes: `run --out "$out/mutants-fresh.txt"` (all ids) and `same` against the committed file. Print `mutants: fresh run at main's tip matches the committed run file (N mutants)`. On a branch nothing changes. A run that fails or kills fewer mutants fails verify.sh.
- [ ] The run file's `#` line also names the pin's Verus version (from `tools/verus-pin.txt`).
- [ ] Demo: on the fixture crate the existing mutants demos use, a registry with one mutant that does not break verification and a hand-written run file claiming `pass` for it: `mutants.sh verify` in the throwaway main fails on `same` (or on the run). A matching honest run file passes.
- [ ] README: the run file stops being an unchecked attestation on main; say what remains trusted on a branch (the branch gate still only checks freshness).
- [ ] RCA section "F4: the mutant gate accepted a run that never happened" (class C6, escape C4).
- [ ] Run `scripts/mutants.sh verify` on the worktree's clean tip as if on main (the gate-demo covers the main case; report the wall time of a full `run`).
- [ ] Commit.

### Task 3: every crate's dependencies are allow-listed (F17, class C4)

**Files:** Create `tools/deps-allow.txt`. Modify `scripts/deps-gate.sh`, `scripts/verify.sh`, `scripts/gate-demos.sh`, `tools/gate-demos/` deps fixtures, `docs/rca/2026-11-09-audit.md`, `docs/rca/catalog.md`.

**Produces:** `tools/deps-allow.txt`: one line per workspace crate, `CRATE: DEP DEP ..` (normal deps at depth 1, names only, sorted; workspace crates included), e.g. `crypto: vstd`. `deps-gate.sh ROOT [TREEDIR]` checks every crate under `crates/` (TREEDIR holds one canned `cargo tree -p C -e normal --depth 1 --prefix none --locked` output per crate as `C.txt`): each crate's dep set equals its line exactly; a crate without a line, a line without a crate, an empty tree, or a cargo failure fails. Prints `deps-gate: N crates match tools/deps-allow.txt`.

- [ ] Fill the file from today's tree (expected third-party: vstd everywhere verified, vest_lib 0.2.2 in wire/h3/quic, libc in server); report the full list.
- [ ] Demos: an extra dep in one crate's canned tree; a crate missing from the allow-list; an allow-list line for a removed crate; an empty canned tree; crypto with a second dep (keeps the old demo's meaning).
- [ ] RCA section "F17: a new dependency outside crypto passed every gate". Commit.

### Task 4: interop in verify.sh and a shrink-proof test floor (F13, class C4/C6)

**Files:** Create `scripts/interop.sh`, `tools/test-floor.txt`. Modify `scripts/test-gate.sh`, `tools/ratchet_walk.py`, `scripts/verify.sh`, `scripts/gate-demos.sh`, `crates/server/tests/interop.rs` only if a test needs a per-client strict switch (it is a test file, not `src`; allowed), `docs/rca/2026-11-09-audit.md`, `docs/rca/catalog.md`, `docs/rca/README.md`.

**Produces:**
- `scripts/interop.sh ROOT`: decides per client whether it is present (curl: `curl --version` lists `HTTP3`; quiche: `$QUICHE_CLIENT`, else `<main checkout>/.worktrees/ext-quiche/src/target/release/quiche-client` if executable, where the main checkout is the parent of `git -C ROOT rev-parse --path-format=absolute --git-common-dir`, so it works from a worktree). For each present client it runs that client's tests (`cargo test --locked -p server --test interop -- --ignored --exact <name>` with `INTEROP_STRICT=1`) and requires `test <name> ... ok`. It prints one line `interop: curl ok|skipped (no HTTP3), quiche ok|skipped (no client)`. A present client whose test fails, or a test that printed neither ok nor FAILED, fails.
- `tools/test-floor.txt`: `CRATE COUNT` per workspace crate that has tests, COUNT = today's passed count. `test-gate.sh --workspace` fails when a crate passes fewer than its floor, or has tests and no floor line, or a line names no crate.
- `tools/ratchet_walk.py` MODE `floors`: `CRATE COUNT` keyed by crate; the floor is each key's highest value over the first-parent history, and a key once present may not disappear. HEAD's copy and the working tree must be at or above it. On a branch the file is compared with the merge-base's copy the same way (values not lower, no key removed), following `scripts/rlimit-ceilings.sh`'s branch/main split.
- [ ] verify.sh runs `interop.sh` after the test gate and prints its line; the final line is unchanged.
- [ ] Demos: a fake `curl` on `PATH` that lists HTTP3 and makes the test fail → interop.sh fails; a fake curl without HTTP3 and no quiche → passes printing both `skipped`; a crate below its floor; a crate with tests and no floor line; a floor lowered against the merge-base (throwaway repo); growth then a drop across two first-parent commits on main (throwaway repo).
- [ ] RCA section "F13: interop never re-checked; deleting a test stayed green". Commit.

### Task 5: the roadmap, the carryover gate, and tracked evidence (F3, F10, F12, F18, F19 note; class C3, C2)

**Files:** Create `docs/roadmap.md`, `docs/carryovers.tsv`, `tools/carryovers.py`, `scripts/carryovers.sh`. Modify `TRUSTED.md` (removal column), `docs/rca/2026-11-06-empty-crypto.md`, `docs/rca/2026-11-06-phase-9a-night.md`, `crates/ctmir/tests/eval.rs` (comments at :147, :172 only), `scripts/verify.sh`, `scripts/gate-demos.sh`, `docs/rca/2026-11-09-audit.md`, `docs/rca/catalog.md`, `docs/rca/README.md`, `README.md` (one link to the roadmap).

**Produces:**
- `docs/roadmap.md` with a table `| id | title | status | order | plan / merge |` where status is one of `merged`, `in progress`, `planned`, `unplanned`. It lists every phase ever named (0-1, 2a, 2b, 3a-3e, 3d2, 4a-4d, 5a-5e, 6, 7a, 7, 8a-8d, 9r, 9r2, 9r3, 9a, 9a2, 9b, 9c, the six trust-base sub-phases of `docs/superpowers/specs/2026-11-05-phase-9-acceptance-and-closes-design.md:268-276` with ids `9t1`..`9t6`), plus new phases: `10a` admission and bounds (owns audit F2's handshake deadline, F14's per-datagram walk, F15's memory figure, MAX_CONNS admission/slot eviction, Retry or a per-source handshake limit, SipHash CID/token index, path-slot eviction, the RSA key loader for `rsa_key_wf`, server-level running-time and memory bounds, catalog C10), `11` composed end-to-end theorem (audit F8: re-export the clauses the quictls wrapper drops, then request→response, frame-space rules, authenticated-request), `12` production readiness (logging/metrics, CI, a handler API, an async shell, zeroisation), and `t1` toolchain upgrade procedure (audit F12: ceilings reset, binary digests, MIR schema, vstd/vest_lib pin; design only). Order follows the owner's F11 decision: 9a2, 9r3, 10a, 9b's non-`conn.rs` parts (9b Task 1 Frags index, C15), Phase 6, then 9b/9c's `conn.rs` send/recovery parts, then the trust-base sub-phases, 4d, 7, 11, 12. Each open phase gets a short section: scope, its sources (spec/plan path:line), and its carryover ids. One paragraph per finding of the audit says where it went.
- `docs/carryovers.tsv`, tab-separated, header line `#id	owner	status	evidence	source	text`. `owner` is a roadmap id; `status` is `open` or `closed`; `evidence` is `-` when open, else one of `test:<name>`, `fn:<name>`, `doc:<repo path>`, `commit:<sha>`. Seed rows: every still-open item of the owner's memory note `/home/tavern/.claude/projects/-home-tavern-Projects-rust-web-server/memory/phase-2-carryover.md` (re-check each against the tree; an item already done becomes a `closed` row with its evidence), every "Binding notes for later phases" item in the 3d2, 3e and 4c plans and `docs/superpowers/plans/2026-10-28-phase-4-outlines.md` that is not yet done, the open items of `docs/rca/catalog.md` (status `open`/`partial`), and the audit's F2, F6-F10, F12, F14-F16 and its "Smaller items".
- `tools/carryovers.py check ROOT` (via `scripts/carryovers.sh`, in verify.sh): every row has exactly the 6 header columns, ids unique; every owner is an id of the roadmap table; every `closed` row's evidence resolves (`test:`/`fn:` — `fn <name>` appears in a tracked `.rs` file; `doc:` — the path is tracked; `commit:` — `git cat-file -e`); **a phase whose roadmap status is `merged` owns no `open` row** (the C3 catch); every `TRUSTED.md` table row's last cell names a roadmap id or starts with `never (` and a reason; and no tracked file among `docs/rca/*.md` `- **Evidence` lines, `TRUSTED.md`, `docs/requirements.md` and `crates/**/*.rs` cites `.worktrees/`, `.superpowers/`, `/tmp/` or `vt-*-evidence`. Prints `carryovers: N rows (M open), roadmap P phases, ok`.
- Shrink protection: on main, a row present in any first-parent copy of `docs/carryovers.tsv` may not disappear (closing it is a status change, not a deletion); on a branch, compared with the merge-base copy. Reuse `tools/ratchet_walk.py` with a new MODE `ids` (key = first column; a key once present stays).
- [ ] TRUSTED.md: give each row's removal cell a roadmap id (fix the audit's :37, :42, :43, :45, :49, :51) or `never (<why it cannot be proved>)`; per the owner's no-shortcuts rule only genuinely inexpressible items stay `never` (timing below MIR, zeroisation's existence, the MIR semantics/leakage model, the dumper); report each `never` you keep with its reason.
- [ ] Rewrite the dangling evidence citations: RCA Evidence lines name the mutant ids and `scripts/mutants.sh run`, the test names, or commits; `eval.rs` comments name the commit (0b0061c) only. The audit's F19 bullet lists them.
- [ ] Demos: a closed row with an unresolvable `fn:`; an owner not in the roadmap; an open row owned by a `merged` phase; a duplicate id; a TRUSTED row with an empty removal cell; an RCA Evidence line citing `.worktrees/vt-x-evidence/log`; a row deleted on main across two commits (throwaway repo); an empty tsv; a missing roadmap file.
- [ ] RCA sections "F3: no roadmap in the repo; open work lived in a private note" (class C3; the catch is this gate) and "F19 follow-up: committed docs cited evidence in deleted untracked dirs" (class C3 untracked evidence). Catalog C3 status becomes caught; C2 notes the TRUSTED removal-cell check.
- [ ] Add the roadmap to the README's Files list and a line in the top-level README. Commit.

### Task 6: requirements status column (F9, class C1)

**Files:** Modify `docs/requirements.md`, `tools/carryovers.py` (or a new `tools/requirements.py` with `scripts/requirements.sh`), `scripts/verify.sh`, `scripts/gate-demos.sh`, `docs/rca/2026-11-09-audit.md`, `docs/rca/catalog.md`.

**Produces:** a `Status` column on every row: `proved:<fn>[,<fn>]`, `tested:<test>[,..]`, `false (<TRUSTED.md row key>)`, `open:<roadmap id>`, `n/a`, `declined`. A ticked row must be `proved:` (every fn resolves as in Task 5) or say plainly what it is; `tested:`-only rows are not ticked (owner rule: tested is open work) and carry an `open:` owner too. The gate fails on a row without a status, an unresolvable name, a ticked row whose status is not `proved:`, and an `open:` id not in the roadmap. The legend's Phase 7 exit ("no unannotated MUSTs", `verify.sh` runs `duvet report` with no threshold) becomes a carryover row owned by `7`.

- [ ] Fix the rows the audit names: `:257` (§9.4, false per TRUSTED.md:37), `:387`, `:531`, `:533` (tested), `:540`, `:423`, `:409`, `:204`, `:89`, `:219`; and the three requirements.md items from the carryover note (§7.2.5 separator, RFC 8446 §4.4.2.2 ECDSA-only wording, RFC 9114 §7.1 placement wording).
- [ ] Report the counts per status (the audit counted 255 ticked, 112 N/A, 66 declined, 19 Phase 6 rows, 7 on 4d).
- [ ] Demos: a ticked row with `tested:` only; a `proved:` fn that does not exist; a row with no status; an `open:` id not in the roadmap.
- [ ] RCA section "F9: requirements.md marked unproved rows done" (class C1). Commit.

### Task 7: merge prep

- [ ] Merge main into the branch (after 9a2 has merged), re-run the whole of `scripts/verify.sh` on the clean tip, `scripts/mutants.sh run` (crates/ctmir/tests changed), commit the run file, then the final whole-branch review.
