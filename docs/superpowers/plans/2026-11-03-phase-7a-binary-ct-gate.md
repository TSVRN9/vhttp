# Phase 7a: Binary-Level Constant-Time Gate and Timing Tests — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Two checks of what the compiler emits for `crates/crypto`, below the MIR level that Phase 8a proves:
- a `verify.sh` gate that fails when the shipped object code changes without a fresh read;
- dudect-style timing tests.

**Architecture:**
- The gate is a script, `scripts/ct-binary.sh`. It runs the audit recipe in `docs/crypto-binary-audit.md`, normalises the disassembly, and compares a digest per function against a tracked file, `docs/crypto-binary-digests.txt`. It also checks structurally that `ct_mask` stays out of line.
- The timing tests are an `#[ignore]`d test binary in `crates/crypto/tests/`, std only.

**Tech Stack:** rustc 1.98.1, binutils `objdump`/`ar`, POSIX sh, plain Rust tests.

**Spec:** `docs/superpowers/specs/2026-10-27-verified-http3-design.md` (Phase 7; line 22's RSA deployment conditions), `docs/crypto-binary-audit.md`, and TRUSTED.md rows 36–38 and 43.

## Global Constraints

- **Do not edit `crates/crypto/src/`.** Any edit there voids the recorded object read. Tests go in `crates/crypto/tests/`.
- **The gate must fail closed:**
  - a missing tool, a build failure or an unexpected unit count is a failure, not a skip;
  - every failure message names what to re-read.
- **Use the shipped build:** plain workspace `cargo build --release`, with its own fresh `--target-dir` under `target/`. Never `--emit=obj`, and never a different profile.
- **No new dependencies.**
- **Commit messages carry no attribution lines.**
- **Work in `/home/tavern/Projects/rust/web-server/.worktrees/wt-7a`** (branch `phase-7a`). Scratch goes in `.worktrees/vt-7a-evidence/`, never `/tmp`.
- **Don't break the final line.** `scripts/verify.sh`'s final line keeps its current fields. The gate adds one field, `binary ok (<n> fns)`, and the line must still be parseable by anything that reads it today. grep the scripts first.

## Review Focus

1. **Determinism.** Two clean builds at different target dirs must give identical digests. A digest that depends on paths, hashes or `.llvm.NNN` suffixes makes the gate flaky. Task 1 proves this, using a second checkout path as well.
2. **The gate must catch the real failure mode.** That is LLVM turning a masked select into a branch, which happens when `ct_mask` is inlined. Task 1's test removes `#[inline(never)]` in a scratch copy and must fail. The scratch copy is a copy of the tree, never the repo's own `crates/crypto/src`.
3. **Time added to `verify.sh`.** Measure it and report it.
4. **Timing tests must detect a leaky control** before any verdict on real code counts. If a real function shows a leak, stop and report it; never loosen the threshold.
5. **Honesty.** TRUSTED.md and the audit doc must say:
   - the gate detects change, not leaks;
   - a digest update requires a fresh read per the audit's recipe;
   - the timing tests are `--ignored` and not in `verify.sh`, and what they cover.

---

### Task 1: The binary gate

**Files:**
- Create: `scripts/ct-binary.sh`, `docs/crypto-binary-digests.txt`
- Modify: `scripts/verify.sh` (call it and add `binary ok (<n> fns)` to the final line), `docs/crypto-binary-audit.md` (a "Gate" section)

**Interfaces:**
- `scripts/ct-binary.sh [--update]`:
  1. Builds `crates/crypto` as the workspace ships it, with its own target dir.
  2. Extracts the rlib's `*.rcgu.o` members and checks that their count equals the tracked unit count, today 2.
  3. Disassembles each member with `objdump -dr --no-show-raw-insn -C`.
  4. Splits the output per function symbol and normalises each: strip addresses and `.llvm.N` suffixes, keep opcodes, operands and relocations.
  5. Writes `<sha256> <symbol>` lines and diffs them against `docs/crypto-binary-digests.txt`.

  With `--update` it rewrites the file and prints the reminder that a fresh read is needed. On success it prints `ct-binary: ok (<n> fns)`.
- Structural checks, which run in every mode:
  - the symbol `crypto::bignum::ct_mask` exists as its own function, and its body is `mov`/`neg`/`ret`;
  - each function that the audit lists as calling `ct_mask` (`cond_sub`, `rsa_pss_sha256_sign`, and the others the audit names) contains at least one `PLT32 crypto::bignum::ct_mask` relocation;
  - `scalar_in_range` exists out of line.

- [ ] **Step 1:** Write the script and generate the digests file at HEAD. Check that the whole-dump md5 per the audit's recipe is still `a247bd0fc9216f57f9ba2fe5fc376e88`. If it differs, `crates/crypto` or the toolchain changed since 8b32220; stop and report.
- [ ] **Step 2: Determinism.** Run two clean builds, one from a second checkout at a different path (a `git worktree` under `.worktrees/`). The digests must be identical.
- [ ] **Step 3: Negative tests, in scratch copies of the tree.**
  - Remove `#[inline(never)]` from `ct_mask`. The gate must fail with both a digest diff and the structural message.
  - Make a no-op source edit in an unrelated crypto fn, such as a reordered `let`. The digest must diff, or, if the opcodes are unchanged, the script says so.
- [ ] **Step 4:** Wire the script into `verify.sh`, and measure the time it adds, cold and warm.
- [ ] **Step 5:** Add the audit doc's "Gate" section: what the gate checks, what it does not check, and the update protocol. Under the update protocol, a digest change requires a fresh read of every changed symbol per the recipe, recorded in the audit with its date and commit. Then commit.

### Task 2: Timing tests and the trust rows

**Files:**
- Create: `crates/crypto/tests/dudect.rs`
- Modify: `TRUSTED.md` (rows 36–38 and 43), `docs/crypto-binary-audit.md` (a "Timing tests" section), `docs/superpowers/specs/2026-10-27-verified-http3-design.md` (Phase 7: what 7a delivered and what remains)

**Interfaces:**
- `cargo test --release -p crypto --test dudect -- --ignored --nocapture --test-threads 1`. Each test:
  - pins itself to one core with `sched_setaffinity` through `libc`, if libc is already a dependency. Otherwise it relies on `taskset` from the script and says so;
  - interleaves two classes, a fixed secret and a random secret. The inputs come from a simple xorshift with a fixed seed;
  - measures with `std::time::Instant` around each call, or with `core::arch::x86_64::_rdtsc` behind `cfg(target_arch)`;
  - crops the top 5% of measurements;
  - computes Welch's t and fails at |t| > 10 over at least 10^6 measurements. For RSA-2048 it is 10^4, and the report says why.
- Targets:
  - `aes128_encrypt_block` (secret key);
  - GHASH `gf128_mul_exec` (secret H);
  - the GCM tag compare through `aes128_gcm_open` (a wrong tag against the right one at a differing byte position);
  - `p256_ecdsa_sign` (secret d);
  - `p256_ecdh` (secret d);
  - `rsa_pss_sha256_sign` at 2048 bits (secret d, same n).
- Control: a deliberately leaky function in the test file, an early-exit byte compare, which must give |t| > 10. If the control does not fail, the harness's results don't count.

- [ ] **Step 1:** Write the harness and the control. Show that the control fails.
- [ ] **Step 2:** Run every target, and record |t|, the measurement counts and the wall time in the report. Any real target over the threshold: stop and report, with the raw numbers.
- [ ] **Step 3:** Update the TRUSTED rows, the audit doc and the design spec. Say what runs when (the gate in `verify.sh`, timing by hand), what each covers, and what stays uncovered:
  - other CPUs, frequency scaling and SMT;
  - cache attacks beyond the dudect signal;
  - every non-crypto secret path.

  RSA stays not deployable: the loader and the handshake limit remain.
- [ ] **Step 4:** Commit.
