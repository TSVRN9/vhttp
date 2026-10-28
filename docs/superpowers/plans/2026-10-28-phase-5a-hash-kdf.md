# Phase 5a: Verified SHA-256, HMAC-SHA256, HKDF — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the four RustCrypto-backed `#[verifier::external_body]` exec fns below with verified Verus exec code. Each keeps its 3a signature, `requires` and `ensures` byte for byte.
- `crypto::sha256::sha256`
- `crypto::hmac::hmac_sha256`
- `crypto::hkdf::hkdf_extract`
- `crypto::hkdf::hkdf_expand`

TRUSTED.md rows 30–33 go, and the crypto escape count drops from 11 to 7. No other crate depends on `crypto` yet, so nothing upstream changes.

**Architecture:**
- **`sha256.rs` gains private exec code under the existing specs:**
  - word helpers;
  - `compress` (one block, at an offset into a slice, with no copy);
  - `sha256_cat(prefix, msg)`, the one hashing core.
  
  `sha256(msg)` becomes `sha256_cat(&[], msg)`. HMAC's inner and outer hashes are `sha256_cat(&k0_xor_pad, …)`, so the message is never copied.
- **`hmac.rs` gains `hmac_sha256_core`,** which is HMAC with a looser message bound. HKDF-Expand's `T ‖ info ‖ i` input is 33 bytes longer than `MAX_INPUT_LEN` allows. The public `hmac_sha256` calls the core.
- **`hkdf.rs`:**
  - `hkdf_extract` is `hmac_sha256(salt, ikm)`;
  - `hkdf_expand` loops T(i) over one reused `Vec` buffer.
- **Allocation:**
  - SHA-256 and HMAC allocate nothing on the heap. Their state is a `[u32; 8]`, the schedule a `[u32; 64]`, the pad tail a `[u8; 128]` and the key blocks `[u8; 64]`.
  - HKDF-Expand allocates twice per call: the output and the message buffer.
- **No streaming/incremental hash API.**
  - `crates/tls` has no hash call today.
  - The Phase 4 outline (`2026-10-28-phase-4-outlines.md`, line 173) already decided that the TLS transcript is a byte buffer rehashed with one-shot `sha256` (`// ponytail:`).
  - YAGNI. If 4b/4c later measure a need, `compress` plus the suffix-form block invariant (Task 2) is the core of an `update`/`finish` pair.

**Tech Stack:** Verus 0.2026.10.04.426d8b0 (`~/.local/opt/verus/0.2026.10.04.426d8b0/verus-x86-linux`), vstd `=0.0.0-2026-10-04-0306`. No new crates.

**Spec:** `docs/superpowers/specs/2026-10-27-verified-http3-design.md`, Phase 5. Its order is SHA-256 → HMAC → HKDF → …, and it calls for "bit-vector and nonlinear arithmetic proofs come in small lemma steps".

## Global Constraints

- **Spec freeze.** Nothing in this list may change:
  - any `spec fn` body or signature;
  - any `const` (`SHA256_K`, `SHA256_H0`, `MAX_INPUT_LEN`);
  - any `pub` exec signature, `requires` or `ensures`, in `sha256.rs`, `hmac.rs`, `hkdf.rs` and `bytes.rs`.

  Allowed additions are new proof fns, private or `pub(crate)` exec fns, and private helper `spec fn`s that no trusted spec references. Allowed edits are doc comments. Before each commit, the `git diff` of those four files must show only those kinds of change.
- **This is the first time the specs meet the vectors through a proof.** If a vector test fails after verification passes, the spec is wrong (or the vector is). Stop and escalate with the failing input. Never edit a spec to make a test pass.
- **Escapes:**
  - add none;
  - `scripts/verify.sh` counts every `#[verifier::external_body]` line in `crates/crypto/src/` and requires the count to equal the number of `| crypto::` rows in TRUSTED.md;
  - the commit that deletes an attribute also deletes its row, or the gate fails.

  Its grep matches `external_body`, `assume(`, `admit(`, `assume_specification`, `verifier::external…` and the bare word `axiom` *anywhere*, comments included:
  - delete the old `/// Trusted shim: …` doc lines rather than rewording them around the token;
  - never name a lemma `*assume*` or `axiom`;
  - use no vstd items through `#[verifier::external…]` attributes in `crates/`.

  `#[verifier::rlimit(N)]`, `#[verifier::spinoff_prover]` and `reveal_with_fuel` are not escapes and are allowed. Every `rlimit` is listed in the task report with its measured time.
- **No `by (compute_only)` / `by (compute)` on SHA-256.** The 3a probes timed out. No proof may evaluate SHA-256, or `spec_sha256`/`sha256_compress`/`sha256_w`, on concrete bytes. Vector checking stays in `cargo test`.
- **Proof structure for SHA-256:**
  - `by (bit_vector)` only in small standalone `proof fn bv_*` lemmas, in `crates/wire/src/varint.rs` style;
  - per-round equality is proved once, then lifted over the 64 rounds by a **loop invariant with one-step unfolding** of `sha256_rounds`;
  - never unroll the 64 rounds in proof or exec code. A 4- or 8-round unrolled exec loop is out of scope (`// ponytail:` note on the round loop: one round per iteration, unroll if profiling shows it matters).
- **Exec arithmetic must mirror the spec's association order.**
  - `t1` is `add32(add32(add32(add32(h, Σ1(e)), Ch(e,f,g)), K[t]), W[t])`.
  - `W[t]` is `add32(add32(add32(σ1(W[t−2]), W[t−7]), σ0(W[t−15])), W[t−16])`.
  - Reassociating makes you prove modular commutativity for nothing.
- **There is no vstd spec for `u32::rotate_right`, `from_be_bytes` or `to_be_bytes` at this pin**, so don't use them. Write shifts with literal amounts (`(x >> 2) | (x << 30)`). Use `u32::wrapping_add`: vstd specifies it as `vstd::wrapping::u32_specs::wrapping_add`, which is bridged to `add32` by one lemma.
- **These vstd APIs are specified and may be used:**
  - `vstd::slice::slice_subrange`;
  - `Vec::with_capacity`, `push`, `extend_from_slice` and `truncate`;
  - `.set(i, v)` on arrays, slices and Vecs (`ArrayAdditionalExecFns`, etc.).
- **Hash-input bound.** FIPS 180-4 limits the input to < 2⁶⁴ bits, i.e. < 2⁶¹ bytes. The internal cores require `prefix@.len() + msg@.len() < 0x2000_0000_0000_0000`, so the `8 * len` length field fits a `u64` and equals `i2osp(8 * m.len(), 8)` without truncation. Public bounds stay `MAX_INPUT_LEN` (2⁶⁰).
- **Citations:**
  - FIPS 180-4, RFC 2104 and RFC 5869 are **not** tracked in `.duvet/config.toml`. Every new citation is a plain `//` comment (e.g. `// FIPS 180-4 §6.2.2 step 3`).
  - This phase writes **zero** `//=` / `//#` lines.
- **Imports of spec items** stay glob-imported under `#[allow(unused_imports)]`, as in 3a. Named imports of spec fns break plain `cargo build` (E0432).
- **Every task's verification runs all four checks:**
  - `scripts/verify.sh` prints `verify.sh: all crates verified, duvet ok, escapes accounted (N)`, with N given per task;
  - `cargo build && cargo test` pass with 0 warnings;
  - the escape grep `grep -rnE 'admit\(|assume\(|external_body|assume_specification|verifier::external|axiom fn' crates --include='*.rs'` prints only `crates/crypto/src/*.rs:N:#[verifier::external_body]` lines, N of them;
  - `duvet report` exits 0 (run inside verify.sh).
- **Verification evidence uses a fresh, absolute `CARGO_TARGET_DIR`:**
  - Run `CARGO_TARGET_DIR=/tmp/claude-1000/-home-tavern-Projects-rust-web-server/19d690a3-7cab-4802-bc1f-9aa0173a905e/scratchpad/vt-5a-tN scripts/verify.sh`. The path must be absolute because `verify.sh` `cd`s into each crate, and a relative path would land inside it.
  - The output must show `verification results:: … 0 errors` for crypto. A cache hit prints nothing.
  - **Then `rm -rf` that directory.** The tmpfs is shared and capped at 16 GB.
  - While iterating, verify only the crate (`cd crates/crypto && CARGO_TARGET_DIR=<same absolute dir> cargo verus verify`). Use Verus's `--verify-module` / `--verify-function` / `--time` pass-through flags (syntax per `cargo verus verify --help`).
- **Proof-time budget.**
  - Task 1 and Task 2 reports list the five slowest functions from `--time`.
  - If any single function takes over 60 s, split it with a lemma or use `spinoff_prover` before moving on. Don't raise the rlimit globally.
- **Branch:** `phase-5a`, cut from `main` and merged locally into `main` at the end.

## Matrix rows this plan touches

None. The Phase-5 rows (RFC 8446 §4.2.8.2, §9.1 (req)) are P-256 and RSA, and RFC 9001 §5.2's "HKDF primitive itself is Phase 5" note closes with Phase 4's row. No matrix commit.

## Review Focus

1. **Spec freeze held.** Check the diff of `sha256.rs`/`hmac.rs`/`hkdf.rs`/`bytes.rs`: every spec fn, const and pub signature/requires/ensures is unchanged (Global Constraints). This is what makes "no upper-crate changes" true.
2. **No hidden escape or trusted helper.**
   - No `external_body` was moved rather than deleted.
   - No vstd escape is used through `crates/`.
   - `shim.rs` no longer has `sha256`/`hmac_sha256`/`hkdf_extract`/`hkdf_expand`.
   - The escape count goes 11 → 11 → 10 → 7.
3. **Padding boundaries.** These are the lengths where an off-by-one hides:
   - `len % 64` ∈ {55, 56, 63, 0};
   - the 128-byte tail case;
   - the bit length as a big-endian **bit** count;
   - HMAC's 64-byte prefix shifting the total length.

   Pinned by `sha256_matches_rustcrypto` (all lengths 0..=300) and `hmac_matches_rustcrypto` (key lengths 0..=130 × the message lengths in Task 3).
4. **HMAC key boundary: `key.len() > 64` hashes, `== 64` does not.** Pinned by `hmac_matches_rustcrypto` (key lengths 63, 64, 65) and RFC 4231 TC6.
5. **HKDF-Expand.**
   - The counter byte is `i as u8` with i from 1.
   - T(1) has no T(0) prefix.
   - The last block is truncated.
   - `len = 0` gives an empty result.

   Pinned by `rfc5869_hkdf`, `hkdf_expand_lengths` and `hkdf_matches_rustcrypto`.
6. **Proof cost.** Check the slowest-function report against the 60 s budget, and that no `rlimit` was added without a reason in the report.

---

### Task 1: SHA-256 word ops, message schedule and compression function

**Files:**
- Modify: `crates/crypto/src/sha256.rs`

**Interfaces:**
- Consumes: `add32`, `rotr`, `ch`, `maj`, `bsig0`, `bsig1`, `ssig0`, `ssig1`, `sha256_w`, `sha256_round`, `sha256_rounds`, `sha256_compress`, `SHA256_K`, `os2ip`.
- Produces (all private to `sha256.rs`):
  - `fn add32_exec(a: u32, b: u32) -> (r: u32) ensures r == add32(a, b)`. The body is `a.wrapping_add(b)`, bridged by `proof fn lemma_wrapping_add32(a: u32, b: u32) ensures vstd::wrapping::u32_specs::wrapping_add(a, b) == add32(a, b)`. If the path differs at this pin, fall back to `((a as u64) + (b as u64)) as u32`.
  - `fn bsig0_exec`, `bsig1_exec`, `ssig0_exec`, `ssig1_exec` `(x: u32) -> (r: u32)`, and `fn ch_exec`, `maj_exec` `(x: u32, y: u32, z: u32) -> (r: u32)`. Each `ensures r == <spec>(…)`, with a body that literally mirrors the spec using literal shift amounts.
    - Try plain unfolding first.
    - Only if the spec's `32 - n` shift amount doesn't match the literal, add one `proof fn bv_rotr_<n>(x: u32) by (bit_vector) ensures (x >> n) | (x << (32 - n)) == (x >> n) | (x << <32-n literal>)` per rotation amount. The rotation amounts are 2, 6, 7, 11, 13, 17, 18, 19, 22 and 25. After unfolding `rotr`, assert the spec side equal to the bv form.
  - `proof fn bv_be32(b0: u32, b1: u32, b2: u32, b3: u32) by (bit_vector)`: requires each `< 256` and ensures `(b0 << 24) | (b1 << 16) | (b2 << 8) | b3 == b0 * 0x100_0000 + b1 * 0x1_0000 + b2 * 0x100 + b3`.
  - `proof fn lemma_os2ip4(s: Seq<u8>)`: requires `s.len() == 4` and ensures `os2ip(s) == s[0] * 0x100_0000 + s[1] * 0x1_0000 + s[2] * 0x100 + s[3]`. Prove it with `reveal_with_fuel(os2ip, 5)` and `drop_last` `=~=` steps.
  - **`fn schedule(src: &[u8], off: usize) -> (w: [u32; 64])`**:
    - `requires off + 64 <= src@.len()`;
    - `ensures forall|j: int| 0 <= j < 64 ==> w@[j] == sha256_w(src@.subrange(off as int, off + 64), j as nat)`;
    - the result is a stack array (no heap). `let ghost block = src@.subrange(off, off + 64)`.
    - **Load loop t in 0..16:** `w[t] = (src[off+4t] as u32) << 24 | …`. The invariant is `forall|j| 0 <= j < t ==> w@[j] == sha256_w(block, j as nat)`. Discharge it with `bv_be32` + `lemma_os2ip4` on `block.subrange(4t, 4t+4)`.
    - **Expand loop t in 16..64:** same invariant. `sha256_w(block, t)` unfolds once (default fuel), to the four earlier entries the invariant already gives.
  - **`fn compress(h: &mut [u32; 8], src: &[u8], off: usize)`**:
    - `requires off + 64 <= src@.len()`;
    - `ensures h@ == sha256_compress(old(h)@, src@.subrange(off as int, off + 64))`;
    - mark it `#[allow(dead_code)]` with a comment saying it is used from Task 2 (`schedule` is used by `compress`, so it needs no allow). Task 2 removes the allow, keeping plain `cargo build` at 0 warnings.
    - Body:
      - `let ghost block = src@.subrange(off, off + 64)`.
      - `let w = schedule(src, off)` (above).
      - **Round loop t in 0..64** over locals `a..hh`, initialised from `h`. The invariant is `seq![a, b, c, d, e, f, g, hh] == sha256_rounds(block, old(h)@, t as nat)`, plus the full-`w` invariant. Each step unfolds `sha256_rounds` once and matches `sha256_round` field by field. `// ponytail:` one round per iteration, as in Global Constraints.
      - **Final:** `h[i] = add32_exec(h[i], v_i)` for the 8 words, then `assert(h@ =~= sha256_compress(old(h)@, block))`.

- [ ] **Step 1:** No new runtime test. `compress` is private and not yet called. The task's check is the proof, plus the 6 existing crypto test files staying green.
- [ ] **Step 2: Implement** the helpers, the lemmas and `compress`, in the order listed.
  - Verify `add32_exec` and the six word helpers in isolation (`--verify-function`) first.
  - Then verify `schedule`.
  - Then verify `compress`.
- [ ] **Step 3:** Run the four checks and the fresh-target-dir evidence run, and report the five slowest functions. Escape count: **11** (unchanged). `rm -rf` the target dir.
- [ ] **Step 4: Commit:** `feat(crypto): verified SHA-256 word ops, schedule and compression (FIPS 180-4 §4.1.2, §6.2.2)`

---

### Task 2: Full SHA-256 exec, shim row removed

**Files:**
- Modify: `crates/crypto/src/sha256.rs`, `crates/crypto/src/shim.rs`, `TRUSTED.md`
- Test: `crates/crypto/tests/sha256.rs`

**Interfaces:**
- Consumes: `compress` (Task 1), `sha256_pad`, `sha256_blocks`, `sha256_words_be`, `spec_sha256`, `i2osp`, `lemma_spec_sha256_len`.
- Produces:
  - `proof fn lemma_pad_block(m: Seq<u8>, k: int)`:
    - requires `0 <= k`, `k + 64 <= m.len()`;
    - ensures `sha256_pad(m).skip(k).take(64) =~= m.subrange(k, k + 64)` and `sha256_pad(m).skip(k).skip(64) =~= sha256_pad(m).skip(k + 64)`.
  - `proof fn lemma_pad_tail(m: Seq<u8>)`. With `base = 64 * (m.len() / 64)` and `n = if m.len() % 64 < 56 { 64 } else { 128 }`, it ensures:
    - `sha256_pad(m).skip(base).len() == n`;
    - for `j < m.len() - base`, byte j is `m[base + j]`;
    - byte `m.len() - base` is `0x80`;
    - bytes up to `n - 8` are 0;
    - the last 8 bytes are `i2osp(8 * m.len(), 8)`.

    This is the one nonlinear step: it shows `(m.len() % 64) + 1 + ((55 - m.len()) % 64) + 8 == n`. Write `m.len() = 64q + r` and use vstd `div_mod` lemmas or `by (nonlinear_arith)`.
  - `proof fn lemma_i2osp_be4(x: u32)`: ensures `i2osp(x as nat, 4) =~= seq![(x >> 24) as u8, (x >> 16) as u8, (x >> 8) as u8, x as u8]`.
  - `proof fn lemma_i2osp_be8(x: u64)`: the same for 8 bytes, with shifts 56, 48, …, 0.
  - Prove both with `reveal_with_fuel(i2osp, N+1)` and `proof fn bv_div256_u32` / `bv_div256_u64` (`x / 256 == x >> 8`, `(x % 256) as u8 == x as u8`) by (bit_vector).
  - `fn words_be(h: &[u32; 8]) -> (r: [u8; 32]) ensures r@ == sha256_words_be(h@)`. It is a loop i in 0..8 with the invariant `r@.take(4 * i) == sha256_words_be(h@.take(i))`. The step uses `h@.take(i + 1).drop_last() =~= h@.take(i)` and `lemma_i2osp_be4`.
  - **`pub(crate) fn sha256_cat(prefix: &[u8], msg: &[u8]) -> (r: [u8; 32])`**:
    - requires `prefix@.len() == 0 || prefix@.len() == 64` and `prefix@.len() + msg@.len() < 0x2000_0000_0000_0000`;
    - ensures `r@ == spec_sha256(prefix@ + msg@)`.
    - Body, with `let ghost m = prefix@ + msg@` and `h = SHA256_H0`:
      - **Suffix-form invariant** for every block step: `sha256_blocks(h@, sha256_pad(m).skip(k)) == sha256_blocks(SHA256_H0@, sha256_pad(m))`. k is the bytes consumed so far, starting at `skip(0) =~= sha256_pad(m)`.
      - **Prefix:** if `prefix.len() == 64`, then `compress(&mut h, prefix, 0)`, which takes k from 0 to 64 (`lemma_pad_block(m, 0)`).
      - **Message blocks:** `off` in steps of 64 while `off + 64 <= msg.len()`, calling `compress(&mut h, msg, off)` with k = `prefix.len() + off`, via `lemma_pad_block` and `m.subrange(k, k+64) =~= msg@.subrange(off, off+64)`.
      - **Tail:**
        - `let mut buf = [0u8; 128]`;
        - copy the `r = msg.len() - off` remaining bytes;
        - `buf[r] = 0x80`;
        - write `bits = 8 * (prefix.len() + msg.len()) as u64` big-endian into `buf[n-8..n]` (`lemma_i2osp_be8`);
        - `compress(&mut h, &buf, 0)` and, if `n == 128`, `compress(&mut h, &buf, 64)`.
        
        `lemma_pad_tail` gives `sha256_pad(m).skip(base) =~= buf@.take(n)`. Then unfold `sha256_blocks` one or two more levels, down to the empty remainder.
      - **Output:** `words_be(&h)`.
  - `pub fn sha256(msg: &[u8]) -> (r: [u8; 32])`:
    - delete `#[verifier::external_body]` and the `/// Trusted shim…` line;
    - the new doc is `/// FIPS 180-4 §6.2; verified against spec_sha256.`;
    - the body is `sha256_cat(&[], msg)`, plus `assert(Seq::<u8>::empty() + msg@ =~= msg@)`. Use `&[0u8; 0]` if `&[]` doesn't infer.
    - The signature, `requires` and `ensures` are untouched.
  - Remove `#[allow(dead_code)]` from `compress`.
  - Update the module doc to say verified, not shim-backed.
- `shim.rs`:
  - delete `pub(crate) fn sha256`;
  - keep `use sha2::{Digest, Sha256};`, because `rsa_pss_sign` uses both;
  - keep `sha2` in `Cargo.toml`, because the RSA shim and `tests/rsa_pss.rs` use it.
- `TRUSTED.md`:
  - delete the `| crypto::sha256::sha256: …` row (line 30);
  - in the row "Constants `SHA256_K`, `SHA256_H0` and the SHA-256 specs", replace `spec fns not machine-checked until phase 5` with `spec fns checked against FIPS 180-4 and RustCrypto sha2 vectors through the verified exec (tests/sha256.rs) since phase 5a`.

- [ ] **Step 1: New tests** in `crates/crypto/tests/sha256.rs`. The existing `fips180_examples` and `sha256_constants_from_roots` stay.
  - `sha256_matches_rustcrypto`: for each `len` in `0..=300`, take message bytes `(i * 31 + 7) as u8` and require `sha256(&m) == <sha2::Sha256 as sha2::Digest>::digest(&m).into()`.
  - `sha256_1mib`:
    - 1 MiB (1 << 20 bytes) of the same pattern;
    - the result equals `sha2`'s;
    - `std::time::Instant` elapsed is `< 2 s`. That bound is generous enough for a debug build, so the test runs unconditionally.
    - This doubles as the throughput sanity check. Skipped: a real benchmark harness. Add one when 4c/interop shows hashing on a profile.
- [ ] **Step 2:** Run the tests against the shim first: all pass. That confirms the test is right, and confirms the differential agrees with today's trusted body.
- [ ] **Step 3: Implement** the lemmas, `words_be`, `sha256_cat` and the new `sha256` body. Then the shim and TRUSTED edits, in the same commit.
- [ ] **Step 4:** Run the four checks and the fresh-target-dir evidence run, and report the five slowest functions. `cargo test -p crypto`: 4 sha256 tests pass, plus all other crypto tests. Escape count: **10**. `rm -rf` the target dir.
- [ ] **Step 5: Commit:** `feat(crypto): verified SHA-256 exec replaces sha2 shim (FIPS 180-4 §5.1.1, §6.2)`

---

### Task 3: HMAC-SHA256 and HKDF exec; shim fns, rows and direct deps removed

**Files:**
- Modify: `crates/crypto/src/hmac.rs`, `crates/crypto/src/hkdf.rs`, `crates/crypto/src/shim.rs`, `crates/crypto/Cargo.toml`, `Cargo.lock`, `TRUSTED.md`
- Test: `crates/crypto/tests/hmac_hkdf.rs`

**Interfaces:**
- Consumes: `sha256`, `sha256_cat`, `lemma_spec_sha256_len`, `hmac_k0`, `spec_hmac_sha256`, `xor_bytes`, `hkdf_t`, `hkdf_t_cat`, `lemma_hkdf_t_len`, `lemma_hkdf_t_cat_len`.
- Produces (`hmac.rs`):
  - `proof fn lemma_hmac_k0(key: Seq<u8>)`. It ensures `hmac_k0(key).len() == 64`, and for each `j < 64`, `hmac_k0(key)[j]` is:
    - `spec_sha256(key)[j]` if `key.len() > 64 && j < 32`;
    - `key[j]` if `key.len() <= 64 && j < key.len()`;
    - 0 otherwise.

    It uses `lemma_spec_sha256_len`.
  - **`pub(crate) fn hmac_sha256_core(key: &[u8], msg: &[u8]) -> (r: [u8; 32])`**:
    - requires `key@.len() <= MAX_INPUT_LEN` and `msg@.len() + 64 < 0x2000_0000_0000_0000`;
    - ensures `r@ == spec_hmac_sha256(key@, msg@)`.
    - Body:
      - if `key.len() > 64`, then `kh = sha256(key)`;
      - one loop j in 0..64 fills `ipad: [u8; 64]` and `opad: [u8; 64]` with `k0[j] ^ 0x36` and `k0[j] ^ 0x5c`. The invariant is against `xor_bytes(hmac_k0(key@), Seq::new(64, |i| 0x36u8))[i]` and the matching `0x5c` form;
      - `inner = sha256_cat(&ipad, msg)`;
      - `r = sha256_cat(&opad, &inner)`.
    - No heap.
  - `pub fn hmac_sha256`:
    - attribute and shim doc line deleted;
    - the doc is `/// RFC 2104 §2 (B = 64, L = 32); verified against spec_hmac_sha256.`;
    - the body is `hmac_sha256_core(key, msg)`;
    - signature unchanged.
- Produces (`hkdf.rs`):
  - `pub fn hkdf_extract`:
    - attribute and doc line deleted;
    - the body is `hmac_sha256(salt, ikm)`, which `spec_hkdf_extract` unfolds to.
  - `pub fn hkdf_expand`: attribute and doc line deleted. The body:
    - `let n = (len + 31) / 32`, which is ≤ 255. The loop counter `i` is a `usize` with `1 <= i <= n <= 255` in the invariant, and is cast with `i as u8` only at the counter byte;
    - `out = Vec::with_capacity(len)`;
    - `buf` = 32 zero bytes, then `extend_from_slice(info)`, then `push(1)`. It is the reused `T(i−1) ‖ info ‖ i` buffer.
    - **For i = 1:** `t = hmac_sha256_core(prk, slice_subrange(buf.as_slice(), 32, buf.len()))`, since T(0) is empty.
    - **For i ≥ 2:** `buf.set(j, t[j])` for j < 32 and `buf.set(last, i as u8)`, then `t = hmac_sha256_core(prk, buf.as_slice())`.
    - After each T(i), push `min(32, len − out.len())` bytes of `t`.
    - The invariants are `t@ == hkdf_t(prk@, info@, i)`, `out.len() == min(len, 32 * i)` and `out@ == hkdf_t_cat(prk@, info@, i).take(out.len())`.
    - The final ensures follows from `spec_hkdf_expand` = `hkdf_t_cat(…, n).take(len)`.
    - `// ponytail:` info is copied once into `buf`. A streaming HMAC would avoid the copy if `info` ever gets large; TLS HkdfLabel is ≤ 520 bytes.
  - Update the `spec_hkdf_extract` doc comment's "(not machine-checked here; tests/hmac_hkdf.rs exercises the shim only)" to say the empty-salt equivalence is checked by `rfc5869_hkdf` through the verified exec. This is a comment-only edit.
- `shim.rs`: delete `hmac_sha256`, `hkdf_extract` and `hkdf_expand`. `sha2` stays, for RSA.
- `Cargo.toml`:
  - move the `hmac` and `hkdf` lines from `[dependencies]` to `[dev-dependencies]`, verbatim except for the trailing comment, which becomes `# 5a differential tests`;
  - both stay in `Cargo.lock` regardless (rfc6979 → hmac, elliptic-curve → hkdf, via p256);
  - zero new crates in the lockfile diff.
- `TRUSTED.md`:
  - delete the three rows `crypto::hmac::hmac_sha256`, `crypto::hkdf::hkdf_extract` and `crypto::hkdf::hkdf_expand` (originally lines 31–33; 30–32 after Task 2);
  - in "Pinned versions", the RustCrypto shim line drops `hmac =0.13.0, hkdf =0.13.0` from the direct list and adds them under dev (`dev: primeorder =0.14.0, rsa with hazmat, hmac =0.13.0, hkdf =0.13.0`) and to the transitive list;
  - the "HMAC/HKDF specs" row's `not machine-checked until phase 5` becomes `checked against RFC 4231/5869 and RustCrypto vectors through the verified exec (tests/hmac_hkdf.rs) since phase 5a`;
  - the `shim.rs` row stays, since AES, GCM, P-256, ECDSA and RSA remain.

- [ ] **Step 1: New tests** in `crates/crypto/tests/hmac_hkdf.rs`. The existing `rfc4231_hmac`, `rfc5869_hkdf` and `hkdf_expand_lengths` stay.
  - `hmac_matches_rustcrypto`: for each key length `0..=130` (63, 64 and 65 are the boundary) and each message length in `[0, 1, 55, 56, 63, 64, 65, 119, 120, 300]`, compare against `<hmac::Hmac<sha2::Sha256> as hmac::KeyInit>::new_from_slice` + `Mac::update` + `finalize`. Use pattern bytes for key and message.
  - `hkdf_matches_rustcrypto`:
    - extract: for each salt length `0..=130`, against `hkdf::Hkdf::<sha2::Sha256>::extract(Some(salt), ikm).0`;
    - expand: for each `len` in `[0, 1, 31, 32, 33, 64, 65, 8159, 8160]` and each info length in `[0, 1, 300]`, against `Hkdf::from_prk(prk).expand`.
  - Skipped: Wycheproof `hmac_sha256_test.json` / `hkdf_sha256_test.json`. They need a JSON dev-dependency, and the differential above covers the same boundaries. They go to the Phase 5 exit, where the design lists CAVP + Wycheproof.
- [ ] **Step 2:** Run against the shim first: all pass.
- [ ] **Step 3: Implement** `lemma_hmac_k0`, `hmac_sha256_core`, the three public bodies, and the shim, Cargo and TRUSTED edits, all in one commit.
- [ ] **Step 4:** Run the four checks and the fresh-target-dir evidence run.
  - `cargo test -p crypto`: 5 hmac/hkdf tests pass, plus all others.
  - `cargo tree -p crypto -e normal --depth 1 | grep -E ' (hmac|hkdf) v'` prints nothing: they are no longer direct normal deps.
  - Escape count: **7**.
  - `rm -rf` the target dir.
- [ ] **Step 5: Commit:** `feat(crypto): verified HMAC-SHA256 and HKDF exec replace shim (RFC 2104 §2, RFC 5869 §2.2-2.3)`

---

## Exit criteria (Phase 5a)

- All four checks pass on the merged tree. `verify.sh` prints `escapes accounted (7)`.
- TRUSTED.md has no `crypto::sha256::`, `crypto::hmac::` or `crypto::hkdf::` rows. Both spec rows are reworded, the pins line is updated and the `shim.rs` row remains.
- `shim.rs` contains no SHA-256/HMAC/HKDF function. `hmac`/`hkdf` are dev-dependencies only, and `sha2` stays for the RSA shim.
- The spec-freeze diff check passes for `sha256.rs`, `hmac.rs`, `hkdf.rs` and `bytes.rs`.
- `phase-5a` is merged into `main`.

## Self-review (done while writing)

- **Scope.** There are exactly four functions. No streaming hash (Architecture: 4b rehashes one-shot). No AES/GCM/P-256, which are 5b+.
- **Preconditions chain.** Public `sha256` and `hmac_sha256` keep `MAX_INPUT_LEN`. The internal cores take the 2⁶¹-byte hash bound, which covers HMAC's +64 and HKDF's +33.
- **No compute_only anywhere.** Vectors are checked only by `cargo test`.
- **Proportion.** Signatures, invariants and lemma names only. Lemma internals are spelled out only where the signature doesn't fix the strategy: the suffix-form block invariant, the pad-tail length arithmetic, and the round loop's one-step unfolding.
