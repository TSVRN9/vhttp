# Phase 5b: Verified AES-128 and AES-128-GCM — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the three RustCrypto-backed `#[verifier::external_body]` exec fns below with verified Verus exec code. Each keeps its 3a signature, `requires` and `ensures` byte for byte.
- `crypto::aes::aes128_encrypt_block`
- `crypto::gcm::aes128_gcm_seal`
- `crypto::gcm::aes128_gcm_open`

TRUSTED.md rows `crypto::aes::aes128_encrypt_block`, `crypto::gcm::aes128_gcm_seal` and `crypto::gcm::aes128_gcm_open` go. The crypto escape count drops 7 → 6 → 4. No crate on `main` depends on `crypto`. Phase 3e's planned `quic::{hp, aead}` consume exactly these three signatures, so nothing upstream changes.

**Branch:** `phase-5b`, cut from `main` **after `phase-5a` merges**. Everything below assumes 5a's code is present: `sha256.rs` exec, `lemma_os2ip4`, `lemma_i2osp_be4/be8`, `bv_div256_*`, `add32_exec`, and the `verify.sh` count of 7.

**Architecture:**
- **`aes.rs`** gains private exec code under the frozen specs:
  - GF(2⁸) ops: `xtime_ct` and `gmul_ct`, branch-free.
  - A **computed, table-free S-box**: x²⁵⁴ by a 13-multiply chain, then the affine map. It is proved equal to the spec's `sbox` on all 256 inputs by 16 `by (compute_only)` chunk lemmas (D1).
  - The four round transforms, `expand_key` (`pub(crate)`, `[u8; 176]` on the stack), and `encrypt_rk` (`pub(crate)`).
  - `aes128_encrypt_block` = `expand_key` + `encrypt_rk`.
- **`gcm.rs`** gains private exec code:
  - `gf128_mul_exec`, the 128-step SP 800-38D Algorithm 1 loop on `u128` (D3);
  - `load_be128` / `store_be128`;
  - `ghash_padded`, which feeds `data ‖ 0^pad` into a running GHASH against one ghost concatenation and never builds it;
  - `ctr_block`, `gctr_append` (a `u32` counter with `wrapping_add`) and `gcm_tag_exec`.
  - Seal and open each expand the key **once** and share `gctr_append` and `gcm_tag_exec`.
- **Allocation:** seal allocates one `Vec` (`with_capacity(pt.len() + 16)`). Open allocates one `Vec` (`with_capacity(c.len())`), and only after the tag matches. Every per-block temporary is a `[u8; 16]` or a `u128` on the stack. No other heap use.
- **No public pre-expanded-key API** (D2).

**Tech Stack:** Verus 0.2026.10.04.426d8b0 (`~/.local/opt/verus/0.2026.10.04.426d8b0/verus-x86-linux`), vstd `=0.0.0-2026-10-04-0306`. No new crates; `aes`/`aes-gcm` move to dev-dependencies.

**Spec:** `docs/superpowers/specs/2026-10-27-verified-http3-design.md`, Phase 5, in the order SHA-256 → HMAC → HKDF → **AES-128 → GCM** → P-256…. It says "bit-vector and nonlinear arithmetic proofs come in small lemma steps". The constant-time line is a non-goal for *proof*, but the code is written "in a constant-time style" (Goals, line 32).

## Decisions (recorded)

- **D1. The S-box is computed, not a table.**
  - **The spec is algebraic.** `sbox(b) = sbox_bits(gpow(b, 254), 8)` (aes.rs:48–73), so a 256-entry table is *not* trivially equal to it. A table and a computed S-box both need the same 256-entry compute proof, so proof cost doesn't separate them.
  - **Timing separates them.** A table indexed by key or state bytes is the textbook cache-timing leak, and the design's constant-time style forbids it.
  - **Exec:** `sbox_ct(x) = affine_exec(ginv_chain_exec(x))`.
    - `ginv_chain_exec` computes x², x³, x⁶, x⁷, x¹⁴, x¹⁵, x³⁰, x³¹, x⁶², x⁶³, x¹²⁶, x¹²⁷, x²⁵⁴ with 13 calls to `gmul_ct`.
    - `affine_exec` is `x ^ rotl1 ^ rotl2 ^ rotl3 ^ rotl4 ^ 0x63` with literal shifts.
  - **Proof:** private spec helpers `ginv_chain`/`affine` mirror the exec. `lemma_sbox_chain(x: u8)` gives `affine(ginv_chain(x)) == sbox(x)` from 16 chunk lemmas of 16 inputs each, each one `by (compute_only)`.
  - **Planner probe, 2026-10-28.** This was run in a `git archive` copy of `wt-5a` with the real `crate::aes::sbox`:
    - `cargo verus verify` gave crypto **102 verified, 0 errors**;
    - crypto took 16.7 s wall (7 threads), 20.6 s CPU;
    - each chunk takes ~1.3 s;
    - a negative control `sbox(0x53) == 0xee` is rejected with `expression simplifies to 237 == 238`.
    - Standalone, `xtime(0x57) == 0xae`, `gmul(0x57, 0x13) == 0xfe` and `sbox(0x53) == 0xed` each take < 1 s.
  - **Chunk size is forced.** The evaluator has an internal timeout of about 3 s that `#[verifier::rlimit(infinity)]` does not lift. All 256 inputs in one assert fails; 16 or 32 inputs per assert pass.
  - **Why 3a timed out:**
    - its in-crate probes, even `p_trivial` and `p_xtime`, hit 240 s;
    - its logs show the rejected `--verify-module` + `--verify-function` combination, and a fresh target dir that first verifies vstd (~23 s wall, 80 s CPU);
    - so the 3a harness is the likely cause, not the evaluator.
  - **Named fallback.** Use it only if Task 1's in-crate re-run fails or any chunk takes over 60 s.
    - `ginv_slow`: a fixed 254-step `gmul_ct` loop with the invariant `r == gpow(b, i)`, using one-step unfolding of `gpow`;
    - `bv_affine`: `affine(x) == sbox_bits(x, 8)` after `reveal_with_fuel(sbox_bits, 9)`;
    - no compute at all. It is about 20× slower, and its `ponytail:` note says so.
    - Do not improvise a third route; escalate instead.
  - **Ceiling.** The note on `sbox_ct` is `// ponytail: S-box = 13 constant-time GF(2^8) multiplies (8 masked steps each) + affine, ≈<measured> µs per AES block (release, Task 5 gcm_64kib); upgrade: Boyar–Peralta bitsliced circuit, proved by the same chunk lemmas, or AES-NI behind an equivalence proof`.
- **D2. Key expansion runs per call; there is no pre-expanded public API.**
  - The frozen signatures take `key: &[u8]` per call.
  - Per the Phase 3e plan, QUIC calls `aes128_encrypt_block(hp, sample)` once per packet for header protection (`rfc_hp_mask`). It calls `aes128_gcm_seal`/`open` once per packet through `seal_packet`/`open_packet(k: &PacketKeys, …)`, which pass key slices.
  - So each packet pays two expansions: 40 S-boxes each, about ¼ of one block.
  - A `pub` expanded-key type would change 3e/quic signatures. YAGNI.
  - Internally, seal and open call `expand_key` once and reuse the `[u8; 176]` for every block, including H and E(J0).
  - The note on `aes128_encrypt_block` is `// ponytail: key schedule recomputed per call (40 S-boxes, ≈<measured>% of one block); add a pub expanded-key type if packet-rate profiling shows it`.
- **D3. GHASH is the bitwise GF(2¹²⁸) multiply of SP 800-38D Algorithm 1.**
  - It is one `u128` loop of 128 iterations, mirroring `gf128_loop` (gcm.rs:194–212).
  - The bit is `(x >> (127 - i)) & 1`.
  - Both selects are mask multiplies, with no branch and no table.
  - One `bv_gf128_step` lemma covers both selects.
  - The note is `// ponytail: 128 masked shift/xor steps per 16-byte block, ≈<measured> µs/block; upgrade: carry-less multiply (PCLMULQDQ) behind an equivalence lemma. 4-bit Shoup tables are faster but index by H, so not constant-time style`.
- **D4. GCTR, J0, the length block and the tag.**
  - **GCTR:** the counter block is `nonce ‖ be32(c)`, built on the stack per block. `c: u32` advances by `wrapping_add(1)`, which mirrors `inc32`'s `mod 2^32` exactly, so no no-wrap argument is needed.
  - **J0 and the payload counter:** J0 = `nonce ‖ be32(1)` (`gcm_j0`, 96-bit IV only). The payload starts at `c = 2`, which is `inc32(J0)`.
  - **Length block:** `be64(8·|A|) ‖ be64(8·|C|)`, both **bit** counts, written into a stack `[u8; 16]` with 5a's `lemma_i2osp_be8` and loaded with `load_be128`. `8·|A| ≤ 2⁶³` because `aad ≤ MAX_INPUT_LEN = 2⁶⁰`.
  - **Tag:** `E_K(J0) ⊕ store_be128(S)`. This is `gctr` on one full block, which unfolds twice.
- **D5. Open checks the tag before it decrypts, and compares in constant-time style.**
  1. `ct.len() < 16` returns `None`.
  2. `c = slice_subrange(ct, 0, len − 16)`, with no copy. `t = gcm_tag_exec(…, c)`.
  3. `diff |= ct[len−16+i] ^ t[i]` for all 16 i, with no early exit (`bv_ctacc`).
  4. `if diff != 0 { return None }`. Only then allocate and decrypt.

  So no plaintext byte is computed, let alone returned, on a mismatch. The only data-dependent branch reveals accept/reject, which is public.
- **D6. Constant-time style rule for all new exec code.** No branch, loop bound or memory index may depend on key, state, plaintext, H, S or tag bytes. Branches and indices may depend only on lengths, offsets and the loop counter. This is reviewed by reading, since Verus can't check it (design non-goal; dudect later). Rust/LLVM may still introduce branches; that is out of scope.

## Global Constraints

- **Spec freeze.** Nothing in this list may change:
  - any `spec fn` body or signature;
  - any `const` (`GCM_MAX_PT_LEN`, `MAX_INPUT_LEN`, `SHA256_K`, `SHA256_H0`);
  - any `pub` exec signature, `requires` or `ensures`, in `aes.rs`, `gcm.rs`, `bytes.rs` and `sha256.rs`.

  Allowed additions:
  - new proof fns;
  - private or `pub(crate)` exec fns;
  - private or `pub(crate)` helper `spec fn`s that no trusted spec references (`sq`, `ginv_chain`, `affine`, `sbox_chunk_ok`, `rk_ok`).

  Allowed edits:
  - doc comments;
  - in `sha256.rs`, **visibility only**: `lemma_os2ip4`, `lemma_i2osp_be4` and `lemma_i2osp_be8` become `pub(crate)`. Reuse them; don't copy them.

  Before each commit, the `git diff` of those four files must show only those kinds of change.
- **Specs meet vectors for the first time.** The 3a check was an independent Python transcription. Phase 5b is the first time the specs meet FIPS 197 / SP 800-38D / RFC 9001 vectors through a proof, via `cargo test` on the verified exec. If a vector test fails after verification passes, the spec is wrong (or the vector is). Stop and escalate with the failing input. **Never edit a spec** to make a test pass.
- **Escapes:**
  - add none;
  - `scripts/verify.sh` counts every `#[verifier::external_body]` line in `crates/crypto/src/` and requires the count to equal the number of `| crypto::` rows in TRUSTED.md;
  - the commit that deletes an attribute also deletes its row;
  - the grep also matches the bare words `assume(`, `admit(` and `axiom` in comments, so delete the `/// Trusted shim: …` doc lines outright, and never name a lemma `*assume*`/`*axiom*`.

  `rlimit`, `spinoff_prover`, `hide` and `reveal_with_fuel` are not escapes. Every `rlimit` goes in the task report with its measured time.
- **`by (compute_only)`:**
  - **Allowed only** in `lemma_sbox_chunk_0` … `lemma_sbox_chunk_15`, plus the Task 1 scratch probes.
  - **Never** on `spec_aes128_encrypt`, `key_word`, `round_key`, `gf128_*`, `ghash`, `gctr` or `gcm_*`. `key_word` recurses on both `i−1` and `i−4`, which is exponential, and these were the 3a timeouts.
  - Compute assertions are evaluated even under `--verify-function` filtering. One failing compute assert breaks every focused run in the crate, so revert negative controls at once.
- **Proof patterns that worked in 5a:**
  - **Loops** carry a loop invariant with **one-step unfolding** of the trusted recursive spec (`gmul_n`, `aes128_rounds`, `key_word`, `gf128_loop`, `ghash`, `gctr`, `os2ip`). Never unroll 10 rounds or 128 steps.
  - **`hide()`** the big spec fns a proof doesn't need. Mandatory hides:
    - `key_word` and `sbox` in `encrypt_rk`;
    - `sbox` in `expand_key`;
    - `spec_aes128_encrypt` and `gf128_mul` in every gcm.rs exec fn except `gf128_mul_exec`;
    - `key_word` wherever `rk_ok` is in scope at GCM level.
  - **`by (bit_vector)`** only in small standalone `proof fn bv_*` lemmas, in `crates/wire/src/varint.rs` style.
    - Parenthesize `^`, `&` and `|` before `==`. Rust parses `a ^ b == c` as `a ^ (b == c)`.
    - Cast spec products back to their width: `((b >> 7) * 0x1b) as u8`.
    - The planner probe verified `bv_xtime`, `bv_sel8`, `bv_gf128_step`, `bv_ctacc`, `bv_be128_step`, `bv_div256_u128` and `lemma_i2osp_be16` in that form, each < 0.5 s.
- **Exec mirrors spec argument order.**
  - `mix_columns` uses `gmul(2, s[…])`, with the state byte as the **second** argument. So the exec calls `gmul_ct(2, s[…])` and `gmul_ct(3, s[…])`, not `xtime(s)`, which would need commutativity.
  - The xor order follows the spec expression left to right.
  - `ginv_chain_exec` uses the helper spec's exact argument order (`gmul(x2, x)`, not `gmul(x, x2)`).
- **Pin facts from 5a:**
  - `&mut` post-states in `ensures` are spelled `final(x)@`;
  - array writes are `a[i] = v` (`ArrayAdditionalExecFns::set` is deprecated and warns);
  - offset arithmetic needs an exec-length invariant (`off + 16 <= src.len()`), not only `src@.len()`;
  - `vstd::wrapping::u32_specs::wrapping_add` exists, and an empty-body bridge lemma suffices (5a `lemma_wrapping_add32`);
  - there is no vstd spec for `rotate_left`, `to_be_bytes` or `from_be_bytes`, so use literal shifts.
- **Citations:**
  - FIPS 197 and SP 800-38D are not tracked in `.duvet/config.toml`, so citations are plain `//` comments (e.g. `// SP 800-38D §6.3 Algorithm 1`);
  - write **zero** `//=` / `//#` lines;
  - spec imports stay glob-only under `#[allow(unused_imports)]`.
- **The four checks, every task:**
  1. `scripts/verify.sh` prints `verify.sh: all crates verified, duvet ok, escapes accounted (N)`, with N given per task;
  2. `cargo build && cargo test` pass with 0 warnings;
  3. the escape grep prints only N `crates/crypto/src/*.rs:L:#[verifier::external_body]` lines;
  4. `duvet report` exits 0 (inside verify.sh).
- **Evidence run:**
  - `CARGO_TARGET_DIR=/tmp/claude-1000/-home-tavern-Projects-rust-web-server/19d690a3-7cab-4802-bc1f-9aa0173a905e/scratchpad/vt-5b-tN scripts/verify.sh`. The path must be absolute, and the output must show crypto `verification results:: … 0 errors`.
  - **Then `rm -rf` the dir.** The tmpfs is shared and capped at 16 GB.
  - While iterating, use `cargo verus focus -- --verify-only-module aes` (or `gcm`), adding `--verify-function f` when needed. `--verify-module` with `--verify-function` is rejected.
- **Proof-time budget:**
  - every report lists the five slowest functions (`--output-json --time-expanded`) and crypto's total wall time;
  - no single function may exceed 60 s; split it or use `spinoff_prover`, and never raise the rlimit globally;
  - the S-box chunks are expected at ~1.3 s each and ~20 s crypto wall in total; every other new function is expected under 1 s, as in 5a.

## Matrix rows this plan touches

None. `docs/requirements.md` has no AES/GCM-primitive row. RFC 9001 §5.3/§5.4 rows close with Phase 3e/4. No matrix commit.

## Review Focus

1. **Spec freeze held.**
   - Diff `aes.rs`/`gcm.rs`/`bytes.rs`/`sha256.rs`.
   - Every pre-existing `spec fn`, const and pub signature/requires/ensures is unchanged.
   - sha256.rs changes only the three visibilities.
2. **No hidden escape or trusted helper.**
   - `shim.rs` has no `aes128_*` fn.
   - No `external_body` moved.
   - `compute_only` appears only in the 16 chunk lemmas.
   - The count goes 7 → 7 → 6 → 6 → 4.
   - The new helper specs (`ginv_chain`, `affine`, `rk_ok`, …) are referenced by no trusted spec.
3. **Constant-time style (D6), by reading.**
   - There is no `if`/`match`/`&&`-short-circuit or index on secret bytes in `xtime_ct`, `gmul_ct`, `sbox_ct`, the round fns, `expand_key`, `gf128_mul_exec` or the tag compare.
   - There is no S-box table anywhere.
   - Open's compare has no early exit, and it decrypts only after the compare.
4. **Mutations must fail on a named assertion or invariant, not on `rlimit`.** The 5a Task 3 reviewer flagged that rlimit-only rejections can't tell wrong from slow. Where a mutation shows only rlimit, the implementer adds an intermediate `assert` naming the step and re-runs. Implementers run every one of these; the reviewer runs two of their own choice.
   - AES:
     - `xtime` constant `0x1b` → `0x1d`;
     - `gmul_ct` mask on `bb >> 1`;
     - ShiftRows `+ (i % 4)` → `−`;
     - MixColumns `gmul_ct(2,·)`/`gmul_ct(3,·)` swapped;
     - MixColumns applied in the final round;
     - `rot_word` rotated the other way;
     - `rcon` advanced one word early;
     - round-key offset `16·r` → `16·(r+1)`.
   - GCM:
     - payload counter starting at 1 (J0) instead of 2;
     - length block halves swapped;
     - byte counts instead of bit counts;
     - pad 16 on an exact multiple of 16;
     - `0xE1 << 120` → `0xE1 << 112`;
     - bit index `127 − i` → `i`;
     - a 15-byte tag-compare loop;
     - aad and c GHASH order swapped.
5. **Vectors run the verified code.**
   - FIPS 197 App. B and C.1, GCM spec TC1–TC4 (96-bit IV), RFC 9001 A.2/A.3 (HP masks and AEAD) and the RustCrypto differentials all call `crypto::aes`/`crypto::gcm`.
   - After Task 5, nothing reaches a shim.
6. **Proof cost and `ponytail:` notes.**
   - Every note on the three ceilings (D1–D3) states a **measured** number from Task 5's `gcm_64kib`. Commit c55b497 was a review fix for exactly an unmeasured ceiling claim.
   - Check the slowest-function list against the 60 s budget.

---

### Task 1: Spec sanity gate (no commit)

Establish cheaply, before writing exec code, that the frozen specs match the standards and that the D1 proof route works in the crate.

**Files:** none in the worktree. The scratch copies go under the scratchpad.

- [ ] **Step 1: The specs are unchanged since 3a's review.** `git diff e2a5175 -- crates/crypto/src/{aes,gcm,bytes}.rs` must show only doc-comment lines plus `lemma_i2osp_len`. e2a5175 is the commit the 3a reviewer's transcription was written against.
- [ ] **Step 2: Re-run the 3a independent transcription.**
  - Command: `python3 -I <scratch>/rev3/t.py <scratch>/probe-5b/tbl/sbox.txt`.
  - The table file is FIPS 197 Table 4, `sed -n 846,861p <scratch>/src-docs/fips197.txt`. Re-extract it if it is missing.
  - Expect `FAILS 0` and four `mutant … detected` lines, in about 1 s.
  - It covers:
    - the S-box against Table 4;
    - rcon, xtime and gmul;
    - FIPS 197 C.1 and App. B;
    - GCM TC1–TC4;
    - 60 random ECB and 150 random GCM seal/open/tamper cases against Python `cryptography`;
    - inc32 wrap.
  - Read each `def` in t.py once against the current spec text, to confirm it is still a literal transcription.
- [ ] **Step 3: In-crate compute probe, bounded at 60 s per probe.**
  - Make the copy with `git archive HEAD | tar -x -C <scratch>/probe-5b-crate`, so the worktree is untouched.
  - Paste the D1 helper specs and the 16 chunk lemmas into the copy's `aes.rs`, plus:
    - `assert(xtime(0x57) == 0xae) by (compute_only)`;
    - the negative control `assert(sbox(0x53) == 0xee) by (compute_only)`, run once and expected to fail with `237 == 238`, then removed.
  - Run `cargo verus verify -- --time` with a fresh absolute `CARGO_TARGET_DIR`.
  - Expected: crypto `0 errors`, ~17 s wall (planner run: 102 verified).
  - **If any probe exceeds 60 s or fails, take the D1 fallback in Task 2 and say so in the report.**
  - `rm -rf` the copy and the target dir.
- [ ] **Step 4: Report.** Record the outputs of Steps 1–3, the timings, and the S-box route chosen (primary or fallback). Escape count: **7**. No commit.

---

### Task 2: GF(2⁸) arithmetic and the constant-time S-box

**Files:**
- Modify: `crates/crypto/src/aes.rs`

**Interfaces** (all private to `aes.rs`; `// FIPS 197 §…` comments):
- `proof fn bv_xtime(b: u8) by (bit_vector)` ensures:
  - `(b >> 7) * 0x1b <= 0x1b`;
  - `((b << 1) ^ (((b >> 7) * 0x1b) as u8)) == (if b & 0x80 != 0 { ((b & 0x7f) << 1) ^ 0x1b } else { b << 1 })`.
- `fn xtime_ct(b: u8) -> (r: u8) ensures r == xtime(b)`. The body is `(b << 1) ^ ((b >> 7) * 0x1b)`.
- `proof fn bv_sel8(a: u8, b: u8) by (bit_vector)` ensures `(b & 1) * 0xff <= 0xff` and `(a & (((b & 1) * 0xff) as u8)) == (if b & 1 == 1 { a } else { 0u8 })`.
- `proof fn bv_xor8(p: u8, q: u8, s: u8) by (bit_vector)` ensures `((p ^ q) ^ s) == (p ^ (q ^ s))` and `(p ^ 0u8) == p`.
- **`fn gmul_ct(a: u8, b: u8) -> (r: u8) ensures r == gmul(a, b)`.**
  - 8 iterations over `acc`, `aa`, `bb`;
  - the invariant is `(acc ^ gmul_n(aa, bb, (8 - i) as nat)) == gmul(a, b)`;
  - the step is `acc = acc ^ (aa & ((bb & 1) * 0xff))`, `aa = xtime_ct(aa)`, `bb = bb >> 1`, unfolding `gmul_n` once.
- Private helper specs, written exactly as the planner probe had them:
  - `spec fn sq(x: u8) -> u8 { gmul(x, x) }`;
  - `spec fn ginv_chain(x: u8) -> u8`: `x2 = sq(x)`, `x3 = gmul(x2, x)`, `x6 = sq(x3)`, `x7 = gmul(x6, x)`, `x14 = sq(x7)`, `x15 = gmul(x14, x)`, `x30 = sq(x15)`, `x31 = gmul(x30, x)`, `x62 = sq(x31)`, `x63 = gmul(x62, x)`, `x126 = sq(x63)`, `x127 = gmul(x126, x)`, result `sq(x127)`;
  - `spec fn affine(x: u8) -> u8 { x ^ ((x << 1) | (x >> 7)) ^ ((x << 2) | (x >> 6)) ^ ((x << 3) | (x >> 5)) ^ ((x << 4) | (x >> 4)) ^ 0x63 }`;
  - `spec fn sbox_chunk_ok(lo: nat, hi: nat) -> bool decreases hi - lo`: true if `lo >= hi`, else `affine(ginv_chain(lo as u8)) == sbox(lo as u8) && sbox_chunk_ok(lo + 1, hi)`.
- **The compute lemmas:**
  - `proof fn lemma_sbox_chunk_K() ensures sbox_chunk_ok(16K, 16K + 16) { assert(sbox_chunk_ok(16K, 16K + 16)) by (compute_only); }` for K = 0..15. These are the only compute uses in the crate.
  - `proof fn lemma_sbox_chunk_elem(lo: nat, hi: nat, x: nat)` requires `sbox_chunk_ok(lo, hi)`, `lo <= x < hi` and `x < 256`, and ensures `affine(ginv_chain(x as u8)) == sbox(x as u8)`. It recurses on `x − lo`.
  - **`proof fn lemma_sbox_chain(x: u8) ensures affine(ginv_chain(x)) == sbox(x)`**: call all 16 chunk lemmas, then `lemma_sbox_chunk_elem(16 * (x / 16), 16 * (x / 16) + 16, x)`.
- **`pub(crate) fn sbox_ct(x: u8) -> (r: u8) ensures r == sbox(x)`.**
  - 13 `gmul_ct` calls in `ginv_chain`'s order, then the affine expression with literal shifts;
  - `proof { lemma_sbox_chain(x); }`;
  - mark it `#[allow(dead_code)] // used from Task 3`;
  - carries the D1 `ponytail:` note, with the number filled in by Task 5.
- **Fallback (D1), only if Task 1 said so:**
  - replace the chain and the chunk lemmas with `fn ginv_slow(b: u8) -> (r: u8) ensures r == ginv(b)`, a 254-step `gmul_ct(b, r)` loop with the invariant `r == gpow(b, i)`;
  - add `proof fn bv_affine(x: u8)`, which shows the affine expression equals `sbox_bits(x, 8)` after `reveal_with_fuel(sbox_bits, 9)`.

- [ ] **Step 1:** No runtime test, because everything is private. The check is the proof, plus the existing crypto tests staying green.
- [ ] **Step 2: Implement in the order listed.** Verify `xtime_ct`/`gmul_ct` first (`--verify-only-module aes --verify-function gmul_ct`), then the chunks, then `sbox_ct`.
- [ ] **Step 3: Mutations.** Run each one, then revert it. Each must fail on a named assertion or invariant:
  - `0x1b` → `0x1d` in `xtime_ct`;
  - the mask on `bb >> 1`;
  - one chain step `gmul(x6, x)` → `sq(x6)`, in exec only;
  - affine `^ 0x63` → `^ 0x62`.
- [ ] **Step 4:** Run the four checks and the evidence run. Report the five slowest functions and the 16 chunk times. Escape count: **7**. `rm -rf` the target dir.
- [ ] **Step 5: Commit:** `feat(crypto): verified constant-time GF(2^8) multiply and computed S-box (FIPS 197 §4.2, §5.1.1)`

---

### Task 3: AES-128 rounds, key expansion, `aes128_encrypt_block`; shim fn and row removed

**Files:**
- Modify: `crates/crypto/src/aes.rs`, `crates/crypto/src/shim.rs`, `TRUSTED.md`
- Test: `crates/crypto/tests/aes_gcm.rs`

**Interfaces** (`aes.rs`):
- `fn sub_bytes_exec(s: &[u8; 16]) -> (r: [u8; 16]) ensures r@ == sub_bytes(s@)`: a loop over i in 0..16 calling `sbox_ct`. Remove `sbox_ct`'s `dead_code` allow.
- `fn shift_rows_exec(s: &[u8; 16]) -> (r: [u8; 16]) ensures r@ == shift_rows(s@)`. A loop with the spec's literal index `i % 4 + 4 * ((i / 4 + i % 4) % 4)`. The index is public.
- `fn mix_columns_exec(s: &[u8; 16]) -> (r: [u8; 16]) ensures r@ == mix_columns(s@)`. A loop over i with `r = i % 4` and `c = i / 4`. The body is `gmul_ct(2, s[4c+r]) ^ gmul_ct(3, s[4c+(r+1)%4]) ^ s[4c+(r+2)%4] ^ s[4c+(r+3)%4]`, in the spec's order.
- `pub(crate) closed spec fn rk_ok(rk: Seq<u8>, key: Seq<u8>) -> bool`: `rk.len() == 176 && forall|j: nat| j < 44 ==> rk.subrange(4 * j as int, 4 * j + 4) == #[trigger] key_word(key, j)`. The trigger is on `key_word`, not on the arithmetic `subrange` term.
- `proof fn lemma_round_key(rk: Seq<u8>, key: Seq<u8>, r: nat)`: requires `rk_ok(rk, key)` and `r <= 10`; ensures `rk.subrange(16 * r, 16 * r + 16) =~= round_key(key, r)`.
- `fn add_round_key_exec(s: &[u8; 16], rk: &[u8; 176], round: usize, Ghost(key): Ghost<Seq<u8>>) -> (r: [u8; 16])`: requires `rk_ok(rk@, key)` and `round <= 10`; ensures `r@ == add_round_key(s@, key, round as nat)`.
- **`pub(crate) fn expand_key(key: &[u8]) -> (rk: [u8; 176])`**: requires `key@.len() == 16`; ensures `rk_ok(rk@, key@)`.
  - Words 0..4 are copied from the key.
  - A loop i in 4..44 has the invariant `forall j < i: rk@.subrange(4j, 4j+4) == key_word(key@, j)` plus `rc == rcon((i / 4) as nat)`.
  - Each step unfolds `key_word(key@, i)` once (default fuel), reading words `i−1` and `i−4` from the invariant.
  - When `i % 4 == 0`, `temp = sub_word(rot_word(prev)) ⊕ [rc, 0, 0, 0]`, with 4 `sbox_ct` calls.
  - At the end of each iteration, if `(i + 1) % 4 == 0` then `rc = xtime_ct(rc)`, which is `rcon(j+1) = xtime(rcon(j))` for j ≥ 1. Initially `rc = 1` = `rcon(1)`.
  - `hide(sbox)`. The note is the D2 `ponytail:`.
- **`pub(crate) fn encrypt_rk(rk: &[u8; 176], Ghost(key): Ghost<Seq<u8>>, block: &[u8]) -> (r: [u8; 16])`**: requires `rk_ok(rk@, key)` and `block@.len() == 16`; ensures `r@ == spec_aes128_encrypt(key, block@)`.
  - `st = block ⊕ rk[0..16]` is `aes128_rounds(…, 0)`.
  - Rounds 1..=9 run in a loop with the invariant `st@ == aes128_rounds(key, block@, (r - 1) as nat)`, with one unfold per step.
  - The final round skips MixColumns.
  - `hide(key_word)` and `hide(sbox)`.
- `pub fn aes128_encrypt_block`:
  - delete the attribute and the `/// Trusted shim…` line;
  - the doc is `/// FIPS 197 §5.1 (Nr = 10), §5.2 (Nk = 4); verified against spec_aes128_encrypt.`;
  - the body is `let rk = expand_key(key); encrypt_rk(&rk, Ghost(key@), block)`;
  - the signature is unchanged;
  - update the module doc to say verified, not shim-backed.
- `shim.rs`: delete `aes128_encrypt_block`.
- `TRUSTED.md`: delete the `| crypto::aes::aes128_encrypt_block: …` row. The spec row is reworded in Task 5.

- [ ] **Step 1: New tests** in `tests/aes_gcm.rs`. `fips197_aes128` (C.1 and App. B) stays.
  - **`aes_matches_rustcrypto`:**
    - for i in 0..256, `key[j] = (i * 29 + j * 7 + 3) as u8` and `block[j] = (i + 17 * j) as u8`, so every byte value appears at every position;
    - compare against `aes::Aes128::new(&k.into()).encrypt_block(…)`, using `aes::cipher::{BlockCipherEncrypt, KeyInit}`, exactly as the shim does;
    - `aes` is still a normal dependency here, so tests can use it.
  - **`rfc9001_hp_masks`** (RFC 9001 A.2/A.3), checking `aes128_encrypt_block(hp, sample)[..5]`:
    - A.2: hp `9f50449e04a0e810283a1e9933adedd2`, sample `d1b1c98dd7689fb8ec11d242b123dc9b`, expected `437b9aec36`;
    - A.3: hp `c206b8d9b9f0f37644430b490eeaa314`, sample `2cd0991cd25b0aac406a5816b6394100`, expected `2ec0d8356a`.
    - The planner cross-checked these with Python `cryptography`. The implementer copies them by script from `<scratch>/rfc/rfc9001.txt` (lines 2355–2480).
- [ ] **Step 2:** Run against the shim first; all pass.
- [ ] **Step 3: Implement**, then the shim and TRUSTED edits, in the same commit.
- [ ] **Step 4: Mutations**, each failing on a named assertion:
  - ShiftRows `+` → `−`;
  - MixColumns 2/3 swap;
  - MixColumns in the final round;
  - `rot_word` direction;
  - `rc` advanced at `i % 4 == 0` instead of the end of the iteration;
  - round key `16·(r+1)`.
- [ ] **Step 5:** Run the four checks and the evidence run, and report the five slowest functions.
  - `cargo test -p crypto --test aes_gcm` passes 5 tests; report its debug time.
  - Escape count: **6**.
  - `rm -rf` the target dir.
- [ ] **Step 6: Commit:** `feat(crypto): verified AES-128 exec replaces aes shim (FIPS 197 §5.1-5.2)`

---

### Task 4: GHASH, GCTR and tag primitives

**Files:**
- Modify: `crates/crypto/src/gcm.rs`, `crates/crypto/src/sha256.rs` (visibility only)

**Interfaces** (private to `gcm.rs` unless marked; top-level fns get `#[allow(dead_code)] // used from Task 5`; `// SP 800-38D §…` comments):
- `proof fn bv_gf128_step(x: u128, z: u128, v: u128, s: u128) by (bit_vector)`: requires `s < 128`. It ensures, with `M = u128::MAX` and `R = 0xE1u128 << 120`:
  - both masks are in range;
  - `(z ^ (v & ((((x >> s) & 1) * M) as u128))) == (if (x >> s) & 1 == 1 { z ^ v } else { z })`;
  - `((v >> 1) ^ (((v & 1) * R) as u128)) == (if v & 1 == 1 { (v >> 1) ^ R } else { v >> 1 })`.
- **`fn gf128_mul_exec(x: u128, y: u128) -> (r: u128) ensures r == gf128_mul(x, y)`.** A loop i in 0..128 over `(z, v)` from `(0, y)`. The invariant is `gf128_loop(x, z, v, i as nat) == gf128_mul(x, y)`, with a constant right-hand side; each step is one unfold plus `bv_gf128_step(x, z, v, (127 - i) as u128)`. The note is the D3 `ponytail:`.
- `proof fn bv_be128_step(acc: u128, b: u8, i: u128) by (bit_vector)`: requires `i < 16` and `acc >> (8 * i) == 0`. It ensures:
  - `acc < (1u128 << 120)`;
  - `((acc << 8) | (b as u128)) >> (8 * (i + 1)) == 0`;
  - `((acc << 8) | (b as u128)) == acc * 256 + (b as u128)`.
- **`fn load_be128(src: &[u8], off: usize) -> (r: u128)`**: requires `off + 16 <= src@.len()`; ensures `r as nat == os2ip(src@.subrange(off as int, off + 16))`.
  - A loop i in 0..16 doing `acc = (acc << 8) | src[off + i]`.
  - The invariants are `acc as nat == os2ip(blk.take(i))` and `acc >> (8 * i) == 0`, with the step `blk.take(i + 1).drop_last() =~= blk.take(i)`.
  - This is the planner-probed form.
- `proof fn bv_div256_u128(x: u128)`: 5a's `bv_div256_u64` chain, extended to 15 shifts and 16 bytes.
- `proof fn lemma_i2osp_be16(x: u128)`: ensures `i2osp(x as nat, 16) =~= seq![(x >> 120) as u8, …, x as u8]`, via `reveal_with_fuel(i2osp, 17)` and `bv_div256_u128` (probed).
- `fn store_be128(x: u128) -> (r: [u8; 16]) ensures r@ == i2osp(x as nat, 16)`.
- **`fn ghash_padded(y: u128, h: u128, data: &[u8], Ghost(s): Ghost<Seq<u8>>, Ghost(off): Ghost<int>) -> (r: u128)`.** With `p = data@ + zero_pad16(data@)`:
  - requires `0 <= off`, `off % 16 == 0`, `off + p.len() <= s.len()`, `s.subrange(off, off + p.len()) == p` and `y == ghash(h, s.take(off))`;
  - ensures `r == ghash(h, s.take(off + p.len()))`.
  - Full blocks use `load_be128(data, i)`.
  - A non-empty tail is copied into `let mut buf = [0u8; 16]` and loaded with `load_be128(&buf, 0)`.
  - Each block is `y = gf128_mul_exec(y ^ blk, h)`, with one `ghash` unfold using `s.take(o + 16).subrange(0, o) =~= s.take(o)`.
  - `p.len() == 16 * ceil(|data| / 16)` comes from vstd `div_mod` lemmas, as in 5a Task 2 (`lemma_fundamental_div_mod_converse`).
  - `hide(gf128_mul)`.
- `sha256.rs`: `lemma_os2ip4`, `lemma_i2osp_be4` and `lemma_i2osp_be8` become `pub(crate)`.
- `fn ctr_block(nonce: &[u8], c: u32) -> (r: [u8; 16])`: requires `nonce@.len() == 12`; ensures `r@ == nonce@ + i2osp(c as nat, 4)` (via `lemma_i2osp_be4`).
- `proof fn bv_u32_bytes(c: u32) by (bit_vector)`: ensures the four big-endian bytes of `c`, recombined by `* 0x100_0000 + * 0x1_0000 + * 0x100 + `, equal `c`.
- `proof fn lemma_wrapping_inc(c: u32)`: ensures `vstd::wrapping::u32_specs::wrapping_add(c, 1) as nat == (c as nat + 1) % 0x1_0000_0000`. Expect an empty body.
- `proof fn lemma_inc32(nonce: Seq<u8>, c: u32)`: requires `nonce.len() == 12`; ensures `inc32(nonce + i2osp(c as nat, 4)) == nonce + i2osp(vstd::wrapping::u32_specs::wrapping_add(c, 1) as nat, 4)`. It uses `lemma_i2osp_be4`, `lemma_os2ip4` and `bv_u32_bytes` to get `os2ip(i2osp(c, 4)) == c`.
- `proof fn lemma_j0(nonce: Seq<u8>)`: requires `nonce.len() == 12`; ensures `gcm_j0(nonce) =~= nonce + i2osp(1, 4)` and `inc32(gcm_j0(nonce)) =~= nonce + i2osp(2, 4)`.
- **`pub proof fn lemma_gctr_len(key: Seq<u8>, icb: Seq<u8>, x: Seq<u8>)`**: ensures `gctr(key, icb, x).len() == x.len()`, with `decreases x.len()`.
  - Seal needs it to discharge `gcm_tag_exec`'s `c@.len() <= GCM_MAX_PT_LEN` on `out.as_slice()`.
  - It is `pub` because Phase 3e's open∘seal lemma already cites `lemma_gctr_len`.
  - It is a new proof fn, so the freeze allows it.
- **`fn gctr_append(rk: &[u8; 176], Ghost(key): Ghost<Seq<u8>>, nonce: &[u8], c0: u32, x: &[u8], out: &mut Vec<u8>)`**: requires `rk_ok(rk@, key)` and `nonce@.len() == 12`; ensures `final(out)@ == old(out)@ + gctr(key, nonce@ + i2osp(c0 as nat, 4), x@)`.
  - Per block:
    - `ks = encrypt_rk(rk, Ghost(key), &ctr_block(nonce, c))`;
    - push `x[off + j] ^ ks[j]` for `j < min(16, x.len() − off)`;
    - `c = c.wrapping_add(1)`.
  - The **suffix-form invariant** (5a's `sha256_blocks` pattern) is `out@ + gctr(key, nonce@ + i2osp(c as nat, 4), x@.skip(off)) == old(out)@ + gctr(key, nonce@ + i2osp(c0 as nat, 4), x@)`.
  - Each step unfolds `gctr` once, uses `x@.skip(off).subrange(n, …) =~= x@.skip(off + n)` and `lemma_inc32`, and appeals to Seq-add associativity via `=~=`.
  - `hide(spec_aes128_encrypt)`.
  - The pushes stay within the capacity the caller reserved, so there is no per-block allocation.
- **`fn gcm_tag_exec(rk: &[u8; 176], Ghost(key): Ghost<Seq<u8>>, nonce: &[u8], aad: &[u8], c: &[u8]) -> (t: [u8; 16])`**: requires `rk_ok(rk@, key)`, `nonce@.len() == 12`, `aad@.len() <= MAX_INPUT_LEN` and `c@.len() <= GCM_MAX_PT_LEN`; ensures `t@ == gcm_tag(key, nonce@, aad@, c@)`.
  - `h = load_be128(&encrypt_rk(rk, Ghost(key), &[0u8; 16]), 0)`, with `[0u8; 16]@ =~= Seq::new(16, |i| 0u8)`.
  - The ghost `S` is `aad@ + zero_pad16(aad@) + c@ + zero_pad16(c@) + i2osp(8·|A|, 8) + i2osp(8·|C|, 8)`, exactly `gcm_tag`'s argument.
  - Then `y = ghash_padded(0, h, aad, S, 0)` (where `ghash(h, S.take(0)) == 0`), followed by `y = ghash_padded(y, h, c, S, |A|+padA)`.
  - The length block is `lb: [u8; 16]` from `8 * aad.len() as u64` and `8 * c.len() as u64`, big-endian (`lemma_i2osp_be8`). Then `y = gf128_mul_exec(y ^ load_be128(&lb, 0), h)`, with one unfold and `S.take(S.len()) =~= S`.
  - The tag is `ks = encrypt_rk(rk, Ghost(key), &ctr_block(nonce, 1))` and `t[i] = ks[i] ^ store_be128(y)[i]`. `gctr` on 16 bytes unfolds twice, with `lemma_j0`.
  - `hide(spec_aes128_encrypt)` and `hide(gf128_mul)`.

- [ ] **Step 1:** No runtime test, because everything is private. The checks are the proof and the existing suites.
- [ ] **Step 2: Implement in the order listed.** Verify `gf128_mul_exec`, `load_be128` and `store_be128` in isolation first, then `ghash_padded`, then the GCTR group, then `gcm_tag_exec`.
- [ ] **Step 3: Mutations**, each failing on a named assertion or invariant:
  - `0xE1 << 112`;
  - bit index `i` instead of `127 − i`;
  - pad 16 on an exact multiple;
  - length halves swapped;
  - byte counts instead of bit counts;
  - aad and c order swapped;
  - `wrapping_add(2)`.
- [ ] **Step 4:** Run the four checks and the evidence run, and report the five slowest functions. Escape count: **6**. `rm -rf` the target dir.
- [ ] **Step 5: Commit:** `feat(crypto): verified GHASH, GCTR and GCM tag primitives (SP 800-38D §6.3-6.5, §7.1)`

---

### Task 5: `aes128_gcm_seal` / `aes128_gcm_open`; shim, rows and direct deps removed

**Files:**
- Modify: `crates/crypto/src/gcm.rs`, `crates/crypto/src/shim.rs`, `crates/crypto/Cargo.toml`, `TRUSTED.md`
- Test: `crates/crypto/tests/aes_gcm.rs`

**Interfaces** (`gcm.rs`):
- `pub fn aes128_gcm_seal`:
  - delete the attribute and the shim doc line;
  - the doc is `/// SP 800-38D §7.1 (96-bit IV, 128-bit tag); verified against spec_gcm_seal.`;
  - the body:
    - `rk = expand_key(key)`;
    - `out = Vec::with_capacity(pt.len() + 16)`;
    - `gctr_append(&rk, Ghost(key@), nonce, 2, pt, &mut out)`, with `lemma_j0` giving `inc32(gcm_j0(nonce@))`;
    - `t = gcm_tag_exec(&rk, Ghost(key@), nonce, aad, out.as_slice())`;
    - `out.extend_from_slice(&t)`.
  - The signature is unchanged.
  - Remove the Task 4 `dead_code` allows.
- `pub fn aes128_gcm_open`:
  - delete the attribute and the doc line;
  - the doc is `/// SP 800-38D §7.2; verified against spec_gcm_open. The tag is checked before any plaintext is produced.`;
  - the body follows D5:
    1. `if ct.len() < 16 { return None; }`;
    2. `c = slice_subrange(ct, 0, ct.len() - 16)`;
    3. `t = gcm_tag_exec(…, c)`;
    4. compare: `diff: u8 = 0`, then a loop i in 0..16 doing `diff = diff | (ct[ct.len() - 16 + i] ^ t[i])`. The invariant is `(diff == 0) == (ct@.subrange(len − 16, len − 16 + i) =~= t@.take(i))`, using `bv_ctacc(acc: u8, a: u8, b: u8) by (bit_vector)`, which ensures `((acc | (a ^ b)) == 0) == (acc == 0 && a == b)` (probed);
    5. `if diff != 0 { return None; }`;
    6. otherwise `out = Vec::with_capacity(c.len())`, `gctr_append(…, 2, c, &mut out)` and `Some(out)`.
  - The ensures follow `spec_gcm_open`'s two branches. Equal tags come from `=~=` at `i == 16`; unequal ones from the invariant's negation.
  - The `ponytail:`/CT comment on the `if diff != 0` says the branch reveals only accept/reject.
  - Update the module doc.
- `shim.rs`: delete `aes128_gcm_seal` and `aes128_gcm_open`. The file and its TRUSTED row stay for P-256, ECDSA and RSA.
- `Cargo.toml`:
  - move `aes` and `aes-gcm` from `[dependencies]` to `[dev-dependencies]`, verbatim except that the trailing comment becomes `# 5b differential tests`;
  - Cargo.lock does not change (5a Task 3 showed the lockfile doesn't separate dev from normal);
  - `cargo tree -p crypto -e normal --depth 1 | grep -E ' (aes|aes-gcm) v'` must print nothing.
- `TRUSTED.md`:
  - delete the two `| crypto::gcm::…` rows;
  - pins line: move `aes =0.9.3, aes-gcm =0.11.1` from the direct list into the `dev:` parenthetical. Rebuild the "transitively pinned" list from `cargo tree -p crypto -e normal`: `ghash`, `polyval`, `ctr` and `cipher` drop out of the normal tree if nothing else pulls them, so check it and don't guess;
  - the AES/GCM spec row's `not machine-checked until phase 5` becomes `checked against FIPS 197 App. B/C.1, GCM spec test cases 1-4, RFC 9001 A.2/A.3 and RustCrypto aes/aes-gcm vectors through the verified exec (tests/aes_gcm.rs) since phase 5b; sbox is proved equal to the exec inversion chain on all 256 inputs by Verus's by (compute_only) evaluator, part of the trusted verifier`.
- **Fill in the measured numbers** in the three D1–D3 `ponytail:` notes, from Step 1's `gcm_64kib` release run.

- [ ] **Step 1: New tests** in `tests/aes_gcm.rs`. `gcm_spec_vectors` and `gcm_open_rejects` stay.
  - **`gcm_spec_tc3`** (GCM spec TC3: K4, IV4, no AAD):
    - pt = `PT4 + "1aafd255"`;
    - expected `CT4 + "473f5985" + "4d5c2af327cd64a62cf35abd2ba6fab4"`;
    - plus the open round trip.
    - The values come from `<scratch>/rev3/t.py`, copied by script, and they pass there. TC5/TC6 use non-96-bit IVs and are out of scope.
  - **`gcm_matches_rustcrypto`.** Use linear sweeps, not a cross product, because a constant-time AES in a debug build is slow:
    - (a) pt lengths `0..=300` × aad lengths {0, 20};
    - (b) aad lengths `0..=300` × pt lengths {0, 17}.
    - If the debug `cargo test -p crypto` time goes over about 60 s, thin (b) to every third aad length, keeping 15, 16, 17, 31, 32 and 33, and say so in the report.
    - Use pattern bytes, with key/nonce varying by length.
    - For each case:
      - seal must equal `Aes128Gcm::encrypt`, as in the shim;
      - `open(seal) == Some(pt)`;
      - flipping bit `len % 8` of tag byte `len % 16` makes both ours and RustCrypto's return `None`;
      - if pt is non-empty, flipping `ct[0]` does the same.
  - **`rfc9001_initial_aead`.** The implementer extracts these by script from `<scratch>/rfc/rfc9001.txt` and checks the sha256 prefixes in the same `python3 -I` step:
    - **A.3:**
      - key `cf3a5331653c364c88f0f379b6067e37`;
      - nonce `0ac1493ca1905853b0bba03f` (iv ⊕ pn 1);
      - aad = header `c1000000010008f067a5502a4262b50040750001`;
      - pt: 99 bytes, sha256 prefix `ccbb15df19fe4ed3`;
      - expected seal: protected packet `[20..]`, 115 bytes, prefix `9a8d8130199e794c`, full hex in the test;
      - open returns `Some(pt)`.
    - **A.2:**
      - key `1f369613dd76d5467730efcbe3b1a22d`;
      - nonce `fa044b2f42a3fd3b46fb255e` (iv ⊕ pn 2);
      - aad `c300000001088394c8f03e5157080000449e00000002`;
      - pt = the 245-byte CRYPTO frame (prefix `c62b4bef888f771b`) zero-padded to 1162 bytes (prefix `f9ca5740dccd911a`);
      - check `crypto::sha256::sha256(&seal)` against the full digest `b920e67ea7fdfe77e9f2c3a24d75c04afed30c24ec84d5bcd5464f634657e49f` of protected `[22..]` (1178 bytes), so ~2.4 KB of hex stays out of the source;
      - open returns `Some(pt)`.
    - The planner verified both with Python `cryptography` `AESGCM`.
  - **`gcm_64kib`:**
    - 65 536-byte pt with 20-byte aad, matching RustCrypto;
    - prints the elapsed time, with **no time assertion**, since the debug speed of the constant-time code is unknown;
    - run it with `cargo test --release -p crypto --test aes_gcm gcm_64kib -- --nocapture` to get the µs-per-block numbers for the `ponytail:` notes;
    - also report the debug time.
  - Skipped: Wycheproof `aes_gcm_test.json`. It needs a JSON dev-dep, the sweeps cover the same boundaries, and it belongs to the Phase 5 exit, which the design lists as CAVP + Wycheproof.
- [ ] **Step 2:** Run against the shim first; all pass.
- [ ] **Step 3: Implement** the two bodies, then the shim, Cargo and TRUSTED edits and the ponytail numbers, all in one commit.
- [ ] **Step 4: Mutations**, each failing on a named assertion or invariant:
  - payload `c0 = 1`;
  - a 15-iteration compare loop;
  - `diff = diff ^ …`, which can cancel;
  - open passing `ct` instead of `c` to `gcm_tag_exec`.

  Also by reading: no `return` inside the compare loop, and no allocation before step 5.
- [ ] **Step 5:** Run the four checks and the evidence run.
  - `cargo test -p crypto`: aes_gcm has 9 tests, and every other crypto suite stays green. Report the times.
  - The `cargo tree` check prints nothing.
  - Escape count: **4**.
  - `rm -rf` the target dir.
- [ ] **Step 6: Commit:** `feat(crypto): verified AES-128-GCM seal/open replace aes-gcm shim (SP 800-38D §7.1-7.2)`

---

## Exit criteria (Phase 5b)

- All four checks pass on the merged tree, and `verify.sh` prints `escapes accounted (4)`.
- TRUSTED.md has no `crypto::aes::` or `crypto::gcm::` rows. The AES/GCM spec row is reworded, the pins line is rebuilt from `cargo tree`, and the `shim.rs` row remains.
- `shim.rs` has no AES/GCM fn, and `aes`/`aes-gcm` are dev-dependencies only.
- The spec-freeze diff check passes for `aes.rs`, `gcm.rs`, `bytes.rs` and `sha256.rs`.
- `compute_only` appears only in `lemma_sbox_chunk_*`.
- The three `ponytail:` ceilings carry measured numbers.
- `phase-5b` is merged into `main`.

## Self-review (done while writing)

- **Scope.** Exactly three functions. There is no public expanded-key API (D2), no AES-256 or ChaCha20 (design non-goals), no non-96-bit IV (the 3a spec is 96-bit only), and no streaming AEAD.
- **Preconditions chain.**
  - `aad ≤ 2⁶⁰` gives `8·|A| ≤ 2⁶³ < 2⁶⁴`.
  - `pt ≤ 2³⁶ − 32` means `pt.len() + 16` can't overflow.
  - `ct ≤ GCM_MAX_PT_LEN + 16` means `c ≤ GCM_MAX_PT_LEN`, which `gcm_tag_exec` requires.
  - The counter wrap is mirrored rather than excluded.
- **Every proof route was probed by the planner with the pinned Verus**, except the round, GCTR and GHASH loops. Those reuse 5a's one-step-unfolding and suffix-invariant patterns.
- **Proportion.** Signatures, invariants, lemma names and exact vector values. Bodies are given only where the invariant shape isn't fixed by the signature: gmul's `acc ^ rest` invariant, `rc` timing, the GHASH ghost concatenation, and the GCTR suffix form.
