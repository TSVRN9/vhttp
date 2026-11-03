# Phase 3a: `crypto` Specs + RustCrypto Shim — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A new `crates/crypto` crate holding two things for every primitive the server needs:
- spec functions transcribed from the standards;
- exec functions whose `ensures` state results in terms of those specs.

Each exec body is a `#[verifier::external_body]` one-liner into a RustCrypto shim. That lets Phase 3e (QUIC packet protection) and Phase 4 (TLS 1.3) prove against the specs from day one. Phase 5 swaps each body for verified code behind the same signature.

**Architecture:**
- **New crate `crates/crypto`.** It does not depend on `wire`/`h3`, and nothing depends on it yet.
- **One file per primitive**, holding its spec fns, its exec fn(s) and the TRUSTED.md-listed `external_body`s: `bytes.rs` (shared octet-string specs), `sha256.rs`, `hmac.rs`, `hkdf.rs`, `aes.rs`, `gcm.rs`, `p256.rs`, `ecdsa.rs`, `rsa.rs`.
- **All RustCrypto calls live in `src/shim.rs`.** It is plain Rust outside `verus!`, `mod shim;` is private, and Phase 5 deletes it. No RustCrypto type appears in any `pub` signature.
- **One piece of verified exec code:** the ECDSA (r, s) DER encoder. It is a byte codec, not a primitive, and Phase 5's list doesn't include it, so a shim would have no owner.

**Tech Stack:**
- Verus 0.2026.10.04.426d8b0 and vstd `=0.0.0-2026-10-04-0306`.
- RustCrypto, all versions exact: sha2 `=0.11.1`, hmac `=0.13.0`, hkdf `=0.13.0`, aes `=0.9.3`, aes-gcm `=0.11.1`, p256 `=0.14.0` (with ecdsa 0.17.0 and rfc6979 0.6.0 via the lock), rsa `=0.10.0-rc.19` (with crypto-bigint 0.7.10).
- Dev-only: primeorder `=0.14.0`, plus rsa with the `hazmat` feature.

**Spec:** `docs/superpowers/specs/2026-10-27-verified-http3-design.md`. See Phase 3 ("crypto with spec functions … external_body … RustCrypto shim"), Phase 5, the trusted base, and "Calls I made" (P-256 only, TLS_AES_128_GCM_SHA256 only, RSA ruling: PSS signing, no verification).

## Global Constraints

- **Pins:**
  - Verus 0.2026.10.04.426d8b0 and vstd `=0.0.0-2026-10-04-0306`.
  - The RustCrypto pins in Tech Stack, exactly as written there. Never upgrade one alone.
  - Probe crates (`<scratch>/probe` with all dependencies, and `probe2` with only the Task 1–2 dependencies) checked these on 2026-10-27:
    - `cargo build` and `cargo test` pass on rustc 1.92.0;
    - `cargo verus verify` passes on Verus's 1.98.1 frontend with these exact dependency lines;
    - every KAT in this plan passes against the shim.
- **`crates/crypto/Cargo.toml`:** same layout as `crates/wire/Cargo.toml`, with `wire`/`vest_lib` removed. Each task adds its own lines, copied verbatim:
  ```toml
  sha2 = { version = "=0.11.1", default-features = false }                                         # Task 1
  hmac = { version = "=0.13.0", default-features = false }                                         # Task 2
  hkdf = { version = "=0.13.0", default-features = false }                                         # Task 2
  aes = { version = "=0.9.3", default-features = false }                                           # Task 3
  aes-gcm = { version = "=0.11.1", default-features = false, features = ["aes", "alloc"] }         # Task 3
  p256 = { version = "=0.14.0", default-features = false, features = ["arithmetic", "ecdsa", "ecdh"] }  # Task 4
  rsa = { version = "=0.10.0-rc.19", default-features = false, features = ["sha2"] }               # Task 6
  # [dev-dependencies]
  primeorder = "=0.14.0"                                                                           # Task 4
  rsa = { version = "=0.10.0-rc.19", default-features = false, features = ["sha2", "hazmat"] }     # Task 6
  ```
- **Escapes, which replaces 2a's zero-escape rule:**
  - The only escape allowed is `#[verifier::external_body]`, and only on the exec fns this plan names, in `crates/crypto/src/*.rs`.
  - **`scripts/verify.sh` currently fails on any escape hit in `crates/`** (Phase 2a final-review fix). Task 1 replaces that with per-hit accounting:
    - any hit outside `crates/crypto/src/` fails;
    - any hit in `crates/crypto/src/` that isn't exactly a `#[verifier::external_body]` attribute line fails;
    - the number of `#[verifier::external_body]` lines must equal the number of TRUSTED.md rows starting with `| crypto::`;
    - for each attribute, the next `fn` it precedes must be named in a `crypto::<mod>::<fn>` row.
    Prove the gate in Task 1's report with three probes, reverting each: an extra unlisted external_body fails; an `assume(` in crates/h3 fails; the clean tree passes.
  - Every `external_body` gets its own TRUSTED.md row in the task that adds it. The row format is:
    `| crypto::<mod>::<fn>: 1 external_body (RustCrypto <crate> via shim::<fn>) | crates/crypto/src/<mod>.rs | exec body is unverified RustCrypto; ensures trusted | 5 |`
  - The escape tokens (`external_body`, `assume(`, …) appear in `crates/` **only** as the attribute itself, never in comments or docs. Otherwise the count check below breaks. Comments say "trusted shim" instead.
  - Task 1 also adds a row for `crates/crypto/src/shim.rs` (Removed in phase 5). It holds no escape token, but it is trusted code.
  - Task 1 also adds the RustCrypto pins to TRUSTED.md "Pinned versions" under "RustCrypto shim (crates/crypto), removed in phase 5".
- **The specs are not machine-checked against the test vectors until Phase 5.** Every test in this plan exercises the *shim*. A spec typo (a wrong round constant, a bit-order slip) passes every test here and is caught only when Phase 5 proves an implementation against the spec and that implementation meets the same vectors. Until then, reading each spec against its cited section *is* the check (Review Focus 1).
- **Citations:**
  - Each spec fn cites its standard and section in a plain `//` or `///` comment, e.g. `/// FIPS 180-4 §6.2.2 step 1`.
  - These standards are not in `.duvet/config.toml`, so never write `//=` or `//#` in `crates/crypto`.
- **Every task's verification runs all four checks:**
  - `scripts/verify.sh` reports 0 errors and prints its summary line;
  - `cargo build && cargo test` pass with 0 warnings;
  - the escape grep `grep -rnE 'admit\(|assume\(|external_body|assume_specification|verifier::external|axiom fn' crates --include='*.rs'` prints only `crates/crypto/src/*.rs:N:#[verifier::external_body]` lines, and their count equals the number of `crypto::` rows in TRUSTED.md (running total given per task);
  - `duvet report` exits 0.
- **Verification evidence must come from a fresh `CARGO_TARGET_DIR`:** `(cd crates/crypto && CARGO_TARGET_DIR=<scratch>/vt-3a-tN cargo verus verify)`. It must print `verification results:: … 0 errors` for vstd and for crypto. A cache hit prints nothing.
- **Exec signatures:**
  - **Inputs are `&[u8]`,** with a `requires x@.len() == N` for each fixed length. The probe showed `&[u8; N]`, `.as_slice()` and `Vec::as_slice()` all coerce, with the view preserved, so callers holding arrays or Vecs both work.
  - **Fixed-length outputs are arrays** (`[u8; 32]`, `[u8; 16]`, `[u8; 65]`, `[u8; 64]`); variable-length outputs are `Vec<u8>`.
  - **Optional results** are `Option<[u8; N]>` or `Option<Vec<u8>>`, stated as `ensures r.deep_view() == spec_x(..)` where `spec_x` returns `Option<Seq<u8>>`. `r@` does not typecheck on `Option` (probe).
- **Spec math:**
  - Big integers are `nat`/`int`. Field and scalar elements are `int` in `[0, m)`, reduced with `%`, which on `int` is Euclidean in Verus.
  - Inverses are Fermat: `pow(x, m - 2) % m` (both P-256 moduli are prime).
  - Octet strings are `Seq<u8>` and convert with `os2ip`/`i2osp` (Task 1).
  - Words are `u32`, with spec-level `add32` = `((a + b) % 2^32) as u32`.
  - **Every import of a spec item is a glob under `#[allow(unused_imports)]`.** This covers vstd's (`use vstd::arithmetic::power::*;`, `power2::*`) and the crate's own (`use crate::sha256::*;`, `use crate::p256::*;`). Plain `cargo build` erases spec fns, so a named `use crate::sha256::spec_sha256;` or `use …::pow;` fails with E0432 (probe).
  - **`usize` is 64-bit.** `lib.rs` starts with `verus! { #[allow(unused_braces)] global size_of usize == 8; }`. Without it, Verus rejects `MAX_INPUT_LEN`/`GCM_MAX_PT_LEN` ("integer literal out of range USize"). Without the `allow`, plain `cargo build` warns `unused_braces`. Both were probed.
  - An `exists` or `choose` with a nested `forall` needs explicit `#[trigger]` on both function applications. Without it, Verus can't infer triggers (probe).
- **Standard constants are exec `pub const` arrays that the spec reads via `@`** (e.g. `SHA256_K@[t as int]`, `os2ip(P256_N@)`). The probe showed `by (compute_only)` evaluates both. Because the constants are exec code, tests can check them against an independent source (Tasks 1 and 4).
- **Input-size bound:** `pub const MAX_INPUT_LEN: usize = 0x1000_0000_0000_0000;` (2⁶⁰ bytes). Every variable-length message, key, salt, ikm, info or aad input `requires x@.len() <= MAX_INPUT_LEN`. The point is that every derived hash input stays below FIPS 180-4's 2⁶⁴-bit limit (2⁶¹ bytes), even after HMAC/HKDF/PSS prepend ≤ 105 bytes. AES-GCM plaintext has its own bound (Task 3).
- **No panics:**
  - Every `unwrap`/`expect` in `shim.rs` carries a `// unreachable: <requires that rules it out>` comment.
  - Any input the shim can reject maps to `None`, and the spec has a matching `None` case or the ensures is one-directional (RSA, Task 6).
- **Matrix bookkeeping:**
  - 3a closes **no** rows. Every crypto row closes in Phase 5, when its `external_body` goes. Write no ✅ marks.
  - Task 4 appends `3a spec: crates/crypto/src/p256.rs (exec external_body until 5)` to the Notes of RFC 8446 §4.2.8.2, and Task 6 appends the same with `rsa.rs` to §9.1 (req).
  - Each append goes in the task's own commit.

## Matrix rows this plan touches (none closed)

- RFC 8446 §4.2.8.2 (point validation, Phase 5): its spec is `sec1_decode`.
- RFC 8446 §9.1 (req) (RSASSA-PSS signing, Phase 5): its spec is `spec_rsassa_pss_sign`.
- RFC 8446 §7.4.2 (Phase 4) also gets its primitive here: ECDH output is the full 32-byte x-coordinate. RFC 9001 §5.2/§5.4.x (Phase 4) consume `hkdf_*`/`aes128_encrypt_block`. Neither row is edited.

## Review Focus

1. **Spec transcription faithfulness.** The specs are trusted and nothing machine-checks them before Phase 5, so a reviewer reads each spec fn against its cited section. These are the most likely slips:
   - SHA-256: big-endian word load; the 64-bit *bit*-length field.
   - GCM:
     - bit 0 of a block is the MSB of byte 0;
     - R = `0xE1 << 120`, and a right shift moves toward the LSB;
     - `[len]64` counts bits;
     - `inc32` touches only the last 4 bytes.
   - AES: column-major state (`s[r][c] = in[r + 4c]`); the last round has no MixColumns.
   - ECDSA:
     - retry on `r == 0` and on `s == 0` (RustCrypto's `Signature::from_scalars` rejects both; RFC 6979 §3.4 names only r, FIPS 186-5 §6.4.1 both);
     - `r = x(kG) mod n`;
     - `bits2octets` includes `mod q`;
     - **no** low-S normalization.
   - PSS: `emBits = modBits − 1`, and the leftmost `8·emLen − emBits` bits are cleared.

   Pinned where it can be: Task 1 `sha256_constants_from_roots` recomputes K/H0. Task 4 `p256_constants_match_rustcrypto` checks p, n, b, G. ECDSA "sample" has a high-S `s = F7CB…` and must match exactly, which proves the shim doesn't normalize (Task 5 `rfc6979_a25_sha256`).
2. **RSA signature length and salt for a modulus that isn't a multiple of 64 bits.**
   - rsa 0.10.0-rc.19's `pss::Signature::to_vec` pads to limb width: 264 bytes for a 2049-bit n instead of k = 257.
   - The salt must be used verbatim. The shim feeds it through an RNG adapter, which breaks silently if the crate draws differently.
   - Pinned in Task 6: `pss_rsa2049_len_and_salt` (length 257, crate verifier accepts, salt recovered from `s^e mod n`).
3. **Peer point validation (ECDH):**
   - Expected `None` for: off-curve; 64-byte or 66-byte input; compressed `0x02`/`0x03` prefix; non-canonical x = p (the point (0, 0x6648…f3f4) re-encoded with x + p); a 1-byte input; private scalar 0, n or 0xff…ff.
   - The canonical (0, 0x6648…f3f4) must be *accepted*.
   - Pinned in Task 4: `ecdh_rejects_invalid`, `scalar_range`.
4. **AEAD open on bad input:**
   - Expected `None` for: a flipped tag bit; a flipped ciphertext bit; changed AAD; input of 15 bytes or 0 bytes.
   - An empty plaintext round-trips (GCM test case 1).
   - Pinned in Task 3: `gcm_open_rejects`, `gcm_spec_vectors`.
5. **DER INTEGER edges:**
   - a high bit set needs a `0x00` prefix;
   - leading zero bytes are stripped, then the prefix is re-added if the next byte is ≥ 0x80;
   - zero encodes as `02 01 00`.
   - Pinned in Task 5: `der_vectors`.

---

### Task 1: `crypto` crate, octet-string specs, SHA-256

**Files:**
- Create: `crates/crypto/Cargo.toml`, `crates/crypto/src/lib.rs`, `crates/crypto/src/bytes.rs`, `crates/crypto/src/sha256.rs`, `crates/crypto/src/shim.rs`
- Modify: `TRUSTED.md`, `Cargo.lock`, `scripts/verify.sh` (the per-hit escape accounting in Global Constraints)
- Test: `crates/crypto/tests/sha256.rs`

**Interfaces:**
- Produces (`crypto::bytes`):
  - `pub const MAX_INPUT_LEN: usize = 0x1000_0000_0000_0000;`
  - `pub open spec fn os2ip(s: Seq<u8>) -> nat`: RFC 8017 §4.2, big-endian, recursing on `drop_last`.
  - `pub open spec fn i2osp(x: nat, len: nat) -> Seq<u8>`: RFC 8017 §4.1. Callers ensure `x < 256^len`; the spec keeps the low `len` octets.
  - `pub open spec fn xor_bytes(a: Seq<u8>, b: Seq<u8>) -> Seq<u8>`: length `a.len()`, `a[i] ^ b[i]`.
- Produces (`crypto::sha256`, FIPS 180-4):
  - `pub const SHA256_K: [u32; 64]` (§4.2.2) and `pub const SHA256_H0: [u32; 8]` (§5.3.3).
  - Spec helpers (§3.2, §4.1.2):
    - `add32`;
    - `rotr(x: u32, n: u32) -> u32`;
    - `ch`, `maj`;
    - `bsig0` (Σ0: 2, 13, 22), `bsig1` (Σ1: 6, 11, 25), `ssig0` (σ0: 7, 18, SHR 3), `ssig1` (σ1: 17, 19, SHR 10).
  - `pub open spec fn sha256_pad(m: Seq<u8>) -> Seq<u8>` (§5.1.1): `m ++ [0x80] ++ zeros ++ i2osp(8·|m|, 8)`, with the total a multiple of 64.
  - `spec fn sha256_w(block: Seq<u8>, t: nat) -> u32` (§6.2.2 step 1):
    - t < 16 is a big-endian load of bytes `4t..4t+4`;
    - otherwise `σ1(W[t−2]) + W[t−7] + σ0(W[t−15]) + W[t−16]`;
    - `decreases t`.
  - `spec fn sha256_compress(h: Seq<u32>, block: Seq<u8>) -> Seq<u32>` (§6.2.2 steps 2–4): 64 rounds over (a..h), recursing on the round index, then the word-wise `add32` with `h`.
  - `pub open spec fn spec_sha256(m: Seq<u8>) -> Seq<u8>` (§6.2): fold `sha256_compress` over the 64-byte blocks of `sha256_pad(m)` from `SHA256_H0@`, then emit the 8 words big-endian. The length is 32.
  - `pub fn sha256(msg: &[u8]) -> (r: [u8; 32])`: `#[verifier::external_body]`, with `requires msg@.len() <= MAX_INPUT_LEN` and `ensures r@ == spec_sha256(msg@)`.
- Produces (`shim`): `pub(crate) fn sha256(m: &[u8]) -> [u8; 32] { Sha256::digest(m).into() }`.

- [ ] **Step 1: Failing tests** in `crates/crypto/tests/sha256.rs`. Add a local `fn h(s: &str) -> Vec<u8>` hex helper that ignores whitespace; later test files copy it.
  - `fips180_examples`:
    - `sha256(b"abc")` = `ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad` (FIPS 180-4 example, SHA256.pdf);
    - `sha256(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")` = `248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1`. This 56-byte message makes the padding spill into a second block;
    - `sha256(b"")` = `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (CAVP SHA256ShortMsg Len = 0).
  - `sha256_constants_from_roots`:
    - Take the first 64 primes as `u128`.
    - `SHA256_K[t]` must equal `icbrt(p_t << 96) as u32`, and `SHA256_H0[i]` must equal `isqrt(p_i << 64) as u32` for i < 8. Both are integer binary searches on `u128`; `p·2⁹⁶ < 2¹⁰⁵`, so the cube fits.
    - The probe checked `K[0] = 0x428a2f98`, `K[63] = 0xc67178f2`, `H0[0] = 0x6a09e667` and `H0[7] = 0x5be0cd19`.
- [ ] **Step 2:** `cargo test -p crypto`. Expected to fail: the crate doesn't exist.
- [ ] **Step 3: Implement.**
  - `lib.rs` is `use vstd::prelude::*;`, then the `global size_of usize == 8` block (Global Constraints), then `pub mod bytes; pub mod sha256; mod shim;`.
  - Write `bytes.rs` and `sha256.rs` with the spec fns above, then the exec fn and the shim fn.
  - TRUSTED.md: the `crypto::sha256::sha256` row, the `shim.rs` row and the RustCrypto pins.
  - `scripts/verify.sh`: per-hit escape accounting with the three gate probes (Global Constraints).
- [ ] **Step 4:** Run the four checks, the fresh-target-dir verify, and `cargo test -p crypto`: 2 pass. Escape count: 1.
- [ ] **Step 5: Commit:** `feat(crypto): crate, octet-string specs, SHA-256 spec + shim (FIPS 180-4)`

---

### Task 2: HMAC-SHA256 and HKDF

**Files:**
- Create: `crates/crypto/src/hmac.rs`, `crates/crypto/src/hkdf.rs`
- Modify: `crates/crypto/src/lib.rs`, `crates/crypto/src/shim.rs`, `crates/crypto/Cargo.toml`, `TRUSTED.md`
- Test: `crates/crypto/tests/hmac_hkdf.rs`

**Interfaces:**
- Consumes: `spec_sha256`, `xor_bytes`, `i2osp`, `MAX_INPUT_LEN`.
- Produces (`crypto::hmac`, RFC 2104 §2, with B = 64 and L = 32):
  - `pub open spec fn spec_hmac_sha256(key: Seq<u8>, msg: Seq<u8>) -> Seq<u8>`:
    - K0 = `spec_sha256(key)` if `key.len() > 64`, else `key`, right-padded with zeros to 64 bytes;
    - the result is `H((K0 ⊕ opad) ++ H((K0 ⊕ ipad) ++ msg))`, with ipad = 64×`0x36` and opad = 64×`0x5c`.
  - `pub fn hmac_sha256(key: &[u8], msg: &[u8]) -> (r: [u8; 32])`: external_body, with `requires key@.len() <= MAX_INPUT_LEN, msg@.len() <= MAX_INPUT_LEN` and `ensures r@ == spec_hmac_sha256(key@, msg@)`.
- Produces (`crypto::hkdf`, RFC 5869 §2.2–2.3; **no** Expand-Label, which is Phase 3e/4):
  - `pub open spec fn spec_hkdf_extract(salt: Seq<u8>, ikm: Seq<u8>) -> Seq<u8>` = `spec_hmac_sha256(salt, ikm)`. Add a comment: "salt not provided" is an empty `salt`; HMAC zero-pads keys to 64 bytes, so it equals HashLen zeros (A.3 checks this).
  - `spec fn hkdf_t(prk, info, i: nat) -> Seq<u8>`: T(0) is empty; T(i) = `HMAC(prk, T(i−1) ++ info ++ [i as u8])`.
  - `pub open spec fn spec_hkdf_expand(prk: Seq<u8>, info: Seq<u8>, len: nat) -> Seq<u8>`: the first `len` bytes of T(1) ++ … ++ T(⌈len/32⌉).
  - `pub fn hkdf_extract(salt: &[u8], ikm: &[u8]) -> (r: [u8; 32])`: external_body, with both inputs `<= MAX_INPUT_LEN`, ensures `r@ == spec_hkdf_extract(salt@, ikm@)`.
  - `pub fn hkdf_expand(prk: &[u8], info: &[u8], len: usize) -> (r: Vec<u8>)`: external_body, with `requires prk@.len() == 32, info@.len() <= MAX_INPUT_LEN, len <= 8160` and `ensures r@ == spec_hkdf_expand(prk@, info@, len as nat)`. The 8160 bound is 255·HashLen.
- Shim:
  - HMAC is keyed with `<Hmac<Sha256> as KeyInit>::new_from_slice(k)`, using `use hmac::{Hmac, KeyInit, Mac};`. That import path builds with only the Task 1–2 dependencies (probed). `Mac::new_from_slice` doesn't exist in hmac 0.13. The `// unreachable` reason: HMAC accepts any key length.
  - `hkdf::Hkdf::<Sha256>::extract(Some(salt), ikm).0`.
  - `Hkdf::from_prk(prk)` (unreachable: `prk@.len() == 32`) followed by `.expand(info, &mut out)` (unreachable: `len <= 8160`).

- [ ] **Step 1: Failing tests:**
  - `rfc4231_hmac`:
    - TC1: key 20×`0b`, data `b"Hi There"`, result `b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7`;
    - TC2: key `b"Jefe"`, data `b"what do ya want for nothing?"`, result `5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843`;
    - TC6, whose key is longer than a block: key 131×`aa`, data `b"Test Using Larger Than Block-Size Key - Hash Key First"`, result `60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54`.
  - `rfc5869_hkdf`:
    - **A.1:** IKM 22×`0b`, salt `000102030405060708090a0b0c`, info `f0f1f2f3f4f5f6f7f8f9`, L = 42.
      - PRK = `077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5`;
      - OKM = `3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865`.
    - **A.3:** IKM 22×`0b`, empty salt, empty info, L = 42.
      - PRK = `19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04`;
      - OKM = `8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d9d201395faa4b61a96c8`;
      - also `hkdf_extract(&[0u8; 32], ikm)` equals the empty-salt PRK.
  - `hkdf_expand_lengths`: with the A.3 PRK, `len` 0 returns empty and `len` 8160 returns 8160 bytes, whose first 42 equal the A.3 OKM.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3: Implement** the specs, the exec fns, the shim fns, the Cargo lines and TRUSTED rows for `hmac_sha256`, `hkdf_extract` and `hkdf_expand`.
- [ ] **Step 4:** Run the four checks and the fresh verify. Tests: 3 new pass. Escape count: 4.
- [ ] **Step 5: Commit:** `feat(crypto): HMAC-SHA256 + HKDF specs + shim (RFC 2104, RFC 5869)`

---

### Task 3: AES-128 block cipher and AES-128-GCM

**Files:**
- Create: `crates/crypto/src/aes.rs`, `crates/crypto/src/gcm.rs`
- Modify: `lib.rs`, `shim.rs`, `Cargo.toml`, `TRUSTED.md`
- Test: `crates/crypto/tests/aes_gcm.rs`

**Interfaces:**
- Consumes: `os2ip`, `i2osp`, `xor_bytes`, `MAX_INPUT_LEN`.
- Produces (`crypto::aes`, FIPS 197):
  - **GF(2⁸)** (§4.2): `xtime(b: u8) -> u8`, and `gmul(a: u8, b: u8) -> u8` as shift-and-xtime over the 8 bits of `b`.
  - **S-box, defined algebraically** (§5.1.1). Do not transcribe the table.
    - `ginv(b)` = `b^254` in GF(2⁸), so 0 maps to 0.
    - `sbox(b)` applies equation (5.2) per bit to `x = ginv(b)`: `b'_i = x_i ⊕ x_{(i+4) mod 8} ⊕ x_{(i+5) mod 8} ⊕ x_{(i+6) mod 8} ⊕ x_{(i+7) mod 8} ⊕ c_i`, with c = `0x63`.
  - **Key expansion** (§5.2): `rot_word`, `sub_word`, and `rcon(j)` with `rcon(1) = 0x01` and `rcon(j+1) = xtime(rcon(j))`. Then `key_word(key: Seq<u8>, i: nat) -> Seq<u8>` gives the 4-byte word w[i] for i < 44, with `decreases i`.
  - **State** is a 16-byte `Seq<u8>` in input order, `s[r][c] = s[r + 4c]` (§3.4).
    - `sub_bytes`;
    - `shift_rows`: `s'[r][c] = s[r][(c + r) mod 4]`;
    - `mix_columns`: the matrix `02 03 01 01` (§5.1.3);
    - `add_round_key(s, key, round)`.
  - `pub open spec fn spec_aes128_encrypt(key: Seq<u8>, block: Seq<u8>) -> Seq<u8>` (§5.1, Algorithm 1, Nr = 10): the final round omits MixColumns.
  - `pub fn aes128_encrypt_block(key: &[u8], block: &[u8]) -> (r: [u8; 16])`: external_body, with `requires key@.len() == 16, block@.len() == 16` and `ensures r@ == spec_aes128_encrypt(key@, block@)`.
- Produces (`crypto::gcm`, SP 800-38D, 96-bit IV and 128-bit tag only):
  - `pub const GCM_MAX_PT_LEN: usize = 0xF_FFFF_FFE0;`. That's 2³⁶ − 32 bytes, i.e. len(P) ≤ 2³⁹ − 256 bits (§5.2.1.1).
  - `spec fn gf128_mul(x: u128, y: u128) -> u128` (§6.3, Algorithm 1):
    - bit x_i is `(x >> (127 − i)) & 1`, where blocks map to `u128` by `os2ip` (bit 0 is the MSB of byte 0);
    - R = `0xE1u128 << 120`;
    - each step does `Z ^= V` when x_i is 1, then `V = V >> 1`, xored with R when `V & 1 == 1`;
    - recurse on i up to 128.
  - `spec fn ghash(h: u128, x: Seq<u8>) -> u128` (§6.4): `x.len() % 16 == 0`, and Y_i = (Y_{i−1} ⊕ X_i)·H.
  - `spec fn inc32(cb: Seq<u8>) -> Seq<u8>` (§6.2): the last 4 bytes, as a big-endian counter, are incremented mod 2³²; the first 12 are unchanged.
  - `spec fn gctr(key, icb: Seq<u8>, x: Seq<u8>) -> Seq<u8>` (§6.5): per 16-byte block, `X_i ⊕ CIPH(CB_i)`. A final partial block uses the leading bytes of `CIPH(CB_n)`. Recurse on blocks.
  - `spec fn gcm_tag(key, nonce, aad, c) -> Seq<u8>` (§7.1 steps 1, 2, 5, 6):
    - H = `os2ip(CIPH(0¹²⁸))`;
    - J0 = `nonce ++ [0, 0, 0, 1]`;
    - S = `ghash(H, aad ++ 0^v ++ c ++ 0^u ++ i2osp(8·|aad|, 8) ++ i2osp(8·|c|, 8))`, where the padding goes to a 16-byte multiple and the lengths are in **bits**;
    - T = `gctr(key, J0, i2osp(S, 16))`.
  - `pub open spec fn spec_gcm_seal(key, nonce, aad, pt) -> Seq<u8>` (§7.1): C = `gctr(key, inc32(J0), pt)`, and the result is `C ++ gcm_tag(key, nonce, aad, C)`.
  - `pub open spec fn spec_gcm_open(key, nonce, aad, ct) -> Option<Seq<u8>>` (§7.2):
    - `None` if `ct.len() < 16`;
    - otherwise split C ++ T, and return `None` if `T != gcm_tag(..C)`, else `Some(gctr(key, inc32(J0), C))`.
  - `pub fn aes128_gcm_seal(key: &[u8], nonce: &[u8], aad: &[u8], pt: &[u8]) -> (r: Vec<u8>)`: external_body.
    - requires `key@.len() == 16`, `nonce@.len() == 12`, `aad@.len() <= MAX_INPUT_LEN` and `pt@.len() <= GCM_MAX_PT_LEN`;
    - ensures `r@ == spec_gcm_seal(key@, nonce@, aad@, pt@)`.
  - `pub fn aes128_gcm_open(key: &[u8], nonce: &[u8], aad: &[u8], ct: &[u8]) -> (r: Option<Vec<u8>>)`: external_body.
    - same requires, except `ct@.len() <= GCM_MAX_PT_LEN + 16`;
    - ensures `r.deep_view() == spec_gcm_open(key@, nonce@, aad@, ct@)`.
- Shim:
  - `aes::Aes128::new(k.into())` and `encrypt_block`, via `aes::cipher::{BlockCipherEncrypt, KeyInit}`.
  - `aes_gcm::Aes128Gcm::new(..).encrypt(nonce.into(), Payload { msg, aad })` (unreachable: `GCM_MAX_PT_LEN`); `.decrypt(..).ok()` for open.
  - Slices become arrays via `try_into` (unreachable: the length requires).

- [ ] **Step 1: Failing tests:**
  - `fips197_aes128`:
    - C.1 (FIPS 197, 2001 edition): key `000102030405060708090a0b0c0d0e0f`, plaintext `00112233445566778899aabbccddeeff`, ciphertext `69c4e0d86a7b0430d8cdb78070b4c55a`;
    - Appendix B: key `2b7e151628aed2a6abf7158809cf4f3c`, input `3243f6a8885a308d313198a2e0370734`, output `3925841d02dc09fbdc118597196a0b32`.
  - `gcm_spec_vectors`, from McGrew–Viega "The Galois/Counter Mode of Operation" test cases. Key K and IV are zero in TC1/TC2, so `seal(K, IV, aad, pt)` returns C ++ T:
    - **TC1:** empty pt → `58e2fccefa7e3061367f1d57a4e7455a`, and opening that gives `Some(empty)`.
    - **TC2:** pt 16×`00` → `0388dace60b6a392f328c2b971b2fe78` ++ `ab6e47d42cec13bdf53a67b21257bddf`.
    - **TC4:**
      - K = `feffe9928665731c6d6a8f9467308308`, IV = `cafebabefacedbaddecaf888`;
      - aad = `feedfacedeadbeeffeedfacedeadbeefabaddad2`;
      - pt = `d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39`;
      - expected result: C = `42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091` ++ T = `5bc94fbc3221a5db94fae95ae7121a47`;
      - opening it returns `Some(pt)`.
  - `gcm_open_rejects`, starting from TC4's C ++ T. Each case returns `None`:
    - last byte xor 1;
    - first byte xor 1;
    - `aad[1..]`;
    - `ct[..15]`;
    - an empty `ct`.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3: Implement** the specs, the exec fns, the shim fns, the Cargo lines and TRUSTED rows for `aes128_encrypt_block`, `aes128_gcm_seal` and `aes128_gcm_open`.
- [ ] **Step 4:** Run the four checks and the fresh verify. Tests: 3 new pass. Escape count: 7.
- [ ] **Step 5: Commit:** `feat(crypto): AES-128 + AES-128-GCM specs + shim (FIPS 197, SP 800-38D)`

---

### Task 4: P-256 curve, SEC1 encoding, public key, ECDH

**Files:**
- Create: `crates/crypto/src/p256.rs`
- Modify: `lib.rs`, `shim.rs`, `Cargo.toml`, `TRUSTED.md`, `docs/requirements.md` (RFC 8446 §4.2.8.2 Notes)
- Test: `crates/crypto/tests/p256.rs`

**Interfaces:**
- Consumes: `os2ip`, `i2osp`.
- Produces (`crypto::p256`; curve from SP 800-186 §3.2.1.3, group law and encoding from SEC 1 v2):
  - `pub const P256_P, P256_N, P256_B, P256_GX, P256_GY: [u8; 32]`, all big-endian:
    - p = `ffffffff00000001000000000000000000000000ffffffffffffffffffffffff`
    - n = `ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551`
    - b = `5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b`
    - Gx = `6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296`
    - Gy = `4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5`
  - `pub open spec fn p256_p() -> int` = `os2ip(P256_P@) as int`, and likewise `p256_n`, `p256_b`. The curve parameter a is −3.
  - `fmod(x: int) -> int` = `x % p256_p()`; `finv(x: int) -> int` = `fmod(pow(x, (p256_p() − 2) as nat))`.
  - `pub enum SpecPoint { Infinity, Affine(int, int) }` and `pub open spec fn p256_g() -> SpecPoint`.
  - `pub open spec fn on_curve(x: int, y: int) -> bool`: `0 <= x < p && 0 <= y < p && fmod(y·y) == fmod(x³ − 3x + b)`.
  - `pub open spec fn point_add(a: SpecPoint, b: SpecPoint) -> SpecPoint` (SEC 1 §2.2.1):
    - Infinity is the identity;
    - x1 == x2 with y1 + y2 ≡ 0 gives Infinity;
    - doubling uses λ = (3x² − 3)/(2y);
    - otherwise λ = (y2 − y1)/(x2 − x1);
    - x3 = λ² − x1 − x2 and y3 = λ(x1 − x3) − y1, all `fmod`.
  - `pub open spec fn scalar_mult(k: nat, pt: SpecPoint) -> SpecPoint`: k = 0 gives Infinity, else `point_add(pt, scalar_mult(k − 1, pt))`, with `decreases k`. It is written for readability; it is never computed.
  - `pub open spec fn scalar_valid(d: Seq<u8>) -> bool`: `d.len() == 32 && 1 <= os2ip(d) < p256_n()`. This is the FIPS 186-5 / SEC 1 §3.2.1 private-key range.
  - `pub open spec fn sec1_encode(pt: SpecPoint) -> Seq<u8>` (SEC 1 §2.3.3, uncompressed): `[0x04] ++ i2osp(x, 32) ++ i2osp(y, 32)`. Infinity gives `[0x00]` and is unreachable from valid scalars.
  - `pub open spec fn sec1_decode(b: Seq<u8>) -> Option<SpecPoint>` (SEC 1 §2.3.4, restricted to the uncompressed form by RFC 8446 §4.2.8.2): `Some(Affine(x, y))` iff `b.len() == 65`, `b[0] == 4`, x = `os2ip(b[1..33])`, y = `os2ip(b[33..65])` and `on_curve(x, y)`. Since on_curve requires x, y < p, the non-canonical x ≥ p is rejected. The cofactor is 1, so no subgroup check is needed.
  - `pub open spec fn spec_p256_public_key(d: Seq<u8>) -> Option<Seq<u8>>`: `None` if `!scalar_valid(d)`, else `Some(sec1_encode(scalar_mult(os2ip(d), p256_g())))`.
  - `pub open spec fn spec_p256_ecdh(d: Seq<u8>, peer: Seq<u8>) -> Option<Seq<u8>>` (SEC 1 §3.3.1):
    - `None` if `!scalar_valid(d)` or `sec1_decode(peer)` is `None`;
    - for `Affine(x, _) = scalar_mult(os2ip(d), Q)`, the result is `Some(i2osp(x, 32))`. That's the full 32 bytes with no leading-zero stripping (RFC 8446 §7.4.2);
    - Infinity gives `None`.
  - `pub fn p256_public_key(d: &[u8]) -> (r: Option<[u8; 65]>)`: external_body, with `requires d@.len() == 32` and `ensures r.deep_view() == spec_p256_public_key(d@)`.
  - `pub fn p256_ecdh(d: &[u8], peer: &[u8]) -> (r: Option<[u8; 32]>)`: external_body, with `requires d@.len() == 32` and `ensures r.deep_view() == spec_p256_ecdh(d@, peer@)`.
- Shim:
  - `p256::SecretKey::from_bytes(d.into()).ok()?` handles the range check;
  - `public_key().to_sec1_point(false)` via `p256::elliptic_curve::sec1::ToSec1Point`, then `as_bytes().try_into().ok()`.
  - For ECDH, first return `None` unless `peer.len() == 65 && peer[0] == 4`. `from_sec1_bytes` would accept compressed points, which the spec rejects.
  - Then `PublicKey::from_sec1_bytes(peer).ok()?` and `p256::ecdh::diffie_hellman(sk.to_nonzero_scalar(), pk.as_affine()).raw_secret_bytes()`.

- [ ] **Step 1: Failing tests:**
  - `rfc6979_a25_public_key`: d = `c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721` gives `04` ++ `60fed4ba255a9d31c961eb74c6356d68c049b8923b61fa6ce669622e60f29fb6` ++ `7903fe1008b8bc99a41ae9e95628bc64f2f1b20c2d7e9f5177a3c294d4462299`.
  - `rfc5903_ecdh` (RFC 5903 §8.1):
    - i = `c88f01f510d9ac3f70a292daa2316de544e9aab8afe84049c62a9c57862d1433` has public key `04` ++ `dad0b65394221cf9b051e1feca5787d098dfe637fc90b9ef945d0c3772581180` ++ `5271a0461cdb8252d61f1c456fa3e59ab1f45b33accf5f58389e0577b8990bb3`;
    - r = `c6ef9c5d78ae012a011164acb397ce2088685d8f06bf9be0b283ab46476bee53` has public key `04` ++ `d12dfb5289c8d4f81208b70270398c342296970a0bccb74c736fc7554494bf63` ++ `56fbf3ca366cc23e8157854c13c58d6aac23f046ada30f8353e74f33039872ab`;
    - both `p256_ecdh(i, g^r)` and `p256_ecdh(r, g^i)` give `d6840f6b42f6edafd13116e0e12565202fef8e9ece7dce03812464d04b9442de`.
  - `ecdh_rejects_invalid`, with d = i. Each of these peers gives `None`:
    - g^r with its last byte xor 1 (off-curve);
    - `g^r[..64]`;
    - `g^r[1..]`;
    - `g^r[..33]` with byte 0 set to `0x03`;
    - `[0x00]`;
    - `04 ++ ffffffff00000001000000000000000000000000ffffffffffffffffffffffff ++ 66485c780e2f83d72433bd5d84a06bb6541c2af31dae871728bf856a174f93f4`, which is x = p, non-canonical.

    In contrast, `04 ++ 32×00 ++ 66485c78…f3f4` (the valid point with x = 0) gives `Some`. Also `p256_ecdh(32×00, g^r)` is `None`.
  - `scalar_range`: `p256_public_key` of 32×`00`, of n, and of 32×`ff` is `None`; n − 1 (`…632550`) is `Some`.
  - `p256_constants_match_rustcrypto`:
    - `P256_N` equals `<p256::NistP256 as p256::elliptic_curve::Curve>::ORDER.to_be_bytes()`;
    - `P256_B` equals `<p256::NistP256 as primeorder::PrimeCurveParams>::EQUATION_B.to_bytes()`;
    - `P256_P` equals the bytes of 2²⁵⁶ − 2²²⁴ + 2¹⁹² + 2⁹⁶ − 1, written out from the formula as 8 big-endian u32 words: `ffffffff 00000001 00000000 00000000 00000000 ffffffff ffffffff ffffffff`;
    - `04 ++ P256_GX ++ P256_GY` equals `p256_public_key` of 31×`00` ++ `01`.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3: Implement.** Write the specs, the exec fns, the shim fns, the Cargo lines (p256 and dev primeorder) and TRUSTED rows for `p256_public_key` and `p256_ecdh`. Then do the matrix Notes append (Global Constraints).
- [ ] **Step 4:** Run the four checks and the fresh verify. Tests: 5 new pass. Escape count: 9.
- [ ] **Step 5: Commit:** `feat(crypto): P-256 curve, SEC1, ECDH specs + shim (SP 800-186, SEC 1)`

---

### Task 5: ECDSA P-256/SHA-256 with RFC 6979, and verified DER encoding

**Files:**
- Create: `crates/crypto/src/ecdsa.rs`
- Modify: `lib.rs`, `shim.rs`, `TRUSTED.md`
- Test: `crates/crypto/tests/ecdsa.rs`

**Interfaces:**
- Consumes: `spec_sha256`, `spec_hmac_sha256`, `scalar_mult`, `p256_g`, `p256_n`, `scalar_valid`, `os2ip`, `i2osp`, `MAX_INPUT_LEN`.
- Produces (`crypto::ecdsa`). The specs are specialized to qlen = hlen = 256, so `bits2int` is `os2ip` and step h.2 takes exactly one HMAC.
  - `spec fn rfc6979_init(x: Seq<u8>, h1: Seq<u8>) -> (Seq<u8>, Seq<u8>)` (RFC 6979 §3.2 steps b–g) returns (K, V):
    - start from V = 32×`01` and K = 32×`00`;
    - K = HMAC_K(V ++ [0x00] ++ x ++ b2o), then V = HMAC_K(V);
    - K = HMAC_K(V ++ [0x01] ++ x ++ b2o), then V = HMAC_K(V);
    - here x is the 32-byte private key (its `int2octets`), and b2o = `i2osp(os2ip(h1) % n, 32)` (`bits2octets`, §2.3.4, **with** `mod q`).
  - `spec fn rfc6979_state(x, h1, i: nat) -> (Seq<u8>, Seq<u8>)`: the (K, V) before attempt i.
    - attempt 0 is `rfc6979_init`;
    - attempt i+1 starts from attempt i's (K, V): T = HMAC_K(V), K' = HMAC_K(T ++ [0x00]), V' = HMAC_K'(T). That is step h.3's retry.
  - `spec fn rfc6979_k(x, h1, i: nat) -> nat` = `os2ip(HMAC_K(V))` for the (K, V) of `rfc6979_state(x, h1, i)` (step h.2 then h.3; compared to n, **not** reduced).
  - `spec fn ecdsa_r(k: nat) -> nat`: the x-coordinate of `scalar_mult(k, p256_g())` mod n (RFC 6979 §2.4 step 3).
  - `spec fn ecdsa_s(d: nat, h: nat, k: nat) -> nat` = `(pow(k, n − 2) · (h + ecdsa_r(k)·d)) % n` (step 4), where h = `os2ip(h1) % n` (step 1).
  - `spec fn suitable(x, h1, i) -> bool`: `1 <= k < n`, `ecdsa_r(k) != 0` and `ecdsa_s(..) != 0`, for k = `rfc6979_k(x, h1, i)`. The r condition is RFC 6979 §3.4; the s condition is FIPS 186-5 §6.4.1, which is also what RustCrypto does.
  - `pub open spec fn spec_ecdsa_p256_sha256_sign(d: Seq<u8>, msg: Seq<u8>) -> Option<Seq<u8>>`:
    - `None` if `!scalar_valid(d)`;
    - with h1 = `spec_sha256(msg)`: if some i is `suitable` with no smaller suitable j, the result is `Some(i2osp(r, 32) ++ i2osp(s, 32))` for the least such i (`choose` with explicit triggers);
    - otherwise `None`;
    - no low-S normalization.
  - `pub fn p256_ecdsa_sign(d: &[u8], msg: &[u8]) -> (r: Option<[u8; 64]>)`: external_body, with `requires d@.len() == 32, msg@.len() <= MAX_INPUT_LEN` and `ensures r.deep_view() == spec_ecdsa_p256_sha256_sign(d@, msg@)`.
  - `spec fn der_uint_content(x: nat) -> Seq<u8>` (X.690 §8.3): the minimal big-endian octets of x (`[0x00]` for 0), with `0x00` prepended when the first octet is ≥ 0x80.
  - `pub open spec fn spec_ecdsa_der(sig: Seq<u8>) -> Seq<u8>`: `[0x30, L] ++ [0x02, l_r] ++ der_uint_content(r) ++ [0x02, l_s] ++ der_uint_content(s)`.
    - r = `os2ip(sig[0..32])` and s = `os2ip(sig[32..64])`;
    - this is ECDSA-Sig-Value (RFC 8446 §4.2.3 → RFC 3279 §2.2.3);
    - every length is ≤ 70, so DER short-form lengths (X.690 §8.1.3.4) suffice.
  - `pub fn serialize_ecdsa_der(sig: &[u8], out: &mut Vec<u8>)` is **verified, not external_body**. It requires `sig@.len() == 64` and ensures `out@ == old(out)@ + spec_ecdsa_der(sig@)`.
- Shim: `p256::ecdsa::SigningKey::from_bytes(d.into()).ok()?`, then `Signer::sign(msg)` into `p256::ecdsa::Signature`, then `to_bytes().into()`.

- [ ] **Step 1: Failing tests:**
  - `rfc6979_a25_sha256`, with d = `c9afa9d8…120f6721` (Task 4):
    - `b"sample"` gives r ++ s = `efd48b2aacb6a8fd1140dd9cd45e81d69d2c877b56aaf991c34d0ea84eaf3716` ++ `f7cb1c942d657c41d436c7a1b6e29f65f3e900dbb9aff4064dc4ab2f843acda8`;
    - `b"test"` gives `f1abb023518351cd71d881567b1ea663ed3efcf6c5132b354f28d3b0b7d38367` ++ `019f4113742a2b14bd25926b49c649155f267e60d3814b4c0cc84250e46f0083`.
  - `ecdsa_scalar_range`: d = 32×`00` and d = n are `None`; d = n − 1 is `Some`.
  - `der_vectors`. The expected DER values were cross-checked with Python `cryptography`'s `encode_dss_signature`.
    - the "sample" sig gives `3046022100efd48b2aacb6a8fd1140dd9cd45e81d69d2c877b56aaf991c34d0ea84eaf3716022100f7cb1c942d657c41d436c7a1b6e29f65f3e900dbb9aff4064dc4ab2f843acda8`;
    - the "test" sig gives `3045022100f1abb023518351cd71d881567b1ea663ed3efcf6c5132b354f28d3b0b7d383670220019f4113742a2b14bd25926b49c649155f267e60d3814b4c0cc84250e46f0083`;
    - r = 1, s = 1 (as 32-byte big-endian each) gives `3006020101020101`;
    - r = 0, s = 0 gives `3006020100020100`;
    - r = `7f` ++ 31×`00` and s = `0080` ++ 30×`00` give `304402207f` ++ 31×`00` ++ `022000` ++ `80` ++ 30×`00`;
    - `serialize_ecdsa_der` appends: with `out = [0xAA]` beforehand, the output starts with `0xAA`.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3: Implement.**
  - **Specs, exec sign and shim**, plus the TRUSTED row for `p256_ecdsa_sign`.
  - **`serialize_ecdsa_der`**:
    - Find the first nonzero byte in each half with a loop over `sig`.
    - Push `0x30`, the length, then each INTEGER.
    - Prove it against `spec_ecdsa_der` with a lemma that the minimal-octets strip of a 32-byte big-endian slice equals the minimal octets of its `os2ip`.
  - **Fallback if that lemma doesn't close after real attempts:** make `serialize_ecdsa_der` an external_body backed by a shim that does the same strip in plain Rust, add a TRUSTED row (Removed in phase 5), and report it. Don't weaken the ensures.
- [ ] **Step 4:** Run the four checks and the fresh verify. Tests: 3 new pass. Escape count: 10, or 11 if the DER fallback was used.
- [ ] **Step 5: Commit:** `feat(crypto): ECDSA P-256 + RFC 6979 spec + shim, verified DER signature encoding`

---

### Task 6: RSASSA-PSS-SHA256 signing (2048–4096-bit modulus)

**Files:**
- Create: `crates/crypto/src/rsa.rs`
- Modify: `lib.rs`, `shim.rs`, `Cargo.toml`, `TRUSTED.md`, `docs/requirements.md` (RFC 8446 §9.1 (req) Notes)
- Test: `crates/crypto/tests/rsa_pss.rs`

**Interfaces:**
- Consumes: `spec_sha256`, `os2ip`, `i2osp`, `xor_bytes`, `MAX_INPUT_LEN`.
- Produces (`crypto::rsa`, RFC 8017; signing only, per the RSA ruling: no RSA verification code):
  - `pub struct RsaPrivateKey { pub n: Vec<u8>, pub e: Vec<u8>, pub d: Vec<u8>, pub p: Vec<u8>, pub q: Vec<u8> }`.
    - Each field is big-endian unsigned, and leading zeros are allowed.
    - The unverified shell fills it from the PKCS#8 key, which is already in the trusted base.
    - `impl View` gives `RsaKeySpec { n: nat, e: nat, d: nat, p: nat, q: nat }` via `os2ip`.
  - `spec fn is_prime(x: nat) -> bool`: `x > 1 && forall|k: nat| 1 < k < x ==> #[trigger] (x % k) != 0`.
  - `spec fn bitlen(x: nat) -> nat`: 0 for 0, else `1 + bitlen(x / 2)`.
  - `pub open spec fn rsa_key_wf(k: RsaKeySpec) -> bool` (RFC 8017 §3.1–3.2, restricted to two primes and our size range):
    - `is_prime(p)`, `is_prime(q)`, `p != q` and `n == p·q`;
    - `3 <= e < n`;
    - `(e·d) % (p − 1) == 1 && (e·d) % (q − 1) == 1`, i.e. e·d ≡ 1 mod λ(n);
    - `2048 <= bitlen(n) <= 4096`.
  - `spec fn mgf1_sha256(seed: Seq<u8>, len: nat) -> Seq<u8>` (B.2.1): the first `len` bytes of the concatenation, for counter = 0 .. ⌈len/32⌉ − 1, of `spec_sha256(seed ++ i2osp(counter, 4))`.
  - `pub open spec fn emsa_pss_encode(msg: Seq<u8>, em_bits: nat, salt: Seq<u8>) -> Seq<u8>` (§9.1.1, sLen = hLen = 32):
    - emLen = ⌈em_bits/8⌉;
    - mHash = H(msg);
    - H = H(8×`00` ++ mHash ++ salt);
    - DB = zeros(emLen − 66) ++ [0x01] ++ salt;
    - maskedDB = DB ⊕ `mgf1_sha256(H, emLen − 33)`, then clear the leftmost `8·emLen − em_bits` bits of `maskedDB[0]`;
    - the result is maskedDB ++ H ++ [0xbc].

    Step 1's "message too long" is the `MAX_INPUT_LEN` requires. Step 3's "encoding error" can't happen, because emLen ≥ 256 > 66 under wf. Step 4's random salt is the caller's `salt`.
  - `pub open spec fn spec_rsassa_pss_sign(k: RsaKeySpec, msg: Seq<u8>, salt: Seq<u8>) -> Seq<u8>` (§8.1.1):
    - modBits = `bitlen(k.n)`;
    - EM = `emsa_pss_encode(msg, modBits − 1, salt)`;
    - s = `pow(os2ip(EM), k.d) % k.n`, which is RSASP1 §5.2.1 form (a); the shim's CRT agrees for wf keys;
    - the result is `i2osp(s, ⌈modBits/8⌉)`.
  - `pub fn rsa_pss_sha256_sign(key: &RsaPrivateKey, msg: &[u8], salt: &[u8]) -> (r: Option<Vec<u8>>)`: external_body.
    - requires `rsa_key_wf(key@)`, `msg@.len() <= MAX_INPUT_LEN` and `salt@.len() == 32`;
    - ensures `r matches Some(s) ==> s@ == spec_rsassa_pss_sign(key@, msg@, salt@)`.
    - The ensures is one-directional: the shim returns `None` instead of panicking when RustCrypto rejects a key that wf allows (e ≥ 2³³, `RsaPublicKey::MAX_PUB_EXPONENT`) or when its fault check fails. Phase 4 maps `None` to `internal_error`, and Phase 5 may strengthen this to always-`Some`.
    - Primality is a `requires` that no verified code can establish. It flows up to the trusted shell's key loading, so say so in the TRUSTED row.
- Shim. This exact shape is probe-verified; the obvious alternative mis-sizes signatures.
  ```rust
  struct SaltRng<'a>(&'a [u8], bool); // yields the caller's salt exactly once
  impl rsa::rand_core::TryRng for SaltRng<'_> {
      type Error = core::convert::Infallible;
      fn try_next_u32(&mut self) -> Result<u32, Self::Error> { unreachable!("PSS draws only the salt") }
      fn try_next_u64(&mut self) -> Result<u64, Self::Error> { unreachable!("PSS draws only the salt") }
      fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Self::Error> {
          assert!(!self.1 && dst.len() == 32, "unblinded PSS draws exactly one 32-byte salt");
          dst.copy_from_slice(self.0); self.1 = true; Ok(())
      }
  }
  impl rsa::rand_core::TryCryptoRng for SaltRng<'_> {}
  // ponytail: rebuilds and re-validates the RustCrypto key on every signature; the whole shim goes in Phase 5.
  pub(crate) fn rsa_pss_sign(n: &[u8], e: &[u8], d: &[u8], p: &[u8], q: &[u8], msg: &[u8], salt: &[u8]) -> Option<Vec<u8>> {
      let u = |b: &[u8]| rsa::BoxedUint::from_be_slice_vartime(b);
      let key = rsa::RsaPrivateKey::from_components(u(n), u(e), u(d), vec![u(p), u(q)]).ok()?;
      // Not pss::SigningKey + Signature::to_vec: that pads to limb width (264 bytes for a 2049-bit n).
      key.sign_with_rng(&mut SaltRng(salt, false), rsa::Pss::<Sha256>::new_with_salt(32), &Sha256::digest(msg)).ok()
  }
  ```
  Use `Pss::new_with_salt`, which is unblinded. `new_blinded_with_salt` would draw more RNG bytes and trip the assert. The TRUSTED row must note RUSTSEC-2023-0071 (Marvin timing side channel): it is unpatched in every rsa release including rc.19, unblinded signing doesn't help, RSA certificates are opt-in, and constant-time is a design non-goal until Phase 5 replaces this.

- [ ] **Step 1: Failing tests.** Add a helper `key(p_hex, q_hex) -> (crypto::rsa::RsaPrivateKey, rsa::RsaPrivateKey)`:
  - build the RustCrypto key with `rsa::RsaPrivateKey::from_p_q(p, q, BoxedUint::from(65537u32))`;
  - fill our struct with `to_be_bytes().to_vec()` of `n()`, `e()`, `d()`, `primes()[0]` and `primes()[1]`, using the traits `rsa::traits::{PublicKeyParts, PrivateKeyParts}`.

  Add a shared `check(p, q, bits)`:
  - assert `n().bits() == bits`;
  - set salt = `[0, 1, …, 31]` and msg = `b"TLS 1.3, server CertificateVerify"`, and let s = `rsa_pss_sha256_sign(..).unwrap()`;
  - `s.len() == ⌈bits/8⌉`;
  - signing again with the same salt gives the same s; flipping `salt[0]` gives a different s;
  - `k.to_public_key().verify(rsa::Pss::<sha2::Sha256>::new_with_salt(32), &sha256(msg), &s)` is `Ok`;
  - **salt recovery:**
    - EM = the last ⌈(bits−1)/8⌉ bytes of `rsa::hazmat::rsa_encrypt(&pub, &BoxedUint::from_be_slice(&s, k.n_bits_precision()))`;
    - `EM[last] == 0xbc`;
    - H = `EM[emLen−33 .. emLen−1]`;
    - DB = `EM[..emLen−33]` ⊕ (a test-local MGF1 over `crypto::sha256::sha256`);
    - `DB[DB.len()−32..] == salt`.

  The two tests:
  - `pss_rfc9500_2048`: `check(p, q, 2048)` with the RFC 9500 §2.1 testRSA2048 primes (e = 65537):
    - p = `dd105702382f232b3681f53791e22617c7bf4e9acb81ed48daf6d6995da3eab642839aff012d2ea628b90af279fd3e6f7c93cd80f072f01ff2443b3ee8f24ed469a79613a41bd24020f92fd11059bd1d0f301b5ba7a9d3637ca8d65c1a9815417d8eab734b0b4f3a2c661d9a1a82f3ac734c40530669ab8e473045a58e65539d`
    - q = `ccf1e5bb90c8e9781ea75bebf10bc252e11eb023a0260f1887552a56863f4a6421e8c600bf523d6cb1b0adbdd65bfee4a88a037e3d1a415e5bb95648da5a0ca26b54f4a63948522c3d5f89b94a72efff95134d5940ce45758f308980908956588eef575b3e4bc4c368cfe813ee9c252c2b02e0df91f1aa01938d38685d60ba6f`
  - `pss_rsa2049_len_and_salt`: `check(p, q, 2049)`. These primes were generated for this plan (Miller–Rabin, 40 rounds); any primes whose product has 2049 bits work, and the bit-count assert catches a bad copy.
    - p = `01fa9ff01c702938f8290b7fe5099537cf6c0d0b48a1f9ef02a02614387c464ab96737256ee4d1cb82c27c71f748737adb1939bd1aa6732ea3da37355f1b516b6c7052da370af35f9df697cdf0da1d140f29fd9b87bd777f21523030824f3ce0ffab10b79aeb16dba61509d65841c38f8721db01fcb63dab8c82a82312de30ca63`
    - q = `cc0ecbe9727c4d3d1651a1be964f3f89e202875507f8686b1168565b262ace6724e33d24b23471ea83d13966f35c5aa8a2cdb9b556862c9f09b2c5afccec2868742a7b9b63a92e72a4145117a61fd8f33a74e2b1b32d45a08827cdc59dd8bc39c3a10fc341fd31a01b2362a0dad100c91ec4af744c23e68aba202b23da2403dd`
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3: Implement** the specs, the struct and View, the exec fn, the shim, the Cargo lines (rsa, and the dev rsa with hazmat), the TRUSTED row for `rsa_pss_sha256_sign` and the matrix Notes append.
- [ ] **Step 4:** Run the four checks and the fresh verify. Tests: 2 new pass, 18 in `crypto` in total. Escape count: 11 (12 with the Task 5 fallback).
- [ ] **Step 5: Commit:** `feat(crypto): RSASSA-PSS-SHA256 signing spec + shim (RFC 8017 §8.1, §9.1)`

---

## Exit criteria (Phase 3a)

- All four checks pass on the merged tree, and `verify.sh` prints its summary line.
- TRUSTED.md has one `crypto::` row per `external_body` (11), all "Removed in phase 5", plus the `shim.rs` row and the RustCrypto pins.
- RFC 8446 §4.2.8.2 and §9.1 (req) Notes carry their `3a spec:` pointers, with no ✅ anywhere for 3a.
- Phase 3e can `use crypto::{gcm::*, aes::*, hkdf::*}` and prove against `spec_gcm_seal`, `spec_gcm_open`, `spec_aes128_encrypt` and `spec_hkdf_expand`.
- The branch `phase-3a` is merged into `main`.

## Self-review (done while writing)

- **Spec coverage.** Every primitive in the design's Phase 3 crypto bullet has a task:
  - SHA-256 → 1; HMAC, HKDF → 2; AES-128, GCM → 3; P-256, SEC1, ECDH → 4; ECDSA + RFC 6979 + DER → 5; RSASSA-PSS → 6.
  - Excluded per the design: verification code (ECDSA/RSA), ChaCha20, AES-256, X25519, SHA-384, HKDF-Expand-Label.
- **Types.** One name per item across tasks: `spec_sha256`, `spec_hmac_sha256`, `scalar_valid`, `scalar_mult`, `p256_g`, `p256_n`, `MAX_INPUT_LEN`, `os2ip`, `i2osp`, `xor_bytes`.
- **Review Focus.** Each item names its pinning test. Item 1 (faithfulness) can be pinned only partly; that is why the Global Constraints state that the specs are unchecked until Phase 5.
- **Proportion.** Code appears only for the RSA shim, the one place where the probe showed the obvious API is wrong. All spec bodies are left to the implementer, with each convention that could go wrong pinned in Interfaces.
