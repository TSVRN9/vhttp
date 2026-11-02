# Phase 5e: Verified RSASSA-PSS signing, zero escapes, CAVP + Wycheproof vectors — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the last escape, `crypto::rsa::rsa_pss_sha256_sign`, with verified constant-time Rust + Verus, delete the RustCrypto shim, take `escapes accounted` to 0, and run the owed CAVP and Wycheproof files under `cargo test`.

**Architecture:** A new `crates/crypto/src/bignum.rs` holds Montgomery arithmetic over `[u64; 64]` arrays with a public limb count `nl`. `rsa.rs` gains MGF1, EMSA-PSS, an always-multiply `m^d mod n` over n with no CRT, and a CT root that takes `n` public and `d` secret. Vectors land first, as an independent task.

**Tech Stack:** Verus 0.2026.10.04.426d8b0 (`~/.local/opt/verus/0.2026.10.04.426d8b0/verus-x86-linux`), vstd `=0.0.0-2026-10-04-0306`. No new crates. Vector tests use a small hand-written `.rsp` and JSON parser; no JSON dev-dep.

**Spec:** `docs/superpowers/specs/2026-10-27-verified-http3-design.md` (lines 18-22, Phase 5 at lines 116-117); `crates/crypto/src/rsa.rs` (frozen spec fns).

**Branch:** `phase-5e`, worktree `.worktrees/wt-5e`, from `main` e6c1c00. Escapes start at 1.

## Decisions

Probes are in `.worktrees/wt-5e/.superpowers/probe-5e/` (git-ignored): `mm.rs`, `glue.rs`, `bn-labelled.rs` (`mm.rs` with CT labels), `bn_probe.rs` (the KAT test).

- **D1. Limbs: `[u64; 64]` values, `[u64; 66]` accumulator, public `nl: usize`.** `R = 2^(64·nl)`, `32 <= nl <= 64`. Modulus range 2048-4096 bits: `rsa_key_wf` already says so. `Vec<u64>` is out because the CT front end admits Vec only for `u8` and `(u64, u64)`, and widening it grows the TCB. `limbs(s, n)` recurses on an index, not on `take`, so no extensionality is needed.
- **D2. No CRT.** Spec form (a), plain `m^d mod n`, 8k always-multiply steps. The ensures needs nothing more. CRT needs FLT for arbitrary p and q (`p256_group/nt.rs` has it only for certified moduli, so `is_prime` alone would need a new general proof), Garner, secret reductions mod p and q, and exec `d mod (p-1)`, for about 4x speed. Measured (probe, release, full-length exponent): **6.7 ms at 2048 bits, 52 ms at 4096**, plus about 0.3 / 2 ms for R² mod n. 2048-bit RSA signing then costs about one P-256 scalar multiplication (6.1 ms), so a handshake is no worse off. This corrects design spec line 116, which lists CRT (Task 6).
- **D3. Ensures: total.** `pub fn rsa_pss_sha256_sign(key: &RsaPrivateKey, msg: &[u8], salt: &[u8]) -> (r: Vec<u8>)`, `ensures r@ == spec_rsassa_pss_sign(key@, msg@, salt@)`. Same `requires`. No `Option`: under `rsa_key_wf` the spec has no error case (emLen >= 256 > 66). `tls::sign_cv` drops its `None` arm, and its iff drops the `key@ is EcdsaP256 ==>` guard.
- **D4. Proof route: three-pass CIOS row** (`addmul(a·b)`, `addmul(q·m)`, `shift_down`), products as atoms in bookkeeping lemmas, final masked `cond_sub`.
  - Hard lemmas, and what makes them feasible:
    - `lemma_addmul_step`: one distribution by `wp(j)`, on atoms.
    - `lemma_addmul_top`: top carry cannot overflow, from `total < wp(nl + 2)`.
    - `lemma_row_zero`: `(t + q·M) % W == 0`, because `limbs % W == limb[0]` (`lemma_limbs_low`).
    - `lemma_limbs_shift`: drop-first over the index recursion.
    - `lemma_cond_final`: case analysis on atoms.
    - `lemma_acc`: row accumulation to `t·R == a·b + Q·M`.
  - **Probe result:** `mm.rs` has 67 fns including `mont_mul_n`, `pow_step_ct`, `mod_pow_ct` and `neg_inv64`. All verify at `--rlimit 4` **and** `--rlimit 0.6`, about 1 s total, `by (compute_only)` only in `lemma_k_at` and `neg_inv64` (k_at values). Three mutations fail on named obligations: q xored by 1 fails a precondition, a swapped mask in `cond_sub` fails an invariant, a swapped `select_n` fails a postcondition. Compiled, `mod_pow_ct` matches Python `pow()` at 2048 and 4096 bits. Under `ct-driver check`, `mod_pow_ct` (exponent secret) and `neg_inv64` are `ok` with no new `intr` line, no declassify and no driver change. The other 10 roots stay `ok`.
  - `glue.rs` also verifies at `--rlimit 4`: `modulus_bits` against recursive `bitlen`, `limbs_from_be_n`, `lemma_os2ip_tail`, `lemma_prime_odd`. A mutated `bits` branch fails an assertion. It uses `external_body` stubs of `lemma_os2ip_append`, `lemma_os2ip_bound` and `load_be64`, whose real versions are verified in the repo: do not port the stubs.
  - **Preflight:** Task 3, `pad_be`, `pow2_mod`, `limbs_to_be_n`, the Task 4 glue lemmas, `rsasp1` and the `Ghost<RsaKeySpec>` root all pass at `--rlimit 4` and under ct-driver, in `.superpowers/probe-5e-preflight/wt/`.
- **D5. `R` inverse without Bezout.** Ghost `ri = limbs(mont_mul_n(unit, unit, ..))`. `mont_mul_n`'s ensures gives `(ri·R) % M == 1 % M` directly. One extra multiply at runtime; no gcd proof. `mp` comes from Newton (`neg_inv64`, six steps from `y = 1`, via `u128` multiply and the existing `wrapping_sub` intr).
- **D6. What is claimed.** `s = I2OSP(m^d mod n, k)` and nothing else. Primality's only use is `n` odd: `p = 2` would need `ed % 1 == 1`, which is false, so `is_prime` at k = 2 makes p odd; likewise q (`lemma_prime_odd`, `lemma_odd_mul`). No Euler theorem, no proof that `s^e == EM`: tests check that (RustCrypto, ring, CAVP). Exec reads only `n`, `d`, `msg` and `salt`; `e`, `p` and `q` stay in the struct for `rsa_key_wf`. No proof needs `EM < n`: `mont_mul_n` leaves `a` unbounded, so EM only has to fit `nl` limbs.
- **D7. CT labels and declassify.** Labels are per parameter and `n` must be public (the shift `0xff >> (8·emLen − emBits)`, Vec sizes and the bit scan depend on it), so `key` cannot be the root. Root: `pub(crate) fn rsa_pss_sign_inner(n: &[u8], d: &[u8], msg: &[u8], salt: &[u8], Ghost(k): Ghost<RsaKeySpec>) -> Vec<u8>`, `#[cfg_attr(ct_check, ct::secret(d, salt, msg), ct::public(n))]` (msg secret only if Task 5's ct-check stays `ok` with no new declassify, else `ct::secret(d, salt), ct::public(n, msg)` and Task 5 reports why). The pub fn only projects fields and sits outside the analysed set; TRUSTED says so. Secret-labelled helpers may take `n`: nothing branches on limbs. Only `modulus_bits` branches, on raw public `n` bytes.
  - **Declassify: none.** Count stays 10. The checker covers MIR only. Task 2's `ct_mask` exists because LLVM turned the masked select into a branch on d's bits; Task 6 checks the object code once.
  - **`d` never sets the iteration count.** `d_be = pad_be(d, k)` makes the loop exactly 8k bits, with k from public n. D7 of the CT spec would accept `d.len()` as the loop count; the modexp does not use it. `pad_be`'s own cost does depend on d's encoded length (public under spec D7), so a minimal encoding exposes d's octet length and nothing below that; the loader may zero-pad d to k to remove even that.
- **D8. Vector availability; deviations from the brief, for the user.**
  - **Wycheproof has no RSA-PSS or ECDSA signing file** (its verify file still pins the encoding through s^e): `rsa_pss_*` and `ecdsa_*` are verify schemas, and the user ruled out verify code. Substitutes:
    - RSA-PSS: CAVP `SigGenPSS_186-3.txt` 3072-bit SHA-256 (10 vectors, salt 32; the 2048-bit set uses salt 20, which `requires salt@.len() == 32` excludes), plus RustCrypto verification at 2048-4096.
    - RSA-PSS 2048, salt 32: Wycheproof `rsa_pss_2048_sha256_mgf1_32_test.json`, 63 `valid` rows, run as an EMSA-PSS KAT (`wycheproof_emsa_2048`, Task 3): the only independent salt-32 vector at 2048.
    - RSA modexp: Wycheproof `rsa_pkcs1_{2048,3072,4096}_sig_gen_test.json` SHA-256 `valid` and `acceptable` rows (24 valid, plus 3 `acceptable` edge rows: `short signature` at 2048 and 3072, `signature is close to n`, e = 3; 27 total). The test pads PKCS#1 v1.5 itself and calls `rsasp1`. This is the only Wycheproof RSA coverage and the only 4096-bit vector.
    - ECDSA: CAVP `SigGen.txt` `[P-256,SHA-256]` (15, fixed k, in-crate). Wycheproof `ecdsa_secp256r1_sha256_test.json` runs only as DER re-serialization of its 174 `valid` rows; its 310 `invalid` rows need a verifier and do not run.
  - **No CAVP HKDF file exists:** Wycheproof and RFC 5869 only.
  - `ecdh_secp256r1_test.json` (SPKI-wrapped) is skipped: `ecpoint` covers the same curve checks with raw SEC1.
- **D9. Dev-only stays:** `rsa` (with `hazmat`), `sha2`, `p256`, `primeorder`, `hmac`, `hkdf`, `aes`, `aes-gcm` remain differential dev-dependencies. `cargo tree -p crypto -e normal` must show only `vstd` and its dependencies. No normal dep on RustCrypto.

## Global Constraints

- **No new `external_body`, no `assume`, no new trusted primitives, no new TRUSTED `intr`.** Run `CT_MODE=census` over the new root; a new `intr` line means rewrite the code (read `Vec<u8>` through `.as_slice()`, allocate with `Vec::with_capacity`; `Vec::new`, Vec indexing and `wrapping_mul` are not in `manifest.txt`). If that is impossible, stop and escalate.
- `scripts/verify.sh` ends: `verify.sh: all crates verified, duvet ok, ct ok (10 declassify), cost 19/36, escapes accounted (N)`; N = 1 through Task 4, **0** from Task 5.
- Every function verifies at `--rlimit 4`. Any compute lemma passes fresh at `--rlimit 0.6` (the only ones are the `k_at` asserts in `bignum.rs`; add no others). Integer_ring is unavailable.
- CT: no secret-dependent branch, index, division or shift amount. `ct-check: crypto ok (F fns, 11 roots, 10 declassify)`. Baseline `checked` lines (84 fns by probe count; confirm in Task 2 Step 1) may change only by additions; `diff` them in each report. `cost 19/36` unchanged.
- **Never edit a spec fn body.** If a vector fails after verification passes, the spec or the vector is wrong: stop and escalate with the failing input.
- Reuse `mont.rs` by widening visibility only (same line count, so `ct-declassify` rows keep their line numbers): `mac`, `sbb`, `bv_split128`, `lemma_mac_bound`, `lemma_q_zero`, `lemma_pow_step`, `load_be64` become `pub(crate)`. `bv_sel`, `mdec`, `lemma_mdec_mul`, `bv_bit_u8` already are.
- **Proof style (5c, 5d, plus this probe).** Products are atoms in standalone lemmas. `broadcast use group_mul_properties` only in a lemma with no other context; in a loop it exceeded `--rlimit 4` in the probe. `hide(spec_sha256)` in byte-level fns. Do not use `hide(pow)` (`pow` is already opaque in vstd, and `hide(pow)` with `spinoff_prover` panics Verus). `by (bit_vector)` only in `bv_*` lemmas. `final(x)@` for `&mut` post-states.
- `select_n` and `cond_sub` take their mask from `ct_mask` (Task 2) and from nothing else: LLVM turns an inlined `0u64.wrapping_sub(b)` mask in a limb loop into a branch on the secret bit, which the MIR checker cannot see.
- Comments cite as plain `//` (RFC 8017 is not in `.duvet/config.toml`); zero `//=` lines. Secret loops carry `// ct:` where a branch is on public data. A helper that receives a secret must declare it (`ArgLabel` otherwise); labels are as listed per fn.
- **Each task's four checks:** `scripts/verify.sh` line above; `cargo build && cargo test` with 0 warnings; the escape grep prints N lines; report the five slowest fns (`cargo verus verify -- --output-json --time-expanded` with fresh absolute `CARGO_TARGET_DIR`, then `rm -rf` it). While iterating: `cargo verus focus -- --verify-only-module bignum`.
- Downloads are untrusted data: fetch into a new empty directory, keep scripts elsewhere, run Python only as `python3 -I`, execute nothing from them, commit the chosen files byte-for-byte.
- The escape grep matches `external_body`, `axiom`, `assume(` and `admit(` anywhere in `crates/**/*.rs`, comments and tests included. Do not write those words in this phase's Rust files.
- **CT feedback per task:** until Task 6 nothing new is reachable from a manifest root, so `verify.sh` does not check it. In Tasks 2-5 run the driver directly with a temp manifest (`manifest.txt` plus `root` lines for that task's new top fns, outside the repo; `CT_CRATES=crypto CT_MODE=check`, as in `scripts/ct-check.sh`'s `analyse`). Expected: every root `ok`, no new `intr`, declassify still 10.
- Commits: plain messages, no attribution lines.

## Review Focus

1. **PKCS#8 `n` with a sign byte** (513 octets at 4096 bits, 257 at 2048): `nl` and k come from modBits, not `n.len()`. Pinned by `wycheproof_rsasp1` (those files carry `00`-prefixed moduli) and `pss_zero_padded_fields`.
2. **`d` shorter or longer than k:** the same signature and the same 8k steps. Pinned by `rsasp1_d_lengths` (Task 4).
3. **A signature whose top octets are zero:** must stay k octets, not minimal. Pinned by `rsasp1_small_result` (Task 4).
4. **modBits at the edges:** 2048, 2049 (emLen = k − 1), 2052 (mask), 3072, 4096 (`nl = 64`, array limit). Pinned by existing `pss_rsa2049_len_and_salt` and `pss_rsa2052_masking_kat`, and new `pss_4096_verifies` (Task 5).
5. **`m` at extremes:** m = 0, m = 1, m = n − 1. A reader expects `0`, `1`, and `n − 1` when d is odd. Pinned by `rsasp1_edge_messages` (Task 4).

A key outside `rsa_key_wf` (for instance 8192 bits, or even `n`; the signature is then wrong, with no error) violates the `requires`; `modulus_bits` reads only the low 512 octets, so it is not rejected at signing time. Task 5's TRUSTED edit makes the trusted loader's size check explicit. That loader does not exist yet.

---

### Task 1: Vector files and tests (no RSA code)

**Files:**
- Create: `crates/crypto/tests/data/{nist,wycheproof}/*`, `crates/crypto/tests/data/SOURCES.txt`, `crates/crypto/tests/vecdata/mod.rs`, `crates/crypto/tests/vectors.rs`, `.gitattributes` (`crates/crypto/tests/data/** -text`)
- Modify: `crates/crypto/src/ecdsa.rs` (test mod only), `crates/crypto/tests/rsa_pss.rs`

**Interfaces:**
- Produces, in `tests/vecdata/mod.rs` (in-crate tests include it at file level, as the last lines of the file so ct-declassify line numbers hold: `#[cfg(test)] #[path = "../tests/vecdata/mod.rs"] mod vecdata;`, then `use super::vecdata::*;` in `mod tests`. `tests/*.rs` use plain `mod vecdata;`. The file starts with `#![allow(dead_code)]`: each target uses a different subset):
  - `pub fn hex(s: &str) -> Vec<u8>`
  - `pub fn rsp_records(text: &str) -> Vec<BTreeMap<String, String>>`: strips CR, skips `#`, carries `[K = v]` headers into each record, `[P-256,SHA-256]` as key `section`, a bare `FAIL` as key `FAIL`.
  - `pub enum J { Null, Bool(bool), Num(i64), Str(String), Arr(Vec<J>), Obj(BTreeMap<String, J>) }`, `pub fn parse_json(s: &str) -> J`: panics on malformed input. Strings need `\"` and `\n` (Wycheproof comments and PEMs); no floats occur.
  - `pub fn data(rel: &str) -> String`: reads `tests/data/<rel>`.
- Produces: `crates/crypto/tests/data/**` paths below, for Tasks 3-5.

| file (under `tests/data/`) | source | sha256 |
|---|---|---|
| `nist/SHA256ShortMsg.rsp` | `shs/shabytetestvectors.zip` member `shabytetestvectors/SHA256ShortMsg.rsp` | `75e1cb83994638481808e225b9eb0c1ebd0c232d952ac42b61abce6363be283c` |
| `nist/SHA256LongMsg.rsp` | same zip | `6fac36f37360bcf74ffcf4465c18e30d6d5a04cc90885b901fc3130c16060974` |
| `nist/SHA256Monte.rsp` | same zip | `29ea30c6bb4b84e425fb8c1d731c6bb852dac935825f2bd1143e5d3c4f10bfb9` |
| `nist/HMAC.rsp` | `mac/hmactestvectors.zip` | `cf27b6ad24fc3d72f8d18f8cee8a2b366302395cc50f5d9e607fbce4e98001eb` |
| `nist/gcmEncryptExtIV128.rsp` | `mac/gcmtestvectors.zip` | `30156236f768b0d81e58a3e5bd3bd79ce294cf9ef0ba0a84cf7b869c89ebd9fd` |
| `nist/gcmDecrypt128.rsp` | same zip | `0d1f98d0c9e176ede1f3e85484dd13de92c3436ca97df378ec3481e04c19a732` |
| `nist/SigGen.txt` | `dss/186-4ecdsatestvectors.zip` member `186-4ecdsatestvectors/SigGen.txt` | `95d0a19c03f6d2dc16e9e18fd5c3318e1952e0bc88a45127c996c35b4a15f4e2` |
| `nist/KAS_ECC_CDH_PrimitiveTest.txt` | `components/ecccdhtestvectors.zip` | `456068d3f8aad8ac62a03d19ed3173f00ad51f42b51aeab4753c20f30c01cf23` |
| `nist/SigGenPSS_186-3.txt` | `dss/186-3rsatestvectors.zip` | `46de7f2fccb5f89516e64b5bdb1c4fd456a09c9cc680dd64e0756e62ff5000ec` |
| `wycheproof/hmac_sha256_test.json` | Wycheproof | `2d201cfa61d1bf95e6f5d07d96634b4a348b31e8eaa277ad7c8d09677b7a743f` |
| `wycheproof/hkdf_sha256_test.json` | Wycheproof | `bb2b462a38b251cb52a2aede706d6d4b62b26864f4e80c95497507ddb07c5f1e` |
| `wycheproof/aes_gcm_test.json` | Wycheproof | `985e5ecc172e181eaf49e89508b9470dcf478002eb7e8559c707eb42dc97dfe7` |
| `wycheproof/ecdh_secp256r1_ecpoint_test.json` | Wycheproof | `648f16d077caf2400d02331ca51f44744c72c799830c8d0595d0b18b6dd9f886` |
| `wycheproof/ecdsa_secp256r1_sha256_test.json` | Wycheproof | `182db4f3e230f6f9fa9f800d2a614dede30284b8e8438bbfe1171905402e9332` |
| `wycheproof/rsa_pkcs1_2048_sig_gen_test.json` | Wycheproof | `587b3d27d3429f2118cb02818da4d08eb3f36f50c747939eb550fae4337ccbf0` |
| `wycheproof/rsa_pkcs1_3072_sig_gen_test.json` | Wycheproof | `45153219d486fd135d35aa968a957a0c015c7829e8dc59bea5f87e6c30912677` |
| `wycheproof/rsa_pkcs1_4096_sig_gen_test.json` | Wycheproof | `f13eadbec6c45291cb33e6b2fa0a0c2b862d0bd2eaec29f930d3b78067cd48c7` |
| `wycheproof/rsa_pss_2048_sha256_mgf1_32_test.json` | Wycheproof (85 KB) | compute at fetch; record in SOURCES.txt and here |

NIST base URL: `https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/`. NIST zip sha256s as fetched 2026-11-02, for SOURCES.txt: shabytetestvectors `929ef80b7b3418aca026643f6f248815913b60e01741a44bba9e118067f4c9b8`, hmactestvectors `418c3837d38f249d6668146bd0090db24dd3c02d2e6797e3de33860a387ae4bd`, gcmtestvectors `f9fc479e134cde2980b3bb7cddbcb567b2cd96fd753835243ed067699f26a023`, 186-4ecdsatestvectors `fe47cc92b4cee418236125c9ffbcd9bb01c8c34e74a4ba195d954bcb72824752`, ecccdhtestvectors `5fff092551f2d72e89a3d9362711878708f9a14b502f0dfae819649105b0ea39`, 186-3rsatestvectors `8405aeb3572a4f98ed4b1a3ccb3f2f49e725462dd28ec4759d6a15d88855d19c`. Versions: the file headers (CAVS 11.1/11.4/14.1). Wycheproof URL: `https://raw.githubusercontent.com/C2SP/wycheproof/d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9/testvectors_v1/<file>` (commit 2026-10-23, Apache-2.0). If a sha differs from this table, stop and escalate.

- [ ] **Step 1: Download into a new empty directory, `sha256sum -c` against the table, copy verbatim. Write `SOURCES.txt`,** one line per file: `sha256  path  url[#member]  version`. NIST CAVP files are US-government works; Wycheproof is Apache-2.0: say so at the top.
- [ ] **Step 2: Write the tests in `tests/vectors.rs`.** Each pins its count:

  | test | filter and assertion | count |
  |---|---|---|
  | `sources_match` | every `SOURCES.txt` line: `crypto::sha256::sha256(file)` == sha256 column | 18 |
  | `cavp_sha256_short`, `cavp_sha256_long` | parse `Msg` by `Len` (`Len = 0` has `Msg = 00`); digest == `MD` | 65, 64 |
  | `cavp_sha256_monte` | FIPS SHAVS Monte: MD[i] = H(MD[i-3] ‖ MD[i-2] ‖ MD[i-1]), 1000 per checkpoint | 100 |
  | `cavp_hmac` | `[L=32]`; `hmac_sha256(Key, Msg)[..Tlen] == Mac` | 225 |
  | `wycheproof_hmac` | `tagSize/8` prefix; `valid` equal, `invalid` differs | 174 (66, 108) |
  | `wycheproof_hkdf` | `valid`: expand(extract(salt, ikm), info, size) == okm; `size > 8160` is `invalid` and skipped | 83 run, 3 skipped |
  | `cavp_gcm_encrypt` | `Keylen=128`, `IVlen=96`, `Taglen=128`; seal == `CT ‖ Tag` | 375 |
  | `cavp_gcm_decrypt` | same filter; `FAIL` gives `None`, else `Some(PT)` | 375 (196 FAIL) |
  | `wycheproof_gcm` | `keySize=128`, `ivSize=96`; `valid`: seal and open agree; `invalid`: open is `None` | 67 (40, 27) |
  | `cavp_ecdh` | `[P-256]`; `p256_ecdh(dIUT, 04‖QCAVS) == ZIUT`, `p256_public_key(dIUT) == 04‖QIUT` | 25 |
  | `wycheproof_ecdh` | private normalized to 32 octets (strip `00`, left-pad short); 65-octet public and `valid`: `Some(shared)`; every other row (`invalid`, 33-octet `acceptable`, empty) `None` | 355 (330 valid) |
  | `wycheproof_ecdsa_der` | `valid` rows: parse the DER `sig`, normalize r and s to 32 octets each (drop a `00` sign octet, left-pad short values), concatenate, `serialize_ecdsa_der` == `sig` | 174 |

  In `tests/rsa_pss.rs`, `cavp_pss_3072`: `[mod = 3072]`, `SHA256`, salt 32 octets. `n`, then `e` and `d`, sit in their own blank-line records before the `SHAAlg` records, not in `[K = v]` headers: carry the latest `n`, `e`, `d` while walking the records. Key from `n`, `e`, `d` (`rsa::RsaPrivateKey::from_components(n, e, d, vec![])` recovers p and q, filling our struct); `rsa_pss_sha256_sign(&key, &Msg, &SaltVal).unwrap() == S`. Count 10. (Task 5 removes the `.unwrap()`.)

  In `src/ecdsa.rs`'s test mod, `cavp_siggen_file`: `[P-256,SHA-256]`, h = SHA-256(Msg); `ecdsa_r_exec(k)` == R, `ecdsa_s_exec` == S, `p256_public_key(d) == 04‖Qx‖Qy`. Count 15. If this table holds the same 15 vectors as the inline SIGGEN table and `cavp_siggen_fixed_k` in `src/ecdsa.rs`, compare them and replace those two with it (everything is after line 841, so declassify lines hold); otherwise keep both.
- [ ] **Step 3: Run `cargo test -p crypto --test vectors --test rsa_pss` and the lib tests.** Expected: all pass on the current code. A failure means a real bug or a parser bug: distinguish them, and escalate the former with the input.
- [ ] **Step 4: Mutation check.** Flip one hex digit of an expected value in a temp copy of each parser path (rsp, JSON): the test must fail, then revert. `sources_match` must fail on a flipped data byte.
- [ ] **Step 5: Report debug timings.** If `cargo test -p crypto` grows by over 60 s debug, thin with `cfg!(debug_assertions)` and say what. Four checks, N = 1. TRUSTED's five spec rows (SHA, HMAC/HKDF, AES-GCM, P-256, ECDSA) gain the file names; the ECDSA row says `Wycheproof ecdsa file: DER re-serialization only`, not signing coverage. Commit: `test(crypto): CAVP and Wycheproof vectors`.

---

### Task 2: `bignum.rs`: Montgomery multiply over `[u64; 64]`

**Files:**
- Create: `crates/crypto/src/bignum.rs` (`mod bignum;`). Port `bn-labelled.rs`, every `pub` becoming `pub(crate)`, minus: `pow_step_ct`, `mod_pow_ct`, `lemma_mul_two`, `lemma_prefix_step` (Task 4 ports these into `rsa.rs`) and the items reused from `mont.rs`. Import with `#[allow(unused_imports)] use crate::mont::*;` (named imports of proof and spec fns break the plain build with E0432). A working port is at `.superpowers/probe-5e-preflight/wt/crates/crypto/src/`; its `mod_pow_ct` and `pow_step_ct` sit in `bignum.rs` and need moving
- Modify: `crates/crypto/src/lib.rs`, `crates/crypto/src/mont.rs` (visibility only), `crates/crypto/src/bytes.rs` (add `lemma_os2ip_tail`), `TRUSTED.md` (compute row only)
- Test: `#[cfg(test)]` mod in `bignum.rs`

**Interfaces:**
- Consumes: mont.rs `mac`, `sbb`, `bv_split128`, `bv_sel`, `lemma_mac_bound`, `lemma_q_zero`, `load_be64`; `bytes::{lemma_os2ip_append, lemma_os2ip_i2osp, lemma_os2ip_bound}`; `sha256::lemma_i2osp_be8`.
- Produces (all `pub(crate)`):
  - `spec wp(i: nat) -> int`, `spec limbs(s: Seq<u64>, n: nat) -> int`; `lemma_wp`, `lemma_limbs_ext`, `lemma_limbs_bound`, `lemma_limbs_low`, `lemma_limbs_zero`, `lemma_wp_256` (`wp(j) == pow(256, 8 * j)`).
  - `fn mont_mul_n(a: &[u64; 64], b: &[u64; 64], m: &[u64; 64], mp: u64, nl: usize) -> (r: [u64; 64])`: `requires 1 <= nl <= 64, (m[0]·mp + 1) % 2^64 == 0, limbs(b@, nl) < limbs(m@, nl)`; `ensures limbs(r@, nl) < limbs(m@, nl), (limbs(r@, nl)·wp(nl)) % M == (limbs(a@, nl)·limbs(b@, nl)) % M`. Label `secret(a, b, m, mp), public(nl)`.
  - `fn ct_mask(b: u64) -> (r: u64)`, `#[inline(never)]`, `ensures r == 0u64.wrapping_sub(b)`, label `secret(b)`. Body `0u64.wrapping_sub(b)`. `select_n` and `cond_sub` take their mask from it and from nothing else. Comment: `// Not inlined: seen as sext(i1) in a limb loop, the mask becomes a loop-unswitched branch on the secret bit in release builds, which the MIR checker cannot see.`
  - `fn select_n(b: u64, x: &[u64; 64], y: &[u64; 64], nl: usize) -> [u64; 64]`, label `secret(b, x, y), public(nl)`; mask from `ct_mask(b)`.
  - `fn neg_inv64(m0: u64) -> (mp: u64)`: `requires m0 % 2 == 1`; `ensures (m0·mp + 1) % 2^64 == 0`. Label `secret(m0)`.
  - `fn pow2_mod(m: &[u64; 64], nl: usize, count: usize) -> (r: [u64; 64])`: `requires limbs(m@, nl) > 1`; `ensures limbs(r@, nl) == pow2(count) % M`. Label `secret(m), public(nl, count)`. Repeated doubling from 1: `t = 0; addmul(t, 1, r, nl)` twice; `cond_sub` (no copy loop).
  - `fn limbs_from_be_n(b: &[u8], nl: usize) -> (r: [u64; 64])` (proved in `glue.rs`), label `secret(b), public(nl)`.
  - `fn limbs_to_be_n(l: &[u64; 64], nl: usize, k: usize) -> (r: Vec<u8>)`: `requires 8 * (nl - 1) < k <= 8 * nl, limbs(l@, nl) < pow(256, k)`; `ensures r@ == i2osp(limbs(l@, nl) as nat, k)`. Label `secret(l), public(nl, k)`. Route mirrors `limbs_from_be_n`: push 8·nl zeros into a `with_capacity` Vec, fill back to front with `set`, invariant `os2ip(out@.subrange(8 * (nl - j), 8 * nl)) == limbs(l@, j)`; `lemma_os2ip_tail` for the low k octets, copied by `slice_subrange`; new `bytes::lemma_i2osp_os2ip(s: Seq<u8>)`: `i2osp(os2ip(s), s.len()) == s`.
  - `fn pad_be(b: &[u8], len: usize) -> (r: Vec<u8>)`: `requires os2ip(b@) < pow(256, len)`; `ensures r@.len() == len, os2ip(r@) == os2ip(b@)`. Label `secret(b), public(len)`. Route: drop the prefix (`lemma_os2ip_tail`) or push zeros (`lemma_os2ip_append`), `extend_from_slice`. Its cost depends only on `b.len()` and `len`.
  - `bytes::lemma_os2ip_tail(s: Seq<u8>, k: nat)`: `requires k <= s.len(), os2ip(s) < pow(256, k)`; `ensures os2ip(s.subrange(s.len() - k, s.len() as int)) == os2ip(s)`.

- [ ] **Step 1: Baseline.** `scripts/ct-check.sh`; save `grep '^checked' target/ct/out/crypto/report-crypto.txt` to `.superpowers/ct-baseline.txt`; report F.
- [ ] **Step 2: Write the failing tests in the test mod.**
  - `neg_inv64_kat`: for 1000 odd `m0` (xorshift from a fixed seed, plus 1, 3, `u64::MAX`): `m0.wrapping_mul(neg_inv64(m0)).wrapping_add(1) == 0`.
  - `mont_mul_one_limb`: `nl = 1`, odd `m: u64`: `(r as u128) << 64) % m == (a * b) % m` for 1000 triples.
  - `pow2_mod_kat`: `nl = 1`: equals `(1u128 << count) % m` for `count <= 127`.
  - `limbs_be_round_trip`: `nl` 32, 33, 64; `k` at `8·nl`, `8·nl − 7`; octets out == octets in.
  - `pad_be_lengths`: shorter, equal, longer-with-zero-prefix.
- [ ] **Step 3: Run to verify they fail** (`mont_mul_n` undefined).
- [ ] **Step 4: Implement,** with `#[allow(dead_code)] // used from Task 4` where needed. CT feedback roots: `mont_mul_n`, `pow2_mod`, `pad_be`, `limbs_to_be_n`. `addmul`, `shift_down`, `mont_row`, `sub_n`, `cond_sub` stay private with the probe's signatures; `cond_sub` takes its mask from `ct_mask`. Prefix exec values used only in ghost code with `_` (`_dn`, `_q`, `_rinv`); put `#[allow(unused_imports)]` on every vstd import.
- [ ] **Step 5: Mutations:** the three in D4 plus `neg_inv64` running 5 steps, and `ct_mask` returning `b` unmasked or `select_n` using `0u64.wrapping_sub(b)` inline instead of `ct_mask` (the second is caught only by Task 6's object read); each must fail on a named obligation, not on rlimit.
- [ ] **Step 6: Four checks, N = 1.** `cargo verus verify` at `--rlimit 4`. `TRUSTED.md` `by (compute_only)` row: add "the 5e `k_at` values (`crypto::bignum`, `neg_inv64`)" to its list and `crates/crypto/src/bignum.rs` to its files. Commit: `feat(crypto): Montgomery multiply over 64-limb arrays`.

---

### Task 3: MGF1 and EMSA-PSS exec

Probed in preflight: 12 fns verify at `--rlimit 4` with no splitting (over `Seq` with `spec_sha256` hidden: `xor_bytes`, `update(0, top)`, `mgf1_blocks`). The mutations failed as named: counter from 1 and PS one longer on assertions, mask shift off by one on the shift bound. The closest precedent is `hkdf_expand`. If a fn exceeds `--rlimit 4`, split at the let-chain step and report it; never raise the limit.

**Files:**
- Modify: `crates/crypto/src/rsa.rs`

**Interfaces:**
- Consumes: `sha256::{sha256, lemma_i2osp_be4, lemma_spec_sha256_len}`.
- Produces:
  - `fn mgf1_exec(seed: &[u8; 32], len: usize) -> (r: Vec<u8>)`: `requires len <= 512`; `ensures r@ == mgf1_sha256(seed@, len as nat)`. Label `secret(seed), public(len)`.
  - `fn emsa_pss_encode_exec(msg: &[u8], em_bits: usize, salt: &[u8]) -> (r: Vec<u8>)`: `requires msg@.len() <= MAX_INPUT_LEN, salt@.len() == 32, 2047 <= em_bits <= 4095`; `ensures r@ == emsa_pss_encode(msg@, em_bits as nat, salt@), r@.len() == (em_bits + 7) / 8`. Label `secret(salt, msg), public(em_bits)` (if its CT feedback is not `ok` with no new declassify, `secret(salt), public(msg, em_bits)` and report why).

- [ ] **Step 1: Write the failing test `emsa_matches_cavp`** in `rsa.rs`'s test mod: for the 10 `[mod = 3072]` SHA-256 vectors, `rsa::hazmat::rsa_encrypt(pub, S)`, left-pad to emLen, == `emsa_pss_encode_exec(Msg, 3071, SaltVal)`. Carry the latest `n`, `e` from the blank-line records while walking. The test mod includes `vecdata` at file level (Task 1 Produces).
- [ ] **Step 1b: Failing test `wycheproof_emsa_2048`:** `wycheproof/rsa_pss_2048_sha256_mgf1_32_test.json`, for each `valid` row (count 63): recover EM with `rsa_encrypt(pub, sig)`, read the salt from EM (unmask DB with `mgf1_exec(H)`), then assert `emsa_pss_encode_exec(msg, 2047, salt) == EM`.
- [ ] **Step 2: Add `emsa_mask_bits`:** with the 2052-bit key and signature from `tests/rsa_pss.rs::pss_rsa2052_masking_kat`, recovered EM == exec output (`em_bits = 2051`). `emsa_len_2049`: `em_bits = 2048`, output length 256. `mgf1_one_block`: `mgf1_exec(&seed, 20) == SHA-256(seed ‖ 00000000)[..20]`; `mgf1_len_zero` is empty.
- [ ] **Step 3: Run to verify they fail.**
- [ ] **Step 4: Implement.** MGF1: 36-octet input Vec, counter from a public loop, loop invariant over `mgf1_blocks` with one-step unfolding, truncate by `slice_subrange`. EMSA mirrors the spec's let-chain order; `hide(spec_sha256)` in the xor and concat proofs. Add `#[allow(dead_code)] // used from Task 5, removed there.` Exec top mask: `masked[0] & (0xffu8 >> ((8 * em_len - em_bits) as u8))`. CT feedback root: `emsa_pss_encode_exec`.
- [ ] **Step 5: Mutations:** counter starts at 1; PS one octet longer; mask shift off by one. Each must fail on a named obligation.
- [ ] **Step 6: Four checks, N = 1.** Commit: `feat(crypto): verified MGF1 and EMSA-PSS encoding`.

---

### Task 4: RSASP1: `m^d mod n` to `k` octets

**Files:**
- Modify: `crates/crypto/src/rsa.rs`

**Interfaces:**
- Consumes: Task 2's Produces (including `ct_mask` through `select_n`); mont.rs `mdec`, `lemma_mdec_mul`, `lemma_pow_step`, `bv_bit_u8`.
- Produces:
  - `fn modulus_bits(n: &[u8]) -> (r: usize)`: `requires bitlen(os2ip(n@)) <= 4096`; `ensures r == bitlen(os2ip(n@))`. Label `ct::public(n)` (from `glue.rs`, with `lemma_bitlen_step`, `lemma_bitlen_bound`, `lemma_pow2_256`). It is the only fn branching on `n`.
  - `fn pow_step_ct` as in `mm.rs` (with `lemma_mul_two`, `lemma_prefix_step`; Task 2 does not port these); `fn mod_pow_ct(x: &[u64; 64], e: &[u8], k: usize, m: &[u64; 64], mp: u64, one: &[u64; 64], nl: usize, Ghost(ri): Ghost<int>) -> (r: [u64; 64])`: as in `mm.rs`, plus `requires e@.len() == k`, and the outer loop is `while j < k`, so an unpadded `d` fails the proof. Label `secret(x, e, m, mp, one), public(k, nl)`.
  - `fn rsasp1(n: &[u8], d: &[u8], em: &[u8], k: usize) -> (r: Vec<u8>)`:
    - `requires 256 <= k <= 512, os2ip(n@) > 1, os2ip(n@) % 2 == 1, os2ip(n@) < pow(256, k), os2ip(d@) < os2ip(n@), os2ip(em@) < pow(256, k)`.
    - `ensures r@ == i2osp((pow(os2ip(em@) as int, os2ip(d@)) % (os2ip(n@) as int)) as nat, k)`.
    - Label `secret(n, d, em), public(k)`.
  - `proof fn lemma_wf_odd(k: RsaKeySpec)`: `requires rsa_key_wf(k)`; `ensures k.n % 2 == 1`.

- Fixed sequence in `rsasp1`: `nl = (k + 7) / 8`; `n_be, d_be, em_be` by `pad_be` (lengths `8·nl`, `k`, `8·nl`); `m = limbs_from_be_n(n_be)`; `mp = neg_inv64(m[0])`; `unit = [1, 0, ..]`; `rinv = mont_mul_n(unit, unit)`, ghost `ri = limbs(rinv)`; `r2 = pow2_mod(m, nl, 128 * nl)`; `one = mont_mul_n(unit, r2)`; `x = mont_mul_n(em_limbs, r2)`; `r = mod_pow_ct(x, d_be, k, m, mp, one, nl, ri)`; `s = mont_mul_n(r, unit)`; `limbs_to_be_n(s, nl, k)`.
- Glue lemmas (atoms only):
  - `lemma_ri`: `(R·ri) % M == 1`.
  - `lemma_to_mont(xv, a, rr, R, ri, M)`: `(xv·R) % M == (a·rr) % M`, `rr == R·R % M`, `(R·ri) % M == 1` gives `mdec(xv) == a % M`.
  - `lemma_from_mont(s, r, R, ri, M)`: `s < M`, `(s·R) % M == r·1 % M` gives `s == mdec(r)`.
  - vstd `lemma_pow_mod_noop` carries `pow(a % M, e) % M == pow(a, e) % M`.

- [ ] **Step 1: Write the failing tests** in `rsa.rs`'s test mod, using `vecdata`:
  - `wycheproof_rsasp1`: for each of the three files, `valid` and `acceptable` rows in `sha == "SHA-256"` groups (the 3 `acceptable` rows are `short signature` at 2048 and 3072 and `signature is close to n`, e = 3; independent KATs for Review Focus item 3): EM = `00 01 FF.. 00 ‖ DigestInfo(SHA-256) ‖ H(msg)` built in the test, k from `keySize`; `rsasp1(modulus, privateExponent, EM, k) == sig`. Count 27. Moduli carry a `00` prefix: pass as is.
  - `rsasp1_small_result`: on the 2048-bit Wycheproof key, s = `0x0102`, m = `rsa_encrypt(pub, s)`: `rsasp1(m)` is k octets, 254 zeros then `01 02`.
  - `rsasp1_edge_messages`: m = 0 gives all zeros; m = 1 gives `00..01`; m = n − 1 gives n − 1 (d is odd for this key).
  - `rsasp1_d_lengths`: d stripped of leading zeros, with 5 zeros prepended, and padded to k: same output.
  - `modulus_bits_edges`: 2048-bit `n`, the same with a `00` prefix and with 600 zero octets prefixed; 2049, 2052, 4096.
  - `lemma_wf_odd` is exercised by Task 5's call.
- [ ] **Step 2: Run to verify they fail.**
- [ ] **Step 3: Implement.** The test mod includes `vecdata` at file level (Task 1 Produces). Add `#[allow(dead_code)] // used from Task 5, removed there.` Port `modulus_bits`, `mod_pow_ct` and `pow_step_ct` from the probes. `// ct: branch on the public modulus` at the one branch. CT feedback root: `rsasp1`. `// ponytail: no CRT or window, 7 ms at 2048 bits, 52 ms at 4096; a 4-bit window saves about 37%, CRT about 75%, at the cost of a general FLT proof`. R² is recomputed per signature: `// ponytail: about 0.3 ms at 2048 bits; cache it in the key if signing ever matters`.
- [ ] **Step 4: Mutations:** swap `select_n`'s arguments; `d` passed to `mod_pow_ct` unpadded (fails `e@.len() == k`); `r2` from `64 * nl` doublings; `lemma_prime_odd` without the `p = 2` case. Each must fail on a named obligation.
- [ ] **Step 5: Add the release timing test** `rsa_speed` (`#[ignore]`, `cargo test --release -p crypto rsa_speed -- --ignored --nocapture`); report ms at 2048, 3072, 4096. Expected within 2x of D2.
- [ ] **Step 6: Four checks, N = 1.** Report the slowest fns; if `rsasp1` passes 60 s, split the setup into a helper returning `(m, mp, one, x)`. Commit: `feat(crypto): verified constant-time RSASP1`.

---

### Task 5: Replace the signer; delete the shim

**Files:**
- Modify: `crates/crypto/src/rsa.rs`, `crates/crypto/src/lib.rs`, `crates/crypto/Cargo.toml`, `crates/crypto/tests/rsa_pss.rs`, `crates/tls/src/sign.rs`, `crates/tls/src/flight.rs` and `crates/tls/src/server.rs` (comments only), `crates/crypto/src/p256.rs` (line 2, same line count), `crates/crypto/tests/p256.rs`, `TRUSTED.md`
- Delete: `crates/crypto/src/shim.rs`
- Test: `crates/crypto/tests/rsa_pss.rs`

**Interfaces:**
- Consumes: `modulus_bits`, `emsa_pss_encode_exec`, `rsasp1`, `lemma_wf_odd`.
- Produces: `pub fn rsa_pss_sha256_sign(key, msg, salt) -> (r: Vec<u8>)` (D3); `pub(crate) fn rsa_pss_sign_inner` (D7) with `requires rsa_key_wf(k), k.n == os2ip(n@), k.d == os2ip(d@), msg@.len() <= MAX_INPUT_LEN, salt@.len() == 32`; `ensures r@ == spec_rsassa_pss_sign(k, msg@, salt@)`.

- [ ] **Step 1: Failing test `pss_4096_verifies`:** the Wycheproof 4096-bit key (`e`, `n`, `d`; p and q recovered by `from_components`); `rsa_pss_sha256_sign` then `rsa::RsaPublicKey::verify(Pss::<Sha256>::new_with_salt(32), ..)`, length 512. Change the test file's `.unwrap()`s to the new return type (compile failure is the red state).
- [ ] **Step 2: Implement the inner and pub fns.** Remove `#[verifier::external_body]` and the doc lines naming the shim (rsa.rs lines 2 and 115; the escape grep matches the bare word). Remove the `#[allow(dead_code)]` lines Tasks 3 and 4 added. Edit the step-2b comment in `spec_rsassa_pss_sign`: drop the shim clause. Spec bodies stay byte-identical. CT feedback root: `rsa_pss_sign_inner`, labelled `ct::secret(d, salt, msg), ct::public(n)`. If ct-check stays `ok` with no new declassify (count 10), keep msg secret; otherwise label `ct::secret(d, salt), ct::public(n, msg)` and report why. Task 6's first gate grep follows the choice. No tls test signs with the dummy `common::rsa()` key (negotiate tests only), so it needs no change.
- [ ] **Step 3: `tls::sign_cv`.** The `Rsa` arm becomes `SigningKey::Rsa(k) => rsa_pss_sha256_sign(k, &content, salt)`. Ensures line 106 becomes `r is Ok <==> spec_cv_signature(key@, th@, salt@) is Some`. The `Err` postcondition stays. Comments only, same line counts:
  - `flight.rs:424` becomes `// sign_cv is exact for both kinds; this iff stays ECDSA-only. ponytail: dropping the guard exceeds --rlimit 4 on build_flight; do it when a caller needs it.` Keep the `key is EcdsaP256 ==>` guard.
  - `server.rs:1504` becomes `// build_flight's Err where the spec has a flight, which its ensures still allows for RSA keys: the spec drain` (next comment line unchanged).
  - `p256.rs:2` becomes `//! spec and verified exec.`
  - `tests/p256.rs:87` becomes `// RustCrypto reference, called directly.`
- [ ] **Step 4: Delete shim.rs and `mod shim;`.** `Cargo.toml`: `sha2` moves to `[dev-dependencies]` (`=0.11.1`, tests/sha256.rs and hmac_hkdf.rs use it); drop the normal `rsa` line; the dev `rsa` line stays. `Cargo.lock` is unchanged (crypto's dev-deps keep `rsa` and `sha2`).
- [ ] **Step 5: `TRUSTED.md`, same commit** (the gate counts the rows):
  - Delete row 58 (`| crypto::rsa::rsa_pss_sha256_sign: …`) and row 59 (`shim.rs`).
  - Delete line 8 (`**Temporary:** …`).
  - Pinned-versions line 22: `RustCrypto (crates/crypto, test-only; `cargo tree -p crypto -e normal` contains none of it): sha2 =0.11.1, rsa =0.10.0-rc.19 with hazmat, p256 =0.14.0, primeorder =0.14.0, hmac =0.13.0, hkdf =0.13.0, aes =0.9.3, aes-gcm =0.11.1`.
  - Row 34 (`ServerConfig::wf`): add `the loader checks every clause of rsa_key_wf before building a key: modulus 2048-4096 bits, n = p q, 3 <= e < n, 0 < d < n, e d = 1 mod p - 1 and mod q - 1, p and q prime (n is then odd). Since 5e nothing checks at signing time: a key outside rsa_key_wf gives a wrong signature rather than an error, possibly computed from a truncated n and d (pad_be and modulus_bits keep the low octets).`
  - Line 21: replace "were already locked by the RustCrypto shim" with "were already locked through RustCrypto".
  - Row 65: replace `sign specs not machine-checked until phase 5` with `checked against CAVP SigGenPSS 3072-bit SHA-256 and Wycheproof RSA PKCS#1 sig-gen keys, and RustCrypto verification, through the verified exec since phase 5e`; replace `the sign shim is partially correct, see its row` with nothing. The claim is `s = m^d mod n`; `s^e == EM` is checked by tests, not proved.
- [ ] **Step 6: Run** `cargo test -p crypto -p tls`. Expected: all pass, including `rsa_verifies` (ring, which already unwraps `sign_cv` and asserts 256 octets) and `rustls_direct_rsa`.
- [ ] **Step 7: Evidence.** `cargo tree -p crypto -e normal` shows no `rsa`, `sha2`, `crypto-bigint`, `digest` or `signature`. `verify.sh` ends `escapes accounted (0)`. Four checks, N = 0. Commit: `feat(crypto): verified RSASSA-PSS signing replaces the RustCrypto shim`.

---

### Task 6: RSA under the CT checker; phase exit

**From the crypto binary audit (.superpowers/archive/crypto-binary-audit.md, in the main checkout):**
- The object read must use what `cargo build --release` ships: the crate's rlib (5 codegen units today). `cargo rustc ... --emit=obj` gives 1 codegen unit and different inlining, so it isn't the shipped code. Read both, and repeat C1's check on the rlib.
- `#[inline(never)]` on `p256::scalar_in_range`, so a rejected key's branch reveals only the declassified bit (the audit's F1, tested: no proof impact). Update TRUSTED.md citations after p256.rs:257.
- The compiler/CPU row gains: "Object code of the 30 non-RSA crypto functions was audited once, 2026-11-02, rustc 1.98.1 x86-64, no masked select became a branch; coverage tiers and what was not checked are in the audit. Not dudect, and inlining varies with codegen units, so this does not carry to other builds." Commit the audit file as docs/crypto-binary-audit.md.

**Files:**
- Modify: `tools/ct-driver/manifest.txt`, `tools/ct-driver/selftest.txt`, `scripts/verify.sh`, `TRUSTED.md`, `docs/requirements.md`, `docs/superpowers/specs/2026-10-27-verified-http3-design.md`

**Interfaces:**
- Consumes: `crypto::rsa::rsa_pss_sign_inner`; `bignum::ct_mask` (the object read).
- Produces: `root crypto::rsa::rsa_pss_sign_inner` in the manifest.

- [ ] **Step 1: Failing gate.** Add to `verify.sh`, after the `fe_from_be` loop:
  ```sh
  grep -q '^checked crypto::rsa::rsa_pss_sign_inner secret=d,msg,salt ret=' "$report" || fail "rsa_pss_sign_inner lost its secret labels"
  grep -q '^checked crypto::rsa::mod_pow_ct secret=[^ ]*\be\b' "$report" || fail "mod_pow_ct's exponent is not secret"
  grep -q '^checked crypto::rsa::modulus_bits secret= ret=' "$report" || fail "modulus_bits has a secret-labelled param"
  if cargo tree -p crypto -e normal --prefix none | grep -qE '^(rsa|sha2|crypto-bigint) '; then fail "RustCrypto in crypto's normal deps"; fi
  ```
  If Task 5 left msg public, the first grep reads `secret=d,salt ret=`. Run `scripts/verify.sh`: expected FAIL on the first grep (the root is not in the manifest). There is no objdump gate in `verify.sh`: Phase 7's binary-level check supersedes it.
- [ ] **Step 2: Add the root** under a `# RSA (5e)` comment. Run `CT_MODE=census` over it; expected no new `intr` key.
- [ ] **Step 3: Selftest vectors:** `crypto::bignum::neg_inv64 0x1u64 => 0xffffffffffffffffu64` and `crypto::rsa::modulus_bits 01ff => 0x9usize` (both pass, selftest 17/17; the interpreter does not read the `requires`); add `01ff` to `modulus_bits_edges`. Each line cites its test, per the file's header. Add both tests to the Rust suites if not already there. Do not add a modexp vector: the interpreter would take about 10^9 steps.
- [ ] **Step 4: Run** `scripts/ct-check.sh`. Expected: `ct-check: crypto ok (F fns, 11 roots, 10 declassify)`, `ct-check: cost 19/36 bounded`, negative control rejected. `diff` `checked` lines against `.superpowers/ct-baseline.txt`: additions only.
- [ ] **Step 5: CT mutations, each must reject:** `select_n` written as `if b == 1`: `SecretSwitch`. `mod_pow_ct` with `if bit == 1 { multiply }`: `SecretSwitch`. The checker cannot see a loop running on `d.len()` (lengths are public); Task 4's `requires e@.len() == k` covers that.
- [ ] **Step 6: `TRUSTED.md`:**
  - The "CT check scope" row (line 38 after Task 5 removed line 8): delete ` and `crypto::rsa` (its row below)`, and replace its "are not CT-checked" with "is not CT-checked" (the subject is now singular).
  - New row after the P-256 timing row: `| Timing of RSASSA-PSS signing (`crypto::bignum`, `crypto::rsa`): MIR-level constant time proved by `ctcore::ni::theorem_ct` for the root `rsa_pss_sign_inner` under `ct::secret(d, salt, msg)`, `ct::public(n)` (if Task 5 left msg public: `ct::secret(d, salt)`, `ct::public(n, msg)`, and say msg is known to the client), with no declassify. `n` is declared public, a reviewed input. Exactly 8k exponent bits run, with k from n, whatever `d`'s encoded length; `pad_be`'s copy depends on `d`'s encoded length, public under spec D7. `rsa_pss_sha256_sign` only projects `key`'s fields and is not analysed; `e`, `p` and `q` are not read by exec code. RUSTSEC-2023-0071 no longer applies to shipped code (RustCrypto `rsa` is test-only). RSA certificates are not deployable from this phase: MIR-level constant time is proved, and the object code was read once, on pinned rustc 1.98.1 x86-64, no dudect or timing measurement at binary level. LLVM did turn `select_n` and `cond_sub`'s masked select into branches on d's bits and on the final subtraction until `ct_mask` was added. Deployment waits for Phase 7's binary-level check and for the shell's loader, which must establish `rsa_key_wf` (the `ServerConfig::wf` row). There is no exponent or message blinding, so any binary-level leak faces the same d on every signature. Modulo the CT front-end, manifest, semantics/leakage and compiler/CPU rows | `crates/crypto/src/bignum.rs`, `crates/crypto/src/rsa.rs` | the CT checker's trust boundary | never (MIR level checked; binary level unverified) |`.
- [ ] **Step 7: Docs.** `docs/requirements.md` row 9.1 (req): replace `bignum modexp, CRT, MGF1, EMSA-PSS` with `bignum modexp without CRT, MGF1, EMSA-PSS, verified and CT-checked (5e)`. Design spec line 116: `(bignum modexp, MGF1, EMSA-PSS encoding; no CRT, see the 5e plan)`. Do not touch `.worktrees/wt-3d2`.
- [ ] **Step 8: Binary evidence.** `cargo rustc --release -p crypto --lib -- --emit=obj` with a fresh absolute target dir, then `objdump -dr --no-show-raw-insn -C` on the object. In `rsa_pss_sha256_sign` and `cond_sub`: `ct_mask` is called (a relocation in the object), and no conditional jump follows a test of the exponent byte or the mask. Paste the exponent-bit and mask regions into the report. Without `ct_mask` this shows `test $0x80,%al; je`. Scope: a barrier on pinned rustc 1.98.1, x86-64, one build configuration; not a dudect result. If the toolchain pin changes, repeat this step. `rm -rf` the target dir.
- [ ] **Step 9: Final evidence.** Fresh target dir: `CARGO_TARGET_DIR=<fresh absolute> scripts/verify.sh` prints exactly `verify.sh: all crates verified, duvet ok, ct ok (10 declassify), cost 19/36, escapes accounted (0)`. `cargo test` at the workspace root: 0 warnings; report the count. `grep -rn shim crates/ TRUSTED.md` prints nothing. `rm -rf` the target dir. Commit: `feat(crypto): RSA under the constant-time checker; Phase 5 exit`.
