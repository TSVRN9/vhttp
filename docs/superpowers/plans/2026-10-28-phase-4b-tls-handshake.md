# Phase 4b: TLS 1.3 Key Schedule, Negotiation, Signing and the Server Handshake — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A verified, sans-IO `ServerHandshake` for a TLS 1.3 QUIC server.
- **Inputs:** handshake bytes per encryption level, and `TLS_RAND_LEN` random bytes per call.
- **Outputs:**
  - handshake bytes per level;
  - traffic secrets per level;
  - the peer's transport-parameter bytes;
  - a completion event, or a QUIC error code.
- Every transition is a literal transcription of RFC 8446's server path (Appendix A.2, restricted to ours: no PSK, no 0-RTT, no client authentication).
- The key schedule is proven against an RFC 8446 §7.1 transcription over 3a's HKDF, HMAC and SHA-256 specs.

**Architecture:**
- **`crates/tls` gains `crypto = { path = "../crypto" }`** (outline, shared decisions). `quic` is still not a dependency. Transport parameters cross the core as opaque bytes.
- **Seven new modules, one responsibility each:**
  - `hkdf_label`: §7.1 HKDF-Expand-Label and Derive-Secret. 4c reuses it for the `quic *` labels;
  - `schedule`: the §4.4.1 transcript `message_hash`, and the §7.1 secrets, `finished_key` and `verify_data`;
  - `config`: `ServerConfig`, `CertChain`, `SigningKey`, `wf()`, and the checked constructor `build_config`;
  - `negotiate`: the pure choice of suite, ALPN, chain/scheme and group;
  - `sign`: the §4.4.3 CertificateVerify content and signature;
  - `flight`: `Level`, `TlsEvent`, and the spec-exact server flight;
  - `server`: `ServerHandshake`, a per-message `spec_step` drained per level.
- **The state machine is specified as a spec function** (`spec_on_crypto`, built from `spec_step`). The exec code is proven equal to it. RSA signing is the one exception: its shim is one-directional, so the exec code may fail with internal_error where the spec succeeds.
- **Results are `Result<_, u64>` carrying QUIC error codes,** as in 4a. A TLS alert *a* is `0x100 + a` (RFC 9001 §4.8).

**Tech Stack:**
- Verus 0.2026.10.04.426d8b0, vstd `=0.0.0-2026-10-04-0306`, duvet 0.4.3.
- `crypto` (3a, on `main`).
- Test only: `rustls =0.23.45` (features `ring`, `std`) and `ring =0.17.14`.

**Spec:** `docs/superpowers/specs/2026-10-27-verified-http3-design.md`. See:
- Phase 4: "TLS 1.3 server state machine: ClientHello → [HRR] → ServerHello/EE/Cert/CertVerify/Finished", "Key schedule as spec", and "ALPN `h3`, with the `no_application_protocol` alert when nothing matches";
- "Calls I made": P-256 for ECDHE and ECDSA; TLS_AES_128_GCM_SHA256 only; RSA signing with rsa_pss_rsae_sha256 only, no RSA verification; RFC 6979 deterministic ECDSA; sans-IO;
- Non-goals: 0-RTT, PSK/resumption, client certificates, proven constant time ("constant-time *style*");
- the anti-goal: no "proven" claim for anything that isn't.

Also read:
- the outline, `2026-10-28-phase-4-outlines.md`: §4b, the MUST table, the controller rulings and the I2 note;
- the 4a plan, `2026-10-28-phase-4a-tls-codecs.md`: its Global Constraints and its "Binding notes for later sub-phases";
- `<scratch>/rev-4a-final/final-review.md`, items M1 (serializer obligations) and M7 (HsReader bound);
- the 3d plan's TLS boundary (`crypto_read`, `crypto_write`, `on_peer_params`, `on_handshake_complete`, `on_tls_alert`) and its ruling #16 (A.2 iscid mismatch);
- RFC 8446 §2, §4–§4.4.4, §4.6.3, §7.1, §7.4.2, §7.5, §9.1, Appendices A, C and E;
- RFC 9001 §4.8, §6 and §8.1;
- RFC 8448 §3 and §5 (`<scratch>/rfc4/rfc8448.txt`).

## Global Constraints

- **4a's Global Constraints apply unchanged except where this list says otherwise.** That covers:
  - the pins;
  - Duvet citation form, including `#appendix-C.5` / `#appendix-E.5` style anchors (names from `.duvet/requirements/www.rfc-editor.org/rfc/rfc8446/`);
  - sans-IO, with no async, trait objects or closures in exec code (tests may use them);
  - no panics;
  - glob imports of spec items;
  - `Spec*` twins with a `View`/`DeepView` for every type with `Vec`/array fields;
  - `final(x)@` in `&mut` ensures, as 4a writes them;
  - the naming (`rfc_*`, `spec_*`, `theorem_*`, `lemma_*`, `Spec<Type>`);
  - zero escape tokens in `crates/tls`, and `scripts/verify.sh` unedited.

  The escape gate greps `crates/**/*.rs`, test files included. So no `admit(`, `assume(`, `external_body` or the word `axiom` may appear anywhere in `crates/tls`, comments included.
- **The four checks, every task:**
  - `scripts/verify.sh` reports 0 errors and prints its summary line;
  - `cargo build && cargo test` pass with 0 warnings. Add `--offline` if the registry can't be reached; every crate is cached;
  - the escape grep prints nothing under `crates/tls`;
  - `duvet report` exits 0.
- **Fresh evidence:** `(cd crates/tls && CARGO_TARGET_DIR=<scratch>/vt-4b-tN cargo verus verify)` prints `verification results:: … 0 errors`. **Delete `<scratch>/vt-4b-tN` afterwards.** The same applies to any other fresh target directory you create.
- **Base branch:** `phase-4b` branches from `main` after `phase-4a` merges, including its final-review fix wave.
  - From that wave, 4b uses `server_msgs::cert_chain_fits(chain: &Vec<Vec<u8>>) -> (r: bool)` (ensures `r == cert_chain_ok(chain.deep_view())`).
  - It also uses `client_hello::lemma_client_hello_ok(body)`: from `rfc_client_hello(body) == Ok(s)`, it gives `s.legacy_session_id.len() == 0`, `s.versions.contains(TLS13)`, `s.random.len() == 32`, and every key share's `key_exchange.len()` in `1..=0xffff`.
  - If either name differs once merged, use the merged name and record it in the task report.
- **`crates/tls/Cargo.toml` changes:**
  - Task 1 adds `crypto = { path = "../crypto" }` under `[dependencies]`;
  - Task 4 adds `[dev-dependencies] ring = "=0.17.14"`;
  - Task 7 adds `rustls = { version = "=0.23.45", default-features = false, features = ["ring", "std"] }`. The default features pull in aws-lc-rs.

  Checked 2026-10-28 with a throwaway crate (`cargo tree --offline -e normal,dev`). It resolves offline to ring 0.17.14, rustls-webpki 0.103.15, rustls-pki-types 1.15.1, untrusted 0.9.0, getrandom 0.2.17, subtle 2.6.1, zeroize 1.9.1 and once_cell 1.21.4. No other dependency is added.
- **Every 4a serializer `requires` is discharged explicitly** (final review M1). Each task names where:

  | Serializer | Precondition | Discharged by |
  |---|---|---|
  | `serialize_server_hello` | `session_id_echo ≤ 32` | `lemma_client_hello_ok` (the echo is empty) |
  | | `1 ≤ kx ≤ 256` | the `[u8; 65]` from `p256_public_key` |
  | | `!spec_reserved_group(0x0017)` | `by (compute)` |
  | `serialize_hello_retry_request` | `!spec_reserved_group(0x0017)` | `by (compute)` |
  | | `session_id_echo ≤ 32` | `lemma_client_hello_ok` |
  | `serialize_encrypted_extensions` | `tp ≤ 1024` | `requires local_tp@.len() <= 1024` on `ServerHandshake::new`, pushed to 4c (Decision 1) |
  | `serialize_certificate` | `cert_chain_ok` | `ServerConfig::wf()`, established only through `build_config`, which runs `cert_chain_fits` (Task 3) |
  | `serialize_certificate_verify` | `!spec_reserved_scheme(0x0403 / 0x0804)` | `by (compute)` |
  | | `sig ≤ 0xffff` | the runtime check in `sign_cv`, for both RSA and ECDSA (Task 4) |
  | `crypto::*` | `MAX_INPUT_LEN` on every hash/HMAC/sign input | the transcript bound in `ServerHandshake::wf()` (Task 6) |
- **HsReader bound** (final review M7, a binding on Task 6). The outline's "MAX_CRYPTO_BUFFER" mechanism is wrong. Instead:
  - `on_crypto` calls `next_message` after every `push`, and fails on `Err`;
  - bytes at a level with no expected message fail with unexpected_message *before* `push`.

  So the reader at the expected level holds less than `4 + MAX_HS_BODY` bytes after every call. A reader at a level the handshake has left holds at most the leftover of one chunk, and never grows.
- **New codepoints in `tls::codes`** (Task 1), each a `pub const` with its RFC name in a comment:
  - `HT_MESSAGE_HASH: u8 = 254` (§4.4.1);
  - `SECP256R1: u16 = 0x0017`;
  - `ECDSA_SECP256R1_SHA256: u16 = 0x0403`, `RSA_PSS_RSAE_SHA256: u16 = 0x0804`, `RSA_PKCS1_SHA1: u16 = 0x0201` and `ECDSA_SHA1: u16 = 0x0203` (§4.2.3);
  - `ALERT_HANDSHAKE_FAILURE 0x128` (40), `ALERT_DECRYPT_ERROR 0x133` (51), `ALERT_INTERNAL_ERROR 0x150` (80) and `ALERT_NO_APPLICATION_PROTOCOL 0x178` (120);
  - `TLS_RAND_LEN: usize = 96`. Bytes `[0..32]` are the ServerHello random, `[32..64]` the ECDHE scalar, and `[64..96]` the PSS salt;
  - `LABEL_PREFIX: [u8; 6] = *b"tls13 "`;
  - the labels `LABEL_DERIVED *b"derived"`, `LABEL_C_HS *b"c hs traffic"`, `LABEL_S_HS *b"s hs traffic"`, `LABEL_C_AP *b"c ap traffic"`, `LABEL_S_AP *b"s ap traffic"` and `LABEL_FINISHED *b"finished"`;
  - `CV_SERVER_CONTEXT: [u8; 33] = *b"TLS 1.3, server CertificateVerify"`.

  Specs use them as `LABEL_DERIVED@` etc., as 4a uses `H3_ALPN@`.
- **Shared test data,** added to `crates/tls/tests/common/mod.rs` by script, never by hand. Use `<scratch>/chk4/v8448.py`'s `blocks()`, and check each sha256 prefix in the same `python3 -I` step:

  | Name | Bytes | sha256 prefix | Source |
  |---|---|---|---|
  | `R3_EE` | 40 | `00c6db4f891797dd` | RFC 8448 §3 EncryptedExtensions |
  | `R3_CV` | 136 | `97995117fd06d2b3` | RFC 8448 §3 CertificateVerify |
  | `R3_SFIN` | 36 | `5310ae922151ea96` | RFC 8448 §3 server Finished |
  | `R3_CFIN` | 36 | `4e33a5b229519eb6` | RFC 8448 §3 client Finished |
  | `R5_HRR` | 176 | `5e4fd6086b7d68e5` | RFC 8448 §5 HelloRetryRequest (with cookie) |
  | `R5_EE` | 28 | `7a64098d06203436` | RFC 8448 §5 EncryptedExtensions |
  | `R5_CFIN` | 36 | `1b417119894d67fe` | RFC 8448 §5 client Finished |

  - RFC 8448 §3's Certificate is byte-identical to 4a's `R5_CERT` (`bf4c94104efe86a6`), so reuse it.
  - Task 4 adds the key fixtures (`ECDSA_D`, `RSA_N/E/D/P/Q`, the two certificate DER files).
  - `vectors_intact` asserts the lengths.
- **What RFC 8448 can and cannot pin** (so no task attempts the impossible):
  - **Can:** schedule-level values over the raw RFC transcripts, for both §3 and §5. That covers the early, handshake and master secrets, all four traffic secrets, both finished keys, and both Finished bodies. All of them were recomputed in Python on 2026-10-28 and match the RFC.
  - **Can, through the flight builder:** RFC 8448 §5's ServerHello byte for byte, and its handshake traffic secrets. Set `rand[0..32]` to R5's random and `rand[32..64]` to `8c510601f9765bfb8ed693449a48989859b5cfa879cb9f5443c41c5ff10634ed`, with the raw §5 transcript.
  - **Cannot:**
    - **RFC 8448's EE, CV or Finished bytes.** Our EE (ALPN + QTP) differs from §5's, so everything after the SH diverges. The PSS salt is unknown, and the RFC 8448 RSA key is 1024-bit, which fails `rsa_key_wf`'s 2048 floor.
    - **Feeding R5_CH2 to the state machine.** It carries a cookie, so 4a rejects it with 0x12f.
- **Matrix bookkeeping:** `✅ 4b: <file>` on each closed row, with a short note. Touched rows get `4b: <what> (closed in 4c)`.

## Matrix rows this plan closes (28)

Labels are exactly as in `docs/requirements.md`. Ownership is from `<scratch>/chk4/rows4.py` (bucket `b4`).
- **Task 2:** RFC 8446 §7.5.
- **Task 3:**
  - RFC 8446 §2.1, §4.1.1, §4.2.3, §4.2.8, §4.4.2.2, §9.1;
  - RFC 8446 §4.2.3 (req) "RSA signature scheme requirements …" and §4.2.3 (req) "Deprecated algorithms MUST NOT be offered or negotiated …";
  - RFC 9001 §8.1.
- **Task 4:** RFC 8446 §4.4.3, and §4.4.3 (req) "RSA signatures MUST use an RSASSA-PSS algorithm".
- **Task 5:** RFC 8446 §2, §4.1.3, §4.3.1, §4.4.2, §7.4.2, Appendix C.
- **Task 6:**
  - RFC 8446 §4, §4.1.2, §4.1.4, §4.2, §4.4.4, §4.6.3, Appendix E;
  - RFC 8446 §4.6.3 (req) "Implementations that receive a KeyUpdate message …";
  - RFC 9001 §6;
  - RFC 9114 §7.2.4.2 (req) "Server MUST NOT accept 0-RTT if settings compatibility unknown".

1 + 9 + 2 + 6 + 10 = 28.

**Rows touched but not closed.** Each gets the note `4b: <what> (closed in 4c)`:

| Row | Task | 4b provides |
|---|---|---|
| RFC 8446 §6 | 6 | `0x100 + alert` codes; secrets and transcript zeroed on `Failed` |
| RFC 8446 §5.1 (req) | 6 | `pending(level)` |
| RFC 9001 §4.1.3 | 6 | `pending(level)` for the "data TLS has not consumed" rule |
| RFC 9001 §4.8 | 6 | every TLS failure is `CRYPTO_ERROR_BASE + AlertDescription` |
| RFC 9001 §4.1.2 | 6 | `TlsEvent::Complete` / `is_complete()` |

## Review Focus

1. **curl's real first fetch: a two-datagram ClientHello whose shares are X25519MLKEM768 and X25519 only.** The server must answer it with exactly one 56-byte HRR selecting 0x0017. It must emit nothing after the first 1200 bytes, and no PeerParams or secrets before CH2. Pinned in Task 6: `curl_ch_hrr`.
2. **A CH2 that differs from CH1 beyond its key share.** Examples: it drops 0x1301, changes ALPN or random, carries two secp256r1 shares, or still offers only X25519. Each must be illegal_parameter, with no ServerHello and no second HRR. Pinned in Task 6: `ch2_rules`.
3. **A client Finished coalesced with trailing bytes, or a post-handshake message.**
   - Trailing bytes in the same chunk give `Ok` with `Complete` and `pending(Handshake)` true, so 4c raises PROTOCOL_VIOLATION.
   - The same bytes in a later call give 0x10a.
   - KeyUpdate at OneRtt is 0x10a.

   Pinned in Task 6: `finished_coalesced`, `key_update`.
4. **A hostile P-256 share.** Off-curve, compressed (33 bytes), or 0x04 ‖ zeros: each must be illegal_parameter, with no flight and no secrets emitted. Pinned in Task 5: `bad_peer_share`.
5. **A doomed CH1 must fail before any HRR.** The cases are an RSA-only config with a client listing only 0x0403, ALPN `h3-29` only, and AES-256-only suites. Each must fail on CH1 (0x128 / 0x178 / 0x128), even though its X25519-only shares would otherwise trigger an HRR. Pinned in Task 6 (`doomed_ch1`) and Task 7 (`rustls_doomed`).

---

### Task 1: HKDF-Expand-Label and Derive-Secret (`tls::hkdf_label`) — suggested model: sonnet

**Files:**
- Create: `crates/tls/src/hkdf_label.rs`, `crates/tls/tests/hkdf_label.rs`
- Modify:
  - `crates/tls/Cargo.toml` (`crypto` dependency);
  - `crates/tls/src/lib.rs` (`pub mod hkdf_label;`; later tasks append);
  - `crates/tls/src/codes.rs` (every constant in Global Constraints);
  - `Cargo.lock`.

**Interfaces:**
- Consumes:
  - `spec_be_bytes`, `spec_vec_bytes`, `put_u16`, `put_vec` (4a `pl`);
  - `crypto::hkdf::{spec_hkdf_expand, hkdf_expand, lemma_spec_hkdf_expand_len}`;
  - `crypto::sha256::spec_sha256`.
- Produces (`tls::hkdf_label`), transcribing RFC 8446 §7.1:
  - **`pub open spec fn spec_hkdf_label(label: Seq<u8>, context: Seq<u8>, len: nat) -> Seq<u8>`** = `spec_be_bytes(len, 2) + spec_vec_bytes(255, LABEL_PREFIX@ + label) + spec_vec_bytes(255, context)`. That is the `HkdfLabel` struct: `uint16 length`, `opaque label<7..255> = "tls13 " + Label`, `opaque context<0..255>`.
  - **`pub open spec fn spec_hkdf_expand_label(secret: Seq<u8>, label: Seq<u8>, context: Seq<u8>, len: nat) -> Seq<u8>`** = `spec_hkdf_expand(secret, spec_hkdf_label(label, context, len), len)`.
  - **`pub open spec fn spec_derive_secret(secret: Seq<u8>, label: Seq<u8>, messages: Seq<u8>) -> Seq<u8>`** = `spec_hkdf_expand_label(secret, label, spec_sha256(messages), 32)`.
    - `messages` is the §4.4.1 transcript as a byte string. After an HRR, the caller passes the substituted transcript (Task 2's `spec_message_hash`).
  - **`pub open spec fn label_ok(label: Seq<u8>) -> bool`** = `1 <= label.len() <= 249`. That is the `<7..255>` bound after the 6-byte prefix.
  - **Exec:**
    - **`pub fn hkdf_label(label: &[u8], context: &[u8], len: u16) -> (r: Vec<u8>)`**:
      - requires `label_ok(label@)` and `context@.len() <= 255`;
      - ensures `r@ == spec_hkdf_label(label@, context@, len as nat)`.
    - **`pub fn hkdf_expand_label(secret: &[u8; 32], label: &[u8], context: &[u8], len: usize) -> (r: Vec<u8>)`**:
      - requires `label_ok(label@)`, `context@.len() <= 255` and `len <= 8160`;
      - ensures `r@ == spec_hkdf_expand_label(secret@, label@, context@, len as nat)` and `r@.len() == len`, via `lemma_spec_hkdf_expand_len`.
      - 4c calls it for "quic key" (16), "quic iv" (12), "quic hp" (16) and "quic ku" (32).
    - **`pub fn derive_secret(secret: &[u8; 32], label: &[u8], transcript_hash: &[u8; 32]) -> (r: [u8; 32])`**:
      - requires `label_ok(label@)`;
      - ensures `r@ == spec_hkdf_expand_label(secret@, label@, transcript_hash@, 32)`.
      - Callers that know `transcript_hash@ == spec_sha256(t)` then get `r@ == spec_derive_secret(secret@, label@, t)` by unfolding.

- [ ] **Step 1: Failing tests** (`tests/hkdf_label.rs`). Every hex value comes from RFC 8448's printed `info`/`expanded` lines (script-checked 2026-10-28).
  - **`labels_rfc8448`:**
    - `hkdf_label(b"key", &[], 16)` == `001009746c733133206b657900`;
    - `hkdf_label(b"iv", &[], 12)` == `000c08746c73313320697600`;
    - `hkdf_label(b"finished", &[], 32)` == `00200e746c7331332066696e697368656400`;
    - `hkdf_label(b"derived", &sha256(b""), 32)` == `00200d746c733133206465726976656420e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (49 bytes);
    - `hkdf_label(b"c hs traffic", &hex("8aa8e828ec2f8a884fec95a3139de01c15a3daa7ff5bfc3f4bfcc21b438d7bf8"), 32)` == `002012746c73313320632068732074726166666963208aa8e828ec2f8a884fec95a3139de01c15a3daa7ff5bfc3f4bfcc21b438d7bf8` (54 bytes);
    - `hkdf_label(b"quic key", &[], 16)` == `00100e746c7331332071756963206b657900`. This is the 4c label.
  - **`expand_label_rfc8448_s5`:**
    - with the server handshake secret `3403e781e2af7b6508da28574f6e95a1abf162de83a97927c37672a4a0cef8a1`: `"key"`, 16 → `4646bfac1712c426cd78d8a24a8a6f6b`, and `"iv"`, 12 → `c7d395c08d62f297d13768ea`;
    - with the client handshake secret `158aa7ab8855073582b41d674b4055cabcc534728f659314861b4e08e2011566`: `"key"` → `2f1f918663d590e7421149a29d94b0b6`, and `"iv"` → `414d5485235e1a688793bd74`.
  - **`derive_secret_derived`:** `derive_secret(&hex("33ad0a1c607ec03b09e6cd9893680ce210adf300aa1f2660e1b22e10f170f92a"), b"derived", &sha256(b""))` == `6f2615a108c702c5678f54fc9dbab69716c076189c48250cebeac3576c3611ba`.
  - **`new_alert_sums`:** `ALERT_HANDSHAKE_FAILURE`, `ALERT_DECRYPT_ERROR`, `ALERT_INTERNAL_ERROR` and `ALERT_NO_APPLICATION_PROTOCOL` equal `CRYPTO_ERROR_BASE` + {40, 51, 80, 120}.
- [ ] **Step 2:** Run `cargo test -p tls --test hkdf_label` and confirm it fails to compile.
- [ ] **Step 3: Implement.**
  - Build the label with `put_u16`, then `put_vec(255, prefix ‖ label)`, then `put_vec(255, context)`. The proof is the composition of their ensures.
  - Copy `Vec` → `[u8; 32]` with an index loop, using `lemma_spec_hkdf_expand_len` for the length.
  - RFC 8446 §7.1 has only a SHOULD in `.duvet/requirements`. Plain-comment-cite the `HkdfLabel` struct and the Derive-Secret definition, as 4a does for §3.
- [ ] **Step 4:** Run the four checks and the fresh verify, then delete the target directory.
- [ ] **Step 5: Commit:** `feat(tls): verified HKDF-Expand-Label and Derive-Secret (RFC 8446 §7.1); crypto dependency`
- [ ] **Step 6:** No matrix commit.

---

### Task 2: Transcript `message_hash` and the key schedule (`tls::schedule`) — suggested model: opus

**Files:**
- Create: `crates/tls/src/schedule.rs`, `crates/tls/tests/schedule.rs`
- Modify: `crates/tls/src/lib.rs`, `crates/tls/tests/common/mod.rs` (the seven vectors in Global Constraints), `docs/requirements.md`

**Interfaces:**
- Consumes:
  - Task 1's `spec_hkdf_expand_label`, `spec_derive_secret`, `derive_secret`, `hkdf_expand_label`;
  - `crypto::hkdf::{spec_hkdf_extract, hkdf_extract}`;
  - `crypto::hmac::{spec_hmac_sha256, hmac_sha256}`;
  - `crypto::sha256::{spec_sha256, sha256, lemma_spec_sha256_len}`;
  - `HT_MESSAGE_HASH`, `LABEL_*`.
- Produces (`tls::schedule`):
  - **`pub open spec fn zeros32() -> Seq<u8>`** = `Seq::new(32, |_i| 0u8)`. This is §7.1's "0-value consisting of a string of Hash.length bytes set to zeros", used for the absent PSK and as the master secret's IKM.
  - **`pub open spec fn spec_message_hash(ch1: Seq<u8>) -> Seq<u8>`** = `seq![HT_MESSAGE_HASH, 0, 0, 32] + spec_sha256(ch1)`. That is §4.4.1: "message_hash || 00 00 Hash.length || Hash(ClientHello1)". Here `ch1` is the full CH1 message, header included.
  - **The §7.1 diagram, PSK absent:**
    - `spec_early_secret() = spec_hkdf_extract(zeros32(), zeros32())`;
    - `spec_handshake_secret(ecdhe) = spec_hkdf_extract(spec_derive_secret(spec_early_secret(), LABEL_DERIVED@, seq![]), ecdhe)`;
    - `spec_master_secret(hs) = spec_hkdf_extract(spec_derive_secret(hs, LABEL_DERIVED@, seq![]), zeros32())`.
  - **§4.4.4:**
    - `spec_finished_key(base) = spec_hkdf_expand_label(base, LABEL_FINISHED@, seq![], 32)`;
    - `spec_verify_data(base, messages) = spec_hmac_sha256(spec_finished_key(base), spec_sha256(messages))`.
  - **Exec:**
    - **`pub fn message_hash(ch1: &[u8]) -> (r: Vec<u8>)`**:
      - requires `ch1@.len() <= MAX_INPUT_LEN`;
      - ensures `r@ == spec_message_hash(ch1@)` and `r@.len() == 36`.
    - **`pub struct HsSecrets { pub hs: [u8; 32], pub client: [u8; 32], pub server: [u8; 32] }`**.
    - **`pub fn handshake_secrets(ecdhe: &[u8; 32], th: &[u8; 32]) -> (r: HsSecrets)`** ensures:
      - `r.hs@ == spec_handshake_secret(ecdhe@)`;
      - `r.client@ == spec_hkdf_expand_label(r.hs@, LABEL_C_HS@, th@, 32)`;
      - `r.server@` the same with `LABEL_S_HS`.

      Here `th` is `Transcript-Hash(ClientHello…ServerHello)`.
    - **`pub fn master_secret(hs: &[u8; 32]) -> (r: [u8; 32])`** ensures `r@ == spec_master_secret(hs@)`.
    - **`pub fn app_secrets(master: &[u8; 32], th: &[u8; 32]) -> (r: ([u8; 32], [u8; 32]))`** ensures `r.0@`/`r.1@` == `spec_hkdf_expand_label(master@, LABEL_C_AP@ / LABEL_S_AP@, th@, 32)`. Here `th` is `Transcript-Hash(ClientHello…server Finished)`.
    - **`pub fn finished_key(base: &[u8; 32]) -> (r: [u8; 32])`** and **`pub fn verify_data(base: &[u8; 32], th: &[u8; 32]) -> (r: [u8; 32])`**, the latter ensuring `r@ == spec_hmac_sha256(spec_finished_key(base@), th@)`.
  - **No exporter or resumption secret is derived** (§7.5: QUIC uses no exporter, and resumption is declined).

- [ ] **Step 1: Failing tests** (`tests/schedule.rs`). `H(x)` = `crypto::sha256::sha256(&x)`.
  - **`rfc8448_s3`.** Use IKM `8bd4054fb55b9d63fdfbacf9f04b9f0d35e6d63f537563efd46272900f89492d`, which is RFC 8448's printed X25519 shared secret, taken as an input because we have no X25519.
    - `H(R3_CH‖R3_SH)` == `860c06edc07858ee8e78f0e7428c58edd6b43f2ca3e6e95f02ed063cf0e1cad8`.
    - `handshake_secrets(ikm, that)`:
      - `.hs` == `1dc826e93606aa6fdc0aadc12f741b01046aa6b99f691ed221a9f0ca043fbeac`;
      - `.client` == `b3eddb126e067f35a780b3abf45e2d8f3b1a950738f52e9600746a0e27a55a21`;
      - `.server` == `b67b7d690cc16c4e75e54213cb2d37b4e9c912bcded9105d42befd59d391ad38`.
    - `master_secret(hs)` == `18df06843d13a08bf2a449844c5f8a478001bc4d4c627984d5a41da8d0402919`.
    - `finished_key(server)` == `008d3b66f816ea559f96b537e885c31fc068bf492c652f01f288a1d8cdc19fc8`, and `finished_key(client)` == `b80ad01015fb2f0bd65ff7d4da5d6bf83f84821d1f87fdc7d3c75b5a7b42d9c4`.
    - `verify_data(server, H(CH‖SH‖EE‖R5_CERT‖CV))` == `R3_SFIN[4..]`.
    - With `th = H(…‖R3_SFIN)` == `9608102a0f1ccc6db6250b7b7e417b1a000eaada3daae4777a7686c9ff83df13`:
      - `app_secrets(master, th)` == (`9e40646ce79a7f9dc05af8889bce6552875afa0b06df0087f792ebb7c17504a5`, `a11af9f05531f856ad47116b45a950328204b4f44bfb6b3a4b4f1f3fcb631643`);
      - `verify_data(client, th)` == `R3_CFIN[4..]`.
  - **`rfc8448_s5_hrr`:**
    - `p256_public_key(&hex("8c510601f9765bfb8ed693449a48989859b5cfa879cb9f5443c41c5ff10634ed"))` == `R5_SH[52..117]`.
    - `z = p256_ecdh(that scalar, CH2's P-256 share)` == `c142ce13ca11b5c2233652e63ad3d97844f1621fbfb9de69d547dc8fedeabeb4`. CH2's share is the `0x33` entry's key_exchange from `split_ch(R5_CH2)`.
    - `message_hash(R5_CH1)` == `fe000020` ‖ `de7420cc7426d2f6b221edcc9c4bdc9bb0ab048b3ddd2411da7e3a01baea6c7e`.
    - With `t = message_hash(R5_CH1) ‖ R5_HRR ‖ R5_CH2 ‖ R5_SH`, `H(t)` == `8aa8e828ec2f8a884fec95a3139de01c15a3daa7ff5bfc3f4bfcc21b438d7bf8`. This pins the HRR transcript.
    - `handshake_secrets(z, H(t))`:
      - `.hs` == `ce022e5e6e81e50736d773f2d3adfce8220d049bf510f0dbfac927ef4243b148`;
      - `.client` == `158aa7ab8855073582b41d674b4055cabcc534728f659314861b4e08e2011566`;
      - `.server` == `3403e781e2af7b6508da28574f6e95a1abf162de83a97927c37672a4a0cef8a1`.
    - `master_secret` == `1131545d0baf79ddce9b87f06945781a57dd18ef378dcd2060f8f9a569027ed8`.
    - Finished keys: `e7f8bb3ea4b6c30c4710b3d09c3313658117e70b097e850368e2510ca5631f74` (server) and `81be4131fbb9b6f4471450846f74fd1e68c5224ba7c2a8677f5c53ad226fdc13` (client).
    - `verify_data(server, H(t‖R5_EE‖R5_CERT‖R5_CV))` == `R5_SFIN[4..]`.
    - With `th = H(…‖R5_SFIN)` == `50f63cbf36b0dd049e7a0ba27d6455745ea2aaac54bb167f9950b2b7ce9509da`:
      - `app_secrets` == (`75ecf4b972525aa0dcd057c9944d4cd5d82671d8843141d7dc2a4ff15a21dc51`, `5c74f87df04225db0f8209c9de6429e49435fdefa7cad61864874d12f31cfc8d`);
      - `verify_data(client, th)` == `R5_CFIN[4..]`.
  - **`early_secret_constant`:** with ikm `[0; 32]`, `handshake_secrets` is consistent with an early secret of `33ad0a1c607ec03b09e6cd9893680ce210adf300aa1f2660e1b22e10f170f92a`. Check it through Task 1's `derive_secret(early, "derived", H(""))` == `6f26…11ba`, and through `hkdf_extract([0; 32], [0; 32])`.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3: Implement.**
  - Each exec function is a straight line of `hkdf_extract` / `derive_secret` / `hmac_sha256` calls. Each proof is the unfolding of the spec, plus `lemma_spec_sha256_len` for the 32-byte `Hash("")`.
  - Plain-comment-cite §4.4.1's `message_hash` paragraph and the §7.1 diagram.
  - Duvet-cite §7.5 "Implementations MUST use the exporter_master_secret unless explicitly specified by the application." at the module doc, with the note "vacuous: no exporter is offered; QUIC (RFC 9001) uses none".
- [ ] **Step 4:** Run the four checks and the fresh verify, then delete the target directory.
- [ ] **Step 5: Commit:** `feat(tls): verified TLS 1.3 key schedule and HRR message_hash, RFC 8448 §3/§5 vectors (RFC 8446 §4.4.1, §7.1)`
- [ ] **Step 6: Matrix commit:** `✅ 4b: crates/tls/src/schedule.rs` on RFC 8446 §7.5 (note "no exporter derived; QUIC uses none").

---

### Task 3: Server config and negotiation (`tls::config`, `tls::negotiate`) — suggested model: opus

**Files:**
- Create: `crates/tls/src/config.rs`, `crates/tls/src/negotiate.rs`, `crates/tls/tests/negotiate.rs`
- Modify: `crates/tls/src/lib.rs`, `crates/tls/tests/common/mod.rs` (add `h3_ch`, `dummy_cfg`), `TRUSTED.md`, `docs/requirements.md`

**Interfaces:**
- Consumes:
  - `ClientHello`/`SpecClientHello`, `rfc_client_hello`, `lemma_client_hello_ok` (4a);
  - `cert_chain_ok`, `cert_chain_fits` (4a);
  - `crypto::rsa::{RsaPrivateKey, RsaKeySpec, rsa_key_wf}`;
  - `crypto::p256::scalar_valid`;
  - the codes.
- Produces (`tls::config`):
  - **`pub enum SigningKey { EcdsaP256([u8; 32]), Rsa(RsaPrivateKey) }`**, and `pub enum SpecSigningKey { EcdsaP256(Seq<u8>), Rsa(RsaKeySpec) }`.
  - **`pub struct CertChain { pub der: Vec<Vec<u8>>, pub chain_schemes: Vec<u16>, pub key: SigningKey }`**, and `SpecCertChain`.
    - `der` is end-entity first, opaque DER.
    - `chain_schemes` holds the SignatureSchemes that sign the chain's non-anchor certificates. It is trusted metadata from the shell (Decision 3). It is empty for a single self-signed certificate, which §4.4.2.2 says "MAY be signed with any algorithm".
  - **`pub struct ServerConfig { pub chains: Vec<CertChain> }`**, whose View is `Seq<SpecCertChain>`.
  - **Specs:**
    - **`pub open spec fn key_wf(k: SpecSigningKey) -> bool`**: `EcdsaP256(d) => scalar_valid(d)`, `Rsa(k) => rsa_key_wf(k)`;
    - **`pub open spec fn key_scheme(k: SpecSigningKey) -> u16`**: `EcdsaP256 => ECDSA_SECP256R1_SHA256`, `Rsa => RSA_PSS_RSAE_SHA256`;
    - **`pub open spec fn chain_wf(c: SpecCertChain) -> bool`** = `cert_chain_ok(c.der) && key_wf(c.key)`;
    - **`impl ServerConfig { pub open spec fn wf(&self) -> bool }`** = `self@.len() >= 1 && forall i. chain_wf(self@[i])`. That is the I2 note.
  - **`pub fn build_config(chains: Vec<CertChain>) -> (r: Option<ServerConfig>)`**:
    - requires `forall i. key_wf(chains@[i].key@)`, the trusted half the PKCS#8 loader establishes;
    - ensures `r is Some ⇔ (chains@.len() >= 1 && forall i. cert_chain_ok(chains@[i].der.deep_view()))`, and `r matches Some(c) ⇒ c@ == old chains view && c.wf()`.
    - It runs one `cert_chain_fits` per chain. This is the "checked when the config is built" discharge of `serialize_certificate`'s precondition.
- Produces (`tls::negotiate`):
  - **`pub enum Choice { Proceed { chain: usize, scheme: u16, share: usize }, Retry }`** (Copy).
  - **Specs:**
    - **`pub open spec fn cert_offered(ch: SpecClientHello) -> Seq<u16>`** = `ch.sig_algs_cert.unwrap_or(ch.sig_algs)`. §4.2.3: "If no "signature_algorithms_cert" extension is present, then the "signature_algorithms" extension also applies to signatures appearing in certificates.";
    - **`pub open spec fn key_usable(ch, c) -> bool`** = `ch.sig_algs.contains(key_scheme(c.key))`;
    - **`pub open spec fn chain_fits(c, offered) -> bool`** = every `c.chain_schemes[k]` is in `offered`;
    - **`pub open spec fn sha1_ok(c, offered) -> bool`** = every `c.chain_schemes[k]` in {`RSA_PKCS1_SHA1`, `ECDSA_SHA1`} is in `offered`. This is §4.4.2.2's fallback "MUST NOT [use SHA-1] otherwise".
  - **`pub open spec fn rfc_select_chain(cfg: Seq<SpecCertChain>, ch) -> Option<nat>`:**
    - the least `i` with `key_usable && chain_fits(cfg[i], cert_offered(ch))`;
    - else the least `i` with `key_usable && sha1_ok(cfg[i], cert_offered(ch))` (the §4.4.2.2 SHOULD fallback);
    - else `None`.
  - **`pub open spec fn rfc_negotiate(ch: SpecClientHello, cfg: Seq<SpecCertChain>, after_hrr: bool) -> Result<Choice, u64>`.** The check order is the requirement (outline Decision 7):
    1. `!ch.cipher_suites.contains(TLS_AES_128_GCM_SHA256)` → `ALERT_HANDSHAKE_FAILURE` (§4.1.1);
    2. `ch.alpn` is `None`, or doesn't contain `H3_ALPN@` → `ALERT_NO_APPLICATION_PROTOCOL` (RFC 9001 §8.1). An absent ALPN is included;
    3. `rfc_select_chain` is `None` → `ALERT_HANDSHAKE_FAILURE` (§4.4.3: the scheme MUST be one the client offered). Let `i` be the chain and `scheme = key_scheme(cfg[i].key)`;
    4. let `g = ch.groups matches Some(gs) && gs.contains(SECP256R1)`:
       - if `after_hrr`: `g && ch.key_shares matches Some(ks) && ks.len() == 1 && ks[0].group == SECP256R1` → `Proceed { i, scheme, 0 }`, else `ALERT_ILLEGAL_PARAMETER`. §4.1.2: CH2 replaces the shares "with a list containing a single KeyShareEntry from the indicated group";
       - else if `g` and the least `j` with `ks[j].group == SECP256R1` exists → `Proceed { i, scheme, j }`. A share for a group absent from supported_groups is unusable (§4.2.8);
       - else if `g` → `Retry`;
       - else → `ALERT_HANDSHAKE_FAILURE` (§2.1, §4.1.1).
  - **`pub fn negotiate(ch: &ClientHello, cfg: &ServerConfig, after_hrr: bool) -> (r: Result<Choice, u64>)`** ensures `r == rfc_negotiate(ch@, cfg@, after_hrr)`.
  - **Theorems:**
    - **`theorem_no_second_hrr(ch, cfg)`:** `rfc_negotiate(ch, cfg, true) != Ok(Retry)`.
    - **`theorem_proceed_facts(ch, cfg, h)`:** `Ok(Proceed { chain, scheme, share })` ⇒
      - `chain < cfg.len()`;
      - `scheme == key_scheme(cfg[chain].key)` and `ch.sig_algs.contains(scheme)`;
      - `ch.key_shares matches Some(ks)`, `share < ks.len()` and `ks[share].group == SECP256R1`;
      - `ch.alpn` contains `h3`.
    - **`theorem_no_unsolicited(body, cfg, h)`:** `rfc_client_hello(body) == Ok(ch)` and `rfc_negotiate(ch, cfg, h) is Ok` ⇒ `ch.key_shares is Some`, by 4a's §9.2 groups⇔key_share check. Together with ALPN `h3`, and QTP/supported_versions always present, every extension in SH, HRR and EE was offered (§4.2; used by Task 6).

- [ ] **Step 1: Failing tests** (`tests/negotiate.rs`).
  - Helpers, in `common`:
    - `h3_ch(shares: &[(u16, Vec<u8>)], edit)` = `A2_CH` with ALPN `[b"h3"]` and key_share entries `shares`, then `edit` (a `with`-style closure);
    - `P256_SHARE` = the 65-byte key_exchange of R5_CH2's `0x33` entry;
    - `X25519_SHARE` = A.2's 32-byte share;
    - `dummy_cfg(keys: &[(SigningKey, Vec<u16>)])` builds `ServerConfig { chains }` directly, with `der = vec![vec![0x30, 0x00]]`. The tests aren't verified, so `key_wf` is not needed.
    - `ecdsa()` = `SigningKey::EcdsaP256([1; 32])`, and `rsa()` = `SigningKey::Rsa` with dummy 1-byte fields.
  - **`a2_alpn`:** `negotiate(&p(A2_CH), &dummy_cfg([(ecdsa(), [])]), false)` == `Err(0x178)`.
  - **`order`:**
    - A.2 with suites `[0x1302]` → `Err(0x128)`, because the suite is checked before ALPN;
    - `h3_ch` with ALPN `[b"h3-29"]` → `Err(0x178)`;
    - `h3_ch` with sig_algs `[0x0804]` and an ECDSA-only config → `Err(0x128)`, even though the shares are X25519-only. That is step 3 before step 4.
  - **`groups`.** Each row is (shares and groups → result):
    - `[(0x1d, X25519)]` → `Ok(Retry)`;
    - `[(0x1d, X25519), (0x17, P256)]` → `Proceed { 0, 0x0403, 1 }`;
    - groups `[0x1d]` with share `(0x17, P256)` → `Err(0x128)` (unusable; no Retry);
    - groups `[0x1d]` with `[(0x1d, X25519)]` → `Err(0x128)`;
    - `[]` (empty client_shares) → `Ok(Retry)`.
  - **`after_hrr`.** With `after_hrr = true`:
    - `[(0x17, P256)]` → `Proceed { .., share: 0 }`;
    - `[(0x17, P256), (0x17, P256)]` → `Err(0x12f)`;
    - `[(0x1d, X25519)]` → `Err(0x12f)`;
    - `[]` → `Err(0x12f)`.
  - **`chain_selection`:**
    - config `[(ecdsa(), [0x0401]), (rsa(), [])]`, client sig_algs `[0x0403, 0x0804]`, no sig_algs_cert → `chain 1, 0x0804`. Chain 0 isn't signed with an offered scheme;
    - the same with sig_algs_cert `[0x0401]` → `chain 0, 0x0403`;
    - config `[(ecdsa(), [0x0501])]` with sig_algs `[0x0403]` → `chain 0`, as the fallback;
    - config `[(ecdsa(), [0x0203])]` with sig_algs `[0x0403]` → `Err(0x128)`. That is SHA-1 when not offered;
    - an RSA-only config with client sig_algs `[0x0403]` → `Err(0x128)`.
  - **`curl_ch`:** `negotiate(&p(CURL_CH), &dummy_cfg([(ecdsa(), [])]), false)` == `Ok(Retry)`.
  - **`build_config_checks`:**
    - `build_config(vec![])` → `None`;
    - a chain with `der = vec![]` → `None`;
    - a chain with `der = vec![vec![]]` (an empty certificate) → `None`;
    - a chain with `der = vec![vec![0x30; 10]]` → `Some`.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3: Implement.**
  - The exec functions are small index loops (`contains_u16`, first-match), each with an `==`-spec ensures.
  - **TRUSTED.md, one new row:**
    - Item: "`tls::config::ServerConfig::wf()` key half: the trusted PKCS#8 loader in the shell establishes ServerConfig::wf() for its keys (`rsa_key_wf`, including primality of p and q; the P-256 scalar range), and the configured chain matches its key, is X.509v3, permits digitalSignature, uses rsaEncryption for RSA keys, and `chain_schemes` lists the SignatureSchemes signing its non-anchor certificates. The chain-size half is checked by `build_config`";
    - File: `crates/tls/src/config.rs`;
    - Why trusted: "no verified code can establish primality or parse X.509";
    - Removed in phase: "never (config boundary)".
  - Duvet-cite, at the matching `rfc_negotiate` step:
    - §2.1 ("If no common cryptographic parameters can be negotiated, the server MUST abort the handshake with an appropriate alert.");
    - §4.1.1 (the handshake_failure / insufficient_security sentence, and the HelloRetryRequest sentence);
    - §4.2.3:
      - the missing-extension sentence is 4a's; here, the "MUST NOT be offered or negotiated" deprecated-algorithm sentence: we sign only with 0x0403/0x0804;
      - the rsa_pss_rsae salt and OID sentences: the salt is 32 = the hash length, and the rsaEncryption OID is in the trusted row;
    - §4.2.8: "This value MUST be in the same group as the KeyShareEntry value offered by the client that the server has selected for the negotiated key exchange." and "Servers MUST NOT send a KeyShareEntry for any group not indicated in the client's "supported_groups" extension …";
    - §4.4.2.2 (all four bullets, the "MUST be signed by a signature algorithm advertised by the client if it is able" sentence, and the SHA-1 fallback sentence);
    - §9.1 (TLS_AES_128_GCM_SHA256, secp256r1 and the three signature schemes);
    - RFC 9001 §8.1 (the no_application_protocol sentence).
- [ ] **Step 4:** Run the four checks and the fresh verify, then delete the target directory.
- [ ] **Step 5: Commit:** `feat(tls): verified negotiation (suite, ALPN, chain/scheme, group) and checked ServerConfig (RFC 8446 §4.1.1, §4.2.3, §4.2.8, §4.4.2.2; RFC 9001 §8.1)`
- [ ] **Step 6: Matrix commit:** `✅ 4b: crates/tls/src/negotiate.rs` on:
  - RFC 8446 §2.1, §4.1.1, §4.2.3, §4.2.8 and §9.1;
  - the two §4.2.3 (req) rows;
  - §4.4.2.2. Rewrite its stale "ECDSA P-256 key" note to "P-256 or RSA key; chain metadata trusted (TRUSTED.md)", which is the carry-over;
  - RFC 9001 §8.1 (note "checked at ClientHello, before any HRR").
  - Each replaces the row's 4a touched note (§4.2.3, §4.2.8, RFC 9001 §8.1), so every row ends with a single closing note.

---

### Task 4: CertificateVerify content and signing (`tls::sign`) — suggested model: sonnet

**Files:**
- Create:
  - `crates/tls/src/sign.rs`, `crates/tls/tests/sign.rs`;
  - `crates/tls/tests/data/ecdsa-p256-cert.der`, `crates/tls/tests/data/rsa2048-cert.der`.
- Modify: `crates/tls/Cargo.toml` (ring dev-dependency), `crates/tls/src/lib.rs`, `crates/tls/tests/common/mod.rs` (key constants), `TRUSTED.md` (the test-only pin line), `docs/requirements.md`

**Interfaces:**
- Consumes:
  - Task 3's `SigningKey`/`SpecSigningKey`, `key_wf`;
  - `crypto::ecdsa::{spec_ecdsa_p256_sha256_sign, p256_ecdsa_sign, spec_ecdsa_der, serialize_ecdsa_der}`;
  - `crypto::rsa::{spec_rsassa_pss_sign, rsa_pss_sha256_sign}`;
  - `CV_SERVER_CONTEXT`, `ALERT_INTERNAL_ERROR`.
- Produces (`tls::sign`):
  - **`pub open spec fn spec_cv_content(th: Seq<u8>) -> Seq<u8>`** = `Seq::new(64, |_i| 0x20u8) + CV_SERVER_CONTEXT@ + seq![0x00u8] + th`. That is §4.4.3: 64 × 0x20, the context string, a 0 separator, then the content.
  - **`pub open spec fn spec_cv_signature(key: SpecSigningKey, th: Seq<u8>, salt: Seq<u8>) -> Option<Seq<u8>>`:**
    - let `m = spec_cv_content(th)`;
    - `EcdsaP256(d)` → `spec_ecdsa_p256_sha256_sign(d, m)` mapped through `spec_ecdsa_der`;
    - `Rsa(k)` → `Some(spec_rsassa_pss_sign(k, m, salt))`;
    - then `None` if the result is longer than `0xffff`. `// ponytail: unreachable (DER ≤ 72 B, PSS ≤ 512 B); a length lemma over der_uint_content/i2osp removes the guard.`
  - **`pub fn cv_content(th: &[u8; 32]) -> (r: Vec<u8>)`** ensures `r@ == spec_cv_content(th@)`.
  - **`pub fn sign_cv(key: &SigningKey, th: &[u8; 32], salt: &[u8; 32]) -> (r: Result<Vec<u8>, u64>)`**:
    - requires `key_wf(key@)`;
    - ensures:
      - `r matches Ok(s) ⇒ spec_cv_signature(key@, th@, salt@) == Some(s@)`, which also gives `s@.len() <= 0xffff`;
      - `r matches Err(e) ⇒ e == ALERT_INTERNAL_ERROR`;
      - `key@ is EcdsaP256 ⇒ (r is Ok ⇔ spec_cv_signature(..) is Some)`. ECDSA is exact; the RSA shim is one-directional.
    - The `salt` is ignored for ECDSA (RFC 6979). The runtime `len() <= 0xffff` check runs for both kinds.

- [ ] **Step 1: Fixtures** (scripted; record every command and the sha256 of each committed file in the task report). In a fresh scratch directory:
  ```sh
  openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:P-256 -nodes -keyout ec.key -outform DER -out ecdsa-p256-cert.der -days 36500 -subj /CN=localhost -addext subjectAltName=DNS:localhost -addext keyUsage=critical,digitalSignature
  openssl req -x509 -newkey rsa:2048 -nodes -keyout rsa.key -outform DER -out rsa2048-cert.der -days 36500 -subj /CN=localhost -addext subjectAltName=DNS:localhost -addext keyUsage=critical,digitalSignature
  ```
  - Extract the P-256 scalar (`ECDSA_D: [u8; 32]`) and the RSA `n, e, d, p, q` (`RSA_N: &[u8]` …, big-endian) with a `python3 -I` script using `cryptography`. Keep the script outside the repo.
  - Paste the output into `common/mod.rs`, together with `pub fn rsa_key() -> RsaPrivateKey`, `pub const ECDSA_CERT`/`RSA_CERT` (`include_bytes!`), and their lengths in `vectors_intact`.
  - Both certificates are self-signed leaves, so `chain_schemes` is empty.
- [ ] **Step 2: Failing tests** (`tests/sign.rs`):
  - **`cv_content_rfc8446_example`:** `cv_content(&[0x01; 32])` == `20`×64 ‖ `544c5320312e332c207365727665722043657274696669636174655665726966` `79` ‖ `00` ‖ `01`×32 (130 bytes). That is the §4.4.3 example, copied from rfc8446.txt by script.
  - **`ecdsa_verifies`:**
    - `sign_cv(&EcdsaP256(ECDSA_D), &[0x5a; 32], &[0; 32])` is `Ok(sig)`, with `sig[0] == 0x30` and `sig.len() <= 72`;
    - `ring::signature::UnparsedPublicKey::new(&ECDSA_P256_SHA256_ASN1, p256_public_key(&ECDSA_D).unwrap()).verify(&cv_content(&[0x5a; 32]), &sig)` is `Ok`;
    - a second call, and a call with salt `[9; 32]`, give identical bytes (RFC 6979).
  - **`rsa_verifies`:**
    - `sign_cv(&Rsa(rsa_key()), &[0x5a; 32], &[0x33; 32])` is `Ok(sig)` with `sig.len() == 256`;
    - `ring::signature::RsaPublicKeyComponents { n: RSA_N, e: RSA_E }.verify(&RSA_PSS_2048_8192_SHA256, &cv_content(..), &sig)` is `Ok`;
    - salt `[0x34; 32]` gives different bytes, which also verify.
  - **`ecdsa_invalid_scalar`:** `sign_cv(&EcdsaP256([0; 32]), ..)` == `Err(0x150)`. The spec is `None` for an invalid `d`. Only the test can reach this, since `key_wf` excludes it.
  - **`wrong_context_fails`:** ring verification of the ECDSA signature over `cv_content` with byte 64 changed (`T` → `t`) fails. This pins the context string.
- [ ] **Step 3:** Run the tests and confirm they fail.
- [ ] **Step 4: Implement.**
  - ECDSA: `p256_ecdsa_sign(d, &content)`, then `serialize_ecdsa_der` into a fresh `Vec`.
  - RSA: `rsa_pss_sha256_sign(k, &content, salt)`.
  - `None` from either → `Err(ALERT_INTERNAL_ERROR)`, as does `len > 0xffff`.
  - TRUSTED.md, Pinned versions: add "Test-only (crates/tls dev-dependencies, not in the trusted base): ring =0.17.14; rustls =0.23.45 (Task 7)".
  - Duvet-cite §4.4.3:
    - "Servers MUST send this message when authenticating via a certificate.";
    - the content bullets;
    - "the signature algorithm MUST be one offered in the client's "signature_algorithms" extension …" (discharged by Task 3);
    - "RSA signatures MUST use an RSASSA-PSS algorithm …";
    - "The SHA-1 algorithm MUST NOT be used in any signatures of CertificateVerify messages.".
- [ ] **Step 5:** Run the four checks and the fresh verify, then delete the target directory.
- [ ] **Step 6: Commit:** `feat(tls): verified CertificateVerify content and ECDSA/RSA-PSS signing (RFC 8446 §4.4.3)`
- [ ] **Step 7: Matrix commit:** `✅ 4b: crates/tls/src/sign.rs` on RFC 8446 §4.4.3 and §4.4.3 (req) "RSA signatures MUST use an RSASSA-PSS algorithm". The §4.4.3 entry replaces 4a's touched note.

---

### Task 5: The server flight (`tls::flight`) — suggested model: opus

**Files:**
- Create: `crates/tls/src/flight.rs`, `crates/tls/tests/flight.rs`
- Modify: `crates/tls/src/lib.rs`, `TRUSTED.md` (add `Level`, `TlsEvent` to the tls derived-impl row), `docs/requirements.md`

**Interfaces:**
- Consumes:
  - Tasks 2–4;
  - 4a's `spec_server_hello_bytes`, `serialize_server_hello`, `spec_encrypted_extensions_bytes`, `serialize_encrypted_extensions`, `spec_certificate_bytes`, `serialize_certificate`, `spec_certificate_verify_bytes`, `serialize_certificate_verify`, `spec_finished_bytes`, `serialize_finished`, `lemma_client_hello_ok`;
  - `crypto::p256::{spec_p256_public_key, p256_public_key, spec_p256_ecdh, p256_ecdh}`.
- Produces (`tls::flight`):
  - **`pub enum Level { Initial, Handshake, OneRtt }`** (Copy). There is no 0-RTT level (RFC 9114 §7.2.4.2: 0-RTT is never accepted).
  - **`pub enum TlsEvent { Send { level: Level, data: Vec<u8> }, Secrets { level: Level, client: [u8; 32], server: [u8; 32] }, PeerParams(Vec<u8>), Complete }`**, with `SpecTlsEvent` and a `DeepView`.
  - **`pub struct SpecFlight { pub events: Seq<SpecTlsEvent>, pub client_vd: Seq<u8> }`**.
  - **`pub open spec fn spec_flight(cfg: Seq<SpecCertChain>, tp: Seq<u8>, t0: Seq<u8>, ch: SpecClientHello, chain: nat, scheme: u16, share: nat, rand: Seq<u8>) -> Result<SpecFlight, u64>`.**
    - `t0` is the transcript up to and including the ClientHello being answered: `CH`, or `message_hash(CH1) ‖ HRR ‖ CH2`.
    - The order is the requirement:
      1. `d = rand[32..64]`, `peer = ch.key_shares.unwrap()[share].key_exchange`;
      2. `spec_p256_public_key(d)` is `None` → `ALERT_INTERNAL_ERROR`, else `pk`. `// ponytail: an out-of-range scalar has probability ≈ 2^-32; internal_error, not a resample` (outline Decision 6);
      3. `spec_p256_ecdh(d, peer)` is `None`, or equals `zeros32()`, → `ALERT_ILLEGAL_PARAMETER`. §4.2.8.2 says "peers MUST validate", and §7.4.2 says "MUST check whether the computed Diffie-Hellman shared secret is the all-zero value and abort"; both are taken literally. Else `z`;
      4. `sh = spec_server_hello_bytes(rand[0..32], ch.legacy_session_id, SECP256R1, pk)`, and `t1 = t0 + sh`;
      5. `hs = spec_handshake_secret(z)`, `c_hs = spec_derive_secret(hs, LABEL_C_HS@, t1)`, `s_hs = spec_derive_secret(hs, LABEL_S_HS@, t1)`;
      6. `ee = spec_encrypted_extensions_bytes(tp)`, `cert = spec_certificate_bytes(cfg[chain].der)`, `t2 = t1 + ee + cert`;
      7. `spec_cv_signature(cfg[chain].key, spec_sha256(t2), rand[64..96])` is `None` → `ALERT_INTERNAL_ERROR`, else `sig`. Then `cv = spec_certificate_verify_bytes(scheme, sig)` and `t3 = t2 + cv`;
      8. `fin = spec_finished_bytes(spec_verify_data(s_hs, t3))`, `t4 = t3 + fin`, `m = spec_master_secret(hs)`;
      9. `Ok(SpecFlight { events, client_vd: spec_verify_data(c_hs, t4) })`, with `events` =
         ```
         [ PeerParams(ch.transport_params),
           Send { Initial, sh },
           Secrets { Handshake, c_hs, s_hs },
           Send { Handshake, ee + cert + cv + fin },
           Secrets { OneRtt, spec_derive_secret(m, LABEL_C_AP@, t4), spec_derive_secret(m, LABEL_S_AP@, t4) } ]
         ```
  - **`pub fn build_flight(cfg: &ServerConfig, local_tp: &[u8], t0: Vec<u8>, ch: &ClientHello, chain: usize, scheme: u16, share: usize, rand: &[u8; TLS_RAND_LEN]) -> (r: Result<(Vec<TlsEvent>, [u8; 32]), u64>)`:**
    - requires:
      - `cfg.wf()` and `local_tp@.len() <= 1024`;
      - `t0@.len() <= 0x2_0000`;
      - `exists|b| rfc_client_hello(b) == Ok(ch@)`, so `lemma_client_hello_ok` applies;
      - the facts of `theorem_proceed_facts` for `(chain, scheme, share)`.
    - ensures `match spec_flight(cfg@, local_tp@, t0@, ch@, chain, scheme, share, rand@)`:
      - `Err(e) => r == Err(e)`;
      - `Ok(f) => (r matches Ok((evs, vd)) ⇒ evs.deep_view() == f.events && vd@ == f.client_vd) && (r matches Err(e) ⇒ e == ALERT_INTERNAL_ERROR)`.

      The second conjunct is the RSA shim's one-directional `None`.
  - **`theorem_flight_order(..)`.** If `spec_flight` is `Ok(f)`:
    - `f.events.len() == 5`, with the shape above;
    - no `Send { OneRtt, .. }` exists, and `Secrets { Handshake }` precedes `Send { Handshake }`. Together these are the "server handshake traffic secret derived before EE is sent" MUST;
    - the `Send { Initial }` data at `[6..38]` is `rand[0..32]`;
    - its key_share group is `SECP256R1`, which is the group of `ch.key_shares[share]`.

- [ ] **Step 1: Failing tests** (`tests/flight.rs`).
  - Shared setup:
    - `rsa_cfg()` = `ServerConfig { chains: [CertChain { der: [RSA_CERT], chain_schemes: [], key: Rsa(rsa_key()) }] }`, and `ecdsa_cfg()` likewise;
    - `ch2 = p(with(R5_CH2, remove 0x2c, push (0x10, ALPN [b"h3"]), push (0x39, [1, 0])))`, for the typed fields only. The `h3` ALPN keeps the call inside `build_flight`'s `theorem_proceed_facts` precondition;
    - `t0 = message_hash(R5_CH1) ‖ R5_HRR ‖ R5_CH2`, the raw RFC bytes;
    - `rand = R5_SH[6..38] ‖ 8c510601…34ed ‖ [0x33; 32]`.
  - **`rfc8448_s5_flight`:** `build_flight(&rsa_cfg(), &[1, 0], t0, &ch2, 0, 0x0804, 0, &rand)` is `Ok((evs, vd))` with:
    - `evs[0] == PeerParams([1, 0])`;
    - `evs[1] == Send { Initial, R5_SH }`, **byte-exact** (123 bytes);
    - `evs[2] == Secrets { Handshake, 158aa7ab…1566, 3403e781…f8a1 }`. These are RFC 8448's own values, through our HRR transcript;
    - `evs[3]`'s data == `ee ‖ cert ‖ cv ‖ fin`, where:
      - `ee` is `serialize_encrypted_extensions([1, 0])` and `cert` is `serialize_certificate([RSA_CERT])`;
      - `cv` starts `0f000104 0804 0100` and its signature ring-verifies (RSA-PSS) over `cv_content(H(t0‖R5_SH‖ee‖cert))`;
      - `fin == serialize_finished(verify_data(3403…, H(t0‖R5_SH‖ee‖cert‖cv)))`;
    - `evs[4] == Secrets { OneRtt, app_secrets(master_secret(ce02…b148), H(t4)) }`;
    - `vd == verify_data(158a…, H(t4))`.
  - **`ecdsa_flight`:** the same with `ecdsa_cfg()` and scheme `0x0403`. The CV's signature ring-verifies (`ECDSA_P256_SHA256_ASN1`), and `evs[1]` is still R5_SH.
  - **`bad_peer_share`.** `ch2` with its share replaced; each gives `Err(0x12f)`:
    - `04 ‖ [0; 64]`;
    - `04 ‖ [0xff; 64]`;
    - a 33-byte `02 ‖ x`;
    - a 65-byte point with one coordinate byte flipped.
  - **`invalid_scalar`:** `rand[32..64] = [0xff; 32]` (≥ n) → `Err(0x150)`.
  - **`random_from_rand`:** two `rand` values that differ only in `[0..32]` give `Send { Initial }` data whose `[6..38]` equals each `rand[0..32]`. Every other byte of the ServerHello is unchanged, and none of it depends on `ch2.random`.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3: Implement.**
  - Build the transcript in a local `Vec<u8>`, starting from `t0` and extended by each serializer's output.
  - Hash with `crypto::sha256::sha256` at `t1`, `t2`, `t3` and `t4`. `MAX_INPUT_LEN` holds because `t4.len() < 0x2_0000 + 2^25`.
  - Every serializer precondition is discharged as in the Global Constraints table:
    - `by (compute)` for `!spec_reserved_group(0x0017)` and `!spec_reserved_scheme(0x0403 / 0x0804)`;
    - `lemma_client_hello_ok` for the echo length;
    - `cfg.wf()` for `cert_chain_ok`;
    - `sign_cv`'s ensures for the signature length.
  - Duvet-cite:
    - **§2:** "the server's share MUST be in the same group as one of the client's shares." and "Application Data MUST NOT be sent prior to sending the Finished message". The 1-RTT secrets are the last event, and 3d sends no 1-RTT before `on_handshake_complete`.
    - **§4.1.3:**
      - "This structure is generated by the server and MUST be generated independently of the ClientHello.random." and "… but the remaining bytes MUST be random." (`rand[0..32]`);
      - the three downgrade-sentinel MUSTs ("TLS 1.3 servers which negotiate TLS 1.2 or below …", "If negotiating TLS 1.2 …", "If negotiating TLS 1.1 or below …"), each with the note "vacuous: 4a rejects every ClientHello without 0x0304 (protocol_version), so we never negotiate ≤ 1.2";
      - the echo is a plain `//` comment (`ch.legacy_session_id`). §4.1.3's only echo MUST is the client's check.
    - **§4.3.1:** "In all handshakes, the server MUST send the EncryptedExtensions message immediately after the ServerHello message.".
    - **§4.4.2:** "The server MUST send a Certificate message whenever the agreed-upon key exchange method uses certificates for authentication".
    - **§7.4.2:** both MUSTs: no truncation (the `[u8; 32]`), and the all-zero check.
    - **Appendix C** (`#appendix-C.5`): the "MUST NOT use TLS in such a way absent explicit configuration" sentence. Every flight carries Certificate and CertificateVerify.
- [ ] **Step 4:** Run the four checks and the fresh verify, then delete the target directory.
- [ ] **Step 5: Commit:** `feat(tls): verified server flight SH/EE/Cert/CV/Finished with per-level secrets (RFC 8446 §2, §4.1.3, §4.3.1, §4.4.2, §7.4.2)`
- [ ] **Step 6: Matrix commit:** `✅ 4b: crates/tls/src/flight.rs` on RFC 8446 §2, §4.1.3 (note "random = rand[0..32]; downgrade sentinel vacuous, TLS 1.3 only"), §4.3.1, §4.4.2, §7.4.2 and Appendix C. These replace 4a's touched notes on §4.1.3, §4.3.1 and §4.4.2.

---

### Task 6: The handshake state machine (`tls::server`) — suggested model: opus

**Files:**
- Create: `crates/tls/src/server.rs`, `crates/tls/tests/server.rs`
- Modify: `crates/tls/src/lib.rs`, `TRUSTED.md`, `docs/requirements.md`

**Interfaces:**
- Consumes:
  - Tasks 2, 3 and 5;
  - 4a's `HsReader` (`new`, `push`, `next_message`, `is_empty`), `rfc_next_message`, `rfc_client_hello`, `parse_client_hello`, `rfc_finished`, `parse_finished`, `spec_hello_retry_request_bytes`, `serialize_hello_retry_request`, `HT_CLIENT_HELLO`, `HT_FINISHED`.
- Produces (`tls::server`). This transcribes RFC 8446 Appendix A.2 restricted to our features:
  - `START → RECVD_CH → NEGOTIATED → WAIT_FINISHED → CONNECTED`, with the HRR loop back to `START`;
  - `WAIT_EOED`, `WAIT_FLIGHT2`'s client-certificate branch, `WAIT_CERT` and `WAIT_CV` are never entered.

  The types:
  - **`pub enum SpecPhase { Start, HrrSent, WaitFinished, Complete, Failed }`**.
  - **`pub struct ServerHandshake<'a>`**, with private fields:
    - `cfg: &'a ServerConfig`, `local_tp: Vec<u8>`;
    - `phase`;
    - `initial: HsReader`, `handshake: HsReader`;
    - `transcript: Vec<u8>`;
    - `ch1: Option<ClientHello>`;
    - `client_vd: [u8; 32]`;
    - `err: u64`.
  - **`pub struct SpecServerHs { phase, initial: Seq<u8>, handshake: Seq<u8>, transcript: Seq<u8>, ch1: Option<SpecClientHello>, client_vd: Seq<u8>, err: u64 }`**. This is the View. `cfg@` and `local_tp@` are exposed by `pub closed spec fn cfg_view` / `tp_view`, or made `open`, whichever verifies.
  - **`pub open spec fn wf(&self) -> bool`:**
    - `self.cfg.wf()` and `local_tp@.len() <= 1024`;
    - `transcript@.len() <= 0x2_0000`;
    - `phase is HrrSent ⇔ ch1 is Some`.
  - **Spec functions:**
    - **`pub open spec fn spec_expected(p: SpecPhase) -> Option<(Level, u8)>`**: `Start | HrrSent → (Initial, HT_CLIENT_HELLO)`, `WaitFinished → (Handshake, HT_FINISHED)`, otherwise `None`.
    - **`pub open spec fn spec_same_except_shares(a: SpecClientHello, b: SpecClientHello) -> bool`**: equality of every field except `key_shares`. The fields are `random`, `legacy_session_id`, `cipher_suites`, `versions`, `groups`, `sig_algs`, `sig_algs_cert`, `alpn`, `server_name` and `transport_params`. That is §4.1.2's "the client MUST send the same ClientHello without modification, except as follows", checked over the typed fields (Decision 4).
    - **`pub open spec fn spec_failed(s, e) -> SpecServerHs`**: `s` with phase `Failed`, `err = e`, `transcript = empty`, `ch1 = None` and `client_vd = zeros32()`. The readers are unchanged. Secrets are dropped (in support of §6, which 4c closes).
  - **`pub open spec fn spec_step(cfg, tp, s: SpecServerHs, m: Seq<u8>, rand: Seq<u8>) -> Result<(SpecServerHs, Seq<SpecTlsEvent>), u64>`**, for one complete message `m` (header included) of the expected type:
    - **`Start`:**
      - `ch = rfc_client_hello(m.skip(4))?`, then `rfc_negotiate(ch, cfg, false)?`;
      - `Retry` → let `hrr = spec_hello_retry_request_bytes(ch.legacy_session_id, SECP256R1)`. The result is phase `HrrSent`, `transcript = spec_message_hash(m) + hrr`, `ch1 = Some(ch)`, with events `[Send { Initial, hrr }]`;
      - `Proceed { c, sc, j }` → `f = spec_flight(cfg, tp, m, ch, c, sc, j, rand)?`. The result is phase `WaitFinished`, `transcript = empty`, `client_vd = f.client_vd`, with events `f.events`.
    - **`HrrSent`:**
      - `ch = rfc_client_hello(m.skip(4))?`;
      - `!spec_same_except_shares(s.ch1.unwrap(), ch)` → `ALERT_ILLEGAL_PARAMETER`;
      - `rfc_negotiate(ch, cfg, true)?` can only be `Proceed` (`theorem_no_second_hrr`). The flight uses `t0 = s.transcript + m`, and `ch1 = None`.
    - **`WaitFinished`:** `vd = rfc_finished(m.skip(4))?`. If `vd != s.client_vd` → `ALERT_DECRYPT_ERROR`; else phase `Complete`, `client_vd = zeros32()`, with events `[Complete]`.
  - **`pub open spec fn spec_on_crypto(cfg, tp, s, level: Level, data: Seq<u8>, rand) -> (SpecServerHs, Result<Seq<SpecTlsEvent>, u64>)`:**
    1. `s.phase is Failed` → `(s, Err(s.err))`, which is absorbing;
    2. `data.len() > 0` and `spec_expected(s.phase)` is not `Some((level, _))` → `(spec_failed(s, U), Err(U))`, with `U = ALERT_UNEXPECTED_MESSAGE`. This covers:
       - any OneRtt byte (post-handshake, KeyUpdate: §4.6.3, RFC 9001 §6);
       - an Initial byte after the ServerHello ("receives a ClientHello at any other time", §4.1.2);
       - any byte after `Complete`;
    3. otherwise `spec_drain(.., s with reader[level] += data, level, rand, empty)`. That drain:
       - while `spec_expected(phase) == Some((level, ty))`, applies `rfc_next_message(reader[level], ty)`;
       - `Err(e)` → fail with `e`;
       - `Ok(None)` → stop, with `Ok(acc)`;
       - `Ok(Some(n))` → pop `n` bytes, then apply `spec_step`. `Err(e)` → fail with `e`; otherwise append its events and continue.

       Each step advances the phase strictly (`decreases` its rank), so at most two messages are processed per call.
    - Bytes left in a reader whose level is no longer expected stay there. `pending()` exposes them for 4c's RFC 9001 §4.1.3 PROTOCOL_VIOLATION (Decision 6).
  - **Exec:**
    - **`pub fn new(cfg: &'a ServerConfig, local_tp: Vec<u8>) -> (r: ServerHandshake<'a>)`**:
      - requires `cfg.wf()` (I2) and `local_tp@.len() <= 1024` (M1, pushed to 4c);
      - ensures `r.wf()`, phase `Start`, and both readers empty.
    - **`pub fn on_crypto(&mut self, level: Level, data: &[u8], rand: &[u8; TLS_RAND_LEN], ev: &mut Vec<TlsEvent>) -> (r: Result<(), u64>)`**:
      - requires `old(self).wf()`;
      - ensures `final(self).wf()`, and with `(s2, res) = spec_on_crypto(cfg@, tp@, old(self)@, level, data@, rand@)`:
        - `res == Err(e) ⇒ r == Err(e) && final(self)@ == s2 && ev@ == old(ev)@`;
        - `res == Ok(evs) ⇒ (r is Ok && final(self)@ == s2 && ev.deep_view() == old(ev).deep_view() + evs) || (r == Err(ALERT_INTERNAL_ERROR) && final(self)@.phase is Failed && ev@ == old(ev)@)`.
      - The events are built in a local `Vec` and appended only on `Ok`.
      - `next_message` is called after every `push` (M7).
    - **`pub fn pending(&self, level: Level) -> (r: bool)`** ensures `r == !(reader(level)@.len() == 0)`, and `false` for `OneRtt`.
    - **`pub fn is_complete(&self) -> (r: bool)`** ensures `r == (self@.phase is Complete)`.
    - **`fn ct_eq32(a: &[u8; 32], b: &[u8; 32]) -> (r: bool)`** ensures `r == (a@ == b@)`. It xor-accumulates (`acc |= a[i] ^ b[i]`) over all 32 bytes with no early exit, with a `by (bit_vector)` step lemma, as in 3d ruling #8.
  - **Theorems,** over `spec_step` / `spec_on_crypto`:
    - **`theorem_failed_absorbing`:** `s.phase is Failed ⇒ spec_on_crypto(.., s, ..) == (s, Err(s.err))`, so no `Send` ever follows `Failed`;
    - **`theorem_complete_iff_finished`:** for a step result `Ok((s2, evs))`, `evs.contains(Complete) ⇔ (s.phase is WaitFinished && m == spec_finished_bytes(s.client_vd))`;
    - **`theorem_no_second_hrr`:** a step from `HrrSent` never emits a `Send { Initial, d }` with `d[6..38] == HRR_RANDOM@`, and never reaches `HrrSent`;
    - **`theorem_event_discipline`:** in every `Ok` result of `spec_on_crypto`:
      - no `Send { OneRtt }` (3d's `crypto_write` requires `level != OneRtt`);
      - every `Send { Handshake }` is preceded by a `Secrets { Handshake }` in the same result;
      - `PeerParams` appears at most once per connection, only in a step that leads to `WaitFinished`, and carries that ClientHello's (CH2's, after HRR) `transport_params`;
    - **`theorem_reader_bound`:** after any call, `reader(expected level)@.len() < 4 + MAX_HS_BODY`. This is the M7 obligation 4c relies on.

- [ ] **Step 1: Failing tests** (`tests/server.rs`).
  - Setup:
    - `cfg = ecdsa_cfg()` (Task 5), `R = [7u8; 96]`, `TP = [1, 0]`, and `hs = ServerHandshake::new(&cfg, TP.to_vec())`;
    - `direct_ch = h3_ch([(0x17, P256_SHARE)])` and `hrr_ch = h3_ch([(0x1d, X25519_SHARE)])`;
    - `fin_for(evs, transcript)`: the test computes the client Finished with Task 2's `verify_data(client_hs, H(transcript))`, using the `Secrets { Handshake }.client` it received.
  - **`a2_ch_0x178`:**
    - `on_crypto(Initial, A2_CH)` == `Err(0x178)`, and `ev` is empty;
    - a second call at any level gives `Err(0x178)` again, with `ev` still empty. A.2's TPs are never handed out (see 4c binding notes).
  - **`curl_ch_hrr`:**
    - `on_crypto(Initial, CURL_CH[..1200])` → `Ok`, with `ev` empty;
    - then `CURL_CH[1200..]` → `Ok`, with `ev == [Send { Initial, hex("020000340303cf21…002b00020304") }]`. That is 4a's 56-byte `hrr_p256` vector;
    - `pending(Initial)` is false.
  - **`direct_p256`:**
    - `on_crypto(Initial, direct_ch)` gives events of kinds `[PeerParams, Send(Initial), Secrets(Handshake), Send(Handshake), Secrets(OneRtt)]`;
    - `PeerParams` is A.2's 50-byte TP, and the `Send(Initial)` data `[6..38]` is `R[0..32]`;
    - then `on_crypto(Handshake, fin_for(..))` → `ev == [Complete]`, and `is_complete()`.
  - **`hrr_then_ch2`:**
    - `hrr_ch` → HRR;
    - then CH2 = `hrr_ch` with key_share `[(0x17, P256_SHARE)]` → the five-event flight;
    - its `Secrets { Handshake }` == `handshake_secrets(p256_ecdh(R[32..64], P256_SHARE), H(message_hash(hrr_ch) ‖ HRR ‖ CH2 ‖ SH))`;
    - then the client Finished → `Complete`.
  - **`ch2_rules`.** After `hrr_ch` → HRR, each CH2 below gives `Err(0x12f)` with `ev` unchanged:
    - two `(0x17, P256)` shares;
    - suites `[0x1302]` (drops 0x1301);
    - ALPN `[h3, h3-29]`;
    - random changed in byte 0;
    - shares still `[(0x1d, X25519)]`;
    - an empty share list;
    - TP changed.
  - **`ch_at_wrong_time`:** after `direct_p256`'s flight, `on_crypto(Initial, direct_ch)` → `Err(0x10a)`. After `Complete`, the same call → `Err(0x10a)`.
  - **`finished_checks`:**
    - one flipped byte → `Err(0x133)`;
    - a 31-byte body (`14 00 00 1f ‖ ..`) → `Err(0x132)`;
    - a ServerHello-typed message (`0x02 …`) at Handshake → `Err(0x10a)`.
  - **`key_update`:**
    - in `WaitFinished`, `on_crypto(Handshake, [0x18, 0, 0, 1, 0])` → `Err(0x10a)`;
    - after `Complete`, `on_crypto(OneRtt, [0x18, 0, 0, 1, 0])` → `Err(0x10a)`;
    - `on_crypto(OneRtt, &[])` → `Ok`, with no events.
  - **`finished_coalesced`:**
    - (a) `on_crypto(Handshake, fin ‖ [0x14])` → `Ok`, `ev == [Complete]`, `pending(Handshake)` true;
    - (b) on a fresh run, `Complete` first, then `on_crypto(Handshake, [0x14])` → `Err(0x10a)`.
  - **`leftover_initial`:** `on_crypto(Initial, direct_ch ‖ [0x01])` → `Ok` with the flight, and `pending(Initial)` true.
  - **`failed_absorbs`:** after `ch2_rules`' first failure, `on_crypto(Initial, valid CH2)` → `Err(0x12f)`, `ev` unchanged, and `is_complete()` false.
  - **`doomed_ch1`.** Each of these fails on CH1, with no HRR emitted:
    - an RSA-only config with a `hrr_ch` whose sig_algs are `[0x0403]` → `Err(0x128)`;
    - `hrr_ch` with ALPN `[b"h3-29"]` → `Err(0x178)`;
    - `hrr_ch` with suites `[0x1302]` → `Err(0x128)`;
    - `h3_ch([(0x17, P256)])` with groups `[0x1d]` → `Err(0x128)`.
  - **`reader_bound`:**
    - `on_crypto(Initial, [1, 0x01, 0x00, 0x01])` → `Err(0x0d)`, with nothing buffered past the header;
    - in `WaitFinished`, `on_crypto(Initial, [0x01])` → `Err(0x10a)`, with `pending(Initial)` unchanged.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3: Implement.**
  - `on_crypto` follows `spec_on_crypto` literally. The drain loop's `decreases` is the phase rank.
  - The HRR path stores `ch1` and replaces `transcript` with `message_hash(m) ‖ hrr`.
  - `Failed` zeroes `client_vd` and clears `transcript` and `ch1`.
  - **TRUSTED.md, one new row:**
    - Item: "Finished `verify_data` comparison (`tls::server::ct_eq32`): constant-time style (xor-accumulate over all 32 bytes, no early exit), proven equal to `==`; the timing itself is unverified";
    - File: `crates/tls/src/server.rs`;
    - Why trusted: "Verus cannot express timing (design non-goal)";
    - Removed in phase: "never (known gap)".
  - Duvet-cite:
    - **§4:** the unexpected_message sentence, at `spec_expected`;
    - **§4.1.2:**
      - "the client MUST send the same ClientHello without modification, except as follows", at `spec_same_except_shares`;
      - "receives a ClientHello at any other time, it MUST terminate the connection with an "unexpected_message" alert";
    - **§4.1.4:**
      - "Servers MUST ensure that they negotiate the same cipher suite when receiving a conformant updated ClientHello" (one suite, unchanged list);
      - the client-side "second HelloRetryRequest … unexpected_message" sentence, with the note "server side: never sends a second HRR (`theorem_no_second_hrr`); a CH2 that would need one is illegal_parameter";
    - **§4.2:** "Implementations MUST NOT send extension responses if the remote endpoint did not send the corresponding extension requests, with the exception of the "cookie" extension in the HelloRetryRequest.", at `theorem_no_unsolicited`'s use;
    - **§4.4.4:** "Recipients of Finished messages MUST verify that the contents are correct and if incorrect MUST terminate the connection with a "decrypt_error" alert.";
    - **§4.6.3:** the KeyUpdate-before-Finished sentence. Its other MUSTs (SHALL/MUST update keys, encrypt with old keys) get a "vacuous: TLS KeyUpdate is replaced by QUIC key update (RFC 9001 §6); any KeyUpdate is unexpected_message" note;
    - **§4.6.1** (a MAY, cited for the record): no NewSessionTicket is sent (PSK/resumption declined);
    - **Appendix E** (`#appendix-E.5`): "TLS implementations MUST provide a way for the application to determine if the handshake has completed.", at `is_complete`; and "TLS implementations MUST NOT enable 0-RTT (either sending or accepting) unless specifically requested by the application …";
    - **RFC 9001 §6:** "Endpoints MUST NOT send a TLS KeyUpdate message" and "Endpoints MUST treat the receipt of a TLS KeyUpdate message as a connection error of type 0x010a";
    - **RFC 9114 §7.2.4.2:** the 0-RTT sentence. There is no 0-RTT level, and no early secret is ever expanded.
- [ ] **Step 4:** Run the four checks and the fresh verify, then delete the target directory.
- [ ] **Step 5: Commit:** `feat(tls): verified ServerHandshake state machine with HRR, Finished check and per-level draining (RFC 8446 §4, §4.1.2, §4.1.4, §4.4.4, §4.6.3; RFC 9001 §6)`
- [ ] **Step 6: Matrix commit.**
  - `✅ 4b: crates/tls/src/server.rs` on:
    - RFC 8446 §4, §4.1.2, §4.1.4, §4.2 and §4.4.4;
    - §4.6.3 (note "replaced by QUIC key update; receipt is 0x10a") and its (req) row;
    - Appendix E;
    - RFC 9001 §6;
    - RFC 9114 §7.2.4.2 (req).
  - These replace 4a's touched notes on §4, §4.1.2, §4.1.4, §4.2 and §4.4.4, so every row ends with a single closing note.
  - Add the five "Rows touched" notes.

---

### Task 7: In-memory handshake against rustls — suggested model: sonnet

**Files:**
- Create: `crates/tls/tests/rustls_e2e.rs`
- Modify: `crates/tls/Cargo.toml` (rustls dev-dependency), `Cargo.lock`, `docs/requirements.md` (row check only)

**Interfaces:**
- Consumes:
  - Task 6's `ServerHandshake::{new, on_crypto, pending, is_complete}`;
  - `TlsEvent`, `Level`, `build_config`;
  - Task 4's fixtures (`ECDSA_CERT`, `ECDSA_D`, `RSA_CERT`, `rsa_key()`).
- Produces: nothing for later tasks. It is the first independent check of the handshake.

- [ ] **Step 1: Harness** (in the test file):
  - **`struct Log(Mutex<Vec<(String, Vec<u8>)>>)`**, implementing `rustls::KeyLog`.
  - **`struct Verifier { schemes: Vec<SignatureScheme>, algs: WebPkiSupportedAlgorithms }`**, implementing `rustls::client::danger::ServerCertVerifier`:
    - `verify_server_cert` → `Ok(ServerCertVerified::assertion())`. That is test-only: there is no path validation, and the chain is opaque DER;
    - `verify_tls13_signature` → `rustls::crypto::verify_tls13_signature(msg, cert, dss, &self.algs)`. This **really checks our CertificateVerify** with ring;
    - `verify_tls12_signature` → `Err`;
    - `supported_verify_schemes` → `self.schemes`.
  - **`fn client(kx, suites, alpn: Vec<Vec<u8>>, schemes) -> (rustls::quic::ClientConnection, Arc<Log>)`:**
    - provider = `rustls::crypto::ring::default_provider()` with `kx_groups`/`cipher_suites` overridden;
    - TLS 1.3 only, `.dangerous().with_custom_certificate_verifier(..)`, `.with_no_client_auth()`;
    - `key_log` = the `Log`, and `alpn_protocols` = `alpn`;
    - `ClientConnection::new(cfg, Version::V1, "localhost".try_into(), CLIENT_TP)`, where `CLIENT_TP` is A.2's 50-byte TP.
  - **`enum Fail { Server(u64), Client(rustls::Error) }`**.
  - **`fn run(c, hs, tamper: Option<fn(Level, &mut Vec<u8>)>) -> Result<Vec<Vec<TlsEvent>>, Fail>`.** It loops at most 10 times:
    - `c.write_hs(&mut buf)`. The bytes before a `KeyChange` are at the client's current write level (Initial → Handshake on `KeyChange::Handshake` → OneRtt on `KeyChange::OneRtt`);
    - non-empty `buf` → apply `tamper(level, &mut buf)` if given, then `hs.on_crypto(level, &buf, &RAND, &mut ev)`. `Err(e)` → `Fail::Server(e)`;
    - every `Send { data, .. }` → `c.read_hs(&data)`. `Err(e)` → `Fail::Client(e)`;
    - it stops when `!c.is_handshaking() && hs.is_complete()`;
    - it returns the events of each call.
- [ ] **Step 2: Failing tests:**
  - **`rustls_hrr_ecdsa`.** Use kx `[X25519, SECP256R1]` (rustls shares X25519 only, so the server must HRR), the default suites, ALPN `[b"h3"]`, schemes `[ECDSA_NISTP256_SHA256]`, and an ECDSA config. Then:
    - the first call's events == `[Send { Initial, HRR }]`, and exactly two `Send { Initial }` occur overall;
    - the handshake completes, with `c.alpn_protocol() == Some(b"h3")` and `c.quic_transport_parameters() == Some(LOCAL_TP)`;
    - the server's `PeerParams == CLIENT_TP`;
    - the key log's `CLIENT_HANDSHAKE_TRAFFIC_SECRET` / `SERVER_HANDSHAKE_TRAFFIC_SECRET` equal `Secrets { Handshake }`, and `CLIENT_TRAFFIC_SECRET_0` / `SERVER_TRAFFIC_SECRET_0` equal `Secrets { OneRtt }`.
  - **`rustls_direct_rsa`:** kx `[SECP256R1]`, schemes `[RSA_PSS_SHA256]`, an RSA config. There is exactly one `Send { Initial }` (no HRR), the handshake completes, and the secrets match the key log.
  - **`rustls_two_chains`:** config `[ecdsa, rsa]`.
    - Schemes `[RSA_PSS_SHA256]` → the CV in the `Send { Handshake }` data carries `0804`. Locate it by walking the message headers;
    - schemes `[ECDSA_NISTP256_SHA256]` → `0403`.

    Both complete.
  - **`rustls_doomed`:** each fails on the first call, with no events:
    - ALPN `[b"h3-29"]` → `Fail::Server(0x178)`;
    - suites `[TLS13_AES_256_GCM_SHA384]` → `Fail::Server(0x128)`;
    - an RSA-only config with schemes `[ECDSA_NISTP256_SHA256]` → `Fail::Server(0x128)`.
  - **`rustls_tampered_finished`:** a `tamper` that flips the last byte at `Level::Handshake` → `Fail::Server(0x133)`.
  - **`verifier_is_live`:** an ECDSA config whose key is `[0x42; 32]`, not the certificate's key, → `Fail::Client(_)` from `read_hs` of the server flight. This shows the verifier checks signatures.
- [ ] **Step 3:** Run the tests and confirm the failures are real. Every test must fail before the dependency is wired, not just fail to compile.
- [ ] **Step 4: Make it pass.** If a test fails on behaviour rather than on the harness, the bug is in Tasks 1–6. Fix it there, with a new failing unit test in that task's test file first.
- [ ] **Step 5:** Run the four checks.
- [ ] **Step 6: Row check.**
  - Regenerate `p4rows.txt` with the outline's `awk` extraction.
  - `python3 -I <scratch>/chk4/rows4.py <that file>` prints `75 3e 0 4a 17 4b 28 4c 30` (or `77 3e 2 …` if 3e has not merged).
  - `grep -c '✅ 4b:' docs/requirements.md` prints `28`.
- [ ] **Step 7: Commit:** `test(tls): in-memory TLS 1.3 handshake against rustls 0.23.45 (HRR, ECDSA, RSA-PSS, failures)`

---

## Exit criteria (Phase 4b)

- All four checks pass on the merged tree.
- The 28 rows carry `✅ 4b: <file>`, the five touched rows carry their notes, and the row check passes.
- `cargo test -p tls` passes, including `rustls_e2e`.
- TRUSTED.md has the two new rows (config key half, constant-time compare) and the test-only pin line.
- `phase-4b` is merged into `main`.

## Binding notes for 4c

- **Construction.**
  - The shell builds `ServerConfig` with `build_config(chains)`, which checks chain sizes. That needs the TRUSTED key half (`rsa_key_wf`, the scalar range, chain metadata) and `chain_schemes` (empty for self-signed leaves).
  - The shell gets a `&'static ServerConfig` (for example `Box::leak`) and creates one `ServerHandshake::new(cfg, local_tp)` per connection.
  - `local_tp` must be ≤ 1024 bytes (3b's server TPs are < 256).
- **Per packet:** for each level with new data, `crypto_read(level)` → `on_crypto(level, data, tls_rand, &mut ev)`. Then handle `ev` in order:
  - `PeerParams(b)` → `quic::tp::parse_transport_params(b, true)` (TRANSPORT_PARAMETER_ERROR), then `on_peer_params`;
  - `Send { level, data }` → `crypto_write(level, data)`. `level` is never `OneRtt`;
  - `Secrets { level, .. }` → `PacketKeys` via `hkdf_expand_label(secret, b"quic key" / b"quic iv" / b"quic hp", &[], 16 / 12 / 16)`;
  - `Complete` → `on_handshake_complete(b"h3", ..)`. ALPN was enforced at ClientHello time, so 3d's `check_alpn` always passes.
  - **Then, after each call's events:** if `pending(L)` holds for any L below the current receive level, close with PROTOCOL_VIOLATION (RFC 9001 §4.1.3, RFC 8446 §5.1 (req)).
    - Initial is below the receive level after `Secrets { Handshake }`; Handshake is below it after `Complete`.
    - `Secrets { OneRtt }` arrives with the server flight, when nothing is pending yet. So a coalesced client Finished with trailing bytes is caught only by this after-`Complete` check.
- **Interop:** curl's real CH2 must pass `spec_same_except_shares`, which compares GREASE-bearing lists and TPs. 4c's first-fetch interop (curl takes the HRR path) is the test. A false positive there breaks the Phase 4 exit, so capture CH2 with `<scratch>/chk4/cap.py` if it fails.
- **Errors.** `Err(code)` with `0x100 ≤ code ≤ 0x1ff` → `on_tls_alert((code - 0x100) as u8)`. Otherwise → `close(code)` (0x0a, 0x0d).
- **HsReader bound** (M7): already enforced inside `on_crypto` (`theorem_reader_bound`). 4c only needs each `crypto_read` chunk bounded, which it is by 3c's receive buffer.
- **A.2:** its unmodified ClientHello fails at 4b's ALPN check (`0x178`) before any `PeerParams`, so 3d #16's iscid mismatch is not reached. A 4c test that patches A.2's ALPN to `h3` must expect TRANSPORT_PARAMETER_ERROR (iscid mismatch).
- **Level mapping:** `tls::flight::Level` → 3d's `PacketKind` (Initial, Handshake, OneRtt). 4c's `tls::codes` = `quic::codes` test also covers the four new alerts.

## Self-review (done while writing)

- **Spec coverage:**
  - the state machine CH → [HRR] → SH/EE/Cert/CV/Fin (Tasks 5–6);
  - ALPN `h3` with no_application_protocol (Task 3);
  - the key schedule as spec (Tasks 1–2);
  - the outline's proof obligations:
    - Send equals the spec flight: `on_crypto`'s ensures and `spec_flight`;
    - secrets equal the spec schedule over the exact transcript: `spec_flight` over `t1`/`t4`;
    - Complete iff the Finished matched: `theorem_complete_iff_finished`;
    - no Send after Failed: `theorem_failed_absorbing`.
- **The brief's easy-to-miss MUSTs:**
  - the HRR transcript `message_hash`: `spec_message_hash`, `rfc8448_s5_hrr`, `hrr_then_ch2`;
  - CH2 = CH1 except the shares: `spec_same_except_shares`, `ch2_rules`;
  - no second HRR: `theorem_no_second_hrr`;
  - a CH2 share for the selected group: `rfc_negotiate` step 4 after HRR;
  - the CV context and 64 × 0x20: `cv_content_rfc8446_example`, `wrong_context_fails`;
  - the SH random from the RNG: `random_from_rand`, `theorem_flight_order`;
  - the downgrade sentinel: vacuous, cited in Task 5;
  - the HMAC Finished with a constant-time-style compare: `spec_verify_data`, `ct_eq32`, the TRUSTED row;
  - nothing after the client Finished: `spec_expected(Complete) == None`, `key_update`, `finished_coalesced`;
  - no NewSessionTicket: the §4.6.1 MAY is cited;
  - alerts → CRYPTO_ERROR: the codes, plus the RFC 9001 §4.8 touched note;
  - the handshake secret before EE: `theorem_event_discipline`.
- **Type consistency.** These names are used identically everywhere:
  - `spec_hkdf_expand_label`/`hkdf_expand_label`/`derive_secret` (1 → 2, 4c);
  - `spec_message_hash`/`handshake_secrets`/`master_secret`/`app_secrets`/`verify_data` (2 → 5, 6, 7);
  - `ServerConfig`/`CertChain`/`SigningKey`/`key_wf`/`key_scheme`/`build_config` (3 → 4–7);
  - `Choice`/`rfc_negotiate` (3 → 6);
  - `spec_cv_signature`/`sign_cv` (4 → 5);
  - `Level`/`TlsEvent`/`spec_flight`/`build_flight` (5 → 6, 7);
  - `ServerHandshake`/`on_crypto`/`pending`/`is_complete` (6 → 7, 4c).
  - 4a names are copied from the code: `cert_chain_ok`, `spec_reserved_group`/`scheme`, `rfc_finished`, `spec_server_hello_bytes`, and so on.
- **Arithmetic re-checked by script** (`<scratch>/plan4b/sched.py`, 2026-10-28):
  - every RFC 8448 §3/§5 value in Tasks 1–2;
  - `H(CH1)` for `message_hash`;
  - the R5 SH = `sh(rand[0..32], [], 0x17, pubkey(8c51…))`;
  - CV content = 130 bytes;
  - CV body for RSA-2048 = 2 + 2 + 256 = 0x104.
- **Rows:** 1 + 9 + 2 + 6 + 10 = 28, each named in exactly one task. `rows4.py`'s `b4` bucket lists the same 28.
- **Proportion.** Bodies appear only where the order is the requirement: `rfc_negotiate`, `spec_flight`, `spec_step` and `spec_on_crypto`. Everything else is signatures, vectors and citations.

## Open decisions (each needs a controller ruling; recommendation given)

1. **The config is held by reference.**
   - `ServerHandshake<'a> { cfg: &'a ServerConfig, .. }`, with `new(cfg, local_tp)` requiring `cfg.wf()` (I2, literally) and `local_tp ≤ 1024` (M1, pushed to 4c).
   - If Verus rejects the lifetime-parameterized struct, the fallback is `cfg` passed per `on_crypto` call with the same `requires`. The task report must name the blocker.

   *Recommend: accept.*
2. **`build_config` is the only way to get a `wf` config.** It runs `cert_chain_fits` per chain and rejects an empty list. Key well-formedness stays a `requires` that the trusted PKCS#8 loader establishes (the TRUSTED row). *Recommend: accept.*
3. **`CertChain.chain_schemes` is trusted metadata** for §4.4.2.2's "signed by an algorithm the client advertised, if able" preference and its SHA-1 fallback ban.
   - It is empty for self-signed leaves.
   - The alternative is selection by key type only, with the MUST pushed entirely into TRUSTED.md.

   *Recommend: accept, because it keeps the MUST in verified code.*
4. **The CH2 consistency check compares typed fields only.** Every field except `key_shares` is compared; a mismatch is illegal_parameter. Changes to unrecognized extensions go undetected: `// ponytail: typed fields only; raw extension-list diff if a client is caught changing unknown extensions`. *Recommend: accept.*
5. **Events per call.**
   - The order is PeerParams, SH, Secrets(Handshake), EE‖Cert‖CV‖Fin, Secrets(OneRtt), then later Complete.
   - A call that fails appends no events. `Failed` is absorbing and returns its first error.

   *Recommend: accept.*
6. **The level rule.**
   - Bytes at a level with no expected message are unexpected_message, before any buffering.
   - Bytes left over in the same chunk after a level is finished stay `pending()` for 4c's RFC 9001 §4.1.3 PROTOCOL_VIOLATION.

   Both close the connection. *Recommend: accept.*
7. **ECDHE failures.** An invalid, compressed or all-zero peer share, or an all-zero shared secret, is illegal_parameter (§4.2.8.2 and §7.4.2, which name no alert). An invalid server scalar is internal_error (≈ 2⁻³²). *Recommend: accept.*
8. **Signature length uses a runtime `≤ 0xffff` check** for both ECDSA and RSA, mirrored in `spec_cv_signature`, instead of length lemmas over `der_uint_content`/`i2osp`. *Recommend: accept, as a `ponytail:` note.*
9. **The client `verify_data` is precomputed when the flight is built.** The transcript and handshake secrets are not kept after the flight. The comparison is xor-accumulate constant-time style, with its timing recorded as a TRUSTED.md known gap. *Recommend: accept.*
10. **No NewSessionTicket and no post-handshake messages.** §4.6.1 makes the ticket a MAY, PSK/resumption is a non-goal, and RFC 9001 §4.4 forbids post-handshake CertificateRequest. Any byte after `Complete` is unexpected_message. *Recommend: accept.*
11. **A CH1 with several secp256r1 shares uses the first.** §4.2.8's "Servers MAY check" is not taken. CH2 must carry exactly one share. *Recommend: accept.*
12. **Test-only rustls verification.**
    - A danger verifier skips path validation but runs `verify_tls13_signature`, and `verifier_is_live` proves it checks.
    - The fixtures are self-signed P-256 and RSA-2048 leaves made by openssl 3.5.9, committed as DER plus raw key bytes.

    *Recommend: accept.*
13. **Task 1 is tagged sonnet** (the outline said opus). Its proof is a composition of `put_u16`/`put_vec` ensures. *Recommend: accept.*

## Controller rulings (2026-10-28)

All 13 open decisions are accepted as recommended.
- **#4 and #11:** RFC 8446 makes server-side detection of these client violations a MAY (§4.1.2, §4.2.8), so the lenient choices conform.
- **#4, CH2 check:** compare only the typed fields that must stay unchanged. If curl, Chrome or Firefox interop in 4c shows a false rejection, relax the check there rather than here.

4b branches from main after phase-4a merges.
