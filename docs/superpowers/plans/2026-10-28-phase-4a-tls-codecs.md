# Phase 4a: TLS 1.3 Message Codecs and ClientHello Validation — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Verified, sans-IO codecs for every TLS 1.3 handshake message a QUIC server reads or writes, each proven against a literal transcription of RFC 8446:
- handshake-message framing across CRYPTO chunks;
- the extension block;
- the ten ClientHello extension grammars we recognize;
- a typed, fully validated `ClientHello` that raises every ClientHello-intrinsic alert in a fixed order;
- serializers for ServerHello, HelloRetryRequest, EncryptedExtensions, Certificate, CertificateVerify and Finished.

**Architecture:**
- **New crate `crates/tls`, depending on `vstd` only.** 4b adds `crypto`, and 4c adds `quic` for its glue module (outline, shared decisions).
- **Specs are hand-written over a small presentation-language module (`tls::pl`).** That module transcribes RFC 8446 §3.3–§3.4: network byte order, and `<floor..ceiling>` vectors whose length field is as wide as the ceiling needs. Every message grammar is built from it, so the inbound parser and the outbound serializers share one transcription of the length rules.
- **Parse only what a server receives** (ClientHello, Finished), **serialize only what it sends.**
- **Validation is ClientHello-intrinsic only:** syntax, extension-block rules, version, compression, session id, cookie, and missing extensions. Negotiation, which needs config and state, is 4b.
- **Results are `Result<_, u64>`, carrying QUIC error codes** (3b house style). A TLS alert *a* is `0x100 + a` (RFC 9001 §4.8).

**Tech Stack:** Verus 0.2026.10.04.426d8b0, vstd `=0.0.0-2026-10-04-0306`, duvet 0.4.3. No `vest_lib` (Decision 1).

**Spec:** `docs/superpowers/specs/2026-10-27-verified-http3-design.md`. See:
- Phase 4: "Extensions, by name: supported_versions, supported_groups, key_share, signature_algorithms; ALPN h3 …; quic_transport_parameters; no early_data";
- "Calls I made": server only; TLS_AES_128_GCM_SHA256 only; secp256r1 only, with HRR; ECDSA/RSA-PSS signing; the certificate chain sent as opaque DER;
- Non-goals: 0-RTT, resumption/PSK, client certificates;
- the codec proof obligations;
- the anti-goal: no "proven" claim for anything that isn't proven.

Also read:
- the outline `2026-10-28-phase-4-outlines.md`: its shared decisions, its easy-to-miss MUST table and its captured facts;
- `2026-10-27-phase-3b-quic-codecs.md` (Global Constraints, house style);
- RFC 8446 §3, §4, §4.1.2–§4.1.4, §4.2–§4.2.11, §4.3.1, §4.4.2–§4.4.4, §6, §9.2–§9.3 and Appendix D (`.duvet/specifications/www.rfc-editor.org/rfc/rfc8446.txt`);
- RFC 9001 §4.2, §4.4, §8.2 and §8.4;
- RFC 8448 (`<scratch>/rfc4/rfc8448.txt`), which is the vector source.

## Global Constraints

- **3b's Global Constraints apply unchanged except where this list says otherwise.** That covers:
  - the pins;
  - Duvet citations: `//= https://www.rfc-editor.org/rfc/rfc8446#section-X` or `…/rfc9001#section-X`, plus a contiguous `//#` quote copied exactly from the `.duvet/specifications` text.
    - Appendices use `#appendix-B`, `#appendix-D.2` and `#appendix-D.5`, the names under `.duvet/requirements/www.rfc-editor.org/rfc/rfc8446/`.
    - RFC 8446 §3.x has no requirement entries, so cite it in plain `//` comments, like RFC 7301 and RFC 6066;
  - sans-IO, with no async, trait objects or closures in exec code (test code may use closures);
  - no panics;
  - no allocation sized by an untrusted length before it is checked against the bytes present;
  - glob-only imports of spec items (`use crate::pl::*;`);
  - `Spec*` twins with a `View` for every type with `Vec` or array fields;
  - zero escape tokens in `crates/tls`, and `scripts/verify.sh` unedited;
  - matrix bookkeeping, written here as `✅ 4a: <file>`.
- **The four checks, every task:**
  - `scripts/verify.sh` reports 0 errors and prints its summary line;
  - `cargo build && cargo test` pass with 0 warnings;
  - the escape grep `grep -rnE 'admit\(|assume\(|external_body|assume_specification|verifier::external|axiom fn' crates --include='*.rs'` prints nothing under `crates/tls`;
  - `duvet report` exits 0.
- **Fresh evidence:** `(cd crates/tls && CARGO_TARGET_DIR=<scratch>/vt-4a-tN cargo verus verify)` prints `verification results:: … 0 errors`.
- **`crates/tls/Cargo.toml`:**
  ```toml
  [package]
  name = "tls"
  version = "0.1.0"
  edition = "2021"

  [dependencies]
  vstd = "=0.0.0-2026-10-04-0306"

  [package.metadata.verus]
  verify = true

  [lints.rust]
  unexpected_cfgs = { level = "warn", check-cfg = ['cfg(verus_only)'] }
  ```
  No task adds a dependency.
- **Base branch:** `phase-4a` branches from `main` at any point. It has no code dependency on 3b–3e. If 3a has merged, `verify.sh`'s per-hit escape accounting applies, and `crates/tls` contributes no hits.
- **Naming** (the carry-over item "convention isn't written down", settled here for `tls`):
  - `rfc_*`: transcribed parse specs;
  - `spec_*_bytes`: serialization specs;
  - `theorem_*`: public round-trip or canonicity results;
  - `lemma_*`: helpers;
  - `Spec<Type>`: spec twins.
- **Proven, per codec** (Decision 2):
  - exec ≡ spec, always;
  - canonicity, `rfc_x(b) == Some(v) ⇒ spec_x_bytes(v) == b`, for `pl` vectors and u16 lists, the handshake header, the extension list, and the ClientHello field layer;
  - every serializer ensures `out@ == old(out)@ + spec_*_bytes(..)`.
  - No client-side parser and no exec ClientHello serializer exist.
- **Codepoints, in `tls::codes`** (`pub const`, with the RFC 8446 name in a comment). Only these, because later sub-phases add their own:
  - **Handshake types (`u8`):** `HT_CLIENT_HELLO 1`, `HT_SERVER_HELLO 2`, `HT_ENCRYPTED_EXTENSIONS 8`, `HT_CERTIFICATE 11`, `HT_CERTIFICATE_VERIFY 15`, `HT_FINISHED 20`.
  - **Versions (`u16`):** `LEGACY_VERSION 0x0303`, `TLS13 0x0304`, `SSL30 0x0300`.
  - **Cipher suite (`u16`):** `TLS_AES_128_GCM_SHA256 0x1301`.
  - **Extension types (`u16`):**
    - `EXT_SERVER_NAME 0`, `EXT_SUPPORTED_GROUPS 10`, `EXT_SIGNATURE_ALGORITHMS 13`, `EXT_ALPN 16`;
    - `EXT_PRE_SHARED_KEY 41`, `EXT_EARLY_DATA 42`, `EXT_SUPPORTED_VERSIONS 43`, `EXT_COOKIE 44`, `EXT_PSK_KEY_EXCHANGE_MODES 45`;
    - `EXT_OID_FILTERS 48`, `EXT_SIGNATURE_ALGORITHMS_CERT 50`, `EXT_KEY_SHARE 51`, `EXT_QUIC_TRANSPORT_PARAMETERS 0x39`.
  - **`HRR_RANDOM: [u8; 32]`** = `cf21ad74e59a6111be1d8c021e65b891c2a211167abb8c5e079e09e2c8a8339c` (§4.1.3).
  - **`H3_ALPN: [u8; 2] = *b"h3"`.**
  - **Error codes (`u64`):**
    - `CRYPTO_ERROR_BASE 0x100`, `PROTOCOL_VIOLATION 0x0a`, `CRYPTO_BUFFER_EXCEEDED 0x0d`. These are RFC 9000 §20.1 values; 4c tests them against `quic::codes`.
    - `ALERT_UNEXPECTED_MESSAGE 0x10a`, `ALERT_ILLEGAL_PARAMETER 0x12f`, `ALERT_DECODE_ERROR 0x132`, `ALERT_PROTOCOL_VERSION 0x146`, `ALERT_MISSING_EXTENSION 0x16d`. Each is `CRYPTO_ERROR_BASE` + its §6 AlertDescription: 10, 47, 50, 70, 109.
  - **`MAX_HS_BODY: usize = 1 << 16`.** `// ponytail: largest legal ClientHello is ~131 KiB; every observed client is < 2 KiB (curl 1532 B with an ML-KEM share); raise if a client needs more.`
- **Shared test data, `crates/tls/tests/common/mod.rs`, loaded with `mod common;`.**
  - **Copy every vector by script, never by hand.** `<scratch>/chk4/v8448.py` and `<scratch>/chk4/parse.py` extract them.
    - Check each one's sha256 prefix in that same `python3 -I` step, using hashlib, before pasting it in. `tls` has no SHA-256 dependency, and none is added.
    - In Rust, `#[test] fn vectors_intact` asserts only the lengths.
  - **Helpers:**
    - `hex(&str) -> Vec<u8>`;
    - `split_ch(msg: &[u8]) -> (Vec<u8>, Vec<(u16, Vec<u8>)>)` returns the bytes between the handshake header and the extension block, plus the extensions;
    - `join_ch(head: &[u8], exts: &[(u16, Vec<u8>)]) -> Vec<u8>` rebuilds a full message, including the header and both length fields;
    - `head(version: u16, session_id: &[u8], suites: &[u16], comp: &[u8]) -> Vec<u8>` uses A.2's random.
  - **Vectors** (name, length, first 16 hex digits of sha256):

    | Name | Bytes | sha256 prefix | Source |
    |---|---|---|---|
    | `A2_CH` | 241 | `72067e70ea2e42b8` | the RFC 9001 A.2 CRYPTO data after `060040f1` |
    | `A3_SH` | 90 | `27fcb1c6f0a24ed7` | the RFC 9001 A.3 payload after `02000000000600405a` |
    | `R3_CH` | 196 | `4db255f30da09a40` | RFC 8448 §3 ClientHello |
    | `R3_SH` | 90 | `ed88d69f6adbcad6` | RFC 8448 §3 ServerHello |
    | `R4_CH` | 512 | `08ad0fa05d7c7233` | RFC 8448 §4 ClientHello, the full 512-byte "payload" (rfc8448.txt:972), not the 477-byte binder-hash prefix: pre_shared_key last, early_data |
    | `R5_CH1` | 180 | `de7420cc7426d2f6` | RFC 8448 §5 first ClientHello: X25519-only share |
    | `R5_CH2` | 512 | `5c2fe8a843fd18e4` | RFC 8448 §5 second ClientHello: P-256 share, **cookie** |
    | `R5_SH` | 123 | `11b2f096784fb1de` | RFC 8448 §5 ServerHello (P-256) |
    | `R5_CERT` | 445 | `bf4c94104efe86a6` | RFC 8448 §5 Certificate |
    | `R5_CV` | 136 | `2b9773310bdbc6f4` | RFC 8448 §5 CertificateVerify (0x0804) |
    | `R5_SFIN` | 36 | `bfee1ab25f3a44ee` | RFC 8448 §5 server Finished |
    | `CURL_CH` | 1532 | full `78670831801f554919d42170b2a425c01e609af4b7115771c64998ba0965a581` | `include_bytes!("../data/curl-8.18-openssl-3.5.9-ch.bin")`. The path is relative to `tests/common/mod.rs`, and the file lives at `tests/data/`, copied from `<scratch>/chk4/`. Captured 2026-10-28 from curl 8.18.0 / ngtcp2 1.22.1 / OpenSSL 3.5.9 by `<scratch>/chk4/cap.py` (Decision 12) |

## Matrix rows this plan closes (17)

Labels are exactly as in `docs/requirements.md`. `python3 -I <scratch>/chk4/rows4.py <scratch>/chk4/p4rows.txt` prints `77 3e 2 4a 17 4b 28 4c 30` before 3e merges, and `75 3e 0 4a 17 4b 28 4c 30` once 3e Task 1 has retagged RFC 9001 §5.4.1 and §5.4.2 to Phase 3.

- **Task 5:**
  - RFC 8446 §4.2.11, §9.3;
  - RFC 8446 §9.2 (req) "MUST implement ... cookie".
- **Task 6:**
  - RFC 8446 §4.2.1, §4.2.2, §4.2.6, §4.2.9, §4.2.10, §4.5, §9.2, Appendix D;
  - RFC 9001 §4.2, §8.2.
- **Task 7:**
  - RFC 8446 Appendix B, §4.4.2.1;
  - RFC 8446 §4.4.2 (req) "RawPublicKey certificate type";
  - RFC 9001 §4.4.

**Rows touched but not closed.** Each task appends `4a codec: <file> (closed in 4x)` to Notes:

| Row | Task | 4a provides | Closed in |
|---|---|---|---|
| RFC 8446 §4 | 2 | first-byte type check, unexpected_message | 4b |
| RFC 8446 §5.1 (req) | 2 | `HsReader::is_empty` for the key-change boundary | 4c |
| RFC 8446 §4.2 | 3 | duplicates, pre_shared_key last, oid_filters in CH | 4b (no unsolicited responses) |
| RFC 8446 §4.2.8 | 4 | key_share grammar | 4b |
| RFC 8446 §4.1.2 | 5 | compression check, unknown suites kept | 4b |
| RFC 8446 §4.2.3 | 5 | missing signature_algorithms | 4b |
| RFC 8446 §6 | 5 | the decode_error / illegal_parameter split and fixed order | 4c |
| RFC 9001 §8.1 | 5 | ALPN grammar | 4b |
| RFC 8446 §4.1.3 | 6 | ServerHello layout (0x0303, compression 0, supported_versions, echo) | 4b |
| RFC 8446 §4.1.4 | 6 | HRR layout | 4b |
| RFC 8446 §4.3.1 | 6 | EncryptedExtensions layout | 4b |
| RFC 8446 §4.4.2, §4.4.3, §4.4.4 | 7 | message layouts | 4b |

RFC 9001 §8.4 is an N/A (client-only) row. Task 5 adds to its Notes: `server SHOULD taken: non-empty legacy_session_id → PROTOCOL_VIOLATION (crates/tls/src/client_hello.rs, 4a)`.

## Review Focus

1. **curl's real 1532-byte ClientHello, delivered in arbitrary chunks.** It spans two Initial datagrams, with CRYPTO frames out of order. The framer must report "incomplete" until byte 1532, and then exactly one message identical to the fixture, whatever the split. Pinned in Task 2: `curl_ch_any_chunking`.
2. **GREASE codepoints everywhere**, as Chrome sends them: in extension types, supported_versions, cipher suites, groups, signature schemes, a key share with a 1-byte key, and ALPN. Every one must be accepted and kept, never rejected. Pinned in Task 5: `grease_ignored`.
3. **A duplicate *unknown* extension type**, such as two `0xff01` or two GREASE `0x0a0a`. It is illegal_parameter even though we ignore the type, because §4.2 says "same type". Pinned in Task 3: `dup_unknown`, `dup_grease`.
4. **pre_shared_key present but not last**, for example RFC 8448 §4's resumption ClientHello with quic_transport_parameters appended. It is illegal_parameter, not missing_extension and not a silent ignore of the PSK. Pinned in Task 5: `rfc8448_s4_psk_not_last`.
5. **An extension block of 16,383 empty extensions** (65,532 bytes). It must be decided in linear time, with no allocation proportional to the extension count beyond the parsed list. All distinct gives `Ok`; a duplicate appended at the end gives illegal_parameter. Pinned in Task 3: `max_ext_count`.

---

### Task 1: `tls` crate, `codes`, presentation-language primitives (`tls::pl`) — suggested model: opus

**Files:**
- Create:
  - `crates/tls/Cargo.toml` (Global Constraints);
  - `crates/tls/src/lib.rs` (`pub mod codes; pub mod pl;`; later tasks append);
  - `crates/tls/src/codes.rs`, `crates/tls/src/pl.rs`;
  - `crates/tls/tests/pl.rs`;
  - `crates/tls/tests/common/mod.rs`, starting with `#![allow(dead_code)]`, because each test binary uses only part of it; without the attribute the 0-warnings check fails. `hex` and `vectors_intact` start here, and later tasks add vectors and helpers.
- Modify: `Cargo.lock` (new workspace member), `TRUSTED.md` (new row: "Derived `Debug`/`PartialEq`/`Eq` on tls types", which Tasks 3–5 extend; test support, never removed).

**Interfaces:**
- Consumes: nothing.
- Produces (`tls::pl`). RFC 8446 §3.3 network byte order, and §3.4 vectors. Every width is ≤ 3.
  - **`pub open spec fn len_width(ceiling: nat) -> nat`** = `if ceiling < 0x100 { 1 } else if ceiling < 0x1_0000 { 2 } else { 3 }`. §3.4: "consuming as many bytes as required to hold the vector's specified maximum (ceiling) length".
  - **`pub open spec fn be(b: Seq<u8>, w: nat) -> nat`**: the big-endian value of `b.take(w)`. **`pub open spec fn spec_be_bytes(x: nat, w: nat) -> Seq<u8>`**: its `w`-byte inverse.
  - **`pub open spec fn rfc_vec(b: Seq<u8>, floor: nat, ceiling: nat) -> Option<(Seq<u8>, Seq<u8>)>`** returns `(content, rest)`. With `w = len_width(ceiling)`:
    - it needs `b.len() >= w`;
    - `n = be(b, w)` must satisfy `floor <= n <= ceiling` and `w + n <= b.len()`;
    - the result is then `(b.subrange(w, w + n), b.skip(w + n))`.
  - **`pub open spec fn rfc_vec_exact(b, floor, ceiling) -> Option<Seq<u8>>`**: `rfc_vec` with an empty `rest`.
  - **`pub open spec fn spec_vec_bytes(ceiling: nat, c: Seq<u8>) -> Seq<u8>`** = `spec_be_bytes(c.len(), len_width(ceiling)) + c`.
  - **`pub open spec fn rfc_u16_list(b: Seq<u8>) -> Option<Seq<u16>>`**: `None` if `b.len()` is odd (§3.4: "an exact multiple of the length of a single element"), else the big-endian pairs. **`pub open spec fn spec_u16_list_bytes(s: Seq<u16>) -> Seq<u8>`**.
  - **Lemmas:**
    - **`lemma_vec_canonical`:** `rfc_vec(b, f, c) == Some((x, r)) ⇒ b == spec_vec_bytes(c, x) + r`;
    - **`lemma_vec_roundtrip`:** `f <= x.len() <= c < 0x100_0000 ⇒ rfc_vec(spec_vec_bytes(c, x) + r, f, c) == Some((x, r))`;
    - **`lemma_u16_list_canonical`** and **`lemma_u16_list_roundtrip`**, the same pair for u16 lists.
  - **Exec:**
    - **`pub fn read_vec(b: &[u8], pos: usize, floor: usize, ceiling: usize) -> (r: Option<(usize, usize)>)`**:
      - requires `pos <= b@.len()` and `ceiling < 0x100_0000`;
      - ensures `r is None ⇔ rfc_vec(b@.skip(pos), floor, ceiling) is None`, and `r == Some((s, e)) ⇒ rfc_vec(b@.skip(pos), floor, ceiling) == Some((b@.subrange(s, e), b@.skip(e)))`.
      - It works by index, with no copy.
    - `pub fn read_u16(b: &[u8], pos: usize) -> (r: Option<u16>)`;
    - `pub fn parse_u16_list(b: &[u8]) -> (r: Option<Vec<u16>>)` ensures `r.deep_view() == rfc_u16_list(b@)`;
    - `pub fn put_u16(out: &mut Vec<u8>, x: u16)` ensures `out@ == old(out)@ + spec_be_bytes(x as nat, 2)`;
    - `pub fn put_vec(out: &mut Vec<u8>, ceiling: usize, c: &[u8])` requires `c@.len() <= ceiling < 0x100_0000`, and ensures `out@ == old(out)@ + spec_vec_bytes(ceiling as nat, c@)`.
  - Serializers build nested bodies in a local `Vec` and then `put_vec` it. That costs one copy, sized by our own output.
- Produces (`tls::codes`): every constant listed in Global Constraints.

- [ ] **Step 1: Failing tests** (`tests/pl.rs`):
  - **`vec_widths`:**
    - `read_vec(&[0x02, 0xaa, 0xbb, 0xcc], 0, 0, 255) == Some((1, 3))`;
    - `read_vec(&[0x00, 0x02, 0xaa, 0xbb], 0, 0, 0xffff) == Some((2, 4))`;
    - `read_vec(&[0, 0, 1, 0xaa], 0, 1, 0xff_ffff) == Some((3, 4))`.
  - **`vec_bounds`.** Each of these is `None`:
    - `read_vec(&[0x00], 0, 1, 255)` (below floor);
    - `read_vec(&[0x03, 1, 2, 3], 0, 0, 2)` (above ceiling);
    - `read_vec(&[0x05, 1, 2], 0, 0, 255)` (overrun);
    - `read_vec(&[], 0, 0, 255)`;
    - `read_vec(&[0x00], 0, 0, 0xffff)` (a 2-byte length with only 1 byte present).
  - **`vec_offset`:** `read_vec(&[9, 9, 0x01, 0x7f], 2, 1, 255) == Some((3, 4))`.
  - **`u16_list`:**
    - `parse_u16_list(&[0x13, 0x01, 0x13, 0x02]) == Some(vec![0x1301, 0x1302])`;
    - `&[0x13]` → `None`;
    - `&[]` → `Some(vec![])`.
  - **`put_vec_widths`.** Start with `out = [0xaa]`:
    - `put_vec(&mut out, 255, b"h3")` gives `[0xaa, 2, 0x68, 0x33]`;
    - ceiling `0xffff` gives `[0xaa, 0, 2, 0x68, 0x33]`;
    - ceiling `0xff_ffff` gives `[0xaa, 0, 0, 2, 0x68, 0x33]`.
  - **`alert_sums`:** each `ALERT_*` equals `CRYPTO_ERROR_BASE` + {10, 47, 50, 70, 109}.
- [ ] **Step 2:** Run `cargo test -p tls --test pl` and confirm it fails to compile.
- [ ] **Step 3: Implement.**
  - Plain-comment-cite RFC 8446 §3.4 at `len_width` and `rfc_vec` ("The length will be in the form of a number consuming as many bytes as required to hold the vector's specified maximum (ceiling) length."), and §3.3's network byte order at `be`. §3 has no Duvet requirement entries.
  - `be` and `spec_be_bytes` use arithmetic (`b[0] * 65536 + …`), not shifts. That keeps the lemmas linear over constants.
- [ ] **Step 4:** Run the four checks and the fresh verify.
- [ ] **Step 5: Commit:** `feat(tls): crate, codepoints, verified RFC 8446 §3 presentation-language primitives with canonicity`
- [ ] **Step 6:** No matrix commit.

---

### Task 2: Handshake message framing (`tls::handshake`) — suggested model: opus

**Files:**
- Create: `crates/tls/src/handshake.rs`, `crates/tls/tests/handshake.rs`, `crates/tls/tests/data/curl-8.18-openssl-3.5.9-ch.bin` (copied from `<scratch>/chk4/`)
- Modify: `crates/tls/src/lib.rs`, `crates/tls/tests/common/mod.rs` (add `A2_CH`, `CURL_CH`), `docs/requirements.md`

**Interfaces:**
- Consumes: `be`, `spec_vec_bytes`, `HT_*`, `MAX_HS_BODY`, `ALERT_UNEXPECTED_MESSAGE`, `CRYPTO_BUFFER_EXCEEDED`.
- Produces (`tls::handshake`):
  - **`pub open spec fn spec_hs_bytes(ty: u8, body: Seq<u8>) -> Seq<u8>`** = `seq![ty] + spec_vec_bytes(0xff_ffff, body)`. This is §4 `Handshake`: `msg_type`, then `uint24 length`, then the body.
  - **`pub open spec fn rfc_next_message(buf: Seq<u8>, expect: u8) -> Result<Option<nat>, u64>`** returns the length of the first complete message:
    - `buf.len() == 0` → `Ok(None)`;
    - `buf[0] != expect` → `Err(ALERT_UNEXPECTED_MESSAGE)`. The type is known at the first byte (§4: "unexpected order MUST abort … unexpected_message"), so nothing is buffered for a message we will refuse (Decision 4);
    - `buf.len() < 4` → `Ok(None)`;
    - `be(buf.subrange(1, 4), 3) > MAX_HS_BODY` → `Err(CRYPTO_BUFFER_EXCEEDED)` (Decision 3);
    - `buf.len() < 4 + len` → `Ok(None)`;
    - otherwise `Ok(Some(4 + len))`.
  - **`pub struct HsReader { buf: Vec<u8> }`**, whose View is `Seq<u8>`.
    - `pub fn new() -> (r: HsReader)` ensures `r@ == Seq::empty()`;
    - `pub fn push(&mut self, data: &[u8])` ensures `self@ == old(self)@ + data@`;
    - `pub fn is_empty(&self) -> (r: bool)` ensures `r == (self@.len() == 0)`.
  - **`pub fn next_message(&mut self, expect: u8) -> (r: Result<Option<Vec<u8>>, u64>)`.** It ensures, against `rfc_next_message(old(self)@, expect)`:
    - `Ok(Some(n))` ⇒ `r == Ok(Some(m))`, with `m@ == old(self)@.take(n)` and `self@ == old(self)@.skip(n)`;
    - `Ok(None)` ⇒ `r == Ok(None)`, and `self` is unchanged;
    - `Err(e)` ⇒ `r == Err(e)`, and `self` is unchanged.
    - The returned message includes its 4-byte header, which is what 4b's transcript hashes (§4.4.1).
    - `// ponytail: drains from the front of a Vec (O(n) per message); a ring buffer if handshakes grow.`
  - **`theorem_next_message_extend(buf, rest, e)`:** if `rfc_next_message(buf, e)` is `Ok(Some(n))` or `Err(x)`, then `rfc_next_message(buf + rest, e)` is the same. Applied repeatedly, the message sequence doesn't depend on how the stream is chunked. That is RFC 8446 §5.1's "MAY be coalesced … or fragmented", with QUIC CRYPTO chunks in place of records.
  - **`theorem_hs_canonical(buf, e)`:** `rfc_next_message(buf, e) == Ok(Some(n)) ⇒ buf.take(n) == spec_hs_bytes(e, buf.subrange(4, n))`.
  - **`theorem_hs_roundtrip(body, rest, e)`:** `body.len() <= MAX_HS_BODY ⇒ rfc_next_message(spec_hs_bytes(e, body) + rest, e) == Ok(Some(4 + body.len()))`.

- [ ] **Step 1: Failing tests** (`tests/handshake.rs`):
  - **`a2_byte_by_byte`:** push `A2_CH` one byte at a time, calling `next_message(HT_CLIENT_HELLO)` after each push.
    - It is `Ok(None)` after pushes 1–240.
    - After the 241st push it is `Ok(Some(A2_CH))`, and `is_empty()` is true.
  - **`curl_ch_any_chunking`:** for each split set `[[1532], [1200, 332], [7; …] + remainder, [1531, 1]]`, the result is `Ok(Some(CURL_CH))` only after the last chunk, and `Ok(None)` before it.
  - **`two_coalesced`:** push `spec_hs(1, [0xaa; 3]) ++ spec_hs(1, [])` once.
    - The first `next_message(1)` gives the 7-byte message;
    - the second gives `[1, 0, 0, 0]`;
    - the third gives `Ok(None)`.
  - **`wrong_type_first_byte`:**
    - push `[0x02]`: `next_message(1) == Err(0x10a)`, and `is_empty()` is false;
    - push `[0x18]` (key_update) with expect 20: `Err(0x10a)`.
  - **`length_cap`:**
    - `[1, 0x01, 0x00, 0x00]` (exactly 2¹⁶) → `Ok(None)`;
    - `[1, 0x01, 0x00, 0x01]` → `Err(0x0d)`;
    - `[1, 0xff, 0xff, 0xff]` → `Err(0x0d)`, decided after 4 bytes with no body buffered.
  - **`empty_body`:** `[20, 0, 0, 0]` with expect 20 → `Ok(Some([20, 0, 0, 0]))`. Finished's length check is Task 7.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3: Implement.** Duvet-cite:
  - RFC 8446 §4: "A peer which receives a handshake message in an unexpected order MUST abort the handshake with an "unexpected_message" alert.", at the first-byte check;
  - RFC 8446 §5.1: "Handshake messages MAY be coalesced into a single TLSPlaintext record or fragmented across several records", at `theorem_next_message_extend`.
- [ ] **Step 4:** Run the four checks.
- [ ] **Step 5: Commit:** `feat(tls): verified handshake framing with chunking-independence theorem (RFC 8446 §4, §5.1)`
- [ ] **Step 6: Matrix commit.** Add touched notes:
  - RFC 8446 §4: `4a codec: crates/tls/src/handshake.rs (closed in 4b)`;
  - RFC 8446 §5.1 (req): `4a codec: HsReader::is_empty (closed in 4c)`.

---

### Task 3: Extension block (`tls::ext`) — suggested model: opus

**Files:**
- Create: `crates/tls/src/ext.rs`, `crates/tls/tests/ext.rs`
- Modify: `crates/tls/src/lib.rs`, `TRUSTED.md` (extend the tls derived-impl row with `Ext`), `docs/requirements.md`

**Interfaces:**
- Consumes: `rfc_vec`, `read_vec`, `read_u16`, `spec_be_bytes`, `spec_vec_bytes`, `EXT_PRE_SHARED_KEY`, `EXT_OID_FILTERS`, `ALERT_ILLEGAL_PARAMETER`.
- Produces (`tls::ext`):
  - **`pub struct Ext { pub ty: u16, pub data: Vec<u8> }`**, and `pub struct SpecExt { pub ty: u16, pub data: Seq<u8> }`.
  - **`pub open spec fn rfc_ext_list(b: Seq<u8>) -> Option<Seq<SpecExt>>`**, which decreases on `b.len()`. It parses the *content* of an `Extension extensions<..>` vector:
    - `b` empty → `Some(empty)`;
    - otherwise a `u16` type, then `rfc_vec(_, 0, 0xffff)` for `extension_data` (§4.2), then the remainder.
    - Any shortfall → `None`.
  - **`pub open spec fn spec_ext_bytes(ty: u16, data: Seq<u8>) -> Seq<u8>`** and **`spec_ext_list_bytes(s: Seq<SpecExt>) -> Seq<u8>`**.
  - **`theorem_ext_list_canonical(b)`:** `rfc_ext_list(b) == Some(s) ⇒ spec_ext_list_bytes(s) == b`.
  - **`pub open spec fn rfc_ch_ext_check(s: Seq<SpecExt>) -> Result<(), u64>`**, in this order, each failing with `Err(ALERT_ILLEGAL_PARAMETER)`:
    1. two indices `i < j` with `s[i].ty == s[j].ty`. This covers **every** type, including unknown and GREASE (§4.2: "There MUST NOT be more than one extension of the same type in a given extension block."). The RFC names no alert, so this is Decision 7;
    2. some `s[i].ty == EXT_PRE_SHARED_KEY` with `i != s.len() − 1` (§4.2.11);
    3. some `s[i].ty == EXT_OID_FILTERS`. It is recognized and specified only for CertificateRequest (§4.2 table and "If an implementation receives an extension which it recognizes and which is not specified for the message in which it appears, it MUST abort the handshake with an "illegal_parameter" alert.") (Decision 8).

    Otherwise `Ok(())`.
  - **`pub open spec fn spec_find(s: Seq<SpecExt>, ty: u16) -> Option<Seq<u8>>`**: the data of the first entry of that type.
  - **Exec:**
    - **`pub fn parse_ext_list(b: &[u8]) -> (r: Option<Vec<Ext>>)`** ensures `r.deep_view() == rfc_ext_list(b@)`;
    - **`pub fn check_ch_exts(s: &Vec<Ext>) -> (r: Result<(), u64>)`** ensures `r == rfc_ch_ext_check(s@)`. It runs in a single pass, using a `Vec<bool>` of exactly 65,536 entries built by a constant loop, with the invariant `seen[t] ⇔ ∃ k < i. s[k].ty == t`. `// ponytail: 64 KiB scratch per ClientHello; an [u64; 1024] bitmap if memory matters.`;
    - **`pub fn find_ext(s: &Vec<Ext>, ty: u16) -> (r: Option<usize>)`** ensures that `Some(i)` means `s@[i].ty == ty` and no earlier index has `ty`, and `None` means no index has it.

- [ ] **Step 1: Failing tests** (`tests/ext.rs`). Build blocks with `spec`-shaped helpers in the test.
  - **`a2_ext_list`:** `parse_ext_list` of `A2_CH[49..241]` (192 bytes, the content after the `00c0` length at `[47..49]`) gives the types `[0x0000, 0xff01, 0x000a, 0x0010, 0x0005, 0x0033, 0x002b, 0x000d, 0x002d, 0x001c, 0x0039]`, with data lengths `[16, 1, 8, 7, 5, 38, 3, 16, 2, 2, 50]`.
  - **`ext_list_malformed`.** Each of these is `None`:
    - `[0x00]` (a truncated type);
    - `[0x00, 0x2b, 0x00]` (a truncated length);
    - `[0x00, 0x2b, 0x00, 0x03, 0x02, 0x03]` (data overrun).
  - **`dup_known`:** `[(0x2b, [2, 3, 4]), (0x2b, [2, 3, 4])]` → `Err(0x12f)`.
  - **`dup_unknown`:** `[(0xff01, [0]), (0x000a, 0006001d00170018), (0xff01, [0])]` → `Err(0x12f)`.
  - **`dup_grease`:** `[(0x0a0a, []), (0x0a0a, [])]` → `Err(0x12f)`.
  - **`psk_last`:**
    - `[(0x2b, ..), (0x29, [..])]` → `Ok`;
    - `[(0x29, [..]), (0x2b, ..)]` → `Err(0x12f)`.
  - **`oid_filters_in_ch`:** `[(0x30, [0, 0])]` → `Err(0x12f)`.
  - **`max_ext_count`:**
    - 16,383 empty extensions with types `0x1000..0x4fff` give 65,532 bytes; `parse_ext_list` gives 16,383 entries, and `check_ch_exts` gives `Ok`;
    - replacing the last type with `0x1000` gives `Err(0x12f)`.
  - **`find_first`:** `find_ext(a2_list, 0x39) == Some(10)` and `find_ext(a2_list, 0x2c) == None`.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3: Implement.** Duvet-cite:
  - the §4.2 duplicate sentence and the §4.2 "recognizes and which is not specified" sentence, at `rfc_ch_ext_check`;
  - §4.2.11: "The "pre_shared_key" extension MUST be the last extension in the ClientHello" and "Servers MUST check that it is the last extension and otherwise fail the handshake with an "illegal_parameter" alert.".
- [ ] **Step 4:** Run the four checks.
- [ ] **Step 5: Commit:** `feat(tls): verified extension block with all-type duplicate check, pre_shared_key-last, CH-forbidden types (RFC 8446 §4.2, §4.2.11)`
- [ ] **Step 6: Matrix commit.** RFC 8446 §4.2 gets the touched note `4a codec: crates/tls/src/ext.rs: duplicates, psk-last, oid_filters (closed in 4b: no unsolicited responses)`.

---

### Task 4: ClientHello extension bodies (`tls::ch_ext`) — suggested model: sonnet

**Files:**
- Create: `crates/tls/src/ch_ext.rs`, `crates/tls/tests/ch_ext.rs`
- Modify: `crates/tls/src/lib.rs`, `TRUSTED.md` (add `KeyShareEntry` to the row), `docs/requirements.md`

**Interfaces:**
- Consumes: `rfc_vec`, `rfc_vec_exact`, `rfc_u16_list`, `read_vec`, `read_u16`, `parse_u16_list`.
- Produces (`tls::ch_ext`). Each grammar below is exact: the whole `extension_data` must be consumed, with no trailing bytes.
  - **`pub struct KeyShareEntry { pub group: u16, pub key_exchange: Vec<u8> }`**, and `SpecKeyShare`.

  | Spec fn | Exec fn | Grammar (RFC 8446 unless noted) |
  |---|---|---|
  | `rfc_versions(d) -> Option<Seq<u16>>` | `parse_versions(d: &[u8]) -> Option<Vec<u16>>` | §4.2.1 `ProtocolVersion versions<2..254>` |
  | `rfc_groups(d) -> Option<Seq<u16>>` | `parse_groups` | §4.2.7 `NamedGroup named_group_list<2..2^16-1>` |
  | `rfc_sig_schemes(d) -> Option<Seq<u16>>` | `parse_sig_schemes` (for both 13 and 50) | §4.2.3 `SignatureScheme supported_signature_algorithms<2..2^16-2>` |
  | `rfc_key_shares(d) -> Option<Seq<SpecKeyShare>>` | `parse_key_shares -> Option<Vec<KeyShareEntry>>` | §4.2.8 `KeyShareEntry client_shares<0..2^16-1>`, each entry `NamedGroup group; opaque key_exchange<1..2^16-1>` |
  | `rfc_alpn(d) -> Option<Seq<Seq<u8>>>` | `parse_alpn -> Option<Vec<Vec<u8>>>` | RFC 7301 §3.1 `ProtocolName protocol_name_list<2..2^16-1>`, `opaque ProtocolName<1..2^8-1>` |
  | `rfc_server_name(d) -> Option<Option<Seq<u8>>>` | `parse_server_name -> Option<Option<Vec<u8>>>` | RFC 6066 §3 `ServerName server_name_list<1..2^16-1>`, each entry `NameType name_type` (u8), then for `host_name(0)` `opaque HostName<1..2^16-1>`, else `opaque<0..2^16-1>` (RFC 6066: future types "MUST begin with a 16-bit length field"). The result is the first host_name, or `None` if the list has none |
  | `rfc_cookie_ok(d) -> bool` | `cookie_ok` | §4.2.2 `opaque cookie<1..2^16-1>` |
  | `rfc_psk_modes(d) -> Option<Seq<u8>>` | `parse_psk_modes` | §4.2.9 `PskKeyExchangeMode ke_modes<1..255>` |
  | `rfc_offered_psks_ok(d) -> bool` | `offered_psks_ok` | §4.2.11 `PskIdentity identities<7..2^16-1>` (each `opaque identity<1..2^16-1>; uint32 obfuscated_ticket_age`), then `PskBinderEntry binders<33..2^16-1>` (each `opaque <32..255>`) |
  | `rfc_early_data_ok(d) -> bool` | `early_data_ok` | §4.2.10 `client_hello: Empty`, so `d.len() == 0` |

  - RFC 7301 and RFC 6066 are not in `.duvet/config.toml`, so cite them in plain `//` comments.
  - Each exec fn ensures `r.deep_view() == rfc_*(d@)` (or `r == rfc_*_ok(d@)`).
  - Allocation is bounded by `d@.len()`.

- [ ] **Step 1: Failing tests** (`tests/ch_ext.rs`):
  - **`a2_bodies`.** Taken from A.2's extensions, in Task 3's order:
    - `parse_versions(020304) == Some([0x0304])`;
    - `parse_groups(0006001d00170018) == Some([0x1d, 0x17, 0x18])`;
    - `parse_sig_schemes(000e0403050306030203080408050806) == Some([0x0403, 0x0503, 0x0603, 0x0203, 0x0804, 0x0805, 0x0806])`;
    - `parse_alpn(000504616c706e) == Some([b"alpn"])`;
    - `parse_server_name(000e00000b6578616d706c652e636f6d) == Some(Some(b"example.com"))`;
    - `parse_key_shares(<A.2's 38 bytes>) == Some([{0x1d, 9370b2c9caa47fbabaf4559fedba753de171fa71f50f1ce15d43e994ec74d748}])`;
    - `parse_psk_modes(0101) == Some([1])`.
  - **`grammar_bounds`.** Each of these is `None` or `false`:
    - versions `00`, `0102`, `03030400`;
    - groups `0000`, `00030017aa`;
    - sig schemes `0000`;
    - key shares `00050017000100` plus a trailing byte, and `000400170000` (an empty key_exchange);
    - alpn `0000` (below the list floor of 2) and `0003000141` (a first ProtocolName of length 0);
    - server name `0000`;
    - `cookie_ok(0000)`;
    - psk modes `00`;
    - `early_data_ok([0])`;
    - `offered_psks_ok` of an identity list of length 6.
  - **`grammar_edges`:**
    - key shares `0000` gives `Some([])`, because the vector MAY be empty (§4.2.8);
    - server name `0005 01 0002 abcd` (only an unknown type) gives `Some(None)`;
    - `cookie_ok(00 01 aa)` is true;
    - the `pre_shared_key` body of `R4_CH` gives `offered_psks_ok == true`;
    - `early_data_ok([])` is true.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3: Implement.** Duvet-cite each RFC 8446 grammar at its `rfc_*`, quoting its struct lines from that section. If `duvet report` rejects a struct quote, cite the section's nearest keyword sentence instead.
- [ ] **Step 4:** Run the four checks.
- [ ] **Step 5: Commit:** `feat(tls): verified ClientHello extension grammars (RFC 8446 §4.2.x, RFC 7301, RFC 6066)`
- [ ] **Step 6: Matrix commit.** RFC 8446 §4.2.8 gets the touched note `4a codec: crates/tls/src/ch_ext.rs (closed in 4b)`.

---

### Task 5: ClientHello parse and validation (`tls::client_hello`) — suggested model: opus

**Files:**
- Create: `crates/tls/src/client_hello.rs`, `crates/tls/tests/client_hello.rs`
- Modify:
  - `crates/tls/src/lib.rs`;
  - `crates/tls/tests/common/mod.rs` (add `split_ch`, `join_ch`, `head` and the `R*` ClientHello vectors);
  - `TRUSTED.md` (add `ClientHello`);
  - `docs/requirements.md`.

**Interfaces:**
- Consumes: everything from Tasks 1, 3 and 4, and `ALERT_*`, `PROTOCOL_VIOLATION`, `EXT_*`, `TLS13`, `SSL30`.
- Produces (`tls::client_hello`):
  - **`pub struct SpecChFields`** (spec only), with fields `legacy_version: u16`, `random: Seq<u8>`, `legacy_session_id: Seq<u8>`, `cipher_suites: Seq<u16>`, `compression: Seq<u8>` and `exts: Option<Seq<SpecExt>>`.
  - **`pub open spec fn rfc_ch_fields(body: Seq<u8>) -> Option<SpecChFields>`** transcribes the §4.1.2 `ClientHello`, in order:
    - `uint16 legacy_version`;
    - `opaque Random[32]`;
    - `legacy_session_id<0..32>`;
    - `CipherSuite cipher_suites<2..2^16-2>`, through `rfc_u16_list`;
    - `legacy_compression_methods<1..2^8-1>`;
    - then the end of `body` gives `exts: None` (no extensions block, §4.1.2). Otherwise it is `rfc_vec_exact(rest, 8, 0xffff)` (`extensions<8..2^16-1>`), then `rfc_ext_list`, giving `Some(list)`.
  - **`pub open spec fn spec_ch_fields_bytes(f: SpecChFields) -> Seq<u8>`** and **`theorem_ch_fields_canonical(body)`:** `rfc_ch_fields(body) == Some(f) ⇒ spec_ch_fields_bytes(f) == body`.
  - **`pub struct ClientHello`**, with its twin `SpecClientHello`:
    ```
    random: [u8; 32], legacy_session_id: Vec<u8>, cipher_suites: Vec<u16>, versions: Vec<u16>,
    groups: Option<Vec<u16>>, key_shares: Option<Vec<KeyShareEntry>>, sig_algs: Vec<u16>,
    sig_algs_cert: Option<Vec<u16>>, alpn: Option<Vec<Vec<u8>>>, server_name: Option<Vec<u8>>,
    transport_params: Vec<u8>
    ```
    Every list keeps unknown and GREASE values in wire order. 4b's selection ignores them (§9.3).
  - **`pub open spec fn rfc_client_hello(body: Seq<u8>) -> Result<SpecClientHello, u64>`.** The check order is the requirement (Decision 9). Let `x = f.exts.unwrap_or(empty)`.
    1. `rfc_ch_fields(body)` is `None` → `ALERT_DECODE_ERROR` (§6: "cannot be parsed according to the syntax");
    2. `rfc_ch_ext_check(x)` is `Err(e)` → `e`;
    3. eleven straight-line checks, one per recognized type T in {0, 10, 13, 16, 41, 42, 43, 44, 45, 50, 51}: `spec_find(x, T) matches Some(d) && !grammar_T(d)` → `ALERT_DECODE_ERROR`. Step 2 has already ruled out duplicates, so the first match is the only one. The exec code is eleven `find_ext` calls with no quantifier loop. Types 41 (`pre_shared_key`, syntax only) and 57 (`quic_transport_parameters`) are otherwise opaque: PSK is declined, and 4c parses TPs with `quic::tp`;
    4. `f.legacy_version <= SSL30` → `ALERT_PROTOCOL_VERSION` (Appendix D.5);
    5. `supported_versions` is absent, or its list lacks `TLS13` → `ALERT_PROTOCOL_VERSION`. That includes `exts: None`. Appendix D.2 and §4.2.1: we support only 1.3, and never read `legacy_version` for negotiation;
    6. `f.compression != [0x00]` → `ALERT_ILLEGAL_PARAMETER` (§4.1.2);
    7. `f.legacy_session_id.len() != 0` → `PROTOCOL_VIOLATION` (RFC 9001 §8.4 SHOULD, Decision 6);
    8. a `cookie` is present → `ALERT_ILLEGAL_PARAMETER`. We never issue cookies (Decision 5; matrix binding note "rejects a cookie we never issued");
    9. → `ALERT_MISSING_EXTENSION` if any of these holds:
       - `signature_algorithms` is absent (§4.2.3: we always authenticate with a certificate);
       - `pre_shared_key` and `supported_groups` are both absent (§9.2);
       - exactly one of `supported_groups` and `key_share` is present (§9.2);
       - `pre_shared_key` is present without `psk_key_exchange_modes` (§4.2.9 names no alert; Decision 7);
       - `quic_transport_parameters` is absent (RFC 9001 §8.2, whose 0x016d is this same code);
    10. otherwise `Ok`. Each field comes from `spec_find` plus its grammar, and `random` is `f.random`.
  - **`pub fn parse_client_hello(body: &[u8]) -> (r: Result<ClientHello, u64>)`**, where `body` is the message after its 4-byte header. It ensures: `rfc_client_hello(body@) == Ok(s) ⇒ r matches Ok(c) && c@ == s`, and `rfc_client_hello(body@) == Err(e) ⇒ r == Err(e)`.

- [ ] **Step 1: Failing tests** (`tests/client_hello.rs`). `p(msg) = parse_client_hello(&msg[4..])`, and `with(msg, f)` = `join_ch` of `split_ch` with `f` applied to the extension list.
  - **`a2_ch`:** `p(A2_CH)` is `Ok(c)` with:
    - `random` = `ebf8fa56f12939b9584a3896472ec40bb863cfd3e86804fe3a47f06a2b69484c`;
    - `legacy_session_id == []` and `cipher_suites == [0x1301, 0x1302]`;
    - `versions == [0x0304]` and `groups == Some([0x1d, 0x17, 0x18])`;
    - `key_shares == Some([{0x1d, 9370…d748}])`;
    - `sig_algs` as in Task 4 and `sig_algs_cert == None`;
    - `alpn == Some([b"alpn"])` and `server_name == Some(b"example.com")`;
    - `transport_params` = the 50 bytes `0408ffffffffffffffff…048000ffff`.
  - **`curl_ch`:** `p(CURL_CH)` is `Ok(c)` with:
    - `cipher_suites == [0x1302, 0x1303, 0x1301, 0x1304]` and `versions == [0x0304]`;
    - `groups` containing `0x0017`, and `key_shares` groups `[0x11ec, 0x001d]` with key lengths `[1216, 32]`;
    - `alpn == Some([b"h3", b"h3-29"])` and `server_name == Some(b"localhost")`;
    - `transport_params.len() == 68`;
    - `sig_algs` containing `0x0403` and `0x0804`.
  - **`rfc8448_needs_qtp`:**
    - `p(R3_CH)`, `p(R5_CH1)` and `p(R4_CH)` each give `Err(0x16d)`: they are TCP ClientHellos, with no quic_transport_parameters;
    - `p(with(R3_CH, push (0x39, [0x01, 0x00])))` is `Ok`, with `groups == Some([0x1d, 0x17, 0x18, 0x19, 0x100, 0x101, 0x102, 0x103, 0x104])`, `alpn == None`, and the unknown session_ticket (0x23) ignored.
  - **`rfc8448_s5_ch2_cookie`:** `p(R5_CH2)` and `p(with(R5_CH2, push QTP))` both give `Err(0x12f)`. The cookie check precedes missing_extension.
  - **`rfc8448_s4_psk_not_last`:**
    - `p(with(R4_CH, push QTP))` gives `Err(0x12f)`;
    - `p(with(R4_CH, insert QTP before the 0x29 entry))` is `Ok`.
  - **`grease_ignored`.** Start from `A2_CH`, with suites `[0x6a6a, 0x1301]`, then apply:
    - insert `(0x0a0a, [])` first;
    - supported_versions becomes `[0x3a3a, 0x0304]`;
    - groups and sig_algs each get `0x4a4a` prepended;
    - key_share gets `{0x5a5a, [0x00]}` prepended;
    - ALPN gets `"\x7a\x7a"` prepended;
    - push `(0xfafa, [0])`.

    The result is `Ok`, with every GREASE value present in its list.
  - **`ch_errors`.** This is a table whose head or extension edits come from `head`/`with`. Each row is `(edit, expected)`:
    - **Truncation:** drop the last byte of A.2 → `0x132`.
    - **Field bounds:** session id of 33 bytes → `0x132`; suites of odd length 3 → `0x132`; suites of length 0 → `0x132`; compression of length 0 → `0x132`.
    - **Extension block framing:** block length 4 (one empty extension) → `0x132` (`<8..>`); a trailing byte after the block → `0x132`.
    - **Bad bodies:** key_share body `00` → `0x132`; early_data body `[0]` → `0x132`; ALPN `0003000141` → `0x132`.
    - **Version:** no extension block → `0x146`; `legacy_version` `0x0300` → `0x146`; supported_versions `[0x0303]` → `0x146`; supported_versions absent → `0x146`.
    - **Compression:** `[0, 1]` → `0x12f`; `[1]` → `0x12f`.
    - **Session id:** 32 bytes → `0x0a` (Decision 6).
    - **Cookie:** `(0x2c, 0001aa)` added → `0x12f`.
    - **missing_extension:**
      - signature_algorithms removed → `0x16d`;
      - supported_groups and key_share both removed, no PSK → `0x16d`;
      - key_share removed → `0x16d`;
      - supported_groups removed → `0x16d`;
      - a valid `pre_shared_key` pushed last, with psk_key_exchange_modes removed → `0x16d`;
      - QTP removed → `0x16d`.
    - **Order pins:** compression `[1]` with QTP removed → `0x12f` (step 6 before 9); a duplicate 0x2b with supported_versions `[0x0303]` → `0x12f` (step 2 before 5); a bad key_share body with `legacy_version` `0x0300` → `0x132` (step 3 before 4).
  - **`ch_oks`:**
    - ALPN removed → `Ok`, `alpn == None`. 4b answers it with 0x178;
    - supported_groups and key_share removed, with a valid `pre_shared_key` last and psk_key_exchange_modes present → `Ok`, `groups == None`. 4b answers it with handshake_failure;
    - signature_algorithms_cert `00020403` added → `sig_algs_cert == Some([0x0403])`.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3: Implement.** Duvet-cite at each step of `rfc_client_hello`:
  - RFC 8446 §6, the decode_error sentence and the illegal_parameter sentence;
  - RFC 8446 §4.1.2, the cipher_suites "MUST ignore those cipher suites" sentence, the compression "MUST contain exactly one byte" and "MUST abort … illegal_parameter" sentences, and "Servers MUST ignore unrecognized extensions.";
  - RFC 8446 §4.2.1, "servers MUST NOT use the ClientHello.legacy_version value for version negotiation …", "MUST ignore any unknown versions …" and "Servers MUST be prepared to receive ClientHellos that include this extension but do not include 0x0304 …";
  - RFC 8446 Appendix D.2 ("If the "supported_versions" extension is absent and the server only supports versions greater than ClientHello.legacy_version, the server MUST abort the handshake with a "protocol_version" alert.") and Appendix D.5 (the 0x0300 sentence);
  - RFC 8446 §4.2.3, the missing_extension sentence;
  - RFC 8446 §4.2.9, "servers MUST abort the handshake";
  - RFC 8446 §9.2, the two bullets and "Servers receiving a ClientHello which does not conform to these requirements MUST abort the handshake with a "missing_extension" alert.";
  - RFC 8446 §9.3, "A server receiving a ClientHello MUST correctly ignore all unrecognized cipher suites, extensions, and other parameters.";
  - RFC 8446 §4.2.10, "A server which receives an "early_data" extension MUST behave in one of three ways:". We take the first: ignore it. EE never echoes it (Task 6), and 3e drops 0-RTT packets;
  - RFC 8446 §4.4.2.1, "TLS 1.3 servers MUST be able to process ClientHello messages that include it". `status_request_v2` (17) is an ignored type;
  - RFC 9001 §8.2, the 0x016d sentence;
  - RFC 9001 §8.4, the SHOULD sentence.
- [ ] **Step 4:** Run the four checks.
- [ ] **Step 5: Commit:** `feat(tls): verified ClientHello parse and ordered validation (RFC 8446 §4.1.2, §4.2.x, §9.2-9.3, App. D; RFC 9001 §8.2, §8.4)`
- [ ] **Step 6: Matrix commit.**
  - `✅ 4a: crates/tls/src/client_hello.rs` on RFC 8446 §4.2.11, §9.3 and §9.2 (req) "MUST implement ... cookie" (note "parsed; any cookie rejected (never issued)").
  - Touched notes, `4a codec: crates/tls/src/client_hello.rs (closed in 4x)`, on RFC 8446 §4.1.2 (4b), §4.2.3 (4b) and §6 (4c), and on RFC 9001 §8.1 (4b).
  - Notes for rows Task 6 will close: `4a: ClientHello half in client_hello.rs` on §4.2.1, §4.2.2, §4.2.9, §4.2.10, §9.2, Appendix D, and RFC 9001 §4.2 and §8.2.
  - The RFC 9001 §8.4 note (see "Rows touched").

---

### Task 6: ServerHello, HelloRetryRequest and EncryptedExtensions serializers (`tls::server_msgs`) — suggested model: sonnet

**Files:**
- Create: `crates/tls/src/server_msgs.rs`, `crates/tls/tests/server_msgs.rs`
- Modify: `crates/tls/src/lib.rs`, `crates/tls/tests/common/mod.rs` (add `A3_SH`, `R3_SH`, `R5_SH`), `docs/requirements.md`

**Interfaces:**
- Consumes: `spec_hs_bytes`, `spec_ext_bytes`, `spec_vec_bytes`, `spec_be_bytes`, `put_u16`, `put_vec`, `LEGACY_VERSION`, `TLS13`, `TLS_AES_128_GCM_SHA256`, `HRR_RANDOM`, `H3_ALPN`, `EXT_*`, `HT_*`.
- Produces (`tls::server_msgs`). Let `ks(g, kx) = spec_ext_bytes(EXT_KEY_SHARE, spec_be_bytes(g, 2) + spec_vec_bytes(0xffff, kx))` and `sv = spec_ext_bytes(EXT_SUPPORTED_VERSIONS, spec_be_bytes(TLS13, 2))`.
  - **`pub open spec fn spec_server_hello_bytes(random: Seq<u8>, sid: Seq<u8>, group: u16, kx: Seq<u8>) -> Seq<u8>`** = `spec_hs_bytes(HT_SERVER_HELLO, spec_be_bytes(LEGACY_VERSION, 2) + random + spec_vec_bytes(32, sid) + spec_be_bytes(TLS_AES_128_GCM_SHA256, 2) + seq![0] + spec_vec_bytes(0xffff, ks(group, kx) + sv))`.
    - That is the §4.1.3 `ServerHello`.
    - The extensions are exactly key_share, then supported_versions. RFC 8448 and A.3 use the same order.
    - The cipher suite is the constant 0x1301, our only suite. So whatever 4b negotiates, no other suite can be sent (Appendix D.5 RC4/<112-bit).
  - **`pub fn serialize_server_hello(random: &[u8; 32], session_id_echo: &[u8], group: u16, key_exchange: &[u8], out: &mut Vec<u8>)`**:
    - requires `session_id_echo@.len() <= 32` and `1 <= key_exchange@.len() <= 256` (`// ponytail: every non-PQ NamedGroup fits; 4b passes 65`);
    - ensures `out@ == old(out)@ + spec_server_hello_bytes(random@, session_id_echo@, group, key_exchange@)`.
    - `group` is a parameter, so the X25519 vectors exercise the same code (Decision 10).
  - **`pub open spec fn spec_hello_retry_request_bytes(sid: Seq<u8>, selected_group: u16) -> Seq<u8>`** is the same layout, with `HRR_RANDOM` as `random`. The extensions are `spec_ext_bytes(EXT_KEY_SHARE, spec_be_bytes(selected_group, 2))` (`KeyShareHelloRetryRequest`), then `sv`. There is **no cookie** (Decision 5).
  - **`pub fn serialize_hello_retry_request(session_id_echo: &[u8], selected_group: u16, out: &mut Vec<u8>)`** requires `session_id_echo@.len() <= 32`.
  - **`pub open spec fn spec_encrypted_extensions_bytes(tp: Seq<u8>) -> Seq<u8>`** = `spec_hs_bytes(HT_ENCRYPTED_EXTENSIONS, spec_vec_bytes(0xffff, spec_ext_bytes(EXT_ALPN, spec_vec_bytes(0xffff, spec_vec_bytes(255, H3_ALPN@))) + spec_ext_bytes(EXT_QUIC_TRANSPORT_PARAMETERS, tp)))`.
    - The extensions are exactly ALPN `h3`, then quic_transport_parameters (Decision 11).
    - No `early_data`, `post_handshake_auth`, `psk_key_exchange_modes` or `status_request_v2` is ever sent.
  - **`pub fn serialize_encrypted_extensions(transport_params: &[u8], out: &mut Vec<u8>)`** requires `transport_params@.len() <= 1024` (`// ponytail: 3b's server TPs are < 256 bytes`).

- [ ] **Step 1: Failing tests** (`tests/server_msgs.rs`):
  - **`rfc8448_s5_sh`:** `serialize_server_hello(R5_SH[6..38], [], 0x0017, R5_SH[52..117])` gives exactly `R5_SH` (123 bytes).
  - **`rfc8448_s3_sh`:** the same with `R3_SH`, using its random `[6..38]` and its 32-byte X25519 key `[52..84]`, with group `0x001d` → `R3_SH`.
  - **`rfc9001_a3_sh`:** `A3_SH`, with random `A3_SH[6..38]` (`eefce7f7…9a045a12`), group `0x001d` and key `A3_SH[52..84]` (`9d3c940d…b9da1a`), → `A3_SH`.
  - **`hrr_p256`:** `serialize_hello_retry_request([], 0x0017)` gives `020000340303cf21ad74e59a6111be1d8c021e65b891c2a211167abb8c5e079e09e2c8a8339c00130100000c003300020017002b00020304` (56 bytes, script-checked).
  - **`sh_echo_32`:** with R5's random and key and `session_id_echo = [0xab; 32]`, the result is 155 bytes. Bytes 1..4 are `000097` (0x77 + 32), byte 38 is `0x20`, and bytes 39..71 are `0xab`.
  - **`ee_h3_tp`:** `serialize_encrypted_extensions(010480007530)` gives `08000015001300100005000302683300390006010480007530`.
  - **`ee_empty_tp`:** `serialize_encrypted_extensions([])` gives `0800000f000d00100005000302683300390000`.
  - **`appends`:** with `out = [0xee]` beforehand, every serializer leaves `out[0] == 0xee`.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3: Implement.** Duvet-cite:
  - RFC 8446 §4.1.3: legacy_version "MUST be set to 0x0303", "legacy_compression_method: A single byte which MUST have the value 0.", "All TLS 1.3 ServerHello messages MUST contain the "supported_versions" extension." and "The ServerHello MUST only include extensions which are required to establish the cryptographic context and negotiate the protocol version.";
  - RFC 8446 §4.1.4: "The server's extensions MUST contain "supported_versions"." and the "MUST NOT contain any extensions that were not first offered … with the exception of optionally the "cookie"" sentence;
  - RFC 8446 §4.2.1: "A server which negotiates TLS 1.3 MUST respond by sending a "supported_versions" extension containing the selected version value (0x0304)." and "It MUST set the ServerHello.legacy_version field to 0x0303 (TLS 1.2).";
  - RFC 8446 §4.2.6: "Servers MUST NOT send this extension.";
  - RFC 8446 §4.2.9: "The server MUST NOT send a "psk_key_exchange_modes" extension.";
  - RFC 8446 §4.5: "Servers MUST NOT send this message", at the module doc. No EndOfEarlyData serializer exists;
  - RFC 8446 §9.2: "All implementations MUST send and use these extensions when offering applicable features:";
  - RFC 8446 Appendix D.5: "Implementations MUST NOT send a ClientHello.legacy_version or ServerHello.legacy_version set to 0x0300 or less.";
  - RFC 9001 §4.2: "An endpoint MUST terminate the connection if a version of TLS older than 1.3 is negotiated." Only 0x0304 is ever sent;
  - RFC 9001 §8.2: "Endpoints MUST send the quic_transport_parameters extension".
- [ ] **Step 4:** Run the four checks.
- [ ] **Step 5: Commit:** `feat(tls): verified ServerHello, HelloRetryRequest and EncryptedExtensions serializers (RFC 8446 §4.1.3-4.1.4, §4.3.1; RFC 9001 §8.2)`
- [ ] **Step 6: Matrix commit.**
  - `✅ 4a: crates/tls/src/client_hello.rs + server_msgs.rs` on RFC 8446 §4.2.1, §4.2.2 (note "no cookie in HRR; any received cookie rejected"), §4.2.6, §4.2.9, §4.2.10 (note "ignored; EE never echoes; 0-RTT packets dropped by 3e"), §4.5, §9.2 and Appendix D, and on RFC 9001 §4.2 and §8.2. These replace Task 5's half-notes.
  - Touched notes on RFC 8446 §4.1.3, §4.1.4 and §4.3.1: `4a codec: server_msgs.rs layout (closed in 4b)`.

---

### Task 7: Certificate, CertificateVerify and Finished serializers, and `parse_finished` — suggested model: sonnet

**Files:**
- Modify: `crates/tls/src/server_msgs.rs`, `crates/tls/tests/server_msgs.rs`, `crates/tls/tests/common/mod.rs` (add `R5_CERT`, `R5_CV`, `R5_SFIN`), `docs/requirements.md`

**Interfaces:**
- Consumes: Task 6's helpers, and `HT_CERTIFICATE`, `HT_CERTIFICATE_VERIFY`, `HT_FINISHED`, `ALERT_DECODE_ERROR`.
- Produces (`tls::server_msgs`):
  - **`pub open spec fn spec_cert_entries(chain: Seq<Seq<u8>>) -> Seq<u8>`**: the concatenation over the chain, in order, of `spec_vec_bytes(0xff_ffff, cert) + spec_vec_bytes(0xffff, empty)`. Each entry is a §4.4.2 X509 `CertificateEntry` with `cert_data<1..2^24-1>` and an empty `extensions<0..2^16-1>`.
  - **`pub open spec fn spec_certificate_bytes(chain) -> Seq<u8>`** = `spec_hs_bytes(HT_CERTIFICATE, spec_vec_bytes(255, empty) + spec_vec_bytes(0xff_ffff, spec_cert_entries(chain)))`. The `certificate_request_context` is zero length.
  - **`pub open spec fn cert_chain_ok(chain: Seq<Seq<u8>>) -> bool`**:
    - `chain.len() >= 1` (§4.4.2: "MUST always be non-empty");
    - `∀ c. 1 <= c.len() <= 0xff_ffff`;
    - `spec_cert_entries(chain).len() + 4 <= 0xff_ffff`.
  - **`pub fn serialize_certificate(chain: &Vec<Vec<u8>>, out: &mut Vec<u8>)`** requires `cert_chain_ok(chain.deep_view())`. The chain is opaque DER, end-entity first, in the order the config gives.
  - **`pub open spec fn spec_certificate_verify_bytes(scheme: u16, sig: Seq<u8>) -> Seq<u8>`** = `spec_hs_bytes(HT_CERTIFICATE_VERIFY, spec_be_bytes(scheme, 2) + spec_vec_bytes(0xffff, sig))`, and **`pub fn serialize_certificate_verify(scheme: u16, signature: &[u8], out: &mut Vec<u8>)`**, which requires `signature@.len() <= 0xffff`.
  - **`pub open spec fn spec_finished_bytes(vd: Seq<u8>) -> Seq<u8>`** = `spec_hs_bytes(HT_FINISHED, vd)`, and **`pub fn serialize_finished(verify_data: &[u8; 32], out: &mut Vec<u8>)`**. `Hash.length` is 32 for SHA-256.
  - **`pub open spec fn rfc_finished(body: Seq<u8>) -> Result<Seq<u8>, u64>`** = `if body.len() == 32 { Ok(body) } else { Err(ALERT_DECODE_ERROR) }`, and **`pub fn parse_finished(body: &[u8]) -> (r: Result<[u8; 32], u64>)`**, exec ≡ spec. Comparing the value is 4b's job (decrypt_error).

- [ ] **Step 1: Failing tests:**
  - **`rfc8448_s5_certificate`:** `serialize_certificate(&vec![R5_CERT[11..443]])` gives exactly `R5_CERT` (445 bytes). The DER is 432 bytes and starts `308201ac`.
  - **`two_cert_chain`:** `serialize_certificate(&vec![der, vec![0x30, 0x00]])` starts `0b0001c0 00 0001bc 0001b0 308201ac` and ends `e1 0000 000002 3000 0000`. That is the last DER byte, an empty extensions field, the second entry and its empty extensions.
  - **`rfc8448_s5_cv`:** `serialize_certificate_verify(0x0804, R5_CV[8..136])` gives `R5_CV`.
  - **`rfc8448_s5_finished`:** `serialize_finished(8863e6bfb0420a927fa27f34336a70ae426e968e3eb884945b96856dba3976d1)` gives `R5_SFIN`.
  - **`finished_parse`:**
    - `parse_finished([0x11; 32]) == Ok([0x11; 32])`;
    - 31 bytes → `Err(0x132)`;
    - 33 bytes → `Err(0x132)`;
    - 0 bytes → `Err(0x132)`.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3: Implement.** Duvet-cite:
  - RFC 8446 §4.4.2: "this field SHALL be zero length.", "The server's certificate_list MUST always be non-empty.", "The OpenPGP certificate type [RFC6091] MUST NOT be used with TLS 1.3." and "Extensions in the Certificate message from the server MUST correspond to ones from the ClientHello message." (we send none);
  - RFC 8446 §4.4.2.1: "they MUST NOT send the status_request_v2 extension in the EncryptedExtensions, CertificateRequest, or Certificate messages.";
  - RFC 8446 §4.4.2, the RawPublicKey MUST: X509 only, since `server_certificate_type` is never negotiated;
  - RFC 8446 Appendix B: "TLS 1.3 implementations MUST NOT send them". Every codepoint we write is a `tls::codes` constant, and none is `_RESERVED`;
  - RFC 9001 §4.4: "servers MUST NOT send post-handshake TLS CertificateRequest messages". No CertificateRequest serializer exists.
- [ ] **Step 4:** Run the four checks.
- [ ] **Step 5: Commit:** `feat(tls): verified Certificate, CertificateVerify, Finished serializers and Finished parse (RFC 8446 §4.4.2-4.4.4)`
- [ ] **Step 6: Matrix commit.**
  - `✅ 4a: crates/tls/src/server_msgs.rs` on RFC 8446 Appendix B, §4.4.2.1 and §4.4.2 (req) "RawPublicKey certificate type", and on RFC 9001 §4.4.
  - Touched notes on RFC 8446 §4.4.2, §4.4.3 and §4.4.4: `4a codec: server_msgs.rs layout (closed in 4b)`.
  - Then run the row check, regenerating `p4rows.txt` from the matrix first so that a mislabelled row fails loudly. Use the outline's `awk` extraction: Phase column starting with `4`, as `RFC § | Topic`. It must print `77 3e 2 4a 17 4b 28 4c 30`, or `75 3e 0 4a 17 4b 28 4c 30` if 3e has merged.

---

## Exit criteria (Phase 4a)

- All four checks pass on the merged tree.
- The 17 rows above carry `✅ 4a: <file>`, and every touched row carries its `4a codec:` note.
- The row check prints `75 3e 0 4a 17 4b 28 4c 30` (or `77 3e 2 …` if 3e has not merged).
- `cargo test -p tls` passes. That covers every vector in the table, including `CURL_CH`.
- `phase-4a` is merged into `main`.

## Binding notes for later sub-phases

- **4b:**
  - consume `ClientHello` as validated. Never re-check what Task 5 checked;
  - pass `ch.legacy_session_id` as `session_id_echo` (§4.1.3);
  - run negotiation in the outline's order (suite, ALPN, scheme/chain, group);
  - call `next_message` with the one type each state expects, and treat any byte at a level with no expected type as `ALERT_UNEXPECTED_MESSAGE`;
  - hash the raw messages `next_message` returns.
- **4c:**
  - before raising receive keys for a level, check `HsReader::is_empty()` for the level below (RFC 9001 §4.1.3, RFC 8446 §5.1 (req));
  - parse `transport_params` with `quic::tp::parse_transport_params(_, true)`;
  - add the `tls::codes` = `quic::codes` test;
  - RFC 9001 A.2's ClientHello is a valid `ClientHello` here (`a2_ch`), and fails later at 4b's ALPN check (`0x178`).

## Self-review (done while writing)

- **Spec coverage.** The design spec's Phase 4 extension list is:
  - supported_versions (Tasks 4–6);
  - supported_groups and key_share (Tasks 4–5);
  - signature_algorithms (Tasks 4–5);
  - ALPN (Tasks 4–6);
  - quic_transport_parameters (Tasks 5–6);
  - no early_data (Tasks 5–6).

  Every message a server sends is serialized: ServerHello, HRR, EE, Certificate, CV and Finished. Every message it accepts is parsed: ClientHello and Finished. The certificate chain is opaque DER (Task 7). The codec obligations are met in Global Constraints and Decision 2.
- **Easy-to-miss MUSTs.** Each one in the brief has a pinned test or a 4b/4c binding:
  - the echo: `sh_echo_32` and the 4b note;
  - the HRR cookie: `hrr_p256`, `rfc8448_s5_ch2_cookie`;
  - the downgrade sentinel and the ServerHello random: 4b;
  - unknown extensions ignored: `grease_ignored`, `rfc8448_needs_qtp`;
  - duplicates: `dup_*`;
  - pre_shared_key last: `psk_last`, `rfc8448_s4_psk_not_last`;
  - the alert mapping and order: `ch_errors` order pins;
  - missing_extension: `ch_errors`;
  - coalescing and fragmentation: `two_coalesced`, `curl_ch_any_chunking`;
  - the key-change boundary: `is_empty`, 4c.
- **Type consistency.** These names are used identically everywhere:
  - `rfc_vec`/`spec_vec_bytes`/`read_vec`/`put_vec` (1 → 2–7);
  - `spec_hs_bytes`/`HsReader`/`next_message` (2 → 6, 7, 4b);
  - `Ext`/`SpecExt`/`spec_ext_bytes`/`spec_find`/`check_ch_exts` (3 → 5, 6);
  - `KeyShareEntry` (4 → 5, 4b);
  - `ClientHello`/`parse_client_hello` (5 → 4b);
  - `serialize_*`/`parse_finished` (6–7 → 4b).
- **Arithmetic re-checked by script** (`<scratch>/chk4/v8448.py`):
  - HRR body 52 = 0x34;
  - EE bodies 21 = 0x15 and 15 = 0x0f;
  - the R5 Certificate list is 432 + 5 = 437 = 0x1b5, with body 0x1b9;
  - the two-cert list is 437 + 7 = 444 = 0x1bc, with body 0x1c0;
  - `max_ext_count`: 16,383 × 4 = 65,532 ≤ 65,535;
  - the A.2 extension content is `A2_CH[49..241]`: header 4, then version 2, random 32, sid 1, suites 2 + 4, compression 1 + 1, ext length 2, which totals 49, plus 192 = 0xc0 bytes;
  - ServerHello key offsets: `[52..117]` (P-256) and `[52..84]` (X25519). An empty echo puts key_share's `key_exchange` at 4 + 48. The 32-byte echo makes the length field `0x000097`;
- **Proportion.** Bodies appear only where the order is the requirement (`rfc_client_hello`, `rfc_next_message`, `rfc_ch_ext_check`). Everything else is signatures, grammars, vectors and citations.


## Open decisions (each needs a controller ruling; recommendation given)

1. **Hand-written specs; no `vest_lib` in `tls`.**
   - Vest's approach is reused (literal §3 presentation-language transcription, exec ≡ spec), but no Vest code. vest_lib 0.2.2 ships no TLS formats, and the alert-per-failure split plus the extension-block rules aren't combinator properties.
   - This extends the 2a/3b ruling.

   *Recommend: accept.*
2. **Proof scope.**
   - Exec ≡ spec everywhere.
   - Canonicity is proven for `pl`, the handshake header, the extension list and the ClientHello field layer. It is not proven for the typed `ClientHello` (which deliberately drops unknown extensions) or for the nested extension-body grammars. The transcript hashes raw bytes, so nothing depends on it.
   - No client-side parsers: server messages are checked as `out == old ++ spec_bytes` plus byte-exact RFC 8448 and RFC 9001 vectors.

   *Recommend: accept.*
3. **`MAX_HS_BODY = 2¹⁶`, with CRYPTO_BUFFER_EXCEEDED (0x0d) when exceeded.** That is RFC 9000 §20.1's "more data in CRYPTO frames than it can buffer". The alternative is internal_error (0x150), RFC 8446's "unrelated to the peer". RFC 8446 names neither. *Recommend: 0x0d.*
4. **The message type is checked at its first byte** (unexpected_message before the length or body is buffered), so a refused message never costs buffer. *Recommend: accept.*
5. **Any cookie in a ClientHello is illegal_parameter**, because we never issue one (the matrix binding note), and the HRR carries no cookie. *Recommend: accept.*
6. **RFC 9001 §8.4's SHOULD is taken:** a non-empty legacy_session_id is PROTOCOL_VIOLATION.
   - curl, Chrome, Firefox and quiche all send it empty in QUIC.
   - The serializer still takes `session_id_echo`, so the §4.1.3 echo stays literal if this is overruled.

   *Recommend: accept.*
7. **Alerts the RFC doesn't name:** a duplicate extension is illegal_parameter (§6, "syntactically correct but semantically invalid"), and pre_shared_key without psk_key_exchange_modes is missing_extension (the §9.2 analogue). *Recommend: accept.*
8. **The CH-forbidden set is {oid_filters}.**
   - It is the only RFC 8446 §4.2 table entry not allowed in a ClientHello. quic_transport_parameters is CH/EE.
   - We "recognize" it only to reject it.

   *Recommend: accept.*
9. **The ten-step validation order in Task 5** decides which alert wins when a ClientHello has several faults. Syntax goes first, then extension-block rules, then version, then field semantics, then missing extensions. *Recommend: accept as written; the order pins in `ch_errors` lock it.*
10. **`serialize_server_hello` takes the group and key as parameters** (key length 1..=256), not a P-256 constant. RFC 8448 §3 and RFC 9001 A.3's X25519 ServerHellos then test the same code. 4b only ever passes secp256r1. *Recommend: accept.*
11. **EncryptedExtensions is exactly ALPN `h3` plus quic_transport_parameters**, with `h3` as a `tls::codes` constant, and no server_name acknowledgement. server_name is parsed but unused: a single-certificate server is not "capable of using it" (§9.2). *Recommend: accept.*
12. **The curl ClientHello fixture is committed** (1532 bytes, a binary in `crates/tls/tests/data/`) as the one real-world vector. It exercises a large post-quantum key share, a two-datagram ClientHello and HRR-forcing shares. *Recommend: accept; re-capture with `<scratch>/chk4/cap.py` when curl is upgraded.*

## Controller rulings (2026-10-28)

All 12 open 4a decisions and all 9 outline decisions are accepted as recommended.
- 4a #3, CRYPTO_BUFFER_EXCEEDED: RFC 9000 §7.5 names this code for exceeding a CRYPTO buffer, so it fits.
- 4a #6: RFC 9001 §8.4's SHOULD is taken, as recommended.
- 4a runs in parallel with Phases 2b, 3a and 3b, branched from main. The `requirements.md` and `lib.rs` conflicts get resolved at merge time by keeping both sides.
