# Phase 4a–4c outlines: TLS 1.3 server and QUIC-TLS (4a planned in full; 4b and 4c later)

Each outline is meant to become a full writing-plans document in the house style of `2026-10-28-phase-3e-protection-shell.md`:
- Global Constraints;
- the four checks, with fresh-`CARGO_TARGET_DIR` evidence;
- Duvet citations (`//= https://www.rfc-editor.org/rfc/rfc8446#section-X` or `…/rfc9001#…`, plus a contiguous `//#` quote);
- per-task `✅ 4x: <file>` matrix commits;
- a Review Focus section;
- a suggested model per task.

4a's full plan is `2026-10-28-phase-4a-tls-codecs.md`.

**Spec:** `docs/superpowers/specs/2026-10-27-verified-http3-design.md`, Phase 4, plus "Calls I made":
- server only;
- TLS_AES_128_GCM_SHA256 only;
- secp256r1 only, with HRR for X25519-only offers;
- ECDSA-P256-SHA256 and RSA-PSS-RSAE-SHA256 signing, and no RSA verification code (the RSA ruling);
- no client certificates, 0-RTT, PSK or resumption;
- ALPN `h3`;
- the certificate chain is opaque DER.

---

## Row accounting

There are 77 matrix rows whose Phase is 4: RFC 8446 has 48, RFC 9001 has 28 and RFC 9114 has 1. The 3e ruling #7 retags RFC 9001 §5.4.1 and §5.4.2 to Phase 3, which leaves **75 rows for Phase 4**. Each is owned by exactly one sub-phase: **4a 17, 4b 28, 4c 30**.

How it was checked: `python3 -I <scratch>/chk4/rows4.py <scratch>/chk4/p4rows.txt` printed `77 3e 2 4a 17 4b 28 4c 30`, and asserted that every row appears exactly once.
- Once 3e Task 1 retags §5.4.1 and §5.4.2, a regenerated file prints `75 3e 0 4a 17 4b 28 4c 30`. The 3e bucket is "whichever of the two rows are still Phase 4", checked on `<scratch>/chk4/p4rows-post3e.txt`.
- Extraction: `awk -F'|' '/^## RFC/{split($0,a," "); r=a[3]} /^\|/{s=$2; t=$3; p=$6; gsub(/^ +| +$/,"",s); gsub(/^ +| +$/,"",t); gsub(/^ +| +$/,"",p); if(p ~ /^4/) print r " " s " | " t}' docs/requirements.md`.
- `p4rows.txt` holds the `RFC § | Topic` lines extracted from `docs/requirements.md` on 2026-10-28, where Phase starts with `4`.
- Rows are named by RFC, `§` and the matrix's own `(req)` label.
- Mixed rows that an earlier sub-phase touches get a `4a codec: <file> (closed in 4b)` note (or `4b: … (closed in 4c)`), and are listed once, under their owner.

## Decisions shared by all three sub-phases

- **Crate `crates/tls`, and its dependency direction.**
  - 4a depends on `vstd` only.
  - 4b adds `crypto = { path = "../crypto" }`.
  - 4c adds `quic = { path = "../quic" }`, for the glue module only. That mirrors how 3e added `crypto` to `quic`.
  - `quic` never depends on `tls`.
  - The TLS core takes the serialized local transport parameters as bytes, and hands out the peer's `quic_transport_parameters` bytes unparsed. Only the 4c glue calls `quic::tp`.
- **Errors are `Result<_, u64>` with QUIC error codes**, as in 3b.
  - A TLS alert is `CRYPTO_ERROR_BASE + AlertDescription` (RFC 9001 §4.8). For example, decode_error is 0x132, illegal_parameter 0x12f, missing_extension 0x16d and no_application_protocol 0x178.
  - Non-alert failures use plain transport codes, such as PROTOCOL_VIOLATION for RFC 9001 §4.1.3 and §8.4, and CRYPTO_BUFFER_EXCEEDED.
  - `tls::codes` duplicates the few transport constants it needs. 4c adds a test that they equal `quic::codes`.
- **Parse only what a server receives, serialize only what it sends.**
  - Parsed: ClientHello and the client's Finished. Any other handshake type is unexpected_message when its first byte arrives, so KeyUpdate gives 0x10a (RFC 9001 §6).
  - Serialized: ServerHello, HRR, EncryptedExtensions, Certificate, CertificateVerify and Finished.
  - No client-side parser and no exec ClientHello serializer are written.
- **Hand-written specs, not Vest combinators** (open decision 3). This follows the 2a/3b ruling.
  - `vest_lib` 0.2.2 ships no TLS formats: the grep of `~/.cargo/registry/src/*/vest_lib-0.2.2` finds none.
  - What is reused is Vest's *approach*: a literal transcription of the RFC 8446 §3 presentation language, with `<floor..ceiling>` bounds, and exec code proven equal to it.
  - TLS's per-failure alert split (decode_error vs illegal_parameter vs missing_extension) and its extension-block rules (duplicates, pre_shared_key last, ignoring unknown types, the per-message table) are semantic checks that combinators don't express.
- **Canonicity is provable for TLS and is required**, unlike 3b's varint waiver: every integer has a fixed width and every vector is length-prefixed.
  - For parsed framing: `rfc_x(b) == Some(v) ⇒ spec_x_bytes(v) == b`.
  - For every serializer: `out@ == old(out)@ + spec_*_bytes(..)`.
- **Randomness.** TLS takes its own `rand: &[u8; TLS_RAND_LEN]` per call, with `TLS_RAND_LEN = 96`. That covers the 32-byte ServerHello random, the 32-byte ECDHE scalar and the 32-byte PSS salt. 3d's `RAND_LEN = 128` is already spent on CIDs.
- **Branching:**
  - `phase-4a` can branch from `main` at any time, because it has no code dependency on 3b–3e;
  - `phase-4b` needs 3a Tasks 5–6 (ECDSA, RSA-PSS) merged;
  - `phase-4c` needs `phase-3e` merged.

## Easy-to-miss MUSTs and where each lands

| MUST | Owner | How |
|---|---|---|
| legacy_session_id echo (§4.1.3) | 4a serializer, 4b binding | `serialize_server_hello(.., session_id_echo, ..)`. 4b passes `ch.legacy_session_id`. A non-empty id is already PROTOCOL_VIOLATION under RFC 9001 §8.4's SHOULD (4a open decision 6), so the echo is empty in practice. |
| HRR cookie, or its absence (§4.1.4, §4.2.2, §9.2 cookie) | 4a | The HRR serializer has no cookie. Any cookie in a ClientHello is illegal_parameter, because we never issue one. |
| Downgrade sentinel (§4.1.3) | Declined row, plus 4b | We never negotiate TLS 1.2 or older. The ServerHello random is 32 fresh shell-random bytes, independent of ClientHello.random. |
| ServerHello random (§4.1.3, Appendix C) | 4b | `rand[0..32]`, never derived from the ClientHello. |
| Ignore unknown extensions, suites, groups, versions and sig schemes (§4.1.2, §9.3) | 4a | Parsers accept every codepoint. A GREASE-laden ClientHello is a test vector. |
| Reject duplicate extensions (§4.2) | 4a | All 65,536 types, not only known ones. Linear time, with a constant-size seen table. |
| pre_shared_key must be last (§4.2.11) | 4a | illegal_parameter, checked even though PSK is declined. |
| Alert mapping: decode_error vs illegal_parameter (§6) | 4a codes and order; closed in 4c | 4a fixes a deterministic validation order. 4c turns alerts into CONNECTION_CLOSE 0x1c. |
| missing_extension (§9.2, §4.2.3, RFC 9001 §8.2) | 4a | signature_algorithms, supported_groups ⇔ key_share, psk without psk_key_exchange_modes, and quic_transport_parameters (0x16d). |
| Coalescing and fragmentation (§5.1) | 4a | `HsReader`, with a proven theorem that the result doesn't depend on how the stream is chunked. |
| Key-change boundary (§5.1 (req), RFC 9001 §4.1.3) | 4c, using 4a's `HsReader::is_empty` | Leftover lower-level data when higher keys install is PROTOCOL_VIOLATION. |
| ALPN failure "immediately" (RFC 9001 §8.1) | 4b | Checked at ClientHello time, before any HRR. 3d's `check_alpn` in `on_handshake_complete` would be too late. |
| A share only for a group in the client's supported_groups (§4.2.8) | 4b | A secp256r1 share whose group is absent from supported_groups is unusable. HRR is legal only if secp256r1 is in supported_groups. Otherwise the result is handshake_failure. |

## Facts captured on 2026-10-28 that shape the plans

- **curl 8.18.0 here is ngtcp2 1.22.1 over OpenSSL 3.5.9.** Its real Initial was captured and decrypted by `<scratch>/chk4/cap.py`:
  - **HRR is on the critical path of the very first curl fetch.** Its key shares are X25519MLKEM768 (0x11ec, 1216 bytes) and X25519 only, while supported_groups lists 0x0017.
  - **The ClientHello is 1532 bytes and spans two 1200-byte Initial datagrams.** Each datagram carries 11–19 CRYPTO frames out of offset order, and later Initials repeat the data with different splits.
  - Cipher suites are `1302 1303 1301 1304`, so 0x1301 is third. ALPN is `h3`, `h3-29`.
  - The session id is empty.
  - The fixture is `<scratch>/chk4/curl-8.18-openssl-3.5.9-ch.bin`, sha256 `78670831801f554919d42170b2a425c01e609af4b7115771c64998ba0965a581`.
- **RFC 9001 A.2's ClientHello** has ALPN `"alpn"` (not `h3`) and an X25519-only key share. It is a parse vector for 4a.
  - Through 4b it gives `0x178`, because ALPN is checked before the group.
  - Through 4c it also fails §7.3: 3d #16, `rfc9001_a2_iscid_mismatch`.
- **RFC 8448 §5 is exactly our HRR case**: the client starts with X25519, and the server asks for P-256.
  - Its P-256 ServerHello, Certificate, CertificateVerify (0x0804) and Finished are byte-exact serializer vectors, checked by `<scratch>/chk4/v8448.py`.
  - Its HRR and its second ClientHello carry a **cookie**, so under our policy that CH2 is a parse-only vector (illegal_parameter).
  - Its key-schedule values are 4b's vectors. Both P-256 private keys are printed, so `p256_ecdh` reproduces the shared secret.
- **quiche-client is not installed**, so 4c needs a build-or-obtain step.

---

## 4a — TLS message codecs and ClientHello validation (RFC 8446 §3, §4, §4.2, §9.2–§9.3, App. B/D; RFC 9001 §8.2)

**Goal:** verified, sans-IO codecs for every TLS 1.3 handshake message a QUIC server reads or writes, each proven against an RFC-transcribed spec:
- handshake-message framing across CRYPTO chunks;
- the extension block and its rules;
- the ClientHello extension bodies;
- a fully validated, typed `ClientHello` that carries the ClientHello-intrinsic alerts;
- serializers for ServerHello, HRR, EncryptedExtensions, Certificate, CertificateVerify and Finished.

Negotiation is not done here.

**Tasks** (7; full plan written):
1. `tls` crate, `codes`, and the presentation-language primitives (`pl`) with canonicity lemmas — opus.
2. Handshake framing (`HsReader`): first-byte type check, a 2¹⁶ body cap, and the chunking-independence theorem — opus.
3. The extension block: list parse, duplicates over all types, pre_shared_key last, oid_filters forbidden in a ClientHello — opus.
4. The ClientHello extension bodies (10 grammars) — sonnet.
5. `parse_client_hello`: the field layer with its canonicity theorem, plus the 10-step ordered validation — opus.
6. ServerHello, HRR and EncryptedExtensions serializers — sonnet.
7. Certificate, CertificateVerify and Finished serializers, plus `parse_finished` — sonnet.

**Key interfaces:**
- `HsReader::{new, push, next_message(expect: u8) -> Result<Option<Vec<u8>>, u64>, is_empty}`.
- `parse_client_hello(body: &[u8]) -> Result<ClientHello, u64>`, where `ClientHello` has these fields:
  - `random`, `legacy_session_id`, `cipher_suites`;
  - `versions`, `groups: Option`, `key_shares: Option<Vec<KeyShareEntry>>`;
  - `sig_algs`, `sig_algs_cert: Option`;
  - `alpn: Option<Vec<Vec<u8>>>`, `server_name: Option`;
  - `transport_params: Vec<u8>`.
- The serializers:
  - `serialize_server_hello(random, session_id_echo, group, key_exchange, out)`;
  - `serialize_hello_retry_request(session_id_echo, selected_group, out)`;
  - `serialize_encrypted_extensions(transport_params, out)`;
  - `serialize_certificate(chain, out)`;
  - `serialize_certificate_verify(scheme, signature, out)`;
  - `serialize_finished(verify_data, out)`;
  - `parse_finished(body) -> Result<[u8; 32], u64>`.

**Review Focus seeds:**
- curl's 1532-byte ClientHello, delivered in arbitrary chunks;
- GREASE everywhere;
- duplicate *unknown* extensions;
- pre_shared_key not last;
- 16,383 empty extensions.

**Matrix rows it closes (17):**
- RFC 8446:
  - §4.2.1, §4.2.2, §4.2.6, §4.2.9, §4.2.10, §4.2.11;
  - §4.4.2 (req) "RawPublicKey certificate type";
  - §4.4.2.1, §4.5;
  - §9.2, plus §9.2 (req) "MUST implement ... cookie";
  - §9.3;
  - Appendix B and Appendix D.
- RFC 9001: §4.2, §4.4, §8.2.

---

## 4b — Key schedule, signing and the server handshake state machine (RFC 8446 §2, §4.1–§4.4, §7, §9.1)

**Goal:** a verified, sans-IO `ServerHandshake`.
- **Inputs:** handshake bytes per encryption level, the server config (chains and keys), the local transport-parameter bytes and `TLS_RAND_LEN` random bytes.
- **Outputs:**
  - handshake bytes per level;
  - traffic secrets per level;
  - the peer's transport-parameter bytes;
  - a completion event;
  - or an error code.
- Every transition is allowed by the RFC 8446 Appendix A server diagram, restricted to ours: no PSK, no 0-RTT, no client authentication.
- The key schedule is proven against an RFC 8446 §7.1 transcription over the 3a HKDF and HMAC specs.

**Tasks** (7):
1. `tls::hkdf_label`: HKDF-Expand-Label and Derive-Secret (§7.1) as spec plus exec over `crypto::hkdf_*`. Vectors are RFC 8448's printed `info` strings and outputs — opus.
2. `tls::transcript` and `tls::schedule`:
   - the transcript is a byte buffer, rehashed with one-shot `sha256` on demand (`// ponytail:`, since 3a has no streaming hash);
   - for HRR, the buffer is replaced with `message_hash(254) ‖ 00 00 20 ‖ Hash(CH1)` (§4.4.1);
   - the early secret has no PSK (an all-zero IKM); then the handshake and master secrets, the four traffic secrets, `finished_key` and `verify_data`;
   - RFC 8448 §5 vectors, end to end. The ECDHE secret comes from `p256_ecdh` on the trace's keys, so §7.4.2's "no truncation" is pinned by the 32-byte array — opus.
3. `tls::negotiate`, a pure function `negotiate(ch: &ClientHello, cfg: &ServerConfig, after_hrr: bool) -> Result<Choice, u64>`. The check order is fixed, so a doomed CH1 fails before any HRR:
   1. 0x1301 is offered, else handshake_failure;
   2. ALPN contains `h3`, else 0x178 (an absent ALPN is 0x178 too);
   3. a configured chain whose key type has a matching scheme: 0x0403 for P-256, 0x0804 for RSA. Prefer one whose chain fits `sig_algs_cert` (or `sig_algs`); else handshake_failure;
   4. the group: a usable secp256r1 share (in supported_groups) → `Proceed`; secp256r1 in supported_groups with no share and `!after_hrr` → `Retry`; else handshake_failure. After HRR, a CH2 without exactly one secp256r1 share is illegal_parameter.

   This closes §4.1.1, §4.2.3 and its (req) rows, §4.2.8, §4.4.2.2 and §9.1. It also fixes the stale "ECDSA-only" note on the §4.4.2.2 row (carry-over) — opus.
4. `tls::sign`: CertificateVerify content, which is 64×0x20 ‖ "TLS 1.3, server CertificateVerify" ‖ 0x00 ‖ Transcript-Hash (§4.4.3), pinned by the RFC's 32×01 example.
   - ECDSA uses `p256_ecdsa_sign` and then `serialize_ecdsa_der`.
   - RSA uses `rsa_pss_sha256_sign` with `salt = rand[64..96]`.
   - `None` from either is internal_error — sonnet.
5. The server flight builder:
   - the ServerHello: `random = rand[0..32]`, the echo, and a P-256 share from `scalar = rand[32..64]` via `p256_public_key` (`None` → internal_error, `// ponytail:` probability ≈ 2⁻³²);
   - EncryptedExtensions with the local TP bytes;
   - Certificate, CertificateVerify and Finished;
   - the `TlsEvent`s in order, with SH at Initial and EE…Finished at Handshake.

   This closes §4.1.3, §4.3.1 (EE immediately after SH), §4.4.2, §4.4.3 and §4.4.4 (server side) — opus.
6. The state machine `ServerHandshake`:
   - states `Start → [HrrSent →] WaitFinished → Complete`, with `Failed` absorbing; one `HsReader` per level;
   - CH2 rules: no second HRR, and the same cipher suite (§4.1.4);
   - the client Finished is checked against `verify_data`, decrypt_error on mismatch;
   - anything else, including a ClientHello after the handshake (§4.1.2) and KeyUpdate (§4.6.3 (req), RFC 9001 §6), is unexpected_message;
   - secrets are dropped on `Failed` (in support of §6, which closes in 4c);
   - `pending(level)` exposes `!HsReader::is_empty()` for 4c's boundary rule.

   This closes §2, §2.1, §4, §4.1.2, §4.1.4, §4.2, §4.6.3 and its (req) row, §7.5 (no exporter secret is derived; QUIC uses none), Appendix C, Appendix E, RFC 9001 §6 and §8.1, and RFC 9114 §7.2.4.2 (req) (never 0-RTT) — opus.
7. An in-memory end-to-end test against an independent client: rustls 0.23.45 `quic::ClientConnection` with the ring provider, both already in the local registry, as a **dev-dependency** (open decision 5). It covers:
   - the HRR path (rustls's default key share is X25519);
   - an ECDSA chain and an RSA chain;
   - the ALPN mismatch giving 0x178;
   - A.2's ClientHello giving 0x178.

   Sonnet.

**Key interfaces:**
- `pub struct ServerConfig { pub chains: Vec<CertChain> }`, `pub struct CertChain { pub der: Vec<Vec<u8>>, pub key: SigningKey }`, and `pub enum SigningKey { EcdsaP256([u8; 32]), Rsa(crypto::rsa::RsaPrivateKey) }`.
- `pub enum Level { Initial, Handshake, OneRtt }`.
- `pub enum TlsEvent { Send { level: Level, data: Vec<u8> }, Secrets { level: Level, client: [u8; 32], server: [u8; 32] }, PeerParams(Vec<u8>), Complete }`.
  - `PeerParams` is emitted once, for the ClientHello answered with a ServerHello.
  - `Secrets` for `OneRtt` comes with the server Finished. 3d keeps 1-RTT receive disabled until `on_handshake_complete`.
- `ServerHandshake::new(cfg: &ServerConfig, local_tp: Vec<u8>) -> ServerHandshake`.
- `fn on_crypto(&mut self, level: Level, data: &[u8], rand: &[u8; TLS_RAND_LEN], ev: &mut Vec<TlsEvent>) -> Result<(), u64>`.
- `fn pending(&self, level: Level) -> bool` and `fn is_complete(&self) -> bool`.
- `pub open spec fn spec_hkdf_expand_label(secret: Seq<u8>, label: Seq<u8>, context: Seq<u8>, len: nat) -> Seq<u8>`, which 4c reuses for the "quic key", "quic iv", "quic hp" and "quic ku" labels.

**Proof obligations:**
- every emitted `Send` sequence equals the spec flight for the negotiated `Choice`;
- the traffic secrets equal the spec schedule over the exact transcript bytes;
- `Complete` is emitted iff a client Finished matched;
- no `Send` after `Failed`.

**Review Focus seeds:**
- a CH2 with two secp256r1 shares;
- a CH2 that drops 0x1301;
- a secp256r1 share with secp256r1 absent from supported_groups;
- client Finished coalesced with trailing bytes;
- ALPN `h3-29` only;
- an RSA-only config and a client that lists only 0x0403.

**Matrix rows it closes (28):**
- RFC 8446:
  - §2, §2.1, §4, §4.1.1, §4.1.2, §4.1.3, §4.1.4, §4.2;
  - §4.2.3, plus (req) "RSA signature scheme requirements …" and (req) "Deprecated algorithms MUST NOT be offered or negotiated …";
  - §4.2.8, §4.3.1, §4.4.2, §4.4.2.2;
  - §4.4.3, plus (req) "RSA signatures MUST use an RSASSA-PSS algorithm";
  - §4.4.4;
  - §4.6.3, plus (req) "Implementations that receive a KeyUpdate message …";
  - §7.4.2, §7.5, §9.1;
  - Appendix C and Appendix E.
- RFC 9001: §6, §8.1.
- RFC 9114: §7.2.4.2 (req) "Server MUST NOT accept 0-RTT if settings compatibility unknown".

---

## 4c — QUIC-TLS glue, Initial secrets, key update, and first interop (RFC 9001 §4–§6; RFC 8446 §5–§6)

**Goal:**
- connect `ServerHandshake` to 3d's TLS boundary methods (`crypto_read`, `crypto_write`, `on_peer_params`, `on_handshake_complete`, `on_tls_alert`) and to 3e's `pipeline` key slots;
- derive Initial secrets for any DCID, retiring 3e's A.1-only `initial_keys` shim and its TRUSTED.md row;
- implement QUIC key update and the AEAD limits;
- switch the shell to `H3Server` plus `pump`;
- meet the design-spec Phase 4 exit: `curl --http3` and the quiche client fetch a response.

**Tasks** (7; Tasks 6–7 are the split point. If the full plan overruns 8 tasks, they become 4d, which is off the first-interop path):
1. **`tls::quic_keys`:**
   - `initial_salt = 0x38762cf7f55934b34d179ae6a4c80cadccbb7f0a`, `initial_secret = HKDF-Extract(salt, dcid)`, and "client in"/"server in" (§5.2);
   - "quic key"/"quic iv"/"quic hp" (§5.1), producing 3e's `PacketKeys`;
   - test: RFC 9001 A.1 byte-exact for DCID `8394c8f03e515708`;
   - delete `server::initial_keys` and its TRUSTED.md row, and replace its call site;
   - add the `tls::codes` = `quic::codes` equality test;
   - opus.
2. **`tls::quic::QuicServer`**, the glue. It composes `quic::pipeline::{accept_datagram, receive, transmit}`, `H3Server` and `ServerHandshake`. After every packet's frames (not per datagram; see Review Focus) it:
   1. reads `crypto_read` per level and passes it to `on_crypto`;
   2. turns `Send` into `crypto_write` at that level;
   3. turns `Secrets` into `PacketKeys` in the `[Option<KeyPair>; 3]` slots, receive keys only once `!pending(lower level)`. Otherwise it closes with PROTOCOL_VIOLATION (§4.1.3, RFC 8446 §5.1 (req));
   4. passes `PeerParams` through `quic::tp::parse_transport_params(_, true)` (TRANSPORT_PARAMETER_ERROR) and then `on_peer_params`;
   5. turns `Complete` into `on_handshake_complete(b"h3")`;
   6. turns `Err(code)` into `on_tls_alert(code − 0x100)`, or `close(code)` for transport codes (§4.8, RFC 8446 §6, §6.2).

   Tests: A.2's ClientHello under derived keys gives `0x178` with a CONNECTION_CLOSE in an Initial. 3e retransmits CRYPTO per space, so data is resent under its original keys (§4). Opus.
3. **Key discard and the "replaced by QUIC" rows:**
   - Initial key slots are cleared in lockstep with 3d's `discard(Initial)` on the first processed Handshake packet, and Handshake slots on completion (§4.9, §4.9.1, §4.9.2; §4.9.3 vacuous);
   - HANDSHAKE_DONE goes out via 3d (§4.1.2);
   - 0-RTT: §4.6.2, §5.6, §8.3 (3e drops 0-RTT packets) and §5.7 (3d drops 1-RTT before complete);
   - RFC 8446 §5, §5.1, §5.2, §5.3, §5.4 and §6.1 get Duvet "replaced by QUIC" citations with reasons.

   Sonnet.
4. **The shell:**
   - `server [--cert chain.pem --key key.pem] [ADDR]`;
   - PEM, PKCS#8 P-256 and PKCS#8 RSA loading, trusted, with a TRUSTED.md row (open decision 4);
   - TLS randomness from `libc::getrandom`;
   - drive `QuicServer` and `H3Server::pump`;
   - cap connections (`// ponytail:` a fixed `MAX_CONNS`), replacing 3e's uncapped list.

   Sonnet.
5. **First interop:**
   - `curl --http3-only -k https://localhost:4433/` returns the static body;
   - `quiche-client` is built from a pinned quiche tag (`apps/`) outside the workspace, then `quiche-client --no-verify https://localhost:4433/` succeeds;
   - both runs are recorded in the task report;
   - `<scratch>/chk4/cap.py` serves as a decrypting capture aid. It covers HRR plus a two-Initial ClientHello, which is curl's real path.

   Sonnet.
6. **Key update, receiving and responding** (§5.5, §6.2, §6.3, §6.4):
   - the 1-RTT slot becomes `OneRtt { phase, current, next_rx, prev_rx }`, with "quic ku" for the next secret (HP keys unchanged);
   - the key-phase bit is checked in 3e's `rfc_unprotect` and set in `rfc_protect`;
   - old receive keys are retained until a packet under the new keys is unprotected;
   - KEY_UPDATE_ERROR on a lower PN that unprotects under old keys after a newer key was seen;
   - send keys are updated before the ACK.

   Opus.
7. **Initiating, and AEAD limits** (§6.1, §6.6, §9.5):
   - no initiation before confirmation, and no second initiation before an ACK in the current phase;
   - a per-key encrypted-packet count with server-initiated update before 2²³ (the AES-128-GCM confidentiality limit);
   - a per-connection failed-auth count with AEAD_LIMIT_REACHED at 2⁵²;
   - the §9.5 timing MUSTs stay a TRUSTED.md known gap;
   - a `scripts/verify.sh` re-run with all crates.

   Opus.

**Key interfaces:**
- `tls::quic_keys::{initial_keys(dcid: &[u8]) -> KeyPair, packet_keys(secret: &[u8; 32]) -> PacketKeys, next_secret(secret: &[u8; 32]) -> [u8; 32]}`, each with an `ensures` over `spec_hkdf_expand_label`.
- `tls::quic::QuicServer::{accept, receive, transmit, on_timeout, is_closed}`. These mirror 3e's pipeline signatures, with `tls_rand: &[u8; TLS_RAND_LEN]` added.
- 3e's `[Option<KeyPair>; 3]` becomes `Keys { initial: Option<KeyPair>, handshake: Option<KeyPair>, one_rtt: Option<OneRtt> }`. This is a signature change to `quic::pipeline`, made in Task 6.

**Proof obligations:**
- keys for level L install only when lower-level receive data is fully consumed;
- no packet is ever protected with discarded keys;
- after a key update, packets with higher PNs use the same or newer keys (§6.4);
- encrypted-packet count < 2²³ per key.

**Review Focus seeds:**
- **A datagram that coalesces Handshake (client Finished) with a 1-RTT request.** 3d drops 1-RTT until `on_handshake_complete`, so the glue must run TLS between packets of one datagram, or the request waits for a client PTO.
- curl's two-Initial ClientHello with shuffled, overlapping CRYPTO frames;
- a key-phase flip before confirmation;
- CH2 in a datagram under 1200 bytes, which 3d drops;
- a client ACK-only Initial after the server installed Handshake keys.

**Phase 4 exit (design spec):**
- proofs verify;
- RFC 9001 Appendix A reproduces byte-for-byte. A.1 is derived (Task 1), and A.2/A.3 protect under the derived keys (3e tests rerun with `initial_keys`). A.4 is Retry (declined) and A.5 is ChaCha20 (declined): both N/A;
- `curl --http3` and the quiche client fetch a response.

**Matrix rows it closes (30):**
- RFC 8446:
  - §5, §5.1, plus §5.1 (req) "Handshake messages MUST NOT span key changes …";
  - §5.2, §5.3, §5.4;
  - §6, §6.1, §6.2.
- RFC 9001:
  - §4, §4.1.2, §4.1.3, §4.6.2, §4.8;
  - §4.9, §4.9.1, §4.9.2, §4.9.3;
  - §5.2, §5.3, §5.5, §5.6, §5.7;
  - §6.1, §6.2, §6.3, §6.4, §6.6;
  - §8.3, §9.5.

---

## Open decisions (each needs a controller ruling; recommendation given)

1. **Three sub-phases with 7 tasks each.** 4c Tasks 6–7 (key update, AEAD limits) are the pre-agreed split point into a 4d if 4c's full plan overruns. *Recommend: accept.*
2. **Dependency direction:** `tls → crypto` (4b) and `tls → quic` (4c glue only). `quic` never depends on `tls`, and TP bytes cross the TLS core unparsed. *Recommend: accept.*
3. **Hand-written specs, no `vest_lib` in `tls`**, with Vest's approach (literal presentation-language transcription, exec ≡ spec) reused but no Vest code. This extends the 2a/3b ruling. *Recommend: accept.*
4. **Certificate metadata is trusted config.**
   - The key type comes from the shell's parsed private key (P-256 or RSA). The chain stays opaque DER.
   - §4.4.2.2's X.509v3, keyUsage digitalSignature and chain-signature compatibility MUSTs are met by an operator-supplied chain, recorded in a TRUSTED.md row: "configured chain matches its key and permits digitalSignature".
   - §4.4.2.2's own fallback for chain signatures is a SHOULD.

   *Recommend: accept. The alternative is an X.509 parser, which the design spec rules out.*
5. **rustls 0.23.45 plus ring as a `tls` dev-dependency** for 4b's in-memory end-to-end test. It is test-only, so the trusted base is unchanged. Both are already in `~/.cargo/registry`. *Recommend: accept. Without it, the first independent check of the handshake is 4c's interop.*
6. **TLS randomness is a separate `[u8; 96]` per `on_crypto` call.** An invalid ECDHE scalar is internal_error rather than a resample (`// ponytail:` ≈ 2⁻³²). *Recommend: accept.*
7. **Negotiation order: suite, ALPN, scheme/chain, then group**, so ALPN failure is "immediate" (RFC 9001 §8.1) and a doomed CH1 never gets an HRR. A.2 is pinned to `0x178`. *Recommend: accept.*
8. **TLS runs after each packet, not after each datagram** (4c Task 2), so a client Finished coalesced with 1-RTT data completes the handshake before the 1-RTT packet is processed. *Recommend: accept. It needs a per-packet hook in 3e's `receive`, which is a small signature change.*
9. **quiche-client is built from a pinned quiche release tag**, outside the workspace and outside the trusted base (it is a test tool). *Recommend: accept, and record the tag and commit in the 4c task report.*

## Controller rulings (2026-10-28)

All 9 outline decisions are accepted as recommended. 4b starts after 3a merges; 4c starts after 3e merges.
- 4c obligation (from 4a Task 2): bound total bytes pushed into HsReader per space; 3c's MAX_CRYPTO_BUFFER caps it if push is fed only from in-order CRYPTO data.
- **4b binding note (from 3a final review, I2):** `rsa_key_wf` includes primality of p and q, which no verified code can establish. 4b must define `ServerConfig::wf()` (including `rsa_key_wf` for RSA keys and the P-256 scalar range for ECDSA keys), require it on `ServerHandshake::new`, and add a TRUSTED.md row: "the trusted PKCS#8 loader in the shell establishes ServerConfig::wf()". Use 3a's exported length lemmas (`lemma_spec_sha256_len`, `lemma_i2osp_len`, `lemma_spec_hkdf_expand_len`) for key-schedule array sizes.

- **4c binding note (4b Task 6 review, minor 8):** RFC 9001 §4.1.3 wants PROTOCOL_VIOLATION when CRYPTO data arrives at a level that is no longer current. `tls::server::on_crypto` returns 0x10a (unexpected_message) for that case. The 4c glue must check the level before calling `on_crypto`, and close with PROTOCOL_VIOLATION itself.
- **4c binding notes (4b final review):**
  - `QuicServer::new` carries `requires cfg.wf()`; the PKCS#8/chain loader stays outside `verus!` (trusted, TRUSTED row exists).
  - `chain_schemes` needs an owner in 4c Task 4 (the shell must list the SignatureSchemes signing non-anchor certificates).
  - Keep the error-code range test: `on_crypto` may return 0x0a and 0x0d as well as 0x1xx alerts.
  - RFC 8446 §6.2 "MUST forget" / secret lifetime: 4c owns key lifetime; wipe traffic secrets on Failed and after installing keys (4b leaves a ponytail at the Failed transition).
