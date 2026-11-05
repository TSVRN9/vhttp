# Phase 4c: QUIC-TLS Glue, Initial Secrets and First Interop — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Connect 4b's verified `ServerHandshake` to 3d/3e's verified `Connection` and pipelines, so that:
- Initial keys are derived for any DCID (RFC 9001 §5.2), retiring the shell's A.1-only `initial_keys` shim;
- TLS bytes, secrets, peer transport parameters, completion and errors cross the boundary as RFC 9001 §4 requires;
- the unverified shell serves HTTP/3 with a P-256 certificate;
- `curl --http3` and the quiche client fetch a response, which is the design spec's Phase 4 exit.

**Split (decided):** QUIC key update and the AEAD limits (outline Tasks 6–7) move to a **Phase 4d**.
- With them, this plan has 6 + at least 3 tasks, because key update alone touches `rfc_unprotect`, the pipeline key signature, and the sent-packet key-phase tracking in `conn.rs`. That is more than the 8-task ceiling.
- Neither interop nor the Phase 4 exit needs key update.
- 4c closes 22 of its 30 rows; the other 8 are listed under "Matrix rows".

**Architecture:**
- **A new verified crate, `crates/quictls`** (ruling: quictls crate), holds all QUIC-TLS code. Importing any `quic` item into `tls` pulls `vest_lib`'s default broadcast lemmas into every tls module, and tls then fails at rlimit 4: `spec_drain` goes from 0.45M to 19.1M, and `build_flight` from 11.65M to 16.5M. So `tls` stays free of `quic`.
- **`quictls::keys`** (verified): RFC 9001 §5.1–§5.2 key derivation over 4b's `spec_hkdf_expand_label`, producing 3e's `quic::aead::{PacketKeys, KeyPair}`.
- **`quictls::server::QuicServer<'a>`** (verified): the glue. It owns an `H3Server` (which owns the `Connection`), a `ServerHandshake<'a>` and the three key slots.
  - After the pipeline has handed a datagram's packets to the connection, it reads `crypto_read` per level and feeds `on_crypto`. Then it applies the events in order: `Send` becomes `crypto_write`, `Secrets` become key slots, `PeerParams` go to `on_peer_params`, `Complete` goes to `on_handshake_complete`, and an `Err` becomes a close.
  - It clears a key slot in the same call in which the connection discards that space.
  - It lives in `quictls::server`, not the outline's `tls::quic` (ruling: quictls crate).
- **TLS between packets** (Decision 8 as built; Ruling D1): a datagram's 1-RTT packet is always its last packet. Before completion it is gated by `pipeline::receive` (RFC 9001 §5.7).
  - If TLS completes while that datagram is being processed, `pipeline::refeed_one_rtt` opens the same datagram again with only the 1-RTT slot keyed. It hands the 1-RTT packet to the connection with length 0 (the bytes were already counted), but only if its DCID equals the datagram's first header's (RFC 9000 §12.2).
  - No other packet in a client datagram can depend on TLS output from the same datagram: a client has no Handshake keys before it has read our ServerHello. So this is "TLS after each packet" for every datagram a client can send. It is also the 3e binding note's hold-and-re-feed (3e Decision 20).
- **Dependency direction** (ruling: quictls crate): `quictls → tls, quic, crypto`. `tls` does not depend on `quic`, and `quic` does not depend on `tls`. `server → quictls, tls, quic, h3`: `tls` for `ServerConfig`, `CertChain`, `build_config` and `p256_signing_key`; `h3` per preflight I5.
- **The shell** drives `QuicServer` instead of `Connection`. It loads a PEM chain and a PKCS#8 P-256 key, and answers every request with one static response. The ServerConfig it builds outlives the run loop, so `Server<'a>` borrows it.

**Tech Stack:** Verus 0.2026.10.04.426d8b0 (rustc 1.98.1), vstd `=0.0.0-2026-10-04-0306`, duvet 0.4.3. Test-only: rustls `=0.23.45` with ring `=0.17.14` (tls dev-dependencies since 4b), curl 8.18.0 (ngtcp2 1.22.1, OpenSSL 3.5.9), and quiche-client built from a pinned release tag outside the workspace. No new normal dependency.

**Spec:** `docs/superpowers/specs/2026-10-27-verified-http3-design.md`, Phase 4 exit: "proofs verify; RFC 9001 Appendix A sample packets reproduce byte-for-byte; **first real interop**: `curl --http3` and the quiche client fetch a response".

Also read (their Interfaces and binding notes are this plan's contract):
- `docs/superpowers/plans/2026-10-28-phase-4-outlines.md`: §4c, Open decisions, and Controller rulings (2026-10-28), including the 4c binding notes;
- `docs/superpowers/plans/2026-11-03-phase-3e-packet-protection-shell.md`: Architecture, Global Constraints, Task 5–7 Interfaces, Binding notes for later phases (Phase 4), Decisions 4, 14, 17, 20 and 21;
- `.superpowers/archive/3e-ledger.md` in the main checkout: rulings C1–C28 and the Task 1–5 rulings, especially §9.5, the I1 error gate and C4's residual style;
- `docs/superpowers/plans/2026-10-28-phase-4b-tls-handshake.md`: the `ServerHandshake`, `TlsEvent`, `ServerConfig::wf` and `pending` contracts.

`<scratch>` is `/home/tavern/Projects/rust/web-server/.worktrees`. Evidence goes in `<scratch>/vt-4c-evidence/` (never /tmp).

## Global Constraints

- **3e's Global Constraints apply unchanged**, except where this list says otherwise:
  - **Duvet citations:** `//= https://www.rfc-editor.org/rfc/rfc9001#section-X` (or `rfc8446`, `rfc9000`) plus a contiguous `//#` quote copied verbatim from `.duvet/specifications/www.rfc-editor.org/rfc/`. A vacuous or replaced MUST uses `//= type=exception` and `//= reason=…`.
  - **rlimit:** every function verifies at `--rlimit 4`. Use `#[verifier::spinoff_prover]` and split lemmas; never raise the rlimit.
  - **Verified code:** sans-IO, with no closures or trait objects in verified exec code, no panics, and no allocation sized by an untrusted length before it is checked.
  - **Imports:** glob-only for spec items; add `Spec*` twins for new pub structs with array or `Vec` fields.
  - **Matrix:** `✅ 4c: <file>`. A row's earlier touched note is *replaced*, not appended to.
- **The four checks, every task:**
  - `scripts/verify.sh` ends `verify.sh: all crates verified, duvet ok, ct ok (10 declassify), cost 19/36, escapes accounted (0), binary ok (49 fns)`.
  - `cargo build && cargo test` with 0 warnings.
  - The escape grep (line grep and `grep -Pz`, and the bare word `axiom`) contributes 0 lines from `crates/tls`, `crates/quic` and `crates/server`.
  - `duvet report` exits 0. `.duvet/specifications` and `.duvet/requirements` are git-ignored: copy both from the main checkout into the worktree once (already done in `wt-4c` on 2026-11-05).
- **Evidence recipe (3e's), per task N:**
  - With `CARGO_TARGET_DIR=<scratch>/vt-4c-tN/target` and `CT_TARGET_DIR=$CARGO_TARGET_DIR/ct`, run build, test, `verify.sh` and `duvet report`.
  - Then, on that warm target, run `cargo clean -p <crate>` and `rm -rf $CARGO_TARGET_DIR/verus-partial/*/.fingerprint/<crate>-*`, followed by `(cd crates/<crate> && cargo verus verify -- --rlimit 4)` for every verified crate the task edits (ruling: quictls crate):
    - `quictls` in Tasks 1 and 3;
    - `tls` in Task 3 (`server.rs`'s lemma) and Task 5 (`config.rs`);
    - `quic` in Task 2, and then `quictls` too, since it depends on quic.

    Print each `… 0 errors` line.
  - `scripts/verify.sh` needs no edit for the new crate: it loops over `crates/*/`. `ct-binary.sh` reads every workspace rlib as a dependent (ruling: quictls crate).
  - The tls run also re-checks 4b's `build_flight`, which sat at 1.03× of rlimit 4. Rank by `--output-json --time-expanded` `rlimit`. If it trips, split; never raise.
- **Quote and MUST checks:**
  - `python3 -I <scratch>/qchk/check_quotes.py --spec-dir .duvet/specifications/www.rfc-editor.org/rfc <files>` must print `N citations, 0 bad` for every file the task touched.
  - `python3 -I <scratch>/duvet_q.py <report.json> <sections>` covers the task's sections; the expected residue is named per task.
  - The baseline on `main` is 91 uncovered MUSTs across the 29 sections the 4c rows name (`<scratch>/vt-4c-evidence/duvet-base.json`). The "MUST assignment" table says which task covers each.
- **Mutations, every task with proofs:** each listed mutation, applied alone, must fail verification on a named postcondition, invariant or assertion, not on rlimit.
- **Binary gate** (ruling: quictls crate): `quictls` is a new dependent, whose `U` lines the gate records.
  - Task 1 adds `U quictls crypto::hkdf::hkdf_extract`, and any tls-inlined `crypto::hkdf` reference. Record them by the procedure below, in Task 1's feat commit.
  - If `scripts/ct-binary.sh` reports any other new `U quictls crypto::…`, `U tls crypto::…` or `U server crypto::…` line (rustc inlines small cross-crate leaf fns), follow `docs/crypto-binary-audit.md` update protocol step 2: confirm it is `U` with no `D` line, record a Gate record ("this commit on base c1329b9", toolchain, the line), run `--update`, and commit the digests and the record in the same feat commit.
  - Any `D <crate> crypto::…` line or digest change is a stop: report it.
  - Never edit `crates/crypto/src`.
- **Branch and parallel work:** `phase-4c` from `main` at c1329b9. Phase 8c runs in `wt-8c` and edits the root `Cargo.toml`, `Cargo.lock` and `scripts/verify.sh`'s final line.
  - 4c does not edit `verify.sh`.
  - 4c adds one root `Cargo.toml` block, `[profile.release.package.quictls] overflow-checks = false`, with the usual "verified" comment (ruling: quictls crate).
  - 4c changes `Cargo.lock`: Task 1 adds the `quictls` package and `server → quictls, tls`.
  - Whichever of the two merges second regenerates `Cargo.lock` with `cargo build`, keeps both sets of edges and both profile blocks, and takes 8c's final line. 8c's line today lacks `binary ok`, so that conflict exists whatever 4c does.
- **Dependencies:**
  - Task 1 creates `crates/quictls/Cargo.toml` (ruling: quictls crate):
    - `[dependencies]`: `vstd = "=0.0.0-2026-10-04-0306"`, `tls`, `quic` and `crypto` (path deps);
    - `[dev-dependencies]`: rustls `=0.23.45` (`default-features = false`, features `ring`, `std`) and ring `=0.17.14`, copied from tls's;
    - `[package.metadata.verus] verify = true`, and tls's `[lints.rust]` block.
  - Task 1 also adds `quictls = { path = "../quictls" }` and `tls = { path = "../tls" }` to `crates/server/Cargo.toml`.
  - `crates/tls/Cargo.toml` is not edited.
  - `quictls` modules see `vest_lib`'s default broadcast lemmas (through `quic`). Keep each fn small and spun off.
  - Task 5 adds `h3 = { path = "../h3" }` to `crates/server/Cargo.toml` (and `Cargo.lock`), for `Response`, `FieldLine` and `Output`, which `quic` does not re-export (preflight I5).
  - `crypto`'s normal dependencies stay exactly `vstd`; verify.sh checks this.
- **Consumed from 4b** (`crates/tls/src`; exact names):
  - `ServerHandshake::{new (requires cfg.wf(), local_tp@.len() <= 1024), on_crypto, pending, is_complete}`;
  - `theorem_event_discipline` (no `Send { OneRtt }`; every `Send { Handshake }` follows a `Secrets { Handshake }`);
  - `theorem_reader_bound` and `spec_reader`;
  - `TlsEvent`, `Level`, `TLS_RAND_LEN` (96);
  - `ServerConfig`, `CertChain { der, chain_schemes, key }`, `SigningKey`, `build_config`, `key_wf`, `chain_wf`;
  - `hkdf_label`, `hkdf_expand_label`, `hkdf_expand_label_32`, `spec_hkdf_expand_label`, `label_ok`;
  - `codes::{CRYPTO_ERROR_BASE, PROTOCOL_VIOLATION, CRYPTO_BUFFER_EXCEEDED, H3_ALPN}`.
- **Consumed from quic** (`crates/quic/src`; exact names):
  - `aead::{PacketKeys, KeyPair, SpecKeys, SpecKeyPair, MAX_UDP_PAYLOAD}`;
  - `pipeline::{initial_dcid, accept_datagram, receive, transmit, rx_keys}`;
  - `protect::{rfc_protect_datagram, protect, open_datagram}`;
  - `conn::{Connection, RAND_LEN, H3_ALPN, later}`, and `Connection::{crypto_read, crypto_write (requires !OneRtt), on_peer_params (requires peer_tp_wf), on_handshake_complete, on_tls_alert(u8), close (requires code <= VARINT_MAX), local_params (ensures server_tp_wf), handshake_complete, next_timeout, on_reset_candidate, poll_cid_updates, is_closed, path_state, largest_pn, live, out_log, timers_later, keeps_later}`;
  - `h3_server::{H3Server, AppEvent, SendError, app_grew}` and `H3Server::{new, conn, conn_mut, pump, on_timeout, send_response, wf, history_ok, conn_spec}`;
  - `tp::{TransportParams, parse_transport_params, theorem_peer_tp_wf, serialize_server_params, MAX_SERVER_TP_LEN (174), default_transport_params}`;
  - `codes::{TRANSPORT_PARAMETER_ERROR, INTERNAL_ERROR, MAX_CID_LEN}`;
  - `route::CidUpdate`, `datagram::PathId`.
- **Randomness:** each `QuicServer::accept` and `receive` takes one `Rand { conn: [u8; RAND_LEN], refeed: [u8; RAND_LEN], complete: [u8; RAND_LEN], tls: [u8; TLS_RAND_LEN] }`, filled fresh by the shell:
  - `conn` goes to the pipeline (`accept_datagram` or `receive`);
  - `refeed` goes to `refeed_one_rtt`, a second `on_datagram` call (preflight I1);
  - `complete` goes to `on_handshake_complete` (its CIDs and spin bit);
  - `tls` goes to `on_crypto`.

  `on_timeout` takes a fresh `[u8; RAND_LEN]`. No random array is passed to two `Connection` calls (3e shell rule).
- **Shared test data:**
  - quictls tests (ruling: quictls crate) load quic's `crates/quic/tests/common/mod.rs` with `#[path = "../../quic/tests/common/mod.rs"] mod qc;`, for `A2`, `A3`, `A2_CRYPTO`, `A3_PAYLOAD`, `CLIENT`, `SERVER`, `S1`, `C1`, `L0`, `rnd`, `ltp` and `ptp`.
  - They load tls's `crates/tls/tests/common/mod.rs` with `#[path = "../../tls/tests/common/mod.rs"] mod tc;`, for `CURL_CH`, `A2_CH`, `split_ch`, `join_ch`, `head`, `h3_ch`, `P256_SHARE`, `X25519_SHARE`, `ecdsa_cfg()`, `ECDSA_CERT` and `ECDSA_D`.
    - Its `include_bytes!("../data/…")` resolves relative to that file, so it still finds tls's `tests/data`.
    - It names `crypto::rsa`, so `crypto` is a normal dependency of quictls, which its tests can use.

## Matrix rows

77 Phase-4 rows; 4a closed 17 and 4b 28. 4c owns 30:
- **Closed in 4c (22):**
  - Task 1: RFC 9001 §5.2.
  - Task 2: RFC 9001 §5.7.
  - Task 3 (7): RFC 9001 §4, §4.1.3, §4.8, §4.9; RFC 8446 §5.1 (req) "Handshake messages MUST NOT span key changes …", §6, §6.2.
  - Task 4 (13): RFC 9001 §4.1.2, §4.6.2, §4.9.1, §4.9.2, §4.9.3, §5.6, §8.3; RFC 8446 §5, §5.1, §5.2, §5.3, §5.4, §6.1.
- **Moved to 4d (7):** RFC 9001 §5.3 (its third MUST: key update before the AEAD limit; Task 4 cites the other two), §5.5, §6.1, §6.2, §6.3, §6.4, §6.6. Task 4 retags their Phase to `4d` and writes a touched note on each.
- **Not met, retagged (1):** RFC 9001 §9.5 stays "not met" in TRUSTED (3e). 4c must not regress the constant-time style of `quic::{hp, aead, protect, pn}`: it edits none of those files. Task 4 retags the row Phase `4` → `7` with the note "not met: quic CT roots after 8c" (Ruling D3; preflight I3).
- Row check: `awk -F'|' '/^## RFC/{split($0,a," "); r=a[3]} /^\|/{p=$6; gsub(/^ +| +$/,"",p); if(p=="4" && $0 !~ /✅/) {s=$2; gsub(/^ +| +$/,"",s); print r " " s}}' docs/requirements.md` prints exactly the 30 rows above on `main` (checked 2026-11-05). After Task 4 it prints nothing (preflight I3).

### MUST assignment (the 91 uncovered on `main`)

| Sections | MUSTs | Owner |
|---|---|---|
| 9001 §5.2 | 1 | T1 (implementation) |
| 9001 §5.7 (client) | 1 | T2 (exception: client-only) |
| 9001 §4 (1), §4.1.3 (3), §4.8 (1), §4.9 (2), §4.9.1 (2: the discard sentence, cited for its server half, and "MUST NOT send Initial packets"), §4.9.2 (1); 8446 §5.1 (span, verify-alignment, send-alignment: 3), §6 (4), §6.2 (3) | 20 | T3 (at the glue) |
| 9001 §4.1.2 (1), §4.6.2 (2: server, client), §4.9.3 (1), §5.3 (2 of 3), §5.6 (5), §8.3 (2); 8446 §5 (5), §5.1 (the other 12), §5.2 (5), §5.3 (3), §5.4 (5), §6.1 (4) | 47 | T4 (citation, or exception with reason) |
| 9001 §5.3 (1), §5.5 (2), §6.1 (3), §6.2 (2), §6.3 (2), §6.4 (2), §6.6 (8) | 20 | 4d |
| 9001 §9.5 | 2 | not met (TRUSTED, 3e); the row is retagged to Phase 7 in T4, and its MUSTs stay uncited |

After Task 4, `duvet_q.py` over the 29 sections prints exactly the 22 lines of the last two rows, and `22 uncited MUSTs in 29 sections`.

## Review Focus

1. **A datagram that coalesces the client Finished (Handshake) with a 1-RTT request.** The request must be processed in the same `receive`, not after a client PTO. Task 4: `finished_coalesced_with_one_rtt`.
2. **curl's real ClientHello:** 1532 bytes across two 1200-byte Initials, with shuffled and overlapping CRYPTO frames, and key shares X25519MLKEM768 and X25519 only. It must get exactly one HelloRetryRequest, after the second datagram. Task 3: `curl_ch_two_datagrams_hrr`.
3. **A client Initial retransmission after our ServerHello** (the CH bytes again at offset 0, or an ACK-only Initial) must not be PROTOCOL_VIOLATION. Only new or out-of-range Initial bytes are. Task 3: `initial_retransmit_after_switch_ok`, `initial_data_after_switch_pv`.
4. **A ClientHello2 in a datagram under 1200 bytes** is dropped by 3d. The connection keeps waiting, and the same CH2 padded to 1200 bytes proceeds to a ServerHello. Task 3: `ch2_under_1200_dropped`.
5. **A TLS failure before Handshake keys exist** (A.2's ALPN `alpn`, giving 0x178) must give CONNECTION_CLOSE in an Initial only, with no 1-RTT key kept. Task 3: `a2_closes_0x178`.

---

## File Structure

- `crates/quictls/src/keys.rs` (Task 1, new): Initial secrets and packet keys, spec and exec.
- `crates/tls/src/codes.rs` (Task 1): `INITIAL_SALT` and five labels.
- `crates/quictls/src/server.rs` (Task 3, new): `QuicServer`, `Rand`, `TlsCall`, the TLS step and the event application; Task 4 adds its exception block.
- `crates/tls/src/config.rs` (Task 5): `p256_signing_key`.
- `crates/tls/src/server.rs` (Task 3): the `fail` comment, and `pub proof fn lemma_ok_not_failed` (preflight I2).
- `crates/quic/src/pipeline.rs` (Task 2): `refeed_one_rtt`; `accept_datagram`'s odcid check.
- `crates/quic/src/crypto_stream.rs` (Task 2): `CryptoStream::end` (preflight C6).
- `crates/quic/src/conn.rs` (Task 2): getters `is_live` and `crypto_end`; `odcid_spec`; one spec ensures each on `accept` and `crypto_read`; the `crx_1` comment (preflight M9).
- `crates/quic/src/h3_server.rs` (Task 2): `on_datagram` takes the datagram's error; `on_timeout` ensures `now <= now_spec` (preflight C8).
- `crates/server/Cargo.toml` (Tasks 1, 5): `tls`, then `h3` (preflight I5).
- `crates/server/src/{lib.rs, main.rs}` (Tasks 1, 5): keys from tls in Task 1; `QuicServer`, the config loader and the static response in Task 5.
- Tests: `crates/quictls/tests/{keys.rs, server.rs, e2e.rs}, crates/tls/tests/config.rs`, `crates/quic/tests/{pipeline.rs, h3_server.rs, h3_alloc.rs}`, `crates/server/tests/{shell.rs, initial_exchange.rs, interop.rs, data/*}`.

---

### Task 1: Initial secrets and packet keys (`quictls::keys`) — suggested model: sonnet

**Files:**
- Create: `crates/quictls/src/keys.rs`, `crates/quictls/tests/keys.rs`
- Modify:
  - (ruling: quictls crate) create `crates/quictls/{Cargo.toml, src/lib.rs}` (`pub mod keys;` and the crate doc line);
  - the root `Cargo.toml` (the quictls profile block), `crates/server/Cargo.toml` (`quictls`, `tls`), `Cargo.lock`;
  - `docs/crypto-binary-digests.txt` and `docs/crypto-binary-audit.md` (the new `U quictls …` lines, per the binary gate);
  - `crates/server/src/lib.rs`: delete `A1_DCID`, `A1_CLIENT`, `A1_SERVER`, `initial_keys` and its ponytail; `Route::NewInitial` uses `quictls::keys::initial_keys`;
  - `crates/server/tests/shell.rs`: delete `a1_keys_only`; its vector moves to `crates/quictls/tests/keys.rs`;
  - `TRUSTED.md`: delete the row "RFC 9001 A.1 Initial keys hard-coded in server::initial_keys …";
  - `docs/requirements.md`.

**Interfaces:**
- Consumes: `hkdf_expand_label`, `hkdf_expand_label_32`, `spec_hkdf_expand_label`, `label_ok`; `crypto::hkdf::{hkdf_extract, spec_hkdf_extract}`; `quic::aead::{PacketKeys, KeyPair, SpecKeys, SpecKeyPair}`; `quic::codes::MAX_CID_LEN`.
- Produces (`quictls::keys`, constants; tls's `codes.rs` is not edited (ruling: quictls crate)): `INITIAL_SALT: [u8; 20] = 38 76 2c f7 f5 59 34 b3 4d 17 9a e6 a4 c8 0c ad cc bb 7f 0a` (rfc9001.txt:1066), `LABEL_CLIENT_IN = *b"client in"`, `LABEL_SERVER_IN = *b"server in"`, `LABEL_QUIC_KEY = *b"quic key"`, `LABEL_QUIC_IV = *b"quic iv"`, `LABEL_QUIC_HP = *b"quic hp"`. (`"quic ku"` is 4d's.)
- Produces (`quictls::keys`):
  - `pub open spec fn rfc_initial_secret(dcid: Seq<u8>) -> Seq<u8>` = `spec_hkdf_extract(INITIAL_SALT@, dcid)`.
  - `pub open spec fn rfc_packet_keys(secret: Seq<u8>) -> SpecKeys` = `SpecKeys { key: spec_hkdf_expand_label(secret, LABEL_QUIC_KEY@, seq![], 16), iv: …(LABEL_QUIC_IV@, …, 12), hp: …(LABEL_QUIC_HP@, …, 16) }` (§5.1).
  - `pub open spec fn rfc_initial_keys(dcid: Seq<u8>) -> SpecKeyPair`, the server's view: `rx` = `rfc_packet_keys(spec_hkdf_expand_label(rfc_initial_secret(dcid), LABEL_CLIENT_IN@, seq![], 32))`, and `tx` the same with `LABEL_SERVER_IN` (§5.2).
  - `pub fn packet_keys(secret: &[u8; 32]) -> (r: PacketKeys)`: ensures `r@ == rfc_packet_keys(secret@)`.
  - `pub fn initial_keys(dcid: &[u8]) -> (r: KeyPair)`: requires `dcid@.len() <= MAX_CID_LEN`; ensures `r@ == rfc_initial_keys(dcid@)`.

- [ ] **Step 1: Failing tests** in `crates/quictls/tests/keys.rs`. Values are from rfc9001.txt §A.1, lines 2334–2380.
  - **`a1_labels`:** `hkdf_label(b"client in", &[], 32) == 00200f746c73313320636c69656e7420696e00`. Likewise `server in` gives `00200f746c7331332073657276657220696e00`, `(quic key, 16)` gives `00100e746c7331332071756963206b657900`, `(quic iv, 12)` gives `000c0d746c733133207175696320697600`, and `(quic hp, 16)` gives `00100d746c733133207175696320687000`.
  - **`a1_secrets`:**
    - `hkdf_extract(&INITIAL_SALT, &S1) == 7db5df06e7a69e432496adedb00851923595221596ae2ae9fb8115c1e9ed0a44`;
    - `hkdf_expand_label_32` of that with `client in` gives `c00cf151ca5be075ed0ebfb5c80323c42d6b7db67881289af4008f1f6c357aea`;
    - with `server in` it gives `3c199828fd139efd216c155ad844cc81fb82fa8d7446fa7d78be803acdda951b`.
  - **`a1_keys`:** `initial_keys(&S1) == KeyPair { rx: qc::CLIENT, tx: qc::SERVER }`. That is: key `1f369613dd76d5467730efcbe3b1a22d`, iv `fa044b2f42a3fd3b46fb255c`, hp `9f50449e04a0e810283a1e9933adedd2`; and key `cf3a5331653c364c88f0f379b6067e37`, iv `0ac1493ca1905853b0bba03e`, hp `c206b8d9b9f0f37644430b490eeaa314`.
  - **`a2_a3_under_derived_keys`** (Phase 4 exit, "A.2/A.3 protect under the derived keys"):
    - `protect(&OutPacket{Initial, S1, [], 2, 4, [Crypto{0, A2_CRYPTO}], 917, false}, &initial_keys(&S1).rx, &mut out)` writes exactly `qc::A2`;
    - `protect(&OutPacket{Initial, [], f067a5502a4262b5, 1, 2, [Ack(AckFrame{0, 0, 0, [], None}), Crypto{0, A3_PAYLOAD[9..]}], 0, false}, &initial_keys(&S1).tx, …)` writes exactly `qc::A3`.
  - **`codes_agree`** (outline 4c Task 1; in quictls, because tls cannot see quic (ruling: quictls crate)):
    - `tls::codes::{PROTOCOL_VIOLATION, CRYPTO_BUFFER_EXCEEDED, CRYPTO_ERROR_BASE}` each equal `quic::codes`' constant of the same name;
    - `tls::codes::H3_ALPN == quic::conn::H3_ALPN`;
    - every `tls::codes::ALERT_*` lies in `CRYPTO_ERROR_BASE..=CRYPTO_ERROR_BASE + 0xff`.
  - **`any_dcid`:** `initial_keys(&[0x83; 8]) != initial_keys(&S1)`; `initial_keys(&[0u8; 20])` and `initial_keys(&[])` return without panicking.
- [ ] **Step 2:** `cargo test -p quictls --test keys` fails to compile.
- [ ] **Step 3: Implement.**
  - Duvet-cite RFC 9001 §5.2 "The HKDF-Expand-Label function defined in TLS 1.3 MUST be used for Initial packets even where the TLS versions offered do not include TLS 1.3." at `rfc_initial_keys`.
  - Comment-cite the §5.2 `initial_salt` line at `INITIAL_SALT`.
  - Each 16- or 12-byte output comes from `hkdf_expand_label(_, _, &[], n)` (len `n`), copied into its array as `hkdf_expand_label_32` does.
  - In the shell, `Route::NewInitial` becomes `initial_dcid(d).filter(|x| x.len() <= MAX_CID_LEN).map(|x| initial_keys(&x))`, and the rest is unchanged. From here on every client's Initial is keyed, so the shell's ponytail line "A.1-only keys allow one connection in 3e" becomes "every DCID is keyed (4c): MAX_CONNS is reachable; see the 3e binding note".
- [ ] **Step 4:** The four checks; the quictls rlimit-4 run (ruling: quictls crate); `cargo test -p server` (both 3e suites still pass, since A.2's DCID derives the A.1 keys). Binary gate: the new `U quictls crypto::…` line(s) are recorded per the Global Constraints procedure (ruling: quictls crate).
  - **Mutations:** `initial_keys` uses `LABEL_SERVER_IN` for `rx` (fails its ensures); `packet_keys` derives `key` with `LABEL_QUIC_HP` (fails its ensures).
- [ ] **Step 5: Commit:** `feat(tls): verified RFC 9001 §5.1-§5.2 Initial secrets and packet keys for any DCID; the A.1-only shim retired`
- [ ] **Step 6: Matrix commit.** RFC 9001 §5.2: `✅ 4c: crates/quictls/src/keys.rs (rfc_initial_keys over spec_hkdf_expand_label; A.1 byte-exact, A.2/A.3 reproduced under derived keys)`. Commit: `docs: mark RFC 9001 §5.2 closed in 4c`.

---

### Task 2: Pipeline and connection hooks for the glue (`quic`) — suggested model: opus

**Files:**
- Modify:
  - `crates/quic/src/pipeline.rs`;
  - `crates/quic/src/crypto_stream.rs` (`end`; preflight C6);
  - `crates/quic/src/conn.rs`: two exec getters (`is_live`, `crypto_end`), two spec ensures, one closed spec, and the `crx_1` field comment "Post-handshake CRYPTO: buffered, and TLS never asks for it", which becomes "Post-handshake CRYPTO: the 4c glue reads it, and any byte is unexpected_message (0x10a)" (preflight M9). No behaviour change;
  - `crates/quic/src/h3_server.rs`.
- Test: `crates/quic/tests/pipeline.rs`, `crates/quic/tests/h3_server.rs`; `crates/quic/tests/h3_alloc.rs` (callers gain `None`)

**Interfaces:**
- Consumes: `open_datagram`/`rfc_open_datagram`, `parse_header`/`rfc_header` with `LOCAL_CID_LEN`, `gate_keys`/`rx_keys`, `open_for`, `Connection::{on_datagram, handshake_complete, live}`, `CryptoStream::read`'s ensures.
- Produces (`quic::conn`, all on `Connection`):
  - `pub fn is_live(&self, k: PacketKind) -> (r: bool)`: ensures `r == self.live(k)`.
- Produces (`quic::crypto_stream`, preflight C6): `pub fn end(&self) -> (r: u64)`: requires `self.wf()`; ensures `r == self.reassembly().base() + self.reassembly().buf_len()`. Body: `self.re.base_exec() + self.re.buf_len() as u64`, with `self.re.lemma_wf()` for the `u64` bound (reassembly.rs:253). `CryptoStream.re` is private to this file, so conn.rs cannot read it.
- Produces (`quic::conn`, all on `Connection`):
  - `pub fn is_live(&self, k: PacketKind) -> (r: bool)`: ensures `r == self.live(k)`.
  - `pub closed spec fn crypto_end_spec(&self, k: PacketKind) -> nat` = that level's CRYPTO stream `reassembly().base() + reassembly().buf_len()`. `pub fn crypto_end(&self, k: PacketKind) -> (r: u64)`: requires `self.wf()`; ensures `r == self.crypto_end_spec(k)`, through `CryptoStream::end`. It is the end of the received data in that flow (RFC 9001 §4.1.3).
  - `crypto_read` gains `final(out)@.len() <= old(out)@.len() + MAX_CRYPTO_BUFFER`. It follows from `CryptoStream::read`'s base/buf_len ensures and `CryptoStream::wf`, plus `old.base <= final.base`, from `self.crx_k.reassembly().lemma_wf()` (`base <= rfc_contiguous`, reassembly.rs:257). Without that fact the subrange has no known length (preflight M4). This discharges the controller's HsReader push-bound ruling together with `theorem_reader_bound`.
  - `pub closed spec fn odcid_spec(&self) -> Seq<u8>` = `self.ids@.odcid`. `accept` gains `r matches Some(c) ==> c.odcid_spec() == first.dcid@`.
- Produces (`quic::h3_server`, preflight C8): `H3Server::on_timeout` gains `now <= final(self).conn_spec().now_spec()`, from `Connection::on_timeout`'s ensures (conn.rs:7882) and `pump`'s `keeps_later`.
- Produces (`quic::pipeline`):
  - **`accept_datagram`** (3e binding note M4): returns `None` unless the accepting packet's DCID equals `initial_dcid(d)`. The keys the caller derives from `initial_dcid(d)` are then the odcid's keys (preflight C5):
    - New ensures: `r is Some ==> rfc_long_header(d@) matches Some(SpecHeader::Long { ty: LongType::Initial, .. })`.
    - Right after `Connection::accept` returns `c0`, a proof block asserts `c0.odcid_spec() == dcid@`, from `accept`'s new ensures and the exec comparison.
    - `ids` is *not* framed through `on_datagram`/`on_counted`. Those are big receive-path fns, and nothing consumes the fact after them.
  - **`pub fn refeed_one_rtt(c: &mut Connection, d: &[u8], path: PathId, now: u64, rand: &[u8; RAND_LEN], keys: &[Option<KeyPair>; 3])`**, requires `old(c).wf()`. Ensures:
    - `final(c).wf()` and `final(c).out_log() == old(c).out_log()`;
    - **§5.7:** `!old(c).live(PacketKind::OneRtt) ==> *final(c) == *old(c)`.

    Body order:
    ```
    if !c.handshake_complete() { return }
    first = parse_header(d, LOCAL_CID_LEN)?'s dcid                      // the datagram's first header
    rx = open_for(c, d, &[None, None, keys[2]])                          // only the 1-RTT packet can open
    if every rx.packets[i].dcid and rx.error's header dcid equals first:  // RFC 9000 §12.2
        c.on_datagram(path, 0, rx.packets, rx.error, now, rand)           // 0: already counted (§8.1)
    // rx.reset_tail is ignored: the first pass handled it
    ```
- Produces (`quic::h3_server`): `H3Server::on_datagram(…, packets, error: Option<(u64, PlainPacket)>, now, rand, app)` (3e binding note M2), requiring `error matches Some((c, h)) ==> c <= VARINT_MAX && plain_wf(h@)` and passing `error` to `Connection::on_datagram`. The glue does not call it (it uses `conn_mut` and `pipeline::receive`), but it is public, and with `None` it silently stopped §17.2/§17.3.1 closes.

- [ ] **Step 1: Failing tests.** In `tests/pipeline.rs`, with 3e's `K`, `K1`, `T`, `ini_c1` and `protected`; `HK` is arbitrary Handshake test keys, `K2 = [K[0], Some(KeyPair{rx: HK, tx: HK}), K1[2]]`, `H = protected(&OutPacket{Handshake, L0, C1, 0, 1, [Ping], 30, false}, &HK)` and `S(dcid) = protected(&OutPacket{OneRtt, dcid, [], 0, 1, [Ping], 2, false}, &T)`:
  - **`refeed_after_complete`:**
    - `c = accept_datagram(ini_c1(2, crypto(), 909), 0, 0, &rnd(1), &ltp(), &K2)`; `c.on_peer_params(&ptp(), 10)`;
    - `receive(&mut c, H ++ S(L0), 0, 10, &rnd(2), &K2)` gives `largest_pn(Handshake) == Some(0)` and `largest_pn(OneRtt) == None` (gated);
    - `c.on_handshake_complete(b"h3", 10, &rnd(3))`, then `refeed_one_rtt(&mut c, H ++ S(L0), 0, 10, &rnd(4), &K2)`, gives `largest_pn(OneRtt) == Some(0)`.
  - **`refeed_before_complete_is_noop`:** the same without `on_handshake_complete`; after `refeed_one_rtt`, `largest_pn(OneRtt) == None` and `phase()` is Open.
  - **`refeed_other_dcid_ignored`:** as `refeed_after_complete`, but with `S(rnd(3)[0..8])`, a CID `issue_cids` issued at completion, valid but not the first header's. After the refeed, `largest_pn(OneRtt) == None`.
  - **`accept_odcid_is_first_header`:**
    - `bad` is `A2` with byte 1199 XOR 1 (its AEAD fails; its Length covers all 1200 bytes);
    - `p2 = protected(&OutPacket{Initial, [0x99; 8], C1, 0, 4, [Ping], 1150, false}, &CLIENT)`, protected with S1's keys, which are public;
    - `accept_datagram(bad ++ p2, 0, 0, &rnd(1), &ltp(), &K)` is `None`;
    - `accept_datagram(A2, …, &K)` is `Some(c)` with `c.local_params().original_destination_connection_id == Some(S1.to_vec())`.
  - **`crypto_end_tracks_received`:**
    - after `accepted_a2()`, `crypto_end(Initial) == 241`;
    - `is_live(Initial)` and `is_live(Handshake)` are `true`, and `is_live(OneRtt)` is `false`;
    - then `receive` of a 1200-byte Initial (pn 3) carrying `Crypto{300, [7; 10]}`, a gapped frame, gives `crypto_end(Initial) == 310`. This pins `base + buf_len` as the high-water mark of received data.
    - If `Reassembly` leaves slack past the inserted end, this fails. Then add `lemma_crypto_end_is_max`: `crypto_end_spec` equals 1 + the largest key of `rfc_received(inserted())`, or `base` when there is none, and make `crypto_end` compute that.

  In `tests/h3_server.rs`:
  - **`h3_on_timeout_now`** (preflight C8): after `H3Server::new(established())` and `on_timeout(50, &rnd(4), &mut app)`, `conn().now() >= 50`.
  - **`h3_on_datagram_passes_error`:** `H3Server::new(established())`, then `on_datagram(0, 100, vec![], Some((0x0a, <1-RTT header from the file's builders, frames []>)), 30, &rnd(3), &mut app)`, leaves `conn().phase()` Closing.
- [ ] **Step 2:** The tests fail.
- [ ] **Step 3: Implement.**
  - Duvet-cite at `refeed_one_rtt`:
    - RFC 9001 §5.7 "Received packets protected with 1-RTT keys MAY be stored and later decrypted and used once the handshake is complete." (MAY; the extra citation);
    - RFC 9000 §12.2 "Receivers SHOULD ignore any subsequent packets with a different Destination Connection ID than the first packet in the datagram." (SHOULD).
  - Add the §5.7 client MUST "Even if it has 1-RTT secrets, a client MUST NOT process incoming 1-RTT protected packets before the TLS handshake is complete." as `type=exception`, `reason=Binds clients; the server's half is gate_keys (3e) and conn.rs's 1-RTT gate.`
  - `conn.rs` gets only the listed getters and spec ensures (3e Decision 14 style: no behaviour change). Prove the `crypto_read` bound with `CryptoStream::read`'s `base + buf_len` frame.
- [ ] **Step 4:** The four checks; the quic rlimit-4 run. It re-verifies `conn.rs` and, through quic's dependency, h3 (3d2: h3's margin is thin; split, never raise).
  - **Mutations:** drop `refeed_one_rtt`'s `handshake_complete` check (fails the §5.7 ensures); drop `accept_datagram`'s DCID comparison (fails the proof-block assert; preflight C5); drop `H3Server::on_timeout`'s new ensures' proof step (fails it; preflight C8); `is_live(Handshake)` returns `live_i` (fails its ensures); drop the `crypto_read` length bound's proof step (fails `crypto_read`).
- [ ] **Step 5: Commit:** `feat(quic): refeed of the 1-RTT packet coalesced with the client Finished (RFC 9001 §5.7), odcid equals the keys' DCID, glue getters; H3Server::on_datagram passes the error`
- [ ] **Step 6: Matrix commit.** RFC 9001 §5.7: `✅ 4c: crates/quic/src/pipeline.rs (gate_keys, 3e; refeed_one_rtt after completion, proved a no-op before it) + conn.rs (no processing before completion)`, replacing 3e's touched note. Commit: `docs: mark RFC 9001 §5.7 closed in 4c`.

---

### Task 3: The glue (`quictls::server::QuicServer`) — suggested model: opus

**Files:**
- Create: `crates/quictls/src/server.rs`, `crates/quictls/tests/server.rs`
- Modify:
  - `crates/quictls/src/lib.rs` (`pub mod server;`) (ruling: quictls crate);
  - `crates/tls/src/server.rs`:
    - the comment at `fail` (`// ponytail: secrets not wiped; zeroize on Failed/Complete when 4c owns key lifetime`) becomes `// Secrets are dropped from the state here; memory is not zeroised (TRUSTED: secret lifetime).`;
    - add `pub proof fn lemma_ok_not_failed`, which needs 4b's private `lemma_drain_events` and `spec_call_shape` (preflight I2);
  - `TRUSTED.md`;
  - `docs/requirements.md`.

**Interfaces:**
- Consumes: Task 1 (`initial_keys`, `packet_keys`), Task 2 (`refeed_one_rtt`, `accept_datagram`'s odcid ensures, `is_live`, `crypto_end`, `crypto_read`'s bound), and the Global Constraints lists.
- Produces (`quictls::server`):
  - `pub struct Rand { pub conn: [u8; RAND_LEN], pub refeed: [u8; RAND_LEN], pub complete: [u8; RAND_LEN], pub tls: [u8; TLS_RAND_LEN] }` (`refeed`: preflight I1). `tls` holds the ECDHE scalar and the PSS salt, so `Rand` gets no derived `Debug` (3e's `PacketKeys` ruling). `QuicServer` gets no derives. Any derive a task adds goes on TRUSTED's derived-impl tls row (4b's).
  - `pub enum TlsCall { Fed { level: Level, current: Level }, KeyChange { lower: Level, unread: nat } }` (ghost log entries), with `pub open spec fn level_rank(l: Level) -> nat` (Initial 0, Handshake 1, OneRtt 2).
  - `pub struct QuicServer<'a> { h3: H3Server, hs: ServerHandshake<'a>, keys: [Option<KeyPair>; 3], level: Level, init_end: u64, log: Ghost<Seq<TlsCall>> }`:
    - `level` is TLS's current receive level as the glue tracks it: Initial; then Handshake at `Secrets { Handshake }`; then OneRtt at `Complete`;
    - `init_end` is `crypto_end(Initial)` when `level` left Initial.
  - Closed specs: `conn_spec()`, `keys_spec() -> Seq<Option<SpecKeyPair>>`, `tls_log()`, `level_spec()`. **`pub closed spec fn wf(&self)`:**
    ```
    h3.wf() && h3.history_ok() && hs.wf()
    keys[0] is Some ==> conn.live(Initial);  keys[1] is Some ==> conn.live(Handshake)     // no discarded keys (§4.9.1, §4.9.2)
    forall i: tls_log[i] matches Fed { level, current } ==> level_rank(level) >= level_rank(current)   // §4.1.3: never fed a left level
    forall i: tls_log[i] matches KeyChange { unread, .. } ==> unread == 0                               // §4.1.3: nothing unread at a key change
    ```
  - The `log` field is ghost and needs `#[allow(dead_code)]`, as at conn.rs:222-227, or the 0-warnings check fails (preflight M3).
  - `impl<'a> QuicServer<'a>`. Every method except `accept` requires `old(self).wf()` and ensures `final(self).wf()`. Every method taking `app` ensures `app_grew(old(app)@, final(app)@)`.
  - **`sync_keys()` is the last statement of every `QuicServer` method and of every return path of `tls_step` and `apply`, after any `pump` (preflight C1).** No `Connection` or `H3Server` pub fn ensures that `live(k)` is unchanged, so the wf key clauses are re-established only by `sync_keys`. It touches only `keys`, so every conn ensures carries over. Do *not* add liveness frames to `poll_transmit` (at 7.13M of the ~12M cap) or to the other conn fns.
    - **`pub fn accept(cfg: &'a ServerConfig, d: &[u8], path: PathId, now: u64, r: &Rand, local_tp: &TransportParams, app: &mut Vec<AppEvent>) -> (s: Option<QuicServer<'a>>)`**: requires `cfg.wf()`; ensures `s matches Some(q) ==> q.wf()`. Body order:
      ```
      dcid = initial_dcid(d)?;  if dcid.len() > MAX_CID_LEN { return None }
      keys = [Some(initial_keys(&dcid)), None, None]
      c = accept_datagram(d, path, now, &r.conn, local_tp, &keys)?          // Task 2: c's odcid is dcid (exec check)
      let mut tp = Vec::new(); serialize_server_params(c.local_params(), &mut tp)   // out param (preflight M1); ≤ MAX_SERVER_TP_LEN = 174 ≤ 1024
      s = QuicServer { h3: H3Server::new(c), hs: ServerHandshake::new(cfg, tp), keys, level: Initial, init_end: 0, log: [] }
      s.sync_keys()                                                        // wf's key clauses, with no fact about accept's liveness needed
      s.tls_step(now, r); s.h3.pump(app); s.sync_keys(); Some(s)           // preflight C1
      ```
    - **`pub fn receive(&mut self, d: &[u8], path: PathId, now: u64, r: &Rand, app: &mut Vec<AppEvent>)`**:
      ```
      was = conn.handshake_complete()
      pipeline::receive(h3.conn_mut(), d, path, now, &r.conn, &keys); sync_keys()
      tls_step(now, r)
      if !was && conn.handshake_complete() { refeed_one_rtt(h3.conn_mut(), d, path, now, &r.refeed, &keys); sync_keys() }   // r.refeed: preflight I1
      h3.pump(app); sync_keys()                                             // SETTINGS goes out once 1-RTT is live; preflight C1
      ```
    - **`pub fn transmit(&mut self, now: u64, out: &mut Vec<u8>) -> (r: Option<PathId>)`** = `pipeline::transmit(h3.conn_mut(), now, &keys, out)`, then `sync_keys()`. It forwards `transmit`'s ensures with `old(self).keys_spec()`, so `final(out)@ == rfc_protect_datagram(l, keys)`. That protects only packets whose slot is `Some`, and `wf` puts slot `Some` ⇒ space live, so no packet is protected with discarded keys. It also forwards:
      - `now < u64::MAX && old.conn_spec().timers_later(now) ==> final….timers_later(now)`;
      - the whole `r is None ==> final(out)@ == [] && out_log unchanged && final(self).conn_spec().acks_later(now)` clause, which `next_timeout` in `settled_later` needs (preflight C8).
    - **`pub fn on_timeout(&mut self, now: u64, rand: &[u8; RAND_LEN], app: &mut Vec<AppEvent>)`** = `h3.on_timeout(now, rand, app)`, then `sync_keys()`. Ensures `now < u64::MAX ==> final(self).conn_spec().timers_later(now)` and `now <= final(self).conn_spec().now_spec()` (from Task 2's `H3Server::on_timeout` ensures; preflight C8: `lemma_keeps_elim` after `poll_cid_updates` needs it). Nothing between `on_timeout` and the deadline read touches TLS (3e binding: `crypto_read` lacks `keeps_later`, and is only on the receive path).
    - **`pub fn poll_cid_updates(&mut self, out: &mut Vec<CidUpdate>)`**, through `conn_mut`, then `sync_keys()`; ensures `final(self).conn_spec().keeps_later(old(self).conn_spec())`.
    - **`pub fn on_reset_candidate(&mut self, tail: &[u8; 16], now: u64, app: &mut Vec<AppEvent>)`**: through `conn_mut`, then `pump`, then `sync_keys`.
    - **`pub fn send_response(&mut self, id: u64, resp: &Response, app: &mut Vec<AppEvent>) -> Result<(), SendError>`** = `h3.send_response`, then `sync_keys()`.
    - **`pub fn conn(&self) -> (r: &Connection)`**: ensures `*r == self.conn_spec()`. `#[doc(hidden)] pub fn key_slots(&self) -> [bool; 3]` (tests).
    - `fn settled_later(&mut self, now, rand, app, out, cap) -> (r: Option<Option<u64>>)`, never called, `#[allow(dead_code)]`. Requires `wf` and `now < u64::MAX`; ensures `r matches Some(t) ==> later(t, now)`.
      - Body: the shell's wake order: `on_timeout`; `poll_cid_updates` (with `lemma_keeps_elim`, using `on_timeout`'s `now <= now_spec`); `transmit` until `None`, at most `cap` times; `Some(conn().next_timeout())` (using `transmit`'s `acks_later`).
      - This is the 3e binding note's `H3Server` twin.
  - Private. Give each event arm of `apply` and each step of `tls_step` its own `#[verifier::spinoff_prover]` fn: every `conn_mut()` call brings in conn_mut's 7 ensures (preflight §4).
    - **`fn sync_keys(&mut self)`**: `keys[0] = None` unless `is_live(Initial)`; `keys[1] = None` unless `is_live(Handshake)`. This is what makes the wf key clauses hold after any `Connection` call.
    - **`fn tls_step(&mut self, now: u64, r: &Rand)`**. Requires `old(self).wf()`. Ensures:
      - `final(self).wf()` and `final(self).conn_spec().out_log() == old(self).conn_spec().out_log()`.
      - **1-RTT keys on a failed handshake** (preflight C9; ruling: clear only before completion): `final(self).hs@.phase is Failed && !(old(self).hs@.phase is Failed) && !old(self).conn_spec().live(OneRtt) ==> final(self).keys_spec()[2] is None`.
        - After completion the 1-RTT keys stay. Initial and Handshake are already discarded, so CONNECTION_CLOSE for, say, a post-handshake 0x10a goes out under 1-RTT keys.
        - The proof needs `lemma_ok_not_failed(cfg, tp, s, level, data, rand)`: `!(s.phase is Failed) && spec_on_crypto(cfg, tp, s, level, data, rand).1 is Ok ==> !(spec_on_crypto(…).0.phase is Failed)`.
        - Task 3 adds it to **server.rs** as a `pub proof fn` of about 5 lines. It calls the private `lemma_drain_events` on `spec_with_reader(s, level, spec_reader(s, level) + data)`, whose Ok arm uses the private `spec_call_shape` (preflight I2).
      - **§4.1.3 close:** `!(old(self).level_spec() is Initial) && old(self).conn_spec().crypto_end_spec(Initial) > old(self).init_end && old(self).conn_spec().phase_spec() is Open ==> !(final(self).conn_spec().phase_spec() is Open)`. It follows from `close`'s `Open ==> Closing` ensures, because step 1 reads `crypto_end` *before* any `crypto_read` (preflight C7).

      In this order:
      1. **Superseded Initial** (reordered, preflight C7). If `level` is not Initial:
         1. `e = crypto_end(Initial)`; if `e > init_end`, close with PROTOCOL_VIOLATION, `sync_keys()`, return;
         2. then `b = crypto_read(Initial)`; if `b` is non-empty, the same.

         This is §4.1.3, and the 4b binding note: check before `on_crypto`, which would say 0x10a. Handshake needs no such check: `on_handshake_complete` discards it in the call that leaves it, and resets its stream.
      2. For each `l` in Initial, Handshake, OneRtt with `level_rank(l) >= level_rank(level)`: `b = crypto_read(l)`. If `b` is empty, continue. Otherwise push `Fed { l, level }` and call `hs.on_crypto(l, &b, &r.tls, &mut ev)`:
         - `Err(code)` → if `!conn.handshake_complete()` { `keys[2] = None` } (no 1-RTT key survives a handshake that failed before completion; RFC 8446 §6; preflight C9). Then `report(code, now)`, `sync_keys()`, return;
         - `Ok` → `if !apply(ev, now, r) { return }`.
      3. When `level` left Initial during this call: `init_end = crypto_end(Initial)`. Then `sync_keys()`.
    - **`fn apply(&mut self, ev: Vec<TlsEvent>, now: u64, r: &Rand) -> bool`**. First the pre-checks, which apply none of the events:
      - if `ev` has `Secrets { Handshake }` and `hs.pending(Initial)`: close with PROTOCOL_VIOLATION, `sync_keys()`, return `false`;
      - if `ev` has `Complete` and `hs.pending(Handshake)`: the same;
      - otherwise, for each of those two events present, push `KeyChange { lower, |spec_reader(hs@, lower)| }` (lower = Initial or Handshake). This push is the key change the wf clause audits: with the check dropped, a non-zero `unread` gets logged.

      Then, in order:
      - `PeerParams(b)` → `parse_transport_params(&b, true)`.
        - On `Err`, close with TRANSPORT_PARAMETER_ERROR, `sync_keys()`, return `false`.
        - On `Ok(t)`, apply `theorem_peer_tp_wf`, then `on_peer_params(&t, now)`. Then, if `conn().phase()` is not Open (its §7.3 check closed it), `sync_keys()` and return `false`: no keys are installed on a failed connection (preflight I7).
      - `Send { l, data }` → `crypto_write(kind(l), &data)`. `OneRtt` is unreachable by `theorem_event_discipline`.
      - `Secrets { l, client, server }` → `keys[idx(l)] = Some(KeyPair { rx: packet_keys(&client), tx: packet_keys(&server) })`. For `l` Handshake, `level = Handshake`.
      - `Complete` → `on_handshake_complete(&H3_ALPN, now, &r.complete)`; `level = OneRtt`. If `conn().phase()` is not Open (its ALPN or INTERNAL_ERROR close), `sync_keys()` and return `false` (preflight I7).

      Finally `sync_keys()`, then return `true`.
    - **`fn report(&mut self, code: u64, now: u64)`**: `CRYPTO_ERROR_BASE <= code <= CRYPTO_ERROR_BASE + 0xff` → `on_tls_alert((code - CRYPTO_ERROR_BASE) as u8, now)`; else `code <= VARINT_MAX` → `close(code, false, &[], now)`; else `close(INTERNAL_ERROR, …)`. This keeps the 4b binding: `on_crypto` also returns 0x0a and 0x0d.

- [ ] **Step 1: Failing tests** in `crates/quictls/tests/server.rs`. Setup:
  - `R(n)` is `Rand { conn: rnd(n), refeed: rnd(n + 50), complete: rnd(n + 100), tls: [n; 96] }`, and `cfg = ecdsa_cfg()`.
  - `ini(dcid, pn, frames, _)` = `protect(&OutPacket{Initial, dcid, C1, pn, 4, frames, padding, false}, &initial_keys(dcid).rx)`, with `padding` chosen so the datagram is exactly 1200 bytes unless a test says otherwise.
  - The curl tests use `ini` with DCID `S1` and SCID `curl_scid()` instead of `C1` (preflight M1). `curl_scid()` is the `initial_source_connection_id` of `CURL_CH`'s 0x39 extension, read with `parse_transport_params(_, true)`; otherwise `on_peer_params`' §7.3 check closes the connection at the ServerHello.
  - `ctp()` is the client transport-parameter bytes `0f08c1c1c1c1c1c1c1c1 0e0104`: `initial_source_connection_id` `C1`, and `active_connection_id_limit` 4.
  - `h3ch(edit)` is `h3_ch(&[(0x17, P256_SHARE.to_vec())], |e| { <set 0x39 to ctp()>; edit(e) })`: A.2's ClientHello with ALPN `h3` and a P-256 share. `P256_SHARE` is a `&[u8]`, hence the `.to_vec()` (preflight M1). `L` is `h3ch(id).len()`.
  - `open(out)` (preflight I6): with `ik = initial_keys(dcid)`, it is `open_datagram(out, &[Some(KeyPair { rx: ik.tx, tx: ik.rx }), None, None], &[None; 3])`. It asserts `error` is `None` and returns the Initial packets' frames. A coalesced Handshake packet (a close after `direct_flight` goes out in both spaces) is dropped for lack of keys. Do not copy 3e's `client_open`: it asserts one packet fills the datagram.
  - **`a2_closes_0x178`** (Review Focus 5; outline test): `QuicServer::accept(&cfg, &A2, 0, 0, &R(1), &qc::ltp(), &mut app)` is `Some(s)`. `s.transmit(0, &mut out)` is `Some(0)`, and `open(out)` is exactly `[ConnectionClose { app: false, error_code: 0x178, frame_type: 0, reason: [] }]` in one Initial. `s.key_slots() == [true, false, false]`.
  - **`curl_ch_two_datagrams_hrr`** (Review Focus 2):
    - `CURL_CH` is cut into 8 CRYPTO frames of 192 bytes each (the last 188).
    - Datagram 1 carries frames `[5, 0, 7, 2]`. Datagram 2 carries `[1, 3, 4, 6]` plus the overlapping `Crypto{64, CURL_CH[64..256]}`, which re-sends part of frames 0 and 1 with a different split.
    - Both datagrams are 1200 bytes, pn 0 and 1. Datagram 2's frames come to about 960 bytes, so they fit.
    - After `accept` with datagram 1, `transmit` carries no CRYPTO frame.
    - After `receive` with datagram 2, `transmit` carries one Initial whose CRYPTO data at offset 0 is exactly the 4b HRR `020000340303cf21ad74e59a6111be1d8c021e65b891c2a211167abb8c5e079e09e2c8a8339c00130100000c003300020017002b00020304`. `key_slots() == [true, false, false]`.
  - **`direct_flight`:** `accept` with `ini(S1, 0, [Crypto{0, h3ch(id)}], _)` (a P-256 share, so no HRR).
    - Over the datagrams `transmit` returns until `None` (3d's packing and padding are not pinned):
      - an Initial whose CRYPTO data starts with a ServerHello (byte 0 is `02`, and bytes 6..38 are not `HRR_RANDOM`);
      - and at least one Handshake packet with DCID `C1`, found by walking each datagram's long headers with `parse_long_header` and their Lengths.
    - The Handshake keys need the ECDHE secret, so Task 4's harness is what decrypts that packet.
    - `key_slots() == [true, true, true]`.
  - **`ch2_under_1200_dropped`** (Review Focus 4): after `curl_ch_two_datagrams_hrr`'s HRR, CH2 is `CURL_CH` with its key_share replaced by `(0x17, P256_SHARE)`, built with tls's `split_ch`/`join_ch`, in one CRYPTO frame at offset 1532 (Initial's stream continues).
    - In a 1199-byte datagram it produces no ServerHello: the next `transmit` is `None` or ACK-only.
    - The same CH2 in a 1200-byte datagram gives a ServerHello.
  - **`trailing_initial_bytes_pv`:** `h3ch(id)` plus one byte `0x01` in the same CRYPTO frame closes with `ConnectionClose{false, 0x0a, …}` in Initial and no ServerHello (§4.1.3, unread data at a key change). `key_slots()[1] == false`.
  - **`initial_retransmit_after_switch_ok`** (Review Focus 3): after `direct_flight`, `receive` of `ini(S1, 1, [Crypto{0, h3ch(id)}], _)` (the same bytes again), and then of an ACK-only Initial, leaves `conn().phase()` Open.
  - **`initial_data_after_switch_pv`:** after `direct_flight`, `receive` of `ini(S1, 1, [Crypto{L + 100, [7; 10]}], _)` (gapped, past the end) closes with 0x0a. On a fresh `direct_flight`, the contiguous `Crypto{L, [7; 10]}` closes with 0x0a too.
  - **`error_ranges`** (4b binding: the error-code range test). Each is from `accept`, with the close code read from the server's Initial:
    - a CRYPTO frame `01 01 00 01` followed by 1000 zero bytes (a ClientHello header claiming a 65537-byte body) gives `0x0d` (CRYPTO_BUFFER_EXCEEDED);
    - `join_ch(&head(0x0303, &[7], &[0x1301], &[0]), &split_ch(&h3ch(id)).1)` (a 1-byte `legacy_session_id`) gives `0x0a` (RFC 9001 §8.4);
    - `h3ch` with ALPN `h3-29` only gives `0x178`;
    - `h3ch` whose 0x39 body is `01 01 05 01 01 05` (max_idle_timeout twice) gives `0x08` (TRANSPORT_PARAMETER_ERROR).
  - **`peer_tp_mismatch_no_keys`** (preflight I7): `accept` with `ini(S1, 0, [Crypto{0, h3ch(id)}], _)`, but with the packet's SCID `[0xc2; 8]`, so `ctp()`'s `C1` fails §7.3. The connection closes with 0x08, and `key_slots() == [true, false, false]`: no Handshake or 1-RTT key is installed on the failed connection.
  - A TLS failure after the 1-RTT slot is filled needs a client Finished, so it is Task 4's `tampered_finished_0x133`.
- [ ] **Step 2:** The tests fail to compile.
- [ ] **Step 3: Implement.** Duvet-cite, each verbatim from `duvet_q.py`'s list:
  - RFC 9001 §4.1.3's three MUSTs: the first two at `tls_step` step 1, the third at `apply`'s pre-checks;
  - RFC 8446 §5.1's "Handshake messages MUST NOT span key changes.", "Implementations MUST verify that all messages immediately preceding a key change align with a record boundary; …" (a comment: RFC 9001 §4.1.3 makes the error PROTOCOL_VIOLATION) and "… implementations MUST send these messages in alignment with a record boundary." (`Send` carries whole messages, one level each) at the pre-checks;
  - RFC 9001 §4 "If QUIC needs to retransmit that data, it MUST use the same keys …" and §4.9's two MUSTs at `apply`'s `Send` arm (each level's bytes go to that level's stream, which 3d retransmits only in that space, under that space's slot; `theorem_event_discipline` orders `Send { Handshake }` after its keys);
  - RFC 9001 §4.8 and RFC 8446 §6.2's three MUSTs at `report`;
  - RFC 8446 §6 "MUST forget the secret values and keys established in failed connections" at `tls_step`'s `Err` arm (with the TRUSTED row);
  - §6's "MUST NOT allow any further data to be sent or received" at `report` (preflight M8). The comment says both halves:
    - the sentence is about *receiving* an error alert, whose QUIC image is a peer CONNECTION_CLOSE: conn.rs enters draining, which sends and processes nothing (RFC 9000 §10.2.2);
    - on our own failure, `report` closes and the closing state sends only CONNECTION_CLOSE (3d);
  - §6's "AlertLevel=fatal" and "Unknown Alert types" as `type=exception`, `reason=QUIC carries no TLS alert records (RFC 9001 §4.8): our alerts become CONNECTION_CLOSE codes, and the peer's close is a CONNECTION_CLOSE whatever its code.`;
  - RFC 9001 §4.9.1's server MUST at `sync_keys`, its "MUST NOT send Initial packets after this point" there too (an Initial packet has no key once the space is discarded), and §4.9.2 there.
  - Call `theorem_reader_bound` in a comment at `tls_step`: with `crypto_read`'s `MAX_CRYPTO_BUFFER` bound, each `on_crypto` gets at most 16384 bytes and each reader stays under `4 + MAX_HS_BODY` (the controller's push-bound ruling).
  - TRUSTED.md:
    - "CT check scope" row: add `quictls::keys` and `quictls::server` (traffic secrets and packet keys handled outside crypto, not CT-checked);
    - a new row: `| Secret lifetime (RFC 8446 §6 "forget"): QuicServer holds no traffic secret after deriving packet keys; ServerHandshake drops transcript, CH1 and client_vd on Failed (4b), and keeps client_vd after Complete (preflight M6); the 1-RTT key slot is cleared on a TLS failure before completion, and kept after completion, because the CONNECTION_CLOSE then goes out under 1-RTT keys (preflight C9); Initial and Handshake packet keys stay until their space is discarded or the connection is dropped, because CONNECTION_CLOSE needs them. Memory is not zeroised: freed buffers, the TlsEvent secrets and stack copies keep their bytes until reused, so a memory disclosure exposes them (Task 5 adds the shell's PEM/DER buffers and scalar copies) | crates/quictls/src/server.rs, crates/tls/src/server.rs | Verus cannot express erasure, and plain overwrites are dead stores the optimiser may drop | never (known gap) |`.
- [ ] **Step 4:** The four checks; the quictls and tls rlimit-4 runs (and `build_flight`'s margin) (ruling: quictls crate). Binary gate per the Global Constraints. The `U tls crypto::…` block may grow if quic's small fns are inlined into tls.
  - **Mutations:** drop the `pending(Initial)` pre-check (fails `wf`'s `KeyChange` clause); drop the `pending(Handshake)` pre-check (same); delete step 1's close (fails the §4.1.3 close ensures); feed step 1's bytes to `on_crypto(Initial)` instead of closing (fails `wf`'s `Fed` clause); `sync_keys` keeps `keys[0]` (fails `wf`'s Initial clause); drop `keys[2] = None` on `Err` (fails the `tls_step` 1-RTT ensures); clear `keys[2]` on `Err` also after completion (fails no proof: the ensures only constrains before completion, so it is caught by Task 4's `post_handshake_error_closes_under_one_rtt`; preflight C9); drop `sync_keys()` after `pump` in `receive` (fails `wf`'s key clauses; preflight C1); drop `apply`'s post-`on_peer_params` Open check (caught by `peer_tp_mismatch_no_keys` below; preflight I7).
  - Residual, as in 3e's C4: a body that skips a `KeyChange`/`Fed` push still verifies. It goes in the report as one line.
- [ ] **Step 5: Commit:** `feat(tls): verified QUIC-TLS glue (RFC 9001 §4, §4.1.3, §4.8, §4.9): events to the connection, key slots in lockstep with discard, alerts to CONNECTION_CLOSE`
- [ ] **Step 6: Matrix commit.**
  - RFC 9001 §4, §4.1.3, §4.8, §4.9: `✅ 4c: crates/quictls/src/server.rs (…)`, each naming its fn.
  - RFC 8446 §5.1 (req): `✅ 4c: crates/quictls/src/server.rs (apply's pending pre-checks; PROTOCOL_VIOLATION per RFC 9001 §4.1.3)`.
  - RFC 8446 §6, §6.2: `✅ 4c: crates/quictls/src/server.rs (report, tls_step's Err arm; memory zeroisation is a TRUSTED known gap)`.

  Each replaces the 4a/4b touched note. Commit: `docs: mark RFC 9001 §4, §4.1.3, §4.8, §4.9 and RFC 8446 §5.1 (req), §6, §6.2 closed in 4c`.

---

### Task 4: The handshake end to end in memory; discard, 0-RTT and replaced-by-QUIC rows — suggested model: sonnet

**Files:**
- Create: `crates/quictls/tests/e2e.rs`
- Modify:
  - `crates/quictls/src/server.rs`: comments only. These are the exception block at the end of the file, and the §4.1.2 citation in `apply`'s `Complete` arm (preflight M7);
  - `docs/requirements.md`.

**Interfaces:**
- Consumes: Task 3's `QuicServer` API, `Rand`, `key_slots`; Task 1's `initial_keys`, `packet_keys`; `quic::protect::{protect, open_datagram}`; `quic::datagram::OutPacket`.
- Consumes: rustls `quic::ClientConnection`. `crates/tls/tests/rustls_e2e.rs`'s `client`, `Log`, `Verifier` and `drain` are private to that file, so copy them. Construct the client with transport parameters `0f08 <scid> 0e0104 090103 040480010000 070480004000` (preflight C2): `initial_source_connection_id` scid, `active_connection_id_limit` 4, `initial_max_streams_uni` 3, `initial_max_data` 65536, `initial_max_stream_data_uni` 16384.
  - Without the uni-stream limit, `H3Server::pump` closes with H3_GENERAL_PROTOCOL_ERROR right after completion (h3_server.rs:1029-1033), and no HANDSHAKE_DONE is sent.
  - Not 4b's `client_tp()`, whose `initial_source_connection_id` would fail `on_peer_params`' §7.3 check.
- Produces: a test-only client in `crates/quictls/tests/e2e.rs`:
  - `struct Client { tls: ClientConnection, log: Arc<Log>, odcid: [u8; 8], scid: [u8; 8] (= C1), dcid: Vec<u8>, keys: [Option<KeyPair>; 3], pn: [u64; 3], rx: [Reader; 3], tx_off: [u64; 3] }`, where `keys` is the client view (`rx` = the server's).
  - Initial keys come from `initial_keys(&odcid)`, swapped. The Handshake and 1-RTT keys are `packet_keys` over the KeyLog secrets `CLIENT_HANDSHAKE_TRAFFIC_SECRET`/`SERVER_HANDSHAKE_TRAFFIC_SECRET` and `CLIENT_TRAFFIC_SECRET_0`/`SERVER_TRAFFIC_SECRET_0`, installed when `write_hs` reports the matching `KeyChange`.
  - `dcid` becomes the server's SCID from its first Initial (RFC 9000 §7.2).
  - `fn datagrams(&mut self, extra_one_rtt: Option<Vec<Frame>>) -> Vec<Vec<u8>>`: everything `drain` gives, as CRYPTO frames at each level's next offset. Initial packets are padded so their datagram is 1200 bytes. A level's packets are coalesced Initial, then Handshake, then 1-RTT, with `extra_one_rtt` last.
  - `fn absorb(&mut self, d: &[u8]) -> Vec<(PacketKind, Vec<Frame>)>`: a **client-side opener**, not `open_datagram`. `open_datagram` parses frames as a server does and rejects HANDSHAKE_DONE (0x1e) as PROTOCOL_VIOLATION (frame.rs:453) (preflight C3). Per packet:
    1. `parse_header`;
    2. `quic::hp::remove_hp` (hp.rs:323);
    3. `quic::aead::open_packet` (aead.rs:307), with the client-view keys and the per-space largest pn;
    4. a frame walk with `parse_frame_type`/`parse_frame_body` (frame.rs:1399, 1423) that maps type 0x1e to `Frame::HandshakeDone` itself.

    Each level's CRYPTO goes in order to `read_hs`; it returns the frames.
  - `fn run(server, client, max_rounds)` shuttles both ways: `transmit` until `None`, asserting **every `Some` has a non-empty `out`**. That is the 3e binding note "no keyless ack-eliciting packet": `protect_datagram`'s write-nothing branch never fires.

- [ ] **Step 1: Tests** in `crates/quictls/tests/e2e.rs`, each against `QuicServer::accept(&ecdsa_cfg(), …)`. rustls's default key share is X25519, so every handshake here takes the HRR path.
  - **`rustls_quic_handshake`:**
    - `run` until `!client.tls.is_handshaking()` and `server.conn().handshake_complete()`, within 6 rounds;
    - the first server datagram after completion holds a 1-RTT packet with `HandshakeDone` (§4.1.2);
    - `server.key_slots() == [false, false, true]` (§4.9.2);
    - no server datagram after completion holds an Initial or Handshake packet.
  - **`initial_keys_dropped_on_first_handshake_packet`** (§4.9.1): before sending its Finished, the client sends a Handshake `[Ping]` packet alone. After `receive`, `key_slots() == [false, true, true]`, and every later server datagram holds no Initial packet.
  - **`finished_coalesced_with_one_rtt`** (Review Focus 1): the client's Finished datagram also carries `extra_one_rtt = [Ping]` (pn 0). Right after that one `receive`, `server.conn().largest_pn(OneRtt) == Some(0)`.
  - **`finished_trailing_bytes_pv`:** the client's Finished CRYPTO plus one byte `0x14` closes with 0x0a: the server's next datagram has `ConnectionClose{false, 0x0a, …}` in a Handshake packet, and no `HandshakeDone`.
  - **`tampered_finished_0x133`:** flip the last verify_data byte; the close code is `0x133` (decrypt_error), in a Handshake packet. Afterwards `key_slots()[2] == false`.
  - **`zero_rtt_dropped`** (§4.6.2, §8.3): a 0-RTT long header (type `0xd0`, DCID `odcid`, a Length covering 30 bytes of `[0x06; 30]`, so it looks like CRYPTO) is coalesced *after* the client's first Initial in the same datagram (RFC 9000 §12.2 order). It must go after: `accept` keys by the first header, which must be an Initial. `accept` succeeds, the handshake completes, and no close happens. A second case does the same in front of the client's CH2 Initial, through `receive`. That makes the first packet a drop, so `receive` calls `on_reset_candidate` with CH2's last 16 bytes (harmless: no reset token exists yet); assert `phase()` is Open right after (preflight M10).
  - **`post_handshake_error_closes_under_one_rtt`** (preflight C9): after `rustls_quic_handshake`, the client sends a 1-RTT packet with `Crypto{0, [0x18, 0, 0, 1, 0]}` (a TLS KeyUpdate). The server closes with 0x10a; its next datagram is non-empty and holds a 1-RTT packet with `ConnectionClose{false, 0x10a, …}`; and `key_slots() == [false, false, true]`.
- [ ] **Step 2:** `cargo test -p quictls --test e2e`. Tasks 1–3 exist, so this is a check, not a red step; on a failure, fix the glue (Task 3's file) and say so in the report.
- [ ] **Step 3: Annotations**, at the end of `crates/quictls/src/server.rs`, under the heading comment `// Requirements on clients, on specification authors, and on TLS records, which QUIC replaces`. Each is a `type=exception` with a reason, unless it says "cite":
  - RFC 9001:
    - §4.1.2: cite at `apply`'s `Complete` arm, outside this block (`on_handshake_complete` sets HANDSHAKE_DONE owed in the call that completes; `rustls_quic_handshake` sees it in the next datagram);
    - §4.6.2's server MUST: cite here, with the comment "0-RTT packets are dropped unopened by quic::protect::rfc_unprotect (3e); no 0-RTT keys exist". Its client MUST is client-only;
    - §4.9.3 (vacuous: no 0-RTT keys are ever derived; `Level` has no 0-RTT);
    - §5.3's first two MUSTs (cite: 4b negotiates only 0x1301, whose HP is 3e's `quic::hp`; unsupported suites are skipped by 4a's parser and 4b's `negotiate`, never rejected);
    - §5.6's five (one server MUST, vacuous: no 0-RTT keys; three client-only; the application-profile one: HTTP/3 0-RTT is declined);
    - §8.3's two (client-only; and "receipt of a CRYPTO frame in a 0-RTT packet", vacuous: 0-RTT packets are never decrypted, so no frame in one is ever received).
  - RFC 8446:
    - §5's five, §5.1's other twelve, §5.2's five, §5.3's three and §5.4's five: `reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).`;
    - §6.1's four: `reason=Replaced by QUIC: closure is CONNECTION_CLOSE (RFC 9001 §4.8, RFC 9000 §10.2); no close_notify is sent or read.`
- [ ] **Step 4:** The four checks; `check_quotes.py` on `crates/quictls/src/server.rs`; `duvet_q.py` over the 29 sections prints exactly the 22 lines named in "MUST assignment". No proof changes.
  - **Mutation (test):** `sync_keys` keeps `keys[0]` (a Task 3 proof mutation too) also makes `initial_keys_dropped_on_first_handshake_packet` fail; drop `refeed_one_rtt` from `receive`, and `finished_coalesced_with_one_rtt` fails.
- [ ] **Step 5: Commit:** `test(tls): in-memory QUIC handshake against rustls through QuicServer (HRR, discard, HANDSHAKE_DONE, coalesced Finished + 1-RTT); 0-RTT and replaced-by-QUIC annotations`
- [ ] **Step 6: Matrix commit.**
  - RFC 9001 §4.1.2, §4.9.1, §4.9.2: `✅ 4c: crates/quictls/src/server.rs (…) + crates/quictls/tests/e2e.rs`.
  - §4.6.2, §4.9.3, §5.6, §8.3: `✅ 4c: vacuous or client-only (crates/quictls/src/server.rs exceptions); 0-RTT dropped unopened (3e)`.
  - RFC 8446 §5, §5.1, §5.2, §5.3, §5.4, §6.1: `✅ 4c: replaced by QUIC (crates/quictls/src/server.rs exceptions, RFC 9001 §4)`.
  - Retag RFC 9001 §5.3, §5.5, §6.1, §6.2, §6.3, §6.4, §6.6 Phase `4` → `4d`, with touched notes. §5.3: `4c: suite/HP and unsupported-suite MUSTs cited in crates/quictls/src/server.rs; the AEAD-limit key update is 4d`.
  - Retag RFC 9001 §9.5 Phase `4` → `7`, with the note `not met: quic CT roots after 8c` ahead of its 3e note (Ruling D3; preflight I3).
  - Add a Legend row: `| 4d | QUIC key update and AEAD limits (RFC 9001 §5.3 third MUST, §5.5, §6.1–§6.4, §6.6) |`.

  Commit: `docs: mark the 4c discard, 0-RTT and replaced-by-QUIC rows closed; retag key update to 4d and RFC 9001 §9.5 to 7`.

---

### Task 5: The shell over `QuicServer` — suggested model: sonnet

**Files:**
- Modify:
  - `crates/server/src/lib.rs`, `crates/server/src/main.rs`;
  - `crates/tls/src/config.rs` (`p256_signing_key`; it needs no quic item), and a new `crates/tls/tests/config.rs` (one test) (ruling: quictls crate);
  - `crates/server/tests/shell.rs`, `crates/server/tests/initial_exchange.rs`;
  - `crates/server/Cargo.toml` (`h3 = { path = "../h3" }`) and `Cargo.lock` (preflight I5);
  - `TRUSTED.md`;
  - `docs/requirements.md`: the RFC 8446 §9.1 (req) row note gains "RSA keys refused by the 4c loader until Phase 7 (rsa_key_wf needs primality)" (Ruling D4; preflight I4).
- Create: `crates/server/tests/data/{cert.pem, key.pem, ca.pem, leaf.pem, leaf-key.pem, rsa-key.pem}`. The generation commands go in the task report, not the repo.

**Interfaces:**
- Consumes: Task 3's API (`QuicServer::accept` requires `cfg.wf()`, which `build_config` ensures), `Rand`, `AppEvent`, `send_response`, `SendError`; `h3::message::Response { status, headers: Vec<FieldLine>, body }`, `h3::qpack::field_section::FieldLine { name, value }`; `crypto::p256::{scalar_valid, spec_p256_public_key, p256_public_key}` (inside tls only).
- Produces (`tls::config`, verified): **`pub fn p256_signing_key(d: [u8; 32]) -> (r: Option<(SigningKey, [u8; 65])>)`**. Ensures `r is Some <==> scalar_valid(d@)` and `r matches Some((k, q)) ==> k@ == SpecSigningKey::EcdsaP256(d@) && key_wf(k@) && spec_p256_public_key(d@) == Some(q@)`, via `p256_public_key`. tls already has that `U` line. The shell's key half of `ServerConfig::wf()` is now proved for P-256 keys.
- Produces (`server`):
  - `pub fn load_config(cert_pem: &[u8], key_pem: &[u8], chain_schemes: Vec<u16>) -> Result<ServerConfig, String>`, unverified. It does, in order:
    1. collects the PEM `CERTIFICATE` blocks, leaf first (a ~20-line base64 decoder in the shell, `// ponytail:` std has none);
    2. requires one `PRIVATE KEY` block (PKCS#8), parses `PrivateKeyInfo` (version 0, `id-ecPublicKey` 1.2.840.10045.2.1 with `prime256v1` 1.2.840.10045.3.1.7) and its `ECPrivateKey` `privateKey` OCTET STRING of exactly 32 bytes. An RSA key (`rsaEncryption` 1.2.840.113549.1.1.1) is `Err("RSA keys are not loaded before Phase 7: rsa_key_wf needs a primality check")` (Ruling D4); anything else is `Err`;
    3. calls `p256_signing_key(d)` (`None` gives `Err("scalar out of range")`);
    4. requires the 65-byte public point to occur contiguously in `der[0]` (`Err("key does not match the certificate")`);
    5. requires `chain_schemes` non-empty when there are 2 or more certificates (`Err("a chain needs --chain-schemes")`; Ruling D5);
    6. calls `build_config(vec![CertChain { der, chain_schemes, key }])`, where `None` gives `Err("chain too large")`.

    Every `Err` is one of these fixed strings, plus at most a file name or an OID. None ever echoes PEM, DER or key bytes (preflight M6).
  - `pub fn local_params() -> TransportParams`: `default_transport_params()` with `max_idle_timeout 30000`, `initial_max_data 65536`, `initial_max_stream_data_bidi_remote 16384`, `initial_max_stream_data_uni 4096`, `initial_max_streams_bidi 100`, `initial_max_streams_uni 8`, `active_connection_id_limit 2`, `disable_active_migration true` (Ruling D8).
  - `pub const RESPONSE_BODY: &[u8] = b"hello from a verified HTTP/3 server\n";` with `pub fn response() -> Response` (status 200, one header `content-type: text/plain`).
  - `pub fn fill_random(b: &mut [u8]) -> io::Result<()>` via `libc::getrandom`, replacing `fresh_rand` (partial reads and EINTR retried).
  - `pub struct Server<'a> { cfg: &'a ServerConfig, table: CidTable, conns: Vec<Conn<'a>>, next_id: ConnId, rng: fn(&mut [u8]) -> io::Result<()>, out: Vec<u8> }`, with private `struct Conn<'a> { id, q: QuicServer<'a>, addrs: Vec<SocketAddr>, owed: Vec<u64> }`. `Server::new(cfg, rng)`; `on_datagram`, `on_wake`, `deadline`, `conn_count`, `addr_count` keep 3e's contracts and order (I1, E9, `MAX_POLLS`). Changes from 3e:
    - `NewInitial` → `QuicServer::accept(cfg, d, 0, now, &rand(), &local_params(), &mut app)`.
    - `Existing` → `q.receive(d, p, now, &rand(), &mut app)`. The tentative-address rule uses `q.conn().path_state(p)`.
    - `Reset` → `q.on_reset_candidate`.
    - `on_wake` → `q.on_timeout`.
    - `service` → `q.poll_cid_updates` and `q.transmit`, in 3e's order.
    - After every call that fills `app`: each `AppEvent::H3(Output::Request { stream_id, .. })` pushes `stream_id` on `owed`. Then, before `service`'s transmit loop, `send_response(id, &response(), &mut app)` for each owed id, in order, stopping at the first `Busy` (the rest wait for the next call) and removing the id on `Ok` or `Rejected`. Other events are dropped. `// ponytail: one static response; a handler API when there is a second page.`
  - `pub fn run(sock: UdpSocket, cfg: &ServerConfig) -> io::Result<()>`; the 3e loop, otherwise unchanged.
  - `main.rs`: `server --cert CHAIN.pem --key KEY.pem [--chain-schemes 0403,…] [ADDR]` (default `127.0.0.1:4433`). A missing flag, unreadable file or `load_config` error goes to stderr and exits 1.
  - Ponytail in `lib.rs` (3e binding notes, outline open item): `// ponytail: every DCID is keyed, so MAX_CONNS (102) and route's linear scan are reachable, and each unauthenticated Initial costs a P-256 signature (~15 ms); Retry or a per-source handshake limit before deployment.` Connections stay capped by `route`'s `has_room`. The outline's "cap connections with a fixed MAX_CONNS, replacing 3e's uncapped list" is already true on `main` (3e ruling C3), so nothing is added.

- [ ] **Step 1: Failing tests.**
  - `tls` (verified fn), **`p256_signing_key_range`**: `p256_signing_key(ECDSA_D)` is `Some` and its point occurs in `ECDSA_CERT`; `[0; 32]` is `None`; `n` (`ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551`) is `None`; `n − 1` is `Some`.
  - `crates/server/tests/shell.rs`, with the fixtures:
    - **`loads_p256_pem`:** `load_config(cert.pem, key.pem, vec![])` is `Ok`;
    - **`rejects_mismatched_key`:** `load_config(cert.pem, leaf-key.pem, vec![])` is `Err`;
    - **`rejects_rsa_key`:** `load_config(cert.pem, rsa-key.pem, vec![])` is `Err` containing "Phase 7";
    - **`chain_needs_schemes`** (preflight C4): `leaf.pem ++ ca.pem` (leaf first: the key's point must be in `der[0]`) with `leaf-key.pem` is `Err` with `vec![]` and `Ok` with `vec![0x0403]`. The reversed order `ca.pem ++ leaf.pem` is `Err` with either list;
    - **`a2_registered_before_next`:** as in 3e, but `send[0]` decrypts (A.1 server keys) to `[ConnectionClose{false, 0x178, 0, []}]`;
    - **`local_params_accepted`:** `QuicServer::accept` of `A2` with `local_params()` is `Some`.
    - Delete `local_params_are_ltp` (the values changed on purpose).
    - Every remaining 3e shell test changes too (preflight M2): `rng` becomes a deterministic fill `fn(&mut [u8]) -> io::Result<()>`, and `Server::new(&cfg, rng)` takes the fixture config. That covers `spoofed_addresses_take_no_slot` and `idle_close_frees_slot`, not only `a2_registered_before_next`.
  - `initial_exchange.rs`: `a2_gets_one_ack` becomes **`a2_gets_close_0x178`**, with the same reply checks except `p.frames == [ConnectionClose{false, 0x178, 0, []}]`. `initial_1199_ignored` asserts that reply after the 1199-byte Initial. `start()` passes a leaked `load_config(cert.pem, key.pem, vec![])`.
- [ ] **Step 2:** The tests fail.
- [ ] **Step 3: Implement.** Fixtures:
  - `openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:prime256v1 -nodes -keyout key.pem -out cert.pem -days 3650 -subj /CN=localhost -addext subjectAltName=DNS:localhost,IP:127.0.0.1`;
  - CA plus leaf: `ca.pem` self-signed, and `leaf.pem`/`leaf-key.pem` signed by it with ecdsa-with-SHA256;
  - `openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 -out rsa-key.pem`.

  TRUSTED.md:
  - shell row (preflight M5): "drives quictls::server::QuicServer. It calls quic, tls and quictls fns whose requires is the receiver's wf(), plus:
    - `QuicServer::accept`'s `cfg.wf()`, which `build_config` ensures for the only ServerConfig the shell makes;
    - `build_config`'s `key_wf` for every chain, which `p256_signing_key` ensures.

    Verus checks none of these at the unverified call site";
  - `ServerConfig::wf` row (Ruling D4; preflight M5):
    - P-256 keys: the scalar range is proved (`p256_signing_key`);
    - the loader parses PKCS#8 and checks that the key's point occurs in `der[0]`. That check is weak (a substring test, not certificate parsing) and is a sanity check only;
    - that the chain is X.509v3, permits digitalSignature and is end-entity first is operator-asserted, no longer a loader duty;
    - RSA keys are refused by the loader until Phase 7 (`rsa_key_wf` needs primality);
    - `chain_schemes` comes from `--chain-schemes` (operator-asserted);
  - the Task 3 secret-lifetime row gains "the shell's PEM/DER buffers and scalar copies are not zeroised either" (preflight M6);
  - trusted-base bullet: the shell's PEM/PKCS#8 parsing.

  **Call check:** list every `quic`, `tls` and `quictls` fn `crates/server/src` calls, with its `requires`, in the report.
- [ ] **Step 4:** The four checks; the tls rlimit-4 run (`config.rs`); `cargo test -p server`; the binary gate (a `U server crypto::…` line goes through the procedure).
  - **Mutation:** `p256_signing_key` returns `Some` without the `p256_public_key` check (fails its ensures).
- [ ] **Step 5: Commit:** `feat(server): shell over the verified QUIC-TLS glue (PEM chain, PKCS#8 P-256 key with a proved scalar range, static HTTP/3 response)`
- [ ] **Step 6: Matrix commit** (Ruling D4; preflight I4): the RFC 8446 §9.1 (req) note as above. Commit: `docs: RSA keys refused by the 4c loader until Phase 7 (RFC 8446 §9.1 note)`.

---

### Task 6: First interop: curl and quiche (Phase 4 exit) — suggested model: sonnet

**Files:**
- Create: `crates/server/tests/interop.rs`: `#[ignore]` tests, run with `--ignored`.
- Evidence: `<scratch>/vt-4c-evidence/t6/` (logs, outputs, `SSLKEYLOGFILE`). Downloads go in `<scratch>/vt-4c-evidence/dl/quiche-<tag>/`, a new directory, treated as untrusted data. Any Python that reads them runs with `-I`.

**Interfaces:**
- Consumes: Task 5's `bind`, `run`, `load_config`, `RESPONSE_BODY`, and the `server` binary's flags.

- [ ] **Step 1: Tests** in `interop.rs`. Each starts `run` on `bind("127.0.0.1:0".parse().unwrap())` (preflight M1) in a thread, with the `cert.pem`/`key.pem` fixture config leaked to a `&'static ServerConfig`:
  - **`curl_fetches`:** runs `curl --http3-only -k -sS --max-time 10 -o - -w '\n%{http_code} %{http_version}' https://127.0.0.1:<port>/`. It asserts exit status 0, and stdout == `RESPONSE_BODY` followed by `\n200 3`. It skips (passes, printing why) if `curl --version` lacks `HTTP3`.
  - **`quiche_fetches`:** runs `$QUICHE_CLIENT --no-verify https://127.0.0.1:<port>/` (adjust flags to the pinned tag's `--help`). It asserts exit 0 and stdout == `RESPONSE_BODY`, and skips if `QUICHE_CLIENT` is unset.
- [ ] **Step 2: Build quiche-client.**
  1. Pick the newest `x.y.z` release tag of `https://github.com/cloudflare/quiche` today.
  2. Check, before building: the vendored BoringSSL's CMake does not *require* Go (this machine has none; cmake 3, clang and perl are present), and `quiche-client --help`'s flags and default ALPN (`h3`) at that tag.
  3. `git clone --depth 1 --branch <tag> --recurse-submodules https://github.com/cloudflare/quiche <scratch>/vt-4c-evidence/dl/quiche-<tag>`, then `cargo build --release --bin quiche-client` there (its own toolchain resolution, outside the workspace).
  4. Record the tag, the commit (`git rev-parse HEAD`) and the binary's sha256.
  5. Toolchain: `dl/` is inside the project tree, so rustup applies the project's `rust-toolchain.toml` (1.98.1, Verus's pin), and any parent `.cargo/config.toml` applies too. Check both before debugging a quiche build failure. If quiche needs another toolchain, set `RUSTUP_TOOLCHAIN` for that build only, and record it.
  6. If Go turns out to be required, stop and report: installing it needs a ruling.
- [ ] **Step 3: Run.**
  - `cargo build --release -p server`.
  - `cargo test -p server --test interop -- --ignored` with `QUICHE_CLIENT` set: both pass.
  - Then once by hand: `target/release/server --cert crates/server/tests/data/cert.pem --key crates/server/tests/data/key.pem 127.0.0.1:4433 &`, then `SSLKEYLOGFILE=<ev>/t6/keys.log curl --http3-only -k -v https://127.0.0.1:4433/ 2> <ev>/t6/curl.log`, then the quiche-client line; record both outputs.
  - On a failure, debug with `curl -v`'s ngtcp2 trace and `SSLKEYLOGFILE`. The outline's `<scratch>/chk4/cap.py` and `v8448.py` no longer exist; a scratch decrypting script may be written outside `dl/`. Fix the cause in the owning task's file, and name it in the report.
- [ ] **Step 4:** The four checks.
- [ ] **Step 5: Commit:** `test(server): curl --http3 and quiche-client fetch the static response (Phase 4 exit)`. The report quotes both outputs, the quiche tag and commit, and curl's `-V` line.

---

## Exit criteria (Phase 4c, and the Phase 4 exit)

- All four checks pass on the merged tree; `tls` and `quic` verify at `--rlimit 4` (the evidence recipe).
- The 22 rows carry `✅ 4c: <file>`; the 7 key-update rows are Phase `4d`; RFC 9001 §9.5 is Phase `7`, "not met: quic CT roots after 8c" (Ruling D3). The Task 4 awk prints nothing (preflight I3).
- `duvet_q.py` over the 29 sections prints exactly the 22 4d/§9.5 lines (§9.5's two MUSTs stay uncited).
- RFC 9001 Appendix A: A.1 derived (`a1_keys`); A.2 and A.3 reproduced under derived keys (`a2_a3_under_derived_keys`). A.4 (Retry) and A.5 (ChaCha20) are declined; A.5's `ku` vector is 4d's.
- `curl_fetches` and `quiche_fetches` pass with `--ignored`: the design spec's Phase 4 exit.
- TRUSTED.md: the A.1 row is gone; the secret-lifetime, CT-scope, shell and `ServerConfig::wf` rows are updated. RSA keys are refused until Phase 7, in TRUSTED and in the RFC 8446 §9.1 (req) note (Ruling D4).
- `phase-4c` is merged into `main`.

## Preflight (plan self-check against `main` at c1329b9; amended for the 2026-11-05 preflight review, `<scratch>/vt-4c-evidence/preflight.md`)

### Task pairs sharing a file or interface

| Pair | Shared | Producer gives | Consumer needs | Found |
|---|---|---|---|---|
| T1 ↔ all (ruling: quictls crate) | `crates/quictls` (crate, manifest, root profile block); `crates/tls` untouched by T1 and T3's glue | T1 creates the crate with `keys`; T3 adds `server` | T2 changes quic (quictls re-verifies); T3 edits `crates/tls/src/server.rs` only for `lemma_ok_not_failed`; T5 edits `crates/tls/src/config.rs` only for `p256_signing_key`; neither imports a quic item into tls | Consistent: tls never names `quic`, so tls's rlimit margins (`spec_drain`, `build_flight`) are unaffected. The binary gate gains a `quictls` dependent (T1 records its `U` lines). |
| T1 ↔ T3 | `initial_keys`, `packet_keys` | `initial_keys(dcid)` requires `|dcid| ≤ MAX_CID_LEN`; `packet_keys(&[u8; 32])` | `accept` derives from `initial_dcid(d)`; `apply` turns `Secrets { client, server: [u8; 32] }` into slots | Consistent: `accept` checks the length before the call (`initial_dcid`'s ensures give no bound). |
| T1 ↔ T5 | `crates/server/Cargo.toml` (`tls`), `Cargo.lock`, `lib.rs`, `tests/shell.rs` | T1 adds the dependency, replaces the shim's call site, and deletes `a1_keys_only` | T5 replaces `Connection` with `QuicServer`, adds `h3` (preflight I5), and rewrites every remaining shell test (preflight M2) | Consistent: T5 rewrites the call site T1 touched. T1's interim shell keys every DCID with no TLS, which is fine for one task. |
| T1 ↔ T3/T4 | `#[path]` test module | T1 introduces `mod qc` and `mod tc` in quictls tests (ruling: quictls crate) | T3, T4 reuse `qc::{A2, S1, C1, rnd, ltp}` | Consistent; each test file declares the module itself. |
| T2 ↔ T3 | `refeed_one_rtt`, `accept_datagram`'s DCID check, `is_live`, `crypto_end` (via `CryptoStream::end`), `crypto_read`'s bound, `H3Server::on_timeout`'s `now <= now_spec` | names and contracts in T2's Interfaces | `receive`'s body (with `r.refeed`), `sync_keys`, `tls_step` steps 1–3, `QuicServer::on_timeout`/`settled_later` | Consistent after the amendments:<br>• `refeed_one_rtt` masks the slots itself, so T3 passes `&self.keys` unchanged;<br>• `crypto_end` reads a new `CryptoStream::end` (preflight C6);<br>• step 1 reads `crypto_end` before `crypto_read`, so no `crypto_read` frame is needed (preflight C7);<br>• T3 consumes no odcid fact after `on_datagram`, and T2 states only the provable ensures (preflight C5);<br>• `settled_later` gets `now <= now_spec` from T2's `H3Server::on_timeout` ensures, and `acks_later` from `transmit`'s forwarded `None` clause (preflight C8). |
| T2 ↔ T5 | `H3Server::on_datagram` signature | `error` parameter added | the shell uses `QuicServer`, not `H3Server` | Consistent; `h3_alloc.rs` and `h3_server.rs` callers are updated in T2. |
| T3 ↔ T4 | `QuicServer` API, `Rand`, `key_slots`; `crates/quictls/src/server.rs` | T3 creates the file and the API | T4 drives it and adds comments (the exception block, and §4.1.2 at `Complete`; preflight M7) | Consistent: comments only, so no proof re-run beyond the checks.<br>• T4's client sends a uni-stream limit, so the connection survives `pump` and HANDSHAKE_DONE is sent (preflight C2).<br>• T4 opens server packets with a client-side opener (preflight C3).<br>• After completion the 1-RTT keys survive a TLS failure (preflight C9), which `post_handshake_error_closes_under_one_rtt` checks. |
| T3 ↔ T5 | `QuicServer::accept` (`requires cfg.wf()`), `receive`, `transmit`, `on_timeout`, `poll_cid_updates`, `on_reset_candidate`, `send_response`, `conn`; `Rand` with four arrays | T3 | the shell's `Server`, which fills `Rand` fresh, `refeed` included (preflight I1) | Consistent. The shell gets `cfg` only from `build_config`, and its keys from `p256_signing_key`, which discharges `build_config`'s `key_wf` (TRUSTED row amended; preflight M5). |
| T5 ↔ T6 | `bind(SocketAddr)`, `run(sock, &ServerConfig)`, flags, `RESPONSE_BODY`, fixtures | T5 | T6's tests (a leaked `&'static` config; `"127.0.0.1:0".parse()`, preflight M1) and manual run | Consistent. |
| T1/T3/T5 | `TRUSTED.md` | T1 deletes the A.1 row. T3 adds the CT-scope and secret-lifetime rows (C9, M6). T5 updates the shell row, the `ServerConfig::wf` row (D4, M5), the trusted-base bullet, and one clause of the secret-lifetime row (M6) | — | Sequential; T5's edit to T3's row is additive. |
| T1–T5 | `docs/requirements.md` | T1 §5.2; T2 §5.7; T3 seven rows; T4 thirteen, plus the 4d retag, the §9.5 retag to 7 (preflight I3) and the Legend; T5 the RFC 8446 §9.1 (req) note (preflight I4) | — | No row is touched twice. |
| T1/T3/T5 | `docs/crypto-binary-digests.txt` | possible `U` lines from cross-crate inlining | — | Each records its own in its feat commit (3e C26). |

### Each task against itself

| Task | Checked | Found |
|---|---|---|
| T1 | Label hex against rfc9001.txt:2334–2342 (`00 20` = 32, `0f` = 15 = `tls13 client in`); salt against :1066; A.2 arithmetic as in 3e (22 + 245 + 917 + 16 = 1200). | `"quic ku"` deliberately absent (4d). |
| T2 | `refeed_one_rtt`'s order: the completion check precedes any `Connection` call, so the §5.7 ensures is the `return` branch. `CryptoStream::end` is in crypto_stream.rs, where `re` is visible (C6). `crypto_read`'s bound uses `base` monotonicity from `lemma_wf` (M4). The odcid fact is a proof-block assert before `on_datagram` (C5). `on_datagram` with length 0 is 3d2's `early_one_rtt_refed` recipe. The odcid test's datagram `bad ++ p2` is over 1200 bytes, which `accept_datagram` allows (≤ `MAX_UDP_PAYLOAD`); `bad`'s Length covers its 1200 bytes, so `p2` is the walk's second packet. | `p2`'s padding needs no exact target. |
| T3 | Every `Connection` call's `requires` is discharged: `crypto_write` by `theorem_event_discipline`; `on_peer_params` by `theorem_peer_tp_wf`; `close` by `report`'s range split; `ServerHandshake::new` by 174 ≤ 1024.<br>`sync_keys` is the last statement of every method and return path, after `pump` (C1).<br>`Rand` gives `accept_datagram`/`receive`, `refeed_one_rtt` and `on_handshake_complete` three different arrays (I1).<br>`lemma_ok_not_failed` lives in server.rs, beside the private lemmas it needs (I2).<br>`apply` stops after a close by `on_peer_params` or `on_handshake_complete` (I7). | The outline's per-packet hook in `on_datagram` cannot see the gated 1-RTT packet (Ruling D1). The outline's "receive keys only once `!pending(lower)`" is realised as a refusal that closes (no keys are installed then). |
| T4 | The harness's Initial-key swap (client `rx` = server `tx`); a short-header DCID is 8 bytes = `LOCAL_CID_LEN` (`C1` and the server's `L0`-style SCID); the client TP carries `initial_max_streams_uni` 3 (C2); `absorb` decodes HANDSHAKE_DONE (C3); the 0-RTT-before-CH2 case asserts Open after the reset-candidate path (M10). | The HRR path is forced by rustls's X25519 default, so the direct path is covered only by T3's `direct_flight`. |
| T5 | The A.2 reply is still 39 bytes (CC `1c 41 78 00 00` is 5 bytes, like the ACK it replaces), but only the frames are asserted. `chain_needs_schemes` puts the leaf first (C4). The loader's errors are fixed strings (M6). | The `local_params` values changed (3e's test deleted on purpose). |
| T6 | Skips are explicit when tools are missing; the manual run is recorded. | quiche's Go requirement is checked before building. |

## Binding notes for later phases

- **Phase 4d (key update and AEAD limits; outline Tasks 6–7, re-planned):**
  - the 1-RTT slot becomes `OneRtt { phase, current, next_rx, prev_rx }`; `next_secret(secret) = HKDF-Expand-Label(secret, "quic ku", "", 32)`, with vector RFC 9001 A.5 (rfc9001.txt:2510–2527): secret `9ac312a7f877468ebe69422748ad00a15443f18203a07d6060f688f30f21632b` → ku `1223504755036d556342ee9361d253421a826c9ecdf3c7148684b36b714881f9`. SHA-256 HKDF, so it is valid for our suite;
  - `QuicServer` must then keep the 1-RTT traffic secrets (and only those), which changes Task 3's secret-lifetime row;
  - the key-phase bit is read in `rfc_unprotect` and set in `rfc_protect` (HP keys unchanged); KEY_UPDATE_ERROR (0x0e); send keys update before the ACK;
  - no initiation before confirmation or before an ACK in the current phase; a per-key encrypted-packet count below 2²³; a per-connection failed-authentication count, with AEAD_LIMIT_REACHED (0x0f) at 2⁵²; `Rx` must report AEAD failures;
  - §6.3's timing MUST NOT joins §9.5's known gap. Its row note ("constant-time execution is a non-goal") predates 3e's ruling and must be reworded.
- **Phase 7 / before deployment:** RSA key loading (`rsa_key_wf` with primality); Retry or a per-source handshake limit (P-256 or RSA signing per unauthenticated Initial); the SipHash `route` index; `MAX_CONNS` admission under §10.1's 3·PTO floor; parsing `chain_schemes` from the certificates instead of a flag; zeroisation.
- **After 8c:** quic's receive and send paths as CT roots (3e ruling on §9.5); the glue's key handling in the same pass.

## Self-review (done while writing)

- **Spec coverage.** Phase 4 exit: proofs (every task's rlimit-4 run), Appendix A (T1), curl and quiche (T6). Outline 4c Tasks 1–5 → T1, T3, T4, T5, T6; T2 is the earlier-crate edits the glue needs, gated separately; outline Tasks 6–7 → 4d. Every 4c controller ruling has a home:
  - PROTOCOL_VIOLATION level check before `on_crypto`: T3 `tls_step` step 1;
  - `QuicServer::new` requires `cfg.wf()`: T3 `accept`;
  - the `chain_schemes` owner: T5;
  - the error-code range test: T3 `error_ranges`;
  - secret lifetime: T3 and the TRUSTED row;
  - the HsReader push bound: T2's `crypto_read` ensures plus `theorem_reader_bound`.

  3e's Phase 4 binding notes:
  - derive Initial keys: T1;
  - `crypto_read` outside the wake order: T3 `on_timeout`;
  - the `H3Server` switch and its `settled_later` twin: T3, T5;
  - the re-feed: T2, T3;
  - `MAX_CONNS` and the scan: the T5 ponytail;
  - no keyless ack-eliciting packet: T4's `run` assertion;
  - the error in `H3Server::on_datagram`: T2;
  - the odcid: T2.
- **Type consistency.** `Rand` (T3 → T4, T5); `QuicServer::{accept, receive, transmit, on_timeout, poll_cid_updates, on_reset_candidate, send_response, conn, key_slots}` (T3 → T4, T5); `refeed_one_rtt`, `is_live`, `crypto_end`, `odcid_spec` (T2 → T3); `initial_keys`, `packet_keys` (T1 → T3, T4); `p256_signing_key`, `load_config`, `RESPONSE_BODY` (T5 → T6).
- **Proportion.** Bodies appear only where the order is the requirement: `accept`, `receive`, `tls_step`, `apply`, `refeed_one_rtt`.

## Rulings (2026-11-05)

The controller's rulings on the plan's open decisions, recorded in `.superpowers/sdd/2026-11-05-phase-4c-quic-tls-glue/progress.md`:

1. **D1, accepted.** TLS runs after a datagram's long-header packets and before its single, last 1-RTT packet (`refeed_one_rtt`). 1-RTT packets of earlier datagrams are not buffered (the RFC 9001 §5.7 MAY).
2. **D2, accepted.** Key update and the AEAD limits move to Phase 4d.
3. **D3.** RFC 9001 §9.5 is retagged to Phase 7 with the note "not met: quic CT roots after 8c" (Task 4 Step 6).
4. **D4, accepted.** The loader refuses RSA keys until Phase 7: the crypto supports RSA signing, deployment does not. This is stated in TRUSTED and in the RFC 8446 §9.1 (req) row note (Task 5).
5. **D5, accepted.** `chain_schemes` comes from an operator flag; it is parsed from the certificates in Phase 7.
6. **D6, accepted.** Forgetting is state-level. Initial and Handshake packet keys are kept through closing, for CONNECTION_CLOSE, and zeroisation stays a TRUSTED gap. Amended by the preflight C9 ruling: the 1-RTT slot is cleared on a TLS failure only before completion; after completion the close goes out under 1-RTT keys.
7. **D7, accepted.** `Connection::crypto_end`, implemented through `CryptoStream::end` (preflight C6).
8. **D8, accepted.** The interop transport parameters, with the stated memory bound.
9. **D9, accepted.** Our `packet_keys` over rustls's logged secrets.

The preflight review's 26 findings (9 Critical, 7 Important, 10 Minor) are all applied, as the controller ruled. Each change is marked with its finding id.
