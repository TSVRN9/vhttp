# Phase 3d: QUIC connection components — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Eight verified, sans-IO machines in `crates/quic`, each with its own spec and tests, which the sibling plan `2026-10-29-phase-3d2-quic-connection-integration.md` composes into the server `Connection`:
1. stream-layer bounds on 3c's `Streams` (the 3c follow-ups: own-uni cap, absolute send-buffer cap, receive window pinned);
2. received packet numbers and ACK generation;
3. sent-packet records, incoming-ACK processing and the Phase 6 recovery hook (packet-count AIMD placeholder);
4. connection-ID issuance and retirement;
5. handshake CIDs and transport-parameter semantics, including the parsed-peer-TP bound;
6. the 3× amplification budget, exact datagram-length specs and datagram routing;
7. idle timeout, close and draining;
8. the path table (challenges, responses, per-path budgets).

**Where the cut is (3d / 3d2).** 3d is every standalone machine; 3d2 is the `Connection` struct that composes them (receive path, transmit path, timers) and the HTTP/3 adapter.
- Every connection-wide proof obligation (bytes sent ≤ 3× received, Initial datagrams ≥ 1200, nothing sent while draining, PNs strictly increasing, ACKs in their own space) is a property of the packetizer `poll_transmit`, so ACK generation and packetization cannot be split from the connection without leaving a half that has nothing to prove.
- Paths are built into `Connection` from its first line (3d2 Task 1a). The 2026-10-28 drafts added paths afterwards, which meant re-proving `on_datagram` and `poll_transmit` with a per-path budget. This cut proves each big function once.
- A task writes ✅ only on rows whose sections pass its own `duvet_q` run. Each 3d task closes the rows its module discharges on its own (43 rows); rows whose last MUST lands in the composed connection get a "touched (closed in 3d2 Tn)" note here and close in 3d2 (45 rows). `python3 -I <scratch>/chk3d/rows1029.py <scratch>/chk3b/d3.txt` prints `88 43 45` and asserts each of the 88 rows is owned exactly once.

**Architecture:**
- One module per machine, all in `crates/quic`: `ack_track`, `sent`, `recovery`, `cid`, `handshake`, `amp`, `datagram`, `route`, `lifecycle`, `path`. Task 1 edits 3c's `stream_id.rs`, `send_stream.rs` and `streams.rs`; Task 5 adds one theorem to 3b's `tp.rs`.
- Each machine is small enough that a test reaches its edges directly (PN 2⁶²−1, the 33rd ACK range, the 65th incoming ACK range, the 5th pending retirement, the 5th path) without driving a connection.
- **Protection boundary (3e).** 3d consumes `PlainPacket` (decrypted, decoded PN, parsed frames) and emits `OutPacket`s whose exact protected length is the 3d spec fn `out_packet_len`. 3e writes exactly that many bytes, which is how 3d2's amplification proof counts bytes on the wire. These names are unchanged from the 2026-10-28 draft that the 3e plan draft consumes; `OutPacket` gains one field, `spin` (binding note for 3e).
- **TLS boundary (Phase 4).** `Connection::{crypto_read, crypto_write, on_peer_params, on_handshake_complete, on_tls_alert}` in 3d2; these are the outline's `crypto_in` / `crypto_out` (kept under the 2026-10-28 names, which the 3e draft calls).
- **Recovery boundary (Phase 6).** `quic::recovery::Recovery` has fixed signatures and placeholder bodies (Task 3).

**Tech Stack:** Verus 0.2026.10.04.426d8b0 (`~/.local/opt/verus/0.2026.10.04.426d8b0/verus-x86-linux`), vstd `=0.0.0-2026-10-04-0306`, vest_lib `=0.2.2`, duvet 0.4.3. No new crates.

**Spec:** `docs/superpowers/specs/2026-10-27-verified-http3-design.md`, Phase 3 ("ACK generation, idle timeout, close/draining, version negotiation, stateless reset, anti-amplification, minimum Initial datagram size, path validation and connection-ID management"); "Calls I made" (server only, narrow "no migration", sans-IO, shell getrandom for CIDs and reset tokens); non-goals (0-RTT, Retry, migration, proven constant time). Outline: `docs/superpowers/plans/2026-10-28-phase-3-outlines.md` §3d. Codecs: `2026-10-27-phase-3b-quic-codecs.md`. Streams: 3c's merged code (its Interfaces blocks are superseded by the code where they differ) and the "Caller obligations" block at the top of `crates/quic/src/streams.rs`.

## Decisions (recorded)

- **D1. Two plans, cut as above.** 3d2 starts after `phase-3d` merges.
- **D2. Own uni streams are capped inside 3c's `StreamIds`, not in the adapter.** `MAX_OWN_UNI = 3` (RFC 9114 control, QPACK encoder, QPACK decoder). `open_local_uni` refuses `id / 4 >= 3`, and `StreamIds::wf` carries `used <= 3`. Every other `StreamIds` method already ensures `local_uni_spec()` unchanged, so the conjunct costs one proof per method in a 514-line file. h3 opens only stream 3 today; the cap is the RFC's three.
- **D3. Absolute send-buffer bound in `Streams::wf`.** `tx_buffered() <= MAX_SEND_BUFFER` (1 MiB per connection). `write` gains an `Err` case when the new bytes don't fit; `send_room()` reports the room. Every other mutator ensures `tx_buffered` does not grow. `tx_buffered` (Σ physical `buf` length) is the memory itself; `tx_unacked` is not, because a reset empties the buffer while `acked_point` falls back to `acked_base`. 3d2's `Connection::stream_write` accepts a prefix (`min(len, send_room())`), and the 3d2 adapter defers the rest, so no write ever closes the connection for lack of room.
- **D4. Range-set growth: a new-data gate, the in-flight cap and an incoming-ACK range cap (obligation 3, "ACK-range cap"; rewritten by the preflight, C1).**
  - **Why the in-flight cap alone is not enough.** 3c's `poll_stream` loops `poll_data`, lost ranges first, so one record can carry ~200 STREAM frames for one stream. E8's PTO also moves everything in flight into `lost`, where 1-byte ranges separated by acked bytes never merge. Holes are therefore bounded by in-flight *frames* plus accumulated lost ranges, not by the 64 records: ~12.8k per stream.
  - **The gate (Task 1).** `SendStream::poll_data` sends *new* data only while `acked.len() + lost.len() < MAX_SEND_RANGES` (64); lost data and a lone FIN are never gated. New data within one packet is contiguous, so each in-flight record (`MAX_INFLIGHT = 64`, `Recovery::can_send`, Task 3) adds at most one new-data hole per stream. That gives ~2·64 from new data.
  - **The term the gate does not cover.** A large lost range retransmitted in ~1100-byte chunks, alternate-acked, then re-lost on PTO, fragments to chunk size. That adds at most ~`MAX_SEND_BUFFER` / ~1000, about 1000 ranges per connection.
  - **Honest bound:** about 2·64 per send stream plus ~1000 per connection (≈13k across ~103 send streams), so O(10³) per `on_data_acked`, which is per stream (Task 1 review).
  - `SentPackets::on_ack` reads at most the first ACK Range plus `MAX_ACK_RANGES_IN = 64` more, so each incoming ACK costs O(64 × in-flight).
  - **Tested, not proven.** 3c's `range_insert`/`range_remove` carry no length ensures ("Order and merging are exec behavior (tested); only the bounds are proven"), so a `wf` count conjunct is not cheap. Pinned by `range_gate_pto_cycles` (Task 1, simulated PTO cycles) and 3d2 Task 3 `alternate_ack_range_growth` (real PTOs).
- **D5. Only ack-eliciting packets are recorded.** The 2026-10-28 draft recorded ACK-only packets too, and the PTO placeholder drained only eliciting ones, so ACK-only records leaked forever. `on_ack` tolerates acknowledged PNs with no record.
- **D6. Congestion action is a packet-count AIMD placeholder** (cwnd 10 packets, +1 per acked packet up to 64, halved on loss, floor 2). This is "appropriate congestion control action" (§13.3) without RFC 9002's byte accounting. §13.3 therefore closes in 3d2 with no hand-off; Phase 6 replaces the bodies.
- **D7. `peer_tp_wf` is exactly what 3b's parser guarantees** for `from_client = true`, proven in `tp.rs` (Task 5) because `tp_from_decreases` is private there. `on_peer_params` requires it, and `peer_tp_wf ==> stream_tp_ok` discharges `Streams::new` (obligation 4).
- **D8. Receive window pinned.** Every `Streams` mutator ensures `conn_recv_spec().window_spec()` unchanged, `new` ensures it equals `local.initial_max_data`, and `lemma_wf` exports `rx_buffered_phys() <= 2 * window` (3c Task 5 Minor 1; every `RecvCredit` method already keeps the window).
- **D9. Stateless resets are never sent** (§10.3 MAY). Tokens are random per CID with no static key, so §10.3.2's and §21.11's static-key MUSTs and §11's MUST NOT are vacuous; each is a Duvet `type=exception` with its reason. Received resets are detected (3d2).
- **D10. ECN is not accessible** (the shell has no `IP_RECVTOS`) and no ECT is set; every ACK has `ecn: None`, and §13.4.x are exceptions with that reason.
- **D11. Rulings carried from the 2026-10-28 drafts (controller-accepted):** the address is validated only by processing a Handshake packet; tokens never validate; the optional PROTOCOL_VIOLATION MAYs in §19.15, §10.3.2 and §19.16 are taken; closing-state sends are capped against a fresh `AmpBudget`; no CONNECTION_CLOSE before draining; 1-RTT packets are dropped until handshake completion (also RFC 9001 §5.7, the 4b note); the Initial space is discarded on the first processed Handshake packet and the Handshake space at completion; `matches_reset` is constant-time style (xor-accumulate, no early exit inside an entry) and stays a TRUSTED.md known gap; the peer that violates `disable_active_migration` gets path validation, not a drop.

## Global Constraints

- **3b's and 3c's Global Constraints apply unchanged:**
  - Duvet citations: `//= https://www.rfc-editor.org/rfc/rfc9000#section-X` plus a contiguous `//#` quote copied verbatim from `.duvet/specifications/www.rfc-editor.org/rfc/rfc9000.txt`. Vacuous, declined or client-only MUSTs use the `stateless.rs` §10.3.3 form: `//= https://…#section-X`, then `//= type=exception`, then `//= reason=<one line>`, then the `//#` quote. Existing reasons to reuse verbatim: `client-only`, `We never send a Stateless Reset.`
  - sans-IO; no async, trait objects or closures in exec code; no panics; no allocation sized by an untrusted length before it is checked; glob-only spec imports (`#[allow(unused_imports)]` where a glob is spec-only); `Spec*` twins with a `View` on every new pub struct; spec-mode accessors via `#[verifier::when_used_as_spec(<name>_spec)]` as 3c did;
  - each task extends the TRUSTED.md row "Derived `Debug`/`PartialEq`/`Eq` on quic types" with its new type names (unit enums returned by value also derive `Clone`/`Copy`, in that row's `Clone`/`Copy` clause);
  - matrix bookkeeping `✅ 3d: <file>`; a row's earlier "touched … (closed in 3d)" note is *replaced*, not appended to.
- **Proof style (toolchain):**
  - every function verifies at `--rlimit 4`. Put `#[verifier::spinoff_prover]` on any function that needs it (not an escape); never raise the rlimit; split a lemma instead;
  - **no `let … else` inside `proof fn`s** (crashes this Verus); use `match`/`if let`;
  - Verus models `Vec` length, not capacity: when state is dropped, assign a fresh `Vec::new()` / fresh struct, never `clear()`, and add a capacity test outside `verus!` through a `#[doc(hidden)] pub fn …_capacity(&self) -> usize` (3c `SendStream::buf_capacity` precedent);
  - no per-event O(n) copy of attacker-sized data: rebuild a `Vec` at most once per call, never `remove(0)` in a loop over an attacker-sized vector, never re-copy a buffer tail per call (3c Tasks 2 and 4 precedents);
  - loops are isolated (Verus default `loop_isolation(true)`): restate `wf` and every pre-loop fact a loop body needs in its `invariant` (preflight M6).
- **Base branch:** `phase-3d` from `main` (3c merged at c7ef8f0). Record main's head in the Task 1 report.
- **No dependency, toolchain or profile change.** `crates/quic/Cargo.toml` is untouched in 3d; no `rust-toolchain.toml`; no `[profile.*]` edit (Phase 8a will pin rustc 1.98.1 and a release profile).
- **The four checks, every task:**
  1. `scripts/verify.sh` prints the success line it prints on the base commit (today `verify.sh: all crates verified, duvet ok, escapes accounted (N)`; Phase 8a Task 10 rewords it, so match whatever the base prints; preflight M19a), where **N is the value it prints on the base commit** (record it in the Task 1 report; 3d adds no escape, so N never changes);
  2. `cargo build && cargo test` pass across the workspace with 0 warnings, every pre-existing test unchanged; run them also as `cargo +1.98.1 build && cargo +1.98.1 test`, Phase 8a's pinned toolchain, so the 8a merge stays warning-free (preflight M19c);
  3. the escape grep contributes **0** lines from `crates/quic` (line grep and the multi-line `grep -Pz`);
  4. `duvet report` exits 0 (inside verify.sh).
- **Evidence runs** (fresh targets, because `cargo verus` replays cached results when only the args change):
  - `CARGO_TARGET_DIR=<scratch>/vt-3d-tN scripts/verify.sh` with an absolute path, plus `CT_TARGET_DIR=<scratch>/ct-3d-tN` once Phase 8a's `ct-check.sh` is on the base (preflight M19a);
  - `(cd crates/quic && CARGO_TARGET_DIR=<scratch>/vt-3d-tN-r4 cargo verus verify -- --rlimit 4)` in a **new** directory, printing quic `… 0 errors`;
  - then `rm -rf` both (the tmpfs is shared and capped).
  - While iterating, delete `target/verus-partial/debug/.fingerprint/quic-*` before each `cargo verus focus -- --rlimit 4`.
- **Quote check, every task:** `python3 -I <scratch>/qchk/check_quotes.py <repo> <every .rs file the task touched>` prints `N citations, 0 bad` (Duvet doesn't check quote text).
- **MUST coverage, every task with rows:** `duvet report --json <scratch>/vt-3d-tN/duvet.json`, then `python3 -I <scratch>/duvet_q.py <scratch>/vt-3d-tN/duvet.json <the task's sections, comma-separated>` prints nothing: every MUST in those sections is cited or excepted (client-only and declined MUSTs included). The baseline at 3b is `<scratch>/chk3d/musts-open-at-3b.txt` (144 lines over all 3d sections). A task marks ✅ only rows whose sections pass this check; sections whose last MUST lands later get a touched note instead.
- **Mutations, every task:** each listed mutation, applied alone, must make verification fail **on a named postcondition, invariant or assertion, not on rlimit**; report the error line and revert. The reviewer runs two more of their choice, at least one consistent (exec and spec changed together).
- **Units and randomness:** time is `u64` microseconds from the shell; `ms_to_us` saturates (Task 7); randomness is `&[u8; RAND_LEN]` per call (`RAND_LEN = 129` in 3d2: CIDs use `[0, 96)`, path challenges `[96, 128)`, the spin bit `rand[128] & 1`).
- **Consumed from 3b** (exact names, by glob): `PacketKind { Initial, Handshake, OneRtt }`, `frame_permitted`, `ack_eliciting`, `is_ack_eliciting`, `frames_sendable`, `frames_received`, `frames_view`, `spec_frames_bytes`, `serialize_payload`; `Frame` (all variants, 3b field names), `SpecFrame`, `frame_wf`, `frame_type_of`, `spec_frame_type`, `spec_frame_bytes`, `serialize_frame`; `AckFrame { largest, delay, first_range, ranges, ecn }`, `SpecAck`, `rfc_ack_ranges_valid`, `ack_range`, `ack_contains`, `spec_ack_bytes`; `TransportParams`, `SpecTp`, `server_tp_wf`, `rfc_transport_params`, `parse_transport_params`, `serialize_server_params`, `default_transport_params`; `pn_encode_len`, `pn_len_ok`; `rfc_header`, `rfc_long_header`, `parse_header`, `Header`, `SpecHeader`, `LongType`; `rfc_version_negotiation`, `version_negotiation`; wire's `varint_len`, `rfc_varint_min_len`, `VARINT_MAX`; `quic::codes::*` (`PN_MAX`, `MIN_INITIAL_DATAGRAM` 1200, `MAX_CID_LEN` 20, `MIN_SHORT_PACKET` 21, `RESET_TOKEN_LEN` 16, `MAX_STREAMS_LIMIT`, `MAX_ACK_DELAY_LIMIT`, every error code).
- **Consumed from 3c** (merged code): `Streams::{new, on_frame, write, reset, stop_sending, poll_frames, on_frame_acked, on_frame_lost, failed, local_uni_limit, open_streams, lemma_wf}`, `MAX_LOCAL_STREAMS` (100), `stream_tp_ok`, `lemma_server_tp_stream_ok`, `is_stream_layer_frame`; `StreamEvent { Data, Reset, StopSending }`; `CryptoStream::{new, on_crypto, read}`, `MAX_CRYPTO_BUFFER`; `SendStream::{new, write, poll_data, next_off, on_data_acked, on_data_lost}` and `Chunk`.

## Matrix rows these plans close

RFC 9000, labels exactly as in `docs/requirements.md`. 3d closes 43, 3d2 closes 45 (88; checked by `chk3d/rows1029.py`).
- **Task 1:** none (3c strengthenings).
- **Task 2:** §13.2.3, §13.2.5, §13.4.1, §13.4.2.1, §13.4.2.2 (5); touches §13.2.1 and §12.3 (closed in 3d2 Task 2a).
- **Task 3:** none; touches §12.3 (closed in 3d2 Task 2a) and §13.3 (closed in 3d2 Task 3).
- **Task 4:** §5.1, §5.1 (req) "Same CID not issued twice on a connection"; §5.1.1 and its 4 (req) rows; §5.1.2; §19.15 and its 5 open (req) rows; §19.16 and its 3 (req) rows; §10.3.2 (19).
- **Task 5:** §7; §7.2 and (req) "Server sets DCID from first received Initial", "Discard later Initial with different SCID"; §7.3 and (req) "Validate/send initial_source_connection_id; …"; §7.4.1 and (req) "Server MUST reject 0-RTT if restored values unsupported"; §8.1.3 and (req) "Server MUST attempt to validate a token in Initial" (10). Also closes the open tail of RFC 9114 §6.2 (not a 3d row).
- **Task 6:** §5.2.2, §5.2.3, §14.2, §21.11 (4).
- **Task 7:** §10.1, §10.2.3, §11 (3).
- **Task 8:** §8.2.3; §19.17 (2); touches §8.2.1 and its three non-small (req) rows (closed in 3d2 Task 2b, where the 1200-byte sends are built).

Touched notes replaced: 3b's on §5.2.2 (Task 6). 3b's on §10.3 and §19.20 and 3c's on §13.3 are replaced in 3d2.

## Review Focus

1. **Own-uni cap and send-buffer cap really bind** (Task 1). `write(15, ..)` fails with a peer uni limit of 100; `write` of one byte beyond `send_room()` fails with nothing changed; a reset or a full ack restores the room. The new `Streams::wf` conjuncts are exported by `lemma_wf`, and no 3c test changed. Pinned: `own_uni_cap`, `send_buffer_cap`, `room_after_reset`. The new-data gate (D4) holds across loss cycles. Pinned: `range_gate_pto_cycles` (preflight C1).
2. **ACK-only records and incoming range cap** (Task 3). `on_sent` requires an ack-eliciting packet; an ACK for a PN with no record is fine; ranges past the 64th are ignored, not errors. Pinned: `ack_of_unrecorded_pn`, `ack_range_cap_in`.
3. **RETIRE_CONNECTION_ID for the packet's own DCID, or beyond any sequence we issued.** Both PROTOCOL_VIOLATION; retiring twice is harmless. Pinned (Task 4): `retire_rules`.
4. **NEW_CONNECTION_ID whose Retire Prior To covers the CID we send with.** We switch to the lowest active CID; CONNECTION_ID_LIMIT_ERROR is judged after retiring; an identical repeat is not an error. Pinned (Task 4): `rpt_switches_current`, `limit_after_retire`, `duplicate_ok`.
5. **The parsed-peer-TP theorem is the real precondition chain** (Task 5): `rfc_transport_params(b, true) == Ok(t) ==> peer_tp_wf(t)` and `peer_tp_wf(t) ==> stream_tp_ok(t)`, with no assumption about `b`.
6. **Padding arithmetic** (Task 6): `pad_datagram` hits the target exactly when a Length varint grows from 1 to 2 bytes. Pinned: `pad_single_initial`, `pad_coalesced`.
7. **A PATH_RESPONSE arriving on another path validates the challenged path** (§8.2.2 "MUST NOT be enforced"). Pinned (Task 8): `response_any_path`.

---

### Task 1: Stream-layer bounds (3c follow-ups)

**Files:**
- Modify: `crates/quic/src/stream_id.rs`, `crates/quic/src/send_stream.rs`, `crates/quic/src/streams.rs` (module doc "Caller obligations" block too)
- Test: `crates/quic/tests/stream_bounds.rs`

**Interfaces:**
- Consumes: 3c's own items only.
- Produces (`stream_id.rs`):
  - `pub const MAX_OWN_UNI: u64 = 3;` with `// ponytail: RFC 9114 opens at most control + QPACK encoder + QPACK decoder; h3 opens only stream 3 today. Raise with an extension that opens more.`
  - `StreamIds::wf` gains `self.local_uni_spec().used_spec() <= MAX_OWN_UNI`.
  - `open_local_uni`: `ok == (id == 4 * old.used + 3 && old.available > 0 && id / 4 < MAX_OWN_UNI)` (exec guard adds `id / 4 < MAX_OWN_UNI`).
  - `StreamIds::lemma_wf` ensures `self.local_uni_spec().used_spec() <= MAX_OWN_UNI`.
- Produces (`send_stream.rs`):
  - `pub fn buffered(&self) -> (r: usize)`, requires `wf()`, ensures `r == self.buffered_spec()`.
  - `pub proof fn lemma_buffered(&self)`, requires `wf()`, ensures `self.buffered_spec() == if is_reset(self.state()) { 0 } else { (self.all_written().len() - self.acked_base_spec()) as nat }`.
  - New ensures: `write` — `r is Ok ==> final.buffered_spec() == old.buffered_spec() + data@.len()`; every other `&mut self` method (`poll_data`, `reset`, `on_stop_sending`, `on_max_stream_data`, `commit_reset`, `on_reset_lost`, `on_reset_acked`, `on_data_acked`, `on_data_lost`) — `final.buffered_spec() <= old.buffered_spec()`.
  - **New-data gate (preflight C1, D4):**
    - `pub const MAX_SEND_RANGES: usize = 64;` with `// ponytail: new data waits while acked+lost hold 64 ranges; per-stream hole bound is tested (D4), not proven.`
    - `poll_data` takes its new-data branch only while `self.acked.len() + self.lost.len() < MAX_SEND_RANGES`; the lost-first and lone-FIN branches are unchanged.
    - New ensures: `r matches Some(c) && c@.off >= old.sent_end_spec() && c@.data.len() > 0 ==> old.range_count() < MAX_SEND_RANGES`, with `pub closed spec fn range_count(&self) -> nat` = `acked@.len() + lost@.len()`.
    - Sending nothing new is always allowed by `chunk_ok`, so 3c's proofs stand.
    - Outside `verus!`: `#[doc(hidden)] pub fn range_counts(&self) -> (usize, usize)` (moved here from 3d2 Task 2).
- Produces (`streams.rs`):
  - `pub const MAX_SEND_BUFFER: u64 = 1 << 20;` with `// ponytail: one 1 MiB send budget per connection; per-stream budgets if one response must not starve others.`
  - `Streams::wf` gains `self.tx_buffered() <= MAX_SEND_BUFFER as int` and `self.conn_recv.window_spec() == <the stored initial window>` (add a private field `rx_conn: u64`, set to `local.initial_max_data` in `new`).
  - `uni_openable(id)` gains `&&& id / 4 < MAX_OWN_UNI` (so `write`'s existing `r is Ok <==> …` stays exact).
  - **`write`:** the `r is Ok <==> …` clause gains `&& old(self).tx_buffered() + data@.len() <= MAX_SEND_BUFFER`; `Err ==> *final == *old` is kept; add `r is Ok ==> final.tx_buffered() == old.tx_buffered() + data@.len()`. The exec check calls `send_room()` before any swap.
  - **`pub fn send_room(&self) -> (r: u64)`**, requires `wf()`, ensures `r as int == MAX_SEND_BUFFER - self.tx_buffered()`. One loop over `entries` summing `send.buffered()`; invariant `acc == sum(entries@.take(i), 9) <= tx_buffered()`. Needs private `lemma_sum_take(s, i, q)` (`sum(s.take(i + 1), q) == sum(s.take(i), q) + val(s[i], q)`) and `lemma_sum_prefix_le(s, i)` (q = 9 terms are ≥ 0). No overflow: every partial sum ≤ `MAX_SEND_BUFFER`.
  - New ensures on every other pub `&mut self` method (`on_frame`, `reset`, `stop_sending`, `poll_frames`, `on_frame_acked`, `on_frame_lost`): `final.tx_buffered() <= old.tx_buffered()` and `final.conn_recv_spec().window_spec() == old.conn_recv_spec().window_spec()`; `write` also keeps the window. `new` ensures `r.conn_recv_spec().window_spec() == local.initial_max_data` and `r.tx_buffered() == 0`.
  - `lemma_wf` additionally ensures `self.tx_buffered() <= MAX_SEND_BUFFER`, `self.rx_buffered_phys() <= 2 * self.conn_recv_spec().window_spec()` (from `rx_buffered <= counted − consumed <= limit − consumed <= window`), and `self.ids_spec().local_uni_spec().used_spec() <= MAX_OWN_UNI`.
  - Outside `verus!` (`streams.rs`): `#[doc(hidden)] pub fn send_range_counts(&self, id: u64) -> Option<(usize, usize)>` (moved here from 3d2 Task 2; preflight C1).
  - Module doc: replace the bullets "Our own uni streams", "Write backpressure" and "Window is not pinned" with one line each saying what is now enforced and where (`MAX_OWN_UNI`, `MAX_SEND_BUFFER`/`send_room`, D8). Keep "Loop on `poll_data`". Rewrite "ACK-range growth" as: "bounded by the `MAX_SEND_RANGES` new-data gate in `SendStream::poll_data`, `Recovery::can_send`'s in-flight cap and `SentPackets::on_ack`'s range cap; about 2·64 per send stream plus ~1000 per connection, tested not proven (3d D4)" (preflight C1; per-stream wording from Task 1 review).

- [ ] **Step 1: Failing tests** (`tests/stream_bounds.rs`; helpers `local()`/`peer()` copied from 3c's `tests/streams_rx.rs`, `S` = `Frame::Stream`):
  - **`own_uni_cap`:** `peer.initial_max_streams_uni = 100`: `write(3, b"a", false)`, `write(7, ..)`, `write(11, ..)` are `Ok(())`; `write(15, b"a", false) == Err(())`; `local_uni_limit() == 100`.
  - **`send_buffer_cap`:** `peer.initial_max_data = 1 << 30`, `_bidi_local = 1 << 30`. `S(0, 0, "GET", true)`; `send_room() == 1 << 20`; `write(0, &[7; 1 << 20], false) == Ok(())`; `send_room() == 0`; `write(0, &[7], false) == Err(())`; `write(0, &[], true) == Ok(())`.
  - **`room_after_ack`:** continue: `poll_frames(1 << 21, &mut out)` repeatedly until empty, `on_frame_acked(f)` for every frame polled; then `send_room() == 1 << 20` and `open_streams() == 0`.
  - **`room_after_reset`:** `S(0, 0, "GET", false)`, `write(0, &[1; 1000], false)`, `send_room() == (1 << 20) - 1000`; `reset(0, 1)`; `send_room() == 1 << 20`.
  - **`range_gate_pto_cycles`** (preflight C1, simulated PTOs at the `Streams` level):
    - `peer.initial_max_data = 1 << 30`, `_bidi_local = 1`; `S(0, 0, "GET", true)`; `write(0, &[9; 10_000], true)`.
    - For r in 0..400:
      - feed `MaxStreamData{0, r + 2}`;
      - `poll_frames(1200, &mut pkt)`, one "packet" per call;
      - `on_frame_acked` for the frames of every other packet that carried only new data;
      - every 20 rounds, `on_frame_lost` for every frame still outstanding (a PTO).
    - Assert throughout: both counts of `send_range_counts(0) <= 2 * MAX_SEND_RANGES + 1`.
    - Assert once the gate closes: no new-data chunk is polled until a count drops below `MAX_SEND_RANGES`.
    - The splitting adversary (D4's ~1000 term) is not exercised; say so in the test doc.
  - Every 3c test still passes unchanged.
- [ ] **Step 2:** `cargo test -p quic --test stream_bounds` fails (no `send_room`, no cap).
- [ ] **Step 3: Implement** in the order stream_id → send_stream → streams; verify each file with `cargo verus focus -- --verify-only-module <m> --rlimit 4` after deleting the quic fingerprint. No new Duvet citations (no rows).
- [ ] **Step 4: Mutations:**
  - drop `id / 4 < MAX_OWN_UNI` from the `open_local_uni` exec guard → fails on `StreamIds::wf` in `open_local_uni`'s postcondition;
  - skip the `send_room()` check in `Streams::write` → fails on `Streams::wf`'s `tx_buffered` conjunct at `write`;
  - `send_room` returns `MAX_SEND_BUFFER - acc - 1` when `acc < MAX_SEND_BUFFER` → fails on its ensures;
  - delete the `buffered_spec` ensures from `SendStream::on_data_acked` → fails in `streams.rs` at `on_frame_acked`'s new ensures;
  - drop the `MAX_SEND_RANGES` gate from `poll_data` → fails `poll_data`'s new ensures (and `range_gate_pto_cycles`) (preflight C1).
- [ ] **Step 5:** Four checks, evidence runs, quote check (unchanged count; no new citations). Report the five slowest quic functions and any function that newly needed `spinoff_prover`.
- [ ] **Step 6: Commit:** `feat(quic): own-uni cap, absolute send-buffer bound and pinned receive window in the stream layer (3c follow-ups)`. No matrix commit.

---

### Task 2: Received packet numbers and ACK generation (`quic::ack_track`)

**Files:**
- Create: `crates/quic/src/ack_track.rs`
- Modify: `crates/quic/src/lib.rs` (`pub mod ack_track;`), `TRUSTED.md` (extend the derived-impl row with `RecvPns`)
- Test: `crates/quic/tests/ack_track.rs`

**Interfaces:**
- Consumes: `AckFrame`, `SpecAck`, `rfc_ack_ranges_valid`, `ack_contains`, `spec_ack_bytes`, `PacketKind`, `PN_MAX`.
- Produces:
  - `pub const MAX_ACK_RANGES: usize = 32;` `// ponytail: ranges we *generate*; older ranges are forgotten and their PNs refused (§13.2.3); raise if reordering is deep.` (Distinct from Task 3's `MAX_ACK_RANGES_IN`, which caps ranges we *read*.)
  - **`pub struct RecvPns`**, one per space. Private fields: `kind`; `ranges: Vec<(u64, u64)>` (inclusive `(lo, hi)`, descending, disjoint, non-adjacent); `floor: u64` (every PN below is refused); `largest: Option<u64>`, `largest_time: u64`; `eliciting_since_ack: u64`; `first_unacked_time: Option<u64>`; `new_since_ack: bool`; ghost `seen: Set<u64>`, `eliciting_rcvd: nat`, `ack_only_sent: nat`.
  - Closed spec fns `seen()`, `wf()`. `wf()`: `ranges.len() <= MAX_ACK_RANGES`; every PN in a range is in `seen()`; every PN in `seen()` is in a range or `< floor`; `largest == max(seen())` (None iff empty); `ack_only_sent <= eliciting_rcvd`.
  - `pub fn new(kind: PacketKind) -> RecvPns`.
  - **`pub fn is_duplicate(&self, pn: u64) -> (d: bool)`** = `pn < floor || some range contains pn`; ensures `!d ==> !self.seen().contains(pn)` (§12.3).
  - **`pub fn on_packet(&mut self, pn: u64, ack_eliciting: bool, now: u64)`**: requires `!old.is_duplicate(pn)`, `pn <= PN_MAX`; inserts (merging neighbours); on overflow drops the lowest range and sets `floor = its hi + 1` (§13.2.3); updates `largest`/`largest_time`; `ack_eliciting` increments `eliciting_since_ack`/`eliciting_rcvd` and sets `first_unacked_time` if None; sets `new_since_ack`. Ensures `seen() == old.seen().insert(pn)`. `// ponytail: O(ranges) insert; ranges <= 32.`
  - **`pub fn ack_deadline(&self, max_ack_delay_us: u64) -> (d: Option<u64>)`**: None iff `eliciting_since_ack == 0`; Initial/Handshake → `first_unacked_time` (§13.2.1 immediately); OneRtt → `first_unacked_time` if `eliciting_since_ack >= 2` (§13.2.2 SHOULD), else `first_unacked_time + max_ack_delay_us` saturating.
  - `pub fn ack_only_allowed(&self) -> bool` = `eliciting_since_ack > 0`; `pub fn has_new(&self) -> bool`; `pub fn largest(&self) -> Option<u64>` (3e's `decode_pn` input; survives range dropping).
  - **`pub fn build_ack(&self, now: u64, ack_delay_exponent: u64, max_len: usize) -> (r: Option<AckFrame>)`**: requires `ack_delay_exponent <= 20`; None iff `ranges` empty or even the single-range frame exceeds `max_len`; else the longest prefix of `ranges` (highest first) whose `spec_ack_bytes` fits; `first_range = hi₀ − lo₀`, next range `i` is `(lo_{i−1} − hi_i − 2, hi_i − lo_i)` (§19.3.1); `delay` 0 for Initial/Handshake, `(now − largest_time) >> ack_delay_exponent` (saturating at 0) for OneRtt (§13.2.5); `ecn: None`. Ensures `rfc_ack_ranges_valid(r.largest, r.first_range, r.ranges@)`, `ack_contains(r@, pn) ==> self.seen().contains(pn)`, `r.largest == largest.unwrap()`, `spec_ack_bytes(r@).len() <= max_len`. Prove `lemma_build_ack_sound` (acked ⇒ in a range) separately from the length loop.
  - **`pub fn on_ack_sent(&mut self, ack_only: bool)`**: requires `ack_only ==> old.ack_only_allowed()`; clears `eliciting_since_ack`, `first_unacked_time`, `new_since_ack`; ghost `ack_only_sent += ack_only as nat`. With `wf`, this is both §13.2.1 MUST NOTs.

- [ ] **Step 1: Failing tests** (`tests/ack_track.rs`; `A(largest, delay, first, ranges)` is an `AckFrame` with `ecn: None`; OneRtt unless stated):
  - **`dup_suppression`:** `on_packet(5, true, 0)`; `is_duplicate(5)` true, `is_duplicate(4)` false; `on_packet(4, ..)`, `on_packet(7, ..)`; `build_ack(0, 3, 1200) == Some(A(7, 0, 0, [(0, 1)]))`.
  - **`ack_matches_received`** (Initial): PNs 0, 1, 2, 5, 9, 10 → `Some(A(10, 0, 1, [(2, 0), (1, 2)]))`.
  - **`range_cap`:** `on_packet(2k, true, 0)` for k = 0..=32; `is_duplicate(0)` true, `(1)` and `(3)` false (floor = dropped hi + 1 = 1, preflight M1); `build_ack` has 31 pairs and smallest acked PN 2; `largest() == Some(64)`.
  - **`ack_scheduling`:** Initial `on_packet(0, true, 100)` → `ack_deadline(25_000) == Some(100)` (Handshake the same); OneRtt `on_packet(0, true, 100)` → `Some(25_100)`, `on_packet(1, true, 200)` → `Some(100)`, `on_ack_sent(false)` → `None`.
  - **`non_eliciting`:** `on_packet(0, false, 100)` → `ack_deadline(25_000) == None`, `ack_only_allowed() == false`, `has_new() == true`.
  - **`ack_delay_field`:** OneRtt `on_packet(7, true, 1000)`, `build_ack(9000, 3, 1200)` has `delay == 1000`; Initial the same has `delay == 0`.
  - **`build_ack_max_len`** (Initial, PNs as in `ack_matches_received`): `max_len 7` → `A(10, 0, 1, [(2, 0)])`, encoded `02 0a 00 01 01 02 00`; `5` → `A(10, 0, 1, [])`; `4` → `None`.
- [ ] **Step 2:** the tests fail (no module).
- [ ] **Step 3: Implement.** Duvet-cite §13.2.1 (the immediate-ACK MUST at `ack_deadline`; both MUST NOTs and "MUST be acknowledged at least once within the maximum delay" at `on_ack_sent`/`ack_deadline`; the "MUST NOT send an ack-eliciting frame in all packets" MUST at `on_ack_sent`'s doc — we never add one); §13.2.3 (both MUSTs at the range drop); §13.2.5 (at `delay`); §12.3 "A receiver MUST discard a newly unprotected packet unless …" at `is_duplicate`; §13.4.1, §13.4.2.1, §13.4.2.2 as `type=exception`, `reason=ECN is not accessible (no IP_RECVTOS) and no ECT is set; every ACK has ecn: None.` at `ecn: None`.
- [ ] **Step 4: Mutations:** `is_duplicate` ignores `floor`; `build_ack`'s gap `lo − hi − 2` → `− 1`; `on_ack_sent` skips the `ack_only_sent` increment; `ack_deadline` adds `max_ack_delay_us` for Handshake (fails on its ensures only if the ensures states the per-kind cases; state them).
- [ ] **Step 5:** Four checks, evidence, quote check; MUST coverage for `13.2.3,13.2.5,13.4.1,13.4.2.1,13.4.2.2`.
- [ ] **Step 6: Commits:** `feat(quic): verified received-PN tracking, duplicate suppression and ACK generation (RFC 9000 §12.3, §13.2)`; matrix: `✅ 3d: crates/quic/src/ack_track.rs` on §13.2.3, §13.2.5; touched notes on §13.2.1 and §12.3 `3d: ack_track.rs (ACK scheduling / duplicate suppression; closed in 3d2 Task 2a)`; `✅ 3d: exception — ECN not accessible, no ECT set (ack_track.rs ecn: None)` on §13.4.1, §13.4.2.1, §13.4.2.2; `docs: mark RFC 9000 §13.2.x, §13.4.x closed in 3d`.

---

### Task 3: Sent packets, incoming ACKs and the recovery hook (`quic::sent`, `quic::recovery`)

**Files:**
- Create: `crates/quic/src/sent.rs`, `crates/quic/src/recovery.rs`
- Modify: `crates/quic/src/lib.rs`, `TRUSTED.md` (extend the row with `SentPacket`, `SentPackets`, `Recovery`)
- Test: `crates/quic/tests/sent.rs`

**Interfaces:**
- Consumes: `AckFrame`, `SpecAck`, `ack_range`, `ack_contains`, `rfc_ack_ranges_valid`, `Frame`, `PacketKind`, `PN_MAX`, `PROTOCOL_VIOLATION`.
- Produces (`quic::sent`):
  - `pub const MAX_ACK_RANGES_IN: usize = 64;` `// ponytail: ACK ranges read per incoming frame (D4); older ranges are ignored and those packets later count as lost.`
  - `pub open spec fn ack_contains_capped(a: SpecAck, pn: u64) -> bool` = `exists|i: int| -1 <= i < min(a.ranges.len(), MAX_ACK_RANGES_IN) && ack_range(a, i).0 <= pn <= ack_range(a, i).1`. It implies `ack_contains(a, pn)`; prove `lemma_capped_implies`.
  - **`pub struct SentPacket { pub pn: u64, pub time: u64, pub size: u64, pub ack_eliciting: bool, pub frames: Vec<Frame> }`** (+ `SpecSentPacket`). `frames` holds only retransmittable frames (everything except Padding, Ping, Ack, ConnectionClose, PathChallenge, PathResponse). `size` is the packet's `out_packet_len`.
  - **`pub struct SentPackets`**: `next_pn: u64`, `largest_acked: Option<u64>`, `inflight: Vec<SentPacket>` (ascending PN), ghost `issued: Set<u64>`. `wf()`: `next_pn <= PN_MAX`; every issued PN `< next_pn`; `inflight` PNs strictly ascending, each in `issued`, each `ack_eliciting`; `largest_acked is Some(a) ==> a < next_pn`.
  - `pub fn new() -> SentPackets`; `pub fn new_at(next: u64) -> SentPackets` (requires `next <= PN_MAX`; tests).
  - **`pub fn take_pn(&mut self) -> (r: Option<u64>)`**: `Some(n)` iff `old.next_pn < PN_MAX`, with `n == old.next_pn`, `next_pn == n + 1`, `issued == old.issued.insert(n)`, and `forall p in old.issued: p < n`. None = the sender reached 2⁶²−1 (3d2 closes silently).
  - **`pub fn on_sent(&mut self, p: SentPacket)`**: requires `p.ack_eliciting`, `p.pn == old.next_pn − 1`, `p.pn` not in `old.inflight`. ACK-only packets are never recorded (D5).
  - **`pub fn on_ack(&mut self, a: &AckFrame, out: &mut Vec<SentPacket>) -> (r: Result<(), u64>)`**: requires `rfc_ack_ranges_valid(a.largest, a.first_range, a.ranges@)`. `Err(PROTOCOL_VIOLATION)` iff `a.largest >= next_pn` (§13.1 SHOULD), unchanged. Otherwise it appends every in-flight `p` with `ack_contains_capped(a@, p.pn)` to `out` in ascending order, keeps the rest in order (one rebuild of `inflight`, O(inflight · 64)), and sets `largest_acked = max(largest_acked, a.largest)`. PNs with no record are ignored. Ensures each moved record satisfies `ack_contains(a@, pn)` and leaves `inflight`. `// ponytail: O(inflight × 65) per ACK frame; a merge-walk (inflight ascending, ranges descending) if profiling shows it.` (preflight M23)
  - **`pub fn on_packet_lost(&mut self, pn: u64) -> Option<SentPacket>`** (Phase 6 entry; removes and returns).
  - **`pub fn drain_inflight(&mut self, out: &mut Vec<SentPacket>)`**: moves every record (all are eliciting) to `out`; `inflight` becomes `Vec::new()`. PTO placeholder loss declaration and space discard both use it.
  - `pub fn largest_acked(&self) -> Option<u64>`, `pub fn next_pn(&self) -> u64`, `pub fn inflight_len(&self) -> usize`, `pub fn last_sent_time(&self) -> Option<u64>` (time of the newest record).
  - Outside `verus!`: `#[doc(hidden)] pub fn inflight_capacity(&self) -> usize`.
- Produces (`quic::recovery`) — **the Phase 6 hook**; placeholder bodies. Phase 6 keeps the call sites but may extend these signatures (send times, sizes for RTT samples and persistent congestion), since the counts here don't carry what RFC 9002 needs (preflight M7):
  - `pub const PLACEHOLDER_PTO_US: u64 = 999_000;` (kInitialRtt 333 ms + 4·(333/2) ms), `pub const MAX_PTO_BACKOFF: u32 = 6;`, `pub const INITIAL_CWND_PACKETS: u64 = 10;`, `pub const MAX_INFLIGHT: u64 = 64;`, `pub const MIN_CWND_PACKETS: u64 = 2;`.
  - `pub struct Recovery { pto_count: u32, cwnd: u64 }`; `wf()`: `MIN_CWND_PACKETS <= cwnd <= MAX_INFLIGHT`, `pto_count <= MAX_PTO_BACKOFF`.
  - `pub fn new() -> Recovery` (cwnd 10).
  - `pub fn pto_us(&self, space: PacketKind, peer_max_ack_delay_us: u64) -> u64` = `(PLACEHOLDER_PTO_US + (OneRtt ? peer_max_ack_delay_us : 0)) << pto_count`, saturating.
  - `pub fn pto_deadline(&self, space, last_sent: Option<u64>, peer_max_ack_delay_us: u64, amp_blocked: bool) -> Option<u64>`: None if `amp_blocked` or `last_sent` None, else `last + pto_us(..)` saturating (RFC 9002 §6.2.2.1 interplay, a comment reference — that row is Phase 6).
  - **`pub fn can_send(&self, inflight_packets: u64) -> (r: bool)`** = `inflight_packets < cwnd`. Ensures `r ==> inflight_packets < MAX_INFLIGHT` (bounds in-flight records, D4).
  - `pub fn on_packet_sent(&mut self, space, pn, size: u64, now: u64)`: no-op.
  - `pub fn on_ack_received(&mut self, space, newly_acked: usize, ack_delay: u64, now: u64)`: if `newly_acked > 0`: `pto_count = 0`, `cwnd = min(cwnd + newly_acked, MAX_INFLIGHT)`.
  - **`pub fn on_packets_lost(&mut self, space, lost: usize, now: u64)`**: if `lost > 0`: `cwnd = max(cwnd / 2, MIN_CWND_PACKETS)` — the §13.3 congestion action (D6).
  - `pub fn on_pto_fired(&mut self)`: `pto_count = min(pto_count + 1, MAX_PTO_BACKOFF)`.
  - `pub fn on_space_discarded(&mut self, space)`: no-op (RFC 9002 §6.4 in Phase 6).
  - `pub fn on_path_validated(&mut self)`: `pto_count = 0`, `cwnd = INITIAL_CWND_PACKETS` (§9.4 reset; called by 3d2).
  - `// ponytail: placeholder recovery — fixed 999 ms initial PTO with doubling, packet-count AIMD window (10..64), PTO declares the space's in-flight data lost. Phase 6 (RFC 9002) replaces every body; the signatures stay.`

- [ ] **Step 1: Failing tests** (`tests/sent.rs`; `rec(pn)` = `SentPacket{pn, 0, 50, true, [Crypto{0, [pn as u8]}]}`):
  - **`pn_monotonic`:** `take_pn()` gives `Some(0)`, `Some(1)`; `next_pn() == 2`.
  - **`pn_exhaustion`:** `new_at(PN_MAX − 1)`: `Some(PN_MAX − 1)`, then `None`, `None`.
  - **`ack_removes`:** take + `on_sent(rec(n))` for n = 0..=3; `on_ack(&A(2, 0, 0, [(0, 0)]))` → `Ok`, out PNs `[0, 2]`; `largest_acked() == Some(2)`; `inflight_len() == 2`.
  - **`ack_unsent`:** `next_pn() == 4`; `on_ack(&A(4, 0, 0, []))` → `Err(PROTOCOL_VIOLATION)`, out empty, 4 in flight.
  - **`ack_repeat`:** the same ack twice → second out empty; then `A(1, 0, 0, [])` leaves `largest_acked() == Some(2)`.
  - **`ack_of_unrecorded_pn`:** `take_pn()` twice, `on_sent(rec(1))` only; `on_ack(&A(1, 0, 1, []))` → `Ok`, out `[rec(1)]`.
  - **`ack_range_cap_in`:** take and `on_sent(rec(n))` for n = 0..=200; `on_ack(&A(200, 0, 0, [(0, 0); 70]))` → `Ok`; out is the even PNs 72..=200 (65 records); `on_packet_lost(70)` and `on_packet_lost(60)` are `Some` (unacked, the ranges past the 64th were ignored).
  - **`lost_once`:** `on_packet_lost(1)` → `Some(rec(1))`, then `None`.
  - **`drain_frees`:** 3 records, `drain_inflight(&mut out)` → 3 out, `inflight_len() == 0`, `inflight_capacity() == 0`.
  - **`placeholder_pto`:** `pto_us(Initial, 25_000) == 999_000`, `pto_us(OneRtt, 25_000) == 1_024_000`; after `on_pto_fired()` → `1_998_000`; after 10 fires → `999_000 << 6 == 63_936_000`; `on_ack_received(Initial, 1, 0, 0)` → `999_000`.
  - **`pto_not_armed_amp_blocked`:** `pto_deadline(Initial, Some(5), 0, true) == None`; `(.., false) == Some(999_005)`; `(Initial, None, 0, false) == None`.
  - **`aimd`:** `can_send(9)` true, `can_send(10)` false; `on_packets_lost(_, 1, _)` → `can_send(4)` true, `(5)` false; twice more → cwnd 2; `on_ack_received(_, 100, _, _)` → `can_send(63)` true, `(64)` false; `on_path_validated()` → `can_send(10)` false.
- [ ] **Step 2:** the tests fail.
- [ ] **Step 3: Implement.** Duvet-cite §12.3: "MUST increase the packet number by at least one" and "MUST NOT reuse a packet number …" at `take_pn`, the 2⁶²−1 sentence at its `None` branch (3d2 cites the silent close). Plain comment references to RFC 9002 §6.2.1/§6.2.2.1/§7 (Phase 6 rows). §13.3's congestion MUST is cited in 3d2 where `on_packets_lost` is called.
- [ ] **Step 4: Mutations:** `take_pn` returns `next_pn + 1`; `on_ack` uses `ack_contains` with no cap but keeps the capped ensures (fails on the ensures) — or drops the `a.largest >= next_pn` check (fails on `Err` iff); `can_send` returns `inflight <= cwnd` (fails on its ensures at cwnd 64); `on_packets_lost` floors at 1 (fails on `wf`).
- [ ] **Step 5:** Four checks, evidence, quote check. §12.3's MUST coverage is checked in 3d2 (receive side).
- [ ] **Step 6: Commit:** `feat(quic): verified PN allocation, eliciting-only sent records, capped ACK processing; Phase 6 recovery hook with packet AIMD (RFC 9000 §12.3)`. Matrix: append `sent.rs (PN allocation), recovery.rs (AIMD congestion action)` to the §12.3 and §13.3 touched notes; no ✅.

---

### Task 4: Connection IDs (`quic::cid`)

**Files:**
- Create: `crates/quic/src/cid.rs`
- Modify: `crates/quic/src/lib.rs`, `TRUSTED.md` (extend the row with `LocalCids`, `PeerCids`; add the known-gap row "Stateless-reset token comparison (`quic::cid::PeerCids::matches_reset`): constant-time style (xor-accumulate over all 16 bytes of every candidate, no early exit inside an entry), proven equal to `==`; the timing itself is unverified (RFC 9000 §10.3.1)" with "Verus cannot express timing (design non-goal)" / "never (known gap)")
- Test: `crates/quic/tests/cid.rs`

**Interfaces:**
- Consumes: `Frame::{NewConnectionId, RetireConnectionId}`, `frame_wf`, `PROTOCOL_VIOLATION`, `CONNECTION_ID_LIMIT_ERROR`, `RESET_TOKEN_LEN`.
- Produces:
  - `pub const LOCAL_CID_LEN: usize = 8;` (+ `const _: () = assert!(LOCAL_CID_LEN >= 1);` — we never require a zero-length DCID, so the §19.15 send MUST NOT, the §19.15 zero-length-sender MUST on our side, the §19.16 zero-length-provider MUST and §5.1's shared-port MUST are exceptions with `reason=Our connection IDs are 8 bytes (LOCAL_CID_LEN); we never use zero-length connection IDs.`), `ISSUE_CAP_ACTIVE: u64 = 4`, `ISSUE_CAP_LIFETIME: usize = 16` (`// ponytail: lifetime cap (§5.1.1 MAY); raise if long-lived peers rotate CIDs often.`), `PEER_CID_CAP: u64 = 8` (the highest local `active_connection_id_limit` `local_tp_ok` allows).
  - **`pub struct LocalCids`** — fields `active: Vec<(u64, [u8; 8], [u8; 16])>` (seq, cid, token), `ever: Vec<([u8; 8], [u8; 16])>` (≤ `ISSUE_CAP_LIFETIME`), `next_seq: u64`, `max_sent: u64` (the highest seq sent to the peer: 0, the handshake SCID, at `new`; raised by `commit_pending`; `max_sent < next_seq`; preflight I3), `pending: Vec<u64>`, ghost `issued: Map<u64, Seq<u8>>`. `wf()`: `next_seq == ever.len()`; CIDs in `ever` pairwise distinct, tokens pairwise distinct (§5.1, §10.3.2); `active` ⊆ `issued`, seqs ascending; `issued.dom() == [0, next_seq)` (§5.1.1 +1 each).
  - `pub fn new(cid0: [u8; 8], token0: [u8; 16]) -> LocalCids` (seq 0 is our handshake SCID; its token goes in our `stateless_reset_token` TP).
  - **`pub fn issue(&mut self, rand: &[u8], peer_limit: u64) -> (r: bool)`**: requires `rand.len() >= 24`; with `cid = rand[0..8]`, `token = rand[8..24]`, `r` iff `active.len() < min(peer_limit, ISSUE_CAP_ACTIVE)` (§5.1.1 MUST NOT provide more), `ever.len() < ISSUE_CAP_LIFETIME`, `cid ∉ ever`, `token ∉ ever`; then seq `next_seq` is added and pushed to `pending`. A collision returns false (3d2 retries next call).
  - `pub fn pending_frame(&self) -> Option<Frame>` (`NewConnectionId{seq, 0, cid, token}` for the first pending seq still active; ensures `frame_wf`), `pub fn commit_pending(&mut self)`, `pub fn on_frame_lost(&mut self, seq: u64)` (re-pend if active).
  - **`pub fn on_retire(&mut self, seq: u64, packet_dcid: &[u8]) -> (r: Result<Option<[u8; 8]>, u64>)`**: `seq > max_sent` → `Err(PROTOCOL_VIOLATION)` (§19.16 "greater than any previously sent to the peer"; preflight I3); active `seq` whose CID equals `packet_dcid` → `Err(PROTOCOL_VIOLATION)`; active → removed, `Ok(Some(cid))`; else `Ok(None)`. `is_active` stays true until this call (§5.1.1 accept until retired).
  - `pub fn is_active(&self, cid: &[u8]) -> bool`, `pub fn seq_of(&self, cid: &[u8]) -> Option<u64>`, `pub fn active_len(&self) -> usize`.
  - **`pub struct PeerCids`** — fields `zero_len: bool`, `active: Vec<(u64, Vec<u8>, Option<[u8; 16]>, bool /*used*/)>`, `current: u64`, `largest_rpt: u64`, `retire_pending: Vec<u64>`, `retire_unacked: Vec<u64>`, ghost `received: Map<u64, (Seq<u8>, Option<[u8; 16]>)>`. `wf()`: `current` active and used; every received seq is active, or in `retire_pending ∪ retire_unacked`, or its RETIRE was acked (never forgotten without retiring, §5.1.2); `active.len() <= PEER_CID_CAP`; `retire_pending.len() + retire_unacked.len() <= 2 * PEER_CID_CAP` (preflight I4/M24: the memory bound is an invariant, not a consequence of closing); every CID ≤ 20 bytes.
  - `pub fn new(scid0: &[u8]) -> PeerCids`: requires `scid0.len() <= MAX_CID_LEN`; seq 0, no token, `zero_len = scid0.len() == 0`.
  - **`pub fn on_new_cid(&mut self, seq: u64, rpt: u64, cid: &[u8], token: [u8; 16], local_limit: u64) -> (r: Result<(), u64>)`**: requires `rpt <= seq`, `1 <= cid.len() <= 20`, `2 <= local_limit <= PEER_CID_CAP`. Check order (the body; the signature doesn't fix it):
    ```
    1. zero_len                                                    -> Err(PROTOCOL_VIOLATION)   §19.15
    2. seq known with same (cid, token)                            -> Ok, no change unless rpt > largest_rpt, then retire (§5.1.2; controller ruling, Task 4)   §19.15 duplicate
    3. seq known with different cid/token, or cid known under
       another seq, or token equal to another CID's token          -> Err(PROTOCOL_VIOLATION)   §19.15 MAY, §10.3.2 MAY
    4. seq < largest_rpt -> queue RETIRE(seq) unless already in retire_pending/retire_unacked; Ok   §19.15
    5. add (seq, cid, Some(token), used=false)
    6. if rpt > largest_rpt { queue RETIRE for every active seq < rpt and remove them; largest_rpt = rpt }
       else ignore rpt                                                                      §5.1.2, §19.15
    7. if current was retired: current = lowest active seq, mark used
    8. active.len() > local_limit                                  -> Err(CONNECTION_ID_LIMIT_ERROR)   §5.1.1
    9. retire_pending.len() + retire_unacked.len() > 2 * local_limit -> Err(CONNECTION_ID_LIMIT_ERROR)   §5.1.2 MAY
    ```
    Steps 8 and 9 are judged on the counts steps 5–6 *would* produce, before anything is mutated, so `r is Err ==> *final == *old` and `wf()` holds on every path (preflight I4: 3d2's `Connection::wf` keeps `peer_cids` after the close).
  - `pub fn current(&self) -> &[u8]`; `pub fn pending_retire(&self) -> Option<Frame>`, `commit_retire(&mut self)`, `retire_lost(&mut self, seq: u64)`, `retire_acked(&mut self, seq: u64)`.
  - **`pub fn matches_reset(&self, tail: &[u8; 16]) -> bool`**: true iff some *active and used* entry has `Some(tail)` (§10.3.1: never retired or unused ones). Constant-time style per D11, proven equal to the spec.
  - `pub fn used_tokens(&self) -> Vec<[u8; 16]>`; `pub fn has_unused(&self) -> bool`; `pub fn use_next(&mut self) -> Option<Vec<u8>>` (3d2 per-destination CIDs, §9.5).

- [ ] **Step 1: Failing tests** (`tests/cid.rs`; `T(x) = [x; 16]`, `R(x) = [x; 24]`; `PeerCids::new(&[0xc0; 8])`, `N(seq, rpt, cid, tok) = on_new_cid(seq, rpt, cid, tok, 2)` unless stated; `A = [0xa1; 8]`, `B = [0xb1; 8]`):
  - **`issue_sequence`** (`LocalCids::new([0xa0; 8], T(0xb0))`): `issue(&R(1), 4)` then `pending_frame() == Some(NewConnectionId{1, 0, [1; 8], T(1)})`; `issue(&R(2), 4)`, `issue(&R(3), 4)` true; `issue(&R(4), 4)` false (4 active); fresh: `issue(&R(1), 2)` true, `issue(&R(2), 2)` false.
  - **`no_reissue`:** `issue(&([0xa0; 8] ++ [9; 16]), 4)` false (CID); `issue(&([9; 8] ++ [0xb0; 16]), 4)` false (token); `issue(&R(1), 4)` true with seq 1.
  - **`retire_rules`:** after seqs 1, 2: `on_retire(2, &[0xff; 8]) == Err(PROTOCOL_VIOLATION)` (issued, not yet sent; preflight I3); `pending_frame`/`commit_pending` twice (seqs 1, 2 sent); `on_retire(5, &[0xff; 8]) == Err(PROTOCOL_VIOLATION)`; `on_retire(1, &[1; 8]) == Err(PROTOCOL_VIOLATION)`; `on_retire(1, &[0xa0; 8]) == Ok(Some([1; 8]))`; again `Ok(None)`; `is_active(&[1; 8])` false, `(&[2; 8])` true.
  - **`lifetime_cap`:** issue and retire alternately (`peer_limit 4`): the 15th `issue` (seq 15) true, the 16th false.
  - **`zero_length_peer`:** `PeerCids::new(&[])`, `on_new_cid(1, 0, &[1; 8], T(1), 2) == Err(PROTOCOL_VIOLATION)`.
  - **`limit`:** `N(1, 0, &[1; 8], T(1)) == Ok`, `N(2, 0, &[2; 8], T(2)) == Err(CONNECTION_ID_LIMIT_ERROR)`.
  - **`limit_after_retire`:** `N(1, 0, A, T(1))`, `N(2, 1, B, T(2)) == Ok`; active `{1, 2}`; `pending_retire() == Some(RetireConnectionId(0))`.
  - **`rpt_switches_current`:** `current() == [0xc0; 8]`; `N(1, 1, A, T(1))` → `current() == A`; `N(2, 2, B, T(2))` → `B`; pending retires 0 then 1.
  - **`duplicate_ok`:** `N(1, 0, A, T(1))` twice → `Ok`, `Ok`; `N(1, 0, B, T(1)) == Err(PROTOCOL_VIOLATION)`; fresh `N(1, 0, A, T(1))`, `N(3, 0, A, T(3)) == Err(PROTOCOL_VIOLATION)`; fresh `N(1, 0, A, T(1))`, `N(2, 1, B, T(1)) == Err(PROTOCOL_VIOLATION)`.
  - **`non_increasing_rpt`:** `N(1, 1, A, T(1))`, then `N(2, 0, B, T(2)) == Ok`, nothing more retired, active `{1, 2}`.
  - **`seq_below_rpt`:** `N(2, 2, B, T(2))` queues retire 0 only; late `N(1, 0, A, T(1)) == Ok` queues `RetireConnectionId(1)`, `A` not active; replay queues nothing; `commit_retire` twice, `retire_acked(1)`, replay queues `RetireConnectionId(1)` once more (allowed: remembering every acked seq is unbounded).
  - **`retire_backlog`:** `on_new_cid(k, k, [k; 8], T(k), 2)` for k = 1..=4 → `Ok` with nothing committed; k = 5 → `Err(CONNECTION_ID_LIMIT_ERROR)`.
  - **`reset_token_used_only`:** `N(1, 0, A, T(1))` → `matches_reset(&T(1))` false (unused); `N(2, 1, B, T(2))` → `current() == A`, `matches_reset(&T(1))` true, `(&T(2))` false, `(&[0; 16])` false.
- [ ] **Step 2:** the tests fail.
- [ ] **Step 3: Implement.** Duvet-cite §5.1 (both MUSTs; the zero-length one as an exception), §5.1.1 (all four MUSTs), §5.1.2 (both MUSTs), §19.15 (the five open (req) MUSTs), §19.16 (all three; zero-length as exception), §10.3.2 ("MUST be difficult to guess" with "shell randomness" in the doc, "The same stateless reset token MUST NOT be used for multiple connection IDs" at the `ever` check; the static-key, CID-length and reuse-at-other-nodes MUSTs as exceptions `reason=No static key: each token is fresh shell randomness per connection ID, and no stateless reset is ever sent.`).
- [ ] **Step 4: Mutations:** `issue` checks `active.len() <= min(..)`; `on_new_cid` step 8 before step 6; `matches_reset` ignores `used`; `on_retire` skips the own-DCID check; `on_retire` checks `next_seq` instead of `max_sent` (fails `retire_rules`' first call; preflight I3).
- [ ] **Step 5:** Four checks, evidence, quote check; MUST coverage for `5.1,5.1.1,5.1.2,19.15,19.16,10.3.2`.
- [ ] **Step 6: Commits:** `feat(quic): verified connection-ID issuance, retirement and peer CID set (RFC 9000 §5.1, §19.15-19.16)`; matrix: `✅ 3d: crates/quic/src/cid.rs` on the 19 Task 4 rows; zero-length rows note "exception: LOCAL_CID_LEN = 8"; §5.1.1 (req) "Accept issued CID until retired" notes "gate wired in conn.rs (3d2)".

---

### Task 5: Handshake CIDs and transport-parameter semantics (`quic::handshake`, `tp.rs` theorem)

**Files:**
- Create: `crates/quic/src/handshake.rs`
- Modify: `crates/quic/src/tp.rs` (new spec fn and proof fns only; no existing item changes), `crates/quic/src/lib.rs`, `TRUSTED.md` (extend the row with `HandshakeIds`)
- Test: `crates/quic/tests/handshake.rs`

**Interfaces:**
- Consumes: `TransportParams`, `SpecTp`, `server_tp_wf`, `rfc_transport_params`, `rfc_tp_from`, `rfc_tp_apply`, `rfc_tp_value`, `spec_set_int`, `tp_int_valid`, `spec_default_tp`, `serialize_server_params`, `parse_transport_params` (tests), `PacketKind`, `MAX_CID_LEN`, `TRANSPORT_PARAMETER_ERROR`, `CRYPTO_ERROR_BASE`, `PEER_CID_CAP` (Task 4), `MAX_LOCAL_STREAMS`, `stream_tp_ok`, `lemma_server_tp_stream_ok`.
- Produces (`tp.rs`, D7):
  - **`pub open spec fn peer_tp_wf(t: SpecTp) -> bool`**: every integer field `<= VARINT_MAX` (the ten: `max_idle_timeout`, `max_udp_payload_size`, `initial_max_data`, the three `initial_max_stream_data_*`, both `initial_max_streams_*`, `ack_delay_exponent`, `max_ack_delay`, `active_connection_id_limit`); `max_udp_payload_size >= 1200`; `ack_delay_exponent <= 20`; `max_ack_delay < MAX_ACK_DELAY_LIMIT`; `active_connection_id_limit >= 2`; both `initial_max_streams_* <= MAX_STREAMS_LIMIT`; `original_destination_connection_id is None`; `stateless_reset_token is None`; `initial_source_connection_id matches Some(c) ==> c.len() <= MAX_CID_LEN`.
  - `proof fn lemma_tp_apply_wf(id: u64, v: Seq<u8>, t: SpecTp, seen: u32)`: requires `peer_tp_wf(t)`; ensures `rfc_tp_apply(id, v, true, t, seen) matches Some((t2, _)) ==> peer_tp_wf(t2)`. Uses the varint decode bound (`rfc_varint_decode(v) matches Some((_, x)) ==> x <= VARINT_MAX`; take it from `crates/wire/src/varint.rs` if exported, else prove `lemma_decode_le_max` in tp.rs).
  - `proof fn lemma_tp_from_wf(b: Seq<u8>, p: int, t: SpecTp, seen: u32)`: requires `peer_tp_wf(t)`; ensures `rfc_tp_from(b, p, true, t, seen) matches Ok(t2) ==> peer_tp_wf(t2)`; induction with the measure of `tp_from_decreases` (`decreases b.len() - p` with that lemma's facts for progress).
  - **`pub proof fn theorem_peer_tp_wf(b: Seq<u8>)`**: ensures `rfc_transport_params(b, true) matches Ok(t) ==> peer_tp_wf(t)`. No `let … else`.
- Produces (`handshake.rs`):
  - `pub proof fn lemma_peer_tp_stream_ok(t: SpecTp)`: requires `peer_tp_wf(t)`; ensures `stream_tp_ok(t)` (obligation 4: `rfc_transport_params(b, true) == Ok(t) ==> stream_tp_ok(t)` is this composed with the theorem; state the composition as `pub proof fn theorem_parsed_peer_stream_ok(b: Seq<u8>)` ensuring exactly that).
  - **`pub struct HandshakeIds { odcid: Vec<u8>, client_scid: Vec<u8>, local_scid: [u8; 8] }`**, getters `odcid()`, `client_scid()`, `local_scid()`.
  - **`pub fn from_first(kind: PacketKind, dcid: &[u8], scid: &[u8], local_scid: [u8; 8]) -> (r: Option<HandshakeIds>)`**: None iff `kind != Initial`, `dcid.len() ∉ 8..=MAX_CID_LEN`, or `scid.len() > MAX_CID_LEN`; else `odcid = dcid`, `client_scid = scid` (the DCID we send with, §7.2).
  - `pub fn initial_scid_ok(&self, scid: &[u8]) -> bool` = `scid == client_scid` (a later Initial with another SCID is dropped, not an error).
  - **`pub open spec fn local_tp_ok(tp: SpecTp) -> bool`** (precondition on the TP the shell passes to `accept`): with `fill` setting the three ID fields to any valid values, `server_tp_wf(fill(tp))`; `3 <= tp.initial_max_streams_uni <= MAX_LOCAL_STREAMS`; `tp.initial_max_streams_bidi <= MAX_LOCAL_STREAMS`; `2 <= tp.active_connection_id_limit <= PEER_CID_CAP`; `tp.disable_active_migration`; `tp.max_udp_payload_size >= 1200`. Exec twin `pub fn local_tp_ok(tp: &TransportParams) -> (r: bool)` ensuring equality. Prove `lemma_local_tp_streams(tp)`: `local_tp_ok(tp) ==> stream_tp_ok(tp)` and the three `Streams::new` stream-count requires.
  - **`pub fn fill_local_tp(&self, tp: &TransportParams, token0: [u8; 16]) -> (r: TransportParams)`**: `r == tp` except `original_destination_connection_id = Some(odcid)`, `initial_source_connection_id = Some(local_scid)`, `stateless_reset_token = Some(token0)`; ensures `local_tp_ok(tp@) ==> server_tp_wf(r@) && local_tp_ok(r@)` (§7.3: the server sends both).
  - **`pub fn check_peer_tp(&self, tp: &TransportParams) -> (r: Result<(), u64>)`**: `Ok` iff `tp.initial_source_connection_id == Some(client_scid)`, else `Err(TRANSPORT_PARAMETER_ERROR)` (§7.3 absent or mismatched).
  - **`pub fn token_validates(token: &[u8]) -> (r: bool)`**, ensures `!r` (we issue no tokens; §8.1.3: proceed as unvalidated; never INVALID_TOKEN, which is for Retry tokens).
  - **`pub fn check_alpn(alpn: &[u8]) -> (r: Result<(), u64>)`**: `Ok` iff `alpn == b"h3"`, else `Err(CRYPTO_ERROR_BASE + 0x78)` (TLS `no_application_protocol`, RFC 9001 §8.1; §7 "MUST explicitly negotiate").
  - **0-RTT (§7.4.1 req):** nothing to write: 3b's `PacketKind` has no 0-RTT variant, 3e drops 0-RTT packets, Phase 4 never sends `early_data`. Cite at `from_first`'s `PacketKind` match.

- [ ] **Step 1: Failing tests** (`tests/handshake.rs`; `S1 = 8394c8f03e515708`, `C1 = [0xc1; 8]`; `ltp()` = `default_transport_params()` with `initial_max_streams_bidi 10`, `_uni 3`, `active_connection_id_limit 2`, `disable_active_migration true`):
  - **`from_first`:** `(Initial, S1, C1, [0x5a; 8])` → getters `S1`, `C1`, `[0x5a; 8]`; 7-byte DCID → None; `Handshake` → None; 21-byte DCID → None; 21-byte SCID → None; empty SCID accepted.
  - **`later_initial_scid`:** `initial_scid_ok(C1)` true; `[0xc2; 8]` and `[]` false.
  - **`fill_local_tp`:** `fill_local_tp(&ltp(), [0x11; 16])` sets the three fields; `serialize_server_params` of it starts `00 08 8394c8f03e515708 0f 08 5a5a5a5a5a5a5a5a 02 10 1111…`.
  - **`local_tp_rules`:** `local_tp_ok(&ltp())` true; false with each single change: `initial_max_streams_uni 2`, `initial_max_streams_uni 101`, `initial_max_streams_bidi 101`, `active_connection_id_limit 9`, `disable_active_migration false`.
  - **`peer_tp_check`:** `Some(C1)` → `Ok`; `None` → `Err(TRANSPORT_PARAMETER_ERROR)`; `Some([0xc2; 8])` → `Err(TRANSPORT_PARAMETER_ERROR)`.
  - **`rfc9001_a2_iscid_mismatch`:** ids `from_first(Initial, S1, [], _)` (A.2's SCID is empty); peer TP = A.2's 50-byte `quic_transport_parameters` parsed by 3b (its `initial_source_connection_id` is `S1`); `check_peer_tp` → `Err(TRANSPORT_PARAMETER_ERROR)`. This pins a real A.2 inconsistency; Phase 4's A.2 tests must expect it.
  - **`token_never_validates`:** `token_validates(&[1, 2, 3])` and `(&[])` false.
  - **`alpn`:** `b"h3"` → `Ok(())`; `b"h3-29"` and `b""` → `Err(0x178)`.
- [ ] **Step 2:** the tests fail.
- [ ] **Step 3: Implement.** Duvet-cite §7 ("MUST explicitly negotiate an application protocol" at `check_alpn`; "The cryptographic handshake MUST provide …" as exception `reason=Handshake properties are provided by TLS 1.3 (Phase 4).`); §7.2 (the server-DCID MUST at `from_first`, "Any further changes … NEW_CONNECTION_ID" at `initial_scid_ok`'s doc; the four client MUSTs as `reason=client-only`); §7.3 (all four MUSTs at `check_peer_tp`/`fill_local_tp`); §7.4.1 (the reject MUST at `from_first`; the client MUSTs `client-only`; the accept-0-RTT MUSTs and the new-parameter MUST as exceptions `reason=We never accept 0-RTT.` / `reason=binds authors of future specifications, not an implementation`); §8.1.3 (the validate MUST at `token_validates`; client MUSTs `client-only`; NEW_TOKEN MUSTs `reason=We send no NEW_TOKEN frames.`). RFC 9114 §6.2 "MUST allow the peer to create at least three unidirectional streams" at `local_tp_ok`.
- [ ] **Step 4: Mutations:** `peer_tp_wf` adds `initial_max_streams_uni <= 100` (fails on `theorem_peer_tp_wf`); `local_tp_ok` drops the bidi bound (fails at `lemma_local_tp_streams`); `fill_local_tp` swaps odcid and local_scid (fails on its ensures); `check_alpn` accepts `b"h"` prefix match (fails on its ensures).
- [ ] **Step 5:** Four checks, evidence, quote check; MUST coverage for `7,7.2,7.3,7.4.1,8.1.3`.
- [ ] **Step 6: Commits:** `feat(quic): verified handshake CID and transport-parameter checks; parsed peer TPs are in range (RFC 9000 §7.2-7.3, §8.1.3)`; matrix: `✅ 3d: crates/quic/src/handshake.rs` on the 10 Task 5 rows (§7 note "ALPN here; handshake properties Phase 4 TLS"; §7.4.1 (req) note "0-RTT never accepted: no PacketKind, 3e drops, no early_data"); on RFC 9114 §6.2 replace the tail "(open: 3c `Streams::new` requires …; closed in 3d)" with `✅ 3d: crates/quic/src/handshake.rs (local_tp_ok: 3 <= initial_max_streams_uni <= MAX_LOCAL_STREAMS)`.

---

### Task 6: Amplification budget, datagram lengths and routing (`quic::amp`, `quic::datagram`, `quic::route`)

**Files:**
- Create: `crates/quic/src/amp.rs`, `crates/quic/src/datagram.rs`, `crates/quic/src/route.rs`
- Modify: `crates/quic/src/lib.rs`, `TRUSTED.md` (extend the row with `AmpBudget`, `PlainPacket`, `OutPacket`, `OutDatagram`, `CidUpdate`, `CidTable`, `Route`)
- Test: `crates/quic/tests/amp.rs`, `crates/quic/tests/datagram.rs`, `crates/quic/tests/route.rs`

**Interfaces:**
- Consumes: `Frame`, `SpecFrame`, `frame_wf`, `frame_permitted`, `frames_received`, `frames_view`, `spec_frame_type`, `spec_frame_bytes`, `spec_frames_bytes`, `PacketKind`, `pn_encode_len`, `rfc_varint_min_len`, `varint_len`, `rfc_header`/`parse_header`, `SpecHeader`, `LongType`, `rfc_version_negotiation`/`version_negotiation`, `MIN_INITIAL_DATAGRAM`, `MIN_SHORT_PACKET`, `MAX_CID_LEN`, `PN_MAX`, `LOCAL_CID_LEN`, `ISSUE_CAP_ACTIVE` (Task 4).
- Produces (`quic::amp`):
  - ghost `pub enum AmpEv { Recv(nat), Sent(nat), Validated }`, spec `recv_sum`, `sent_sum`, `validated_in` over `Seq<AmpEv>`.
  - **`pub open spec fn amp_ok(t: Seq<AmpEv>) -> bool`** = `forall|i| 0 <= i <= t.len() && !validated_in(t.take(i)) ==> sent_sum(t.take(i)) <= 3 * recv_sum(t.take(i))` (§8.1 over every prefix).
  - **`pub struct AmpBudget { recv: u64, sent: u64, validated: bool, trace: Ghost<Seq<AmpEv>> }`**; `wf()`: `amp_ok(trace)`; `recv == min(recv_sum, u64::MAX)`; `!validated ==> sent == sent_sum`; `validated == validated_in(trace)`.
  - `new()`; `on_recv(&mut self, n: u64)` (pushes `Recv(n)`, saturating); **`budget(&self) -> (b: u64)`** (`u64::MAX − sent` if validated, else `min(3·recv − sent, u64::MAX − sent)` in `u128`, so `sent` never overflows; preflight M4); **`on_sent(&mut self, n: u64)`** (requires `n <= budget()`, pushes `Sent(n)`, ensures `amp_ok`); `validate`; `is_validated`; `pub closed spec fn trace(&self)`.
- Produces (`quic::datagram`) — **the protection boundary for 3e**:
  - `pub type PathId = u64;`, `pub const MAX_DATAGRAM: usize = 1200;` (no PMTUD, §14.2 SHOULD), `pub const AEAD_TAG_LEN: usize = 16;`, `pub const MIN_PN_AND_PAYLOAD: usize = 4;` (RFC 9001 §5.4.2 sample allowance).
  - **`pub struct PlainPacket { pub kind: PacketKind, pub dcid: Vec<u8>, pub scid: Vec<u8>, pub token: Vec<u8>, pub pn: u64, pub frames: Vec<Frame> }`** + `SpecPlain`. **`pub open spec fn plain_wf(p: SpecPlain) -> bool`** = `frames_received(p.frames, p.kind)` (so each frame is `frame_wf`, permitted, not Padding/HandshakeDone, and every CRYPTO/STREAM `offset + |data| <= VARINT_MAX`) `&& p.dcid.len() <= MAX_CID_LEN && p.scid.len() <= MAX_CID_LEN && p.pn <= PN_MAX`. 3d2's `accept`/`on_datagram` require it; 3e discharges it from `parse_payload`'s ensures and its header checks.
  - **`pub struct OutPacket { pub kind: PacketKind, pub dcid: Vec<u8>, pub scid: Vec<u8>, pub pn: u64, pub pn_len: u8, pub frames: Vec<Frame>, pub padding: usize, pub spin: bool }`** (`padding` = zero bytes 3e appends after the frames; `spin` = the 1-RTT spin bit, ignored for long headers) + `SpecOutPacket`; **`pub struct OutDatagram { pub path: PathId, pub packets: Vec<OutPacket> }`** + `SpecOutDatagram`.
  - Length specs (3e's `protect` ensures its output length equals `out_packet_len(p@)`): `plaintext_len(p)` = Σ `spec_frame_bytes(f).len()` + `padding`; `length_field(p)` = `pn_len + plaintext_len + AEAD_TAG_LEN`; `out_packet_len(p)`: OneRtt `1 + |dcid| + pn_len + plaintext_len + 16`; Initial `7 + |dcid| + |scid| + 1 + rfc_varint_min_len(length_field) + pn_len + plaintext_len + 16` (the `+ 1` is Token Length 0); Handshake without the `+ 1`. `out_datagram_len(d)` = Σ.
  - **`pub open spec fn out_packet_wf(p, largest_acked: Option<u64>) -> bool`**: `frames.len() >= 1`; `frames_sendable(frames, kind)` (`serialize_payload`'s precondition, §12.4/§12.5); `pn_len_ok(pn, largest_acked, pn_len)` and `forall|m| 1 <= m < pn_len ==> !pn_len_ok(pn, largest_acked, m)`, which is `pn_encode_len`'s ensures; 3b has no spec twin (preflight M5); `pn_len + plaintext_len >= MIN_PN_AND_PAYLOAD`; `|dcid|, |scid| <= MAX_CID_LEN`, OneRtt ⇒ `scid == []`; `length_field < 16384`.
  - `pub fn packet_len(p: &OutPacket) -> (n: usize)` (`== out_packet_len(p@)`), `pub fn datagram_len(d: &OutDatagram) -> usize`.
  - **`pub fn add_sample_padding(p: &mut OutPacket)`**: `padding = max(padding, 4 − pn_len − frames_len)`; ensures `pn_len + plaintext_len >= 4`.
  - **`pub fn pad_datagram(d: &mut OutDatagram, target: usize)`**: requires `1 <= packets.len() <= 3`, `out_datagram_len(d) <= target`, `MIN_INITIAL_DATAGRAM <= target <= MAX_DATAGRAM`, every CID ≤ 20 bytes; ensures `out_datagram_len(d') == target` and only one packet's `padding` changed. Body (the signature doesn't fix it):
    ```
    i   = first index maximising pn_len + plaintext_len   // its Length ends >= 350 > 64
    gap = target - out_datagram_len(d)
    padding_i += if packets[i] is long-header && length_field(packets[i]) < 64 { gap - 1 } else { gap }
    ```
    Prove `lemma_pad_exact` (bytes outside each Length value ≤ 50, so the chosen Length ends ≥ 350; its varint grows 1 → 2 exactly when it was 1 byte, never past 2 since Length < 16384).
- Produces (`quic::route`):
  - `pub type ConnId = u64;`; `pub const MAX_TABLE: usize = 4096;` (`// ponytail: linear-scan CID table capped at 4096 entries; HashMap when connections exceed ~100.`)
  - **`pub enum CidUpdate { Add(Vec<u8>), Remove(Vec<u8>), AddToken([u8; 16]), RemoveToken([u8; 16]) }`**.
  - **`pub struct CidTable { cids: Vec<(Vec<u8>, ConnId)>, tokens: Vec<([u8; 16], ConnId)> }`**: `new()`; `apply(&mut self, c: ConnId, u: &CidUpdate) -> (ok: bool)` (Add fails, unchanged, if the key is present for any connection or the list is at `MAX_TABLE`; Remove succeeds only for the owner); `remove_conn(&mut self, c)` (rebuilds both lists once); `lookup(&self, cid: &[u8]) -> Option<ConnId>`; `reset_owner(&self, tail: &[u8]) -> Option<ConnId>`; `has_room(&self) -> bool` (= `cids.len() + ISSUE_CAP_ACTIVE + 2 <= MAX_TABLE`).
  - **`pub enum Route { Existing(ConnId), NewInitial, VersionNegotiation(Vec<u8>), Reset(ConnId), Drop }`**.
  - **`pub open spec fn rfc_route(d: Seq<u8>, t: SpecTable) -> SpecRoute`**, `h = rfc_header(d, LOCAL_CID_LEN)`; the first rule that applies:
    1. `h` is Long/Short with `dcid` mapped to `c` → `Existing(c)`;
    2. `h` is `Long{ty: Initial, dcid, ..}`, `d.len() >= 1200`, `8 <= dcid.len()`, `t` has room → `NewInitial` (§14.1, §7.2);
    3. `h` is `UnsupportedVersion` and `rfc_version_negotiation(d) == Some(v)` → `VersionNegotiation(v)` (§6, §5.2.2);
    4. `d.len() >= MIN_SHORT_PACKET` and `t`'s tokens map `d.take_last(16)` to `c` → `Reset(c)` (§10.3 any packet ending in a valid token; §10.3.1 no connection matched);
    5. else `Drop` (§5.2.2 both MUSTs, sub-1200 Initial, unknown Handshake/0-RTT, unmatched short headers, a full table: the §5.2.2 CONNECTION_REFUSED SHOULD is declined).
  - **`pub fn route(datagram: &[u8], table: &CidTable) -> (r: Route)`**, ensures `r@ == rfc_route(datagram@, table@)`. **Binding for 3e:** call `version_negotiation` only via `route` (§17.2.1 once per datagram).

- [ ] **Step 1: Failing tests.**
  - `tests/amp.rs`: **`amp_budget`** (`new()` → 0; `on_recv(1200)` → 3600; `on_sent(3600)` → 0; `on_recv(1)` → 3; `validate()` → `u64::MAX − 3600`; `on_sent(10_000)` → `u64::MAX − 13_600`; preflight M4); **`amp_saturating`** (`on_recv(u64::MAX)`, `on_recv(5)` → `u64::MAX`).
  - `tests/datagram.rs` (`CRYPTO90` = the 90 CRYPTO bytes of RFC 9001 A.3; all `spin: false`):
    - **`a3_server_initial_len`:** `OutPacket{Initial, [], f067a5502a4262b5, 1, 2, [Ack{0, 0, 0, [], None}, Crypto{0, CRYPTO90}], 0, false}` → `packet_len == 135` (20-byte header `c1000000010008f067a5502a4262b50040750001` + 99 + 16).
    - **`a2_client_initial_len`:** `OutPacket{Initial, 8394c8f03e515708, [], 2, 4, [Crypto{0, <the 241 A.2 bytes>}], 917, false}` → `1200` (Length 1182, 2-byte varint, 22-byte header).
    - **`short_sample_padding`:** `OutPacket{OneRtt, [0x11; 8], [], 0, 1, [Ping], 0, false}` → `add_sample_padding` → `padding == 2`, `packet_len == 29`.
    - **`pad_single_initial`:** `OutPacket{Initial, [0xc1; 8], [0x5a; 8], 0, 1, [Ping], 0, false}` is 43; `pad_datagram(_, 1200)` → `padding == 1156`, `datagram_len == 1200` (Length 1 → 2 bytes).
    - **`pad_coalesced`:** that Initial + `OutPacket{Handshake, [0xc1; 8], [0x5a; 8], 0, 1, [Crypto{0, [7; 30]}], 0, false}` (74) = 117; `pad_datagram(_, 1200)` → `packets[1].padding == 1082`, `packets[0].padding == 0`, 1200.
    - **`pad_short`:** the 29-byte packet → `padding == 1173`, 1200.
  - `tests/route.rs` (`t` has, for connection 7, `Add(8394c8f03e515708)`, `Add([0x11; 8])`, `AddToken([0x77; 16])`; `A2H = c000000001088394c8f03e5157080000449e`):
    - **`route_existing`:** `A2H` zero-padded to 1200 → `Existing(7)`; `[0x40] ++ [0x11; 8] ++ [0; 20]` → `Existing(7)`.
    - **`route_new_initial`:** `A2H` padded to 1200, empty table → `NewInitial`; a 7-byte-DCID Initial whose Length fits 1200 → `Drop`; `A2H` with Length `0x449d` padded to 1199 → `Drop`. A.2's own Length 1182 would fail `rfc_header` first and not test §14.1 (preflight M3).
    - **`route_vn`:** 3b's `vn_response` input → `VersionNegotiation(c0 00000000 04 0a0b0c0d 08 0001020304050607 00000001)`; truncated to 1199 → `Drop`.
    - **`route_reset`:** `[0x40] ++ [0x22; 8] ++ [0x33; 5] ++ [0x77; 16]` (30) → `Reset(7)`; tail `[0x78; 16]` → `Drop`; a 1200-byte Handshake long header with an unknown 8-byte DCID → `Drop`.
    - **`table_rules`:** `apply(8, Add([0x11; 8]))` false, lookup still 7; `apply(8, Remove(..))` false; `apply(7, Remove(..))` true, lookup None; `remove_conn(7)` empties both.
    - **`table_full`:** add 4091 distinct 8-byte CIDs for connection 1 (4090 + 6 = 4096 still has room; preflight M2); `has_room()` false; `A2H` padded to 1200 with an unknown DCID → `Drop`.
- [ ] **Step 2:** the tests fail.
- [ ] **Step 3: Implement.** Duvet-cite §8.1's two server MUSTs at `amp_ok`/`on_sent` and `on_recv` (the rows close in 3d2 where every send is gated); §14.2 (the SHOULD at `MAX_DATAGRAM`; the cease-sending MUST as exception `reason=No PMTUD: we never determine a PMTU below 1200, and never send more than 1200 bytes.`); §5.2.2 (both MUSTs at rule 5); §5.2.3 and §21.11 (exceptions `reason=We never send a Stateless Reset.` plus `reason=No static key …` for §21.11's static-key MUST); §10.3 "MUST treat any packet ending in a valid stateless reset token as a Stateless Reset" at rule 4 (row closes in 3d2); §14.1's discard MUST at rule 2 (row closes in 3d2).
- [ ] **Step 4: Mutations:** `amp_ok` over the whole trace only (fails at `on_sent` on a prefix); `budget` computed in `u64` without saturation (fails on overflow check); `pad_datagram` always adds `gap` (fails at `lemma_pad_exact`'s use); `rfc_route` rule order "reset before Existing" and "NewInitial before Existing" with the exec unchanged (each fails on `route`'s ensures; ruling: 3-before-1 is neutral, the rules match disjoint header kinds).
- [ ] **Step 5:** Four checks, evidence, quote check; MUST coverage for `5.2.2,5.2.3,14.2,21.11`.
- [ ] **Step 6: Commits:** `feat(quic): verified amplification trace budget, exact datagram length specs, CID routing (RFC 9000 §5.2.2, §8.1, §14)`; matrix: `✅ 3d: crates/quic/src/route.rs` on §5.2.2 (replacing 3b's touched note); `✅ 3d: route.rs (exception: never sends resets, no static key)` on §5.2.3 and §21.11; `✅ 3d: datagram.rs MAX_DATAGRAM (exception: no PMTUD)` on §14.2. Also mark §10.3.3 (3b-owned and excepted in stateless.rs, but its matrix row lacks ✅; outside the 88) as `✅ 3b: exception — we never send a Stateless Reset (stateless.rs)` (preflight M20).

---

### Task 7: Idle timeout, close and draining (`quic::lifecycle`)

**Files:**
- Create: `crates/quic/src/lifecycle.rs`
- Modify: `crates/quic/src/lib.rs`, `TRUSTED.md` (extend the row with `Phase`, `Lifecycle`, `IdleTimer`)
- Test: `crates/quic/tests/lifecycle.rs`

**Interfaces:**
- Consumes: `AmpBudget` (Task 6), `Frame::ConnectionClose`, `frame_wf`, `frame_permitted`, `PacketKind`, `APPLICATION_ERROR`, `VARINT_MAX`.
- Produces:
  - **`pub fn ms_to_us(ms: u64) -> u64`** = `if ms > u64::MAX / 1000 { u64::MAX } else { ms * 1000 }`.
  - **`pub fn effective_idle_us(local_ms: u64, peer_ms: Option<u64>, pto_us: u64) -> (r: Option<u64>)`**: with `p = peer_ms.unwrap_or(0)`, None iff `local_ms == 0 && p == 0`, else `Some(max(ms_to_us(m), 3·pto_us))` with `m` the minimum non-zero value, saturating (§10.1).
  - **`pub struct IdleTimer { last: u64, eliciting_since_rx: bool }`**: `new(now)`; `on_packet_processed(now)` (last = now, clear flag); `on_eliciting_sent(now)` (last = now only if the flag is clear, then set it); `deadline(eff: u64) -> u64` (saturating).
  - **`pub fn close_frame(app: bool, code: u64, reason: &[u8], space: PacketKind) -> (f: Frame)`**: requires `code <= VARINT_MAX`, `reason.len() <= 64`. `space != OneRtt && app` → `ConnectionClose{false, APPLICATION_ERROR, 0, []}` (§10.2.3); else `ConnectionClose{app, code, 0, reason}`. Ensures `frame_wf(f@)` and `frame_permitted(spec_frame_type(f@), space)`.
  - **`pub fn close_spaces(confirmed: bool, initial_live: bool, handshake_live: bool, one_rtt_live: bool) -> Vec<PacketKind>`**: `confirmed` → `[OneRtt]` (§10.2.3 MUST); else the live spaces in order Initial, Handshake, OneRtt.
  - **`pub enum Phase { Open, Closing, Draining, Closed }`** (Clone/Copy).
  - **`pub struct Lifecycle`** — `phase`, `deadline: Option<u64>`, `close: Option<(bool, u64, Vec<u8>)>`, `first_sent: bool`, `owed: bool`, `budget: AmpBudget` (closing-state only):
    - `new()` (Open); **`enter_closing(&mut self, now, pto_us, app: bool, code: u64, reason: &[u8])`** (requires `code <= VARINT_MAX`; only from Open, else no-op — first error wins, §11.1; deadline `now + 3·pto_us`; `owed = true`; reason truncated to 64 bytes `// ponytail: 64-byte reason cap.`); **`enter_draining(&mut self, now, pto_us)`** (from Open or Closing; deadline `now + 3·pto_us`; no-op from Draining/Closed); `close_silently(&mut self)` (→ Closed); `on_recv_closing(&mut self, n: u64)` (Closing: `budget.on_recv(n)`, `owed = true`); **`may_send_close(&self, n: u64) -> bool`** = `phase is Closing && owed && (!first_sent || n <= budget.budget())`; `on_close_sent(&mut self, n)` (requires `may_send_close(n)`; clears `owed`; first send sets `first_sent`, later ones `budget.on_sent(n)`); `on_timeout(&mut self, now)` (Closing/Draining with `now >= deadline` → Closed); getters `phase()`, `deadline()`, `close_info()`.
    - Ensures/invariants: phase only moves forward (Open → Closing → Draining → Closed, Open → Draining, anything → Closed); `may_send_close` false outside Closing (§10.2.2); `amp_ok(budget.trace())` (§10.2.1).

- [ ] **Step 1: Failing tests** (`tests/lifecycle.rs`):
  - **`idle_effective`:** `(30000, Some(0), 999_000)` → `Some(30_000_000)`; `(30000, Some(10000), _)` → `Some(10_000_000)`; `(0, Some(5000), _)` → `Some(5_000_000)`; `(1, Some(0), 999_000)` → `Some(2_997_000)`; `(0, Some(0), _)` and `(0, None, _)` → `None`; `(VARINT_MAX, Some(0), 999_000)` → `Some(u64::MAX)`.
  - **`idle_restart`:** `new(0)`; `on_packet_processed(100)` → `deadline(10) == 110`; `on_eliciting_sent(200)` → 210; `on_eliciting_sent(300)` → 210; `on_packet_processed(400)` → 410.
  - **`close_frame_conversion`:** `(true, 0x0100, b"bye", Initial)` → `ConnectionClose{false, 0x0c, 0, []}` (Handshake the same); `OneRtt` → `{true, 0x0100, 0, b"bye"}`; `(false, 0x0a, b"x", Handshake)` → `{false, 0x0a, 0, b"x"}`.
  - **`close_spaces`:** `(true, false, false, true)` → `[OneRtt]`; `(false, true, true, false)` → `[Initial, Handshake]`; `(false, false, true, true)` → `[Handshake, OneRtt]`.
  - **`closing_budget`:** `enter_closing(0, 1000, false, 0x0a, b"")`, `deadline() == Some(3000)`; `may_send_close(30)` true, `on_close_sent(30)`, then false; `on_recv_closing(9)` → false (27); `on_recv_closing(9)` → true (54); `on_close_sent(30)`; `on_timeout(2999)` Closing; `on_timeout(3000)` Closed.
  - **`draining_silent`:** `enter_draining(10, 1000)`: `may_send_close(1)` false, `deadline() == Some(3010)`; `enter_closing(..)` stays Draining; `on_timeout(3010)` → Closed; separately Closing → `enter_draining` → Draining.
- [ ] **Step 2:** the tests fail.
- [ ] **Step 3: Implement.** Duvet-cite §10.1 (the 3×PTO MUST), §10.2.3 (all three MUSTs), §10.2.1 (both MUSTs at `may_send_close`; rows close in 3d2), §10.2.2 (both MUST NOTs; closes in 3d2), §11 (exception `reason=We never send a Stateless Reset.`).
- [ ] **Step 4: Mutations:** `effective_idle_us` without the `3·pto` floor; `close_frame` keeps the reason in Initial; `may_send_close` true in Draining; `enter_closing` overwrites an earlier close.
- [ ] **Step 5:** Four checks, evidence, quote check; MUST coverage for `10.1,10.2.3,11`.
- [ ] **Step 6: Commits:** `feat(quic): verified idle timer, close/drain lifecycle and close-frame conversion (RFC 9000 §10.1, §10.2)`; matrix: `✅ 3d: crates/quic/src/lifecycle.rs` on §10.1 and §10.2.3; `✅ 3d: exception — no stateless reset is ever sent` on §11.

---

### Task 8: Path table (`quic::path`)

**Files:**
- Create: `crates/quic/src/path.rs`
- Modify: `crates/quic/src/lib.rs`, `TRUSTED.md` (extend the row with `PathState`, `Path`, `Paths`)
- Test: `crates/quic/tests/path.rs`

**Interfaces:**
- Consumes: `AmpBudget`, `PathId` (Task 6).
- Produces:
  - `pub const MAX_PATHS: usize = 4;` (`// ponytail: datagrams from a 5th distinct path are dropped uncounted (§9 "MUST either drop" branch).`), `pub const MAX_RESPONSES: usize = 4;` (per path; further challenges dropped until responses go out; the peer retransmits, §8.2.1 MAY).
  - **`pub enum PathState { Unvalidated, Validating, Validated }`** (Clone/Copy).
  - **`pub struct Path`** — `id`, `amp: AmpBudget`, `state`, `challenge: Option<([u8; 8], u64 /*started_at, preflight I5*/, bool /*padded*/)>`, `challenge_owed: bool` (started, not yet sent), `mtu_ok: bool`, `responses: Vec<[u8; 8]>`, `dcid: Option<Vec<u8>>` (the peer CID we send with on this path; None = nothing may be sent there, §9.5; preflight I1), `peer_used: Option<Vec<u8>>` (our CID the peer last used on this path), ghost `challenges_rcvd: Seq<[u8; 8]>`, `responses_taken: Seq<[u8; 8]>`.
  - **`pub struct Paths { paths: Vec<Path>, active: PathId, last_validated: Option<PathId> }`**; `wf()`: ids unique, `paths.len() <= MAX_PATHS`, `active` present; every `amp.wf()`; `responses_taken` is a sub-multiset of `challenges_rcvd` in order (one response per challenge, same data, §8.2.2); `last_validated is Some(p) ==> state(p) == Validated`; `responses.len() <= MAX_RESPONSES`.
  - `new(first: PathId) -> Paths` (Unvalidated, active); `index(&self, id) -> Option<usize>`; `insert(&mut self, id) -> (ok: bool)` (false when full).
  - `on_recv(&mut self, id, n: u64)`, `budget(&self, id) -> u64`, `on_sent(&mut self, id, n: u64)` (requires `n <= budget(id)`), `pub closed spec fn amp_trace(&self, id) -> Seq<AmpEv>` with `amp_ok` exported.
  - **`set_validated(&mut self, id)`** (handshake §8.1 and `on_response`): `amp.validate()`, Validated, `last_validated = Some(id)`.
  - **`on_challenge(&mut self, id, data: [u8; 8])`**: push to `responses` if room; ghost `challenges_rcvd.push(data)` (§19.17).
  - **`take_response(&mut self, id) -> (r: Option<[u8; 8]>)`**: pops the oldest; ensures `r` extends `responses_taken` consistently with `challenges_rcvd` (taken at most once).
  - **`start_challenge(&mut self, id, data: [u8; 8], now: u64)`**: `challenge = Some((data, now, false))`, `challenge_owed = true`, Unvalidated → Validating. `data` from shell randomness (§8.2.1 unpredictable).
  - **`take_challenge(&mut self, id, padded: bool) -> Option<[u8; 8]>`**: if owed, clears `challenge_owed`, records `padded`, returns the data (3d2 builds the datagram and says whether it reached 1200). The challenge's clock is its `start_challenge` time; `deadline`/`on_timeout` use it (preflight I5).
  - **`on_response(&mut self, data: [u8; 8]) -> (r: Option<PathId>)`**: matches *any* path's outstanding challenge (no arrival-path parameter, §8.2.2 "MUST NOT be enforced"); on a match `set_validated`, `challenge = None`, `mtu_ok = padded`, returns the path; else None.
  - **`needs_mtu_probe(&self, id) -> bool`** = `state == Validated && !mtu_ok && challenge is None` (§8.2.1, §8.2.3 second validation at 1200).
  - **`on_timeout(&mut self, now: u64, pto_us: u64) -> (failed: Option<PathId>)`**: one failure per call. 3d2 Task 3 loops until None (preflight I5). For the first path with `challenge = Some((_, t, _))`, not owed, and `now >= t + 3·pto_us` (§8.2.4 SHOULD): clear the challenge, return it; state back to Unvalidated unless Validated (a failed MTU probe keeps Validated, `mtu_ok` false).
  - `deadline(&self, pto_us) -> Option<u64>`, `active()`, `set_active(&mut self, id)`, `last_validated()`, `state(id)`, `dcid(id) -> Option<&[u8]>`, `set_dcid(&mut self, id, d: Option<&[u8]>)` (None clears it; preflight I1/I2), `peer_used(id) -> Option<&[u8]>`, `set_peer_used(&mut self, id, d: &[u8])`, `has_response(id) -> bool`, `challenge_owed(id) -> bool`.

- [ ] **Step 1: Failing tests** (`tests/path.rs`; `D(x) = [x; 8]`):
  - **`respond_echo`:** `new(0)`, `on_challenge(0, D(1))`; `take_response(0) == Some(D(1))`, then `None`.
  - **`two_challenges`:** D(1), D(2) → D(1), D(2), None.
  - **`response_cap`:** 5 challenges → 4 responses D(1)..D(4).
  - **`response_any_path`:** `new(0)`, `set_validated(0)`, `insert(1)`, `start_challenge(1, D(9), 100)`, `take_challenge(1, true) == Some(D(9))`; `on_response(D(9)) == Some(1)`; `state(1) == Validated`, `budget(1) == u64::MAX`.
  - **`wrong_response_ignored`:** same setup; `on_response(D(8)) == None`; `state(1) == Validating`.
  - **`mtu_second_validation`:** `start_challenge(1, D(9), 0)`, `take_challenge(1, false)`, `on_response(D(9)) == Some(1)`; `needs_mtu_probe(1)` true; `start_challenge(1, D(10), 10)`, `take_challenge(1, true)`, `on_response(D(10))`; `needs_mtu_probe(1)` false.
  - **`validation_timeout`:** `start_challenge(1, D(9), 100)`, `take_challenge(1, true)`; `deadline(999_000) == Some(2_997_100)`; `on_timeout(2_997_099, 999_000) == None`; `on_timeout(2_997_100, 999_000) == Some(1)`, `state(1) == Unvalidated`.
  - **`path_cap`:** `insert(1)`, `(2)`, `(3)` true; `insert(4)` false.
  - **`per_path_amp`:** `insert(1)`, `on_recv(1, 100)` → `budget(1) == 300`, `budget(0) == 0`.
- [ ] **Step 2:** the tests fail.
- [ ] **Step 3: Implement.** Duvet-cite §8.2.1 ("MUST use unpredictable data" at `start_challenge`; the expand MUST and "second path validation" MUST at `take_challenge`/`needs_mtu_probe` — the padding itself is 3d2's, so the expand (req) row's citation is repeated at 3d2's builder); §8.2.3 (at `needs_mtu_probe`); §19.17 (at `on_challenge`/`take_response`). §8.2.1's "MUST NOT discard … too small" is 3d2's.
- [ ] **Step 4: Mutations:** `on_response` also requires the arrival path; `take_response` returns the newest; `needs_mtu_probe` ignores `mtu_ok`; `on_timeout` uses `2·pto_us`.
- [ ] **Step 5:** Four checks, evidence, quote check; MUST coverage for `8.2.3,19.17`.
- [ ] **Step 6: Commits:** `feat(quic): verified path table — per-path amplification, challenge/response bookkeeping (RFC 9000 §8.2, §19.17)`; matrix: `✅ 3d: crates/quic/src/path.rs` on §8.2.3 and §19.17; touched notes `3d: path.rs (closed in 3d2 Task 2b)` on §8.2.1 and its three non-small (req) rows.

---

## 3c follow-ups (binding obligations on 3d, ruled from 3c's tasks and final review)

| # | Obligation | Placed in |
|---|---|---|
| 1 | Cap the uni streams we open (h3: control + QPACK enc/dec = 3) | 3d Task 1 (`MAX_OWN_UNI` in `StreamIds::wf`, `uni_openable`) |
| 2 | Absolute write backpressure (3c proves only buffered ≤ 2·unacked; `write` never refused) | 3d Task 1 (`MAX_SEND_BUFFER` in `Streams::wf`, `write` Err, `send_room`); 3d2 Task 1b (`stream_write` accepts a prefix); 3d2 Task 4 (adapter defers, `send_response` refuses while a deferral is pending, before h3 commits) |
| 3 | ACK-range cap or min chunk, against alternate-ack + credit-drip growth | 3d Task 1 (`MAX_SEND_RANGES` new-data gate in `SendStream::poll_data`, `range_gate_pto_cycles`; preflight C1); 3d Task 3 (`MAX_ACK_RANGES_IN`, `Recovery::can_send` ≤ 64 in flight, eliciting-only records); 3d2 Task 2a (`can_send` gate); 3d2 Task 3 (`alternate_ack_range_growth` with PTO cycles). Bound tested, not proven (D4) |
| 4 | `rfc_transport_params(b, true) == Ok(t) ==> stream_tp_ok(t)` for `peer_tp_wf` | 3d Task 5 (`theorem_peer_tp_wf`, `theorem_parsed_peer_stream_ok`) |
| 5 | Loop on `poll_data`'s result, never on `next_off()` | 3d2 Task 2a (CRYPTO packing: `next_off` only sizes the header, one `poll_data` per space per packet, branch on its result); 3c's `poll_stream` already does |
| 6 | Verus models Vec length: drop buffers on removal; capacity tests | 3d Tasks 3 (`drain_frees`); 3d2 Tasks 1a–3 (`discard` assigns fresh `CryptoStream`/`SendStream`/`RecvPns` and drains `SentPackets` (a fresh one would reset `next_pn`; preflight M17); `streams = None` on close; capacity tests) |
| 7 | No per-event O(n) copies of attacker sizes | 3d Task 3 (`on_ack` rebuilds once), Task 6 (`remove_conn` once); 3d2 Task 4 (pending writes keep an offset, never re-copy the tail) |
| 8 | Receive window not pinned (3c Task 5 Minor 1) | 3d Task 1 (window ensures, `lemma_wf` exports `rx_buffered_phys ≤ 2·window`) |
| 2b-1 | Bounded streams; every event to H3Conn in order | 3d Task 5 (`local_tp_ok` ≤ `MAX_LOCAL_STREAMS`); 3d2 Task 4 (pump proof obligation) |
| 2b-2 | `start()` before any event | 3d2 Task 4 (drain gated on `started`) |
| 2b-3 | `initial_max_streams_uni >= 3` encoded | 3d Task 5 (`local_tp_ok`; RFC 9114 §6.2 tail closed) |
| 2b-4 | Abort signal on Reset | 3d2 Task 4 (`AppEvent::Aborted(id)` on every client-bidi `Reset`) |
| 3c | Frames polled are frames sent; forward every StopSending | 3d2 Task 2a (P8), Task 4 |
| 3b | spin bit random per CID (§17.4); ack_contains meaningful under valid ranges | 3d Task 6 (`OutPacket.spin`); 3d2 Tasks 1a–1b (`rand[128]` per CID change); 3d Task 3 (`on_ack` requires `rfc_ack_ranges_valid`) |
| 4b | No 1-RTT processing before handshake complete (RFC 9001 §5.7) | 3d2 Task 1a (1-RTT dropped until `on_handshake_complete`; cite §5.7 there) |

## Binding notes for later phases

- **3e:** `OutPacket` gains `spin: bool` (append `, false` to the 3e draft's literal `OutPacket{…}` vectors; 3e's `protect` passes it to `serialize_short_header`). `accept`/`on_datagram` now *require* `plain_wf` for every packet: discharge it from `parse_payload`'s `Ok` ensures (`frames_received`), the header's CID lengths and `decode_pn`'s bound. `RAND_LEN` is 129. 3d2's `poll_transmit` now also exports `out_log()`, P7 on its result and P16 (`out_datagram_len <= MAX_DATAGRAM`), which 3e Task 5's `transmit` needs, so 3e's Decision 14 fallback is moot. 3e's cross-references to "3d Task 5/7", `2026-10-28-phase-3d2-quic-paths.md` and `tests/conn.rs` move to this plan's Task 6/8, 3d2 Tasks 1a–3 and `tests/conn_rx.rs` (preflight I6, M21). Everything else in the 3e draft's 3d contract is unchanged.
- **Phase 4:** the TLS boundary is 3d2's `crypto_read`/`crypto_write`/`on_peer_params`/`on_handshake_complete`/`on_tls_alert` (the outline's `crypto_in`/`crypto_out`). `on_peer_params` requires `peer_tp_wf(tp@)`: call `theorem_peer_tp_wf` on the parsed extension. RFC 9001 A.2's ClientHello fails §7.3 against A.2's own header (`rfc9001_a2_iscid_mismatch`).
- **Phase 6:** replace `Recovery`'s bodies (byte-based NewReno, RFC 9002 loss detection through `SentPackets::on_packet_lost`, `on_space_discarded`) keeping the call sites and the `amp_blocked` parameter; signatures may grow (preflight M7); `MAX_INFLIGHT` stays as a memory cap.

## Exit criteria (Phase 3d)

- All four checks pass on the merged tree, with N = the escape count of `main` at merge (preflight M19d).
- The 43 Task 2–8 rows carry `✅ 3d: <file>`, and §12.3, §13.2.1, §13.3 and the four §8.2.1 rows carry touched notes; 3b's touched note on §5.2.2 is replaced; RFC 9114 §6.2's tail is closed.
- `python3 -I <scratch>/duvet_q.py <json> 5.1,5.1.1,5.1.2,5.2.2,5.2.3,7,7.2,7.3,7.4.1,8.1.3,8.2.3,10.1,10.2.3,10.3.2,11,13.2.3,13.2.5,13.4.1,13.4.2.1,13.4.2.2,14.2,19.15,19.16,19.17,21.11` prints nothing.
- `phase-3d` is merged into `main`; 3d2 then runs.

## Self-review (done while writing)

- **Spec coverage.** The design spec's Phase 3 list maps to: ACK generation (Task 2), idle/close/draining (Task 7), version negotiation (Task 6 `route`), stateless reset received (Tasks 4, 6) and never sent (D9), anti-amplification (Task 6, P1 in 3d2), minimum Initial size (Task 6 + 3d2), connection-ID management (Task 4), path validation (Task 8 + 3d2).
- **3c reality checked against the code at bf31b2a (merged to main as c7ef8f0):** `Streams::new` requires `local.initial_max_streams_uni >= 3`, both counts `<= MAX_LOCAL_STREAMS`, `stream_tp_ok` for both TPs; every `Streams` mutator requires `!failed()`; `on_frame` requires `frame_wf` and `is_stream_layer_frame`; `CryptoStream::on_crypto` requires `offset + |data| <= VARINT_MAX` (given by `frame_wf`); `StreamIds` peer ops already ensure `local_uni_spec()` unchanged; every `RecvCredit` method keeps `window_spec()`.
- **Type consistency.** `RecvPns` (2 → 3d2), `SentPacket`/`SentPackets`/`Recovery` (3 → 3d2), `LocalCids`/`PeerCids` (4 → 3d2), `HandshakeIds`/`local_tp_ok`/`peer_tp_wf` (5 → 3d2), `AmpBudget`/`PlainPacket`/`plain_wf`/`OutPacket`/`OutDatagram`/`PathId`/`CidUpdate`/`CidTable`/`Route` (6 → 8, 3d2, 3e), `Lifecycle`/`Phase`/`IdleTimer`/`close_frame`/`close_spaces` (7 → 3d2), `Paths`/`PathState` (8 → 3d2).
- **Arithmetic re-checked:** A.3 20 + 99 + 16 = 135; A.2 22 + 1162 + 16 = 1200; padding 1156, 1082, 1173; PTO 999_000, 1_024_000, 63_936_000; capped ACK: first range + 64 ranges from 200 step 2 → 72; closing 27/54; path deadline 100 + 3·999_000 = 2_997_100.
- **Proportion.** Bodies only where order is the requirement (NEW_CONNECTION_ID checks, padding rule, routing rules).
