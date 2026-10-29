# Phase 3d2: QUIC server `Connection` and HTTP/3 adapter — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Compose the Phase 3d machines into a verified, sans-IO server `Connection` over **plaintext** packets, with path validation built in from the start, and connect it to 2b's `H3Conn`:
- receive: datagram accounting per path, packet gating, coalescing, duplicate suppression, frame dispatch to 3c `Streams` and the 3d machines, peer address change;
- transmit: one datagram per call, PATH_RESPONSE/PATH_CHALLENGE first, every send inside its path's amplification budget and the in-flight cap, Initial datagrams padded to 1200, ACKs only in their own space;
- timers: idle, close/drain deadlines, PTO with the placeholder loss declaration, path-validation failure and fallback;
- the HTTP/3 adapter, with write deferral so backpressure never closes the connection.

**Architecture:**
- `quic::conn::Connection` (Tasks 1–3, one file, three tasks: receive, transmit, timers). Task 1 fixes every field and `wf()`; Tasks 2 and 3 add methods and `wf` is unchanged except where stated.
- `quic::h3_server::H3Server` (Task 4) wraps `Connection` and `H3Conn` and pumps events between them. Task 4 adds `h3 = { path = "../h3" }` to `crates/quic/Cargo.toml` (no cycle: `h3` doesn't depend on `quic`; no crates.io change).
- The 3e protection boundary, the Phase 4 TLS boundary and the Phase 6 recovery boundary are as in the parent plan.

**Tech Stack:** as the parent plan.

**Spec:** the parent plan `2026-10-29-phase-3d-quic-connection.md` (its Decisions, Global Constraints, 3c follow-ups table and Interfaces blocks are this plan's contract), the outline §3d, 2b's `docs/superpowers/plans/2026-10-27-phase-2b-h3-connection.md`, and the "Caller obligations" at the top of `crates/quic/src/streams.rs` and `crates/h3/src/conn.rs`.

## Decisions (recorded)

- **E1. Paths from the first line.** There is no single-path `amp`; `Connection.paths: Paths` is used everywhere, and P1 is per path. The handshake path is `paths.new(first path)`.
- **E2. Packets that carry only PATH_CHALLENGE/PATH_RESPONSE (and PADDING) are not recorded** in `SentPackets`: they carry nothing retransmittable (§13.3: PATH_* are never retransmitted; a lost challenge is covered by the validation timer), and §9.4 forbids them counting toward congestion control. Their PNs are still taken from the 1-RTT space.
- **E3. MTU probes are started on receipt, not on transmit.** `poll_transmit` has no randomness, so the second (1200-byte) challenge of §8.2.1 is started in `on_frame(PathResponse)` from that call's `rand`.
- **E4. One spin bit per connection ID in use** (§17.4 RECOMMENDED), redrawn as `rand[128] & 1 == 1` whenever the 1-RTT DCID we send with changes (handshake completion, a Retire-Prior-To switch, a fresh CID for a migrated path). Long-header packets carry `spin: false` (ignored by 3e).
- **E5. `stream_write` accepts a prefix.** `Ok(n)` writes `data[..n]` with `n = min(len, send_room())`, the FIN only if `n == len`. It never closes the connection for lack of room. `Err(())` means the stream can't take writes (reset, stopped, unknown, closed connection).
- **E6. The adapter defers, then refuses** (obligation 2). Unaccepted output bytes wait in a FIFO with an offset (no tail copies). `send_response` returns `Err(SendError::Busy)` *without calling h3* while anything is deferred, so h3 never commits a response we can't buffer, and deferred memory is at most one response plus h3's own control writes. `// ponytail: one deferred response per connection; per-stream queues if head-of-line blocking matters.`
- **E7. Abort signal = `AppEvent::Aborted(id)` on every client-bidi `StreamEvent::Reset`** (2b obligation 4). Over-reporting after a completed request is harmless.
- **E8. The PTO placeholder declares the space's in-flight records lost** (controller ruling #14 on the 2026-10-28 draft). This conflicts with RFC 9002 §6.2 "PTO expiry MUST NOT mark prior unacked packets lost", a Phase 6 row; Phase 6 replaces it with probe sending. Recorded here and in the Phase 6 binding note.
- **E9. Long-header packets from a non-handshake path are dropped** (a client can't migrate before confirmation, §9); a 5th distinct path is dropped uncounted (`MAX_PATHS`).

## Global Constraints

- **All of the parent plan's Global Constraints apply**, with `✅ 3d: <file>` bookkeeping (both plans are Phase 3d), evidence directories `<scratch>/vt-3d2-tN` and `<scratch>/vt-3d2-tN-r4`, and the base escape count N recorded in the Task 1 report (unchanged by every task).
- **Base branch:** `phase-3d2` from `main` after `phase-3d` merges.
- **Proof structure for `conn.rs`** (the rlimit-4 risk): every top-level method delegates to named private helpers with their own contracts, each with `#[verifier::spinoff_prover]` from the start:
  - receive: `fn gate_packet(&self, path, len, p: &PlainPacket, first_dcid: &[u8]) -> (ok: bool)`, `fn on_packet(&mut self, path, p: PlainPacket, now, rand) -> (r: Result<(), u64>)`, `fn on_frame(&mut self, k, path, dcid: &[u8], f: Frame, now, rand) -> (r: Result<(), u64>)`, `fn on_acked_frame(&mut self, k, f: &Frame)`, `fn on_lost_frame(&mut self, k, f: &Frame)`, `fn migrate(..)`, `fn discard(&mut self, k)`, `fn close_internal(&mut self, code)`;
  - transmit: `fn build_close(&mut self, now) -> Option<OutDatagram>`, `fn build_path_datagram(&mut self, now) -> Option<OutDatagram>`, `fn build_space_packet(&mut self, k, room: usize, can_pad: bool, now) -> Option<(OutPacket, bool /*eliciting*/, bool /*ack_only*/)>`, `fn commit_datagram(&mut self, q: PathId, d: &OutDatagram)` (the only place that calls `paths.on_sent` and pushes `out_log`).
- **Per-space state** is three named fields per kind (`recv_i`, `recv_h`, `recv_1`, …) reached through `match k`, with spec accessors `recv(k)`, `sent(k)`, `live(k)`; no arrays of non-`Copy` structs.
- **Consumed from 3d** (parent plan, exact names): `RecvPns`, `SentPacket`, `SentPackets`, `MAX_ACK_RANGES_IN`, `Recovery` (+ consts), `LocalCids`, `PeerCids`, `LOCAL_CID_LEN`, `ISSUE_CAP_ACTIVE`, `PEER_CID_CAP`, `HandshakeIds`, `local_tp_ok`, `lemma_local_tp_streams`, `peer_tp_wf`, `lemma_peer_tp_stream_ok`, `check_alpn`, `token_validates`, `AmpBudget`, `amp_ok`, `PlainPacket`, `plain_wf`, `OutPacket`, `OutDatagram`, `PathId`, `packet_len`, `datagram_len`, `out_packet_len`, `out_datagram_len`, `out_packet_wf`, `add_sample_padding`, `pad_datagram`, `MAX_DATAGRAM`, `AEAD_TAG_LEN`, `CidUpdate`, `Lifecycle`, `Phase`, `IdleTimer`, `ms_to_us`, `effective_idle_us`, `close_frame`, `close_spaces`, `Paths`, `PathState`, `MAX_PATHS`; and 3d Task 1's `Streams::send_room`, `MAX_SEND_BUFFER`, `MAX_OWN_UNI`.

## Matrix rows this plan closes (45, RFC 9000)

- **Task 1 (13):** §5.2; §11.1; §13.1; §10.3; §10.3.1; §8.2.1 (req) "Do NOT discard small datagrams carrying PATH_CHALLENGE/PATH_RESPONSE"; §9 and (req) "Peer violating disable_active_migration …", "Path validation on any peer address change …"; §9.3; §9.3.3; §9.5 and (req) "Do not reuse CID when sending to more than one destination address".
- **Task 2 (29):** §12.3; §13.2.1; §8.2.1 and (req) "Unpredictable PATH_CHALLENGE data", "Expand PATH_CHALLENGE datagrams to 1200 unless anti-amplification forbids", "Second validation with 1200-byte datagram for MTU"; §8; §8.1 and its 2 server (req) rows; §10.2.1; §10.2.2; §12.2; §13.2.6; §14.1 and its 3 server (req) rows; §17.2.3 and (req) "ACK for a 1-RTT packet MUST be in a 1-RTT packet"; §19.20; §8.2.2 and its 7 (req) rows.
- **Task 3 (3):** §9.3.2; §9.4; §13.3.
- Touched notes replaced: 3b's on §10.3 (Task 1) and §19.20 (Task 2); 3c's and 3d's on §13.3 (Task 3); 3d's on §12.3, §13.2.1 and §8.2.1 (Task 2).
- `python3 -I <scratch>/chk3d/rows1029.py <scratch>/chk3b/d3.txt` prints `3d2 T1 13`, `3d2 T2 29`, `3d2 T3 3` and `88 43 45`.

## Review Focus

1. **Amplification below 1200 while Initial CRYPTO is queued.** Nothing ack-eliciting goes in an Initial; an ACK-only Initial or an unpadded Handshake packet may still go out inside the budget; nothing ever exceeds 3× received per path. Pinned (Task 2): `amp_below_1200`.
2. **A sub-1200 datagram coalescing an Initial and a Handshake packet.** The Initial is dropped, the Handshake packet processed (address validated, Initial discarded), the bytes counted, the connection not closed. Pinned (Task 2): `coalesced_small`.
3. **NAT rebinding.** A non-probing 1-RTT packet from a new path with the same DCID moves the send path, keeps the peer CID (§9.5 MAY), challenges both paths (§9.3.3), and sends ≤ 3× the new path's bytes until it validates. Pinned: `nat_rebinding_rx` (Task 1), `nat_rebinding` (Task 2).
4. **A PATH_CHALLENGE in a tiny datagram on a new path** is answered unpadded within 3× those bytes, never discarded for size, never padded past the budget. Pinned (Task 2): `response_not_expanded_past_amp`.
5. **The peer switches to a new DCID on a new address and we hold no unused peer CID:** nothing is sent there (§9.5). Pinned (Task 2): `no_fresh_cid_no_send`.
6. **Alternate-packet ACKs with drip-fed credit** stall at `MAX_INFLIGHT` records and bounded range sets. Pinned (Task 2): `alternate_ack_range_growth`.
7. **Backpressure never closes and never makes h3 commit unbuffered output.** Pinned (Task 4): `deferred_large_response`, `busy_while_pending`, `stop_sending_drops_pending`.
8. **A peer `initial_max_streams_uni` below 3** is CONNECTION_CLOSE H3_GENERAL_PROTOCOL_ERROR, never swallowed. Pinned (Task 4): `peer_uni_too_small`.

---

### Task 1: `Connection` state and receive path (`quic::conn`)

**Files:**
- Create: `crates/quic/src/conn.rs`
- Modify: `crates/quic/src/lib.rs`, `TRUSTED.md` (extend the derived-impl row with `Connection`, `HsDone`)
- Test: `crates/quic/tests/conn_rx.rs`

**Interfaces:**
- Consumes: the parent plan's Tasks 1–8; 3c `Streams`, `StreamEvent`, `CryptoStream`, `SendStream`; 3b `is_ack_eliciting`, `frame_wf`, `frames_received`.
- Produces:
  - `pub const RAND_LEN: usize = 129;`, `pub const H3_ALPN: [u8; 2] = *b"h3";`, `pub open spec fn space_idx(k: PacketKind) -> int` (Initial 0, Handshake 1, OneRtt 2).
  - **`pub enum HsDone { No, Pending, Sent, Acked }`** (Clone/Copy).
  - **`pub struct Connection`** — fields:
    - `now: u64`, `hs_path: PathId`, `ids: HandshakeIds`, `local_tp: TransportParams` (filled), `peer_tp: Option<TransportParams>`;
    - `paths: Paths`, `lc: Lifecycle`, `idle: IdleTimer`, `recovery: Recovery`;
    - `recv_i/recv_h/recv_1: RecvPns`, `sent_i/sent_h/sent_1: SentPackets`, `live_i/live_h: bool` (1-RTT is live iff `complete`), `complete: bool`;
    - `crx_i/crx_h/crx_1: CryptoStream` (receive; `crx_1` takes post-handshake CRYPTO and is never read), `ctx_i/ctx_h: SendStream` (CRYPTO send, `SendStream::new(VARINT_MAX)`, FIN never written);
    - `streams: Option<Streams>`, `events: Vec<StreamEvent>`;
    - `local_cids: LocalCids`, `peer_cids: PeerCids`, `cid_updates: Vec<CidUpdate>`, `tokens_registered: Vec<[u8; 16]>`;
    - `hs_done: HsDone`, `probe_i/probe_h/probe_1: bool`, `spin: bool`;
    - ghost `out_log: Seq<SpecOutDatagram>`.
  - **`wf()`** (closed; Tasks 2–3 keep it):
    - every component's `wf()`; `local_tp_ok(local_tp@)` and `server_tp_wf(local_tp@)`; `peer_tp is Some(t) ==> peer_tp_wf(t@)`; `complete ==> peer_tp is Some && streams is Some || lc.phase() != Open`;
    - **P11:** `streams is Some(s) ==> s.wf() && !s.failed() && lc.phase() is Open`; `lc.phase() !is Open ==> streams is None` (dropped on close: frees the buffers, and `Streams` is never called after an `Err`);
    - **P1 (§8.1, per path):** for every path `q`, `amp_ok(paths.amp_trace(q))`, and the `Sent` entries of `paths.amp_trace(q)` are exactly `out_datagram_len(d)` for the elements `d` of `out_log` with `d.path == q`, in order (Task 1 pushes none);
    - **P4 (§12.3):** within each space, the PNs across `out_log` are strictly increasing and `< sent(k).next_pn()`.
  - **`pub fn accept(first: &PlainPacket, datagram_len: usize, path: PathId, now: u64, rand: &[u8; RAND_LEN], local_tp: &TransportParams) -> (r: Option<Connection>)`**: requires `plain_wf(first@)`. None iff `first.kind != Initial`, `datagram_len < MIN_INITIAL_DATAGRAM`, `from_first(..)` is None, or `!local_tp_ok(local_tp)`. Otherwise `L0 = rand[0..8]` is our seq-0 CID and `rand[8..24]` its token; `local_tp` is filled (`fill_local_tp`); `live_i = live_h = true`; `paths = Paths::new(path)`, `hs_path = path`; `cid_updates = [Add(odcid), Add(L0)]`; `first.token` goes through `token_validates` (false, §8.1.3). **Nothing is processed or counted**: the shell next calls `on_datagram` with the whole datagram. Ensures `r is Some(c) ==> c.wf() && c.out_log == Seq::empty()`.
  - **`pub fn on_datagram(&mut self, path: PathId, datagram_len: usize, packets: Vec<PlainPacket>, now: u64, rand: &[u8; RAND_LEN])`**: requires `old.wf()`, `forall i: plain_wf(packets@[i]@)`. Body (order is the requirement for §8.1, §12.2, §13.1, §14.1):
    ```
    now = max(self.now, now)
    match lc.phase(): Draining | Closed => return
    if paths.index(path) is None && !paths.insert(path) { return }      // MAX_PATHS: drop uncounted (§9 drop branch)
    paths.on_recv(path, len)                                            // §8.1: counted even if every packet is dropped
    if lc.phase() is Closing { lc.on_recv_closing(len); return }        // §10.2.1; packets not processed
    for p in packets (in order, moved; no copies):
      if p.dcid != packets[0].dcid { continue }                         // §12.2 SHOULD ignore
      if !gate_packet(path, len, &p, first_dcid) { continue }
      if let Err(c) = on_packet(path, p, now, rand) { close_internal(c); return }
      if lc.phase() !is Open { return }                                 // CONNECTION_CLOSE or reset → draining
    ```
    **`gate_packet`** drops (returns false) when: Initial — `len < 1200` (§14.1), `!live_i`, `path != hs_path`, `!ids.initial_scid_ok(&p.scid)` (§7.2), or `!(p.dcid == ids.odcid() || local_cids.is_active(&p.dcid))`; Handshake — `!live_h`, `path != hs_path`, `!local_cids.is_active(&p.dcid)`; OneRtt — `!complete` (RFC 9001 §5.7, the 4b note) or `!local_cids.is_active(&p.dcid)` (§5.1.1 accept until retired); any — `recv(k).is_duplicate(p.pn)` (§12.3). No size check applies to 1-RTT, so small PATH_* datagrams are never discarded (§8.2.1 req).
    **`on_packet`**: `for f in p.frames { on_frame(k, path, &p.dcid, f, now, rand)? }`; then, if still Open: `recv(k).on_packet(p.pn, is_ack_eliciting(&frames), now)` (**P10**, §13.1: only after every frame returned `Ok`); `idle.on_packet_processed(now)`; `old_used = paths.peer_used(paths.active())`, `paths.set_peer_used(path, &p.dcid)`; if `k is Handshake` and `hs_path` is not Validated: `paths.set_validated(hs_path)` and `discard(Initial)` (§8.1; RFC 9001 §4.9.1); if `k is OneRtt`, the packet is non-probing (some frame outside {PathChallenge, PathResponse, NewConnectionId, Padding}, §9.1), `path != paths.active()` and `p.pn == recv_1.largest()`: `migrate(path, &p.dcid, old_used, now, rand)`.
  - **`on_frame`** (one arm per variant):
    - Padding/Ping → Ok.
    - `Ack(a)` → `sent(k).on_ack(&a, &mut acked)?` (frame_wf gives `rfc_ack_ranges_valid`); `recovery.on_ack_received(k, acked.len(), a.delay, now)`; `on_acked_frame(k, f)` for every frame of every acked record.
    - `Crypto` → `crx(k).on_crypto(offset, &data)?` (Initial/Handshake; `frame_permitted` excludes nothing else here, and a 1-RTT CRYPTO goes to `crx_1`; `// ponytail: post-handshake CRYPTO (NewSessionTicket) is buffered and ignored; we send none.`).
    - The nine stream-layer frames → `streams.on_frame(&f, &mut events)?` (`streams` is Some: 1-RTT packets pass `gate_packet` only after completion, which requires `peer_tp`; `frame_wf` and `is_stream_layer_frame` hold).
    - `NewConnectionId{seq, retire_prior_to, cid, reset_token}` → `peer_cids.on_new_cid(.., local_tp.active_connection_id_limit)?`; if `peer_cids.current()` changed, redraw `spin` (E4).
    - `RetireConnectionId(s)` → `local_cids.on_retire(s, dcid)?`; on `Some(c)`: push `Remove(c)` and call `issue_cids(rand)` (§5.1.1 SHOULD replace).
    - `PathChallenge(d)` → `paths.on_challenge(path, d)`.
    - `PathResponse(d)` → if `let Some(q) = paths.on_response(d)`: `recovery.on_path_validated()` (§9.4); if `paths.needs_mtu_probe(q)`: `paths.start_challenge(q, next_challenge(rand), now)` (E3).
    - `ConnectionClose{..}` → `lc.enter_draining(now, pto())`; `streams = None`; Ok.
    - `HandshakeDone` cannot occur (`frames_received` excludes it).
  - **`on_acked_frame` / `on_lost_frame`** (the §13.3 routing, one arm per retransmittable frame): stream family → `streams.on_frame_acked`/`on_frame_lost` if `streams` is Some (RESET_STREAM resent unchanged inside 3c); `Crypto` → `ctx(k).on_data_acked`/`on_data_lost(offset, len, false)`; `HandshakeDone` → `Acked`, or on loss back to `Pending` unless `Acked` ("MUST be retransmitted until it is acknowledged"); `NewConnectionId` → no-op / `local_cids.on_frame_lost(seq)`; `RetireConnectionId` → `peer_cids.retire_acked`/`retire_lost`. Outdated frames are accepted (3c's credit `on_max` ignores decreases).
  - **`fn migrate(&mut self, path, dcid_seen: &[u8], old_used: Option<&[u8]>, now, rand)`** (body):
    ```
    if Some(dcid_seen) != old_used:                                   // the peer moved to a new CID of ours
        if !peer_cids.has_unused() { return }                         // §9.5: no fresh CID for a second destination
        paths.set_dcid(path, &peer_cids.use_next().unwrap()); redraw spin
    else { paths.set_dcid(path, peer_cids.current()) }                // §9.5 MAY (NAT rebinding)
    old = paths.active(); paths.set_active(path)                      // §9.3: send subsequent packets to the new address
    if paths.state(path) != Validated { paths.start_challenge(path, next_challenge(rand), now) }   // §9, §9.3
    if paths.state(old) == Validated  { paths.start_challenge(old, next_challenge(rand), now) }    // §9.3.3
    ```
    `next_challenge(rand)` takes `rand[96 + 8i .. 104 + 8i]` for the i-th challenge started in this call (i < 4).
  - **`fn discard(&mut self, k)`**: `live(k) = false`; `sent(k).drain_inflight(&mut v)` and `recovery.on_space_discarded(k)`; `crx(k) = CryptoStream::new()`, `ctx(k) = SendStream::new(VARINT_MAX)`, `recv(k) = RecvPns::new(k)` (fresh values, obligation 6); Initial also pushes `Remove(odcid)`.
  - **`fn close_internal(&mut self, code)`** = `close(code, false, &[], self.now)`.
  - **TLS boundary** (Phase 4 and these tests):
    - `pub fn crypto_read(&mut self, level: PacketKind, out: &mut Vec<u8>)` reads `crx(level)`.
    - `pub fn crypto_write(&mut self, level: PacketKind, data: &[u8])`: requires `level !is OneRtt`; ignored unless the space is live (`ctx(level).write(data, false)`).
    - **`pub fn on_peer_params(&mut self, tp: &TransportParams, now: u64)`**: requires `peer_tp_wf(tp@)`. `ids.check_peer_tp(tp)` failing → `close_internal(TRANSPORT_PARAMETER_ERROR)`; else `peer_tp = Some(tp.clone())` and `streams = Some(Streams::new(&local_tp, tp))` (preconditions from `lemma_local_tp_streams` and `lemma_peer_tp_stream_ok`).
    - **`pub fn on_handshake_complete(&mut self, alpn: &[u8], now: u64, rand: &[u8; RAND_LEN])`**: `peer_tp` None → `close_internal(INTERNAL_ERROR)`; `check_alpn` failing → `close_internal(code)`; else `complete = true`, `discard(Initial)` and `discard(Handshake)` (whichever live), `hs_done = Pending`, `spin = rand[128] & 1 == 1`, `issue_cids(rand)`. After this no long-header packet is built.
    - `pub fn on_tls_alert(&mut self, alert: u8, now: u64)` → `close_internal(CRYPTO_ERROR_BASE + alert)` (RFC 9001 §4.8).
  - **Application side:**
    - `pub fn poll_stream_events(&mut self, out: &mut Vec<StreamEvent>)` moves `events` into `out` (in order, no data copies) and leaves `events` empty.
    - **`pub fn stream_write(&mut self, id: u64, data: &[u8], fin: bool) -> (r: Result<usize, ()>)`** (E5): `Err` unless Open and `streams` is Some; `n = min(data.len(), streams.send_room())`; if `n == 0 && !(fin && data.len() == 0)` → `Ok(0)` with nothing changed; else `streams.write(id, &data[..n], fin && n == data.len())`, mapping `Err(())` to `Err(())`. Ensures `r matches Ok(n) ==> n <= data.len()` and `n < data.len() ==> n == old send_room`.
    - `pub fn stream_reset(&mut self, id, code)` and `pub fn stream_stop_sending(&mut self, id, code)`: require `code <= VARINT_MAX`; no-ops unless `streams` is Some.
    - **`pub fn close(&mut self, code: u64, app: bool, reason: &[u8], now: u64)`**: requires `code <= VARINT_MAX`; `lc.enter_closing(now, pto(), app, code, reason)`; `streams = None`.
  - **Other surface:**
    - **`pub fn on_reset_candidate(&mut self, tail: &[u8; 16], now: u64)`**: 3e calls it when a datagram's first packet won't decrypt; the shell calls it on `Route::Reset(c)`. If `peer_cids.matches_reset(tail)` → `lc.enter_draining(now, pto())`, `streams = None` (§10.3.1).
    - `pub fn poll_cid_updates(&mut self, out: &mut Vec<CidUpdate>)` drains `cid_updates`, then diffs `peer_cids.used_tokens()` against `tokens_registered` into `AddToken`/`RemoveToken`.
    - `fn issue_cids(&mut self, rand)`: only when `complete`; `local_cids.issue(&rand[24i .. 24i + 24], peer.active_connection_id_limit)` for i = 0..4 while it returns true, pushing `Add(cid)` for each.
    - `fn pto(&self) -> u64` = `recovery.pto_us(OneRtt, peer_mad_us)`, with `peer_mad_us = ms_to_us(peer_tp.map_or(25, |t| t.max_ack_delay))`.
    - Getters: `largest_pn(k) -> Option<u64>` (3e's `decode_pn` input), `phase() -> Phase`, `is_closed()`, `handshake_complete()`, `local_params() -> &TransportParams`, `peer_uni_limit() -> Option<u64>`, `now()`, `active_path() -> PathId`, `path_state(q) -> PathState`, `response_owed(q) -> bool`, `challenge_owed(q) -> bool`, `streams_live() -> bool`, `sent_inflight_len(k) -> usize`, `close_info()`. Outside `verus!`: `#[doc(hidden)] pub fn crypto_capacity(&self, k) -> usize` (sum of the CRYPTO buffers' capacities, via 3c's `buf_capacity`/`Reassembly::capacities`).

- [ ] **Step 1: Failing tests** (`tests/conn_rx.rs`). Helpers (copied into every 3d2 test file; test crates share no modules):
  - `rnd(n)`: the `[u8; 129]` with byte `j = n.wrapping_add(j)`; `S1 = 8394c8f03e515708`, `C1 = [0xc1; 8]`, `L0 = rnd(1)[0..8] = 0102030405060708`; `D(x) = [x; 8]`.
  - `A(l, d, f, r)` = `AckFrame` with `ecn: None`; `CC(app, c, r)` = `ConnectionClose{app, error_code: c, frame_type: 0, reason: r}`.
  - `ltp()` = `default_transport_params()` with `max_idle_timeout 30000`, `initial_max_data 1000`, `initial_max_stream_data_bidi_remote 100`, `_uni 100`, `initial_max_streams_bidi 10`, `_uni 3`, `active_connection_id_limit 2`, `disable_active_migration true`.
  - `ptp()` = default with `initial_source_connection_id Some(C1)`, `initial_max_data 1000`, `initial_max_stream_data_bidi_local 100`, `_uni 100`, `initial_max_streams_uni 3`, `active_connection_id_limit 4`.
  - Packets: `ini(pn, f)` = `PlainPacket{Initial, S1, C1, [], pn, f}`; `ini2` the same with dcid `L0`; `hs(pn, f)` = `{Handshake, L0, C1, [], pn, f}`; `one(pn, f)` = `{OneRtt, L0, [], [], pn, f}`; `one_on(pn, dcid, f)`.
  - `conn()` = `accept(&ini(2, [Crypto{0, [1; 100]}]), 1200, 0, 0, &rnd(1), &ltp()).unwrap()` then `on_datagram(0, 1200, vec![that packet], 0, &rnd(1))`.
  - `established_rx()` = `conn()`, `on_datagram(0, 1200, vec![hs(0, [Ping])], 10, &rnd(9))`, `on_peer_params(&ptp(), 10)`, `on_handshake_complete(b"h3", 10, &rnd(2))` (no polling; Tasks 2–3 define `established()` as this plus `poll_transmit(10)` until None).
  The tests:
  - **`accept_rules`:** None for `accept(&ini(2, ..), 1199, ..)`, `accept(&hs(0, ..), 1200, ..)`, and `ltp()` with `initial_max_streams_uni = 2` or `101`.
  - **`crypto_delivered`:** `conn()`, `crypto_read(Initial)` gives `[1; 100]`; `poll_cid_updates` gives `[Add(S1), Add(L0)]`.
  - **`small_datagram_initial_dropped`:** `conn()`, `on_datagram(0, 1199, vec![ini(3, [Ping])], 1, ..)` → `largest_pn(Initial) == Some(2)`, `phase() == Open`.
  - **`coalesced_dcid_rule`:** `conn()`, `on_datagram(0, 1200, vec![ini(3, [Ping]), hs(0, [Ping])], ..)` → `largest_pn(Handshake) == None`, `largest_pn(Initial) == Some(3)`.
  - **`handshake_validates_and_discards`:** `conn()`, `on_datagram(0, 1100, vec![ini2(3, [Ping]), hs(0, [Ping])], 1, ..)` → `largest_pn(Handshake) == Some(0)`, `largest_pn(Initial) == None` (discarded), `path_state(0) == Validated`, `phase() == Open`, `crypto_capacity(Initial) == 0`.
  - **`later_initial_other_scid`:** `PlainPacket{Initial, S1, [0xc2; 8], [], 3, [Ping]}` leaves `largest_pn(Initial) == Some(2)`, Open.
  - **`duplicate_pn`:** `conn()`, `crypto_read`, then `ini(2, [Crypto{100, [2; 10]}])` → `crypto_read(Initial)` gives `[]`.
  - **`one_rtt_before_complete`:** `conn()`, `one(0, [Ping])` → `largest_pn(OneRtt) == None`.
  - **`peer_params_checked`:** `conn()`, `on_peer_params(&ptp() with initial_source_connection_id None, 1)` → `phase() == Closing`, `close_info() == Some((false, 0x08, []))`.
  - **`stream_events`:** `established_rx()`, `on_datagram(0, 100, vec![one(0, [Stream{0, 0, b"GET", true}])], 30, ..)` → `poll_stream_events` gives `[Data{0, b"GET", true}]`; `stream_write(0, b"ok", true) == Ok(2)`.
  - **`stream_write_partial`:** `established_rx()` with `ptp()` credits `1 << 30`; a GET on stream 0 without FIN; `stream_write(0, &[7; (1 << 20) + 5], true) == Ok(1 << 20)`; `stream_write(0, &[7; 5], true) == Ok(0)`.
  - **`stream_error_closes`:** `established_rx()`, `one(0, [Stream{3, 0, b"x", false}])` → `phase() == Closing`, `close_info()` code `0x05`, `streams_live() == false`; a later `one(1, [Stream{0, 0, b"GET", true}])` leaves `poll_stream_events` empty.
  - **`ack_of_unsent`:** `conn()`, `ini(3, [Ack(A(9, 0, 0, []))])` → Closing, code `0x0a`.
  - **`connection_close_drains`:** `established_rx()`, `one(0, [CC(false, 0, [])])` → `phase() == Draining`, `streams_live() == false`.
  - **`reset_candidate`:** `established_rx()`, `one(0, [NewConnectionId{1, 1, [0xd1; 8], [0xe1; 16]}])` → `poll_cid_updates` contains `AddToken([0xe1; 16])`; `on_reset_candidate(&[0xe1; 16], 31)` → Draining. Fresh `established_rx()`: the same call leaves Open.
  - **`retire_replacement`:** `established_rx()`, `on_datagram(0, 100, vec![one(0, [RetireConnectionId(1)])], 30, &rnd(5))` → `poll_cid_updates` ends with `[Remove(rnd(2)[0..8]), Add(rnd(5)[0..8])]`.
  - **`path_challenge_recorded`:** `established_rx()`, `on_datagram(1, 50, vec![one(1, [PathChallenge(D(1))])], 30, ..)` → `response_owed(1)`, `active_path() == 0` (probing packet: no migration).
  - **`nat_rebinding_rx`:** `established_rx()`, `on_datagram(1, 100, vec![one(1, [Stream{0, 0, b"GET", true}])], 30, &rnd(5))` → `active_path() == 1`, `challenge_owed(1)`, `challenge_owed(0)` (path 0 was validated by the Handshake packet).
  - **`no_fresh_cid_no_migration`:** `established_rx()`, `one_on(1, rnd(2)[0..8], [Stream{0, 0, b"GET", true}])` on path 1 (our seq-1 CID; the peer gave us no spare CID) → `active_path() == 0`.
  - **`path_cap_rx`:** datagrams on paths 1, 2, 3 accepted; `on_datagram(4, 1200, vec![one(5, [PathChallenge(D(4))])], ..)` → `response_owed(4) == false`.
  - **`long_header_other_path_dropped`:** `conn()`, `on_datagram(1, 1200, vec![ini(3, [Ping])], ..)` → `largest_pn(Initial) == Some(2)`.
- [ ] **Step 2:** the tests fail.
- [ ] **Step 3: Implement.** Duvet-cite §5.2 ("MUST generate a connection error … or fully revert", at `close_internal` on the first `Err`); §11.1 (at `close_internal`); §13.1 (at P10); §10.3 ("MUST use a CONNECTION_CLOSE frame if it is able" at `close_internal`; "MUST discard packets that are too small" with 3b's `MIN_SHORT_PACKET` and 3e's decryption drop; replace 3b's touched note); §10.3.1 (all four MUSTs at `on_reset_candidate`/`matches_reset`; "without leaking information" with the TRUSTED.md known-gap reference); §8.2.1's "MUST NOT discard datagrams that appear to be too small" at `gate_packet`; §9 (the violation MUST, "MUST perform path validation … any change to a peer's address"; the initiate/disable MUSTs as `reason=We never initiate migration and never send from another local address.`; the client MUST `client-only`); §9.3 (both MUSTs at `migrate`); §9.3.3 (at `migrate`); §9.5 (the destination MUST at `migrate`; the local-address MUST with the never-initiate reason); RFC 9001 §5.7 at the OneRtt gate (comment citation if that row is Phase 4 and already cited, else Duvet).
- [ ] **Step 4: Mutations:** call `recv(k).on_packet` before the frame loop (fails P10's ghost check); keep `streams` Some in `close` (fails P11); `migrate` without the `has_unused` check (fails `migrate`'s §9.5 ensures: `paths.dcid(path) != paths.dcid(q)` for every other `q` whose `peer_used` differs); `gate_packet` accepts 1-RTT before `complete` (fails `on_packet`'s `streams is Some` precondition at the stream-frame arm). Test-only mutation (no proof can see it; report the failing test): skip `paths.on_recv` when every packet is dropped → Task 2's `amp_limit` fails.
- [ ] **Step 5:** Four checks, evidence, quote check; MUST coverage for `5.2,11.1,13.1,10.3,10.3.1,9,9.3,9.3.3,9.5`.
- [ ] **Step 6: Commits:** `feat(quic): verified server Connection receive path — per-path accounting, packet gating, frame dispatch, migration (RFC 9000 §5.2, §9, §10.3, §13.1)`; matrix: `✅ 3d: crates/quic/src/conn.rs` on the 13 Task 1 rows (§10.3 replacing 3b's note); `docs: mark RFC 9000 §5.2, §9.x, §10.3.x, §11.1, §13.1 closed in 3d`.

---

### Task 2: Transmit path (`Connection::poll_transmit`)

**Files:**
- Modify: `crates/quic/src/conn.rs`, and (test support outside `verus!` only) `crates/quic/src/send_stream.rs` (`#[doc(hidden)] pub fn range_counts(&self) -> (usize, usize)`), `crates/quic/src/streams.rs` (`#[doc(hidden)] pub fn send_range_counts(&self, id: u64) -> Option<(usize, usize)>`)
- Test: `crates/quic/tests/conn_tx.rs`

**Interfaces:**
- Consumes: Task 1; `Streams::poll_frames`; `SendStream::{next_off, poll_data}`; `RecvPns::{has_new, build_ack, ack_only_allowed, ack_deadline, on_ack_sent}`; `SentPackets::{take_pn, on_sent, next_pn, largest_acked, inflight_len}`; `Recovery::{can_send, on_packet_sent}`; `Paths::{budget, on_sent, take_response, take_challenge, has_response, challenge_owed, dcid, active}`; `pad_datagram`, `add_sample_padding`, `datagram_len`, `close_frame`, `close_spaces`, `pn_encode_len`.
- Produces:
  - **`pub fn poll_transmit(&mut self, now: u64) -> (r: Option<OutDatagram>)`**, requires/ensures `wf()`. Body:
    ```
    now = max(self.now, now)
    match lc.phase():
      Draining | Closed => return None                                        // §10.2.2
      Closing => return build_close(now)                                      // §10.2.1, §10.2.3
    if let Some(d) = build_path_datagram(now) { return Some(d) }              // §8.2.2: never delayed
    q = paths.active(); budget = min(MAX_DATAGRAM, paths.budget(q)); can_pad = budget >= MIN_INITIAL_DATAGRAM
    d = []
    for k in [Initial, Handshake, OneRtt] where live(k):
      if sent(k).next_pn() >= PN_MAX { lc.close_silently(); streams = None; return None }   // §12.3, nothing polled yet
      room = budget - datagram_len(d) - header_bytes(k) - pn_len - AEAD_TAG_LEN - 3; skip k on underflow
      if let Some((p, eliciting, ack_only)) = build_space_packet(k, room, can_pad, now) { d.push(p) }
    if d is empty { return None }
    if some Initial in d is ack-eliciting { pad_datagram(&mut d, MIN_INITIAL_DATAGRAM) }      // §14.1; can_pad held
    commit_datagram(q, &d); Some(OutDatagram{path: q, packets: d})
    ```
    `header_bytes(k)` = long: `7 + |client_scid| + LOCAL_CID_LEN + (Initial ? 1 : 0) + 2` (2-byte Length reserved); short: `1 + |path_dcid(q)|`. `path_dcid(q)` = `paths.dcid(q)` or, if unset, `peer_cids.current()`. `// ponytail: one datagram per call (the shell loops), one CRYPTO frame per space per packet.`
  - **`build_close`**: on `paths.active()`, one packet per `k` in `close_spaces(complete, live_i, live_h, complete)` with frames `[close_frame(app, code, reason, k)]`; `n = datagram_len`; if `n <= paths.budget(active) && lc.may_send_close(n)` → `commit_datagram`, `lc.on_close_sent(n)`, return it; else None.
  - **`build_path_datagram`** (only when `complete`; PATH frames arrive only in 1-RTT): the first path `q` (table order) with `has_response(q) || challenge_owed(q)` and a DCID (`path_dcid(q)` set; else skip q — §9.5). One OneRtt packet with frames `[PathResponse(r)?, PathChallenge(c)?]`, `pn = sent_1.take_pn()`; `add_sample_padding`; if `paths.budget(q) >= 1200` → `pad_datagram(_, 1200)`, `padded = true` (§8.2.1, §8.2.2 expand); else send unpadded only if `datagram_len <= paths.budget(q)` (§8.2.2 "MUST NOT expand … exceeds"), else return None leaving them owed. Commit: `take_response`/`take_challenge(q, padded)`, `recv_1` untouched, **not recorded** (E2), `commit_datagram(q, ..)`.
  - **`build_space_packet(k, room, can_pad, now)`**:
    ```
    pn_len = pn_encode_len(sent(k).next_pn(), sent(k).largest_acked())   (None => close_silently, return None)
    ack = if recv(k).has_new() { recv(k).build_ack(now, local_tp.ack_delay_exponent, room) } else { None }
    may_elicit = !(k is Initial && !can_pad) && recovery.can_send(total inflight records)        // §14.1, D4
    others = []
    if may_elicit:
      Initial/Handshake: if let Some(off) = ctx(k).next_off() {                                 // sizes the header only
          max_len = room' - 1 - varint_len(off) - 2; if max_len >= 1 {
            match ctx(k).poll_data(max_len, VARINT_MAX) { Some(c) => push Crypto{c.off, c.data}, None => {} } } }   // obligation 5
      OneRtt: HandshakeDone if hs_done is Pending;
              while let Some(f) = local_cids.pending_frame() and it fits room' { push; commit_pending }  // stop at first misfit
              while let Some(f) = peer_cids.pending_retire() and it fits room' { push; commit_retire }
              streams.poll_frames(room', &mut others)                                    // every polled frame is placed (P8)
      Ping if probe(k) and nothing ack-eliciting was appended
    eliciting = others has an ack-eliciting frame
    if !eliciting && !(ack is Some && recv(k).ack_only_allowed() && recv(k).ack_deadline(local_mad_us) <= now) { return None }
    pn = sent(k).take_pn(); dcid = long ? ids.client_scid() : path_dcid(paths.active())
    p = OutPacket{k, dcid, long ? local_cids seq-0 CID : [], pn, pn_len, [ack?] ++ others, 0, long ? false : spin}; add_sample_padding(&mut p)
    commit: ack => recv(k).on_ack_sent(!eliciting); hs_done Pending => Sent;
            eliciting => sent(k).on_sent(record(p)); recovery.on_packet_sent(..); idle.on_eliciting_sent(now); probe(k) = false
    ```
    `room'` is `room` minus the ACK's bytes. `record(p)` keeps only retransmittable frames (D5). `local_mad_us = ms_to_us(local_tp.max_ack_delay)`.
  - **`commit_datagram(q, d)`**: requires `out_datagram_len(d@) <= paths.budget(q)`; `paths.on_sent(q, datagram_len(d))`; ghost `out_log.push(d@)`.
  - **Proof obligations** (`wf()` plus `poll_transmit`'s ensures):
    - **P1 (§8.1, §14.1 req "limits bytes", §8 "MUST limit"):** kept by `commit_datagram` being the only `on_sent`, so 3e's written bytes (`out_packet_len`) are what is bounded, per path.
    - **P2 (§14.1):** `r is Some(d)` and some Initial in `d` is ack-eliciting ⇒ `out_datagram_len(d) == 1200`.
    - **P3 (§10.2.2, §10.2.1):** Draining/Closed ⇒ `r is None`; Closing ⇒ every frame of `r` is a ConnectionClose and the closing budget holds.
    - **P4 (§12.3, §17.2.3 new PNs):** the PNs in `r` are fresh `take_pn` results, so strictly increasing per space.
    - **P5 (§13.2.6, §17.2.3):** every `Ack` in a packet of space `k` has `ack_contains(a, pn) ==> recv(k).seen().contains(pn)`.
    - **P6 (§12.2):** every packet in `r` has the same `dcid`.
    - **P7:** every packet satisfies `out_packet_wf(p, sent(k).largest_acked())` (3e's precondition).
    - **P8 (3c ruling):** every frame `Streams::poll_frames` returned is in `r` (none polled and dropped, so no lost report is owed).
    - **P9 (§19.20):** `HandshakeDone` appears only when `complete`.
    - **P12 (§8.2.2):** every `PathResponse(x)` in a datagram for path `q` was taken from `q`'s responses (echoes a challenge received on `q`, at most once).
    - **P13 (§8.2.1, §8.2.2):** a datagram carrying PathChallenge or PathResponse has `datagram_len == 1200` unless its path's budget was below 1200.
    - **P14 (§9.5):** two datagrams with different `path` and the same 1-RTT `dcid` happen only when those paths' `peer_used` are equal (the NAT-rebinding MAY).
    - **In-flight cap:** `Σ_k sent(k).inflight_len() <= MAX_INFLIGHT` (from `can_send`).

- [ ] **Step 1: Failing tests** (`tests/conn_tx.rs`; Task 1 helpers plus `established()` = `established_rx()` then `poll_transmit(10)` until None):
  - **`harness_mirror`:** `conn()`; `poll_transmit(0) == Some(OutDatagram{0, [OutPacket{Initial, C1, L0, 0, 1, [Ack(A(2, 0, 0, []))], 0, false}]})`, `datagram_len` 47 (ACK-only, not padded); then `None`; `sent_inflight_len(Initial) == 0` (ACK-only not recorded).
  - **`amp_limit`:** `conn()`, `crypto_write(Initial, &[0xaa; 5000])`; polls until None give exactly 3 datagrams of 1200, the first Initial's frames start `Ack(A(2, 0, 0, [])), Crypto{0, ..}`; `on_datagram(0, 1200, vec![], 1, ..)` then `poll_transmit(1)` is `Some` of 1200 (bytes counted from a datagram with no processed packet).
  - **`amp_below_1200`:** `conn()`, poll (47); `crypto_write(Initial, &[0xaa; 3000])`, two polls of 1200 (budget left 1153); `crypto_write(Handshake, &[0xbb; 100])`; `poll_transmit(0) == Some` with exactly `[OutPacket{Handshake, C1, L0, 0, 1, [Crypto{0, [0xbb; 100]}], 0, false}]`, 146 bytes; then `None` with Initial CRYPTO still queued; `on_datagram(0, 1200, vec![ini(3, [Ping])], 1, ..)` → the next poll is 1200 and its Initial's first frame is `Ack(A(3, 0, 1, []))`.
  - **`coalesced_small`:** `conn()`, `on_datagram(0, 1100, vec![ini2(3, [Ping]), hs(0, [Ping])], 1, ..)`; the poll gives exactly `[OutPacket{Handshake, C1, L0, 0, 1, [Ack(A(0, 0, 0, []))], 0, false}]`; `crypto_write(Handshake, &[0xbb; 10_000])`; polls until None total > 6900 bytes (validated).
  - **`close_in_handshake_spaces`:** `conn()`, `on_peer_params(&ptp() with initial_source_connection_id None, 1)`; `poll_transmit(1)` packets `[{Initial, C1, L0, 0, 1, [CC(false, 0x08, [])], 0, false}, {Handshake, C1, L0, 0, 1, [CC(false, 0x08, [])], 0, false}]`; then `None`.
  - **`app_close_conversion`:** `conn()`, `close(0x0100, true, b"bye", 1)` → Initial and Handshake packets each `[CC(false, 0x0c, [])]`; `established()`, `close(0x0100, true, b"bye", 20)` → one OneRtt packet `[CC(true, 0x0100, b"bye")]`.
  - **`alpn_mismatch`:** `conn()`, `on_peer_params(&ptp(), 1)`, `on_handshake_complete(b"h2", 1, ..)` → `[CC(false, 0x178, [])]` in Initial and Handshake.
  - **`closing_capped`:** `established()`, `close(0x0a, false, b"", 20)`; one 30-byte OneRtt datagram `[CC(false, 0x0a, [])]`, then `None`; `on_datagram(0, 9, vec![], 21, ..)` → `None`; `on_datagram(0, 9, vec![], 22, ..)` → `Some` (same frames), then `None`.
  - **`draining_silent_tx`:** `established()`, `one(0, [CC(false, 0, [])])` → `poll_transmit(20) == None`.
  - **`stream_roundtrip`:** `established()`, `one(0, [Stream{0, 0, b"GET", true}])` at 30; `stream_write(0, b"ok", true) == Ok(2)`; `poll_transmit(30)` = one OneRtt packet with frames `[Ack(A(0, 0, 0, [])), Stream{0, 0, b"ok", true}]` and `spin == false` (`rnd(2)[128] = 130`).
  - **`handshake_done_and_cids`:** `conn()`, `on_peer_params(&ptp(), 10)`, `on_handshake_complete(b"h3", 10, &rnd(2))`; `poll_transmit(10)` = one OneRtt packet, pn 0, dcid C1, frames `[HandshakeDone, NCID{1, 0, rnd(2)[0..8], rnd(2)[8..24]}, NCID{2, 0, rnd(2)[24..32], rnd(2)[32..48]}, NCID{3, 0, rnd(2)[48..56], rnd(2)[56..72]}]`; `poll_cid_updates` = `[Add(S1), Add(L0), Remove(S1), Add(rnd(2)[0..8]), Add(rnd(2)[24..32]), Add(rnd(2)[48..56])]`.
  - **`ack_only_not_recorded`:** `established()` (1 record in flight); 100 × `on_datagram(0, 50, vec![one(n, [Ping]), ..])` each followed by polling → `sent_inflight_len(OneRtt) == 1` throughout.
  - **`path_response_echo`:** `established()`, `on_datagram(0, 100, vec![one(1, [PathChallenge(D(1))])], 30, &rnd(5))`; the next `poll_transmit(30)` is on path 0, contains `PathResponse(D(1))`, 1200 bytes; no later poll contains a `PathResponse`.
  - **`probing_does_not_migrate`:** `established()`, `on_datagram(1, 1200, vec![one(1, [PathChallenge(D(2))])], 30, ..)` → a 1200-byte datagram on path 1 with `PathResponse(D(2))`; the next stream data goes to path 0.
  - **`response_not_expanded_past_amp`:** `on_datagram(1, 50, vec![one(1, [PathChallenge(D(3))])], 30, ..)` → path 1 `[OutPacket{OneRtt, C1, [], pn, 1, [PathResponse(D(3))], 0, false}]`, `datagram_len` 35 (1 + 8 + 1 + 9 + 16) ≤ 150.
  - **`nat_rebinding`:** `established()`, `on_datagram(1, 100, vec![one(1, [Stream{0, 0, b"GET", true}])], 30, &rnd(5))`; polls until None give one path-1 datagram with `PathChallenge(rnd(5)[96..104])`, unpadded, ≤ 300 bytes in all on path 1, and one path-0 datagram with `PathChallenge(rnd(5)[104..112])` of 1200; `on_datagram(1, 1200, vec![one(2, [PathResponse(rnd(5)[96..104])])], 40, &rnd(6))` → the next poll is on path 1 with `PathChallenge(rnd(6)[96..104])` at 1200 (MTU probe), and later 1-RTT data goes to path 1 with dcid C1.
  - **`fresh_cid_for_new_dcid`:** `established()`, `one(1, [NewConnectionId{1, 0, D(0xd1), [0xe1; 16]}])` on path 0, then `one_on(2, rnd(2)[0..8], [Stream{0, 0, b"GET", true}])` on path 1 → path-1 datagrams use dcid `D(0xd1)`, path-0 ones C1.
  - **`no_fresh_cid_no_send`:** the same without the NEW_CONNECTION_ID → no datagram with `path == 1` is ever returned; `active_path()` stays 0.
  - **`path_cap`:** on path 4, `on_datagram(4, 1200, vec![one(5, [PathChallenge(D(4))])], ..)` → nothing on path 4 is ever polled.
  - **`alternate_ack_range_growth`** (D4): `established_with(ptp() with initial_max_data 1 << 30, initial_max_stream_data_bidi_local 1)`; GET on stream 0 with FIN; `stream_write(0, &[9; 10_000], true)`. For r in 0..300 at time `30 + r` (no PTO fires): poll until None; the peer acks every *other* recorded 1-RTT PN seen so far (test helper `ack_of(pns) -> AckFrame` builds descending ranges) and raises `MaxStreamData{0, r + 2}` in the same packet. Afterwards: `sent_inflight_len(OneRtt) <= 64`; `send_range_counts(0)` (through a `Connection` doc-hidden getter) has both counts `<= 65`; and no OneRtt packet after the stall carries a STREAM frame until an ACK frees a slot.
- [ ] **Step 2:** the tests fail.
- [ ] **Step 3: Implement.** Duvet-cite §8 and §8.1 (the 3× MUSTs and the count MUST at P1/`commit_datagram`; the client MUSTs `client-only`); §14.1 (the expand MUST at the `pad_datagram` call, the discard MUST at `gate_packet`, "MUST also limit" at `budget`; the client MUST `client-only`); §10.2.1 and §10.2.2 (at `build_close` and the Draining arm); §12.2 ("MUST be able to process coalesced packets", "MUST individually process each QUIC packet" at Task 1's loop, "MUST NOT coalesce … different connection IDs" at P6, the decryption MAY-sentence at `on_datagram`'s doc); §13.2.6 and §17.2.3 (the same-space MUSTs at the ACK placement; the 0-RTT-ack MUST `reason=We never accept 0-RTT.`; §17.2.3's client MUST `client-only`; "New packet numbers MUST be used" at `take_pn`'s call); §19.20 (at P9; replace 3b's note); §13.3's three retransmission MUSTs (RESET_STREAM unchanged, HANDSHAKE_DONE until acked, outdated frames) at `on_lost_frame`/`on_acked_frame` (the row closes in Task 3 with the congestion MUST); §8.2.2 (all seven MUSTs at `build_path_datagram`/P12/P13; "MUST NOT be enforced" at `Paths::on_response`'s call); §8.2.1's expand MUST repeated at `build_path_datagram`; §13.2.1's send-by-deadline MUSTs at the ACK-only rule; §12.3's 2⁶²−1 silent close at the `PN_MAX` check and "Duplicate suppression MUST happen after removing packet protection" at `gate_packet`.
- [ ] **Step 4: Mutations:** `commit_datagram` before `pad_datagram` (fails P1's sum equality); pad only when the *first* packet is Initial (fails P2 on `coalesced`-shape inputs); drop the `may_elicit` Initial condition (fails P2/`out_packet_wf` with budget < 1200); always pad path datagrams to 1200 (fails P1 at `commit_datagram`'s requires); build the ACK from `recv_h` in a 1-RTT packet (fails P5); a `while ctx(k).next_off().is_some()` loop (fails termination — `decreases` cannot be stated; report the error).
- [ ] **Step 5:** Four checks, evidence, quote check; MUST coverage for `8,8.1,8.2.1,8.2.2,10.2.1,10.2.2,12.2,12.3,13.2.1,13.2.6,14.1,17.2.3,19.20`.
- [ ] **Step 6: Commits:** `feat(quic): verified Connection transmit path — per-path amplification, Initial padding, path responses, same-space ACKs, in-flight cap (RFC 9000 §8, §10.2, §12.2, §13.2.6, §14.1)`; matrix: `✅ 3d: crates/quic/src/conn.rs` on the 29 Task 2 rows (§19.20 replacing 3b's note; §12.3, §13.2.1 and §8.2.1 replacing 3d's touched notes with `✅ 3d: conn.rs + sent.rs/ack_track.rs/path.rs`); `docs: mark RFC 9000 §8.x, §10.2.x, §12.2, §12.3, §13.2.x, §14.1, §17.2.3, §19.20 closed in 3d`.

---

### Task 3: Timers (`Connection::{next_timeout, on_timeout}`)

**Files:**
- Modify: `crates/quic/src/conn.rs`
- Test: `crates/quic/tests/conn_timers.rs`

**Interfaces:**
- Consumes: Tasks 1–2; `Lifecycle::{on_timeout, deadline, close_silently}`; `IdleTimer::deadline`; `effective_idle_us`; `RecvPns::ack_deadline`; `Recovery::{pto_deadline, on_packets_lost, on_pto_fired, on_path_validated}`; `SentPackets::{drain_inflight, last_sent_time}`; `Paths::{on_timeout, deadline, last_validated, set_active}`.
- Produces:
  - **`pub fn next_timeout(&self) -> Option<u64>`**: the minimum of the Closing/Draining deadline; and, if Open: `idle.deadline(eff)` with `eff = effective_idle_us(local.max_idle_timeout, peer.max_idle_timeout, pto())` when Some; each live space's `ack_deadline(local_mad_us)`; each live space's `recovery.pto_deadline(k, sent(k).last_sent_time(), peer_mad_us, amp_blocked)` with `amp_blocked = paths.state(hs_path) != Validated && paths.budget(hs_path) == 0`; `paths.deadline(pto())`.
  - **`pub fn on_timeout(&mut self, now: u64, rand: &[u8; RAND_LEN])`**, in order:
    1. `lc.on_timeout(now)`;
    2. Open and the idle deadline passed → `lc.close_silently()`, `streams = None` (§10.1);
    3. Open: for the first live space whose PTO deadline passed: `sent(k).drain_inflight(&mut lost)`; `recovery.on_packets_lost(k, lost.len(), now)` (§13.3 congestion action, D6); `on_lost_frame(k, f)` for every frame; `recovery.on_pto_fired()`; `probe(k) = true` (E8);
    4. Open: `if let Some(f) = paths.on_timeout(now, pto())` and `f == paths.active()`: with `Some(v) = paths.last_validated()` → `paths.set_active(v)` (§9.3.2 revert); with None → `lc.close_silently()`, `streams = None` (§9.3.2 silent close);
    5. `issue_cids(rand)`.
  - **P15 (§9.3.2):** after `on_timeout` processes a failed validation of the active path, `paths.state(paths.active()) == Validated` or `lc.phase() is Closed`.

- [ ] **Step 1: Failing tests** (`tests/conn_timers.rs`; helpers as before):
  - **`close_deadline`:** `conn()`, `on_peer_params(&ptp() with initial_source_connection_id None, 1)`, poll until None; `next_timeout() == Some(3_072_001)` (1 + 3·1_024_000); `on_timeout(3_072_001, ..)` → `is_closed()`.
  - **`draining_deadline`:** `established()`, `one(0, [CC(false, 0, [])])` at 20 → `next_timeout() == Some(3_072_020)`; `on_timeout(3_072_020, ..)` → `is_closed()`.
  - **`idle_timeout`:** `established()`, `on_timeout(30_000_010, ..)` → `is_closed()`, `poll_transmit == None`.
  - **`pto_requeue_crypto`:** `conn()`, poll; `crypto_write(Initial, &[0xaa; 100])`; `poll_transmit(0)` = Initial pn 1 `[Crypto{0, [0xaa; 100]}]`, 1200 bytes; `next_timeout() == Some(999_000)`; `on_timeout(999_000, ..)` → the poll = Initial pn 2 with the same CRYPTO frame, 1200; `next_timeout() == Some(2_997_000)`.
  - **`handshake_done_retransmitted`:** as Task 2's `handshake_done_and_cids` up to its first poll; `next_timeout() == Some(1_024_010)`; `on_timeout(1_024_010, ..)` → the poll = pn 1 with the same four frames; `on_datagram(0, 50, vec![one(0, [Ack(A(1, 0, 0, []))])], 1_024_020, ..)` → the poll is `None` and `next_timeout()` has no PTO term (it equals the idle deadline).
  - **`pto_halves_cwnd`:** `established()` with large credits, write 100_000 bytes on stream 0; poll until None gives 10 eliciting packets (cwnd 10); fire the PTO; the next polls give at most 5 packets before `None`.
  - **`validation_failure_reverts`:** Task 2's `nat_rebinding` up to the first polls, never answered; `on_timeout(30 + 3·1_024_000, ..)` → `active_path() == 0`, and the next stream write goes out on path 0.
  - **`no_validated_path_closes`:** `conn()`, `on_peer_params(&ptp(), 10)`, `on_handshake_complete(b"h3", 10, &rnd(2))` (no Handshake packet, so path 0 is unvalidated); `on_datagram(0, 100, vec![one(0, [Ping])], 20, ..)`; non-probing `one(1, [Ping])` on path 1; `on_timeout(10 + 3·1_024_000 + 1, ..)` → `is_closed()`, and no CONNECTION_CLOSE was ever polled.
  - **`validation_resets_recovery`:** `established()`, let one PTO fire (`pto_us` doubles); validate path 1 as in `nat_rebinding`; the next PTO deadline uses 1_024_000, not 2_048_000.
- [ ] **Step 2:** the tests fail.
- [ ] **Step 3: Implement.** Duvet-cite §9.3.2 (both MUSTs at step 4); §9.4 ("MUST NOT contribute to congestion control" at E2's not-recording in Task 2's builder — cite there; "MUST immediately reset" at `on_path_validated`'s call; "MUST NOT be more aggressive" at `paths.deadline(pto())`, 3·PTO); §13.3's congestion MUST at step 3; §10.1's restart at step 2 (already cited in lifecycle.rs; a second citation is fine).
- [ ] **Step 4: Mutations:** step 4 reverts to the failed path (fails P15); step 2 before step 1 with a `<` deadline compare (fails `idle_timeout`, a test mutation); `pto_deadline` ignores `amp_blocked` (fails the RFC 9002 §6.2.2.1 ensures if stated; otherwise a test mutation — say which); step 3 skips `on_packets_lost` (fails `pto_halves_cwnd`).
- [ ] **Step 5:** Four checks, evidence, quote check; MUST coverage for `9.3.2,9.4,10.1,13.3`.
- [ ] **Step 6: Commits:** `feat(quic): verified Connection timers — idle, close/drain, PTO placeholder with congestion action, path-validation fallback (RFC 9000 §9.3.2, §9.4, §10.1, §13.3)`; matrix: `✅ 3d: crates/quic/src/conn.rs + path.rs` on §9.3.2 and §9.4 (note "port-only MAY not used; RTT/CC reset is Recovery::on_path_validated (placeholder until Phase 6)"); on §13.3 replace the touched notes with `✅ 3d: crates/quic/src/conn.rs (retransmission routing) + recovery.rs (AIMD placeholder congestion action, Phase 6 replaces)`; `docs: mark RFC 9000 §9.3.2, §9.4, §13.3 closed in 3d`.

---

### Task 4: HTTP/3 adapter with write deferral (`quic::h3_server`)

**Files:**
- Create: `crates/quic/src/h3_server.rs`
- Modify: `crates/quic/Cargo.toml` (`h3 = { path = "../h3" }` under `[dependencies]`), `Cargo.lock`, `crates/quic/src/lib.rs`, `TRUSTED.md` (extend the row with `H3Server`, `AppEvent`, `SendError`)
- Test: `crates/quic/tests/h3_server.rs`

**Interfaces:**
- Consumes: Tasks 1–3; 2b's `h3::conn::{H3Conn, Output}`, `h3::message::Response`, `h3::qpack::field_section::FieldLine`, `h3::codes::{H3_GENERAL_PROTOCOL_ERROR (0x101), H3_CLOSED_CRITICAL_STREAM (0x104), H3_MISSING_SETTINGS (0x10a), H3_REQUEST_CANCELLED (0x10c)}`, `h3::limits::MIN_PEER_UNI_STREAMS`; 3c's `StreamEvent`.
- Produces:
  - **`pub enum AppEvent { H3(Output), Aborted(u64) }`** — `H3` carries only `Request`, `RequestBody`, `RequestEnd` (E7).
  - **`pub enum SendError { Busy, Rejected }`** (Clone/Copy).
  - **`pub struct H3Server { conn: Connection, h3: H3Conn, started: bool, pending: Vec<Pending> }`**, `struct Pending { id: u64, data: Vec<u8>, off: usize, fin: bool }`. `wf()`: `conn.wf()`, `h3.wf()`, every `off <= data.len()`.
  - `pub fn new(conn: Connection) -> H3Server`; `pub fn conn(&self) -> &Connection`; `pub fn conn_mut(&mut self) -> &mut Connection` (TLS boundary and `poll_transmit`; call `pump` after any mutation through it).
  - **`pub fn pump(&mut self, app: &mut Vec<AppEvent>)`** (body):
    ```
    if !started:
        if !(conn.handshake_complete() && conn.phase() is Open) { return }        // 2b obligation 2: drain gated on start
        started = true
        if conn.peer_uni_limit().unwrap() < MIN_PEER_UNI_STREAMS { conn.close(H3_GENERAL_PROTOCOL_ERROR, true, &[], conn.now()); return }   // RFC 9114 §6.2
        h3.start(&mut outs); apply(outs, app)
    flush()                                                                       // acks may have freed room
    loop: conn.poll_stream_events(&mut evs); if evs empty break
      for e in evs (in order):
        Data{id, data, fin}   -> h3.on_stream_data(id, &data, fin, &mut outs)
        Reset{id, code}       -> h3.on_stream_reset(id, code, &mut outs); if id % 4 == 0 { app.push(Aborted(id)) }   // E7
        StopSending{id, code} -> h3.on_stop_sending(id, code, &mut outs)       // every stream
        apply(outs, app)
    ```
  - **`apply(outs, app)`**, one arm per `Output`: `StreamWrite{id, data, fin}` → push `Pending{id, data, 0, fin}`, then `flush()`; `ResetStream{id, code}` → remove pending entries for `id`, `conn.stream_reset(id, code)`; `StopSending{id, code}` → `conn.stream_stop_sending`; `CloseConnection{code}` → `conn.close(code, true, &[], conn.now())`; `Request`/`RequestBody`/`RequestEnd` → `app.push(H3(o))`.
  - **`fn flush(&mut self)`**: while `pending` is non-empty: `e = &pending[0]`; `conn.stream_write(e.id, &e.data[e.off..], e.fin)`: `Ok(n)` → `e.off += n`; if the whole tail and FIN were taken, `pending.remove(0)` (the `Vec` is dropped), else stop; `Err(())` → remove every entry for `e.id` (the stream was reset or stopped; h3 already knows). `// ponytail: Vec::remove(0) on <= a few entries (one response + control writes).`
  - **`pub fn send_response(&mut self, id: u64, resp: &Response, app: &mut Vec<AppEvent>) -> (r: Result<(), SendError>)`**: `!pending.is_empty()` → `Err(Busy)` **without calling h3** (E6); else `h3.send_response(id, resp, &mut outs)`: `Err` → `Err(Rejected)`; `Ok` → `apply(outs, app)`, `Ok(())`. Ensures `r is Err(Busy) ==> self.h3 == old.h3`.
  - `pub fn can_send(&self) -> bool` = `pending.is_empty()`.
  - `pub fn on_datagram(&mut self, path, datagram_len, packets, now, rand, app)` = `conn.on_datagram(..)` then `pump` (same `requires` as `Connection::on_datagram`); `pub fn on_timeout(&mut self, now, rand, app)` = `conn.on_timeout(..)` then `pump`; `pub fn shutdown(&mut self, app)` = `h3.shutdown`, then `apply`.
  - **Proof obligations:** every `StreamEvent` drained from `conn` is passed to exactly one `h3` method, in order (2b obligation 1; so 2b's chunking theorem applies to the QUIC byte stream and 3c's E1–E5 hold for what `h3` sees); per stream, the bytes passed to `conn.stream_write` are a prefix of the concatenated `StreamWrite` data h3 emitted for it, in order, unless that stream's entries were dropped on `ResetStream`/`Err`; `send_response` returns Busy without changing `h3`.
  - Outside `verus!`: `#[doc(hidden)] pub fn pending_bytes(&self) -> usize`.

- [ ] **Step 1: Failing tests** (`tests/h3_server.rs`; Task 1–3 helpers duplicated; `est()` = `H3Server::new(established())` then `pump`):
  - **`min_uni_literal`:** `assert_eq!(h3::limits::MIN_PEER_UNI_STREAMS, 3)`, `assert_eq!(quic::stream_id::MAX_OWN_UNI, 3)`; `accept` with `ltp().initial_max_streams_uni = 2` is None.
  - **`control_stream_opened`:** after `est()`, `poll_transmit` contains `Stream{3, 0, 00 04 07 06 80 01 00 00 21 00, false}` (type byte, SETTINGS `[(0x06, 65536), (0x21, 0)]`).
  - **`drain_gated_on_started`:** `H3Server::new(conn())` (not complete) then `pump` → `app` empty and nothing on stream 3 polled.
  - **`get_end_to_end`:** `on_datagram(0, 300, vec![one(0, [Stream{2, 0, [0x00, 0x04, 0x00], false}, Stream{0, 0, HEADERS(GET https example.com /), true}])], 40, ..)` (HEADERS built with 2b's `encode_field_section` and `serialize_frame_header`) → `app == [H3(Request{0, head}), H3(RequestEnd{0, []})]`; `send_response(0, &Response{200, [(content-type, text/plain)], b"hi"}, ..) == Ok(())`; the poll contains `Stream{0, 0, bytes, true}` whose 2b parse is `:status 200`, `content-type text/plain`, then DATA `"hi"`.
  - **`stop_sending_forwarded`:** `est()`, `one(0, [StopSending{3, 0}])` → the poll contains `CC(true, 0x104, [])`; fresh `est()`, a GET on stream 0 without FIN, `one(1, [StopSending{0, 0x10c}])` → `send_response(0, ..) == Err(Rejected)`; the poll contains `ResetStream{0, 0x10c, 0}` and no `Stream{0, ..}`.
  - **`reset_forwarded`:** a GET HEADERS without FIN, then `ResetStream{0, 0x10c, n}` (n = HEADERS length) → `app == [H3(Request{0, ..}), Aborted(0)]`.
  - **`h3_conn_error_closes`:** client control stream `Stream{2, 0, [0x00, 0x07, 0x01, 0x00], false}` (GOAWAY first) → the poll contains `CC(true, 0x10a, [])`.
  - **`peer_uni_too_small`:** `established_with(ptp() with initial_max_streams_uni = 2)`, `new`, `pump` → the poll contains `CC(true, 0x101, [])` and no `Stream{3, ..}`; the same with 0.
  - **`deferred_large_response`:** `established_with(ptp() with initial_max_data 1 << 30, initial_max_stream_data_bidi_local 1 << 30)`; GET on stream 0 with FIN; `send_response(0, &Response{200, [], vec![0x5a; 3 << 20]}, ..) == Ok(())`; `can_send() == false`; then rounds of: poll until None, ack every polled 1-RTT PN in one packet (`ack_of`), `on_datagram` (which pumps); after at most 200 rounds `can_send() == true`, `pending_bytes() == 0`, and the concatenation of every polled `Stream{0, ..}` payload, ordered by offset, equals the response bytes h3 emitted (HEADERS + DATA of 3 MiB). The connection is never closed.
  - **`busy_while_pending`:** as above up to the first `send_response`; a GET on stream 4; `send_response(4, &Response{200, [], b"x"}, ..) == Err(Busy)`; after the deferral drains, the same call is `Ok(())`.
  - **`stop_sending_drops_pending`:** as `deferred_large_response` up to `can_send() == false`; `one(n, [StopSending{0, 0x10c}])` → `can_send() == true`, `pending_bytes() == 0`, phase Open.
- [ ] **Step 2:** the tests fail.
- [ ] **Step 3: Implement.** Duvet-cite RFC 9114 §6.2 "MUST allow the peer to create at least three" at the `peer_uni_limit` check (an extra citation; the row closed in 3d Task 5).
- [ ] **Step 4: Mutations:** `send_response` calls h3 before the Busy check (fails its `h3 == old.h3` ensures); `flush` re-slices by copying the tail into a new `Vec` (no proof failure — a review/test mutation: `deferred_large_response` must still pass, and the reviewer checks there is no tail copy); `pump` drains before `started` (fails the in-order/started obligation if stated in ensures; say which); `Reset` arm without `Aborted` (fails `reset_forwarded`).
- [ ] **Step 5:** Four checks (`cargo verus verify` runs for `h3` and `quic`, both fresh), evidence, quote check.
- [ ] **Step 6: Commit:** `feat(quic): verified HTTP/3 adapter over the QUIC connection with write deferral (StreamEvent → H3Conn, Output → Streams)`. No matrix rows.

---

## Binding notes for later phases

- **3e:** `protect(p: &OutPacket, keys, out)` writes exactly `out_packet_len(p@)` bytes, including `p.padding` zero bytes and `p.spin` for short headers; datagrams are the packets concatenated. On receive: `unprotect` uses `largest = conn.largest_pn(kind)` and `dcid_len = LOCAL_CID_LEN`; call `conn.on_reset_candidate(last16, now)` when the first packet fails to decrypt; always call `on_datagram` with the UDP payload length, even with no surviving packet; every `PlainPacket` passed must satisfy `plain_wf` (from `parse_payload`'s ensures). `RAND_LEN` is 129. The harness's "A.2 → one reply ≤ 3600" is `harness_mirror`'s 47-byte ACK-only Initial.
- **Phase 4:** drives `crypto_read`/`crypto_write`/`on_peer_params` (requires `peer_tp_wf`, via `theorem_peer_tp_wf`)/`on_handshake_complete(alpn)`/`on_tls_alert` and serializes `local_params()`; RFC 9001 A.2's ClientHello fails §7.3 against A.2's own header; key discard follows `discard`. The 3e shell switches from `Connection` to `H3Server` here.
- **Phase 6:** replace `Recovery`'s bodies and the PTO step (E8: today's placeholder marks the space lost on PTO, against RFC 9002 §6.2 "PTO expiry MUST NOT mark prior unacked packets lost" — a Phase 6 row); keep `can_send` as the gate in `build_space_packet` and `MAX_INFLIGHT` as a memory cap; feed RTT samples from `on_ack_received`.

## Exit criteria (Phase 3d2)

- All four checks pass on the merged tree with the base escape count N.
- The 45 rows carry `✅ 3d: <file>`; 3b's notes on §10.3 and §19.20, 3c's on §13.3 and 3d's touched notes are replaced; `python3 -I <scratch>/chk3d/rows1029.py <scratch>/chk3b/d3.txt` prints `88 43 45`.
- Every MUST in the 3d sections is cited or excepted: `python3 -I <scratch>/duvet_q.py <json> 5.1,5.1.1,5.1.2,5.2,5.2.2,5.2.3,7,7.2,7.3,7.4.1,8,8.1,8.1.3,8.2.1,8.2.2,8.2.3,9,9.3,9.3.2,9.3.3,9.4,9.5,10.1,10.2.1,10.2.2,10.2.3,10.3,10.3.1,10.3.2,11,11.1,12.2,12.3,13.1,13.2.1,13.2.3,13.2.5,13.2.6,13.3,13.4.1,13.4.2.1,13.4.2.2,14.1,14.2,17.2.3,19.15,19.16,19.17,19.20,21.11` prints nothing (144 lines at 3b: `<scratch>/chk3d/musts-open-at-3b.txt`).
- `phase-3d2` is merged into `main`.

## Self-review (done while writing)

- **Outline obligations → pinned items:** 3× until validated → P1 (per path); nothing while draining → P3; PNs strictly increasing → P4; active issued CIDs ≤ peer limit → 3d Task 4 `issue`; ack-eliciting Initial datagrams ≥ 1200 → P2; PATH_RESPONSE echo → P12.
- **3c caller obligations → here:** frames polled are sent (P8); `start()` first and drain gated (Task 4); every event in order (Task 4 obligation); abort signal (E7); every StopSending forwarded; Output mapping (`apply`); own-uni cap (3d Task 1); backpressure (E5, E6); ACK-range growth (Task 2 test, 3d D4); loop on `poll_data` (Task 2 CRYPTO rule); window pinned (3d Task 1).
- **Arithmetic re-checked:** ACK-only Initial 26 + 5 + 16 = 47; Handshake CRYPTO-100 26 + 104 + 16 = 146; closing 30 bytes vs 27/54; PTO 999_000, 1_024_000, 3·1_024_000 = 3_072_000; unpadded response 1 + 8 + 1 + 9 + 16 = 35; `rnd(2)[128] = 130` (spin false), `rnd(5)[128] = 133`.
- **Proportion.** Bodies only where order is the requirement: `on_datagram`, `migrate`, `poll_transmit`, `build_space_packet`, `on_timeout`, `pump`, `flush`.
