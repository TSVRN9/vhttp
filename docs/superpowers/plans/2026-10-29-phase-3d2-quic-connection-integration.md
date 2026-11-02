# Phase 3d2: QUIC server `Connection` and HTTP/3 adapter — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Compose the Phase 3d machines into a verified, sans-IO server `Connection` over **plaintext** packets, with path validation built in from the start, and connect it to 2b's `H3Conn`:
- receive: datagram accounting per path, packet gating, coalescing, duplicate suppression, frame dispatch to 3c `Streams` and the 3d machines, peer address change;
- transmit: one datagram per call, PATH_RESPONSE/PATH_CHALLENGE first, every send inside its path's amplification budget and the in-flight cap, Initial datagrams padded to 1200, ACKs only in their own space;
- timers: idle, close/drain deadlines, PTO with the placeholder loss declaration, path-validation failure and fallback;
- the HTTP/3 adapter, with write deferral so backpressure never closes the connection.

**Architecture:**
- `quic::conn::Connection` lives in one file across seven tasks (preflight I7 split; the 3d2 preflight split 1a and 2a again for sizing): 1a-i state, `wf`, accept, the TLS boundary and the public API surface; 1a-ii the handshake-space receive path; 1b stream, CID and path frames; 2a-i the packet-assembly helpers and a 1-RTT `poll_transmit`; 2a-ii the full `poll_transmit` and `build_close`; 2b path datagrams; 3 timers. Task 1a-i fixes every field and every `wf` sub-predicate. Later tasks add methods, or fill bodies earlier tasks declared with their contracts (strengthened only where stated), and `wf` is unchanged.
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
- **E9. Long-header packets from a non-handshake path are dropped** (a client can't migrate before confirmation, §9); an unknown path is added only when a packet on it passes `gate_packet` (1a-ii fix round 1), so spoofed garbage and replays take no slot, and its datagrams with no accepted packet are dropped uncounted, since nothing is ever sent to it; an accepted packet on a 5th distinct path is dropped uncounted (`MAX_PATHS`). Residual: racing first copies of authentic packets can still take slots (paths never evict; `path.rs` ponytail). Close before production.

## Global Constraints

- **All of the parent plan's Global Constraints apply**, with `✅ 3d: <file>` bookkeeping (both plans are Phase 3d), evidence directories `<scratch>/vt-3d2-tN` and `<scratch>/vt-3d2-tN-r4` (`tN` the task id, e.g. `t1a-i`), and the base escape count N recorded in the Task 1a-i report (unchanged by every task).
- **Manifest exception (preflight M18):** the parent's "`crates/quic/Cargo.toml` is untouched" holds for every task except Task 4. Task 4 adds `h3 = { path = "../h3" }` and the resulting `Cargo.lock` lines; the edge is acyclic, since h3 depends only on vstd, vest_lib and wire (3d2 preflight M13).
- **Base branch:** `phase-3d2` from `main` after `phase-3d` merges.
- **Proof structure for `conn.rs`** (the rlimit-4 risk; preflight I7). Every top-level method delegates to named private helpers with their own contracts, each with `#[verifier::spinoff_prover]` from the start:
  - **`wf` is split into named closed sub-predicates** (`wf_parts`, `wf_streams`, `wf_amp`, `wf_pn`, `wf_log_paths`, `wf_dcids`; Task 1a-i). Each helper's contract names the sub-predicates it re-proves and keeps the others by "fields unchanged".
  - **Receive:**
    - `fn gate_packet(&self, path, len, p: &PlainPacket) -> (ok: bool)` (1a-ii; no `first_dcid`, 3d2 preflight M7);
    - `fn on_packet(&mut self, path, p: PlainPacket, now, rand) -> (r: Result<(), u64>)` (1a-ii; 1b adds `set_peer_used` and `repair_pairs`);
    - `fn on_frame(..)`, a dispatcher only, over the per-family helpers `on_ack_frame` and `on_crypto_frame` (1a-ii) and `on_stream_frame`, `on_cid_frame` and `on_path_frame` (1b);
    - `fn after_one_rtt(..)`, `fn assign_dcid(..)`, `fn migrate(..)`, `fn repair_pairs(..)`, `fn rewrite_stale(..)` (1b);
    - `fn on_acked_frame(&mut self, k, f: &Frame)`, `fn on_lost_frame(&mut self, k, f: &Frame)` (1a-ii); `fn discard(&mut self, k)`, `fn close_internal(&mut self, code)` (1a-i).
  - **Transmit:**
    - `fn build_close(&mut self) -> Option<OutDatagram>` (2a-ii);
    - `fn build_path_datagram(&mut self, now) -> Option<OutDatagram>` (contract 2a-ii, body and strengthened ensures 2b; 3d2 preflight M11);
    - `fn build_space_packet(..)` = `collect_frames(..)` (frame sources only) then `commit_space_packet(..)` (PN, ACK and record commits) (2a-i);
    - `fn commit_datagram(&mut self, q: PathId, d: &OutDatagram)` (2a-i), the only place that calls `paths.on_sent` and pushes `out_log`.
- **Per-space state** is three named fields per kind (`recv_i`, `recv_h`, `recv_1`, …) reached through `match k`, with spec accessors `recv(k)`, `sent(k)`, `live(k)`; no arrays of non-`Copy` structs.
- **Consumed from 3d** (parent plan, exact names): `RecvPns`, `SentPacket`, `SentPackets`, `MAX_ACK_RANGES_IN`, `Recovery` (+ consts), `LocalCids`, `PeerCids`, `LOCAL_CID_LEN`, `ISSUE_CAP_ACTIVE`, `PEER_CID_CAP`, `HandshakeIds`, `local_tp_ok` (spec) / `is_local_tp_ok` (exec), `fill_local_tp` (requires `self.wf()`), `lemma_local_tp_streams`, `peer_tp_wf`, `lemma_peer_tp_stream_ok`, `check_alpn`, `token_validates`, `AmpBudget`, `amp_ok`, `PlainPacket`, `plain_wf`, `OutPacket`, `OutDatagram`, `PathId`, `packet_len`, `datagram_len`, `out_packet_len`, `out_datagram_len`, `out_packet_wf`, `add_sample_padding`, `pad_datagram`, `MAX_DATAGRAM`, `AEAD_TAG_LEN`, `CidUpdate`, `CidTable` (for 3e), `PER_CONN`, `MAX_CONNS`, `Lifecycle`, `Phase`, `IdleTimer`, `ms_to_us`, `effective_idle_us`, `close_frame`, `close_spaces`, `Paths` (with `mtu_failed`, `response_room`; 3d final review I2, M2; plus `len`/`id_at`, which Task 1b adds, 3d2 preflight I1), `PathState`, `MAX_PATHS`, `MAX_RESPONSES`; `ack_track::FULL_ACK_LEN` and `lemma_unreported_acked` (3d2 preflight I2); `PN_MAX` and `SentPackets::new_at` (3d2 preflight M9); and 3d Task 1's `Streams::send_room`, `MAX_SEND_BUFFER`, `MAX_OWN_UNI`, `MAX_SEND_RANGES` and the doc-hidden `Streams::send_range_counts` (preflight C1). `Paths::set_dcid` takes an `Option` (preflight I1/I2).

## Matrix rows this plan closes (48, RFC 9000)

Rows were redistributed by the Task 1/Task 2 split (preflight I7). The 3d final review moved three rows here from 3d (I1, M1, I2): §5.1.1 (req) "Accept issued CID until retired" (Task 1a-ii), §8.2.3 (Task 2b) and §14.2 (Task 3). The 3d2 preflight's 1a and 2a splits close no rows in Tasks 1a-i and 2a-i: every old-1a row closes in Task 1a-ii and every old-2a row in Task 2a-ii (2a-i places some of their citations).
- **Task 1a-ii (6):** §5.2; §11.1; §13.1; §10.3; §8.2.1 (req) "Do NOT discard small datagrams carrying PATH_CHALLENGE/PATH_RESPONSE"; §5.1.1 (req) "Accept issued CID until retired" (the I1 registration binding plus the `gate_packet` CID check).
- **Task 1b (8):** §10.3.1; §9 and (req) "Peer violating disable_active_migration …", "Path validation on any peer address change …"; §9.3; §9.3.3; §9.5 and (req) "Do not reuse CID when sending to more than one destination address".
- **Task 2a-ii (17):** §12.3; §13.2.1; §8; §8.1 and its 2 server (req) rows; §10.2.1; §10.2.2; §12.2; §13.2.6; §14.1 and its 3 server (req) rows; §17.2.3 and (req) "ACK for a 1-RTT packet MUST be in a 1-RTT packet"; §19.20.
- **Task 2b (13):** §8.2.1 and (req) "Unpredictable PATH_CHALLENGE data", "Expand PATH_CHALLENGE datagrams to 1200 unless anti-amplification forbids", "Second validation with 1200-byte datagram for MTU"; §8.2.2 and its 7 (req) rows; §8.2.3.
- **Task 3 (4):** §9.3.2; §9.4; §13.3; §14.2.
- Touched notes replaced: 3b's on §10.3 (Task 1a-ii) and §19.20 (Task 2a-ii); 3c's and 3d's on §13.3 (Task 3); 3d's on §12.3 and §13.2.1 (Task 2a-ii), §8.2.1 and §8.2.3 (Task 2b), §5.1.1 (req) "Accept issued CID until retired" (Task 1a-ii) and §14.2 (Task 3).
- `python3 -I <scratch>/chk3d/rows1029.py <scratch>/chk3b/d3.txt` prints `3d2 T1a 6`, `3d2 T1b 8`, `3d2 T2a 17`, `3d2 T2b 13`, `3d2 T3 4` and `88 40 48`. The script is unchanged: its `T1a` label is Task 1a-ii's rows and its `T2a` label Task 2a-ii's.

## Review Focus

1. **Amplification below 1200 while Initial CRYPTO is queued.** Nothing ack-eliciting goes in an Initial; an ACK-only Initial or an unpadded Handshake packet may still go out inside the budget; nothing ever exceeds 3× received per path. Pinned (Task 2a-ii): `amp_below_1200`.
2. **A sub-1200 datagram coalescing an Initial and a Handshake packet.** The Initial is dropped, the Handshake packet processed (address validated, Initial discarded), the bytes counted, the connection not closed. Pinned (Task 2a-ii): `coalesced_small`.
3. **NAT rebinding.** A non-probing 1-RTT packet from a new path with the same DCID moves the send path, keeps the peer CID (§9.5 MAY), challenges both paths (§9.3.3), and sends ≤ 3× the new path's bytes until it validates. Pinned: `nat_rebinding_rx` (Task 1b), `nat_rebinding` (Task 2b).
4. **A PATH_CHALLENGE in a tiny datagram on a new path** is answered unpadded within 3× those bytes, never discarded for size, never padded past the budget. Pinned (Task 2b): `response_not_expanded_past_amp`.
5. **The peer switches to a new DCID on a new address and we hold no unused peer CID:** nothing is sent there (§9.5). Pinned (Task 2b): `no_fresh_cid_no_send`. A probe under a new DCID is answered on a fresh peer CID when we hold one, and never under the CID used on another path; after Retire Prior To, no path keeps a retired CID (preflight I1, I2). Two paths share a DCID only when their `peer_used` are equal (`wf_dcids`, 3d2 preflight C1). Pinned: `probe_new_cid_assigned`, `probe_no_spare_cid`, `stale_dcid_rewritten`, `rpt_switch_to_used_cid`, `peer_rotation_splits_pair` (Task 1b); `probe_new_cid_response`, `stale_cid_not_used` (Task 2b).
6. **Alternate-packet ACKs with drip-fed credit across PTO cycles** stall at `MAX_INFLIGHT` records, and the range sets stay within the gate bound (3d D4; preflight C1). Pinned: `range_gate_pto_cycles` (3d Task 1) and `alternate_ack_range_growth` with real PTOs (Task 3).
7. **Backpressure never closes and never makes h3 commit unbuffered output.** Pinned (Task 4): `deferred_large_response`, `busy_while_pending`, `stop_sending_drops_pending`.
8. **A peer `initial_max_streams_uni` below 3** is CONNECTION_CLOSE H3_GENERAL_PROTOCOL_ERROR, never swallowed. Pinned (Task 4): `peer_uni_too_small`.

---

### Task 1a-i: `Connection` state, `wf`, accept, TLS boundary and the public API surface (`quic::conn`) (preflight: Task 1 split, I7; 3d2 preflight sizing)

**Files:**
- Create: `crates/quic/src/conn.rs`
- Modify:
  - `crates/quic/src/lib.rs`;
  - `TRUSTED.md` (extend the derived-impl row with `Connection`, `HsDone`);
  - `crates/quic/src/crypto_stream.rs` (outside `verus!`: `#[doc(hidden)] pub fn capacities(&self) -> (usize, usize)` over the private `re`, for `crypto_capacity`; 3d2 preflight M2).
- Test: `crates/quic/tests/conn_rx.rs`

**Interfaces:**
- Consumes: the parent plan's Tasks 1–8; 3c `Streams`, `StreamEvent`, `CryptoStream`, `SendStream`; 3b `frame_wf`.
- Produces:
  - `pub const RAND_LEN: usize = 129;`, `pub const H3_ALPN: [u8; 2] = *b"h3";`, `pub open spec fn space_idx(k: PacketKind) -> int` (Initial 0, Handshake 1, OneRtt 2).
  - **`pub enum HsDone { No, Pending, Sent, Acked }`** (Clone/Copy).
  - **`pub struct Connection`**. Every field is fixed here; Tasks 1a-ii–3 add no field. Fields:
    - `now: u64`, `hs_path: PathId`, `ids: HandshakeIds`, `local_tp: TransportParams` (filled), `peer_tp: Option<TransportParams>`;
    - `paths: Paths`, `lc: Lifecycle`, `idle: IdleTimer`, `recovery: Recovery`;
    - `recv_i/recv_h/recv_1: RecvPns`, `sent_i/sent_h/sent_1: SentPackets`, `live_i/live_h: bool` (1-RTT is live iff `complete`), `complete: bool`;
    - `crx_i/crx_h/crx_1: CryptoStream` (receive; `crx_1` takes post-handshake CRYPTO and is never read), `ctx_i/ctx_h: SendStream` (CRYPTO send, `SendStream::new(VARINT_MAX)`, FIN never written);
    - `streams: Option<Streams>`, `events: Vec<StreamEvent>`;
    - `local_cids: LocalCids`, `peer_cids: PeerCids`, `cid_updates: Vec<CidUpdate>`, `tokens_registered: Vec<[u8; 16]>`;
    - `hs_done: HsDone`, `probe_i/probe_h/probe_1: bool`, `spin: bool`;
    - `chal_used: usize`: challenge slices of `rand` used in this call, reset to 0 by every pub fn that takes `rand` (preflight M9);
    - ghost `out_log: Seq<SpecOutDatagram>`.
  - **`wf()`** (closed) is the conjunction of named closed sub-predicates (preflight I7). It is frozen here: Tasks 1a-ii–3 keep every sub-predicate unchanged. Each helper's contract names the sub-predicates it re-proves; the rest it ensures by "those fields unchanged".
    - **`wf_parts()`:** every component's `wf()`; `local_tp_ok(local_tp@)` and `server_tp_wf(local_tp@)`; `peer_tp is Some(t) ==> peer_tp_wf(t@)`; `complete ==> peer_tp is Some && streams is Some || lc.phase() != Open`; `complete ==> !live_i && !live_h`; `chal_used <= 4`; `sent_i` + `sent_h` + `sent_1` in-flight records `<= MAX_INFLIGHT`; `paths.has(hs_path)`; `recv(k).kind_spec() == k`; `cids_only(cid_updates@)` (fix round 1 and its review).
    - **`wf_streams()` (P11):** `streams is Some(s) ==> s.wf() && !s.failed() && lc.phase() is Open`; `lc.phase() !is Open ==> streams is None` (dropped on close: frees the buffers, and `Streams` is never called after an `Err`).
    - **`wf_amp()` (P1, §8.1, per path):** for every path `q`, `amp_ok(paths.amp_trace(q))`, and the `Sent` entries of `paths.amp_trace(q)` are exactly `out_datagram_len(d)` for the elements `d` of `out_log` with `d.path == q`, in order. Tasks 1a-i and 1a-ii push none.
    - **`wf_pn()` (P4, §12.3):** within each space, the PNs across `out_log` are strictly increasing and `< sent(k).next_pn()`.
    - **`wf_log_paths()`:** every `d` in `out_log` has `paths.index(d.path) is Some`. This is what lets `Paths::insert` add an id whose filtered log is empty.
    - **`wf_dcids()` (preflight I1, I2; 3d2 preflight C1):**
      - `paths.dcid(paths.active()) is Some`. There is no `hs_path` clause: `hs_path` may lose its DCID like any other path (C1(a));
      - every `paths.dcid(q) is Some(c)` has `c` active and used in `peer_cids` (`used_cid`; §5.1.2 "MUST stop using"; fix round 1: `lemma_unused_cid_unheld` gives "a `use_next()` CID is held by no path");
      - **§9.5 pairs:** for all `q1 != q2` in `paths` (at most `MAX_PATHS`), `paths.dcid(q1) is Some && paths.dcid(q1) == paths.dcid(q2) ==> paths.peer_used(q1) == paths.peer_used(q2)`. This is §9.5's "MUST NOT reuse a connection ID when sending to more than one destination address" plus its MAY (the peer used the same CID from a new address, NAT rebinding). Task 1b keeps it across `set_peer_used` with the `on_packet` repair step and across `on_new_cid` with the stale-DCID rewrite.
  - **`pub closed spec fn out_log(&self) -> Seq<SpecOutDatagram>`** (preflight I6: 3e Task 5's accessor).
  - **Clock rule (preflight M12):** every pub fn that takes `now` starts with `self.now = max(self.now, now)`.
  - **`pub fn accept(first: &PlainPacket, datagram_len: usize, path: PathId, now: u64, rand: &[u8; RAND_LEN], local_tp: &TransportParams) -> (r: Option<Connection>)`**: requires `plain_wf(first@)`.
    - `None` iff `first.kind != Initial`, `datagram_len < MIN_INITIAL_DATAGRAM`, `from_first(..)` is None, or `!is_local_tp_ok(&local_tp)` (exec twin of spec `local_tp_ok`).
    - Otherwise `L0 = rand[0..8]` is our seq-0 CID and `rand[8..24]` its token; `local_tp` is filled (`fill_local_tp`); `live_i = live_h = true`.
    - Paths: `paths = Paths::new(path)`, `hs_path = path`, `paths.set_dcid(path, Some(&first.scid))` (the client's SCID is peer seq 0; preflight I1).
    - `cid_updates = [Add(odcid), Add(L0)]`; `first.token` goes through `token_validates` (false, §8.1.3).
    - **Binding (3d final review I1):** every active local CID, and `odcid` while `live_i`, is registered through `cid_updates`: each `issue` pushes its `Add`, each retirement its `Remove`, `discard(Initial)` the `Remove(odcid)`. A `Remove` is always queued before the replacement `Add`, so at every prefix of `poll_cid_updates` a connection owns at most `ISSUE_CAP_ACTIVE` active CIDs plus `odcid` = `PER_CONN` table entries (`LocalCids::wf`: active ≤ 4). `CidTable::apply(Add)` (`add_cid`) then never fails for a registered connection except on a key collision, which keeps §5.1.1 "accept until retired" dischargeable.
    - **Nothing is processed or counted**: the shell next calls `on_datagram` with the whole datagram. Ensures `r is Some(c) ==> c.wf() && c.out_log() == Seq::empty()`.
  - **`pub fn on_datagram(&mut self, path: PathId, datagram_len: usize, packets: Vec<PlainPacket>, now: u64, rand: &[u8; RAND_LEN])`**: declared here with its final contract: requires `old.wf()` and `forall i: plain_wf(packets@[i]@)`, ensures `wf()`. The body here is the clock rule and `chal_used = 0` only. Task 1a-ii writes the body.
  - **`fn discard(&mut self, k)`**: `live(k) = false`; `sent(k).drain_inflight(&mut v)` and `recovery.on_space_discarded(k)`. `sent(k)` is drained, not replaced: a fresh `SentPackets` would reset `next_pn` and break `wf_pn` (preflight M17). `crx(k) = CryptoStream::new()`, `ctx(k) = SendStream::new(VARINT_MAX)`, `recv(k) = RecvPns::new(k)` (fresh values, obligation 6). Initial also pushes `Remove(odcid)`.
  - **`fn close_internal(&mut self, code)`** = `close(code, false, &[], self.now)`.
  - **`pub fn close(&mut self, code: u64, app: bool, reason: &[u8], now: u64)`**: requires `code <= VARINT_MAX`; `lc.enter_closing(now, pto(), app, code, reason)`; `streams = None`.
  - **TLS boundary** (Phase 4 and these tests). The first three are no-ops unless `lc.phase() is Open` (preflight M13):
    - `pub fn crypto_read(&mut self, level: PacketKind, out: &mut Vec<u8>)` reads `crx(level)`.
    - `pub fn crypto_write(&mut self, level: PacketKind, data: &[u8])`: requires `level !is OneRtt`; ignored unless the space is live (`ctx(level).write(data, false)`).
    - **`pub fn on_peer_params(&mut self, tp: &TransportParams, now: u64)`**: requires `peer_tp_wf(tp@)`. A no-op unless Open and `peer_tp is None` (preflight M13). `ids.check_peer_tp(tp)` failing → `close_internal(TRANSPORT_PARAMETER_ERROR)`. Else `peer_tp = Some(tp.clone())` and `streams = Some(Streams::new(&local_tp, tp))` (preconditions from `lemma_local_tp_streams` and `lemma_peer_tp_stream_ok`).
    - **`pub fn on_handshake_complete(&mut self, alpn: &[u8], now: u64, rand: &[u8; RAND_LEN])`**: a no-op unless Open and `!complete` (preflight M13). `peer_tp` or `streams` None → `close_internal(INTERNAL_ERROR)`. `check_alpn` failing → `close_internal(code)`. Else: `discard(Initial)` and `discard(Handshake)` (each a no-op if already gone); `complete = true`; `hs_done = Pending`; `spin = rand[128] & 1 == 1`; `issue_cids(rand)`. After this no long-header packet is built.
    - `pub fn on_tls_alert(&mut self, alert: u8, now: u64)` → `close_internal(CRYPTO_ERROR_BASE + alert)` (RFC 9001 §4.8).
  - **`pub fn poll_stream_events(&mut self, out: &mut Vec<StreamEvent>)`** moves `events` into `out` (in order, no data copies) and leaves `events` empty.
    - **Caller obligation, stated in the module doc (preflight M24):** drain this after every `on_datagram`. `events` is bounded only by the caller draining it. `H3Server::pump` discharges this; 3e drives `Connection` before any stream exists.
  - **`pub fn poll_cid_updates(&mut self, out: &mut Vec<CidUpdate>)`** (3d2 preflight I8, which also settles residual N4): drains `cid_updates` into `out`, then diffs `peer_cids.used_tokens()` against `tokens_registered`, pushing **every `RemoveToken` before any `AddToken`**, and updates `tokens_registered`. Ensures:
    - afterwards `tokens_registered` (as a set) `== peer_cids.used_tokens()` and `tokens_registered.len() <= PEER_CID_CAP`;
    - in the pushed suffix, no `AddToken` precedes a `RemoveToken`. Otherwise a connection briefly holds more than `PEER_CID_CAP` tokens, and with every connection at the cap `AddToken` fails at `MAX_TOKENS` (816).
  - **Token binding (3d Task 6 review, restated by 3d2 preflight I8):** "`tokens_registered` ⊆ `used_tokens()` at all times" is not a `wf` conjunct: a retirement inside `on_new_cid` shrinks `used_tokens()` before any poll. The invariant holds after every `poll_cid_updates` (its ensures above). The table therefore holds only tokens of CIDs we have used and never those of retired CIDs (§10.3.1), and each connection registers ≤ `PEER_CID_CAP` tokens. With `route::MAX_TOKENS = MAX_CONNS * PEER_CID_CAP` and at most `MAX_CONNS` admitted connections, `CidTable::apply(AddToken)` from 3e never fails at capacity, **provided** 3e applies each `poll_cid_updates` output in order before routing the next datagram. `Connection` cannot name the `CidTable`, so that is a module-doc caller obligation, not a `requires` (residual N4; the 3e order binding under "Binding notes for later phases"). `route` checks reset tokens directly after the CID match, before NewInitial/VN (§10.3 "any packet"). Pinned by `cid_updates_apply_cleanly` (Task 1b: it needs NEW_CONNECTION_ID and RETIRE_CONNECTION_ID).
  - `fn issue_cids(&mut self, rand)`: only when `complete`. For i = 0..4, each slice tried once: `local_cids.issue(&rand[24i .. 24i + 24], peer.active_connection_id_limit)`, pushing `Add(cid)` when it returns true and moving to the next slice when it returns false (3d2 preflight M8: a second retirement in one call must not retry slice 0, already issued and refused). `// ponytail: a fresh 64-bit CID equal to another connection's makes CidTable::apply(Add) return false with no feedback (probability ~n²/2^64 at n ≤ MAX_CONNS·PER_CONN); a re-issue path if CIDs ever shrink.`
  - `fn pto(&self) -> u64` = `recovery.pto_us(OneRtt, peer_mad_us)`, with `peer_mad_us = ms_to_us(peer_tp.map_or(25, |t| t.max_ack_delay))`.
  - **Getters:** `largest_pn(k) -> Option<u64>` (3e's `decode_pn` input), `phase() -> Phase`, `is_closed()`, `handshake_complete()`, `local_params() -> &TransportParams`, `peer_uni_limit() -> Option<u64>`, `now()`, `active_path() -> PathId`, `streams_live() -> bool`, `sent_inflight_len(k) -> usize`, `close_info()`. The per-path getters go through `paths.index(q)` and need no `has(q)` (3d2 preflight I7, the 3d T8 `has(id)` binding; the tests query absent path 4):
    - `path_state(q) -> Option<PathState>` (None when `q` is absent);
    - `path_dcid(q) -> Option<Vec<u8>>` (preflight I1; None when absent);
    - `response_owed(q) -> bool`, `challenge_owed(q) -> bool` (false when absent).
  - **Outside `verus!`:** `#[doc(hidden)] pub fn crypto_capacity(&self, k) -> usize`, the sum of the CRYPTO buffers' capacities via `CryptoStream::capacities` (added here, M2) and 3c's `buf_capacity`, summed with `saturating_add` (preflight M19b: Phase 8a turns overflow checks off in quic's release profile).

- [ ] **Step 1: Failing tests** (`tests/conn_rx.rs`). Helpers, copied into every 3d2 test file (test crates share no modules):
  - **Basics:** `rnd(n)` is the `[u8; 129]` with byte `j = n.wrapping_add(j)`; `S1 = 8394c8f03e515708`, `C1 = [0xc1; 8]`, `L0 = rnd(1)[0..8] = 0102030405060708`, `D(x) = [x; 8]`.
  - **Frames:** `A(l, d, f, r)` is an `AckFrame` with `ecn: None`; `CC(app, c, r)` = `ConnectionClose{app, error_code: c, frame_type: 0, reason: r}`.
  - **`ltp()`:** `default_transport_params()` with `max_idle_timeout 30000`, `initial_max_data 1000`, `initial_max_stream_data_bidi_remote 100`, `_uni 100`, `initial_max_streams_bidi 10`, `_uni 3`, `active_connection_id_limit 2`, `disable_active_migration true`.
  - **`ptp()`:** default with `initial_source_connection_id Some(C1)`, `initial_max_data 1000`, `initial_max_stream_data_bidi_local 100`, `_uni 100`, `initial_max_streams_uni 3`, `active_connection_id_limit 4`.
  - **Packets:** `ini(pn, f)` = `PlainPacket{Initial, S1, C1, [], pn, f}`; `ini2` is the same with dcid `L0`; `hs(pn, f)` = `{Handshake, L0, C1, [], pn, f}`; `one(pn, f)` = `{OneRtt, L0, [], [], pn, f}`; `one_on(pn, dcid, f)`.
  - **`conn()`:** `accept(&ini(2, [Crypto{0, [1; 100]}]), 1200, 0, 0, &rnd(1), &ltp()).unwrap()`, then `on_datagram(0, 1200, vec![that packet], 0, &rnd(1))` (a no-op body until Task 1a-ii).
  - **`established_with(p: TransportParams)`** (preflight M16): `conn()`, then `on_datagram(0, 1200, vec![hs(0, [Ping])], 10, &rnd(9))`, `on_peer_params(&p, 10)`, `on_handshake_complete(b"h3", 10, &rnd(2))`. This does no polling.
  - **`established_rx()`** = `established_with(ptp())`. Task 2a-i defines `established()` = `established_rx()` followed by `poll_transmit(10)` until None, and `established_tx_with(p)` the same way (in `tests/conn_tx.rs`, which Tasks 2a-ii and 2b append to; Tasks 3 and 4 copy them). Also there, **`drain(c, now) -> Vec<OutDatagram>`**: polls until None, panicking past 1024 datagrams (2a-i review M1).

  The tests:
  - **`accept_rules`:** `None` for:
    - `accept(&ini(2, ..), 1199, ..)`;
    - `accept(&hs(0, ..), 1200, ..)`;
    - `ltp()` with `initial_max_streams_uni = 2`;
    - `ltp()` with `initial_max_streams_uni = 101`.
  - **`peer_params_checked`:** `conn()`, `on_peer_params(&ptp() with initial_source_connection_id None, 1)` → `phase() == Closing`, `close_info() == Some((false, 0x08, []))`.
  - **`tls_calls_after_close`** (preflight M13): continue `peer_params_checked`; `on_peer_params(&ptp(), 2)` and `on_handshake_complete(b"h3", 2, &rnd(2))` leave `streams_live() == false`, `handshake_complete() == false`, and `close_info()` unchanged.
- [ ] **Step 2:** the tests fail.
- [ ] **Step 3: Implement.** Duvet-cite §11.1 and §10.3's "MUST use a CONNECTION_CLOSE frame if it is able" at `close_internal`. No row closes here: the six old-1a rows close in Task 1a-ii, which places their remaining citations.
- [ ] **Step 4: Mutations:**
  - keep `streams` Some in `close` (fails `wf_streams`);
  - `discard` assigns a fresh `SentPackets` (fails `wf_pn`);
  - `poll_cid_updates` pushes the `AddToken`s before the `RemoveToken`s (fails its I8 ensures).
- [ ] **Step 5:** Four checks, evidence, quote check. Record the base escape count N in the report.
- [ ] **Step 6: Commit:** `feat(quic): verified server Connection state, wf, accept and TLS boundary (RFC 9000 §11.1)`. No matrix commit.

---

### Task 1a-ii: the handshake-space receive path (`Connection::on_datagram`, `quic::conn`) (preflight: Task 1 split, I7; 3d2 preflight sizing)

**From the 1a-i re-review:** `on_ack_frame` re-proves the in-flight conjunct in `wf_parts`, which needs a small `unacked_of` length lemma in sent.rs (owned by this task). `poll_cid_updates` already ensures `tokens_changed` and `tokens_covered`; keep them.

**Files:**
- Modify: `crates/quic/src/conn.rs`
- Test: `crates/quic/tests/conn_rx.rs` (append)

**Interfaces:**
- Consumes:
  - Task 1a-i (fields, the frozen `wf` sub-predicates, `on_datagram`'s contract, `discard`, `close_internal`, `pto`);
  - 3b `is_ack_eliciting`, `frame_wf`, `frames_received`;
  - `RecvPns::{is_duplicate, on_packet}`, `SentPackets::on_ack`, `Recovery::on_ack_received`;
  - `Paths::{index, insert, on_recv, set_validated, response_room}`;
  - `LocalCids::{is_active, on_frame_lost}`, `PeerCids::{retire_acked, retire_lost}`, `HandshakeIds::{initial_scid_ok, odcid}`;
  - `CryptoStream::on_crypto`, `SendStream::{on_data_acked, on_data_lost}`, `Streams::{on_frame_acked, on_frame_lost}`;
  - `Lifecycle::{on_recv_closing, enter_draining}`, `IdleTimer::on_packet_processed`.
- Produces:
  - **`on_datagram` body** (order is the requirement for §8.1, §12.2, §13.1, §14.1):
    ```
    now = max(self.now, now); chal_used = 0                            // (preflight M9, M12)
    match lc.phase(): Draining | Closed => return
    known = paths.index(path) is Some                                   // fix round 1: unknown paths take no slot yet
    if known { paths.on_recv(path, len) }                               // §8.1: counted even if every packet is dropped
    if lc.phase() is Closing { if known { lc.on_recv_closing(len) }; return }   // §10.2.1; packets not processed
    for p in packets (in order, moved by value; supported, probe 2026-10-29):
      if p.dcid != packets[0].dcid { continue }                         // §12.2 SHOULD ignore
      if !gate_packet(path, len, &p) { continue }
      if !known { if !paths.insert(path) { return }; paths.on_recv(path, len); known = true }   // MAX_PATHS: drop uncounted (§9 drop branch)
      if let Err(c) = on_packet(path, p, now, rand) { close_internal(c); return }
      if lc.phase() !is Open { return }                                 // CONNECTION_CLOSE or reset → draining
    ```
  - **`fn gate_packet(&self, path, len, p: &PlainPacket) -> (ok: bool)`** (3d2 preflight M7: no `first_dcid` parameter; `on_datagram` already applies §12.2) ensures `ok == gate_spec(path, len, p)`, a biconditional (fix round 1 I2), with an absent path having room `MAX_RESPONSES`. It drops the packet (returns false) when:
    - Initial: `len < 1200` (§14.1), `!live_i`, `path != hs_path`, `!ids.initial_scid_ok(&p.scid)` (§7.2), or `!(p.dcid == ids.odcid() || local_cids.is_active(&p.dcid))`;
    - Handshake: `!live_h`, `path != hs_path`, or `!local_cids.is_active(&p.dcid)`;
    - OneRtt: `!complete` (RFC 9001 §5.7, the 4b note) or `!local_cids.is_active(&p.dcid)` (§5.1.1 accept until retired);
    - any kind: `recv(k).is_duplicate(p.pn)` (§12.3);
    - any kind: more `PathChallenge` frames in `p.frames` than `paths.response_room(path)` (3d final review M2). The whole packet is dropped and never acknowledged, so the peer sees ordinary loss (§21.9 MAY "dropping packets", cited at `MAX_RESPONSES`) and no challenge is silently lost inside an acknowledged packet. Pinned by `challenge_flood_dropped` below (3d2 preflight M10: it passes once the gate exists).
    No size check applies to 1-RTT, so small PATH_* datagrams are never discarded (§8.2.1 req).
  - **`fn on_packet(&mut self, path, p: PlainPacket, now, rand) -> (r: Result<(), u64>)`**:
    - `for f in p.frames { on_frame(k, path, &p.dcid, f, now, rand)?; if lc.phase() !is Open { break } }` (fix round 1, M3: in `[CC, Stream]`, `streams` is None by the second frame).
    - Then, if still Open: `recv(k).on_packet(p.pn, is_ack_eliciting(&frames), now)` (**P10**, §13.1: only after every frame returned `Ok`).
    - `idle.on_packet_processed(now)`. (Task 1b inserts `set_peer_used` and the C1 repair step here; nothing in this task reads `peer_used`, so `wf_dcids` is kept by "paths' DCIDs and `peer_used` unchanged" plus `insert` adding a path with DCID None.)
    - If `k is Handshake` and `hs_path` is not Validated: `paths.set_validated(hs_path)` and `discard(Initial)` (§8.1; RFC 9001 §4.9.1).
    - If `k is OneRtt`: `after_one_rtt(path, &p.dcid, non_probing, p.pn, now, rand)` (Task 1b body), where `non_probing` means some frame is outside {PathChallenge, PathResponse, NewConnectionId, Padding} (§9.1).
    - **P10 stated (preflight M14):** ensures `r is Err ==> recv(k).seen() == old.recv(k).seen()`.
  - **`fn on_frame(..)`** dispatches one arm per variant to a per-family helper (preflight I7). This task writes these:
    - Padding/Ping → Ok.
    - **`on_ack_frame(k, a)`**: `sent(k).on_ack(&a, &mut acked)?` (`frame_wf` gives `rfc_ack_ranges_valid`); `recovery.on_ack_received(k, acked.len(), a.delay, now)`; `on_acked_frame(k, f)` for every frame of every acked record, **except that adjacent STREAM frames of one stream in one record (`off + len` of one is the next's `off`) are coalesced into one `on_frame_acked` call** covering their union, FIN from the last (3d final review M3). `Streams` has only `on_frame_acked(&Frame)`, which reads `data.len()`, so the run is coalesced by appending each later frame's `data` into a copy of the run's first frame (a copy of at most the record's bytes, ≤ `MAX_DATAGRAM`; 3d2 preflight M3, which leaves `streams.rs` untouched). `// ponytail: per incoming ACK at most 64 records × distinct stream runs per record × O(R) range work (R ≈ 2·64 + ~1000, 3d D4); coalescing turns a 200-frame single-stream record into one call. Cap STREAM frames per stream per packet if a split adversary still makes this hot.`
    - **`on_crypto_frame(k, off, data)`**: `crx(k).on_crypto(offset, &data)?` for Initial/Handshake. A 1-RTT CRYPTO goes to `crx_1` (`// ponytail: post-handshake CRYPTO (NewSessionTicket) is buffered and ignored; we send none.`).
    - `ConnectionClose{..}` → `lc.enter_draining(now, pto())`; `streams = None`; Ok.
    - `HandshakeDone` cannot occur (`frames_received` excludes it).
  - **Declared here, bodied in Task 1b:** `on_stream_frame`, `on_cid_frame`, `on_path_frame` and `after_one_rtt(path, dcid, non_probing, pn, now, rand)` (no `old_used` parameter: its body never read it; 3d2 preflight M7). This task gives them their final `requires`/`ensures` over the `wf` sub-predicates only and stub bodies (`Ok(())` / no-op). Task 1b replaces the bodies and adds the behavioural ensures listed there.
  - **`on_stream_frame`'s `Err` arm (binding, fix round 1 M3):** `Streams::on_frame`'s `Err` sets `failed()`, which breaks `wf_streams`, and `close_internal` requires `wf`. So the helper snapshots `pto()` before the call, and on `Err(c)` calls `lc.enter_closing(now, pto, false, c, ..)`, sets `streams = None`, and returns `Err(c)` with `wf` intact. `on_datagram`'s later `close_internal(c)` is then a no-op: the first error wins.
  - **`fn on_acked_frame(&mut self, k, f: &Frame)` / `fn on_lost_frame(&mut self, k, f: &Frame)`** (the §13.3 routing, one arm per retransmittable frame; Task 3's PTO step also calls `on_lost_frame`):
    - stream family → `streams.on_frame_acked`/`on_frame_lost` if `streams` is Some (RESET_STREAM resent unchanged inside 3c);
    - `Crypto` → `ctx(k).on_data_acked`/`on_data_lost(offset, len, false)`;
    - `HandshakeDone` → `Acked`, or on loss back to `Pending` unless `Acked` ("MUST be retransmitted until it is acknowledged");
    - `NewConnectionId` → no-op on ack / `local_cids.on_frame_lost(seq)` on loss;
    - `RetireConnectionId` → `peer_cids.retire_acked`/`retire_lost`.
    Outdated frames are accepted (3c's credit `on_max` ignores decreases).

- [ ] **Step 1: Failing tests** (append to `tests/conn_rx.rs`):
  - **`crypto_delivered`:** `conn()`, then `crypto_read(Initial)` gives `[1; 100]`, and `poll_cid_updates` gives `[Add(S1), Add(L0)]`.
  - **`small_datagram_initial_dropped`:** `conn()`, `on_datagram(0, 1199, vec![ini(3, [Ping])], 1, ..)` → `largest_pn(Initial) == Some(2)`, `phase() == Open`.
  - **`coalesced_dcid_rule`:** `conn()`, `on_datagram(0, 1200, vec![ini(3, [Ping]), hs(0, [Ping])], ..)` → `largest_pn(Handshake) == None`, `largest_pn(Initial) == Some(3)`.
  - **`handshake_validates_and_discards`:** `conn()`, `on_datagram(0, 1100, vec![ini2(3, [Ping]), hs(0, [Ping])], 1, ..)` →
    - `largest_pn(Handshake) == Some(0)`, `largest_pn(Initial) == None` (discarded);
    - `path_state(0) == Some(Validated)` (3d2 preflight I7), `phase() == Open`;
    - `crypto_capacity(Initial) == 0`.
  - **`later_initial_other_scid`:** `PlainPacket{Initial, S1, [0xc2; 8], [], 3, [Ping]}` leaves `largest_pn(Initial) == Some(2)`, Open.
  - **`duplicate_pn`:** `conn()`, `crypto_read`, then `ini(2, [Crypto{100, [2; 10]}])` → `crypto_read(Initial)` gives `[]`.
  - **`one_rtt_before_complete`:** `conn()`, `one(0, [Ping])` → `largest_pn(OneRtt) == None`.
  - **`ack_of_unsent`:** `conn()`, `ini(3, [Ack(A(9, 0, 0, []))])` → Closing, code `0x0a`.
  - **`connection_close_drains`:** `established_rx()`, `one(0, [CC(false, 0, [])])` → `phase() == Draining`, `streams_live() == false`.
  - **`long_header_other_path_dropped`:** `conn()`, `on_datagram(1, 1200, vec![ini(3, [Ping])], ..)` → `largest_pn(Initial) == Some(2)`.
  - **`challenge_flood_dropped`** (3d final review M2; moved here from Task 1b by 3d2 preflight M10): `established_rx()`, five `PathChallenge`s in one 1-RTT packet `one(0, [PathChallenge(D(1)), .., PathChallenge(D(5))])` → `largest_pn(OneRtt)` unchanged (None), `response_owed(0) == false`.
- [ ] **Step 2:** the tests fail.
- [ ] **Step 3: Implement.** Duvet-cite:
  - §5.2 ("MUST generate a connection error … or fully revert") at `close_internal`'s call on the first `Err`;
  - §13.1 at P10;
  - §10.3's "MUST discard packets that are too small" with 3b's `MIN_SHORT_PACKET` and 3e's decryption drop; replace 3b's touched note (its CONNECTION_CLOSE MUST is cited in Task 1a-i);
  - §8.2.1's "MUST NOT discard datagrams that appear to be too small" at `gate_packet`;
  - §5.1.1 "accept until retired" at `gate_packet`'s `is_active` checks;
  - RFC 9001 §5.7 at the OneRtt gate: a comment citation if that row is Phase 4 and already cited, else Duvet.
- [ ] **Step 4: Mutations:**
  - call `recv(k).on_packet` before the frame loop (fails P10's ensures);
  - `gate_packet` accepts 1-RTT before `complete` (fails first at `gate_packet`'s `ok == gate_spec` ensures; with the gate's contract and the chain's `complete` requires also removed, at `on_stream_frame`'s `streams is Some` precondition; this holds only if `on_stream_frame`'s guard is on `Open`, from `wf`'s `complete` clause, not a runtime `streams.is_some()`, fix round 1 M3).
  Test-only mutation (reported in Task 2a-ii, whose `amp_limit` catches it): skip `paths.on_recv` on a known path when every packet is dropped.
  Review check (no test pins it; 3d2 preflight M3): the STREAM-run coalescing in `on_ack_frame` makes one `on_frame_acked` call per run.
- [ ] **Step 5:** Four checks, evidence, quote check; MUST coverage for `5.2,11.1,13.1,10.3,5.1.1`.
- [ ] **Step 6: Commits:**
  - `feat(quic): verified Connection handshake receive path — per-path accounting, packet gating (RFC 9000 §5.2, §10.3, §13.1)`;
  - matrix: `✅ 3d: crates/quic/src/conn.rs` on the 6 Task 1a-ii rows (§10.3 replacing 3b's note; §5.1.1 (req) "Accept issued CID until retired" replacing 3d's touched note, as `✅ 3d: crates/quic/src/conn.rs + cid.rs + route.rs`);
  - `docs: mark RFC 9000 §5.2, §10.3, §11.1, §13.1 closed in 3d`.

---

### Task 1b: stream, CID and path frames, migration, reset detection (`quic::conn`) (preflight: Task 1 split, I7)

**From the 1a-i re-review:** `lemma_unused_cid_unheld` requires the full `wf()`, so call it on a ghost snapshot taken before `use_next`, with the index from `use_next`'s ensures; that serves `assign_dcid` (and Task 3 step 5). It can't serve `rewrite_stale`, which runs while `wf_dcids` is deliberately broken: state a weaker private predicate there (no unused entry's CID is held by a path). `on_new_cid`'s new ensures must say a surviving seq keeps both its CID and its used flag.

> **Binding carry-over from 3d Task 4 (controller, 2026-10-29):** folded into `on_cid_frame`'s stale-DCID rewrite below, which now runs after every successful `on_new_cid` (3d2 preflight I3, C1(b)); its connection-level test is `rpt_switch_to_used_cid` (the twin of `tests/cid.rs`'s `retire_of_used_non_current`, 3d2 preflight M10).

**Files:**
- Modify:
  - `crates/quic/src/conn.rs`;
  - `crates/quic/src/cid.rs` (fix round 1 I1): `on_new_cid` also ensures a surviving seq keeps its CID (the body keeps entries; `received` is the natural carrier), so `rewrite_stale` carries "used" (`wf_dcids`) across a non-stale path;
  - `crates/quic/src/path.rs` (3d2 preflight I1): `pub fn len(&self) -> (r: usize)` with `r == self.ids().len()`, and `pub fn id_at(&self, i: usize) -> (r: PathId)` requiring `i < self.ids().len()` with `r == self.ids()[i]`. Read-only, so `Paths::wf` and every existing ensures are untouched. Tasks 2b and 3 consume them.
- Test: `crates/quic/tests/conn_rx.rs` (append)

**Interfaces:**
- Consumes:
  - Task 1a-i (fields, the frozen `wf` sub-predicates including C1's §9.5 pair conjunct); Task 1a-ii (`on_packet`, the four stubbed helpers' contracts);
  - `Paths::{set_dcid, dcid, peer_used, set_peer_used, start_challenge, on_challenge, on_response, needs_mtu_probe, set_active, state, mtu_failed}`;
  - `PeerCids::{on_new_cid, current, is_active, has_unused, use_next, matches_reset}`;
  - `LocalCids::on_retire` (3d Task 4, checks against the highest *sent* sequence number);
  - `Streams::{on_frame, write, reset, stop_sending, send_room}`;
  - `CidTable::{new, apply}` (test only).
- Produces (bodies for 1a-ii's declarations, plus new fns):
  - **`on_packet` addition (3d2 preflight C1(c)):** after `idle.on_packet_processed(now)`: `paths.set_peer_used(path, &p.dcid)`, then **`fn repair_pairs(&mut self, path)`** (`#[verifier::spinoff_prover]`): for each other path `q` (via `len`/`id_at`, at most `MAX_PATHS`) with `paths.dcid(q) is Some && paths.dcid(q) == paths.dcid(path)` and `paths.peer_used(q) != paths.peer_used(path)`, clear the non-active member's DCID: `set_dcid(q, None)` if `path == paths.active()`, else `set_dcid(path, None)`. `assign_dcid` re-assigns a cleared path later (`after_one_rtt`). Ensures `wf_dcids()`, so the §9.5 pair conjunct holds after every receive (the peer rotating CIDs on one member of a NAT-rebinding pair splits the pair).
  - **Binding from 1a-ii's review:** the stubs' `frames_kept` and `Err` code `<= VARINT_MAX` stay in their ensures. `Streams::on_frame`'s code bound needs a small induction over `rfc_recv`'s `err` (text in the 1a-ii report).
  - **`on_stream_frame`:** the nine stream-layer frames → `streams.on_frame(&f, &mut events)`, with the `Err` arm bound in Task 1a-ii. `streams` is Some: 1-RTT packets pass `gate_packet` only after completion, which requires `peer_tp`. `frame_wf` and `is_stream_layer_frame` hold.
  - **`on_cid_frame`:**
    - **`NewConnectionId{seq, retire_prior_to, cid, reset_token}`** → `peer_cids.on_new_cid(.., local_tp.active_connection_id_limit)?`, then, **after every `Ok`** (3d Task 4 binding; 3d2 preflight I3: a used non-current CID can be retired while `current()` stays put, so "`current()` changed" is not the trigger), **`fn rewrite_stale(&mut self, rand)`** (`#[verifier::spinoff_prover]`; preflight I2, 3d2 preflight C1(b)). A path is stale when `paths.dcid(q) is Some(c)` and `!peer_cids.is_active(c)`. With `a = paths.active()` and `old_a = paths.dcid(a)` (cloned):
      1. **The active path first**, if stale: `cur = peer_cids.current()`.
         - If some other path `h` holds `cur` with `peer_used(h) != peer_used(a)`: `a` gets `use_next()` if Some. If None, no send can meet §9.5, so close silently (`lc.close_silently()`, `streams = None`; Task 1b review I4), after `a` takes `cur` and every disagreeing holder is cleared so that `wf` holds: only the peer's exact-repeat NEW_CONNECTION_ID with a raised Retire Prior To reaches this, and being Closed nothing is sent. `rewrite_active` ensures that any unused entry on entry leaves every other path untouched (review I1).
         - Otherwise `a` gets `cur`.
      2. **Every other stale path `q`** (via `len`/`id_at`): if `peer_used(q) == peer_used(a)`, it gets `paths.dcid(a)` (§9.5 MAY, NAT rebinding); else `use_next()`, or None if there is no unused CID.
      3. Redraw `spin` (E4) only when `paths.dcid(a) != old_a` (3d2 preflight I3).
      `hs_path` gets no special case: after completion no long-header packet is built, and `wf_dcids` no longer requires its DCID (C1(a)). Ensures `wf_dcids()` (at most 4 `is_active` checks).
    - **`RetireConnectionId(s)`** → `local_cids.on_retire(s, dcid)?`. On `Some(c)`: push `Remove(c)` and call `issue_cids(rand)` (§5.1.1 SHOULD replace).
  - **`on_path_frame`:**
    - **`PathChallenge(d)`** → `paths.on_challenge(path, d)`. `after_one_rtt`'s `assign_dcid` follows, with this packet's `peer_used` (Task 1b review M1).
    - **After every `rewrite_stale`:** `assign_owed(rand)`: any path with no DCID that owes a response or challenge gets `assign_dcid`. A full response queue drops the peer's retransmitted probes at the gate, so nothing else recovers it (Task 1b review I3).
    - **`PathResponse(d)`** → snapshot which paths are Validated (via `len`/`id_at`, at most `MAX_PATHS`), then if `let Some(q) = paths.on_response(d)`: `recovery.on_path_validated()` (§9.4) **only if `q` was not Validated before** (3d2 preflight M5: an MTU-probe answer or the §9.3.3 old-path recheck is not a new address, and must not reset cwnd and PTO). Then, if `paths.needs_mtu_probe(q)` and `next_challenge(rand)` is `Some(c)`: `paths.start_challenge(q, c, now)` (E3; Task 3 step 6 retries it when `next_challenge` is None, 3d2 preflight M6; `migrate`'s challenges have no retry, see the 3e notes).
  - **`fn assign_dcid(&mut self, q, rand)`** (both redraw `spin` from `rand`; 1a-ii review M2) (preflight I1). Only when `paths.dcid(q) is None`:
    - if `paths.peer_used(q) == paths.peer_used(paths.active())` → `set_dcid(q, paths.dcid(active))` (§9.5 MAY, NAT rebinding);
    - else, if `peer_cids.has_unused()` → `set_dcid(q, peer_cids.use_next())` and redraw `spin` (E4);
    - else leave it None: nothing is sent to `q` (§9.5).
    `// ponytail: one spin bit per connection, so a redraw for a new path's CID also flips the active path's bit (§17.4 is RECOMMENDED); per-path spin if spin-bit observers ever matter.` (3d2 preflight M14; no test checks a redraw.)
  - **`fn next_challenge(&mut self, rand) -> Option<[u8; 8]>`** (preflight M9): `rand[96 + 8·chal_used .. 104 + 8·chal_used]` and `chal_used += 1`, or None once `chal_used == 4`. Challenge data is therefore never reused within a call. `on_response` ignores the arrival path (§8.2.2), so distinct data is what ties a response to its path (§8.2.1).
  - **`after_one_rtt(path, dcid, non_probing, pn, now, rand)`** (no `old_used`: 3d2 preflight M7):
    - if `path != paths.active()`: `assign_dcid(path, rand)`;
    - if `non_probing && path != paths.active() && pn == recv_1.largest()`: `migrate(path, now, rand)`.
  - **`fn migrate(&mut self, path, now, rand)`** (body):
    ```
    if paths.dcid(path) is None { return }                            // §9.5: no fresh CID for a second destination
    if paths.mtu_failed(path) { return }                              // §14.2: never make a failed-MTU path active (3d final review I2)
    old = paths.active(); paths.set_active(path)                      // §9.3: send subsequent packets to the new address
    if paths.state(path) == Unvalidated { if let Some(c) = next_challenge(rand) { paths.start_challenge(path, c, now) } }   // §9, §9.3: not if already underway (preflight M9)
    if paths.state(old) == Validated  { if let Some(c) = next_challenge(rand) { paths.start_challenge(old, c, now) } }      // §9.3.3
    ```
    Ensures (§9.5): `paths.dcid(path) is Some ==>` every other `q` with `paths.dcid(q) == paths.dcid(path)` has `paths.peer_used(q) == paths.peer_used(path)` (guarded like the pair conjunct, since the early return leaves `dcid(path)` None). `migrate` changes no DCID and no `peer_used`, so this follows from `wf_dcids`' pair conjunct (3d2 preflight C1(d)); P14 (Task 2b) follows from `wf` at every send.
  - **Application side:**
    - **`pub fn stream_write(&mut self, id: u64, data: &[u8], fin: bool) -> (r: Result<usize, ()>)`** (E5):
      - `Err` unless Open and `streams` is Some;
      - `n = min(data.len(), streams.send_room())`;
      - if `n == 0 && !(fin && data.len() == 0)` → `Ok(0)` with nothing changed;
      - else `streams.write(id, &data[..n], fin && n == data.len())`, mapping `Err(())` to `Err(())`.
      Ensures `r matches Ok(n) ==> n <= data.len()` and `n < data.len() ==> n == old send_room`.
    - `pub fn stream_reset(&mut self, id, code)` and `pub fn stream_stop_sending(&mut self, id, code)`: require `code <= VARINT_MAX`; no-ops unless `streams` is Some.
  - **`pub fn on_reset_candidate(&mut self, tail: &[u8; 16], now: u64)`**: 3e calls it when a datagram's first packet won't decrypt; the shell calls it on `Route::Reset(c)`. If `peer_cids.matches_reset(tail)`: `lc.enter_draining(now, pto())`, `streams = None` (§10.3.1).

- [ ] **Step 1: Failing tests** (append to `tests/conn_rx.rs`):
  - **`stream_events`:** `established_rx()`, `on_datagram(0, 100, vec![one(0, [Stream{0, 0, b"GET", true}])], 30, ..)` → `poll_stream_events` gives `[Data{0, b"GET", true}]`; `stream_write(0, b"ok", true) == Ok(2)`.
  - **`stream_write_partial`:** `established_with(ptp() with initial_max_data 1 << 30, initial_max_stream_data_bidi_local 1 << 30)`; a GET on stream 0 without FIN; `stream_write(0, &[7; (1 << 20) + 5], true) == Ok(1 << 20)`; `stream_write(0, &[7; 5], true) == Ok(0)`.
  - **`stream_error_closes`:** `established_rx()`, `one(0, [Stream{3, 0, b"x", false}])` → `phase() == Closing`, `close_info()` code `0x05`, `streams_live() == false`; a later `one(1, [Stream{0, 0, b"GET", true}])` leaves `poll_stream_events` empty.
  - **`reset_candidate`:** `established_rx()`, `one(0, [NewConnectionId{1, 1, [0xd1; 8], [0xe1; 16]}])` → `poll_cid_updates` contains `AddToken([0xe1; 16])`; `on_reset_candidate(&[0xe1; 16], 31)` → Draining. On a fresh `established_rx()`, the same call leaves it Open.
  - **`retire_replacement`** (preflight I3: seq 0, the only seq sent without polling): `established_rx()`, `on_datagram(0, 100, vec![one_on(0, rnd(2)[0..8], [RetireConnectionId(0)])], 30, &rnd(5))` → `poll_cid_updates` ends with `[Remove(L0), Add(rnd(5)[0..8])]`.
  - **`retire_unsent_seq`** (preflight I3): `established_rx()`, `one(0, [RetireConnectionId(1)])` (seq 1 issued, never sent) → Closing, code `0x0a`.
  - **`cid_updates_apply_cleanly`** (3d2 preflight I8; it also pins the 3d final review I1 `PER_CONN` argument): a real `CidTable::new()`; after each step below, apply every `poll_cid_updates` output for connection 0 in order and assert every `apply` returns `true`:
    1. `conn()` (`[Add(S1), Add(L0)]`);
    2. `on_datagram(0, 1200, vec![hs(0, [Ping])], 10, &rnd(9))`, `on_peer_params(&ptp(), 10)`, `on_handshake_complete(b"h3", 10, &rnd(2))`;
    3. `one(0, [NewConnectionId{1, 0, D(0xd1), [0xe1; 16]}])`;
    4. `one(1, [NewConnectionId{2, 1, D(0xd2), [0xe2; 16]}])` (retires C1; path 0 moves to `D(0xd1)`, so `AddToken([0xe1; 16])`);
    5. `on_datagram(0, 100, vec![one_on(2, rnd(2)[0..8], [RetireConnectionId(0)])], 30, &rnd(5))` (`Remove(L0)` before `Add(rnd(5)[0..8])`);
    6. `one_on(3, rnd(2)[0..8], [NewConnectionId{3, 2, D(0xd3), [0xe3; 16]}])` (retires `D(0xd1)`; path 0 moves to `D(0xd2)`) → this poll is exactly `[RemoveToken([0xe1; 16]), AddToken([0xe2; 16])]`, in that order.
  - **`path_challenge_recorded`:** `established_rx()`, `on_datagram(1, 50, vec![one(1, [PathChallenge(D(1))])], 30, ..)` → `response_owed(1)`; `active_path() == 0` (probing packet: no migration); `path_dcid(1) == Some(C1)` (same peer DCID as path 0: the NAT MAY).
  - **`peer_rotation_splits_pair`** (3d2 preflight C1(c)): continue `path_challenge_recorded`; `on_datagram(1, 100, vec![one_on(2, rnd(2)[0..8], [PathChallenge(D(6))])], 31, ..)` (the peer switches CIDs on path 1 only) → `path_dcid(1) == None` (pair split; no spare CID), `path_dcid(0) == Some(C1)`, `active_path() == 0`, `response_owed(1)`.
  - **`probe_new_cid_assigned`** (preflight I1): `established_rx()`, `one(0, [NewConnectionId{1, 0, D(0xd1), [0xe1; 16]}])`, then `on_datagram(1, 100, vec![one_on(1, rnd(2)[0..8], [PathChallenge(D(5))])], 30, ..)` → `path_dcid(1) == Some(D(0xd1))` and `active_path() == 0`.
  - **`rpt_switch_to_used_cid`** (3d2 preflight C1: the traced counterexample; the connection-level twin of `retire_of_used_non_current`): continue `probe_new_cid_assigned`; `on_datagram(0, 100, vec![one(2, [NewConnectionId{2, 1, D(0xd2), [0xe2; 16]}])], 31, ..)` (retires C1; `current()` moves to `D(0xd1)`, which path 1 already uses with a different `peer_used`) → `path_dcid(0) == Some(D(0xd2))`, `path_dcid(1) == Some(D(0xd1))`; the two paths never share a DCID.
  - **`probe_no_spare_cid`** (preflight I1): as `probe_new_cid_assigned` without the NEW_CONNECTION_ID → `path_dcid(1) == None` and `response_owed(1)`.
  - **`nat_rebinding_rx`:** `established_rx()`, `on_datagram(1, 100, vec![one(1, [Stream{0, 0, b"GET", true}])], 30, &rnd(5))` → `active_path() == 1`, `challenge_owed(1)`, and `challenge_owed(0)` (path 0 was validated by the Handshake packet).
  - **`stale_dcid_rewritten`** (preflight I2): continue `nat_rebinding_rx`; `on_datagram(1, 100, vec![one(2, [NewConnectionId{1, 1, D(0xd1), [0xe1; 16]}])], 31, &rnd(6))` (retires C1) → `path_dcid(1) == Some(D(0xd1))` and `path_dcid(0) == Some(D(0xd1))` (equal `peer_used`, so the pair is kept; unchanged by C1).
  - **`no_fresh_cid_no_migration`:** `established_rx()`, `one_on(1, rnd(2)[0..8], [Stream{0, 0, b"GET", true}])` on path 1 (our seq-1 CID; the peer gave us no spare CID) → `active_path() == 0`.
  - **`path_cap_rx`:** datagrams on paths 1, 2 and 3 are accepted; `on_datagram(4, 1200, vec![one(5, [PathChallenge(D(4))])], ..)` → `response_owed(4) == false` (absent path: false, 3d2 preflight I7).
- [ ] **Step 2:** the new tests fail.
- [ ] **Step 3: Implement.** Duvet-cite:
  - §10.3.1: all four MUSTs at `on_reset_candidate`/`matches_reset`; "without leaking information" with the TRUSTED.md known-gap reference;
  - §9:
    - the violation MUST and "MUST perform path validation … any change to a peer's address" at `migrate`;
    - the initiate/disable MUSTs as `reason=We never initiate migration and never send from another local address.`;
    - the client MUST as `client-only`;
  - §9.3 (both MUSTs at `migrate`);
  - §9.3.3 (at `migrate`);
  - §9.5: the destination MUST at `wf_dcids`' pair conjunct, `repair_pairs`, `rewrite_stale`, `assign_dcid` and `migrate`; the local-address MUST with the never-initiate reason.
- [ ] **Step 4: Mutations:**
  - Re-run (1a-ii review M3, M4): remove the room check from `gate_packet`: fails its `ok == gate_spec` ensures, and with `on_path_frame`'s body `challenge_flood_dropped`'s `response_owed` assertion must now bite. The 1-RTT-before-`complete` mutation fails first at that same ensures, not at `on_stream_frame`.
  - `migrate` without the `dcid(path) is None` return (fails `wf_dcids`: `set_active` would make a path with no DCID active, before the §9.5 ensures is reached; 3d2 preflight M15);
  - `assign_dcid` uses `current()` when `peer_used` differs (fails `wf_dcids`' pair conjunct);
  - `on_cid_frame` skips the stale-DCID rewrite (fails `wf_dcids`);
  - `rewrite_stale` gives the active path `current()` even when another path holds it with a different `peer_used` (fails the pair conjunct; `rpt_switch_to_used_cid` is the trace);
  - `on_packet` skips `repair_pairs` (fails the pair conjunct after `set_peer_used`);
  - `next_challenge` without the `chal_used` increment (fails `wf_parts`' `chal_used <= 4`, or the distinct-slice assertion).
- [ ] **Step 5:** Four checks, evidence, quote check; MUST coverage for `10.3.1,9,9.3,9.3.3,9.5`.
- [ ] **Step 6: Commits:**
  - `feat(quic): verified Connection frame dispatch for streams, CIDs and paths; migration and reset detection (RFC 9000 §9, §9.3, §9.5, §10.3.1)`;
  - matrix: `✅ 3d: crates/quic/src/conn.rs` on the 8 Task 1b rows;
  - `docs: mark RFC 9000 §9.x, §10.3.1 closed in 3d`.

---

### Task 2a-i: transmit helpers (`collect_frames`, `commit_space_packet`, `commit_datagram`) and a 1-RTT `poll_transmit` (preflight: Task 2 split, I7; 3d2 preflight sizing)

> **Binding carry-over from 3d Task 2 (controller, 2026-10-29):** folded into `collect_frames` and `commit_space_packet` below (3d2 preflight I2).

**Files:**
- Modify: `crates/quic/src/conn.rs`
- Test: `crates/quic/tests/conn_tx.rs`

**Interfaces:**
- Consumes:
  - Tasks 1a-i–1b; `Streams::poll_frames`; `SendStream::{next_off, poll_data}`;
  - `RecvPns::{has_new, build_ack, ack_only_allowed, ack_deadline, on_ack_sent}`, `ack_track::{FULL_ACK_LEN, lemma_unreported_acked}`;
  - `SentPackets::{take_pn, on_sent, next_pn, largest_acked, inflight_len}`, `PN_MAX` (`codes.rs`);
  - `Recovery::{can_send, on_packet_sent}`;
  - `Paths::{budget, on_sent, dcid, active}`;
  - `add_sample_padding`, `datagram_len`, `pn_encode_len`.
- Produces:
  - **`build_space_packet(k, room, can_pad, now) -> Option<(OutPacket, bool /*eliciting*/, bool /*ack_only*/)>`** = `collect_frames` then `commit_space_packet` (preflight I7: collect/commit split). Each has its own contract and `#[verifier::spinoff_prover]`. Give the room arithmetic (header reserve against `out_packet_len`) a named lemma (3d2 preflight sizing: the rlimit risk).
    - **`fn collect_frames(&mut self, k, room, can_pad, now) -> Option<(OutPacket, bool /*eliciting*/, bool /*ack_only*/)>`** mutates only the frame sources (`ctx(k)`, `streams`, `local_cids`/`peer_cids` pending queues, `hs_done`). It leaves `out_log`, `paths`, `sent(k)` and `recv(k)` unchanged, so it re-proves only `wf_parts` and `wf_streams`:
      ```
      pn_len = pn_encode_len(sent(k).next_pn(), sent(k).largest_acked())   (None => close_silently, return None)
      ack = if recv(k).has_new() && room >= FULL_ACK_LEN { recv(k).build_ack(now, local_tp.ack_delay_exponent, room) } else { None }   // 3d Task 2 binding, 3d2 preflight I2
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
      dcid = long ? ids.client_scid() : paths.dcid(paths.active()).unwrap()
      p = OutPacket{k, dcid, long ? local_cids seq-0 CID : [], sent(k).next_pn(), pn_len, [ack?] ++ others, 0, long ? false : spin}; add_sample_padding(&mut p)
      ```
    - **The ACK room rule (3d Task 2 binding, 3d2 preflight I2):** `build_ack` is called only with `room >= ack_track::FULL_ACK_LEN` (522), whose ensures then guarantees the full frame; otherwise the packet carries no ACK. `// ponytail: no ACK goes on a path with under ~560 bytes of budget until the budget grows (amplification credit or validation); a partial-ACK path if that ever stalls a handshake.` The tests are unaffected (`harness_mirror`'s room is about 1150; `nat_rebinding`'s "≤ 300 bytes on path 1" still holds).
    - **`fn commit_space_packet(&mut self, k, p: &OutPacket, eliciting, ack_only, now)`** re-proves `wf_pn` and `wf_parts`:
      ```
      pn = sent(k).take_pn()   (== p.pn; None excluded by poll_transmit's PN_MAX check)
      ack => recv(k).on_ack_sent(ack_only); hs_done Pending => Sent;
      eliciting => sent(k).on_sent(record(p)); recovery.on_packet_sent(..); idle.on_eliciting_sent(now); probe(k) = false
      ```
      **§13.2.1 proof obligation (3d Task 2 binding):** before `on_ack_sent` (which takes no frame and clears `unreported()`), assert via `lemma_unreported_acked` that the ACK in `p` covers `old.recv(k).unreported()`. §13.2.1 is marked ✅ (Task 2a-ii) only with this discharged.
    - `room'` is `room` minus the ACK's bytes. `record(p)` keeps only retransmittable frames (D5). `local_mad_us = ms_to_us(local_tp.max_ack_delay)`.
  - **`commit_datagram(q, d: &OutDatagram)`**: requires `out_datagram_len(d@) <= paths.budget(q)` and `<= MAX_DATAGRAM`; and that `d`'s PNs per space are increasing and above every logged PN (snapshot before `commit_space_packet` raises `next_pn`); `paths.on_sent(q, datagram_len(d))`; ghost `out_log.push(d@)`. Re-proves `wf_amp`, `wf_pn` and `wf_log_paths` (fix round 1 M4). The only place that calls `paths.on_sent` and pushes `out_log`.
  - **`pub fn poll_transmit(&mut self, now: u64) -> (r: Option<OutDatagram>)`**, requires/ensures `wf()`. The ensures stated here are kept by Task 2a-ii's body:
    - `final.out_log() == match r { Some(d) => old.out_log().push(d@), None => old.out_log() }` (preflight I6; 3e Task 5's input);
    - **P7 on the result:** `r is Some(d) ==>` every packet `p` of `d` satisfies `out_packet_wf(p, final.sent(p.kind).largest_acked())`;
    - **P16:** `r is Some(d) ==> out_datagram_len(d@) <= MAX_DATAGRAM`;
    - **P4 (§12.3, §17.2.3 new PNs):** the PNs in `r` are fresh `take_pn` results, so strictly increasing per space;
    - **P5 (§13.2.6, §17.2.3):** every `Ack` in a packet of space `k` has `ack_contains(a, pn) ==> recv(k).seen().contains(pn)`;
    - **P8 (3c ruling):** every frame `Streams::poll_frames` returned is in `r` (none polled and dropped, so no lost report is owed);
    - **P9 (§19.20):** `HandshakeDone` appears only when `complete`;
    - **In-flight cap:** `Σ_k sent(k).inflight_len() <= MAX_INFLIGHT` (from `can_send`).
  - **Provisional body** (1-RTT only; Task 2a-ii replaces it):
    ```
    now = max(self.now, now)
    if lc.phase() !is Open || !complete { return None }        // Task 2a-ii adds Closing, path datagrams and the long-header spaces
    if sent_1.next_pn() >= PN_MAX { lc.close_silently(); streams = None; return None }
    q = paths.active(); budget = min(MAX_DATAGRAM, paths.budget(q))
    room = budget - header_bytes(OneRtt) - pn_len - AEAD_TAG_LEN - 3; return None on underflow
    let Some((p, _, _)) = build_space_packet(OneRtt, room, budget >= MIN_INITIAL_DATAGRAM, now) else { return None }
    d = OutDatagram{path: q, packets: vec![p]}; commit_datagram(q, &d); Some(d)
    ```
    - `header_bytes(k)`: long header `7 + |client_scid| + LOCAL_CID_LEN + (Initial ? 1 : 0) + 2` (2-byte Length reserved); short header `1 + |paths.dcid(q)|`.
    - `paths.dcid(q)` is Some for the active path by `wf_dcids`. There is no `peer_cids.current()` fallback (preflight I1).

- [ ] **Step 1: Failing tests** (`tests/conn_tx.rs`; Task 1a-i helpers plus `established()` and `established_tx_with(p)`, defined here). Every test here sends only after completion, so only the 1-RTT space is live:
  - **`stream_roundtrip`:** `established()`, `one(0, [Stream{0, 0, b"GET", true}])` at 30; `stream_write(0, b"ok", true) == Ok(2)`; `poll_transmit(30)` = one OneRtt packet with frames `[Ack(A(0, 0, 0, [])), Stream{0, 0, b"ok", true}]` and `spin == false` (`rnd(2)[128] = 130`).
  - **`handshake_done_and_cids`:** `conn()`, `on_peer_params(&ptp(), 10)`, `on_handshake_complete(b"h3", 10, &rnd(2))`.
    - `poll_transmit(10)` = one OneRtt packet, pn 0, dcid C1, frames `[HandshakeDone, NCID{1, 0, rnd(2)[0..8], rnd(2)[8..24]}, NCID{2, 0, rnd(2)[24..32], rnd(2)[32..48]}, NCID{3, 0, rnd(2)[48..56], rnd(2)[56..72]}]`;
    - `poll_cid_updates` = `[Add(S1), Add(L0), Remove(S1), Add(rnd(2)[0..8]), Add(rnd(2)[24..32]), Add(rnd(2)[48..56])]`.
  - **`ack_only_not_recorded`:** `established()` (1 record in flight); 100 × `on_datagram(0, 50, vec![one(n, [Ping]), ..])`, each followed by polling → `sent_inflight_len(OneRtt) == 1` throughout.
  - **`draining_silent_tx`:** `established()`, `one(0, [CC(false, 0, [])])` → `poll_transmit(20) == None`.
  - **`acked_stream_not_resent`** (1a-ii review M1: `s.on_frame_lost` in `on_acked_frame`'s stream arm passes verification): `established()`, `stream_write`, poll, an authentic `Ack` of that packet; the next poll holds no STREAM frame.
- [ ] **Step 2:** the tests fail.
- [ ] **Step 3: Implement.** Duvet-cite (the rows close in Task 2a-ii, whose `duvet_q` run covers these sections):
  - §13.2.6 and §17.2.3: the same-space MUSTs at the ACK placement; "New packet numbers MUST be used" at `take_pn`'s call in `commit_space_packet`;
  - §19.20 at P9 (Task 2a-ii's matrix commit replaces 3b's note);
  - §13.2.1's send-by-deadline MUSTs at the ACK-only rule, and its full-ACK obligation at the `lemma_unreported_acked` assert;
  - §13.3's three retransmission MUSTs (RESET_STREAM unchanged, HANDSHAKE_DONE until acked, outdated frames) at Task 1a-ii's `on_lost_frame`/`on_acked_frame`. The row closes in Task 3 with the congestion MUST.
- [ ] **Step 4: Mutations:**
  - build the ACK from `recv_h` in a 1-RTT packet (fails P5);
  - call `build_ack` without the `room >= FULL_ACK_LEN` test (fails the `lemma_unreported_acked` assert in `commit_space_packet`; 3d2 preflight I2);
  - a `while ctx(k).next_off().is_some()` loop (fails termination: `decreases` cannot be stated; report the error).
- [ ] **Step 5:** Four checks, evidence, quote check.
- [ ] **Step 6: Commit:** `feat(quic): verified Connection packet assembly — frame collection, same-space ACKs, in-flight cap, 1-RTT transmit (RFC 9000 §13.2.1, §13.2.6, §19.20)`. No matrix commit: the 17 old-2a rows close in Task 2a-ii.

---

### Task 2a-ii: `poll_transmit` (all spaces, padding, closing, the §12.3 and §14.2 gates) and `build_close` (preflight: Task 2 split, I7; 3d2 preflight sizing)

**From the 2a-i re-review (M6):** `control_frames` must lift `handshake_done_frame`'s clauses and the CID conservation into its ensures. Today `self.hs_done = HsDone::Sent;` added after the helper call verifies and passes every test, which would lose HANDSHAKE_DONE on a misfit (§13.3). That mutant must fail verification.

**From the 1b re-review:** add a test that drives the I4 silent close (the trace in Task 1b's close test) through `poll_transmit` and asserts it returns `None`: nothing goes out on that CID, CONNECTION_CLOSE included.

**Files:**
- Modify: `crates/quic/src/conn.rs`
- Test: `crates/quic/tests/conn_tx.rs` (append)

**Interfaces:**
- Consumes: Task 2a-i (`build_space_packet`, `commit_datagram`, `poll_transmit`'s ensures); `pad_datagram` (takes `&mut OutDatagram`, target `1200 <= t <= MAX_DATAGRAM`), `datagram_len` (takes `&OutDatagram`; 3d2 preflight M1), `close_frame`, `close_spaces`; `Lifecycle::{may_send_close, on_close_sent, close_silently}`; `Paths::mtu_failed`; `SentPackets::new_at` (the M9 test hook).
- Produces:
  - **`poll_transmit` body** (replaces 2a-i's):
    ```
    now = max(self.now, now)
    match lc.phase():
      Draining | Closed => return None                                        // §10.2.2
      Closing => return build_close()                                         // §10.2.1, §10.2.3
    if some live k has sent(k).next_pn() >= PN_MAX { lc.close_silently(); streams = None; return None }   // §12.3; nothing polled yet (3d2 preflight M9)
    if let Some(d) = build_path_datagram(now) { return Some(d) }              // §8.2.2: never delayed (Task 2b body; stub None here)
    q = paths.active()
    if paths.mtu_failed(q) { return None }                                    // §14.2 send gate, P17 (3d2 preflight I6)
    budget = min(MAX_DATAGRAM, paths.budget(q)); can_pad = budget >= MIN_INITIAL_DATAGRAM
    d = OutDatagram{path: q, packets: vec![]}                                 // built before padding (M1)
    for k in [Initial, Handshake, OneRtt] where live(k):
      room = budget - datagram_len(&d) - header_bytes(k) - pn_len - AEAD_TAG_LEN - 3; skip k on underflow
      if let Some((p, eliciting, ack_only)) = build_space_packet(k, room, can_pad, now) { d.packets.push(p) }
      if lc.phase() !is Open { return None }                                  // pn_encode_len None closed silently (2a-i review M3): an earlier space's packet is recorded and unsent, harmless once Closed; OneRtt runs last, so no polled frame is at risk
    if d.packets is empty { return None }
    if some Initial in d is ack-eliciting { pad_datagram(&mut d, MIN_INITIAL_DATAGRAM) }   // §14.1; can_pad held; the target is exactly 1200 = MAX_DATAGRAM (M1)
    commit_datagram(q, &d); Some(d)
    ```
    - The `PN_MAX` check runs for every live space before anything is polled, so "nothing polled yet" now holds (3d2 preflight M9; the old per-space check inside the loop could fire after an earlier space had polled frames).
    - The `mtu_failed` guard makes P17 local to this body, so Task 3 does not re-prove `poll_transmit` (3d2 preflight I6, settling residual N3).
    - `// ponytail: one datagram per call (the shell loops), one CRYPTO frame per space per packet.`
  - **`fn build_path_datagram(&mut self, now) -> Option<OutDatagram>`**: contract here (`wf`; `r is Some(d) ==>` the commit facts of `commit_datagram`), body `None`. Task 2b writes the body and **strengthens these ensures** with what P12–P14 and P17's path-datagram case need (3d2 preflight M11).
  - **`build_close`**:
    - on `paths.active()`, `d = OutDatagram{path, packets}` with one packet per `k` in `close_spaces(complete, live_i, live_h, complete)` and frames `[close_frame(app, code, reason, k)]`;
    - numbers are peeked and committed once the datagram will go, and None closes silently and returns None (preflight M11);
    - `n = datagram_len(&d)`; if `n <= paths.budget(active) && lc.may_send_close(n)` → `commit_datagram`, `lc.on_close_sent(n)`, return it; else None.
    - Ensures `n <= MAX_DATAGRAM`: at most 2 packets, reason at most 64 bytes.
  - **`#[doc(hidden)] pub fn skip_pns_for_test(&mut self, k: PacketKind, next: u64)`** (3d2 preflight M9: `SentPackets::new_at` is otherwise unreachable through `Connection`), inside `verus!` so it adds no escape: requires `old.wf()`, `old.sent(k).next_pn() <= next <= PN_MAX`, `old.sent(k).inflight_len() == 0`; body `sent(k) = SentPackets::new_at(next)`; ensures `wf()` (`wf_pn` holds because `next` only grows).
  - **Ensures added to `poll_transmit`** (on top of Task 2a-i's):
    - **P1 (§8.1, §14.1 req "limits bytes", §8 "MUST limit"):** kept by `commit_datagram` being the only `on_sent`, so 3e's written bytes (`out_packet_len`) are what is bounded, per path.
    - **P2 (§14.1):** `r is Some(d)` and some Initial in `d` is ack-eliciting ⇒ `out_datagram_len(d) == 1200`.
    - **P3 (§10.2.2, §10.2.1):** Draining/Closed ⇒ `r is None`; Closing ⇒ every frame of `r` is a ConnectionClose and the closing budget holds.
    - **P6 (§12.2):** every packet in `r` has the same `dcid`.
    - **P17 (§14.2 send gate; 3d final review I2; 3d2 preflight I6):** a returned datagram on a path `q` with `paths.mtu_failed(q)` carries only `PathChallenge`, `PathResponse` and `Padding` frames (from `build_path_datagram`) or `ConnectionClose` frames (from `build_close`), and a `PathResponse` there is in a 1200-byte datagram. Here it follows from the guard plus `build_path_datagram`'s stub; Task 2b's strengthened ensures carry it for path datagrams (`mtu_failed ⇒ Validated ⇒` unlimited budget, so the builder always pads to 1200). `mtu_failed` is set only inside Task 3's `on_timeout`.
    - **§12.3 (3d2 preflight M9):** `old.phase() is Open` and some live space has `old.sent(k).next_pn() == PN_MAX` ⇒ `r is None` and `final.phase() is Closed`.

- [ ] **Step 1: Failing tests** (append to `tests/conn_tx.rs`; "poll until None" is `drain`):
  - **`pn_unencodable_closes_silently`** (2a-i review M3): `pn_max_closes_silently`'s setup, then `skip_pns_for_test(OneRtt, 1 << 40)` → `poll_transmit == None`, `phase() == Closed`, `streams_live() == false`.
  - **`harness_mirror`:** `conn()`; `poll_transmit(0) == Some(OutDatagram{0, [OutPacket{Initial, C1, L0, 0, 1, [Ack(A(2, 0, 0, []))], 0, false}]})`, `datagram_len` 47 (ACK-only, not padded); then `None`; `sent_inflight_len(Initial) == 0` (ACK-only packets are not recorded).
  - **`amp_limit`:**
    - `conn()`, `crypto_write(Initial, &[0xaa; 5000])`;
    - polls until None give exactly 3 datagrams of 1200, and the first Initial's frames start `Ack(A(2, 0, 0, [])), Crypto{0, ..}`;
    - `on_datagram(0, 1200, vec![], 1, ..)`, then `poll_transmit(1)` is `Some` of 1200 (bytes counted from a datagram with no processed packet).
  - **`amp_below_1200`:**
    - `conn()`, poll (47); `crypto_write(Initial, &[0xaa; 3000])`; two polls of 1200 (budget left 1153);
    - `crypto_write(Handshake, &[0xbb; 100])`; `poll_transmit(0) == Some` with exactly `[OutPacket{Handshake, C1, L0, 0, 1, [Crypto{0, [0xbb; 100]}], 0, false}]`, 146 bytes;
    - then `None` with Initial CRYPTO still queued;
    - `on_datagram(0, 1200, vec![ini(3, [Ping])], 1, ..)` → the next poll is 1200 and its Initial's first frame is `Ack(A(3, 0, 1, []))`.
  - **`coalesced_small`:**
    - `conn()`, `on_datagram(0, 1100, vec![ini2(3, [Ping]), hs(0, [Ping])], 1, ..)`;
    - the poll gives exactly `[OutPacket{Handshake, C1, L0, 0, 1, [Ack(A(0, 0, 0, []))], 0, false}]`;
    - `crypto_write(Handshake, &[0xbb; 10_000])`; polls until None total > 6900 bytes (validated).
  - **`close_in_handshake_spaces`:** `conn()`, `on_peer_params(&ptp() with initial_source_connection_id None, 1)`; `poll_transmit(1)` packets `[{Initial, C1, L0, 0, 1, [CC(false, 0x08, [])], 0, false}, {Handshake, C1, L0, 0, 1, [CC(false, 0x08, [])], 0, false}]`; then `None`.
  - **`app_close_conversion`:** `conn()`, `close(0x0100, true, b"bye", 1)` → Initial and Handshake packets each `[CC(false, 0x0c, [])]`. Then `established()`, `close(0x0100, true, b"bye", 20)` → one OneRtt packet `[CC(true, 0x0100, b"bye")]`.
  - **`alpn_mismatch`:** `conn()`, `on_peer_params(&ptp(), 1)`, `on_handshake_complete(b"h2", 1, ..)` → `[CC(false, 0x178, [])]` in Initial and Handshake.
  - **`closing_capped`:**
    - `established()`, `close(0x0a, false, b"", 20)`;
    - one 30-byte OneRtt datagram `[CC(false, 0x0a, [])]`, then `None`;
    - `on_datagram(0, 9, vec![], 21, ..)` → `None`;
    - `on_datagram(0, 9, vec![], 22, ..)` → `Some` (same frames, next PN), then `None`;
    - `on_datagram(5, 1200, vec![], 23, ..)` → `None` (1a-ii fix round 1: an unknown path adds no closing budget; no earlier test can read it).
  - **`pn_max_closes_silently`** (§12.3 2⁶²−1; 3d2 preflight M9):
    - `established()`; `on_datagram(0, 50, vec![one(0, [Ack(A(0, 0, 0, []))])], 20, ..)` and poll until None, so `sent_inflight_len(OneRtt) == 0`;
    - `skip_pns_for_test(OneRtt, PN_MAX)`; `poll_transmit(21) == None`;
    - `phase() == Closed`, `streams_live() == false`, and no later poll returns anything (no CONNECTION_CLOSE is ever sent).
- [ ] **Step 2:** the tests fail.
- [ ] **Step 3: Implement.** Duvet-cite:
  - §8 and §8.1: the 3× MUSTs and the count MUST at P1/`commit_datagram`; the client MUSTs as `client-only`;
  - §14.1: the expand MUST at the `pad_datagram` call, the discard MUST at `gate_packet`, "MUST also limit" at `budget`; the client MUST as `client-only`;
  - §10.2.1 and §10.2.2 at `build_close` and the Draining arm;
  - §12.2:
    - "MUST be able to process coalesced packets" and "MUST individually process each QUIC packet" at Task 1a-ii's loop;
    - "MUST NOT coalesce … different connection IDs" at P6;
    - the decryption MAY-sentence at `on_datagram`'s doc;
  - §13.2.6 and §17.2.3 (rest): the 0-RTT-ack MUST as `reason=We never accept 0-RTT.`; §17.2.3's client MUST as `client-only`;
  - §12.3's 2⁶²−1 silent close at the `PN_MAX` check, and "Duplicate suppression MUST happen after removing packet protection" at `gate_packet`.
- [ ] **Step 4: Mutations:**
  - `commit_datagram` before `pad_datagram` (fails P1's sum equality);
  - pad only when the *first* packet is Initial (fails P2 on `coalesced`-shape inputs);
  - drop the `may_elicit` Initial condition in `collect_frames` (fails P2/`out_packet_wf` with budget < 1200);
  - `build_close` reuses the previous PN (fails `wf_pn`);
  - drop the `mtu_failed(q)` guard (fails P17).
  Also run and report Task 1a-ii's test-only mutation (no `paths.on_recv` when every packet is dropped → `amp_limit` fails).
- [ ] **Step 5:** Four checks, evidence, quote check; MUST coverage for `8,8.1,10.2.1,10.2.2,12.2,12.3,13.2.1,13.2.6,14.1,17.2.3,19.20`.
- [ ] **Step 6: Commits:**
  - `feat(quic): verified Connection transmit path — per-path amplification, Initial padding, closing, PN exhaustion, MTU-failure send gate (RFC 9000 §8, §10.2, §12.2, §12.3, §14.1)`;
  - matrix: `✅ 3d: crates/quic/src/conn.rs` on the 17 Task 2a-ii rows (§19.20 replacing 3b's note; §12.3 and §13.2.1 replacing 3d's touched notes with `✅ 3d: conn.rs + sent.rs/ack_track.rs`);
  - `docs: mark RFC 9000 §8, §8.1, §10.2.x, §12.2, §12.3, §13.2.x, §14.1, §17.2.3, §19.20 closed in 3d`.

---

### Task 2b: path datagrams (`build_path_datagram`, P12–P14) (preflight: Task 2 split, I7)

"Poll until None" in this task's tests is `drain` (2a-i review M1).

**Files:**
- Modify: `crates/quic/src/conn.rs`
- Test: `crates/quic/tests/conn_tx.rs` (append)

**Interfaces:**
- Consumes: Tasks 1a-i–2a-ii (`build_path_datagram`'s contract from 2a-ii, `commit_datagram` from 2a-i); `Paths::{budget, take_response, take_challenge, has_response, challenge_owed, dcid, mtu_failed}` and Task 1b's `Paths::{len, id_at}` (3d2 preflight I1); `pad_datagram` (on the `OutDatagram`, target exactly 1200; 3d2 preflight M1), `add_sample_padding`.
- Produces:
  - **`build_path_datagram` body** (only when `complete`; PATH frames arrive only in 1-RTT):
    1. **Choose the path.** Iterate *every* path `q` in table order via `len`/`id_at` (preflight M22; 3d2 preflight I1). Skip `q` unless `has_response(q) || challenge_owed(q)` and `paths.dcid(q) is Some` (preflight I1: no fallback; §9.5).
    2. **Measure the packet, taking nothing.** It will be one OneRtt packet with `PathResponse` if `has_response(q)` and `PathChallenge` if `challenge_owed(q)`, each 9 bytes, on dcid `paths.dcid(q)`. The PN length is `close_pn_len(OneRtt)`, renamed `next_pn_len`; None closes silently (`lc.close_silently()`, `streams = None`) and returns None (preflight M11).
    3. **Decide the size.**
       - If `paths.budget(q) >= 1200`: `padded = true` (§8.2.1, §8.2.2 expand). An `mtu_failed` path is Validated, so its budget is unlimited and this branch always applies (3d2 preflight I6: settles residual N3).
       - Else: send unpadded only if the measured length `<= paths.budget(q)` (§8.2.2 "MUST NOT expand … exceeds").
       - Otherwise try the next path. Nothing on `self` has changed, so `q`'s frames stay owed, no PN is burned, and `r is None && Open ==> tx_kept(o)` holds when no path fits.
    4. **Build and commit, only for the datagram that goes**, in this order: `take_response(q)` and `take_challenge(q, padded)`; the packet with those frames and `pn = sent_1.next_pn()`, then `add_sample_padding`, then `pad_datagram(&mut d, 1200)` if `padded`; `commit_pn(OneRtt)`; `commit_datagram(q, &d)`. `recv_1` is untouched and the packet is **not recorded** (E2). `make_packet` and `packet_built` pin the DCID to the active path, so this packet has its own builder, and `transmit_ok` and `pns_fresh` come from a one-packet lemma (`lemma_packets_pns_one` and `lemma_packets_len_one`, deleted in 2a-ii, are the starting point). If relating the measured length to `datagram_len` proves harder than it looks, add read-only `Paths::peek_response` and `peek_challenge` to path.rs and build before deciding; report it if so, since path.rs holds `Paths::on_timeout`, which fails at rlimit 3.
  - `poll_transmit`'s body is unchanged: its stub call now has a body. P12 and P13 also cover `data_datagram`'s datagrams, so show that they carry no PathChallenge or PathResponse frame. `data_datagram` is the tightest function in conn.rs (passes at rlimit 3, fails at 2): if it tips, move the padding block into a helper.
  - **`build_path_datagram`'s ensures, strengthened here** (3d2 preflight M11: 2a-ii's contract is the base, not final): every frame is `PathResponse`, `PathChallenge` or `Padding`; each `PathResponse(x)` was taken from `d.path`'s responses; `padded` or the budget was below 1200; `paths.dcid(d.path)` is the packet's DCID; and `paths.mtu_failed(d.path) ==> out_datagram_len(d@) == 1200` (P17's path-datagram case, 2a-ii).
  - **Proof obligations added to `poll_transmit`'s ensures:**
    - **P12 (§8.2.2):** every `PathResponse(x)` in a datagram for path `q` was taken from `q`'s responses (it echoes a challenge received on `q`, at most once).
    - **P13 (§8.2.1, §8.2.2):** a datagram carrying PathChallenge or PathResponse has `datagram_len == 1200` unless its path's budget was below 1200.
    - **P14 (§9.5):** a datagram sent on `q` under 1-RTT `dcid` `c` has, at that send, every other path holding `c` with `peer_used` equal to `q`'s (the NAT-rebinding MAY). It follows from `wf_dcids`' pair conjunct (Task 1a-i, 3d2 preflight C1(d)), which Task 1b keeps across every receive. The property is per state, at that send: it is not a theorem over send history (Task 1b review I4; TRUSTED.md).

- [ ] **Step 1: Failing tests** (append to `tests/conn_tx.rs`):
  - **`path_response_echo`:** `established()`, `on_datagram(0, 100, vec![one(1, [PathChallenge(D(1))])], 30, &rnd(5))`; the next `poll_transmit(30)` is on path 0, contains `PathResponse(D(1))` and is 1200 bytes; no later poll contains a `PathResponse`.
  - **`probing_does_not_migrate`:** `established()`, `on_datagram(1, 1200, vec![one(1, [PathChallenge(D(2))])], 30, ..)` → a 1200-byte datagram on path 1 with `PathResponse(D(2))`; the next stream data goes to path 0.
  - **`response_not_expanded_past_amp`:** `on_datagram(1, 50, vec![one(1, [PathChallenge(D(3))])], 30, ..)` → path 1 `[OutPacket{OneRtt, C1, [], pn, 1, [PathResponse(D(3))], 0, false}]`, `datagram_len` 35 (1 + 8 + 1 + 9 + 16), within the 150-byte budget.
  - **`nat_rebinding`:**
    - `established()`, `on_datagram(1, 100, vec![one(1, [Stream{0, 0, b"GET", true}])], 30, &rnd(5))`;
    - polls until None give one path-1 datagram with `PathChallenge(rnd(5)[96..104])`, unpadded, at most 300 bytes in all on path 1; and one path-0 datagram with `PathChallenge(rnd(5)[104..112])` of 1200;
    - `on_datagram(1, 1200, vec![one(2, [PathResponse(rnd(5)[96..104])])], 40, &rnd(6))` → the next poll is on path 1 with `PathChallenge(rnd(6)[96..104])` at 1200 (MTU probe);
    - later 1-RTT data goes to path 1 with dcid C1.
  - **`fresh_cid_for_new_dcid`:** `established()`, `one(1, [NewConnectionId{1, 0, D(0xd1), [0xe1; 16]}])` on path 0, then `one_on(2, rnd(2)[0..8], [Stream{0, 0, b"GET", true}])` on path 1 → path-1 datagrams use dcid `D(0xd1)`, path-0 ones C1.
  - **`probe_new_cid_response`** (preflight I1): as `fresh_cid_for_new_dcid` but the path-1 packet is `one_on(2, rnd(2)[0..8], [PathChallenge(D(5))])` → the path-1 datagram carries `PathResponse(D(5))` with dcid `D(0xd1)`.
  - **`no_fresh_cid_no_send`:** the same without the NEW_CONNECTION_ID → no datagram with `path == 1` is ever returned; `active_path()` stays 0.
  - **`stale_cid_not_used`** (preflight I2): `nat_rebinding` up to its first polls, then `on_datagram(1, 100, vec![one(2, [NewConnectionId{1, 1, D(0xd1), [0xe1; 16]}])], 31, &rnd(6))` → every later datagram's 1-RTT dcid is `D(0xd1)`, never C1.
  - **`path_cap`:** on path 4, `on_datagram(4, 1200, vec![one(5, [PathChallenge(D(4))])], ..)` → nothing on path 4 is ever polled.
  - **`response_on_other_path_validates`** (Task 1b review M3, §8.2.2): a challenge sent on path 1 and its PATH_RESPONSE arriving on path 0 still validates path 1.
  - **`refused_path_burns_no_pn`:** `established()`; `on_datagram(1, 10, vec![one(1, [PathChallenge(D(3))])], 30, ..)` (a 30-byte budget, under the 35-byte response); `on_datagram(1, 50, vec![], 31, ..)`; `drain`: the PATH_RESPONSE goes out exactly once, and the PNs of all drained 1-RTT packets are consecutive.
  - **`second_migration_keeps_challenge`** (Task 1b review M3, §9.3 "not already underway"): migrate to path 1, poll its challenge, migrate away and back before the response → no new challenge data on path 1; the first challenge's response still validates it.
- [ ] **Step 2:** the new tests fail.
- [ ] **Step 3: Implement.** Duvet-cite:
  - §8.2.2: all seven MUSTs at `build_path_datagram`/P12/P13; "MUST NOT be enforced" at `Paths::on_response`'s call in Task 1b;
  - §8.2.1: the expand MUST at `build_path_datagram`, plus "unpredictable data" at `next_challenge` and "second path validation" at Task 1b's MTU-probe start;
  - §8.2.3: "MUST initiate another path validation with an expanded datagram" at Task 1b's MTU-probe start (E3) and at the padding of that challenge here (3d final review M1; 3d's `needs_mtu_probe` only reports the obligation).
- [ ] **Step 4: Mutations:**
  - always pad path datagrams to 1200 (fails `commit_datagram`'s requires);
  - `build_path_datagram` stops at the first candidate path (fails `nat_rebinding` when path 0's frame is blocked; a test mutation);
  - take the response from path 0 for a datagram on path 1 (fails P12);
  - fall back to `peer_cids.current()` when `paths.dcid(q)` is None (fails P14);
  - `commit_pn` at step 2 (fails `build_path_datagram`'s `tx_kept` clause).
- [ ] **Step 5:** Four checks, evidence, quote check; MUST coverage for `8.2.1,8.2.2,8.2.3`.
- [ ] **Step 6: Commits:**
  - `feat(quic): verified path datagrams — responses on the arrival path, challenge expansion within the amplification limit (RFC 9000 §8.2.1-8.2.2)`;
  - matrix: `✅ 3d: crates/quic/src/conn.rs + path.rs` on the 13 Task 2b rows (§8.2.1, its three non-small (req) rows and §8.2.3 replacing 3d's touched notes);
  - `docs: mark RFC 9000 §8.2.1, §8.2.2, §8.2.3 closed in 3d`.

---

### Task 3: Timers (`Connection::{next_timeout, on_timeout}`)

"Poll until None" in this task's tests is `drain` (2a-i review M1).

**Files:**
- Modify:
  - `crates/quic/src/conn.rs`;
  - `crates/quic/src/path.rs` (doc only; 3d2 preflight M12): the `mtu_fail` field doc says it marks any expired challenge on an MTU-unconfirmed Validated path, including §9.3.3's old-path challenge in `migrate` (residual N1); the doc nits at path.rs:271 (`kept`, `prev_validated`; residual N5);
  - `crates/quic/src/cid.rs` (doc only; 3d2 preflight M12): the doc nits at cid.rs:882 (`seq_range`/`rpt_applied`; residual N5).
- Test: `crates/quic/tests/conn_timers.rs`

**Interfaces:**
- Consumes: Tasks 1a-i–2b; `Lifecycle::{on_timeout, deadline, close_silently}`; `IdleTimer::deadline`; `effective_idle_us`; `RecvPns::ack_deadline`; `Recovery::{pto_deadline, on_packets_lost, on_pto_fired, on_path_validated}`; `SentPackets::{drain_inflight, last_sent_time}`; `Paths::{on_timeout, deadline, last_validated, set_active, mtu_failed, state, dcid, set_dcid, needs_mtu_probe, start_challenge}` and Task 1b's `Paths::{len, id_at}`; `PeerCids::use_next`.
- Produces:
  - **`pub fn next_timeout(&self) -> Option<u64>`**: the minimum of the Closing/Draining deadline; and, if Open: `idle.deadline(eff)` with `eff = effective_idle_us(local.max_idle_timeout, peer.max_idle_timeout, pto())` when Some; each live space's `ack_deadline(local_mad_us)`; each live space's `recovery.pto_deadline(k, sent(k).last_sent_time(), peer_mad_us, amp_blocked)` with `amp_blocked = paths.state(hs_path) != Validated && paths.budget(hs_path) == 0`; `paths.deadline(pto())`, the same value the next `on_timeout` snapshots as `pto0`.
  - **`pub fn on_timeout(&mut self, now: u64, rand: &[u8; RAND_LEN])`**. At entry: the clock rule, `chal_used = 0`, and **`let pto0 = self.pto()`** (3d2 preflight I4: step 3's `on_pto_fired` doubles `pto_us`, so a later `pto()` would hide a challenge that expired at `now`). Ensures `wf()` and `out_log` unchanged (3e; fix round 1 M4). Then, in order:
    1. `lc.on_timeout(now)`; then `if lc.phase() !is Open { streams = None }` (3d2 preflight M4: `Lifecycle::on_timeout` has no "Open stays Open" ensures, and `wf_streams` needs this; the 3d T7 frame-condition binding);
    2. Open and the idle deadline passed → `lc.close_silently()`, `streams = None` (§10.1);
    3. Open: for the first live space whose PTO deadline passed: `sent(k).drain_inflight(&mut lost)`; `recovery.on_packets_lost(k, lost.len(), now)` (§13.3 congestion action, D6); `on_lost_frame(k, f)` for every frame; `recovery.on_pto_fired()`; `probe(k) = true` (E8);
    4. Open: `while let Some(f) = paths.on_timeout(now, pto0)` (preflight I5: every expired path, at most `MAX_PATHS` iterations; `decreases` is the number of outstanding challenges). The loop only drains and records `active_failed |= f == paths.active()`; it calls no other `Paths` mutator, so the 3d T8 binding (a `timed_count`-unchanged ensures for any other mutator in the loop) does not arise (3d2 preflight I5);
    5. **Fallback, after the loop** (3d2 preflight I5, C1(e)). If `active_failed` and the active path is no longer usable (`state(active) != Validated`, or `mtu_failed(active)`: an expired MTU probe on the active path is treated like a validation failure, 3d final review I2):
       - with `Some(v) = paths.last_validated()`: `Paths::wf` makes `v` usable (`Validated && !mtu_failed`) and never the failed path (a failed MTU probe removes its path from `last_validated`/`prev_validated`, promoting the previous validated path). If `paths.dcid(v)` is None, give it `peer_cids.use_next()`; if that is None too, `lc.close_silently()`, `streams = None`. Otherwise `paths.set_active(v)` (§9.3.2 revert). `wf_dcids` holds: `v` has a DCID, and a `use_next()` CID is held by no other path. `// ponytail: only two validated paths are remembered, so after 0→1→2 with both 1 and 2 failing we close although 0 might still work (liveness only); a longer validated history if migration chains matter.` (residual N2);
       - with None → `lc.close_silently()`, `streams = None` (§9.3.2 silent close).
    6. `issue_cids(rand)`; then, if Open, for each path `q` (via `len`/`id_at`) with `paths.needs_mtu_probe(q)` and `next_challenge(rand)` Some(c): `paths.start_challenge(q, c, now)` (3d2 preflight M6: retries the §8.2.3 probe that Task 1b's `on_path_frame` could not start when `chal_used` was 4).
  - **P15 (§9.3.2, §14.2):** after `on_timeout`, if the active path had a challenge that expired at `now`, then `paths.state(paths.active()) == Validated && !paths.mtu_failed(paths.active())` or `lc.phase() is Closed`. Stated after step 5 (preflight I5; 3d2 preflight I5; strengthened by the 3d final review I2).
  - **P17 (§14.2 send gate; 3d final review I2)** is stated and proven in Task 2a-ii (`poll_transmit`'s `mtu_failed` guard, 3d2 preflight I6) and Task 2b (path datagrams). `mtu_failed` is set only inside `on_timeout`, and P15 plus `migrate`'s `mtu_failed` guard (Task 1b) keep the active path usable, so the guard does not fire on an Open connection in practice; it exists so that P17 needs no `wf` conjunct. This task does not re-prove `poll_transmit`.
  - Outside `verus!`: `#[doc(hidden)] pub fn send_range_counts(&self, id: u64) -> Option<(usize, usize)>`, delegating to 3d Task 1's `Streams::send_range_counts` (preflight C1).

- [ ] **Step 1: Failing tests** (`tests/conn_timers.rs`; helpers as before):
  - **`close_deadline`:** `conn()`, `on_peer_params(&ptp() with initial_source_connection_id None, 1)`, poll until None; `next_timeout() == Some(3_072_001)` (1 + 3·1_024_000; `on_peer_params` set `now = 1` by the clock rule, preflight M12); `on_timeout(3_072_001, ..)` → `is_closed()`.
  - **`draining_deadline`:** `established()`, `one(0, [CC(false, 0, [])])` at 20 → `next_timeout() == Some(3_072_020)`; `on_timeout(3_072_020, ..)` → `is_closed()`.
  - **`idle_timeout`:** `established()`, `on_timeout(30_000_010, ..)` → `is_closed()`, `poll_transmit == None`.
  - **`idle_refreshed_by_packet`** (1a-ii review M5: removing `idle.on_packet_processed` otherwise passes everything): `established()`, `one(0, [Ping])` at 20_000_000, `on_timeout(30_000_010, ..)` → `phase() == Open`.
  - **`idle_refreshed_by_send`** (2a-i review M4: removing `idle.on_eliciting_sent` otherwise passes everything; §10.1's sending-side restart): `established()`, `one(0, [Stream{0, 0, b"GET", true}])` at 1_000_000, `stream_write(0, b"ok", true)`, `poll_transmit(20_000_000)` is `Some`; `on_timeout(31_000_010, ..)` (past the receive's deadline) → `phase() == Open`.
  - **PING probe** (2a-i review M4: `probe_1` not cleared verifies): reach a probe with nothing to retransmit and assert one `Ping` goes and `probe_1` clears; if E8 makes that unreachable, say so in the report.
  - **`acked_crypto_not_resent`** (1a-ii review M1: the CRYPTO ack/lost swap passes verification): `conn()`, `crypto_write(Initial, ..)`, poll, an `ini` acknowledging that packet; fire the PTO; the following polls hold no CRYPTO frame at those offsets. The same for an acked STREAM frame after a PTO.
  - **`pto_requeue_crypto`:** `conn()`, poll; `crypto_write(Initial, &[0xaa; 100])`; `poll_transmit(0)` = Initial pn 1 `[Crypto{0, [0xaa; 100]}]`, 1200 bytes; `next_timeout() == Some(999_000)`; `on_timeout(999_000, ..)` → the poll = Initial pn 2 with the same CRYPTO frame, 1200; `next_timeout() == Some(2_997_000)`.
  - **`handshake_done_retransmitted`:** as Task 2a-i's `handshake_done_and_cids` up to its first poll; `next_timeout() == Some(1_024_010)`; `on_timeout(1_024_010, ..)` → the poll = pn 1 with the same four frames; `on_datagram(0, 50, vec![one(0, [Ack(A(1, 0, 0, []))])], 1_024_020, ..)` → the poll is `None` and `next_timeout()` has no PTO term (it equals the idle deadline).
  - **`pto_halves_cwnd`** (preflight M15):
    - `established_tx_with(ptp() with initial_max_data 1 << 30, initial_max_stream_data_bidi_local 1 << 30)`;
    - a GET on stream 0 at 30; write 100_000 bytes on stream 0;
    - poll until None gives 9 new eliciting packets: cwnd 10, and the HANDSHAKE_DONE packet is still in flight;
    - fire the PTO; the next polls give at most 5 packets before `None`.
  - **`validation_failure_reverts`:** Task 2b's `nat_rebinding` up to the first polls, never answered. One `on_timeout(30 + 3·1_024_000, ..)` → `active_path() == 0`, and the next stream write goes out on path 0. Both challenges expire together and the step-4 loop handles both (preflight I5); the 1-RTT PTO fired earlier in the same call does not delay them (`pto0`, 3d2 preflight I4).
  - **`no_validated_path_closes`** (preflight I5):
    - `conn()`, `on_peer_params(&ptp(), 10)`, `on_handshake_complete(b"h3", 10, &rnd(2))` (no Handshake packet, so path 0 is unvalidated);
    - `on_datagram(0, 100, vec![one(0, [Ping])], 20, ..)`;
    - `on_datagram(1, 100, vec![one(1, [Ping])], 20, ..)` (non-probing, so we migrate to path 1 and challenge it);
    - poll until None (the challenge is sent, not owed);
    - `on_timeout(20 + 3·1_024_000, ..)` → `is_closed()`, and no CONNECTION_CLOSE was ever polled.
  - **`mtu_probe_failure_moves_off`** (3d final review I2; added to this list by 3d2 preflight M10): Task 2b's `nat_rebinding` up to the path-1 MTU probe, never answered; `on_timeout(40 + 3·1_024_000, ..)` → `active_path() == 0`, and later stream data goes to path 0, never path 1. Then a non-probing `one(3, [Ping])` on path 1 (the next PN after `nat_rebinding`'s path-1 packets, so `migrate` is reached) leaves `active_path() == 0` (`migrate`'s `mtu_failed` guard).
  - **`validation_resets_recovery`:** `established()`, let one PTO fire (`pto_us` doubles); validate path 1 as in `nat_rebinding`; the next PTO deadline uses 1_024_000, not 2_048_000.
  - **`revalidation_keeps_pto`** (Task 1b review M3, 3d2 preflight M5): with `pto_us` doubled by a PTO, an MTU-probe answer and a §9.3.3 old-path recheck answer each leave the next PTO deadline at 2_048_000.
  - **`owed_challenge_cleared_dcid`** (Task 1b review M3): a path with an owed challenge whose DCID was then cleared: `Paths::on_timeout` and `deadline` skip owed challenges, so it adds no timer term. Assert no wake loop (`next_timeout` does not repeat at `now`) and nothing stuck on an active path; once it regains a CID the challenge goes out with its old start time and may expire at once.
  - **`alternate_ack_range_growth`** (D4; moved from Task 2 and extended with real PTO cycles, preflight C1):
    - `established_tx_with(ptp() with initial_max_data 1 << 30, initial_max_stream_data_bidi_local 1)`; GET on stream 0 with FIN; `stream_write(0, &[9; 10_000], true)`.
    - For r in 0..300 at time `t_r`, poll until None. The peer acks every *other* recorded 1-RTT PN among packets that carried no retransmitted bytes (test helper `ack_of(pns) -> AckFrame` builds descending ranges). It never acks packets that carried retransmissions, and raises `MaxStreamData{0, r + 2}` in the same packet.
    - Every 20 rounds, call `on_timeout(next_timeout().unwrap(), ..)` so the PTO declares everything in flight lost.
    - Assert throughout: `sent_inflight_len(OneRtt) <= 64`, and both counts of `send_range_counts(0)` `<= 2 * MAX_SEND_RANGES + 1`.
    - Assert at the end: no OneRtt packet after a stall carries new STREAM bytes until an ACK frees a slot or the range count drops below the gate.
    - This pins the 1-byte credit-drip adversary. Splitting large lost ranges on partial retransmission is not exercised; its bound is 3d D4's ~1000 term.
- [ ] **Step 2:** the tests fail.
- [ ] **Step 3: Implement.** Duvet-cite §9.3.2 (both MUSTs at steps 4–5); §14.2's cease-sending MUST at Task 2a-ii's `mtu_failed` guard (P17; 3d final review I2; it replaces 3d's former exception at `MAX_DATAGRAM`); §9.4 ("MUST NOT contribute to congestion control" at E2's not-recording in Task 2b's builder, cited there. The old-path clause is a placeholder with `// ponytail: one shared Recovery, so old-path records acked after on_path_validated still raise cwnd; Phase 6 keeps per-path state.`, preflight M8; "MUST immediately reset" at `on_path_validated`'s call; "MUST NOT be more aggressive" at `paths.deadline(pto())` and `paths.on_timeout(now, pto0)`, 3·PTO); §13.3's congestion MUST at step 3; §10.1's restart at step 2 (already cited in lifecycle.rs; a second citation is fine).
- [ ] **Step 4: Mutations:** step 5 reverts to the failed path (fails P15); step 5 ignores `mtu_failed` on the active path (fails P15); step 5 makes `v` active without giving it a DCID (fails `wf_dcids`; 3d2 preflight C1(e)); `migrate` drops its `mtu_failed` guard (no proof failure now that Task 2a-ii's guard makes P17 local: a test mutation, `mtu_probe_failure_moves_off`'s last step); step 4 uses `pto()` instead of `pto0` (fails `validation_failure_reverts`, a test mutation; 3d2 preflight I4); step 4 handles only the first expired path (fails `validation_failure_reverts`, a test mutation); 3d Task 1's `MAX_SEND_RANGES` gate removed (fails `alternate_ack_range_growth`, a test mutation); step 2 before step 1 with a `<` deadline compare (fails `idle_timeout`, a test mutation); `pto_deadline` ignores `amp_blocked` (fails the RFC 9002 §6.2.2.1 ensures if stated; otherwise a test mutation — say which); step 3 skips `on_packets_lost` (fails `pto_halves_cwnd`).
- [ ] **Step 5:** Four checks, evidence, quote check; MUST coverage for `9.3.2,9.4,10.1,13.3,14.2`.
- [ ] **Step 6: Commits:** `feat(quic): verified Connection timers — idle, close/drain, PTO placeholder with congestion action, path-validation fallback (RFC 9000 §9.3.2, §9.4, §10.1, §13.3)`; matrix: `✅ 3d: crates/quic/src/conn.rs + path.rs` on §9.3.2 and §9.4 (note "port-only MAY not used; RTT/CC reset is Recovery::on_path_validated (placeholder until Phase 6)"); on §13.3 replace the touched notes with `✅ 3d: crates/quic/src/conn.rs (retransmission routing) + recovery.rs (AIMD placeholder congestion action, Phase 6 replaces)`; on §14.2 replace 3d's touched note with `✅ 3d: crates/quic/src/conn.rs (P17 send gate) + path.rs (mtu_failed)`; `docs: mark RFC 9000 §9.3.2, §9.4, §13.3, §14.2 closed in 3d`.

---

### Task 4: HTTP/3 adapter with write deferral (`quic::h3_server`)

**Files:**
- Create: `crates/quic/src/h3_server.rs`
- Modify: `crates/quic/Cargo.toml` (`h3 = { path = "../h3" }` under `[dependencies]`; the Global Constraints' manifest exception, preflight M18), `Cargo.lock`, `crates/quic/src/lib.rs`, `TRUSTED.md` (extend the row with `H3Server`, `AppEvent`, `SendError`)
- Test: `crates/quic/tests/h3_server.rs`

**Interfaces:**
- Consumes: Tasks 1a-i–3; 2b's `h3::conn::{H3Conn, Output}` (fields named `stream_id`; 3d2 preflight M13), `h3::message::Response`, `h3::qpack::field_section::FieldLine`, `h3::codes::{H3_GENERAL_PROTOCOL_ERROR (0x101), H3_CLOSED_CRITICAL_STREAM (0x104), H3_MISSING_SETTINGS (0x10a), H3_REQUEST_CANCELLED (0x10c)}`, `h3::limits::MIN_PEER_UNI_STREAMS`; 3c's `StreamEvent`.
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
  - **`apply(outs, app)`**, one arm per `Output`: `StreamWrite{stream_id, data, fin}` → push `Pending{id: stream_id, data, 0, fin}`, then `flush()`; `ResetStream{stream_id, code}` → remove pending entries for `stream_id`, `conn.stream_reset(stream_id, code)`; `StopSending{stream_id, code}` → `conn.stream_stop_sending`; `CloseConnection{code}` → `conn.close(code, true, &[], conn.now())`; `Request`/`RequestBody`/`RequestEnd` → `app.push(H3(o))`.
  - **`fn flush(&mut self)`**: while `pending` is non-empty: `e = &pending[0]`; `conn.stream_write(e.id, &e.data[e.off..], e.fin)`: `Ok(n)` → `e.off += n`; if the whole tail was taken (and, when `e.fin`, the FIN with it; a `fin == false` entry is done once its tail is taken, 3d2 preflight M13), `pending.remove(0)` (the `Vec` is dropped), else stop; `Err(())` → remove every entry for `e.id` (the stream was reset or stopped; h3 already knows). `// ponytail: Vec::remove(0) on <= a few entries (one response + control writes).`
  - **`pub fn send_response(&mut self, id: u64, resp: &Response, app: &mut Vec<AppEvent>) -> (r: Result<(), SendError>)`**: `!pending.is_empty()` → `Err(Busy)` **without calling h3** (E6); else `h3.send_response(id, resp, &mut outs)`: `Err` → `Err(Rejected)`; `Ok` → `apply(outs, app)`, `Ok(())`. Ensures `r is Err(Busy) ==> self.h3 == old.h3`.
  - `pub fn can_send(&self) -> bool` = `pending.is_empty()`.
  - `pub fn on_datagram(&mut self, path, datagram_len, packets, now, rand, app)` = `conn.on_datagram(..)` then `pump` (same `requires` as `Connection::on_datagram`); `pub fn on_timeout(&mut self, now, rand, app)` = `conn.on_timeout(..)` then `pump`; `pub fn shutdown(&mut self, app)` = `h3.shutdown`, then `apply`.
  - **Proof obligations:** every `StreamEvent` drained from `conn` is passed to exactly one `h3` method, in order (2b obligation 1; so 2b's chunking theorem applies to the QUIC byte stream and 3c's E1–E5 hold for what `h3` sees); per stream, the bytes passed to `conn.stream_write` are a prefix of the concatenated `StreamWrite` data h3 emitted for it, in order, unless that stream's entries were dropped on `ResetStream`/`Err`; `send_response` returns Busy without changing `h3`.
  - Outside `verus!`: `#[doc(hidden)] pub fn pending_bytes(&self) -> usize`, summed with `saturating_add` (preflight M19b).

- [ ] **Step 1: Failing tests** (`tests/h3_server.rs`; Task 1a-i–3 helpers duplicated; `est()` = `H3Server::new(established())` then `pump`):
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

## Bindings from 3d Tasks 7–8 reviews

The 3d2 preflight (2026-10-29) found conflicts in some of these; each such bullet is now a pointer to the task that owns it.

- **Paths (3d T8):**
  - Per-id `Paths` ops require `has(id)`: folded into Task 1a-i's getters (3d2 preflight I7).
  - A failed-MTU path (Validated, `mtu_failed`; 3d final review I2): folded into Task 2a-ii's P17 guard, Task 2b's strengthened `build_path_datagram` ensures, Task 1b's `migrate` guard and Task 3 step 5/P15 (3d2 preflight I6).
  - `set_validated` is handshake-only (§8.1), and it marks the MTU confirmed (§14.1).
  - One PATH_CHALLENGE per validation attempt (E2), never retransmitted with new data (3d final review M4: `on_response` matches only the current challenge, so a retransmission would orphan a late response to the first). A lost challenge fails after 3·PTO and Task 3 step 5 falls back.
  - The `timed_count` condition on the Task 3 failure loop: folded into Task 3 steps 4–5 (the fallback runs after the loop; 3d2 preflight I5).
- **Lifecycle (3d T7):** `Lifecycle` exposes closed spec accessors, not a View. The frame conditions on `on_recv_closing`, `on_close_sent`, `on_timeout`, `enter_draining` and `enter_closing` (non-Open) are the ones 3d2 may rely on. `on_timeout`'s lack of an "Open stays Open" ensures: folded into Task 3 step 1 (3d2 preflight M4).

## Residuals from the 3d final re-review (rule in the owning 3d2 task)

- **N1** (`mtu_fail` field doc in path.rs over-claims): folded into Task 3's Files (3d2 preflight M12).
- **N2** (only two validated paths remembered): folded into Task 3 step 5's `ponytail:` (3d2 preflight M12).
- **N3** (P17 and PATH_RESPONSE on an `mtu_failed` path): folded into Task 2a-ii's P17 and Task 2b's padding rule: such a response is always in a 1200-byte datagram (3d2 preflight I6).
- **N4** (`MAX_TOKENS` never-fail depends on the 3e order binding): folded into Task 1a-i's `poll_cid_updates` ensures and token binding, as a module-doc caller obligation rather than a `requires` (3d2 preflight I8).
- **N5** (doc nits at cid.rs:882 and path.rs:271): folded into Task 3's Files (3d2 preflight M12).


## Binding notes for later phases

- **3e, from the 3d final review** (no 3e plan is under `docs/superpowers/plans` yet; carry these into its binding block):
  - **Order (I1):** after `route` returns `Route::NewInitial`, call `Connection::accept`, then `CidTable::apply` every update from `poll_cid_updates`, before routing the next datagram. `has_room` counts admitted connections, and a connection is admitted by its first `Add`; another datagram routed in between could be admitted against the same slot. Apply `poll_cid_updates` after every `on_datagram`/`on_timeout` too, and `remove_conn` when a connection is dropped.
  - **Per-datagram cost (I3):** `route` costs at most `MAX_TABLE` (512) CID comparisons plus, for a datagram of at least 21 bytes matching no CID, `MAX_TOKENS` (816) constant-time 16-byte token comparisons; about 100 connections (`MAX_CONNS` = 102) is the ceiling this linear scan is sized for. A random-keyed SipHash index for CIDs and tokens (a token lookup compares CT against one bucket only) replaces it before production; a sorted Vec is not acceptable (it leaks token order, §10.3.1).
- **3e:** `protect(p: &OutPacket, keys, out)` writes exactly `out_packet_len(p@)` bytes, including `p.padding` zero bytes and `p.spin` for short headers; datagrams are the packets concatenated. On receive: `unprotect` uses `largest = conn.largest_pn(kind)` and `dcid_len = LOCAL_CID_LEN`; call `conn.on_reset_candidate(last16, now)` when the first packet fails to decrypt; always call `on_datagram` with the UDP payload length, even with no surviving packet; every `PlainPacket` passed must satisfy `plain_wf` (from `parse_payload`'s ensures). `RAND_LEN` is 129. **Pass at most one 1-RTT packet per datagram to `on_datagram`** (QUIC short headers have no length, so parsing gives this; its contract allows more): `next_challenge` has 4 slices per call, and only this keeps them from running out before `migrate`'s challenges, which have no retry (Task 1b review M4). The harness's "A.2 → one reply ≤ 3600" is `harness_mirror`'s 47-byte ACK-only Initial.
  - **What 3e Task 5 consumes from `poll_transmit`** (preflight I6): `Connection::out_log()` (closed spec fn); `poll_transmit` ensures that `out_log()` is pushed with exactly the returned datagram (unchanged on None); P7 on the result (`out_packet_wf` for every packet); P16 `out_datagram_len(d@) <= MAX_DATAGRAM`. 3e's Decision 14 fallback is therefore not needed.
  - **§12.2 order (Task 2a-ii review M6):** datagrams are written in `packets` order; a 1-RTT packet is always alone because `complete ==> !live_i && !live_h`; state this if 3e needs it as a proof fact.
  - The 3e draft's cross-references move: `Connection` is this plan's Tasks 1a-i–3; `PathId` is 3d Task 6 (`datagram.rs`); `MAX_PATHS` is 3d Task 8 (`path.rs`); the test helpers are in `tests/conn_rx.rs`. 3e Task 6 and Phase 8a Task 10 both edit verify.sh's success line, so the second to land merges the two (preflight M21).
- **Phase 4:** drives `crypto_read`/`crypto_write`/`on_peer_params` (requires `peer_tp_wf`, via `theorem_peer_tp_wf`)/`on_handshake_complete(alpn)`/`on_tls_alert` and serializes `local_params()`; RFC 9001 A.2's ClientHello fails §7.3 against A.2's own header; key discard follows `discard`. The 3e shell switches from `Connection` to `H3Server` here.
- **Phase 6:** path datagrams are outside congestion control (E2) and there is one per owed response: on a validated path 62 bytes in draws 4800 out (77:1), attacker-paced. Decide this with E2; every owed response in one 1200-byte packet gives 19:1 and needs no new state (Task 2b review M2).
- **Phase 6:** `SentPacket.size` and `on_packet_sent`'s size understate padded Initials: 2a-ii pads after `commit_space_packet`, and nothing reads the size today (2a-i review M5). Replace `Recovery`'s bodies and the PTO step (E8: today's placeholder marks the space lost on PTO, against RFC 9002 §6.2 "PTO expiry MUST NOT mark prior unacked packets lost" — a Phase 6 row); keep `can_send` as the gate in `build_space_packet` and `MAX_INFLIGHT` as a memory cap; feed RTT samples from `on_ack_received`. Phase 6 may extend the `Recovery` signatures (send times, sizes); the placeholder's counts don't carry what RFC 9002 needs (preflight M7).

## Exit criteria (Phase 3d2)

- All four checks pass on the merged tree, with N = the escape count of `main` at merge (preflight M19d).
- The 48 rows carry `✅ 3d: <file>`; 3b's notes on §10.3 and §19.20, 3c's on §13.3 and 3d's touched notes are replaced; `python3 -I <scratch>/chk3d/rows1029.py <scratch>/chk3b/d3.txt` prints `88 40 48` (preflight: per-task lines as in "Matrix rows": Task 1a-ii 6, 1b 8, 2a-ii 17, 2b 13, 3 4; the script labels them `T1a` and `T2a`).
- Tasks 1a-i, 1a-ii, 1b, 2a-i, 2a-ii, 2b, 3 and 4 are each committed with their own evidence directory and review.
- Every MUST in the 3d sections is cited or excepted: `python3 -I <scratch>/duvet_q.py <json> 5.1,5.1.1,5.1.2,5.2,5.2.2,5.2.3,7,7.2,7.3,7.4.1,8,8.1,8.1.3,8.2.1,8.2.2,8.2.3,9,9.3,9.3.2,9.3.3,9.4,9.5,10.1,10.2.1,10.2.2,10.2.3,10.3,10.3.1,10.3.2,11,11.1,12.2,12.3,13.1,13.2.1,13.2.3,13.2.5,13.2.6,13.3,13.4.1,13.4.2.1,13.4.2.2,14.1,14.2,17.2.3,19.15,19.16,19.17,19.20,21.11` prints nothing (144 lines at 3b: `<scratch>/chk3d/musts-open-at-3b.txt`).
- `phase-3d2` is merged into `main`.

## Self-review (done while writing)

- **Outline obligations → pinned items:** 3× until validated → P1 (per path); nothing while draining → P3; PNs strictly increasing → P4; active issued CIDs ≤ peer limit → 3d Task 4 `issue`; ack-eliciting Initial datagrams ≥ 1200 → P2; PATH_RESPONSE echo → P12.
- **3c caller obligations → here:** frames polled are sent (P8); `start()` first and drain gated (Task 4); every event in order (Task 4 obligation); abort signal (E7); every StopSending forwarded; Output mapping (`apply`); own-uni cap (3d Task 1); backpressure (E5, E6); ACK-range growth (3d Task 1 gate and test, Task 3 PTO-cycle test, 3d D4; preflight C1); loop on `poll_data` (Task 2a-i CRYPTO rule); fresh state on drop (Task 1a-i `discard`/`close`, `crypto_capacity` pinned in Task 1a-ii); spin per CID (Tasks 1a-i/1b `rand[128]`); no 1-RTT before completion (Task 1a-ii gate); window pinned (3d Task 1). The parent plan's 3c follow-ups table still names "3d2 Task 1a"/"Task 2a" in rows 3, 5, 6, 3c, 3b and 4b; read those as Tasks 1a-i/1a-ii and 2a-i/2a-ii as mapped here (`can_send` gate and P8: 2a-i).
- **Arithmetic re-checked:** ACK-only Initial 26 + 5 + 16 = 47; Handshake CRYPTO-100 26 + 104 + 16 = 146; closing 30 bytes vs 27/54; PTO 999_000, 1_024_000, 3·1_024_000 = 3_072_000; unpadded response 1 + 8 + 1 + 9 + 16 = 35; `rnd(2)[128] = 130` (spin false).
- **Proportion.** Bodies only where order is the requirement: `on_datagram`, `migrate`, `poll_transmit` (2a-i provisional, 2a-ii final), `collect_frames`/`commit_space_packet`, `build_path_datagram`, `on_timeout`, `pump`, `flush`.
