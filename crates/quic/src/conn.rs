//! The server's QUIC connection (RFC 9000): one `Connection` joins the packet number spaces,
//! CRYPTO streams, `Streams`, connection IDs, paths and lifecycle. Sans-IO: the shell hands in
//! decrypted packets, datagram sizes, times and randomness, and the TLS calls below.
//!
//! Caller obligations, which `Connection` cannot state as `requires`:
//! - Drain `poll_stream_events` after every `on_datagram`: `events` is bounded only by that.
//!   `H3Server::pump` discharges this; 3e drives `Connection` before any stream exists.
//! - Apply each `poll_cid_updates` output to the `CidTable`, in order, before routing the next
//!   datagram. Then the table holds only tokens of CIDs we have used and never those of retired
//!   CIDs (§10.3.1), each connection registers at most `PEER_CID_CAP` tokens, and
//!   `CidTable::apply(AddToken)` never fails at `MAX_TOKENS`. `tokens_registered` can lag
//!   `used_tokens()` between polls (a retirement in `on_new_cid` shrinks the latter), so that is
//!   an ensures of `poll_cid_updates` and not part of `wf`.
//!
//! Registration: every active local CID, and `odcid` while the Initial space is live, goes
//! through `cid_updates`. Each `issue` pushes its `Add`, each retirement its `Remove`,
//! `discard(Initial)` the `Remove(odcid)`, and a `Remove` is queued before its replacement `Add`.
//! So at every prefix of a poll a connection owns at most `ISSUE_CAP_ACTIVE` active CIDs plus
//! `odcid`, `PER_CONN` table entries, and `apply(Add)` fails only on a key collision.
use vstd::prelude::*;
use vstd::slice::{slice_subrange, slice_to_vec};

use crate::ack::*;
use crate::ack_track::*;
use crate::cid::*;
use crate::codes::*;
use crate::crypto_stream::*;
use crate::datagram::*;
use crate::frame::*;
use crate::handshake::*;
use crate::lifecycle::*;
use crate::path::*;
use crate::payload::*;
use crate::recovery::*;
use crate::recv_stream::*;
use crate::route::*;
use crate::send_stream::*;
use crate::sent::*;
use crate::streams::*;
use crate::tp::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use crate::amp::*;
#[allow(unused_imports)]
use wire::varint::*;

verus! {

/// The randomness each call that needs it takes: `rand[0..96]` is four 24-byte CID slices (CID
/// and reset token), `rand[96..128]` four 8-byte PATH_CHALLENGE slices, `rand[128]` the spin bit.
pub const RAND_LEN: usize = 129;

pub const H3_ALPN: [u8; 2] = *b"h3";

pub open spec fn space_idx(k: PacketKind) -> int {
    match k {
        PacketKind::Initial => 0,
        PacketKind::Handshake => 1,
        PacketKind::OneRtt => 2,
    }
}

/// HANDSHAKE_DONE (§19.20): not due, owed, sent and unacknowledged, or acknowledged.
#[derive(Clone, Copy)]
pub enum HsDone {
    No,
    Pending,
    Sent,
    Acked,
}

// =============================================================================
// What `wf` says of the ghost log
// =============================================================================

/// The `Sent` sizes of an amplification trace, in order.
pub open spec fn sent_entries(t: Seq<AmpEv>) -> Seq<nat>
    decreases t.len(),
{
    if t.len() == 0 {
        Seq::empty()
    } else {
        match t.last() {
            AmpEv::Sent(n) => sent_entries(t.drop_last()).push(n),
            _ => sent_entries(t.drop_last()),
        }
    }
}

/// The lengths of the datagrams logged on path `q`, in order.
pub open spec fn log_sends(log: Seq<SpecOutDatagram>, q: PathId) -> Seq<nat>
    decreases log.len(),
{
    if log.len() == 0 {
        Seq::empty()
    } else if log.last().path == q {
        log_sends(log.drop_last(), q).push(out_datagram_len(log.last()))
    } else {
        log_sends(log.drop_last(), q)
    }
}

/// The packet numbers of the packets of kind `k`, in order.
pub open spec fn packets_pns(s: Seq<SpecOutPacket>, k: PacketKind) -> Seq<u64>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else if s.last().kind == k {
        packets_pns(s.drop_last(), k).push(s.last().pn)
    } else {
        packets_pns(s.drop_last(), k)
    }
}

/// The packet numbers of space `k` across the log, in order.
pub open spec fn log_pns(log: Seq<SpecOutDatagram>, k: PacketKind) -> Seq<u64>
    decreases log.len(),
{
    if log.len() == 0 {
        Seq::empty()
    } else {
        log_pns(log.drop_last(), k) + packets_pns(log.last().packets, k)
    }
}

/// Strictly increasing, and below `next` (`SentPackets::next_pn`).
pub open spec fn pns_ok(s: Seq<u64>, next: u64) -> bool {
    &&& forall|i: int, j: int| 0 <= i < j < s.len() ==> #[trigger] s[i] < #[trigger] s[j]
    &&& forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] < next
}

/// Some active peer CID we have used is `c`. An unused one is held by no path, so `use_next()`
/// gives a new destination its own CID, and every CID we send with has its token in
/// `used_tokens()`.
pub open spec fn used_cid(e: Seq<PeerEntry>, c: Seq<u8>) -> bool {
    exists|i: int| 0 <= i < e.len() && (#[trigger] e[i]).1@ == c && e[i].3
}

/// `cid_updates` carries our CIDs only; `poll_cid_updates` adds the token updates.
pub open spec fn cids_only(s: Seq<CidUpdate>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] is Add || s[i] is Remove
}

/// No `AddToken` precedes a `RemoveToken`: otherwise a connection briefly holds more than
/// `PEER_CID_CAP` tokens, and with every connection at the cap `AddToken` fails at `MAX_TOKENS`.
pub open spec fn removes_before_adds(s: Seq<CidUpdate>) -> bool {
    forall|i: int, j: int|
        0 <= i < j < s.len() && #[trigger] s[i] is AddToken ==> !(#[trigger] s[j] is RemoveToken)
}

/// Each token update in `s` is a real change from `before` to `after`.
pub open spec fn tokens_changed(s: Seq<CidUpdate>, before: Seq<[u8; 16]>, after: Seq<[u8; 16]>) -> bool {
    forall|i: int|
        0 <= i < s.len() ==> match #[trigger] s[i] {
            CidUpdate::RemoveToken(t) => before.contains(t) && !after.contains(t),
            CidUpdate::AddToken(t) => after.contains(t) && !before.contains(t),
            _ => true,
        }
}

/// `s` holds a token update for every change from `before` to `after`.
pub open spec fn tokens_covered(s: Seq<CidUpdate>, before: Seq<[u8; 16]>, after: Seq<[u8; 16]>) -> bool {
    &&& forall|i: int|
        0 <= i < before.len() && !after.contains(before[i]) ==> s.contains(
            CidUpdate::RemoveToken(#[trigger] before[i]),
        )
    &&& forall|i: int|
        0 <= i < after.len() && !before.contains(after[i]) ==> s.contains(
            CidUpdate::AddToken(#[trigger] after[i]),
        )
}

// =============================================================================
// The connection
// =============================================================================

/// One server connection.
pub struct Connection {
    now: u64,
    hs_path: PathId,
    ids: HandshakeIds,
    local_tp: TransportParams,
    peer_tp: Option<TransportParams>,
    paths: Paths,
    lc: Lifecycle,
    idle: IdleTimer,
    recovery: Recovery,
    recv_i: RecvPns,
    recv_h: RecvPns,
    recv_1: RecvPns,
    sent_i: SentPackets,
    sent_h: SentPackets,
    sent_1: SentPackets,
    live_i: bool,
    live_h: bool,
    /// 1-RTT is live iff `complete`.
    complete: bool,
    crx_i: CryptoStream,
    crx_h: CryptoStream,
    /// Post-handshake CRYPTO: buffered, and TLS never asks for it.
    crx_1: CryptoStream,
    ctx_i: SendStream,
    ctx_h: SendStream,
    streams: Option<Streams>,
    events: Vec<StreamEvent>,
    local_cids: LocalCids,
    peer_cids: PeerCids,
    cid_updates: Vec<CidUpdate>,
    tokens_registered: Vec<[u8; 16]>,
    #[allow(dead_code)]  // Read from Task 2a-i.
    hs_done: HsDone,
    #[allow(dead_code)]  // Read from Task 2a-i.
    probe_i: bool,
    #[allow(dead_code)]  // Read from Task 2a-i.
    probe_h: bool,
    #[allow(dead_code)]  // Read from Task 2a-i.
    probe_1: bool,
    #[allow(dead_code)]  // Read from Task 2a-i.
    spin: bool,
    /// Challenge slices of `rand` used in this call; every pub fn that takes `rand` resets it.
    chal_used: usize,
    /// Only `wf` and `out_log()` read it, which a plain `cargo build` erases.
    #[allow(dead_code)]
    out_log: Ghost<Seq<SpecOutDatagram>>,
}

impl Connection {
    /// Every datagram `poll_transmit` has returned, in order.
    pub closed spec fn out_log(&self) -> Seq<SpecOutDatagram> {
        self.out_log@
    }

    pub closed spec fn recv(&self, k: PacketKind) -> RecvPns {
        match k {
            PacketKind::Initial => self.recv_i,
            PacketKind::Handshake => self.recv_h,
            PacketKind::OneRtt => self.recv_1,
        }
    }

    pub closed spec fn sent(&self, k: PacketKind) -> SentPackets {
        match k {
            PacketKind::Initial => self.sent_i,
            PacketKind::Handshake => self.sent_h,
            PacketKind::OneRtt => self.sent_1,
        }
    }

    pub closed spec fn live(&self, k: PacketKind) -> bool {
        match k {
            PacketKind::Initial => self.live_i,
            PacketKind::Handshake => self.live_h,
            PacketKind::OneRtt => self.complete,
        }
    }

    pub closed spec fn phase_spec(&self) -> Phase {
        self.lc.phase_spec()
    }

    pub closed spec fn events_spec(&self) -> Seq<StreamEvent> {
        self.events@
    }

    pub closed spec fn updates_spec(&self) -> Seq<CidUpdate> {
        self.cid_updates@
    }

    pub closed spec fn registered(&self) -> Seq<[u8; 16]> {
        self.tokens_registered@
    }

    /// `tokens_registered`, as a set, is `peer_cids.used_tokens()`, and within the cap.
    pub closed spec fn tokens_in_sync(&self) -> bool {
        &&& self.tokens_registered@.len() <= PEER_CID_CAP
        &&& forall|t: [u8; 16]|
            #![trigger self.tokens_registered@.contains(t)]
            #![trigger reset_match(self.peer_cids.entries(), t@)]
            self.tokens_registered@.contains(t) <==> reset_match(self.peer_cids.entries(), t@)
    }

    closed spec fn wf_parts(&self) -> bool {
        &&& self.ids.wf()
        &&& self.paths.wf()
        &&& self.lc.wf()
        &&& self.recovery.wf()
        &&& self.recv_i.wf() && self.recv_i.kind_spec() is Initial
        &&& self.recv_h.wf() && self.recv_h.kind_spec() is Handshake
        &&& self.recv_1.wf() && self.recv_1.kind_spec() is OneRtt
        &&& self.sent_i.wf()
        &&& self.sent_h.wf()
        &&& self.sent_1.wf()
        &&& self.crx_i.wf()
        &&& self.crx_h.wf()
        &&& self.crx_1.wf()
        &&& self.ctx_i.wf()
        &&& self.ctx_h.wf()
        &&& self.local_cids.wf()
        &&& self.peer_cids.wf()
        &&& local_tp_ok(self.local_tp@)
        &&& server_tp_wf(self.local_tp@)
        &&& self.peer_tp matches Some(t) ==> peer_tp_wf(t@)
        &&& self.complete ==> (self.peer_tp is Some && self.streams is Some) || !(
        self.lc.phase_spec() is Open)
        &&& self.complete ==> !self.live_i && !self.live_h
        &&& self.chal_used <= 4
        &&& self.sent_i.inflight_spec().len() + self.sent_h.inflight_spec().len()
            + self.sent_1.inflight_spec().len() <= MAX_INFLIGHT
        &&& self.paths.has(self.hs_path)
        &&& cids_only(self.cid_updates@)
    }

    /// `Streams` is never called after an `Err`, and closing drops it, which frees the buffers.
    closed spec fn wf_streams(&self) -> bool {
        &&& self.streams matches Some(s) ==> s.wf() && !s.failed() && self.lc.phase_spec() is Open
        &&& !(self.lc.phase_spec() is Open) ==> self.streams is None
    }

    /// §8.1, per path: the budget's `Sent` entries are exactly the logged datagrams.
    closed spec fn wf_amp(&self) -> bool {
        forall|q: PathId|
            #[trigger] self.paths.has(q) ==> amp_ok(self.paths.amp_trace(q)) && sent_entries(
                self.paths.amp_trace(q),
            ) == log_sends(self.out_log@, q)
    }

    /// §12.3: `sent(k)` is drained on discard, never replaced, so `next_pn` never goes back.
    closed spec fn wf_pn(&self) -> bool {
        &&& pns_ok(log_pns(self.out_log@, PacketKind::Initial), self.sent_i.next_pn_spec())
        &&& pns_ok(log_pns(self.out_log@, PacketKind::Handshake), self.sent_h.next_pn_spec())
        &&& pns_ok(log_pns(self.out_log@, PacketKind::OneRtt), self.sent_1.next_pn_spec())
    }

    /// What lets `Paths::insert` add an id whose filtered log is empty.
    closed spec fn wf_log_paths(&self) -> bool {
        forall|i: int|
            0 <= i < self.out_log@.len() ==> #[trigger] self.paths.index_spec(
                self.out_log@[i].path,
            ) is Some
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-9.5
    //# Similarly, an endpoint MUST NOT reuse a connection ID when sending to
    //# more than one destination address.
    /// The active path has a DCID, every DCID is active (§5.1.2 "MUST stop using") and used, and
    /// §9.5: two paths share a DCID only if the peer used the same CID on both (its MAY: the
    /// peer used the same CID from a new address, NAT rebinding).
    closed spec fn wf_dcids(&self) -> bool {
        &&& self.paths.path(self.paths.active_spec()).dcid is Some
        &&& forall|q: PathId| #[trigger]
            self.paths.has(q) ==> (self.paths.path(q).dcid matches Some(c) ==> used_cid(
                self.peer_cids.entries(),
                c,
            ))
        &&& forall|q1: PathId, q2: PathId|
            #[trigger] self.paths.has(q1) && #[trigger] self.paths.has(q2) && q1 != q2
                && self.paths.path(q1).dcid is Some && self.paths.path(q1).dcid == self.paths.path(
                q2,
            ).dcid ==> self.paths.path(q1).peer_used == self.paths.path(q2).peer_used
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.wf_parts()
        &&& self.wf_streams()
        &&& self.wf_amp()
        &&& self.wf_pn()
        &&& self.wf_log_paths()
        &&& self.wf_dcids()
    }

    /// §9.5: no path holds an unused peer CID, so `use_next()` never reuses a path's CID.
    proof fn lemma_unused_cid_unheld(&self, i: int, q: PathId)
        requires
            self.wf(),
            0 <= i < self.peer_cids.entries().len(),
            !self.peer_cids.entries()[i].3,
            self.paths.has(q),
        ensures
            self.paths.path(q).dcid != Some(self.peer_cids.entries()[i].1@),
    {
        let e = self.peer_cids.entries();
        self.peer_cids.lemma_wf();
        if self.paths.path(q).dcid == Some(e[i].1@) {
            let j = choose|j: int| 0 <= j < e.len() && (#[trigger] e[j]).1@ == e[i].1@ && e[j].3;
            if j < i {
                assert(e[j].1@ != e[i].1@);
            } else {
                assert(e[i].1@ != e[j].1@);
            }
        }
    }

    // =========================================================================
    // Accept
    // =========================================================================

    /// A connection for this client's first Initial. Nothing is processed or counted: the
    /// shell next calls `on_datagram` with the whole datagram.
    #[verifier::spinoff_prover]
    pub fn accept(
        first: &PlainPacket,
        datagram_len: usize,
        path: PathId,
        now: u64,
        rand: &[u8; RAND_LEN],
        local_tp: &TransportParams,
    ) -> (r: Option<Connection>)
        requires
            plain_wf(first@),
        ensures
            r is None <==> (!(first.kind is Initial) || datagram_len < MIN_INITIAL_DATAGRAM
                || first.dcid@.len() < 8 || first.dcid@.len() > MAX_CID_LEN || first.scid@.len()
                > MAX_CID_LEN || !local_tp_ok(local_tp@)),
            r matches Some(c) ==> c.wf() && c.out_log() == Seq::<SpecOutDatagram>::empty(),
    {
        if datagram_len < MIN_INITIAL_DATAGRAM || !is_local_tp_ok(local_tp) {
            return None;
        }
        let mut l0 = [0u8; 8];
        l0.copy_from_slice(slice_subrange(rand.as_slice(), 0, 8));
        let mut token0 = [0u8; 16];
        token0.copy_from_slice(slice_subrange(rand.as_slice(), 8, 24));
        let ids = match from_first(first.kind, first.dcid.as_slice(), first.scid.as_slice(), l0) {
            Some(h) => h,
            None => return None,
        };
        // Never true (§8.1.3): the client stays unvalidated.
        let _ = token_validates(first.token.as_slice());
        let filled = ids.fill_local_tp(local_tp, token0);
        let mut paths = Paths::new(path);
        proof {
            assert(paths.ids()[0] == path);
        }
        paths.set_dcid(path, Some(first.scid.as_slice()));
        let mut cid_updates = Vec::new();
        cid_updates.push(CidUpdate::Add(slice_to_vec(ids.odcid())));
        cid_updates.push(CidUpdate::Add(slice_to_vec(l0.as_slice())));
        let peer_cids = PeerCids::new(first.scid.as_slice());
        let c = Connection {
            now,
            hs_path: path,
            ids,
            local_tp: filled,
            peer_tp: None,
            paths,
            lc: Lifecycle::new(),
            idle: IdleTimer::new(now),
            recovery: Recovery::new(),
            recv_i: RecvPns::new(PacketKind::Initial),
            recv_h: RecvPns::new(PacketKind::Handshake),
            recv_1: RecvPns::new(PacketKind::OneRtt),
            sent_i: SentPackets::new(),
            sent_h: SentPackets::new(),
            sent_1: SentPackets::new(),
            live_i: true,
            live_h: true,
            complete: false,
            crx_i: CryptoStream::new(),
            crx_h: CryptoStream::new(),
            crx_1: CryptoStream::new(),
            ctx_i: SendStream::new(VARINT_MAX),
            ctx_h: SendStream::new(VARINT_MAX),
            streams: None,
            events: Vec::new(),
            local_cids: LocalCids::new(l0, token0),
            peer_cids,
            cid_updates,
            tokens_registered: Vec::new(),
            hs_done: HsDone::No,
            probe_i: false,
            probe_h: false,
            probe_1: false,
            spin: false,
            chal_used: 0,
            out_log: Ghost(Seq::empty()),
        };
        proof {
            let ghost e = c.peer_cids.entries();
            assert(e[0].1@ == first.scid@);
            let ghost ids_seq = c.paths.ids();
            assert(ids_seq.len() == 1);
            c.paths.lemma_wf();
            assert forall|q: PathId| #[trigger] c.paths.has(q) implies q == path by {
                let i = choose|i: int| 0 <= i < ids_seq.len() && ids_seq[i] == q;
                assert(i == 0);
            }
            assert(c.paths.has(path)) by {
                assert(ids_seq[0] == path);
            }
            assert(c.wf_parts()) by {
                assert(c.cid_updates@.len() == 2);
            }
            assert(c.wf_amp());
            assert(c.wf_dcids());
        }
        Some(c)
    }

    // =========================================================================
    // Receive
    // =========================================================================

    /// What every frame helper leaves alone: `recv_*` carries `gate_packet`'s duplicate check to
    /// `RecvPns::on_packet`, and is P10's frame.
    closed spec fn frames_kept(&self, o: Connection) -> bool {
        &&& self.rx_kept(o)
        &&& self.paths.ids() == o.paths.ids()
    }

    /// `frames_kept` less `paths.ids()`: also what admitting a new path leaves alone.
    closed spec fn rx_kept(&self, o: Connection) -> bool {
        &&& self.out_log@ == o.out_log@
        &&& self.recv_i == o.recv_i
        &&& self.recv_h == o.recv_h
        &&& self.recv_1 == o.recv_1
        &&& self.live_i == o.live_i
        &&& self.live_h == o.live_h
        &&& self.complete == o.complete
    }

    /// What `gate_packet` accepts. Biconditional, so what is absent is proved absent: no size rule
    /// on 1-RTT (§8.2.1's MUST NOT). An absent path has all its response room.
    closed spec fn gate_spec(&self, path: PathId, len: usize, p: &PlainPacket) -> bool {
        &&& match p.kind {
            PacketKind::Initial => len >= MIN_INITIAL_DATAGRAM && self.live_i && path == self.hs_path
                && p.scid@ == self.ids@.client_scid && (p.dcid@ == self.ids@.odcid || local_has_cid(
                self.local_cids.active_spec(),
                p.dcid@,
            )),
            PacketKind::Handshake => self.live_h && path == self.hs_path && local_has_cid(
                self.local_cids.active_spec(),
                p.dcid@,
            ),
            PacketKind::OneRtt => self.complete && local_has_cid(
                self.local_cids.active_spec(),
                p.dcid@,
            ),
        }
        &&& !self.recv(p.kind).is_duplicate_spec(p.pn)
        &&& count_ch(p.frames@) <= if self.paths.has(path) {
            MAX_RESPONSES - self.paths.path(path).responses.len()
        } else {
            MAX_RESPONSES as int
        }
    }

    /// §13.3 routing: only the matching CRYPTO send buffer and, for the stream family, `streams`
    /// change.
    closed spec fn routing_kept(&self, n: Connection, k: PacketKind, f: SpecFrame) -> bool {
        &&& !(f is Crypto && k is Initial) ==> n.ctx_i == self.ctx_i
        &&& !(f is Crypto && k is Handshake) ==> n.ctx_h == self.ctx_h
        &&& !is_stream_layer_frame(f) ==> n.streams == self.streams
    }

    /// A datagram of `datagram_len` bytes on `path`, with its decrypted packets in order.
    #[verifier::spinoff_prover]
    pub fn on_datagram(
        &mut self,
        path: PathId,
        datagram_len: usize,
        packets: Vec<PlainPacket>,
        now: u64,
        rand: &[u8; RAND_LEN],
    )
        requires
            old(self).wf(),
            forall|i: int| 0 <= i < packets@.len() ==> plain_wf(#[trigger] packets@[i]@),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
    {
        if now > self.now {
            self.now = now;
        }
        self.chal_used = 0;
        if matches!(self.lc.phase(), Phase::Draining | Phase::Closed) {
            return;
        }
        // A path is added only by a packet that passes the gate: slots never free, and a garbage or
        // replayed datagram from a spoofed address must not take one. Nothing is ever sent to an
        // absent path, so §8.1 loses nothing by not counting its datagrams.
        let mut known = self.paths.index(path).is_some();
        if known {
            // §8.1: counted even if every packet is dropped.
            self.count_recv(path, datagram_len as u64);
        }
        if matches!(self.lc.phase(), Phase::Closing) {
            // §10.2.1: packets are not processed.
            if known {
                self.lc.on_recv_closing(datagram_len as u64);
            }
            return;
        }
        if packets.len() == 0 {
            return;
        }
        // §12.2: the first packet's DCID, even if the gate drops that packet.
        let first = slice_to_vec(packets[0].dcid.as_slice());
        let now = self.now;
        for p in it: packets
            invariant
                self.wf(),
                self.out_log() == old(self).out_log(),
                known ==> self.paths.has(path),
                self.phase_spec() is Open,
                forall|j: int| 0 <= j < it.seq().len() ==> plain_wf(#[trigger] it.seq()[j]@),
        {
            proof {
                assert(it.seq()[it.index()] == p);
                assert(plain_wf(it.seq()[it.index()]@));
            }
            // §12.2: a packet with another DCID is ignored.
            if eq_bytes(p.dcid.as_slice(), first.as_slice()) && self.gate_packet(path, datagram_len, &p) {
                if !known {
                    // §9: at `MAX_PATHS` the datagram is dropped uncounted.
                    if !self.ensure_path(path) {
                        return;
                    }
                    // §8.1: the whole datagram, including packets the gate already dropped.
                    self.count_recv(path, datagram_len as u64);
                    known = true;
                }
                //= https://www.rfc-editor.org/rfc/rfc9000#section-5.2
                //# An
                //# endpoint MUST generate a connection error if processing the contents
                //# of these packets prior to discovering an error, or fully revert any
                //# changes made during that processing.
                if let Err(c) = self.on_packet(path, p, now, rand) {
                    self.close_internal(c);
                    return;
                }
                // CONNECTION_CLOSE, or a closed connection.
                if !matches!(self.lc.phase(), Phase::Open) {
                    return;
                }
            }
        }
    }

    /// `path` is known, or now added; false at `MAX_PATHS`.
    #[verifier::spinoff_prover]
    fn ensure_path(&mut self, path: PathId) -> (ok: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            final(self).phase_spec() == old(self).phase_spec(),
            final(self).rx_kept(*old(self)),
            ok ==> final(self).paths.has(path),
    {
        if self.paths.index(path).is_some() {
            return true;
        }
        let ghost s0 = *self;
        if !self.paths.insert(path) {
            return false;
        }
        proof {
            let log = self.out_log@;
            s0.paths.lemma_wf();
            self.paths.lemma_wf();
            assert forall|q: PathId| #[trigger] self.paths.has(q) implies q == path || s0.paths.has(q) by {
                let i = choose|i: int| 0 <= i < self.paths.ids().len() && self.paths.ids()[i] == q;
                if i < s0.paths.ids().len() {
                    assert(s0.paths.ids()[i] == q);
                }
            }
            assert forall|q: PathId| #[trigger] s0.paths.has(q) implies self.paths.has(q) by {
                let i = choose|i: int| 0 <= i < s0.paths.ids().len() && s0.paths.ids()[i] == q;
                assert(self.paths.ids()[i] == q);
            }
            assert forall|i: int| 0 <= i < log.len() implies (#[trigger] log[i]).path != path by {
                assert(s0.paths.index_spec(log[i].path) is Some);
            }
            lemma_log_sends_absent(log, path);
            assert(self.paths.has(path)) by {
                assert(self.paths.ids()[s0.paths.ids().len() as int] == path);
            }
            assert(self.wf_amp()) by {
                assert forall|q: PathId| #[trigger] self.paths.has(q) implies amp_ok(
                    self.paths.amp_trace(q),
                ) && sent_entries(self.paths.amp_trace(q)) == log_sends(log, q) by {
                    assert(path_ok(self.paths.path(q)));
                    if q == path {
                        assert(self.paths.amp_trace(q) == Seq::<AmpEv>::empty());
                        assert(log_sends(log, q) =~= sent_entries(self.paths.amp_trace(q)));
                    } else {
                        assert(s0.paths.has(q));
                    }
                }
            }
            assert(self.wf_log_paths()) by {
                assert forall|i: int| 0 <= i < log.len() implies #[trigger] self.paths.index_spec(
                    log[i].path,
                ) is Some by {
                    assert(s0.paths.index_spec(log[i].path) is Some);
                    assert(self.paths.has(log[i].path));
                }
            }
            assert(self.wf_dcids());
            assert(self.wf_parts()) by {
                assert(s0.paths.has(s0.hs_path));
            }
        }
        true
    }

    /// §8.1: the bytes of a datagram received on `path`.
    #[verifier::spinoff_prover]
    fn count_recv(&mut self, path: PathId, n: u64)
        requires
            old(self).wf(),
            old(self).paths.has(path),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            final(self).phase_spec() == old(self).phase_spec(),
            final(self).rx_kept(*old(self)),
            final(self).paths.has(path),
            final(self).paths.amp_trace(path) == old(self).paths.amp_trace(path).push(
                AmpEv::Recv(n as nat),
            ),
    {
        let ghost s0 = *self;
        self.paths.on_recv(path, n);
        proof {
            self.lemma_path_event(s0, path, AmpEv::Recv(n as nat));
        }
    }

    /// A Handshake packet validates the client's address (§8.1) and ends the Initial space (RFC
    /// 9001 §4.9.1).
    #[verifier::spinoff_prover]
    fn validate_hs_path(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            final(self).paths.ids() == old(self).paths.ids(),
    {
        let ghost s0 = *self;
        self.paths.set_validated(self.hs_path);
        proof {
            self.lemma_path_event(s0, s0.hs_path, AmpEv::Validated);
        }
        self.discard(PacketKind::Initial);
    }

    /// `self` is `o` with an event other than `Sent` pushed on `id`'s trace.
    proof fn lemma_path_event(&self, o: Connection, id: PathId, e: AmpEv)
        requires
            o.wf(),
            o.paths.has(id),
            !(e is Sent),
            self.paths.wf(),
            kept(o.paths, self.paths, id),
            self.paths.amp_trace(id) == o.paths.amp_trace(id).push(e),
            self.paths.path(id).dcid == o.paths.path(id).dcid,
            self.paths.path(id).peer_used == o.paths.path(id).peer_used,
            self.out_log@ == o.out_log@,
            self.peer_cids == o.peer_cids,
        ensures
            self.paths.has(id),
            self.wf_amp(),
            self.wf_log_paths(),
            self.wf_dcids(),
    {
        let t = o.paths.amp_trace(id);
        assert(t.push(e).drop_last() =~= t);
        assert(o.paths.has(id));
        self.lemma_path_edit(o, id);
        self.lemma_dcids_same(o, id);
    }

    /// `self` is `o` with path `id` edited, its sends unchanged.
    proof fn lemma_path_edit(&self, o: Connection, id: PathId)
        requires
            o.wf_amp(),
            o.wf_log_paths(),
            o.paths.wf(),
            self.paths.wf(),
            kept(o.paths, self.paths, id),
            sent_entries(self.paths.amp_trace(id)) == sent_entries(o.paths.amp_trace(id)),
            self.out_log@ == o.out_log@,
        ensures
            self.wf_amp(),
            self.wf_log_paths(),
    {
        self.paths.lemma_wf();
        assert(self.wf_amp()) by {
            assert forall|q: PathId| #[trigger] self.paths.has(q) implies amp_ok(
                self.paths.amp_trace(q),
            ) && sent_entries(self.paths.amp_trace(q)) == log_sends(self.out_log@, q) by {
                assert(path_ok(self.paths.path(q)));
                assert(o.paths.has(q));
            }
        }
        assert(self.wf_log_paths()) by {
            assert forall|i: int| 0 <= i < self.out_log@.len() implies #[trigger] self.paths.index_spec(
                self.out_log@[i].path,
            ) is Some by {
                assert(o.paths.index_spec(self.out_log@[i].path) is Some);
            }
        }
    }

    /// `self` is `o` with path `id` edited, its DCID and `peer_used` unchanged.
    proof fn lemma_dcids_same(&self, o: Connection, id: PathId)
        requires
            o.wf_dcids(),
            kept(o.paths, self.paths, id),
            self.paths.path(id).dcid == o.paths.path(id).dcid,
            self.paths.path(id).peer_used == o.paths.path(id).peer_used,
            self.peer_cids == o.peer_cids,
        ensures
            self.paths.has(id) == o.paths.has(id),
            self.wf_dcids(),
    {
        assert(self.wf_dcids()) by {
            assert forall|q: PathId| #[trigger]
                self.paths.has(q) implies (self.paths.path(q).dcid matches Some(c) ==> used_cid(
                self.peer_cids.entries(),
                c,
            )) by {
                assert(o.paths.has(q));
            }
            assert forall|q1: PathId, q2: PathId|
                #[trigger] self.paths.has(q1) && #[trigger] self.paths.has(q2) && q1 != q2
                    && self.paths.path(q1).dcid is Some && self.paths.path(q1).dcid
                    == self.paths.path(q2).dcid implies self.paths.path(q1).peer_used
                == self.paths.path(q2).peer_used by {
                assert(o.paths.has(q1));
                assert(o.paths.has(q2));
            }
            assert(o.paths.path(o.paths.active_spec()).dcid is Some);
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-10.3
    //# Endpoints MUST discard packets that are too small to be valid QUIC
    //# packets.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-8.2.1
    //# Unlike other cases where datagrams are expanded, endpoints MUST NOT
    //# discard datagrams that appear to be too small when they contain
    //# PATH_CHALLENGE or PATH_RESPONSE.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-5.1.1
    //# When an endpoint issues a connection ID, it MUST accept packets that
    //# carry this connection ID for the duration of the connection or until
    //# its peer invalidates the connection ID via a RETIRE_CONNECTION_ID
    //# frame (Section 19.16).
    //
    //= https://www.rfc-editor.org/rfc/rfc9001#section-5.7
    //# A server MUST NOT process
    //# incoming 1-RTT protected packets before the TLS handshake is
    //# complete.
    /// Whether packet `p` of a `len`-byte datagram on `path` is processed. Too small a packet is
    /// `MIN_SHORT_PACKET` (route, 3b) or a failed decryption (3e), so it never reaches this
    /// point; the only size rule here is §14.1's for Initial, so small PATH_* datagrams pass. Too
    /// many PATH_CHALLENGEs drop the whole packet unacknowledged, which the peer sees as loss
    /// (§21.9 "dropping packets", at `MAX_RESPONSES`), and no challenge is lost inside an
    /// acknowledged packet.
    #[verifier::spinoff_prover]
    fn gate_packet(&self, path: PathId, len: usize, p: &PlainPacket) -> (ok: bool)
        requires
            self.wf(),
        ensures
            ok == self.gate_spec(path, len, p),
    {
        let dcid = p.dcid.as_slice();
        let duplicate = match p.kind {
            PacketKind::Initial => {
                if len < MIN_INITIAL_DATAGRAM || !self.live_i || path != self.hs_path
                    || !self.ids.initial_scid_ok(p.scid.as_slice()) || !(eq_bytes(dcid, self.ids.odcid())
                    || self.local_cids.is_active(dcid)) {
                    return false;
                }
                self.recv_i.is_duplicate(p.pn)
            },
            PacketKind::Handshake => {
                if !self.live_h || path != self.hs_path || !self.local_cids.is_active(dcid) {
                    return false;
                }
                self.recv_h.is_duplicate(p.pn)
            },
            PacketKind::OneRtt => {
                if !self.complete || !self.local_cids.is_active(dcid) {
                    return false;
                }
                self.recv_1.is_duplicate(p.pn)
            },
        };
        let room = match self.paths.index(path) {
            Some(_) => self.paths.response_room(path),
            None => MAX_RESPONSES,
        };
        !duplicate && count_challenges(p.frames.as_slice()) <= room
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-13.1
    //# A packet MUST NOT be acknowledged until packet protection has been
    //# successfully removed and all frames contained in the packet have been
    //# processed.
    /// One packet that passed `gate_packet`. P10: the packet number is recorded, so the packet
    /// can be acknowledged, only after every frame returned `Ok`.
    #[verifier::spinoff_prover]
    fn on_packet(
        &mut self,
        path: PathId,
        p: PlainPacket,
        now: u64,
        rand: &[u8; RAND_LEN],
    ) -> (r: Result<(), u64>)
        requires
            old(self).wf(),
            old(self).phase_spec() is Open,
            old(self).paths.has(path),
            plain_wf(p@),
            !old(self).recv(p.kind).is_duplicate_spec(p.pn),
            p.kind is OneRtt ==> old(self).complete,
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            final(self).paths.has(path),
            r matches Err(c) ==> c <= VARINT_MAX,
            r is Err ==> final(self).recv(p.kind).seen() == old(self).recv(p.kind).seen(),
    {
        let k = p.kind;
        let pn = p.pn;
        let dcid = p.dcid;
        let frames = p.frames;
        let eliciting = is_ack_eliciting(frames.as_slice());
        let non_probing = has_non_probing(frames.as_slice());
        let f = self.on_frames(k, path, dcid.as_slice(), frames, now, rand);
        if f.is_err() {
            return f;
        }
        if !matches!(self.lc.phase(), Phase::Open) {
            return Ok(());
        }
        match k {
            PacketKind::Initial => self.recv_i.on_packet(pn, eliciting, now),
            PacketKind::Handshake => self.recv_h.on_packet(pn, eliciting, now),
            PacketKind::OneRtt => self.recv_1.on_packet(pn, eliciting, now),
        }
        self.idle.on_packet_processed(now);
        self.note_peer_used(path, dcid.as_slice());
        match k {
            PacketKind::Handshake => {
                if !matches!(self.paths.state(self.hs_path), PathState::Validated) {
                    self.validate_hs_path();
                }
            },
            PacketKind::OneRtt => {
                self.after_one_rtt(path, non_probing, pn, now, rand);
            },
            PacketKind::Initial => {},
        }
        Ok(())
    }

    /// The frames of one packet, stopping at the first error or once no longer Open: in `[CC,
    /// Stream]`, `streams` is None by the second frame.
    #[verifier::spinoff_prover]
    fn on_frames(
        &mut self,
        k: PacketKind,
        path: PathId,
        dcid: &[u8],
        frames: Vec<Frame>,
        now: u64,
        rand: &[u8; RAND_LEN],
    ) -> (r: Result<(), u64>)
        requires
            old(self).wf(),
            old(self).phase_spec() is Open,
            old(self).paths.has(path),
            frames_received(frames_view(frames@), k),
            dcid@.len() <= MAX_CID_LEN,
            k is OneRtt ==> old(self).complete,
        ensures
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            r matches Err(c) ==> c <= VARINT_MAX,
    {
        let ghost fs = frames@;
        for f in it: frames
            invariant
                self.wf(),
                self.frames_kept(*old(self)),
                self.phase_spec() is Open,
                self.paths.has(path),
                it.seq() == fs,
                frames_received(frames_view(fs), k),
                dcid@.len() <= MAX_CID_LEN,
                k is OneRtt ==> self.complete,
        {
            proof {
                let i = it.index();
                assert(fs[i] == f);
                assert(frames_view(fs)[i] == f@);
            }
            let r = self.on_frame(k, path, dcid, &f, now, rand);
            if r.is_err() {
                return r;
            }
            if !matches!(self.lc.phase(), Phase::Open) {
                return Ok(());
            }
        }
        Ok(())
    }

    /// Dispatches one frame.
    #[verifier::spinoff_prover]
    fn on_frame(
        &mut self,
        k: PacketKind,
        path: PathId,
        dcid: &[u8],
        f: &Frame,
        now: u64,
        rand: &[u8; RAND_LEN],
    ) -> (r: Result<(), u64>)
        requires
            old(self).wf(),
            old(self).phase_spec() is Open,
            old(self).paths.has(path),
            frame_wf(f@),
            frame_permitted(spec_frame_type(f@), k),
            !(f@ is HandshakeDone),
            dcid@.len() <= MAX_CID_LEN,
            k is OneRtt ==> old(self).complete,
        ensures
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            r matches Err(c) ==> c <= VARINT_MAX,
    {
        // The stream family reaches only 1-RTT, so `wf`'s `complete` clause gives `streams`.
        proof {
            if is_stream_layer_frame(f@) {
                if let SpecFrame::Stream { offset, fin, .. } = f@ {
                    lemma_stream_type_bits(if offset > 0 { 4 } else { 0 }, if fin { 1 } else { 0 });
                }
                assert(k is OneRtt);
            }
        }
        match f {
            Frame::Padding | Frame::Ping => Ok(()),
            // `frames_received` excludes it.
            Frame::HandshakeDone => {
                proof {
                    assert(false);
                }
                Ok(())
            },
            Frame::Ack(a) => self.on_ack_frame(k, a, now),
            Frame::Crypto { offset, data } => self.on_crypto_frame(k, *offset, data.as_slice()),
            Frame::ConnectionClose { .. } => {
                let pto = self.pto();
                self.lc.enter_draining(now, pto);
                self.streams = None;
                Ok(())
            },
            Frame::ResetStream { .. }
            | Frame::StopSending { .. }
            | Frame::Stream { .. }
            | Frame::MaxData(_)
            | Frame::MaxStreamData { .. }
            | Frame::MaxStreams { .. }
            | Frame::DataBlocked(_)
            | Frame::StreamDataBlocked { .. }
            | Frame::StreamsBlocked { .. } => self.on_stream_frame(f, now),
            Frame::NewConnectionId { .. } | Frame::RetireConnectionId(_) => self.on_cid_frame(
                dcid,
                f,
                rand,
            ),
            Frame::PathChallenge(_) | Frame::PathResponse(_) => self.on_path_frame(path, f, now, rand),
        }
    }

    /// An ACK frame: drops the records it acknowledges and routes their frames (§13.3).
    #[verifier::spinoff_prover]
    fn on_ack_frame(&mut self, k: PacketKind, a: &AckFrame, now: u64) -> (r: Result<(), u64>)
        requires
            old(self).wf(),
            rfc_ack_ranges_valid(a.largest, a.first_range, a.ranges@),
        ensures
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            r matches Err(c) ==> c <= VARINT_MAX,
    {
        let mut acked: Vec<SentPacket> = Vec::new();
        proof {
            lemma_unacked_len(a@, self.sent_i.inflight_spec());
            lemma_unacked_len(a@, self.sent_h.inflight_spec());
            lemma_unacked_len(a@, self.sent_1.inflight_spec());
        }
        let r = match k {
            PacketKind::Initial => self.sent_i.on_ack(a, &mut acked),
            PacketKind::Handshake => self.sent_h.on_ack(a, &mut acked),
            PacketKind::OneRtt => self.sent_1.on_ack(a, &mut acked),
        };
        if r.is_err() {
            return r;
        }
        self.recovery.on_ack_received(k, acked.len(), a.delay, now);
        let mut i: usize = 0;
        while i < acked.len()
            invariant
                i <= acked@.len(),
                self.wf(),
                self.frames_kept(*old(self)),
            decreases acked@.len() - i,
        {
            self.on_acked_record(k, acked[i].frames.as_slice());
            i += 1;
        }
        Ok(())
    }

    // ponytail: per incoming ACK at most 64 records × distinct stream runs per record × O(R) range work (R ≈ 2·64 + ~1000, 3d D4); coalescing turns a 200-frame single-stream record into one call. Cap STREAM frames per stream per packet if a split adversary still makes this hot.
    /// The frames of one acknowledged record, each run of adjacent STREAM frames in one call.
    #[verifier::spinoff_prover]
    fn on_acked_record(&mut self, k: PacketKind, frames: &[Frame])
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).frames_kept(*old(self)),
    {
        let mut j: usize = 0;
        while j < frames.len()
            invariant
                j <= frames@.len(),
                self.wf(),
                self.frames_kept(*old(self)),
            decreases frames@.len() - j,
        {
            match stream_run(frames, j) {
                Some((run, e)) => {
                    self.on_acked_frame(k, &run);
                    j = e;
                },
                None => {
                    self.on_acked_frame(k, &frames[j]);
                    j += 1;
                },
            }
        }
    }

    // ponytail: post-handshake CRYPTO (NewSessionTicket) is buffered and ignored; we send none.
    /// A CRYPTO frame.
    #[verifier::spinoff_prover]
    fn on_crypto_frame(&mut self, k: PacketKind, offset: u64, data: &[u8]) -> (r: Result<(), u64>)
        requires
            old(self).wf(),
            offset + data@.len() <= VARINT_MAX,
        ensures
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            r matches Err(c) ==> c <= VARINT_MAX,
    {
        match k {
            PacketKind::Initial => self.crx_i.on_crypto(offset, data),
            PacketKind::Handshake => self.crx_h.on_crypto(offset, data),
            PacketKind::OneRtt => self.crx_1.on_crypto(offset, data),
        }
    }

    /// One of the nine stream-layer frames. On `Err` the connection is already Closing with
    /// `streams` None and that code: `Streams::on_frame`'s `Err` sets `failed()`, which `wf`
    /// excludes, so `wf` could not otherwise hold on return. `on_datagram`'s `close_internal` is
    /// then a no-op.
    #[verifier::spinoff_prover]
    fn on_stream_frame(&mut self, f: &Frame, now: u64) -> (r: Result<(), u64>)
        requires
            old(self).wf(),
            old(self).phase_spec() is Open,
            old(self).streams is Some,
            frame_wf(f@),
            is_stream_layer_frame(f@),
        ensures
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            r matches Err(c) ==> c <= VARINT_MAX,
            r is Err ==> !(final(self).phase_spec() is Open) && final(self).streams is None,
    {
        // Before `Streams::on_frame`: after its `Err`, `wf` no longer holds.
        let pto = self.pto();
        let ghost s0 = self.streams->0;
        let r = match &mut self.streams {
            Some(s) => s.on_frame(f, &mut self.events),
            None => Ok(()),
        };
        if let Err(c) = r {
            proof {
                lemma_frame_err(s0, f@, r);
            }
            let none: Vec<u8> = Vec::new();
            self.lc.enter_closing(now, pto, false, c, none.as_slice());
            self.streams = None;
            return Err(c);
        }
        Ok(())
    }

    /// NEW_CONNECTION_ID or RETIRE_CONNECTION_ID, in a packet with this DCID.
    #[verifier::spinoff_prover]
    fn on_cid_frame(&mut self, dcid: &[u8], f: &Frame, rand: &[u8; RAND_LEN]) -> (r: Result<(), u64>)
        requires
            old(self).wf(),
            frame_wf(f@),
            f@ is NewConnectionId || f@ is RetireConnectionId,
            dcid@.len() <= MAX_CID_LEN,
        ensures
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            r matches Err(c) ==> c <= VARINT_MAX,
    {
        match f {
            Frame::NewConnectionId { seq, retire_prior_to, cid, reset_token } => {
                let ghost s0 = *self;
                let limit = self.local_tp.active_connection_id_limit;
                let r = self.peer_cids.on_new_cid(
                    *seq,
                    *retire_prior_to,
                    cid.as_slice(),
                    *reset_token,
                    limit,
                );
                if let Err(c) = r {
                    return Err(c);
                }
                proof {
                    self.lemma_after_new_cid(s0);
                }
                self.rewrite_stale(rand);
                Ok(())
            },
            Frame::RetireConnectionId(s) => match self.local_cids.on_retire(*s, dcid) {
                Err(c) => Err(c),
                Ok(None) => Ok(()),
                Ok(Some(c)) => {
                    self.cid_updates.push(CidUpdate::Remove(slice_to_vec(c.as_slice())));
                    proof {
                        assert(cids_only(self.cid_updates@));
                    }
                    // §5.1.1 SHOULD replace.
                    self.issue_cids(rand);
                    Ok(())
                },
            },
            _ => Ok(()),
        }
    }

    /// `self` is `o` with `on_new_cid` applied: only stale paths can break `wf_dcids`.
    proof fn lemma_after_new_cid(&self, o: Connection)
        requires
            o.wf(),
            self.peer_cids.wf(),
            entries_survive(o.peer_cids.entries(), self.peer_cids.entries()),
            self.paths == o.paths,
            self.out_log@ == o.out_log@,
            self.wf_parts(),
            self.wf_streams(),
            self.wf_pn(),
        ensures
            self.wf_rest(),
            self.dcids_weak(),
    {
        let e0 = o.peer_cids.entries();
        let e1 = self.peer_cids.entries();
        assert forall|q: PathId, i: int|
            #[trigger] self.paths.has(q) && 0 <= i < e1.len() && !(#[trigger] e1[i]).3 implies self.paths.path(q).dcid
            != Some(e1[i].1@) by {
            if self.paths.path(q).dcid == Some(e1[i].1@) {
                assert(o.paths.has(q));
                let k = choose|k: int| 0 <= k < e0.len() && (#[trigger] e0[k]).1@ == e1[i].1@ && e0[k].3;
                assert(e0[k].1@ == e1[i].1@ ==> e0[k].0 == e1[i].0);
            }
        }
        assert forall|q1: PathId, q2: PathId| #[trigger] self.paths.has(q1) && #[trigger] self.paths.has(q2) implies self.pair_ok(q1, q2) by {
            if q1 != q2 {
                assert(o.paths.has(q1));
                assert(o.paths.has(q2));
            }
        }
        assert(o.paths.path(o.paths.active_spec()).dcid is Some);
    }

    // =========================================================================
    // The peer's connection IDs on the paths (§9.5)
    // =========================================================================

    /// `wf` without `wf_dcids`.
    closed spec fn wf_rest(&self) -> bool {
        &&& self.wf_parts()
        &&& self.wf_streams()
        &&& self.wf_amp()
        &&& self.wf_pn()
        &&& self.wf_log_paths()
    }

    /// No path holds an unused peer CID, so `use_next()` gives a path a CID of its own. It holds
    /// while a path still holds a retired CID, when `wf_dcids` does not.
    closed spec fn unused_unheld(&self) -> bool {
        forall|q: PathId, i: int|
            #[trigger] self.paths.has(q) && 0 <= i < self.peer_cids.entries().len()
                && !(#[trigger] self.peer_cids.entries()[i]).3 ==> self.paths.path(q).dcid != Some(
                self.peer_cids.entries()[i].1@,
            )
    }

    /// §9.5 for two paths.
    closed spec fn pair_ok(&self, q1: PathId, q2: PathId) -> bool {
        self.paths.path(q1).dcid is Some && self.paths.path(q1).dcid == self.paths.path(q2).dcid
            ==> self.paths.path(q1).peer_used == self.paths.path(q2).peer_used
    }

    closed spec fn pairs_except(&self, x: PathId) -> bool {
        forall|q1: PathId, q2: PathId|
            #[trigger] self.paths.has(q1) && #[trigger] self.paths.has(q2) && q1 != x && q2 != x
                ==> self.pair_ok(q1, q2)
    }

    /// `wf_dcids` but for "every DCID is active".
    closed spec fn dcids_weak(&self) -> bool {
        &&& self.paths.path(self.paths.active_spec()).dcid is Some
        &&& self.unused_unheld()
        &&& forall|q1: PathId, q2: PathId|
            #[trigger] self.paths.has(q1) && #[trigger] self.paths.has(q2) ==> self.pair_ok(q1, q2)
    }

    /// `q` holds no retired CID.
    closed spec fn not_stale(&self, q: PathId) -> bool {
        self.paths.path(q).dcid matches Some(c) ==> peer_has_cid(self.peer_cids.entries(), c)
    }

    proof fn lemma_weak_of_wf(&self)
        requires
            self.wf(),
        ensures
            self.dcids_weak(),
            forall|q: PathId| #[trigger] self.paths.has(q) ==> self.not_stale(q),
    {
        let e = self.peer_cids.entries();
        assert forall|q: PathId, i: int|
            #[trigger] self.paths.has(q) && 0 <= i < e.len() && !(#[trigger] e[i]).3 implies self.paths.path(q).dcid
            != Some(e[i].1@) by {
            self.lemma_unused_cid_unheld(i, q);
        }
        assert forall|q1: PathId, q2: PathId| #[trigger] self.paths.has(q1) && #[trigger] self.paths.has(q2) implies self.pair_ok(q1, q2) by {}
        assert forall|q: PathId| #[trigger] self.paths.has(q) implies self.not_stale(q) by {
            if let Some(c) = self.paths.path(q).dcid {
                let i = choose|i: int| 0 <= i < e.len() && (#[trigger] e[i]).1@ == c && e[i].3;
                assert(e[i].1@ == c);
            }
        }
    }

    proof fn lemma_wf_of_weak(&self)
        requires
            self.dcids_weak(),
            forall|q: PathId| #[trigger] self.paths.has(q) ==> self.not_stale(q),
        ensures
            self.wf_dcids(),
    {
        let e = self.peer_cids.entries();
        assert forall|q: PathId| #[trigger] self.paths.has(q) implies (self.paths.path(q).dcid matches Some(c)
            ==> used_cid(e, c)) by {
            if let Some(c) = self.paths.path(q).dcid {
                assert(self.not_stale(q));
                let i = choose|i: int| 0 <= i < e.len() && (#[trigger] e[i]).1@ == c;
                assert(e[i].3);
            }
        }
        assert forall|q1: PathId, q2: PathId|
            #[trigger] self.paths.has(q1) && #[trigger] self.paths.has(q2) && q1 != q2
                && self.paths.path(q1).dcid is Some && self.paths.path(q1).dcid == self.paths.path(
                q2,
            ).dcid implies self.paths.path(q1).peer_used == self.paths.path(q2).peer_used by {
            assert(self.pair_ok(q1, q2));
        }
    }

    /// One edit of path `q`'s DCID keeps `unused_unheld`, if the new DCID is not an unused CID.
    proof fn lemma_unheld_edit(&self, o: Connection, q: PathId)
        requires
            o.unused_unheld(),
            kept(o.paths, self.paths, q),
            self.peer_cids == o.peer_cids,
            forall|i: int|
                0 <= i < self.peer_cids.entries().len() && !(#[trigger] self.peer_cids.entries()[i]).3
                    ==> self.paths.path(q).dcid != Some(self.peer_cids.entries()[i].1@),
        ensures
            self.unused_unheld(),
    {
        let e = self.peer_cids.entries();
        assert forall|r: PathId, i: int|
            #[trigger] self.paths.has(r) && 0 <= i < e.len() && !(#[trigger] e[i]).3 implies self.paths.path(r).dcid
            != Some(e[i].1@) by {
            if r != q {
                assert(o.paths.has(r));
            }
        }
    }

    /// `Paths::set_dcid`, keeping everything but `wf_dcids`.
    #[verifier::spinoff_prover]
    fn put_dcid(&mut self, q: PathId, d: Option<&[u8]>)
        requires
            old(self).wf_rest(),
            old(self).paths.has(q),
            d matches Some(c) ==> c@.len() <= MAX_CID_LEN,
        ensures
            final(self).wf_rest(),
            final(self).frames_kept(*old(self)),
            final(self).peer_cids == old(self).peer_cids,
            kept(old(self).paths, final(self).paths, q),
            final(self).paths.path(q) == (SpecPath {
                dcid: opt_slice_view(d),
                ..old(self).paths.path(q)
            }),
    {
        let ghost s0 = *self;
        self.paths.set_dcid(q, d);
        proof {
            self.lemma_path_edit(s0, q);
        }
    }

    /// §9.5: `q` takes `d`, which is no unused CID, and which any other path holds only if the peer
    /// used one CID on both (its MAY: the peer used the same CID from a new address).
    #[verifier::spinoff_prover]
    fn hold_dcid(&mut self, q: PathId, d: Option<&[u8]>)
        requires
            old(self).wf_rest(),
            old(self).dcids_weak(),
            old(self).paths.has(q),
            q == old(self).paths.active_spec() ==> d is Some,
            d matches Some(c) ==> {
                &&& c@.len() <= MAX_CID_LEN
                &&& forall|i: int|
                    0 <= i < old(self).peer_cids.entries().len() && !(
                    #[trigger] old(self).peer_cids.entries()[i]).3 ==> old(
                        self,
                    ).peer_cids.entries()[i].1@ != c@
                &&& forall|r: PathId|
                    #[trigger] old(self).paths.has(r) && r != q && old(self).paths.path(r).dcid == Some(
                        c@,
                    ) ==> old(self).paths.path(r).peer_used == old(self).paths.path(q).peer_used
            },
        ensures
            final(self).wf_rest(),
            final(self).dcids_weak(),
            final(self).frames_kept(*old(self)),
            final(self).peer_cids == old(self).peer_cids,
            kept(old(self).paths, final(self).paths, q),
            final(self).paths.path(q).dcid == opt_slice_view(d),
    {
        let ghost s0 = *self;
        self.put_dcid(q, d);
        proof {
            self.lemma_unheld_edit(s0, q);
            assert forall|q1: PathId, q2: PathId| #[trigger] self.paths.has(q1) && #[trigger] self.paths.has(q2) implies self.pair_ok(q1, q2) by {
                assert(s0.paths.has(q1));
                assert(s0.paths.has(q2));
                assert(s0.pair_ok(q1, q2));
            }
        }
    }

    /// `self` is `o` with `use_next`'s mark on `c`: no path holds `c`, and CIDs stay active.
    proof fn lemma_marked(&self, o: Connection, c: Seq<u8>)
        requires
            o.peer_cids.wf(),
            self.peer_cids.wf(),
            o.unused_unheld(),
            self.paths == o.paths,
            exists|i: int|
                0 <= i < o.peer_cids.entries().len() && !(#[trigger] o.peer_cids.entries()[i]).3 && c
                    == o.peer_cids.entries()[i].1@ && self.peer_cids.entries() == o.peer_cids.entries().update(
                    i,
                    (
                        o.peer_cids.entries()[i].0,
                        o.peer_cids.entries()[i].1,
                        o.peer_cids.entries()[i].2,
                        true,
                    ),
                ),
        ensures
            self.unused_unheld(),
            c.len() <= MAX_CID_LEN,
            forall|r: PathId| #[trigger] o.paths.has(r) ==> o.paths.path(r).dcid != Some(c),
            forall|i: int|
                0 <= i < self.peer_cids.entries().len() && !(#[trigger] self.peer_cids.entries()[i]).3
                    ==> self.peer_cids.entries()[i].1@ != c,
            forall|x: Seq<u8>| #[trigger]
                peer_has_cid(self.peer_cids.entries(), x) == peer_has_cid(o.peer_cids.entries(), x),
    {
        let e0 = o.peer_cids.entries();
        let e1 = self.peer_cids.entries();
        let w = choose|w: int|
            0 <= w < e0.len() && !(#[trigger] e0[w]).3 && c == e0[w].1@ && e1 == e0.update(
                w,
                (e0[w].0, e0[w].1, e0[w].2, true),
            );
        o.peer_cids.lemma_wf();
        assert(e0[w].1@.len() <= MAX_CID_LEN);
        assert forall|r: PathId| #[trigger] o.paths.has(r) implies o.paths.path(r).dcid != Some(c) by {
            assert(!e0[w].3);
        }
        assert forall|q: PathId, i: int|
            #[trigger] self.paths.has(q) && 0 <= i < e1.len() && !(#[trigger] e1[i]).3 implies self.paths.path(q).dcid
            != Some(e1[i].1@) by {
            assert(i != w);
            assert(e1[i] == e0[i]);
            assert(!e0[i].3);
        }
        assert forall|i: int| 0 <= i < e1.len() && !(#[trigger] e1[i]).3 implies e1[i].1@ != c by {
            assert(i != w);
            assert(e1[i] == e0[i]);
            if i < w {
                assert(e0[i].1@ != e0[w].1@);
            } else {
                assert(e0[w].1@ != e0[i].1@);
            }
        }
        assert forall|x: Seq<u8>| #[trigger] peer_has_cid(e1, x) == peer_has_cid(e0, x) by {
            if peer_has_cid(e1, x) {
                let i = choose|i: int| 0 <= i < e1.len() && (#[trigger] e1[i]).1@ == x;
                assert(e0[i].1@ == x);
            }
            if peer_has_cid(e0, x) {
                let i = choose|i: int| 0 <= i < e0.len() && (#[trigger] e0[i]).1@ == x;
                assert(e1[i].1@ == x);
            }
        }
    }

    /// `q` takes an unused CID, its own; false, with nothing changed, if there is none.
    #[verifier::spinoff_prover]
    fn fresh_dcid(&mut self, q: PathId) -> (r: bool)
        requires
            old(self).wf_rest(),
            old(self).dcids_weak(),
            old(self).paths.has(q),
        ensures
            final(self).wf_rest(),
            final(self).dcids_weak(),
            final(self).frames_kept(*old(self)),
            kept(old(self).paths, final(self).paths, q),
            forall|x: Seq<u8>| #[trigger]
                peer_has_cid(final(self).peer_cids.entries(), x) == peer_has_cid(
                    old(self).peer_cids.entries(),
                    x,
                ),
            r ==> final(self).not_stale(q) && final(self).paths.path(q).dcid is Some,
            !r ==> final(self).paths == old(self).paths && final(self).peer_cids == old(self).peer_cids,
    {
        let ghost s0 = *self;
        match self.peer_cids.use_next() {
            None => false,
            Some(c) => {
                proof {
                    self.lemma_marked(s0, c@);
                }
                self.hold_dcid(q, Some(c.as_slice()));
                true
            },
        }
    }

    // ponytail: one spin bit per connection, so a redraw for a new path's CID also flips the active path's bit (§17.4 is RECOMMENDED); per-path spin if spin-bit observers ever matter.
    //= https://www.rfc-editor.org/rfc/rfc9000#section-9.5
    //# Similarly, an endpoint MUST NOT reuse a connection ID when sending to
    //# more than one destination address.
    /// Gives `q`, if it has none, the active path's DCID if the peer used one CID on both (§9.5
    /// MAY, NAT rebinding), else an unused CID. With neither it stays None: nothing is sent to `q`.
    #[verifier::spinoff_prover]
    fn assign_dcid(&mut self, q: PathId, rand: &[u8; RAND_LEN])
        requires
            old(self).wf(),
            old(self).paths.has(q),
        ensures
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            final(self).paths.active_spec() == old(self).paths.active_spec(),
    {
        if self.paths.dcid(q).is_some() {
            return;
        }
        let ghost s0 = *self;
        proof {
            s0.lemma_weak_of_wf();
            s0.paths.lemma_wf();
        }
        let a = self.paths.active();
        if opt_eq(self.paths.peer_used(q), self.paths.peer_used(a)) {
            let d = self.active_dcid(a);
            self.hold_dcid(q, Some(d.as_slice()));
            proof {
                assert(s0.not_stale(a));
            }
        } else if self.fresh_dcid(q) {
            self.spin = rand[128] & 1 == 1;
        }
        proof {
            assert forall|r: PathId| #[trigger] self.paths.has(r) implies self.not_stale(r) by {
                assert(s0.paths.has(r));
                assert(s0.not_stale(r));
            }
            self.lemma_wf_of_weak();
        }
    }

    /// A copy of the DCID of the active path `a`, to hand to another path: no unused CID, and
    /// §9.5's pair rule makes every holder agree with `a`.
    #[verifier::spinoff_prover]
    fn active_dcid(&self, a: PathId) -> (d: Vec<u8>)
        requires
            self.wf_rest(),
            self.dcids_weak(),
            a == self.paths.active_spec(),
        ensures
            self.paths.path(a).dcid == Some(d@),
            d@.len() <= MAX_CID_LEN,
            forall|i: int|
                0 <= i < self.peer_cids.entries().len() && !(#[trigger] self.peer_cids.entries()[i]).3
                    ==> self.peer_cids.entries()[i].1@ != d@,
            forall|r: PathId|
                #[trigger] self.paths.has(r) && self.paths.path(r).dcid == Some(d@)
                    ==> self.paths.path(r).peer_used == self.paths.path(a).peer_used,
    {
        proof {
            self.paths.lemma_wf();
        }
        let d = match self.paths.dcid(a) {
            Some(x) => slice_to_vec(x),
            None => Vec::new(),
        };
        proof {
            assert(path_ok(self.paths.path(a)));
            assert forall|r: PathId| #[trigger]
                self.paths.has(r) && self.paths.path(r).dcid == Some(d@) implies self.paths.path(r).peer_used
                == self.paths.path(a).peer_used by {
                assert(self.pair_ok(r, a));
            }
        }
        d
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-9.5
    //# Similarly, an endpoint MUST NOT reuse a connection ID when sending to
    //# more than one destination address.
    /// Only pairs with `path` can break §9.5; each is split by clearing its non-active member,
    /// which `assign_dcid` re-assigns later. At most `MAX_PATHS` steps.
    #[verifier::spinoff_prover]
    fn repair_pairs(&mut self, path: PathId)
        requires
            old(self).wf_rest(),
            old(self).paths.path(old(self).paths.active_spec()).dcid is Some,
            old(self).unused_unheld(),
            old(self).pairs_except(path),
            old(self).paths.has(path),
        ensures
            final(self).wf_rest(),
            final(self).dcids_weak(),
            final(self).frames_kept(*old(self)),
            final(self).peer_cids == old(self).peer_cids,
            final(self).paths.active_spec() == old(self).paths.active_spec(),
            path == old(self).paths.active_spec() ==> final(self).paths.path(path).dcid == old(
                self,
            ).paths.path(path).dcid,
            forall|q: PathId| #[trigger]
                old(self).not_stale(q) && old(self).paths.has(q) ==> final(self).not_stale(q),
    {
        let n = self.paths.len();
        let ghost ids = self.paths.ids();
        let mut i: usize = 0;
        while i < n
            invariant
                n == ids.len(),
                i <= n,
                self.wf_rest(),
                self.paths.ids() == ids,
                self.paths.has(path),
                self.frames_kept(*old(self)),
                self.peer_cids == old(self).peer_cids,
                self.paths.active_spec() == old(self).paths.active_spec(),
                self.paths.path(self.paths.active_spec()).dcid is Some,
                self.unused_unheld(),
                self.pairs_except(path),
                path == self.paths.active_spec() ==> self.paths.path(path).dcid == old(
                    self,
                ).paths.path(path).dcid,
                forall|k: int| 0 <= k < i ==> self.pair_ok(#[trigger] ids[k], path),
                forall|q: PathId| #[trigger]
                    old(self).not_stale(q) && old(self).paths.has(q) ==> self.not_stale(q),
            decreases n - i,
        {
            let q = self.path_at(i);
            if self.pair_conflict(q, path) {
                self.split_pair(q, path, Ghost(i as int));
            }
            i += 1;
        }
        proof {
            assert forall|q1: PathId, q2: PathId| #[trigger] self.paths.has(q1) && #[trigger] self.paths.has(q2) implies self.pair_ok(q1, q2) by {
                if q1 == path && q2 != path {
                    let k = choose|k: int| 0 <= k < ids.len() && ids[k] == q2;
                    assert(self.pair_ok(ids[k], path));
                } else if q2 == path && q1 != path {
                    let k = choose|k: int| 0 <= k < ids.len() && ids[k] == q1;
                    assert(self.pair_ok(ids[k], path));
                }
            }
        }
    }

    /// One step of `repair_pairs`: the conflict between `q` and `path` goes, by clearing the
    /// non-active member.
    #[verifier::spinoff_prover]
    fn split_pair(&mut self, q: PathId, path: PathId, Ghost(i): Ghost<int>)
        requires
            old(self).wf_rest(),
            old(self).paths.has(q),
            old(self).paths.has(path),
            old(self).paths.path(old(self).paths.active_spec()).dcid is Some,
            old(self).unused_unheld(),
            old(self).pairs_except(path),
            !old(self).pair_ok(q, path),
            old(self).paths.ids()[i] == q,
            0 <= i < old(self).paths.ids().len(),
        ensures
            final(self).wf_rest(),
            final(self).frames_kept(*old(self)),
            final(self).peer_cids == old(self).peer_cids,
            final(self).paths.active_spec() == old(self).paths.active_spec(),
            final(self).paths.path(final(self).paths.active_spec()).dcid is Some,
            final(self).unused_unheld(),
            final(self).pairs_except(path),
            final(self).pair_ok(q, path),
            path == old(self).paths.active_spec() ==> final(self).paths.path(path).dcid == old(
                self,
            ).paths.path(path).dcid,
            forall|r: PathId| #[trigger]
                old(self).pair_ok(r, path) ==> final(self).pair_ok(r, path),
            forall|r: PathId| #[trigger]
                old(self).not_stale(r) ==> final(self).not_stale(r),
    {
        let ghost s0 = *self;
        let x = if path == self.paths.active() {
            q
        } else {
            path
        };
        self.put_dcid(x, None);
        proof {
            self.lemma_unheld_edit(s0, x);
            assert forall|q1: PathId, q2: PathId|
                #[trigger] self.paths.has(q1) && #[trigger] self.paths.has(q2) && q1 != path && q2 != path implies self.pair_ok(q1, q2) by {
                assert(s0.paths.has(q1));
                assert(s0.paths.has(q2));
                assert(s0.pair_ok(q1, q2));
            }
        }
    }

    /// Entry `i` of the path table.
    fn path_at(&self, i: usize) -> (q: PathId)
        requires
            i < self.paths.ids().len(),
        ensures
            q == self.paths.ids()[i as int],
            self.paths.has(q),
    {
        let q = self.paths.id_at(i);
        proof {
            assert(self.paths.ids()[i as int] == q);
        }
        q
    }

    /// `q1` and `q2` share a DCID though the peer used different CIDs on them.
    #[verifier::spinoff_prover]
    fn pair_conflict(&self, q1: PathId, q2: PathId) -> (r: bool)
        requires
            self.paths.wf(),
            self.paths.has(q1),
            self.paths.has(q2),
        ensures
            r == !self.pair_ok(q1, q2),
    {
        self.paths.dcid(q1).is_some() && opt_eq(self.paths.dcid(q1), self.paths.dcid(q2)) && !opt_eq(
            self.paths.peer_used(q1),
            self.paths.peer_used(q2),
        )
    }

    /// Whether `q` holds a retired CID.
    #[verifier::spinoff_prover]
    fn is_stale(&self, q: PathId) -> (r: bool)
        requires
            self.paths.wf(),
            self.paths.has(q),
        ensures
            r == !self.not_stale(q),
    {
        match self.paths.dcid(q) {
            Some(c) => !self.peer_cids.is_active(c),
            None => false,
        }
    }

    /// §9.5: the peer used `path`'s DCID `dcid` on this packet: records it, and splits any pair it
    /// breaks (the peer rotating CIDs on one member of a NAT-rebinding pair).
    #[verifier::spinoff_prover]
    fn note_peer_used(&mut self, path: PathId, dcid: &[u8])
        requires
            old(self).wf(),
            old(self).paths.has(path),
            dcid@.len() <= MAX_CID_LEN,
        ensures
            final(self).wf(),
            final(self).frames_kept(*old(self)),
    {
        let ghost s0 = *self;
        proof {
            s0.lemma_weak_of_wf();
        }
        self.paths.set_peer_used(path, dcid);
        proof {
            self.lemma_path_edit(s0, path);
            self.lemma_unheld_edit(s0, path);
            assert forall|q1: PathId, q2: PathId|
                #[trigger] self.paths.has(q1) && #[trigger] self.paths.has(q2) && q1 != path && q2 != path implies self.pair_ok(q1, q2) by {
                assert(s0.paths.has(q1));
                assert(s0.paths.has(q2));
                assert(s0.pair_ok(q1, q2));
            }
            assert forall|q: PathId| #[trigger] s0.paths.has(q) implies self.not_stale(q) by {
                assert(s0.not_stale(q));
            }
        }
        self.repair_pairs(path);
        proof {
            assert forall|q: PathId| #[trigger] self.paths.has(q) implies self.not_stale(q) by {
                assert(s0.paths.has(q));
                assert(s0.not_stale(q));
            }
            self.lemma_wf_of_weak();
        }
    }

    /// Some path other than `a` holds `cur` under another peer CID than `a` does.
    #[verifier::spinoff_prover]
    fn cur_taken(&self, a: PathId, cur: &[u8]) -> (r: bool)
        requires
            self.paths.wf(),
            self.paths.has(a),
    {
        let n = self.paths.len();
        let mut i: usize = 0;
        while i < n
            invariant
                self.paths.wf(),
                self.paths.has(a),
                n == self.paths.ids().len(),
                i <= n,
            decreases n - i,
        {
            let q = self.path_at(i);
            if q != a && opt_eq(self.paths.dcid(q), Some(cur)) && !opt_eq(
                self.paths.peer_used(q),
                self.paths.peer_used(a),
            ) {
                return true;
            }
            i += 1;
        }
        false
    }

    /// The active path holds a retired CID: it takes `current()` unless another path holds that
    /// under another peer CID; then an unused CID, or with none `current()` anyway, and whichever
    /// paths hold it under another peer CID lose it.
    #[verifier::spinoff_prover]
    fn rewrite_active(&mut self, a: PathId)
        requires
            old(self).wf_rest(),
            old(self).dcids_weak(),
            a == old(self).paths.active_spec(),
        ensures
            final(self).wf_rest(),
            final(self).dcids_weak(),
            final(self).frames_kept(*old(self)),
            final(self).paths.active_spec() == a,
            final(self).not_stale(a),
    {
        proof {
            self.paths.lemma_wf();
            self.peer_cids.lemma_wf();
        }
        let cur = slice_to_vec(self.peer_cids.current());
        if self.cur_taken(a, cur.as_slice()) && self.fresh_dcid(a) {
            return;
        }
        let ghost s0 = *self;
        proof {
            let e = self.peer_cids.entries();
            let w = choose|w: int|
                0 <= w < e.len() && (#[trigger] e[w]).0 == self.peer_cids.current_spec() && e[w].3
                    && cur@ == e[w].1@;
            assert(cur@.len() <= MAX_CID_LEN);
            assert forall|i: int| 0 <= i < e.len() && !(#[trigger] e[i]).3 implies e[i].1@ != cur@ by {
                if i < w {
                    assert(e[i].1@ != e[w].1@);
                } else if w < i {
                    assert(e[w].1@ != e[i].1@);
                }
            }
        }
        self.put_dcid(a, Some(cur.as_slice()));
        proof {
            self.lemma_unheld_edit(s0, a);
            assert forall|q1: PathId, q2: PathId|
                #[trigger] self.paths.has(q1) && #[trigger] self.paths.has(q2) && q1 != a && q2 != a implies self.pair_ok(q1, q2) by {
                assert(s0.paths.has(q1));
                assert(s0.paths.has(q2));
                assert(s0.pair_ok(q1, q2));
            }
        }
        self.repair_pairs(a);
        proof {
            assert(peer_has_cid(self.peer_cids.entries(), cur@));
        }
    }

    /// A path other than the active `a`: if it holds a retired CID it takes `a`'s when the peer
    /// used one CID on both, else an unused CID, else none.
    #[verifier::spinoff_prover]
    fn rewrite_path(&mut self, q: PathId, a: PathId)
        requires
            old(self).wf_rest(),
            old(self).dcids_weak(),
            old(self).paths.has(q),
            a == old(self).paths.active_spec(),
            old(self).not_stale(a),
        ensures
            final(self).wf_rest(),
            final(self).dcids_weak(),
            final(self).frames_kept(*old(self)),
            kept(old(self).paths, final(self).paths, q),
            final(self).not_stale(q),
            forall|x: Seq<u8>| #[trigger]
                peer_has_cid(final(self).peer_cids.entries(), x) == peer_has_cid(
                    old(self).peer_cids.entries(),
                    x,
                ),
    {
        if !self.is_stale(q) {
            return;
        }
        proof {
            self.paths.lemma_wf();
        }
        if opt_eq(self.paths.peer_used(q), self.paths.peer_used(a)) {
            let d = self.active_dcid(a);
            self.hold_dcid(q, Some(d.as_slice()));
        } else if !self.fresh_dcid(q) {
            self.hold_dcid(q, None);
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-9.5
    //# Similarly, an endpoint MUST NOT reuse a connection ID when sending to
    //# more than one destination address.
    /// After `on_new_cid`: every path holding a retired CID (§5.1.2 "MUST stop using") gets another,
    /// the active path first. Runs after every `Ok`: a used non-current CID can be retired while
    /// `current()` stays put.
    #[verifier::spinoff_prover]
    fn rewrite_stale(&mut self, rand: &[u8; RAND_LEN])
        requires
            old(self).wf_rest(),
            old(self).dcids_weak(),
        ensures
            final(self).wf(),
            final(self).frames_kept(*old(self)),
    {
        proof {
            self.paths.lemma_wf();
        }
        let a = self.paths.active();
        let moved = self.is_stale(a);
        if moved {
            self.rewrite_active(a);
        }
        let n = self.paths.len();
        let ghost ids = self.paths.ids();
        let mut i: usize = 0;
        while i < n
            invariant
                n == ids.len(),
                i <= n,
                self.paths.ids() == ids,
                self.wf_rest(),
                self.dcids_weak(),
                self.frames_kept(*old(self)),
                a == self.paths.active_spec(),
                self.not_stale(a),
                forall|k: int| 0 <= k < i ==> self.not_stale(#[trigger] ids[k]),
            decreases n - i,
        {
            let q = self.path_at(i);
            let ghost s1 = *self;
            self.rewrite_path(q, a);
            proof {
                assert forall|k: int| 0 <= k < i + 1 implies self.not_stale(#[trigger] ids[k]) by {
                    if k < i && ids[k] != q {
                        assert(s1.not_stale(ids[k]));
                    }
                }
                if a != q {
                    assert(s1.not_stale(a));
                }
            }
            i += 1;
        }
        // E4: a new CID on the active path redraws the spin bit.
        if moved {
            self.spin = rand[128] & 1 == 1;
        }
        proof {
            assert forall|q: PathId| #[trigger] self.paths.has(q) implies self.not_stale(q) by {
                let k = choose|k: int| 0 <= k < ids.len() && ids[k] == q;
                assert(self.not_stale(ids[k]));
            }
            self.lemma_wf_of_weak();
        }
    }

    /// PATH_CHALLENGE or PATH_RESPONSE, arriving on `path`.
    #[verifier::spinoff_prover]
    fn on_path_frame(
        &mut self,
        path: PathId,
        f: &Frame,
        now: u64,
        rand: &[u8; RAND_LEN],
    ) -> (r: Result<(), u64>)
        requires
            old(self).wf(),
            old(self).paths.has(path),
            frame_wf(f@),
            f@ is PathChallenge || f@ is PathResponse,
        ensures
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            r matches Err(c) ==> c <= VARINT_MAX,
    {
        match f {
            Frame::PathChallenge(d) => {
                let ghost s0 = *self;
                self.paths.on_challenge(path, *d);
                proof {
                    self.lemma_path_edit(s0, path);
                    self.lemma_dcids_same(s0, path);
                }
                self.assign_dcid(path, rand);
            },
            Frame::PathResponse(d) => self.on_path_response(*d, now, rand),
            _ => {},
        }
        Ok(())
    }

    /// PATH_RESPONSE: §9.4's congestion reset only for a newly validated address (not an MTU probe's
    /// answer, nor §9.3.3's recheck of the old path), then an MTU probe if the path needs one.
    #[verifier::spinoff_prover]
    fn on_path_response(&mut self, data: [u8; 8], now: u64, rand: &[u8; RAND_LEN])
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            final(self).recovery != old(self).recovery ==> exists|q: PathId|
                #[trigger] old(self).paths.has(q) && answers(old(self).paths.path(q), data) && !(old(
                    self,
                ).paths.state_spec(q) is Validated),
    {
        let was = self.validated_paths();
        let ghost s0 = *self;
        if let Some(q) = self.paths.on_response(data) {
            proof {
                self.lemma_path_event(s0, q, AmpEv::Validated);
            }
            if let Some(i) = self.paths.index(q) {
                if !was[i] {
                    self.recovery.on_path_validated();
                    proof {
                        assert(s0.paths.ids()[i as int] == q);
                        assert(s0.paths.has(q));
                    }
                }
            }
            if self.paths.needs_mtu_probe(q) {
                self.challenge_path(q, now, rand);
            }
        }
    }

    /// Which paths are Validated, by entry (at most `MAX_PATHS`).
    #[verifier::spinoff_prover]
    fn validated_paths(&self) -> (r: Vec<bool>)
        requires
            self.wf(),
        ensures
            r@.len() == self.paths.ids().len(),
            forall|k: int|
                0 <= k < r@.len() ==> r@[k] == (self.paths.state_spec(self.paths.ids()[k]) is Validated),
    {
        let n = self.paths.len();
        let mut r: Vec<bool> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                self.wf(),
                n == self.paths.ids().len(),
                i <= n,
                r@.len() == i,
                forall|k: int|
                    0 <= k < i ==> r@[k] == (self.paths.state_spec(self.paths.ids()[k]) is Validated),
            decreases n - i,
        {
            let q = self.path_at(i);
            r.push(matches!(self.paths.state(q), PathState::Validated));
            i += 1;
        }
        r
    }

    /// The next unused challenge slice of `rand`: never reused within a call, since `on_response`
    /// ignores the arrival path (§8.2.2) and distinct data is what ties a response to its path
    /// (§8.2.1). None once all four are used.
    #[verifier::spinoff_prover]
    fn next_challenge(&mut self, rand: &[u8; RAND_LEN]) -> (r: Option<[u8; 8]>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            final(self).paths == old(self).paths,
            final(self).recovery == old(self).recovery,
            r is None <==> old(self).chal_used == 4,
            r matches Some(c) ==> {
                &&& final(self).chal_used == old(self).chal_used + 1
                &&& c@ == rand@.subrange(
                    96 + 8 * old(self).chal_used as int,
                    104 + 8 * old(self).chal_used as int,
                )
            },
    {
        if self.chal_used == 4 {
            return None;
        }
        let at = 96 + 8 * self.chal_used;
        let mut c = [0u8; 8];
        c.copy_from_slice(slice_subrange(rand.as_slice(), at, at + 8));
        self.chal_used = self.chal_used + 1;
        Some(c)
    }

    /// Starts a challenge on `q` from the next slice of `rand`, if one is left.
    #[verifier::spinoff_prover]
    fn challenge_path(&mut self, q: PathId, now: u64, rand: &[u8; RAND_LEN])
        requires
            old(self).wf(),
            old(self).paths.has(q),
        ensures
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            final(self).paths.active_spec() == old(self).paths.active_spec(),
            final(self).recovery == old(self).recovery,
    {
        if let Some(c) = self.next_challenge(rand) {
            let ghost s0 = *self;
            self.paths.start_challenge(q, c, now);
            proof {
                self.lemma_path_edit(s0, q);
                self.lemma_dcids_same(s0, q);
            }
        }
    }

    /// A 1-RTT packet was processed: assigns `path` a DCID and migrates to it (§9).
    #[verifier::spinoff_prover]
    fn after_one_rtt(
        &mut self,
        path: PathId,
        non_probing: bool,
        pn: u64,
        now: u64,
        rand: &[u8; RAND_LEN],
    )
        requires
            old(self).wf(),
            old(self).paths.has(path),
        ensures
            final(self).wf(),
            final(self).frames_kept(*old(self)),
    {
        if path == self.paths.active() {
            return;
        }
        self.assign_dcid(path, rand);
        if non_probing {
            if let Some(l) = self.recv_1.largest() {
                if l == pn {
                    self.migrate(path, now, rand);
                }
            }
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-9
    //# If the peer
    //# violates this requirement, the endpoint MUST either drop the incoming
    //# packets on that path without generating a Stateless Reset or proceed
    //# with path validation and allow the peer to migrate.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-9
    //# An endpoint MUST
    //# perform path validation (Section 8.2) if it detects any change to a
    //# peer's address, unless it has previously validated that address.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-9
    //= type=exception
    //= reason=We never initiate migration and never send from another local address.
    //# An endpoint MUST NOT initiate
    //# connection migration before the handshake is confirmed, as defined in
    //# Section 4.1.2 of [QUIC-TLS].
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-9
    //= type=exception
    //= reason=We never initiate migration and never send from another local address.
    //# If the peer sent the disable_active_migration transport parameter, an
    //# endpoint also MUST NOT send packets (including probing packets; see
    //# Section 9.1) from a different local address to the address the peer
    //# used during the handshake, unless the endpoint has acted on a
    //# preferred_address transport parameter from the peer.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-9
    //= type=exception
    //= reason=client-only
    //# If a client receives
    //# packets from an unknown server address, the client MUST discard these
    //# packets.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-9.3
    //# If the recipient permits the migration, it MUST send subsequent
    //# packets to the new peer address and MUST initiate path validation
    //# (Section 8.2) to verify the peer's ownership of the address if
    //# validation is not already underway.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-9.3
    //# An endpoint MAY send data to an unvalidated peer address, but it MUST
    //# protect against potential attacks as described in Sections 9.3.1 and
    //# 9.3.2.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-9.3.3
    //# In response to an apparent migration, endpoints MUST validate the
    //# previously active path using a PATH_CHALLENGE frame.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-9.5
    //= type=exception
    //= reason=We never initiate migration and never send from another local address.
    //# An endpoint MUST NOT reuse a connection ID when sending from more
    //# than one local address -- for example, when initiating connection
    //# migration as described in Section 9.2 or when probing a new network
    //# path as described in Section 9.1.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-9.5
    //# Similarly, an endpoint MUST NOT reuse a connection ID when sending to
    //# more than one destination address.
    /// The peer moved to `path`. Changes no DCID and no `peer_used`, so §9.5 at the new address
    /// follows from `wf_dcids`' pair conjunct.
    #[verifier::spinoff_prover]
    fn migrate(&mut self, path: PathId, now: u64, rand: &[u8; RAND_LEN])
        requires
            old(self).wf(),
            old(self).paths.has(path),
        ensures
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            final(self).paths.path(path).dcid is Some ==> forall|q: PathId|
                #[trigger] final(self).paths.has(q) && q != path && final(self).paths.path(q).dcid
                    == final(self).paths.path(path).dcid ==> final(self).paths.path(q).peer_used
                    == final(self).paths.path(path).peer_used,
    {
        // §9.5: no fresh CID for a second destination.
        if self.paths.dcid(path).is_none() {
            return;
        }
        // §14.2: never make a failed-MTU path active (3d final review I2).
        if self.paths.mtu_failed(path) {
            return;
        }
        let old_path = self.paths.active();
        let ghost s0 = *self;
        self.paths.set_active(path);
        proof {
            self.lemma_active_set(s0, path);
        }
        // §9, §9.3: not if validation is already underway (preflight M9).
        if matches!(self.paths.state(path), PathState::Unvalidated) {
            self.challenge_path(path, now, rand);
        }
        proof {
            s0.paths.lemma_wf();
            assert(self.paths.has(old_path)) by {
                assert(s0.paths.has(old_path));
            }
        }
        if matches!(self.paths.state(old_path), PathState::Validated) {
            self.challenge_path(old_path, now, rand);
        }
        proof {
            assert(self.paths.has(path));
            assert forall|q: PathId|
                #[trigger] self.paths.has(q) && q != path && self.paths.path(q).dcid
                    == self.paths.path(path).dcid && self.paths.path(path).dcid is Some implies self.paths.path(q).peer_used
                == self.paths.path(path).peer_used by {
                assert(self.paths.has(path));
            }
        }
    }

    /// `self` is `o` with path `path`, which holds a DCID, made active.
    proof fn lemma_active_set(&self, o: Connection, path: PathId)
        requires
            o.wf(),
            o.paths.path(path).dcid is Some,
            self.paths.wf(),
            self.paths.active_spec() == path,
            self.paths.ids() == o.paths.ids(),
            forall|q: PathId| #[trigger] self.paths.path(q) == o.paths.path(q),
            self.out_log@ == o.out_log@,
            self.peer_cids == o.peer_cids,
            self.wf_parts(),
            self.wf_streams(),
            self.wf_pn(),
        ensures
            self.wf_amp(),
            self.wf_log_paths(),
            self.wf_dcids(),
    {
        assert forall|q: PathId| #[trigger] self.paths.has(q) implies amp_ok(self.paths.amp_trace(q))
            && sent_entries(self.paths.amp_trace(q)) == log_sends(self.out_log@, q) by {
            assert(o.paths.has(q));
        }
        assert forall|i: int| 0 <= i < self.out_log@.len() implies #[trigger] self.paths.index_spec(
            self.out_log@[i].path,
        ) is Some by {
            assert(o.paths.index_spec(self.out_log@[i].path) is Some);
        }
        assert forall|q: PathId| #[trigger] self.paths.has(q) implies (self.paths.path(q).dcid matches Some(c)
            ==> used_cid(self.peer_cids.entries(), c)) by {
            assert(o.paths.has(q));
        }
        assert forall|q1: PathId, q2: PathId|
            #[trigger] self.paths.has(q1) && #[trigger] self.paths.has(q2) && q1 != q2
                && self.paths.path(q1).dcid is Some && self.paths.path(q1).dcid == self.paths.path(
                q2,
            ).dcid implies self.paths.path(q1).peer_used == self.paths.path(q2).peer_used by {
            assert(o.paths.has(q1));
            assert(o.paths.has(q2));
        }
    }

    /// §13.3: frame `f` of an acknowledged record of space `k`.
    #[verifier::spinoff_prover]
    fn on_acked_frame(&mut self, k: PacketKind, f: &Frame)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            final(self).hs_done == (if f@ is HandshakeDone {
                HsDone::Acked
            } else {
                old(self).hs_done
            }),
            !(f@ is RetireConnectionId) ==> final(self).peer_cids == old(self).peer_cids,
            f@ is RetireConnectionId ==> final(self).peer_cids.retire_pending_spec() == old(
                self,
            ).peer_cids.retire_pending_spec(),
            final(self).local_cids == old(self).local_cids,
            old(self).routing_kept(*final(self), k, f@),
    {
        match f {
            Frame::ResetStream { .. }
            | Frame::StopSending { .. }
            | Frame::Stream { .. }
            | Frame::MaxData(_)
            | Frame::MaxStreamData { .. }
            | Frame::MaxStreams { .. }
            | Frame::DataBlocked(_)
            | Frame::StreamDataBlocked { .. }
            | Frame::StreamsBlocked { .. } => {
                if let Some(s) = &mut self.streams {
                    s.on_frame_acked(f);
                }
            },
            Frame::Crypto { offset, data } => match k {
                PacketKind::Initial => self.ctx_i.on_data_acked(*offset, data.len() as u64, false),
                PacketKind::Handshake => self.ctx_h.on_data_acked(*offset, data.len() as u64, false),
                PacketKind::OneRtt => {},
            },
            Frame::HandshakeDone => self.hs_done = HsDone::Acked,
            Frame::RetireConnectionId(s) => self.peer_cids.retire_acked(*s),
            _ => {},
        }
    }

    /// §13.3: frame `f` of a lost record of space `k`. Outdated frames are accepted: 3c's credit
    /// `on_max` ignores decreases.
    #[verifier::spinoff_prover]
    #[allow(dead_code)]  // Called from Task 3.
    fn on_lost_frame(&mut self, k: PacketKind, f: &Frame)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            final(self).hs_done == (if f@ is HandshakeDone && !(old(self).hs_done is Acked) {
                HsDone::Pending
            } else {
                old(self).hs_done
            }),
            !(f@ is RetireConnectionId) ==> final(self).peer_cids == old(self).peer_cids,
            f@ matches SpecFrame::RetireConnectionId(s) ==> old(self).peer_cids.retire_unacked_spec().contains(
                s,
            ) ==> final(self).peer_cids.retire_pending_spec() == old(
                self,
            ).peer_cids.retire_pending_spec().push(s),
            !(f@ is NewConnectionId) ==> final(self).local_cids == old(self).local_cids,
            f@ matches SpecFrame::NewConnectionId { seq, .. } ==> final(self).local_cids.pending_spec()
                == if seq != 0 && local_has_seq(old(self).local_cids.active_spec(), seq) && !old(
                self,
            ).local_cids.pending_spec().contains(seq) {
                old(self).local_cids.pending_spec().push(seq)
            } else {
                old(self).local_cids.pending_spec()
            },
            old(self).routing_kept(*final(self), k, f@),
    {
        match f {
            Frame::ResetStream { .. }
            | Frame::StopSending { .. }
            | Frame::Stream { .. }
            | Frame::MaxData(_)
            | Frame::MaxStreamData { .. }
            | Frame::MaxStreams { .. }
            | Frame::DataBlocked(_)
            | Frame::StreamDataBlocked { .. }
            | Frame::StreamsBlocked { .. } => {
                if let Some(s) = &mut self.streams {
                    s.on_frame_lost(f);
                }
            },
            Frame::Crypto { offset, data } => match k {
                PacketKind::Initial => self.ctx_i.on_data_lost(*offset, data.len() as u64, false),
                PacketKind::Handshake => self.ctx_h.on_data_lost(*offset, data.len() as u64, false),
                PacketKind::OneRtt => {},
            },
            Frame::HandshakeDone => {
                if !matches!(self.hs_done, HsDone::Acked) {
                    self.hs_done = HsDone::Pending;
                }
            },
            Frame::NewConnectionId { seq, .. } => self.local_cids.on_frame_lost(*seq),
            Frame::RetireConnectionId(s) => self.peer_cids.retire_lost(*s),
            _ => {},
        }
    }

    // =========================================================================
    // Discard and close
    // =========================================================================

    /// Drops an Initial or Handshake space, once (RFC 9001 §4.9). `sent(k)` is drained, not
    /// replaced: a fresh `SentPackets` would reset `next_pn` and break `wf_pn`.
    #[verifier::spinoff_prover]
    fn discard(&mut self, k: PacketKind)
        requires
            old(self).wf(),
            !(k is OneRtt),
        ensures
            final(self).wf(),
            !final(self).live(k),
            k is Initial ==> final(self).live(PacketKind::Handshake) == old(self).live(
                PacketKind::Handshake,
            ),
            k is Handshake ==> final(self).live(PacketKind::Initial) == old(self).live(
                PacketKind::Initial,
            ),
            final(self).out_log() == old(self).out_log(),
            final(self).paths == old(self).paths,
            final(self).lc == old(self).lc,
            final(self).complete == old(self).complete,
            final(self).peer_tp == old(self).peer_tp,
            final(self).streams == old(self).streams,
    {
        let mut lost: Vec<SentPacket> = Vec::new();
        match k {
            PacketKind::Initial => {
                if !self.live_i {
                    return;
                }
                self.live_i = false;
                self.sent_i.drain_inflight(&mut lost);
                self.crx_i = CryptoStream::new();
                self.ctx_i = SendStream::new(VARINT_MAX);
                self.recv_i = RecvPns::new(k);
                self.cid_updates.push(CidUpdate::Remove(slice_to_vec(self.ids.odcid())));
            },
            PacketKind::Handshake => {
                if !self.live_h {
                    return;
                }
                self.live_h = false;
                self.sent_h.drain_inflight(&mut lost);
                self.crx_h = CryptoStream::new();
                self.ctx_h = SendStream::new(VARINT_MAX);
                self.recv_h = RecvPns::new(k);
            },
            PacketKind::OneRtt => {},
        }
        self.recovery.on_space_discarded(k);
        proof {
            assert(cids_only(self.cid_updates@));
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-11.1
    //# Errors that result in the connection being unusable, such as an
    //# obvious violation of protocol semantics or corruption of state that
    //# affects an entire connection, MUST be signaled using a
    //# CONNECTION_CLOSE frame (Section 19.19).
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-10.3
    //# An endpoint that wishes to communicate a fatal
    //# connection error MUST use a CONNECTION_CLOSE frame if it is able.
    /// Closes with a transport error.
    #[verifier::spinoff_prover]
    fn close_internal(&mut self, code: u64)
        requires
            old(self).wf(),
            code <= VARINT_MAX,
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
    {
        let now = self.now;
        let none: Vec<u8> = Vec::new();
        self.close(code, false, none.as_slice(), now);
    }

    /// Enters the closing state (the first error wins, §11.1) and drops the streams.
    #[verifier::spinoff_prover]
    pub fn close(&mut self, code: u64, app: bool, reason: &[u8], now: u64)
        requires
            old(self).wf(),
            code <= VARINT_MAX,
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            old(self).phase_spec() is Open ==> final(self).phase_spec() is Closing,
            !(old(self).phase_spec() is Open) ==> final(self).phase_spec() == old(self).phase_spec(),
    {
        if now > self.now {
            self.now = now;
        }
        let pto = self.pto();
        self.lc.enter_closing(self.now, pto, app, code, reason);
        self.streams = None;
    }

    /// The current 1-RTT probe timeout.
    #[verifier::spinoff_prover]
    fn pto(&self) -> (r: u64)
        requires
            self.wf(),
    {
        let ms = match &self.peer_tp {
            Some(t) => t.max_ack_delay,
            None => 25,
        };
        self.recovery.pto_us(PacketKind::OneRtt, ms_to_us(ms))
    }

    // =========================================================================
    // The TLS boundary
    // =========================================================================

    /// Appends the newly contiguous CRYPTO bytes of `level` to `out`.
    #[verifier::spinoff_prover]
    pub fn crypto_read(&mut self, level: PacketKind, out: &mut Vec<u8>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
    {
        if !matches!(self.lc.phase(), Phase::Open) {
            return;
        }
        match level {
            PacketKind::Initial => self.crx_i.read(out),
            PacketKind::Handshake => self.crx_h.read(out),
            PacketKind::OneRtt => self.crx_1.read(out),
        }
    }

    /// Queues CRYPTO data for `level`; ignored once its space is discarded.
    #[verifier::spinoff_prover]
    pub fn crypto_write(&mut self, level: PacketKind, data: &[u8])
        requires
            old(self).wf(),
            !(level is OneRtt),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
    {
        if !matches!(self.lc.phase(), Phase::Open) {
            return;
        }
        match level {
            PacketKind::Initial => if self.live_i {
                let _ = self.ctx_i.write(data, false);
            },
            PacketKind::Handshake => if self.live_h {
                let _ = self.ctx_h.write(data, false);
            },
            PacketKind::OneRtt => {},
        }
    }

    /// TLS delivered the client's transport parameters.
    #[verifier::spinoff_prover]
    pub fn on_peer_params(&mut self, tp: &TransportParams, now: u64)
        requires
            old(self).wf(),
            peer_tp_wf(tp@),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
    {
        if now > self.now {
            self.now = now;
        }
        if !matches!(self.lc.phase(), Phase::Open) || self.peer_tp.is_some() {
            return;
        }
        if let Err(c) = self.ids.check_peer_tp(tp) {
            self.close_internal(c);
            return;
        }
        proof {
            lemma_local_tp_streams(self.local_tp@);
            lemma_peer_tp_stream_ok(tp@);
        }
        self.streams = Some(Streams::new(&self.local_tp, tp));
        self.peer_tp = Some(copy_tp(tp));
    }

    /// TLS finished, with this ALPN. After this no long-header packet is built.
    #[verifier::spinoff_prover]
    pub fn on_handshake_complete(&mut self, alpn: &[u8], now: u64, rand: &[u8; RAND_LEN])
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
    {
        if now > self.now {
            self.now = now;
        }
        self.chal_used = 0;
        if !matches!(self.lc.phase(), Phase::Open) || self.complete {
            return;
        }
        // `streams.is_none()` is unreachable (`on_peer_params` sets both); `wf`'s `complete` clause
        // needs it, and it costs less than one more conjunct.
        if self.peer_tp.is_none() || self.streams.is_none() {
            self.close_internal(INTERNAL_ERROR);
            return;
        }
        if let Err(c) = check_alpn(alpn) {
            self.close_internal(c);
            return;
        }
        self.discard(PacketKind::Initial);
        self.discard(PacketKind::Handshake);
        self.complete = true;
        self.hs_done = HsDone::Pending;
        self.spin = rand[128] & 1 == 1;
        self.issue_cids(rand);
    }

    /// TLS failed with this alert (RFC 9001 §4.8).
    #[verifier::spinoff_prover]
    pub fn on_tls_alert(&mut self, alert: u8, now: u64)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
    {
        if now > self.now {
            self.now = now;
        }
        self.close_internal(CRYPTO_ERROR_BASE + alert as u64);
    }

    /// Issues CIDs up to the peer's limit, trying each CID slice of `rand` once.
    #[verifier::spinoff_prover]
    fn issue_cids(&mut self, rand: &[u8; RAND_LEN])
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            final(self).frames_kept(*old(self)),
    {
        if !self.complete {
            return;
        }
        let limit = match &self.peer_tp {
            Some(t) => t.active_connection_id_limit,
            None => return,
        };
        // ponytail: a fresh 64-bit CID equal to another connection's makes CidTable::apply(Add) return false with no feedback (probability ~n²/2^64 at n ≤ MAX_CONNS·PER_CONN); a re-issue path if CIDs ever shrink.
        let mut i: usize = 0;
        while i < 4
            invariant
                i <= 4,
                self.wf(),
                self.out_log() == old(self).out_log(),
                self.frames_kept(*old(self)),
            decreases 4 - i,
        {
            let s = slice_subrange(rand.as_slice(), 24 * i, 24 * i + 24);
            if self.local_cids.issue(s, limit) {
                self.cid_updates.push(CidUpdate::Add(slice_to_vec(slice_subrange(s, 0, 8))));
                proof {
                    assert(cids_only(self.cid_updates@));
                }
            }
            i += 1;
        }
    }

    // =========================================================================
    // Application side
    // =========================================================================

    /// How many more bytes `stream_write` accepts, over all streams.
    pub closed spec fn send_room_spec(&self) -> int {
        match self.streams {
            Some(s) => MAX_SEND_BUFFER - s.tx_buffered(),
            None => 0,
        }
    }

    /// Whether `id`'s sending part has its FIN written.
    pub closed spec fn fin_written(&self, id: u64) -> bool {
        self.streams matches Some(s) && s.tx_part(id) matches Some(p) && p.fin_written_spec()
    }

    /// Queues as much of `data` as the send buffer takes, with the FIN only if all of it fits;
    /// `Ok(0)` with nothing changed when none of it does. `Err` unless Open with streams, or for a
    /// stream that cannot be written.
    #[verifier::spinoff_prover]
    pub fn stream_write(&mut self, id: u64, data: &[u8], fin: bool) -> (r: Result<usize, ()>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            r matches Ok(n) ==> n <= data@.len() && (n < data@.len() ==> n == old(self).send_room_spec()),
            r matches Ok(n) ==> (n > 0 || data@.len() == 0 && fin) ==> final(self).fin_written(id) == (fin && n
                == data@.len()),
    {
        match &mut self.streams {
            Some(s) => {
                let room = s.send_room();
                let n = if data.len() as u64 > room {
                    room as usize
                } else {
                    data.len()
                };
                if n == 0 && !(fin && data.len() == 0) {
                    return Ok(0);
                }
                match s.write(id, slice_subrange(data, 0, n), fin && n == data.len()) {
                    Ok(()) => Ok(n),
                    Err(()) => Err(()),
                }
            },
            None => Err(()),
        }
    }

    /// The application abandons sending on `id` (RESET_STREAM).
    #[verifier::spinoff_prover]
    pub fn stream_reset(&mut self, id: u64, code: u64)
        requires
            old(self).wf(),
            code <= VARINT_MAX,
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
    {
        if let Some(s) = &mut self.streams {
            s.reset(id, code);
        }
    }

    /// The application stops reading `id` (STOP_SENDING).
    #[verifier::spinoff_prover]
    pub fn stream_stop_sending(&mut self, id: u64, code: u64)
        requires
            old(self).wf(),
            code <= VARINT_MAX,
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
    {
        if let Some(s) = &mut self.streams {
            s.stop_sending(id, code);
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-10.3.1
    //# However, the comparison MUST be performed
    //# when the first packet in an incoming datagram either cannot be
    //# associated with a connection or cannot be decrypted.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-10.3.1
    //# If the last 16 bytes of the datagram are identical in value to a
    //# stateless reset token, the endpoint MUST enter the draining period
    //# and not send any further packets on this connection.
    /// A datagram's last 16 bytes, when its first packet will not decrypt or the shell routed it as
    /// a reset: a match with a used, active CID's token ends the connection (§10.3.1).
    #[verifier::spinoff_prover]
    pub fn on_reset_candidate(&mut self, tail: &[u8; 16], now: u64)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
    {
        if now > self.now {
            self.now = now;
        }
        if self.peer_cids.matches_reset(tail) {
            let pto = self.pto();
            self.lc.enter_draining(self.now, pto);
            self.streams = None;
        }
    }

    // =========================================================================
    // Polling
    // =========================================================================

    /// Moves the stream events into `out`, in order, with no data copies.
    pub fn poll_stream_events(&mut self, out: &mut Vec<StreamEvent>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            final(out)@ == old(out)@ + old(self).events_spec(),
            final(self).events_spec().len() == 0,
    {
        let mut taken: Vec<StreamEvent> = Vec::new();
        core::mem::swap(&mut self.events, &mut taken);
        out.append(&mut taken);
    }

    /// Moves `cid_updates` into `out`, then brings the registered reset tokens in line with
    /// `peer_cids.used_tokens()`, every `RemoveToken` before any `AddToken`.
    #[verifier::spinoff_prover]
    pub fn poll_cid_updates(&mut self, out: &mut Vec<CidUpdate>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            final(self).updates_spec().len() == 0,
            final(self).tokens_in_sync(),
            final(out)@.len() >= old(out)@.len() + old(self).updates_spec().len(),
            forall|i: int|
                0 <= i < old(self).updates_spec().len() ==> #[trigger] final(out)@[old(out)@.len()
                    + i] == old(self).updates_spec()[i],
            removes_before_adds(final(out)@.skip(old(out)@.len() as int)),
            tokens_changed(
                final(out)@.skip(old(out)@.len() as int),
                old(self).registered(),
                final(self).registered(),
            ),
            tokens_covered(
                final(out)@.skip(old(out)@.len() as int),
                old(self).registered(),
                final(self).registered(),
            ),
    {
        let ghost n0 = out@.len() as int;
        let ghost updates = self.cid_updates@;
        let mut taken: Vec<CidUpdate> = Vec::new();
        core::mem::swap(&mut self.cid_updates, &mut taken);
        out.append(&mut taken);
        let ghost s0 = out@;
        let used = self.peer_cids.used_tokens();
        push_removes(&self.tokens_registered, &used, out);
        let ghost s1 = out@;
        push_adds(&self.tokens_registered, &used, out);
        let ghost s2 = out@;
        let ghost regs = self.tokens_registered@;
        self.tokens_registered = used;
        proof {
            self.peer_cids.lemma_wf();
            assert forall|t: [u8; 16]| #[trigger]
                reset_match(self.peer_cids.entries(), t@) implies used@.contains(t) by {
                let e = self.peer_cids.entries();
                let i = choose|i: int| 0 <= i < e.len() && (#[trigger] e[i]).3 && tok_is(e[i].2, t@);
                let x = e[i].2->0;
                assert(x@ == t@);
                assert(x =~= t);
                assert(used@.contains(x));
            }
            assert forall|t: [u8; 16]| #[trigger] used@.contains(t) implies reset_match(
                self.peer_cids.entries(),
                t@,
            ) by {
                let j = choose|j: int| 0 <= j < used@.len() && used@[j] == t;
                assert(reset_match(self.peer_cids.entries(), used@[j]@));
            }
            let s = s2.skip(n0);
            assert forall|i: int, j: int|
                0 <= i < j < s.len() && #[trigger] s[i] is AddToken implies !(
                #[trigger] s[j] is RemoveToken) by {
                let a = n0 + i;
                let b = n0 + j;
                assert(s[i] == s2[a]);
                assert(s[j] == s2[b]);
                if a < s1.len() {
                    assert(s2[a] == s1[a]);
                    if a < s0.len() {
                        assert(s1[a] == s0[a]);
                        assert(s0[a] == updates[a - n0]);
                        assert(updates[a - n0] is Add || updates[a - n0] is Remove);
                    } else {
                        assert(s1[a] is RemoveToken);
                    }
                }
                assert(s2[b] is AddToken);
            }
            assert forall|i: int| 0 <= i < updates.len() implies #[trigger] s2[n0 + i] == updates[i] by {
                assert(s0[n0 + i] == updates[i]);
                assert(s1[n0 + i] == s0[n0 + i]);
                assert(s2[n0 + i] == s1[n0 + i]);
            }
            assert forall|i: int| 0 <= i < s.len() implies match #[trigger] s[i] {
                CidUpdate::RemoveToken(t) => regs.contains(t) && !used@.contains(t),
                CidUpdate::AddToken(t) => used@.contains(t) && !regs.contains(t),
                _ => true,
            } by {
                let a = n0 + i;
                assert(s[i] == s2[a]);
                if a < s1.len() {
                    assert(s2[a] == s1[a]);
                    if a < s0.len() {
                        assert(s1[a] == s0[a]);
                        assert(s0[a] == updates[a - n0]);
                        assert(updates[a - n0] is Add || updates[a - n0] is Remove);
                    }
                }
            }
            assert forall|i: int| 0 <= i < regs.len() && !used@.contains(regs[i]) implies s.contains(
                CidUpdate::RemoveToken(#[trigger] regs[i]),
            ) by {
                let w = choose|w: int|
                    s0.len() <= w < s1.len() && #[trigger] s1[w] == CidUpdate::RemoveToken(regs[i]);
                assert(s2[w] == s1[w]);
                assert(s[w - n0] == s2[w]);
            }
            assert forall|i: int| 0 <= i < used@.len() && !regs.contains(used@[i]) implies s.contains(
                CidUpdate::AddToken(#[trigger] used@[i]),
            ) by {
                let w = choose|w: int|
                    s1.len() <= w < s2.len() && #[trigger] s2[w] == CidUpdate::AddToken(used@[i]);
                assert(s[w - n0] == s2[w]);
            }
        }
    }

    // =========================================================================
    // Getters
    // =========================================================================

    /// The largest packet number received in space `k` (3e's `decode_pn` input).
    pub fn largest_pn(&self, k: PacketKind) -> (r: Option<u64>)
        ensures
            r == self.recv(k).largest_spec(),
    {
        match k {
            PacketKind::Initial => self.recv_i.largest(),
            PacketKind::Handshake => self.recv_h.largest(),
            PacketKind::OneRtt => self.recv_1.largest(),
        }
    }

    pub fn phase(&self) -> (r: Phase)
        ensures
            r == self.phase_spec(),
    {
        self.lc.phase()
    }

    pub fn is_closed(&self) -> (r: bool)
        ensures
            r == (self.phase_spec() is Closed),
    {
        matches!(self.lc.phase(), Phase::Closed)
    }

    pub fn handshake_complete(&self) -> (r: bool)
        ensures
            r == self.live(PacketKind::OneRtt),
    {
        self.complete
    }

    /// Our transport parameters, filled in.
    pub fn local_params(&self) -> (r: &TransportParams)
        requires
            self.wf(),
        ensures
            server_tp_wf(r@),
            local_tp_ok(r@),
    {
        &self.local_tp
    }

    /// The peer's limit on our unidirectional streams, once `Streams` exists.
    pub fn peer_uni_limit(&self) -> (r: Option<u64>)
        requires
            self.wf(),
        ensures
            self.wf() && self.live(PacketKind::OneRtt) && self.phase_spec() is Open ==> r is Some,
    {
        match &self.streams {
            Some(s) => Some(s.local_uni_limit()),
            None => None,
        }
    }

    pub fn now(&self) -> (r: u64) {
        self.now
    }

    pub fn active_path(&self) -> (r: PathId) {
        self.paths.active()
    }

    pub fn streams_live(&self) -> (r: bool) {
        self.streams.is_some()
    }

    pub fn sent_inflight_len(&self, k: PacketKind) -> (r: usize)
        ensures
            r == self.sent(k).inflight_spec().len(),
    {
        match k {
            PacketKind::Initial => self.sent_i.inflight_len(),
            PacketKind::Handshake => self.sent_h.inflight_len(),
            PacketKind::OneRtt => self.sent_1.inflight_len(),
        }
    }

    /// The close we are sending: application or transport, code, reason.
    pub fn close_info(&self) -> (r: &Option<(bool, u64, Vec<u8>)>)
        requires
            self.wf(),
    {
        self.lc.close_info()
    }

    /// None when `q` is absent.
    pub fn path_state(&self, q: PathId) -> (r: Option<PathState>)
        requires
            self.wf(),
    {
        match self.paths.index(q) {
            Some(_) => Some(self.paths.state(q)),
            None => None,
        }
    }

    /// The peer CID we send with on `q`; None when `q` is absent or has none.
    pub fn path_dcid(&self, q: PathId) -> (r: Option<Vec<u8>>)
        requires
            self.wf(),
    {
        match self.paths.index(q) {
            Some(_) => match self.paths.dcid(q) {
                Some(d) => Some(slice_to_vec(d)),
                None => None,
            },
            None => None,
        }
    }

    /// A PATH_RESPONSE is owed on `q`; false when `q` is absent.
    pub fn response_owed(&self, q: PathId) -> (r: bool)
        requires
            self.wf(),
    {
        match self.paths.index(q) {
            Some(_) => self.paths.has_response(q),
            None => false,
        }
    }

    /// A PATH_CHALLENGE is owed on `q`; false when `q` is absent.
    pub fn challenge_owed(&self, q: PathId) -> (r: bool)
        requires
            self.wf(),
    {
        match self.paths.index(q) {
            Some(_) => self.paths.challenge_owed(q),
            None => false,
        }
    }
}

// =============================================================================
// Helpers
// =============================================================================

/// Whether two optional byte strings are equal.
fn opt_eq(a: Option<&[u8]>, b: Option<&[u8]>) -> (r: bool)
    ensures
        r == (opt_slice_view(a) == opt_slice_view(b)),
{
    match (a, b) {
        (Some(x), Some(y)) => eq_bytes(x, y),
        (None, None) => true,
        _ => false,
    }
}

/// A stream's receiving part fails only with constant codes.
proof fn lemma_recv_err(id: u64, window: u64, t: Seq<SpecRecvIn>)
    ensures
        rfc_recv(id, window, t).err matches Some(c) ==> c <= VARINT_MAX,
    decreases t.len(),
{
    if t.len() > 0 {
        lemma_recv_err(id, window, t.drop_last());
    }
}

/// `Streams::on_frame`'s error codes are in range.
proof fn lemma_frame_err(s0: Streams, f: SpecFrame, r: Result<(), u64>)
    requires
        r == match rfc_stream_frame_check(s0.ids_spec(), f) {
            Some(c) => Err(c),
            None => rx_outcome(s0, f),
        },
    ensures
        r matches Err(c) ==> c <= VARINT_MAX,
{
    if let (Some(id), Some(i)) = (frame_stream_id(f), frame_recv_in(f)) {
        lemma_recv_err(id, s0.rx_window(id), s0.rx_trace(id).push(i));
    }
}

/// Nothing is logged on a path absent from the log.
proof fn lemma_log_sends_absent(log: Seq<SpecOutDatagram>, q: PathId)
    requires
        forall|i: int| 0 <= i < log.len() ==> (#[trigger] log[i]).path != q,
    ensures
        log_sends(log, q) == Seq::<nat>::empty(),
    decreases log.len(),
{
    if log.len() > 0 {
        assert(log[log.len() - 1].path != q);
        assert forall|i: int| 0 <= i < log.drop_last().len() implies (#[trigger] log.drop_last()[i]).path != q by {
            assert(log.drop_last()[i] == log[i]);
        }
        lemma_log_sends_absent(log.drop_last(), q);
    }
}

/// The PATH_CHALLENGE frames of `s`.
closed spec fn count_ch(s: Seq<Frame>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        count_ch(s.drop_last()) + if s.last() is PathChallenge {
            1nat
        } else {
            0
        }
    }
}

/// The PATH_CHALLENGE frames in `frames`.
#[verifier::spinoff_prover]
fn count_challenges(frames: &[Frame]) -> (r: usize)
    ensures
        r == count_ch(frames@),
{
    let mut n: usize = 0;
    let mut i: usize = 0;
    while i < frames.len()
        invariant
            n <= i <= frames@.len(),
            n == count_ch(frames@.take(i as int)),
        decreases frames@.len() - i,
    {
        proof {
            assert(frames@.take(i + 1).drop_last() =~= frames@.take(i as int));
        }
        if matches!(frames[i], Frame::PathChallenge(_)) {
            n += 1;
        }
        i += 1;
    }
    proof {
        assert(frames@.take(i as int) =~= frames@);
    }
    n
}

/// §9.1: some frame is not a probing frame.
#[verifier::spinoff_prover]
fn has_non_probing(frames: &[Frame]) -> (r: bool)
    ensures
        r == exists|i: int|
            #![trigger frames@[i]]
            0 <= i < frames@.len() && !(frames@[i] is PathChallenge || frames@[i] is PathResponse
                || frames@[i] is NewConnectionId || frames@[i] is Padding),
{
    let mut i: usize = 0;
    while i < frames.len()
        invariant
            i <= frames@.len(),
            forall|j: int|
                #![trigger frames@[j]]
                0 <= j < i ==> frames@[j] is PathChallenge || frames@[j] is PathResponse
                    || frames@[j] is NewConnectionId || frames@[j] is Padding,
        decreases frames@.len() - i,
    {
        if !matches!(
            frames[i],
            Frame::PathChallenge(_) | Frame::PathResponse(_) | Frame::NewConnectionId { .. } | Frame::Padding
        ) {
            return true;
        }
        i += 1;
    }
    false
}

/// The STREAM frame covering the run of adjacent STREAM frames of one stream that starts at
/// `frames[j]`, FIN from the last, and the index after the run; None when no frame follows on
/// from `frames[j]`, so a lone frame costs no copy. The copy is at most one record's bytes.
/// Public for its test only: no record exists before Task 2a-i.
#[doc(hidden)]
#[verifier::spinoff_prover]
pub fn stream_run(frames: &[Frame], j: usize) -> (r: Option<(Frame, usize)>)
    requires
        j < frames@.len(),
    ensures
        r matches Some((_, e)) ==> j < e <= frames@.len(),
{
    let (id, off, first, mut last_fin) = match &frames[j] {
        Frame::Stream { stream_id, offset, data, fin } => (*stream_id, *offset, data, *fin),
        _ => return None,
    };
    if first.len() as u64 > u64::MAX - off {
        return None;
    }
    let mut next = off + first.len() as u64;
    let mut run: Vec<u8> = Vec::new();
    let mut e = j + 1;
    while e < frames.len()
        invariant
            j < e <= frames@.len(),
        decreases frames@.len() - e,
    {
        match &frames[e] {
            Frame::Stream { stream_id, offset, data, fin } => {
                if *stream_id != id || *offset != next || data.len() as u64 > u64::MAX - next {
                    break;
                }
                if e == j + 1 {
                    run.extend_from_slice(first.as_slice());
                }
                run.extend_from_slice(data.as_slice());
                next = next + data.len() as u64;
                last_fin = *fin;
            },
            _ => break,
        }
        e += 1;
    }
    if e == j + 1 {
        return None;
    }
    Some((Frame::Stream { stream_id: id, offset: off, data: run, fin: last_fin }, e))
}

/// `TransportParams` derives no `Clone`.
fn copy_tp(t: &TransportParams) -> (r: TransportParams)
    ensures
        r@ == t@,
{
    TransportParams {
        original_destination_connection_id: copy_opt(&t.original_destination_connection_id),
        max_idle_timeout: t.max_idle_timeout,
        stateless_reset_token: t.stateless_reset_token,
        max_udp_payload_size: t.max_udp_payload_size,
        initial_max_data: t.initial_max_data,
        initial_max_stream_data_bidi_local: t.initial_max_stream_data_bidi_local,
        initial_max_stream_data_bidi_remote: t.initial_max_stream_data_bidi_remote,
        initial_max_stream_data_uni: t.initial_max_stream_data_uni,
        initial_max_streams_bidi: t.initial_max_streams_bidi,
        initial_max_streams_uni: t.initial_max_streams_uni,
        ack_delay_exponent: t.ack_delay_exponent,
        max_ack_delay: t.max_ack_delay,
        disable_active_migration: t.disable_active_migration,
        active_connection_id_limit: t.active_connection_id_limit,
        initial_source_connection_id: copy_opt(&t.initial_source_connection_id),
    }
}

fn copy_opt(o: &Option<Vec<u8>>) -> (r: Option<Vec<u8>>)
    ensures
        opt_view(r) == opt_view(*o),
{
    match o {
        Some(v) => Some(slice_to_vec(v.as_slice())),
        None => None,
    }
}

#[verifier::spinoff_prover]
fn has_token(v: &Vec<[u8; 16]>, t: &[u8; 16]) -> (r: bool)
    ensures
        r == v@.contains(*t),
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v@.len(),
            forall|j: int| 0 <= j < i ==> v@[j] != *t,
        decreases v@.len() - i,
    {
        let x = v[i];
        if eq_bytes(x.as_slice(), t.as_slice()) {
            proof {
                assert(x =~= *t);
                assert(v@[i as int] == *t);
            }
            return true;
        }
        i += 1;
    }
    false
}

/// A `RemoveToken` for every token of `reg` that `used` lacks, and for no other.
#[verifier::spinoff_prover]
fn push_removes(reg: &Vec<[u8; 16]>, used: &Vec<[u8; 16]>, out: &mut Vec<CidUpdate>)
    ensures
        final(out)@.len() >= old(out)@.len(),
        forall|i: int| 0 <= i < old(out)@.len() ==> #[trigger] final(out)@[i] == old(out)@[i],
        forall|i: int|
            old(out)@.len() <= i < final(out)@.len() ==> (
            #[trigger] final(out)@[i] matches CidUpdate::RemoveToken(t) && reg@.contains(t)
                && !used@.contains(t)),
        forall|i: int|
            0 <= i < reg@.len() && !used@.contains(reg@[i]) ==> exists|w: int|
                old(out)@.len() <= w < final(out)@.len() && #[trigger] final(out)@[w]
                    == CidUpdate::RemoveToken(#[trigger] reg@[i]),
{
    let ghost s0 = out@;
    let mut i: usize = 0;
    while i < reg.len()
        invariant
            i <= reg@.len(),
            out@.len() >= s0.len(),
            forall|k: int| 0 <= k < s0.len() ==> #[trigger] out@[k] == s0[k],
            forall|k: int|
                s0.len() <= k < out@.len() ==> (#[trigger] out@[k] matches CidUpdate::RemoveToken(t)
                    && reg@.contains(t) && !used@.contains(t)),
            forall|k: int|
                0 <= k < i && !used@.contains(reg@[k]) ==> exists|w: int|
                    s0.len() <= w < out@.len() && #[trigger] out@[w] == CidUpdate::RemoveToken(
                        #[trigger] reg@[k],
                    ),
        decreases reg@.len() - i,
    {
        let t = reg[i];
        proof {
            assert(reg@[i as int] == t);
        }
        if !has_token(used, &t) {
            let ghost o = out@;
            out.push(CidUpdate::RemoveToken(t));
            proof {
                assert(out@[o.len() as int] == CidUpdate::RemoveToken(t));
                assert forall|k: int| s0.len() <= k < out@.len() implies (
                #[trigger] out@[k] matches CidUpdate::RemoveToken(x) && reg@.contains(x)
                    && !used@.contains(x)) by {
                    if k < o.len() {
                        assert(out@[k] == o[k]);
                    }
                }
                assert forall|k: int|
                    0 <= k < i + 1 && !used@.contains(reg@[k]) implies exists|w: int|
                    s0.len() <= w < out@.len() && #[trigger] out@[w] == CidUpdate::RemoveToken(
                        #[trigger] reg@[k],
                    ) by {
                    if k < i {
                        let w = choose|w: int|
                            s0.len() <= w < o.len() && #[trigger] o[w] == CidUpdate::RemoveToken(
                                reg@[k],
                            );
                        assert(out@[w] == o[w]);
                    } else {
                        assert(out@[o.len() as int] == CidUpdate::RemoveToken(reg@[k]));
                    }
                }
            }
        }
        i += 1;
    }
}

/// An `AddToken` for every token of `used` that `reg` lacks, and for no other.
#[verifier::spinoff_prover]
fn push_adds(reg: &Vec<[u8; 16]>, used: &Vec<[u8; 16]>, out: &mut Vec<CidUpdate>)
    ensures
        final(out)@.len() >= old(out)@.len(),
        forall|i: int| 0 <= i < old(out)@.len() ==> #[trigger] final(out)@[i] == old(out)@[i],
        forall|i: int|
            old(out)@.len() <= i < final(out)@.len() ==> (
            #[trigger] final(out)@[i] matches CidUpdate::AddToken(t) && used@.contains(t)
                && !reg@.contains(t)),
        forall|i: int|
            0 <= i < used@.len() && !reg@.contains(used@[i]) ==> exists|w: int|
                old(out)@.len() <= w < final(out)@.len() && #[trigger] final(out)@[w]
                    == CidUpdate::AddToken(#[trigger] used@[i]),
{
    let ghost s0 = out@;
    let mut i: usize = 0;
    while i < used.len()
        invariant
            i <= used@.len(),
            out@.len() >= s0.len(),
            forall|k: int| 0 <= k < s0.len() ==> #[trigger] out@[k] == s0[k],
            forall|k: int|
                s0.len() <= k < out@.len() ==> (#[trigger] out@[k] matches CidUpdate::AddToken(t)
                    && used@.contains(t) && !reg@.contains(t)),
            forall|k: int|
                0 <= k < i && !reg@.contains(used@[k]) ==> exists|w: int|
                    s0.len() <= w < out@.len() && #[trigger] out@[w] == CidUpdate::AddToken(
                        #[trigger] used@[k],
                    ),
        decreases used@.len() - i,
    {
        let t = used[i];
        proof {
            assert(used@[i as int] == t);
        }
        if !has_token(reg, &t) {
            let ghost o = out@;
            out.push(CidUpdate::AddToken(t));
            proof {
                assert(out@[o.len() as int] == CidUpdate::AddToken(t));
                assert forall|k: int| s0.len() <= k < out@.len() implies (
                #[trigger] out@[k] matches CidUpdate::AddToken(x) && used@.contains(x)
                    && !reg@.contains(x)) by {
                    if k < o.len() {
                        assert(out@[k] == o[k]);
                    }
                }
                assert forall|k: int|
                    0 <= k < i + 1 && !reg@.contains(used@[k]) implies exists|w: int|
                    s0.len() <= w < out@.len() && #[trigger] out@[w] == CidUpdate::AddToken(
                        #[trigger] used@[k],
                    ) by {
                    if k < i {
                        let w = choose|w: int|
                            s0.len() <= w < o.len() && #[trigger] o[w] == CidUpdate::AddToken(
                                used@[k],
                            );
                        assert(out@[w] == o[w]);
                    } else {
                        assert(out@[o.len() as int] == CidUpdate::AddToken(used@[k]));
                    }
                }
            }
        }
        i += 1;
    }
}

} // verus!

impl Connection {
    /// Test support: the allocated capacity of space `k`'s CRYPTO buffers. Verus models `Vec`
    /// length, not capacity (TRUSTED.md).
    #[doc(hidden)]
    pub fn crypto_capacity(&self, k: PacketKind) -> usize {
        let (c, tx) = match k {
            PacketKind::Initial => (self.crx_i.capacities(), self.ctx_i.buf_capacity()),
            PacketKind::Handshake => (self.crx_h.capacities(), self.ctx_h.buf_capacity()),
            PacketKind::OneRtt => (self.crx_1.capacities(), 0),
        };
        c.0.saturating_add(c.1).saturating_add(tx)
    }

    /// Test support: the amplification budget of `q`, None when absent (the only reading of a
    /// path's receive count before `poll_transmit` exists).
    #[doc(hidden)]
    pub fn path_budget(&self, q: PathId) -> Option<u64> {
        self.paths.index(q).map(|_| self.paths.budget(q))
    }
}
