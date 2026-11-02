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

use crate::ack_track::*;
use crate::cid::*;
use crate::codes::*;
use crate::crypto_stream::*;
use crate::datagram::*;
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

// =============================================================================
// The connection
// =============================================================================

/// One server connection.
pub struct Connection {
    now: u64,
    #[allow(dead_code)]  // Read from Task 1a-ii.
    hs_path: PathId,
    ids: HandshakeIds,
    local_tp: TransportParams,
    peer_tp: Option<TransportParams>,
    paths: Paths,
    lc: Lifecycle,
    #[allow(dead_code)]  // Read from Task 1a-ii.
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
    #[allow(dead_code)]  // Read from Task 1b.
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
        &&& self.chal_used <= 4
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

    /// The active path has a DCID, every DCID is still active (§5.1.2 "MUST stop using"), and
    /// §9.5: two paths share a DCID only if the peer used the same CID on both (its MAY: the
    /// peer used the same CID from a new address, NAT rebinding).
    closed spec fn wf_dcids(&self) -> bool {
        &&& self.paths.path(self.paths.active_spec()).dcid is Some
        &&& forall|q: PathId| #[trigger]
            self.paths.has(q) ==> (self.paths.path(q).dcid matches Some(c) ==> peer_has_cid(
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
    // Receive (Task 1a-ii writes the body)
    // =========================================================================

    /// A datagram of `datagram_len` bytes on `path`, with its decrypted packets in order.
    #[allow(unused_variables)]  // Task 1a-ii writes the body.
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
        if self.peer_tp.is_none() || self.streams.is_none() {
            self.close_internal(INTERNAL_ERROR);
            return;
        }
        if let Err(c) = check_alpn(alpn) {
            self.close_internal(c);
            return;
        }
        self.complete = true;
        self.discard(PacketKind::Initial);
        self.discard(PacketKind::Handshake);
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
            forall|i: int|
                0 <= i < old(self).registered().len() && !final(self).registered().contains(
                    old(self).registered()[i],
                ) ==> final(out)@.contains(
                    CidUpdate::RemoveToken(#[trigger] old(self).registered()[i]),
                ),
            forall|i: int|
                0 <= i < final(self).registered().len() && !old(self).registered().contains(
                    final(self).registered()[i],
                ) ==> final(out)@.contains(
                    CidUpdate::AddToken(#[trigger] final(self).registered()[i]),
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
            assert forall|i: int| 0 <= i < regs.len() && !used@.contains(regs[i]) implies s2.contains(
                CidUpdate::RemoveToken(#[trigger] regs[i]),
            ) by {
                let w = choose|w: int|
                    0 <= w < s1.len() && s1[w] == CidUpdate::RemoveToken(regs[i]);
                assert(s2[w] == s1[w]);
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

/// A `RemoveToken` for every token of `reg` that `used` lacks.
fn push_removes(reg: &Vec<[u8; 16]>, used: &Vec<[u8; 16]>, out: &mut Vec<CidUpdate>)
    ensures
        final(out)@.len() >= old(out)@.len(),
        forall|i: int| 0 <= i < old(out)@.len() ==> #[trigger] final(out)@[i] == old(out)@[i],
        forall|i: int|
            old(out)@.len() <= i < final(out)@.len() ==> #[trigger] final(out)@[i] is RemoveToken,
        forall|i: int|
            0 <= i < reg@.len() && !used@.contains(reg@[i]) ==> final(out)@.contains(
                CidUpdate::RemoveToken(#[trigger] reg@[i]),
            ),
{
    let ghost s0 = out@;
    let mut i: usize = 0;
    while i < reg.len()
        invariant
            i <= reg@.len(),
            out@.len() >= s0.len(),
            forall|k: int| 0 <= k < s0.len() ==> #[trigger] out@[k] == s0[k],
            forall|k: int| s0.len() <= k < out@.len() ==> #[trigger] out@[k] is RemoveToken,
            forall|k: int|
                0 <= k < i && !used@.contains(reg@[k]) ==> out@.contains(
                    CidUpdate::RemoveToken(#[trigger] reg@[k]),
                ),
        decreases reg@.len() - i,
    {
        let t = reg[i];
        if !has_token(used, &t) {
            let ghost o = out@;
            out.push(CidUpdate::RemoveToken(t));
            proof {
                assert(out@[o.len() as int] == CidUpdate::RemoveToken(t));
                assert forall|k: int|
                    0 <= k < i + 1 && !used@.contains(reg@[k]) implies out@.contains(
                    CidUpdate::RemoveToken(#[trigger] reg@[k]),
                ) by {
                    if k < i {
                        let w = choose|w: int|
                            0 <= w < o.len() && o[w] == CidUpdate::RemoveToken(reg@[k]);
                        assert(out@[w] == o[w]);
                    }
                }
            }
        }
        i += 1;
    }
}

/// An `AddToken` for every token of `used` that `reg` lacks.
fn push_adds(reg: &Vec<[u8; 16]>, used: &Vec<[u8; 16]>, out: &mut Vec<CidUpdate>)
    ensures
        final(out)@.len() >= old(out)@.len(),
        forall|i: int| 0 <= i < old(out)@.len() ==> #[trigger] final(out)@[i] == old(out)@[i],
        forall|i: int|
            old(out)@.len() <= i < final(out)@.len() ==> #[trigger] final(out)@[i] is AddToken,
        forall|i: int|
            0 <= i < used@.len() && !reg@.contains(used@[i]) ==> final(out)@.contains(
                CidUpdate::AddToken(#[trigger] used@[i]),
            ),
{
    let ghost s0 = out@;
    let mut i: usize = 0;
    while i < used.len()
        invariant
            i <= used@.len(),
            out@.len() >= s0.len(),
            forall|k: int| 0 <= k < s0.len() ==> #[trigger] out@[k] == s0[k],
            forall|k: int| s0.len() <= k < out@.len() ==> #[trigger] out@[k] is AddToken,
            forall|k: int|
                0 <= k < i && !reg@.contains(used@[k]) ==> out@.contains(
                    CidUpdate::AddToken(#[trigger] used@[k]),
                ),
        decreases used@.len() - i,
    {
        let t = used[i];
        if !has_token(reg, &t) {
            let ghost o = out@;
            out.push(CidUpdate::AddToken(t));
            proof {
                assert(out@[o.len() as int] == CidUpdate::AddToken(t));
                assert forall|k: int|
                    0 <= k < i + 1 && !reg@.contains(used@[k]) implies out@.contains(
                    CidUpdate::AddToken(#[trigger] used@[k]),
                ) by {
                    if k < i {
                        let w = choose|w: int|
                            0 <= w < o.len() && o[w] == CidUpdate::AddToken(used@[k]);
                        assert(out@[w] == o[w]);
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
}
