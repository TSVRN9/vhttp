//! The server's QUIC connection (RFC 9000): one `Connection` joins the packet number spaces,
//! CRYPTO streams, `Streams`, connection IDs, paths and lifecycle. Sans-IO: the shell hands in
//! decrypted packets, datagram sizes, times and randomness, and the TLS calls below.
//!
//! Caller obligations, which `Connection` cannot state as `requires`:
//! - Drain `poll_stream_events` after every `on_datagram`: `events` is bounded only by that.
//!   `H3Server::pump` discharges this; 3e drives `Connection` before any stream exists.
//! - After `on_timeout(now)`, poll `poll_transmit` to None before sleeping until `next_timeout`:
//!   `settled_later` proves that timer is then later than `now`, so the sleep cannot spin. That the
//!   poll loop ends is not proved, so cap the polls per wake, as the tests' `drain` does at 1024.
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
use crate::pn::*;
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

/// The reason phrase a close keeps: its first 64 bytes (`Lifecycle::enter_closing`'s cap).
pub open spec fn reason_cap(r: Seq<u8>) -> Seq<u8> {
    r.take(if r.len() > 64 { 64int } else { r.len() as int })
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
    /// Post-handshake CRYPTO: the 4c glue reads it, and any byte is unexpected_message (0x10a).
    crx_1: CryptoStream,
    ctx_i: SendStream,
    ctx_h: SendStream,
    streams: Option<Streams>,
    events: Vec<StreamEvent>,
    local_cids: LocalCids,
    peer_cids: PeerCids,
    cid_updates: Vec<CidUpdate>,
    tokens_registered: Vec<[u8; 16]>,
    hs_done: HsDone,
    probe_i: bool,
    probe_h: bool,
    probe_1: bool,
    spin: bool,
    /// Challenge slices of `rand` used in this call; every pub fn that draws one resets it.
    chal_used: usize,
    /// Only `wf` and `out_log()` read it, which a plain `cargo build` erases.
    #[allow(dead_code)]
    out_log: Ghost<Seq<SpecOutDatagram>>,
    /// The frames the latest `poll_transmit` took from `Streams::poll_frames` (P8).
    #[allow(dead_code)]
    polled: Ghost<Seq<SpecFrame>>,
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

    /// The end of the received CRYPTO data at level `k` (RFC 9001 §4.1.3), kept for Initial
    /// across its discard.
    pub closed spec fn crypto_end_spec(&self, k: PacketKind) -> nat {
        let s = match k {
            PacketKind::Initial => self.crx_i,
            PacketKind::Handshake => self.crx_h,
            PacketKind::OneRtt => self.crx_1,
        };
        (s.base_spec() + s.buf_len_spec()) as nat
    }

    /// Level `k`'s CRYPTO stream.
    spec fn crx_spec(&self, k: PacketKind) -> CryptoStream {
        match k {
            PacketKind::Initial => self.crx_i,
            PacketKind::Handshake => self.crx_h,
            PacketKind::OneRtt => self.crx_1,
        }
    }

    /// How far level `k`'s CRYPTO data has been read (`crypto_read`).
    pub closed spec fn crypto_base_spec(&self, k: PacketKind) -> nat {
        match k {
            PacketKind::Initial => self.crx_i.base_spec(),
            PacketKind::Handshake => self.crx_h.base_spec(),
            PacketKind::OneRtt => self.crx_1.base_spec(),
        }
    }

    /// The end of level `k`'s in-order CRYPTO data (`crypto_contiguous`).
    pub closed spec fn crypto_contiguous_spec(&self, k: PacketKind) -> nat {
        match k {
            PacketKind::Initial => crypto_contiguous(self.crx_i),
            PacketKind::Handshake => crypto_contiguous(self.crx_h),
            PacketKind::OneRtt => crypto_contiguous(self.crx_1),
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9001#section-4.1.3
    //# *  If the packet is from a previously installed encryption level, it
    //# MUST NOT contain data that extends past the end of previously
    //# received data in that flow.
    /// Byte `p` of level `k`'s CRYPTO stream arrived in a CRYPTO frame. The Initial record
    /// survives the space's discard (`CryptoStream::restart`).
    pub closed spec fn crypto_received(&self, k: PacketKind, p: nat) -> bool {
        match k {
            PacketKind::Initial => self.crx_i.received(p),
            PacketKind::Handshake => self.crx_h.received(p),
            PacketKind::OneRtt => self.crx_1.received(p),
        }
    }

    /// The Initial CRYPTO read offset has not gone back since `o`: with `crypto_read`'s drain,
    /// what quictls reads when TLS leaves Initial stays read (RFC 9001 §4.1.3). Nor has the
    /// handshake's completion been undone. Nor have the peer's transport parameters appeared:
    /// only `on_peer_params` sets them (it ensures `crypto_kept_base`).
    pub closed spec fn crypto_kept(&self, o: Connection) -> bool {
        &&& self.crypto_kept_base(o)
        &&& self.peer_tp is Some ==> o.peer_tp is Some
    }

    /// `crypto_kept` without the transport-parameters frame.
    pub closed spec fn crypto_kept_base(&self, o: Connection) -> bool {
        self.crypto_kept_but(o, None)
    }

    /// The frame of `crypto_kept_base`, but level `skip`'s read offset may move (`crypto_read`):
    /// the Initial offset and end do not go back, the Initial history only grows, completion is
    /// not undone, the connection does not reopen, no space comes back, and while open the read
    /// offset of a live Initial or Handshake space other than `skip` stays where it was.
    pub closed spec fn crypto_kept_but(&self, o: Connection, skip: Option<PacketKind>) -> bool {
        &&& self.crypto_base_spec(PacketKind::Initial) >= o.crypto_base_spec(PacketKind::Initial)
        &&& self.crypto_end_spec(PacketKind::Initial) >= o.crypto_end_spec(PacketKind::Initial)
        &&& o.complete ==> self.complete
        &&& forall|p: nat| #[trigger] o.crx_i.received(p) ==> self.crx_i.received(p)
        &&& self.lc.phase_spec() is Open ==> o.lc.phase_spec() is Open
        &&& self.live_i ==> o.live_i
        &&& self.live_h ==> o.live_h
        &&& skip != Some(PacketKind::Initial) && self.lc.phase_spec() is Open && self.live_i ==> self.crx_i.base_spec()
            == o.crx_i.base_spec()
        &&& skip != Some(PacketKind::Handshake) && self.lc.phase_spec() is Open && self.live_h ==> self.crx_h.base_spec()
            == o.crx_h.base_spec()
    }

    /// The three CRYPTO streams, and the handshake's completion, are as in `o`; no transport
    /// parameters appeared.
    pub closed spec fn crypto_same(&self, o: Connection) -> bool {
        &&& self.crx_i == o.crx_i
        &&& self.crx_h == o.crx_h
        &&& self.crx_1 == o.crx_1
        &&& self.complete == o.complete
        &&& self.peer_tp is Some ==> o.peer_tp is Some
        &&& self.live_i == o.live_i
        &&& self.live_h == o.live_h
        &&& self.lc.phase_spec() is Open ==> o.lc.phase_spec() is Open
    }

    /// A level whose space is discarded or not yet live holds no unread in-order byte: its packets
    /// never reach `on_crypto_frame`. After completion Initial and Handshake are discarded.
    pub proof fn lemma_dead_drained(c: Connection)
        requires
            c.wf(),
        ensures
            forall|k: PacketKind| !c.live(k) ==> #[trigger] crypto_drained(c, k),
            c.live(PacketKind::OneRtt) ==> !c.live(PacketKind::Initial) && !c.live(PacketKind::Handshake),
            // A discarded Initial space buffers nothing: its read offset is its end.
            !c.live(PacketKind::Initial) ==> c.crypto_base_spec(PacketKind::Initial) == c.crypto_end_spec(PacketKind::Initial),
    {
        reveal(crx_ok);
    }

    pub proof fn lemma_crypto_kept_refl(c: Connection)
        ensures
            c.crypto_kept(c),
    {
    }

    pub proof fn lemma_crypto_kept_trans(a: Connection, b: Connection, c: Connection)
        requires
            b.crypto_kept(a),
            c.crypto_kept(b),
        ensures
            c.crypto_kept(a),
    {
    }

    pub proof fn lemma_crypto_kept_to_base(c: Connection, o: Connection)
        requires
            c.crypto_kept(o),
        ensures
            c.crypto_kept_base(o),
    {
    }

    pub proof fn lemma_crypto_kept_base_elim(c: Connection, o: Connection)
        requires
            c.crypto_kept_base(o),
        ensures
            c.crypto_base_spec(PacketKind::Initial) >= o.crypto_base_spec(PacketKind::Initial),
            o.live(PacketKind::OneRtt) ==> c.live(PacketKind::OneRtt),
            forall|p: nat| #[trigger] o.crypto_received(PacketKind::Initial, p) ==> c.crypto_received(PacketKind::Initial, p),
            c.crypto_end_spec(PacketKind::Initial) >= o.crypto_end_spec(PacketKind::Initial),
            c.phase_spec() is Open ==> o.phase_spec() is Open,
            c.live(PacketKind::Initial) ==> o.live(PacketKind::Initial),
            c.live(PacketKind::Handshake) ==> o.live(PacketKind::Handshake),
            c.phase_spec() is Open && c.live(PacketKind::Initial) ==> c.crypto_base_spec(PacketKind::Initial) == o.crypto_base_spec(
                PacketKind::Initial,
            ),
            c.phase_spec() is Open && c.live(PacketKind::Handshake) ==> c.crypto_base_spec(PacketKind::Handshake)
                == o.crypto_base_spec(PacketKind::Handshake),
    {
    }

    /// What `crypto_kept_but` says, in terms quictls can read.
    pub proof fn lemma_crypto_kept_but_elim(c: Connection, o: Connection, skip: Option<PacketKind>)
        requires
            c.crypto_kept_but(o, skip),
        ensures
            c.crypto_base_spec(PacketKind::Initial) >= o.crypto_base_spec(PacketKind::Initial),
            c.crypto_end_spec(PacketKind::Initial) >= o.crypto_end_spec(PacketKind::Initial),
            o.live(PacketKind::OneRtt) ==> c.live(PacketKind::OneRtt),
            forall|p: nat| #[trigger] o.crypto_received(PacketKind::Initial, p) ==> c.crypto_received(PacketKind::Initial, p),
            c.phase_spec() is Open ==> o.phase_spec() is Open,
            c.live(PacketKind::Initial) ==> o.live(PacketKind::Initial),
            c.live(PacketKind::Handshake) ==> o.live(PacketKind::Handshake),
            skip != Some(PacketKind::Initial) && c.phase_spec() is Open && c.live(PacketKind::Initial) ==> c.crypto_base_spec(
                PacketKind::Initial,
            ) == o.crypto_base_spec(PacketKind::Initial),
            skip != Some(PacketKind::Handshake) && c.phase_spec() is Open && c.live(PacketKind::Handshake) ==> c.crypto_base_spec(
                PacketKind::Handshake,
            ) == o.crypto_base_spec(PacketKind::Handshake),
    {
    }

    pub proof fn lemma_crypto_kept_elim(c: Connection, o: Connection)
        requires
            c.crypto_kept(o),
        ensures
            c.crypto_base_spec(PacketKind::Initial) >= o.crypto_base_spec(PacketKind::Initial),
            o.live(PacketKind::OneRtt) ==> c.live(PacketKind::OneRtt),
            c.peer_tp_known_spec() ==> o.peer_tp_known_spec(),
            // RFC 9001 §4.1.3's "previously received data" only grows.
            forall|p: nat| #[trigger] o.crypto_received(PacketKind::Initial, p) ==> c.crypto_received(PacketKind::Initial, p),
            c.crypto_end_spec(PacketKind::Initial) >= o.crypto_end_spec(PacketKind::Initial),
            c.phase_spec() is Open ==> o.phase_spec() is Open,
            c.live(PacketKind::Initial) ==> o.live(PacketKind::Initial),
            c.live(PacketKind::Handshake) ==> o.live(PacketKind::Handshake),
            c.phase_spec() is Open && c.live(PacketKind::Initial) ==> c.crypto_base_spec(PacketKind::Initial) == o.crypto_base_spec(
                PacketKind::Initial,
            ),
            c.phase_spec() is Open && c.live(PacketKind::Handshake) ==> c.crypto_base_spec(PacketKind::Handshake)
                == o.crypto_base_spec(PacketKind::Handshake),
    {
    }

    /// The client's original Destination Connection ID.
    pub closed spec fn odcid_spec(&self) -> Seq<u8> {
        self.ids@.odcid
    }

    pub closed spec fn phase_spec(&self) -> Phase {
        self.lc.phase_spec()
    }

    /// The close being sent: application or transport, code, reason.
    pub closed spec fn close_spec(&self) -> Option<(bool, u64, Seq<u8>)> {
        self.lc.close_spec()
    }

    /// The Source Connection ID of the client's first Initial.
    pub closed spec fn client_scid_spec(&self) -> Seq<u8> {
        self.ids@.client_scid
    }

    /// TLS has delivered the client's transport parameters and they were accepted.
    pub closed spec fn peer_tp_known_spec(&self) -> bool {
        self.peer_tp is Some
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
        &&& crx_ok(self.crx_i, self.crx_h, self.crx_1, self.live_i, self.live_h, self.complete)
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
            r matches Some(c) ==> c.odcid_spec() == first.dcid@,
            //= https://www.rfc-editor.org/rfc/rfc9000#section-7.3
            //# a mismatch between values received from a peer in these transport
            //# parameters and the value sent in the corresponding Destination or
            //# Source Connection ID fields of Initial packets.
            // The value `on_peer_params` checks initial_source_connection_id against: the Source
            // Connection ID field of the client's first Initial.
            r matches Some(c) ==> c.client_scid_spec() == first.scid@,
            // No transport parameters yet: TLS delivers them later (`on_peer_params`).
            r matches Some(c) ==> !c.peer_tp_known_spec(),
            r matches Some(c) ==> c.crypto_base_spec(PacketKind::Initial) == 0 && c.crypto_base_spec(PacketKind::Handshake) == 0,
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
            polled: Ghost(Seq::empty()),
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
                reveal(crx_ok);
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
        &&& self.crypto_kept(o)
    }

    /// What `gate_packet` accepts. Biconditional, so what is absent is proved absent: no size rule
    /// on 1-RTT (§8.2.1's MUST NOT). An absent path has all its response room.
    pub closed spec fn gate_spec(&self, path: PathId, len: usize, p: &PlainPacket) -> bool {
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

    //= https://www.rfc-editor.org/rfc/rfc9000#section-12.2
    //# For example, if decryption fails (because the keys are
    //# not available or for any other reason), the receiver MAY either
    //# discard or buffer the packet for later processing and MUST attempt to
    //# process the remaining packets.
    /// A datagram of `datagram_len` bytes on `path`, with its decrypted packets in order: 3e discards
    /// a packet it cannot decrypt and hands over the rest. `error` is the connection error that
    /// stopped the datagram, with its packet's header (frames empty): after the packets, it closes
    /// the connection only if that header passes the gate a packet would (`close_on_error`).
    #[verifier::spinoff_prover]
    pub fn on_datagram(
        &mut self,
        path: PathId,
        datagram_len: usize,
        packets: Vec<PlainPacket>,
        error: Option<(u64, PlainPacket)>,
        now: u64,
        rand: &[u8; RAND_LEN],
    )
        requires
            old(self).wf(),
            forall|i: int| 0 <= i < packets@.len() ==> plain_wf(#[trigger] packets@[i]@),
            error matches Some((c, h)) ==> c <= VARINT_MAX && plain_wf(h@),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            final(self).crypto_kept(*old(self)),
            // §8.1: a datagram on a known path is counted, and nothing after undoes the count.
            old(self).has_path(path) && !(old(self).phase_spec() is Draining) && !(old(
                self,
            ).phase_spec() is Closed) ==> recv_counted(
                old(self).amp_trace(path),
                final(self).amp_trace(path),
                datagram_len as nat,
            ),
            // An error alone: it closes the connection iff its header passes the gate.
            packets@.len() == 0 && old(self).phase_spec() is Open ==> (error matches Some((_, h)) && old(
                self,
            ).gate_spec(path, datagram_len, &h) && old(self).has_path(path) ==> final(self).phase_spec() is Closing),
            packets@.len() == 0 && old(self).phase_spec() is Open ==> (!(error matches Some((_, h))
                && old(self).gate_spec(path, datagram_len, &h)) ==> final(self).phase_spec() is Open),
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
        let known = self.paths.index(path).is_some();
        if known {
            // §8.1: counted even if every packet is dropped.
            self.count_recv(path, datagram_len as u64);
        }
        let ghost sc = *self;
        self.on_counted(path, datagram_len, known, packets, error, rand);
        proof {
            reveal(recv_counted);
            if known {
                let t0 = old(self).paths.amp_trace(path);
                assert(self.paths.amp_trace(path).take(t0.len() + 1 as int) =~= t0.push(AmpEv::Recv(datagram_len as nat))) by {
                    assert(sc.paths.has(path));
                    assert(sc.paths.amp_trace(path) == t0.push(AmpEv::Recv(datagram_len as nat)));
                }
            }
        }
    }

    /// `on_datagram` once the datagram is counted: `known` is whether `path` was in the table.
    #[verifier::spinoff_prover]
    fn on_counted(
        &mut self,
        path: PathId,
        datagram_len: usize,
        known: bool,
        packets: Vec<PlainPacket>,
        error: Option<(u64, PlainPacket)>,
        rand: &[u8; RAND_LEN],
    )
        requires
            old(self).wf(),
            !(old(self).phase_spec() is Draining) && !(old(self).phase_spec() is Closed),
            known == old(self).paths.has(path),
            forall|i: int| 0 <= i < packets@.len() ==> plain_wf(#[trigger] packets@[i]@),
            error matches Some((c, h)) ==> c <= VARINT_MAX && plain_wf(h@),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            final(self).amp_grew(*old(self)),
            final(self).crypto_kept(*old(self)),
            packets@.len() == 0 && old(self).phase_spec() is Open ==> (error matches Some((_, h)) && old(
                self,
            ).gate_spec(path, datagram_len, &h) && old(self).paths.has(path) ==> final(self).phase_spec() is Closing),
            packets@.len() == 0 && old(self).phase_spec() is Open ==> (!(error matches Some((_, h))
                && old(self).gate_spec(path, datagram_len, &h)) ==> *final(self) == *old(self)),
    {
        let mut known = known;
        proof {
            self.lemma_grew_same(*self);
        }
        if matches!(self.lc.phase(), Phase::Closing) {
            // §10.2.1: packets are not processed.
            if known {
                self.lc.on_recv_closing(datagram_len as u64);
            }
            proof {
                self.lemma_grew_same(*old(self));
            }
            return;
        }
        let ghost np = packets@.len();
        // §12.2: the first packet's DCID, even if the gate drops that packet.
        let first = if packets.len() > 0 {
            slice_to_vec(packets[0].dcid.as_slice())
        } else {
            match &error {
                Some((_, h)) => slice_to_vec(h.dcid.as_slice()),
                None => return ,
            }
        };
        let ghost s1 = *self;
        let now = self.now;
        //= https://www.rfc-editor.org/rfc/rfc9000#section-12.2
        //# Receivers MUST be able to
        //# process coalesced packets.
        //
        //= https://www.rfc-editor.org/rfc/rfc9000#section-12.2
        //# The receiver of coalesced QUIC packets MUST
        //# individually process each QUIC packet and separately acknowledge
        //# them, as if they were received as the payload of different UDP
        //# datagrams.
        if packets.len() > 0 {
            for p in it: packets
                invariant
                    self.wf(),
                    self.out_log() == old(self).out_log(),
                    known == self.paths.has(path),
                    self.phase_spec() is Open,
                    self.amp_grew(s1),
                    self.crypto_kept(s1),
                    s1 == *old(self),
                    forall|j: int| 0 <= j < it.seq().len() ==> plain_wf(#[trigger] it.seq()[j]@),
            {
                proof {
                    assert(it.seq()[it.index()] == p);
                    assert(plain_wf(it.seq()[it.index()]@));
                }
                // §12.2: a packet with another DCID is ignored.
                if eq_bytes(p.dcid.as_slice(), first.as_slice()) && self.gate_packet(path, datagram_len, &p) {
                    if !known {
                        let ghost b0 = *self;
                        // §9: at `MAX_PATHS` the datagram is dropped uncounted.
                        let ok = self.ensure_path(path);
                        proof {
                            self.lemma_grew_trans(b0, s1);
                        }
                        if !ok {
                            return;
                        }
                        let ghost b1 = *self;
                        // §8.1: the whole datagram, including packets the gate already dropped.
                        self.count_recv(path, datagram_len as u64);
                        proof {
                            self.lemma_grew_trans(b1, s1);
                        }
                        known = true;
                    }
                    let ghost b2 = *self;
                    //= https://www.rfc-editor.org/rfc/rfc9000#section-5.2
                    //# An
                    //# endpoint MUST generate a connection error if processing the contents
                    //# of these packets prior to discovering an error, or fully revert any
                    //# changes made during that processing.
                    let r = self.on_packet(path, p, now, rand);
                    proof {
                        self.lemma_grew_trans(b2, s1);
                    }
                    if let Err(c) = r {
                        let ghost b3 = *self;
                        self.close_internal(c);
                        proof {
                            self.lemma_grew_same(b3);
                            self.lemma_grew_trans(b3, s1);
                        }
                        return;
                    }
                    // CONNECTION_CLOSE, or a closed connection.
                    if !matches!(self.lc.phase(), Phase::Open) {
                        return;
                    }
                }
            }
        }
        if let Some((code, h)) = error {
            proof {
                if np == 0 {
                    assert(*self == s1);
                }
            }
            let ghost b4 = *self;
            self.close_on_error(path, datagram_len, first.as_slice(), known, code, &h);
            proof {
                self.lemma_grew_trans(b4, s1);
            }
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-14
    //# Therefore, an endpoint MUST NOT close a connection
    //# when it receives a datagram that does not meet size constraints; the
    //# endpoint MAY discard such datagrams.
    /// The connection error of the packet with header `h`, which stopped its datagram: it closes
    /// the connection only if `h` passes `gate_packet` and the §12.2 DCID check, as a packet must
    /// to be processed. Otherwise the packet is discarded like any gated-out packet.
    #[verifier::spinoff_prover]
    fn close_on_error(&mut self, path: PathId, len: usize, first: &[u8], known: bool, code: u64, h: &PlainPacket)
        requires
            old(self).wf(),
            old(self).phase_spec() is Open,
            known == old(self).paths.has(path),
            code <= VARINT_MAX,
            plain_wf(h@),
        ensures
            final(self).amp_grew(*old(self)),
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            final(self).crypto_kept(*old(self)),
            !(h.dcid@ == first@ && old(self).gate_spec(path, len, h)) ==> *final(self) == *old(self),
            h.dcid@ == first@ && old(self).gate_spec(path, len, h) && old(self).paths.has(path)
                ==> final(self).phase_spec() is Closing,
    {
        if !(eq_bytes(h.dcid.as_slice(), first) && self.gate_packet(path, len, h)) {
            return;
        }
        if !known {
            // §9: at `MAX_PATHS` the datagram is dropped uncounted.
            if !self.ensure_path(path) {
                return;
            }
            // §8.1: the whole datagram, as for a packet that admits the path.
            self.count_recv(path, len as u64);
        }
        let now = self.now;
        let reason: Vec<u8> = Vec::new();
        self.close(code, false, reason.as_slice(), now);
    }

    /// `path` is known, or now added; false at `MAX_PATHS`.
    #[verifier::spinoff_prover]
    fn ensure_path(&mut self, path: PathId) -> (ok: bool)
        requires
            old(self).wf(),
        ensures
            final(self).amp_grew(*old(self)),
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

    //= https://www.rfc-editor.org/rfc/rfc9000#section-8.1
    //# For the purposes of
    //# avoiding amplification prior to address validation, servers MUST
    //# count all of the payload bytes received in datagrams that are
    //# uniquely attributed to a single connection.
    /// §8.1: the bytes of a datagram received on `path`.
    #[verifier::spinoff_prover]
    fn count_recv(&mut self, path: PathId, n: u64)
        requires
            old(self).wf(),
            old(self).paths.has(path),
        ensures
            final(self).amp_grew(*old(self)),
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            final(self).phase_spec() == old(self).phase_spec(),
            final(self).rx_kept(*old(self)),
            final(self).paths.has(path),
            final(self).paths.amp_trace(path) == old(self).paths.amp_trace(path).push(
                AmpEv::Recv(n as nat),
            ),
            *final(self) == (Connection { paths: final(self).paths, ..*old(self) }),
            final(self).paths.path(path).responses == old(self).paths.path(path).responses,
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
            final(self).amp_grew(*old(self)),
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            final(self).paths.ids() == old(self).paths.ids(),
            final(self).peer_used_kept(*old(self)),
            final(self).crypto_kept(*old(self)),
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
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-14.1
    //# A server MUST discard an Initial packet that is carried in a UDP
    //# datagram with a payload that is smaller than the smallest allowed
    //# maximum datagram size of 1200 bytes.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-12.3
    //# Duplicate suppression MUST
    //# happen after removing packet protection for the reasons described in
    //# Section 9.5 of [QUIC-TLS].
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
            old(self).live(p.kind),
        ensures
            final(self).amp_grew(*old(self)),
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            final(self).paths.has(path),
            r matches Err(c) ==> c <= VARINT_MAX,
            r is Err ==> final(self).recv(p.kind).seen() == old(self).recv(p.kind).seen(),
            r is Ok && final(self).phase_spec() is Open ==> final(self).paths.path(path).peer_used
                == Some(p.dcid@),
            final(self).crypto_kept(*old(self)),
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
            old(self).live(k),
        ensures
            final(self).amp_grew(*old(self)),
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            r matches Err(c) ==> c <= VARINT_MAX,
    {
        let ghost fs = frames@;
        for f in it: frames
            invariant
                self.amp_grew(*old(self)),
                self.wf(),
                self.frames_kept(*old(self)),
                self.phase_spec() is Open,
                self.paths.has(path),
                it.seq() == fs,
                frames_received(frames_view(fs), k),
                dcid@.len() <= MAX_CID_LEN,
                k is OneRtt ==> self.complete,
                self.live(k),
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
            old(self).live(k),
        ensures
            final(self).amp_grew(*old(self)),
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
            Frame::Crypto { offset, data } => self.on_crypto_frame(k, *offset, data.as_slice(), now),
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
            final(self).paths == old(self).paths,
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
                self.paths == old(self).paths,
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
            final(self).paths == old(self).paths,
            final(self).wf(),
            final(self).frames_kept(*old(self)),
    {
        let mut j: usize = 0;
        while j < frames.len()
            invariant
                self.paths == old(self).paths,
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

    // Post-handshake CRYPTO is buffered here and read and fed to TLS by quictls; we send no NewSessionTicket.
    /// A CRYPTO frame. On `Err` the connection is already Closing with that code, as in
    /// `on_stream_frame`; `on_datagram`'s `close_internal` is then a no-op.
    //= https://www.rfc-editor.org/rfc/rfc9000#section-7.5
    //# If an endpoint does not expand its buffer, it MUST close
    //# the connection with a CRYPTO_BUFFER_EXCEEDED error code.
    #[verifier::spinoff_prover]
    fn on_crypto_frame(&mut self, k: PacketKind, offset: u64, data: &[u8], now: u64) -> (r: Result<(), u64>)
        requires
            old(self).wf(),
            old(self).live(k),
            offset + data@.len() <= VARINT_MAX,
        ensures
            final(self).paths == old(self).paths,
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            r matches Err(c) ==> c <= VARINT_MAX,
            r matches Err(c) ==> c == CRYPTO_BUFFER_EXCEEDED && crypto_allowed_err(
                old(self).crx_spec(k),
                offset,
                data@.len(),
                c,
            ),
            crypto_allowed_err(old(self).crx_spec(k), offset, data@.len(), CRYPTO_BUFFER_EXCEEDED) ==> r
                == Err::<(), u64>(CRYPTO_BUFFER_EXCEEDED),
            old(self).phase_spec() is Open && crypto_allowed_err(
                old(self).crx_spec(k),
                offset,
                data@.len(),
                CRYPTO_BUFFER_EXCEEDED,
            ) ==> final(self).phase_spec() is Closing && final(self).close_spec() == Some(
                (false, CRYPTO_BUFFER_EXCEEDED, Seq::<u8>::empty()),
            ),
            r is Err ==> !(final(self).phase_spec() is Open),
    {
        proof {
            reveal(crx_ok);
        }
        let pto = self.pto();
        let r = match k {
            PacketKind::Initial => self.crx_i.on_crypto(offset, data),
            PacketKind::Handshake => self.crx_h.on_crypto(offset, data),
            PacketKind::OneRtt => self.crx_1.on_crypto(offset, data),
        };
        if let Err(c) = r {
            let none: Vec<u8> = Vec::new();
            proof {
                assert(none@.take(0) =~= Seq::<u8>::empty());
            }
            self.lc.enter_closing(now, pto, false, c, none.as_slice());
            self.streams = None;
            return Err(c);
        }
        Ok(())
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
            final(self).paths == old(self).paths,
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
            final(self).amp_grew(*old(self)),
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
                self.assign_owed(rand);
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

    /// No path's `peer_used` changed.
    closed spec fn peer_used_kept(&self, o: Connection) -> bool {
        forall|q: PathId|
            #![trigger self.paths.path(q)]
            self.paths.path(q).peer_used == o.paths.path(q).peer_used
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
            final(self).crypto_same(*old(self)),
            final(self).amp_grew(*old(self)),
            final(self).wf_rest(),
            final(self).frames_kept(*old(self)),
            final(self).peer_cids == old(self).peer_cids,
            kept(old(self).paths, final(self).paths, q),
            final(self).paths.path(q) == (SpecPath {
                dcid: opt_slice_view(d),
                ..old(self).paths.path(q)
            }),
            final(self).lc == old(self).lc,
            final(self).clocks_kept(*old(self)),
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
            final(self).crypto_same(*old(self)),
            final(self).amp_grew(*old(self)),
            final(self).wf_rest(),
            final(self).dcids_weak(),
            final(self).frames_kept(*old(self)),
            final(self).peer_cids == old(self).peer_cids,
            kept(old(self).paths, final(self).paths, q),
            final(self).paths.path(q) == (SpecPath {
                dcid: opt_slice_view(d),
                ..old(self).paths.path(q)
            }),
            final(self).peer_used_kept(*old(self)),
            final(self).lc == old(self).lc,
            final(self).clocks_kept(*old(self)),
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
            final(self).crypto_same(*old(self)),
            final(self).amp_grew(*old(self)),
            final(self).wf_rest(),
            final(self).dcids_weak(),
            final(self).frames_kept(*old(self)),
            kept(old(self).paths, final(self).paths, q),
            forall|x: Seq<u8>| #[trigger]
                peer_has_cid(final(self).peer_cids.entries(), x) == peer_has_cid(
                    old(self).peer_cids.entries(),
                    x,
                ),
            final(self).peer_used_kept(*old(self)),
            r ==> final(self).not_stale(q) && final(self).paths.path(q).dcid is Some,
            final(self).paths.path(q).state == old(self).paths.path(q).state,
            final(self).paths.path(q).mtu_failed == old(self).paths.path(q).mtu_failed,
            final(self).paths.path(q).challenge == old(self).paths.path(q).challenge,
            final(self).paths.path(q).owed == old(self).paths.path(q).owed,
            final(self).lc == old(self).lc,
            final(self).clocks_kept(*old(self)),
            !r ==> final(self).paths == old(self).paths && final(self).peer_cids == old(self).peer_cids,
            !r ==> forall|i: int|
                0 <= i < old(self).peer_cids.entries().len() ==> (
                #[trigger] old(self).peer_cids.entries()[i]).3,
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
            final(self).amp_grew(*old(self)),
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            final(self).paths.active_spec() == old(self).paths.active_spec(),
            final(self).peer_used_kept(*old(self)),
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

    /// A CID just arrived: a path with none that owes a PATH_RESPONSE or PATH_CHALLENGE takes one
    /// now. Its full response queue would otherwise drop the peer's retransmitted probes at the
    /// gate, so no later packet on it could reach `after_one_rtt`.
    #[verifier::spinoff_prover]
    fn assign_owed(&mut self, rand: &[u8; RAND_LEN])
        requires
            old(self).wf(),
        ensures
            final(self).amp_grew(*old(self)),
            final(self).wf(),
            final(self).frames_kept(*old(self)),
    {
        let n = self.paths.len();
        let mut i: usize = 0;
        while i < n
            invariant
                self.amp_grew(*old(self)),
                self.wf(),
                self.frames_kept(*old(self)),
                n == self.paths.ids().len(),
                i <= n,
            decreases n - i,
        {
            let q = self.path_at(i);
            if self.paths.dcid(q).is_none() && (self.paths.has_response(q) || self.paths.challenge_owed(q)) {
                self.assign_dcid(q, rand);
            }
            i += 1;
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
            final(self).amp_grew(*old(self)),
            final(self).wf_rest(),
            final(self).dcids_weak(),
            final(self).frames_kept(*old(self)),
            final(self).peer_cids == old(self).peer_cids,
            final(self).paths.active_spec() == old(self).paths.active_spec(),
            final(self).peer_used_kept(*old(self)),
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
                self.amp_grew(*old(self)),
                n == ids.len(),
                i <= n,
                self.wf_rest(),
                self.paths.ids() == ids,
                self.paths.has(path),
                self.frames_kept(*old(self)),
                self.peer_cids == old(self).peer_cids,
                self.paths.active_spec() == old(self).paths.active_spec(),
                self.peer_used_kept(*old(self)),
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
            final(self).amp_grew(*old(self)),
            final(self).wf_rest(),
            final(self).frames_kept(*old(self)),
            final(self).peer_cids == old(self).peer_cids,
            final(self).paths.active_spec() == old(self).paths.active_spec(),
            final(self).peer_used_kept(*old(self)),
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
            final(self).amp_grew(*old(self)),
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            final(self).paths.path(path).peer_used == Some(dcid@),
    {
        let ghost s0 = *self;
        proof {
            s0.lemma_weak_of_wf();
        }
        self.paths.set_peer_used(path, dcid);
        proof {
            assert forall|q: PathId| #[trigger] s0.paths.has(q) implies self.paths.has(q)
                && self.paths.amp_trace(q) == s0.paths.amp_trace(q) by {
                if q != path {
                    assert(self.paths.path(q) == s0.paths.path(q));
                }
            }
            self.lemma_grew_same(s0);
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
        let ghost s1 = *self;
        self.repair_pairs(path);
        proof {
            self.lemma_grew_trans(s1, s0);
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
        ensures
            !r ==> forall|q: PathId|
                #[trigger] self.paths.has(q) && q != a && self.paths.path(q).dcid == Some(cur@)
                    ==> self.paths.path(q).peer_used == self.paths.path(a).peer_used,
    {
        let n = self.paths.len();
        let mut i: usize = 0;
        while i < n
            invariant
                self.paths.wf(),
                self.paths.has(a),
                n == self.paths.ids().len(),
                i <= n,
                forall|k: int|
                    #![trigger self.paths.ids()[k]]
                    0 <= k < i && self.paths.ids()[k] != a && self.paths.path(self.paths.ids()[k]).dcid
                        == Some(cur@) ==> self.paths.path(self.paths.ids()[k]).peer_used
                        == self.paths.path(a).peer_used,
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
        proof {
            assert forall|q: PathId|
                #[trigger] self.paths.has(q) && q != a && self.paths.path(q).dcid == Some(cur@) implies self.paths.path(q).peer_used
                == self.paths.path(a).peer_used by {
                let k = choose|k: int| 0 <= k < self.paths.ids().len() && self.paths.ids()[k] == q;
                assert(self.paths.ids()[k] == q);
            }
        }
        false
    }

    /// The active path holds a retired CID: it takes `current()`, unless another path holds that
    /// under another peer CID; then it takes an unused CID. With none left, neither §5.1.2 nor §9.5
    /// can be met by sending, so the connection closes silently (only the peer's exact-repeat
    /// NEW_CONNECTION_ID with a raised Retire Prior To reaches this). The paths are still put in a
    /// `wf` state, and being Closed nothing is sent on them.
    #[verifier::spinoff_prover]
    fn rewrite_active(&mut self, a: PathId)
        requires
            old(self).wf_rest(),
            old(self).dcids_weak(),
            a == old(self).paths.active_spec(),
        ensures
            final(self).amp_grew(*old(self)),
            final(self).wf_rest(),
            final(self).dcids_weak(),
            final(self).frames_kept(*old(self)),
            final(self).paths.active_spec() == a,
            final(self).not_stale(a),
            (exists|i: int|
                0 <= i < old(self).peer_cids.entries().len() && !(
                #[trigger] old(self).peer_cids.entries()[i]).3) ==> kept(
                old(self).paths,
                final(self).paths,
                a,
            ),
            !kept(old(self).paths, final(self).paths, a) ==> final(self).phase_spec() is Closed,
    {
        proof {
            self.paths.lemma_wf();
            self.peer_cids.lemma_wf();
        }
        let cur = slice_to_vec(self.peer_cids.current());
        let taken = self.cur_taken(a, cur.as_slice());
        if taken && self.fresh_dcid(a) {
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
        if !taken {
            self.hold_dcid(a, Some(cur.as_slice()));
            proof {
                assert(peer_has_cid(self.peer_cids.entries(), cur@));
            }
            return;
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
        self.lc.close_silently();
        self.streams = None;
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
            final(self).amp_grew(*old(self)),
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
            final(self).amp_grew(*old(self)),
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
                self.amp_grew(*old(self)),
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
            final(self).amp_grew(*old(self)),
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
            },
            Frame::PathResponse(d) => self.on_path_response(*d, now, rand),
            _ => {},
        }
        Ok(())
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-8.2.2
    //# This requirement MUST NOT be enforced by the endpoint that initiates
    //# path validation, as that would enable an attack on migration; see
    //# Section 9.3.3.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-8.2.1
    //# To ensure that the path MTU is large enough, the endpoint
    //# MUST perform a second path validation by sending a PATH_CHALLENGE
    //# frame in a datagram of at least 1200 bytes.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-8.2.3
    //# However, the endpoint MUST initiate
    //# another path validation with an expanded datagram to verify that the
    //# path supports the required MTU.
    /// PATH_RESPONSE: §9.4's congestion reset only for a newly validated address (not an MTU probe's
    /// answer, nor §9.3.3's recheck of the old path), then an MTU probe if the path needs one.
    #[verifier::spinoff_prover]
    fn on_path_response(&mut self, data: [u8; 8], now: u64, rand: &[u8; RAND_LEN])
        requires
            old(self).wf(),
        ensures
            final(self).amp_grew(*old(self)),
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
                    //= https://www.rfc-editor.org/rfc/rfc9000#section-9.4
                    //# On confirming a peer's ownership of its new address, an endpoint MUST
                    //# immediately reset the congestion controller and round-trip time
                    //# estimator for the new path to initial values (see Appendices A.3 and
                    //# B.3 of [QUIC-RECOVERY]) unless the only change in the peer's address
                    //# is its port number.
                    self.recovery.on_path_validated();
                    proof {
                        assert(s0.paths.ids()[i as int] == q);
                        assert(s0.paths.has(q));
                    }
                }
            }
            // ponytail: every PATH_RESPONSE may start a probe from the datagram's 4 challenge slices, so one packet answering three sub-1200 validations leaves `migrate`'s §9.3.3 old-path challenge none later in the same packet (only the peer can build it, and that challenge has no retry); start probes only while `chal_used < 2`, or reserve two slices for `after_one_rtt`, if that matters.
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

    //= https://www.rfc-editor.org/rfc/rfc9000#section-8.2.1
    //# The endpoint MUST use unpredictable data in every PATH_CHALLENGE
    //# frame so that it can associate the peer's response with the
    //# corresponding PATH_CHALLENGE.
    /// The next unused challenge slice of `rand`: never reused within a call, since `on_response`
    /// ignores the arrival path (§8.2.2) and distinct data is what ties a response to its path
    /// (§8.2.1). None once all four are used.
    #[verifier::spinoff_prover]
    fn next_challenge(&mut self, rand: &[u8; RAND_LEN]) -> (r: Option<[u8; 8]>)
        requires
            old(self).wf(),
        ensures
            final(self).paths == old(self).paths,
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            final(self).paths == old(self).paths,
            final(self).lc == old(self).lc,
            final(self).recovery == old(self).recovery,
            r is None <==> old(self).chal_used == 4,
            r is None ==> final(self).chal_used == old(self).chal_used,
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
            final(self).amp_grew(*old(self)),
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            final(self).paths.active_spec() == old(self).paths.active_spec(),
            final(self).recovery == old(self).recovery,
            final(self).lc == old(self).lc,
            final(self).paths.path(q).mtu_failed == old(self).paths.path(q).mtu_failed,
            final(self).peer_used_kept(*old(self)),
            forall|r: PathId| r != q ==> #[trigger] final(self).paths.path(r) == old(self).paths.path(r),
            final(self).paths.path(q).state == if old(self).chal_used < 4 && old(self).paths.path(q).state is Unvalidated {
                PathState::Validating
            } else {
                old(self).paths.path(q).state
            },
            old(self).chal_used < 4 ==> final(self).paths.path(q).owed,
            final(self).chal_used <= old(self).chal_used + 1,
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
            final(self).amp_grew(*old(self)),
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            final(self).peer_used_kept(*old(self)),
            final(self).paths.active_spec() != old(self).paths.active_spec() ==> non_probing
                && old(self).recv_1.largest_spec() == Some(pn) && final(self).paths.active_spec()
                == path,
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
            final(self).amp_grew(*old(self)),
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            final(self).paths.path(path).dcid is Some ==> forall|q: PathId|
                #[trigger] final(self).paths.has(q) && q != path && final(self).paths.path(q).dcid
                    == final(self).paths.path(path).dcid ==> final(self).paths.path(q).peer_used
                    == final(self).paths.path(path).peer_used,
            final(self).peer_used_kept(*old(self)),
            final(self).paths.active_spec() == if old(self).paths.path(path).dcid is Some && !old(
                self,
            ).paths.path(path).mtu_failed {
                path
            } else {
                old(self).paths.active_spec()
            },
            old(self).paths.path(path).dcid is Some && !old(self).paths.path(path).mtu_failed ==> {
                &&& old(self).paths.path(path).state is Unvalidated && old(self).chal_used < 4
                    ==> final(self).paths.path(path).owed
                &&& old(self).paths.path(old(self).paths.active_spec()).state is Validated && old(
                    self,
                ).chal_used < 3 ==> final(self).paths.path(old(self).paths.active_spec()).owed
            },
    {
        // §9.5: no fresh CID for a second destination.
        if self.paths.dcid(path).is_none() {
            return;
        }
        // §14.2: never make a failed-MTU path active (3d final review I2).
        if self.paths.mtu_failed(path) {
            // The peer is sending from here: probe again, at most one a 3·PTO (§14.2 allows it).
            if self.paths.needs_mtu_probe(path) {
                self.challenge_path(path, now, rand);
            }
            proof {
                assert forall|q: PathId|
                    #[trigger] self.paths.has(q) && q != path && self.paths.path(q).dcid
                        == self.paths.path(path).dcid && self.paths.path(path).dcid is Some implies self.paths.path(q).peer_used
                    == self.paths.path(path).peer_used by {
                    assert(self.paths.has(path));
                }
            }
            return;
        }
        let old_path = self.paths.active();
        let ghost s0 = *self;
        self.paths.set_active(path);
        proof {
            self.lemma_active_set(s0, path);
            self.lemma_grew_same(s0);
        }
        let ghost s1 = *self;
        // §9, §9.3: not if validation is already underway (preflight M9).
        if matches!(self.paths.state(path), PathState::Unvalidated) {
            self.challenge_path(path, now, rand);
        }
        proof {
            self.lemma_grew_trans(s1, s0);
            s0.paths.lemma_wf();
            assert(self.paths.has(old_path)) by {
                assert(s0.paths.has(old_path));
            }
        }
        let ghost s2 = *self;
        if matches!(self.paths.state(old_path), PathState::Validated) {
            self.challenge_path(old_path, now, rand);
        }
        proof {
            self.lemma_grew_trans(s2, s0);
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
            final(self).paths == old(self).paths,
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

    //= https://www.rfc-editor.org/rfc/rfc9000#section-13.3
    //# The content of a RESET_STREAM frame MUST NOT change when it is
    //# sent again.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-13.3
    //# The HANDSHAKE_DONE frame MUST be retransmitted until it is
    //# acknowledged.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-13.3
    //# A receiver MUST accept packets containing an
    //# outdated frame, such as a MAX_DATA frame carrying a smaller maximum
    //# data value than one found in an older packet.
    /// §13.3: frame `f` of a lost record of space `k`. Outdated frames are accepted: 3c's credit
    /// `on_max` ignores decreases.
    #[verifier::spinoff_prover]
    fn on_lost_frame(&mut self, k: PacketKind, f: &Frame)
        requires
            old(self).wf(),
        ensures
            final(self).crypto_same(*old(self)),
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            final(self).paths == old(self).paths,
            final(self).lc == old(self).lc,
            final(self).clocks_kept(*old(self)),
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
            final(self).paths == old(self).paths,
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
            final(self).crypto_end_spec(PacketKind::Initial) == old(self).crypto_end_spec(PacketKind::Initial),
            final(self).crypto_kept(*old(self)),
            drained_kept(*final(self), *old(self)),
            crypto_drained(*final(self), k),
    {
        proof {
            reveal(crx_ok);
        }
        let mut lost: Vec<SentPacket> = Vec::new();
        match k {
            PacketKind::Initial => {
                if !self.live_i {
                    return;
                }
                self.live_i = false;
                self.sent_i.drain_inflight(&mut lost);
                // Restarted empty at its end, which the glue still checks (RFC 9001 §4.1.3).
                self.crx_i.restart();
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
            final(self).paths == old(self).paths,
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            old(self).phase_spec() is Open ==> final(self).phase_spec() is Closing
                && final(self).close_spec() == Some((false, code, Seq::<u8>::empty())),
            !(old(self).phase_spec() is Open) ==> final(self).phase_spec() == old(self).phase_spec()
                && final(self).close_spec() == old(self).close_spec(),
            final(self).crypto_same(*old(self)),
    {
        let now = self.now;
        let none: Vec<u8> = Vec::new();
        self.close(code, false, none.as_slice(), now);
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-10.2.1
    //# An endpoint enters the closing state after initiating an immediate
    //# close.
    /// Enters the closing state (the first error wins, §11.1) and drops the streams.
    #[verifier::spinoff_prover]
    pub fn close(&mut self, code: u64, app: bool, reason: &[u8], now: u64)
        requires
            old(self).wf(),
            code <= VARINT_MAX,
        ensures
            final(self).paths_kept(*old(self)),
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            old(self).phase_spec() is Open ==> final(self).phase_spec() is Closing,
            !(old(self).phase_spec() is Open) ==> final(self).phase_spec() == old(self).phase_spec(),
            old(self).phase_spec() is Open ==> final(self).close_spec() == Some((app, code, reason_cap(reason@))),
            !(old(self).phase_spec() is Open) ==> final(self).close_spec() == old(self).close_spec(),
            final(self).events_spec() == old(self).events_spec(),
            final(self).keeps_later(*old(self)),
            final(self).crypto_same(*old(self)),
    {
        let ghost o = *self;
        if now > self.now {
            self.now = now;
        }
        let pto = self.pto();
        proof {
            self.recovery.lemma_pto_pos(PacketKind::OneRtt, self.peer_mad_spec());
        }
        self.lc.enter_closing(self.now, pto, app, code, reason);
        self.streams = None;
        proof {
            assert forall|t: u64| t < u64::MAX && t <= o.now && #[trigger] o.timers_later(t) implies self.timers_later(t) by {
                assert(self.pto_spec() == o.pto_spec());
            }
        }
    }

    /// The peer's max_ack_delay in microseconds; its default until TLS delivers its parameters.
    closed spec fn peer_mad_spec(&self) -> u64 {
        spec_ms_to_us(
            match self.peer_tp {
                Some(t) => t.max_ack_delay,
                None => 25u64,
            },
        )
    }

    fn peer_mad(&self) -> (r: u64)
        ensures
            r == self.peer_mad_spec(),
    {
        ms_to_us(
            match &self.peer_tp {
                Some(t) => t.max_ack_delay,
                None => 25,
            },
        )
    }

    closed spec fn pto_spec(&self) -> u64 {
        self.recovery.pto_us_spec(PacketKind::OneRtt, self.peer_mad_spec())
    }

    /// The current 1-RTT probe timeout.
    #[verifier::spinoff_prover]
    fn pto(&self) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self.pto_spec(),
    {
        self.recovery.pto_us(PacketKind::OneRtt, self.peer_mad())
    }

    // =========================================================================
    // The TLS boundary
    // =========================================================================

    /// A connection no longer open: every level's unread in-order CRYPTO bytes are dropped, since
    /// TLS is fed nothing more after a close (RFC 8446 §6.2). The ends and the received history
    /// stay, for RFC 9001 §4.1.3.
    #[verifier::spinoff_prover]
    pub fn crypto_drop(&mut self)
        requires
            old(self).wf(),
            !(old(self).phase_spec() is Open),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            final(self).phase_spec() == old(self).phase_spec(),
            final(self).close_spec() == old(self).close_spec(),
            forall|k: PacketKind| #[trigger] final(self).live(k) == old(self).live(k),
            forall|k: PacketKind| #[trigger] final(self).crypto_end_spec(k) == old(self).crypto_end_spec(k),
            forall|k: PacketKind, p: nat| #[trigger] final(self).crypto_received(k, p) == old(self).crypto_received(k, p),
            final(self).crypto_kept(*old(self)),
            crypto_all_drained(*final(self)),
    {
        hide(crate::reassembly::rfc_received);
        hide(crate::reassembly::rfc_contiguous);
        proof {
            reveal(crx_ok);
            self.crx_i.lemma_wf();
            self.crx_h.lemma_wf();
            self.crx_1.lemma_wf();
        }
        // shortcut: the bytes are copied out and dropped (`read`); a copy-free pop only if this shows up.
        let mut sink: Vec<u8> = Vec::new();
        self.crx_i.read(&mut sink);
        self.crx_h.read(&mut sink);
        self.crx_1.read(&mut sink);
        proof {
            assert forall|k: PacketKind| #[trigger] crypto_drained(*self, k) by {
                match k {
                    PacketKind::Initial => {},
                    PacketKind::Handshake => {},
                    PacketKind::OneRtt => {},
                }
            }
        }
    }

    /// Appends the newly contiguous CRYPTO bytes of `level` to `out`.
    #[verifier::spinoff_prover]
    pub fn crypto_read(&mut self, level: PacketKind, out: &mut Vec<u8>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            final(out)@.len() <= old(out)@.len() + old(self).crypto_end_spec(level) - old(
                self,
            ).crypto_base_spec(level),
            // A read drains the in-order data: nothing received in order stays unread.
            old(self).phase_spec() is Open ==> final(self).crypto_base_spec(level) == old(
                self,
            ).crypto_contiguous_spec(level),
            old(self).phase_spec() is Open ==> final(out)@.len() == old(out)@.len() + old(
                self,
            ).crypto_contiguous_spec(level) - old(self).crypto_base_spec(level),
            old(self).crypto_end_spec(level) <= old(self).crypto_base_spec(level) ==> final(out)@ == old(out)@,
            // The read hands over exactly the bytes its offset passes; no other level's moves.
            final(self).crypto_kept_but(*old(self), Some(level)),
            final(self).peer_tp_known_spec() == old(self).peer_tp_known_spec(),
            !(old(self).phase_spec() is Open) ==> final(out)@ == old(out)@,
            final(self).phase_spec() == old(self).phase_spec(),
            old(self).phase_spec() is Open ==> crypto_drained(*final(self), level),
            drained_kept(*final(self), *old(self)),
    {
        // The bound needs only `lemma_wf`; unfolded, these make a missing fact an rlimit failure.
        hide(crate::reassembly::rfc_received);
        hide(crate::reassembly::rfc_contiguous);
        proof {
            reveal(crx_ok);
        }
        if !matches!(self.lc.phase(), Phase::Open) {
            return;
        }
        match level {
            PacketKind::Initial => {
                proof {
                    self.crx_i.lemma_wf();
                }
                self.crx_i.read(out)
            },
            PacketKind::Handshake => {
                proof {
                    self.crx_h.lemma_wf();
                }
                self.crx_h.read(out)
            },
            PacketKind::OneRtt => {
                proof {
                    self.crx_1.lemma_wf();
                }
                self.crx_1.read(out)
            },
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
            final(self).crypto_kept(*old(self)),
            final(self).crypto_end_spec(PacketKind::Initial) == old(self).crypto_end_spec(PacketKind::Initial),
            final(self).phase_spec() == old(self).phase_spec(),
            drained_kept(*final(self), *old(self)),
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

    //= https://www.rfc-editor.org/rfc/rfc9000#section-7.3
    //# An endpoint MUST treat the following as a connection error of type
    //# TRANSPORT_PARAMETER_ERROR or PROTOCOL_VIOLATION:
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-7.3
    //# a mismatch between values received from a peer in these transport
    //# parameters and the value sent in the corresponding Destination or
    //# Source Connection ID fields of Initial packets.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-7.3
    //# An endpoint MUST treat the absence of the
    //# initial_source_connection_id transport parameter from either endpoint
    //# or the absence of the original_destination_connection_id transport
    //# parameter from the server as a connection error of type
    //# TRANSPORT_PARAMETER_ERROR.
    /// TLS delivered the client's transport parameters.
    #[verifier::spinoff_prover]
    pub fn on_peer_params(&mut self, tp: &TransportParams, now: u64)
        requires
            old(self).wf(),
            peer_tp_wf(tp@),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            old(self).phase_spec() is Open && !(final(self).phase_spec() is Open) ==> {
                &&& final(self).phase_spec() is Closing
                &&& final(self).close_spec() == Some((false, TRANSPORT_PARAMETER_ERROR, Seq::<u8>::empty()))
                &&& tp@.initial_source_connection_id != Some(old(self).client_scid_spec())
            },
            old(self).phase_spec() is Open && !old(self).peer_tp_known_spec() ==> (!(final(self).phase_spec() is Open)
                <==> tp@.initial_source_connection_id != Some(old(self).client_scid_spec())),
            old(self).phase_spec() is Open && !old(self).peer_tp_known_spec() && tp@.initial_source_connection_id is None
                ==> final(self).phase_spec() is Closing
                && final(self).close_spec() == Some((false, TRANSPORT_PARAMETER_ERROR, Seq::<u8>::empty())),
            !(old(self).phase_spec() is Open) ==> final(self).phase_spec() == old(self).phase_spec()
                && final(self).close_spec() == old(self).close_spec(),
            final(self).crypto_kept_base(*old(self)),
            final(self).crypto_end_spec(PacketKind::Initial) == old(self).crypto_end_spec(PacketKind::Initial),
            drained_kept(*final(self), *old(self)),
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

    //= https://www.rfc-editor.org/rfc/rfc9001#section-8.1
    //# When using ALPN, endpoints MUST immediately close a connection (see
    //# Section 10.2 of [QUIC-TRANSPORT]) with a no_application_protocol TLS
    //# alert (QUIC error code 0x0178; see Section 4.8) if an application
    //# protocol is not negotiated.
    /// TLS finished, with this ALPN. After this no long-header packet is built.
    #[verifier::spinoff_prover]
    pub fn on_handshake_complete(&mut self, alpn: &[u8], now: u64, rand: &[u8; RAND_LEN])
        requires
            old(self).wf(),
        ensures
            // §8.1: an open, not yet complete connection whose ALPN is not `h3` closes with 0x0178.
            old(self).phase_spec() is Open && !old(self).live(PacketKind::OneRtt) && alpn@ != seq![0x68u8, 0x33u8]
                ==> final(self).phase_spec() is Closing
                && final(self).close_spec() == Some((false, (CRYPTO_ERROR_BASE + 0x78) as u64, Seq::<u8>::empty())),
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            final(self).crypto_kept(*old(self)),
            final(self).crypto_end_spec(PacketKind::Initial) == old(self).crypto_end_spec(PacketKind::Initial),
            final(self).phase_spec() is Open ==> old(self).phase_spec() is Open,
            drained_kept(*final(self), *old(self)),
            final(self).phase_spec() is Open ==> final(self).live(PacketKind::OneRtt),
            final(self).live(PacketKind::OneRtt) ==> crypto_drained(*final(self), PacketKind::Initial)
                && crypto_drained(*final(self), PacketKind::Handshake),
    {
        if now > self.now {
            self.now = now;
        }
        self.chal_used = 0;
        if !matches!(self.lc.phase(), Phase::Open) || self.complete {
            proof {
                reveal(crx_ok);
            }
            return;
        }
        // ALPN first: §8.1's close is owed whatever else is wrong.
        if let Err(c) = check_alpn(alpn) {
            self.close_internal(c);
            return;
        }
        // `streams.is_none()` is unreachable (`on_peer_params` sets both); `wf`'s `complete` clause
        // needs it, and it costs less than one more conjunct.
        if self.peer_tp.is_none() || self.streams.is_none() {
            self.close_internal(INTERNAL_ERROR);
            return;
        }
        let ghost s0 = *self;
        self.discard(PacketKind::Initial);
        let ghost s1 = *self;
        self.discard(PacketKind::Handshake);
        let ghost s2 = *self;
        proof {
            reveal(crx_ok);
        }
        self.complete = true;
        self.hs_done = HsDone::Pending;
        self.spin = rand[128] & 1 == 1;
        self.issue_cids(rand);
        proof {
            reveal(crx_ok);
            assert forall|k: PacketKind| #[trigger] crypto_drained(*old(self), k) implies crypto_drained(*self, k) by {
                assert(crypto_drained(s0, k));
                assert(crypto_drained(s1, k));
                assert(crypto_drained(s2, k));
            }
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9001#section-4.8
    //# A TLS alert is converted into a QUIC connection error.  The
    //# AlertDescription value is added to 0x0100 to produce a QUIC error
    //# code from the range reserved for CRYPTO_ERROR; see Section 20.1 of
    //# [QUIC-TRANSPORT].  The resulting value is sent in a QUIC
    //# CONNECTION_CLOSE frame of type 0x1c.
    /// TLS failed with this alert (RFC 9001 §4.8).
    #[verifier::spinoff_prover]
    pub fn on_tls_alert(&mut self, alert: u8, now: u64)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            old(self).phase_spec() is Open ==> final(self).phase_spec() is Closing
                && final(self).close_spec() == Some((false, (CRYPTO_ERROR_BASE + alert as u64) as u64, Seq::<u8>::empty())),
            !(old(self).phase_spec() is Open) ==> final(self).phase_spec() == old(self).phase_spec()
                && final(self).close_spec() == old(self).close_spec(),
            final(self).crypto_kept(*old(self)),
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
            final(self).paths == old(self).paths,
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            final(self).frames_kept(*old(self)),
            final(self).paths == old(self).paths,
            final(self).lc == old(self).lc,
            final(self).clocks_kept(*old(self)),
            final(self).crypto_same(*old(self)),
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
                self.paths == old(self).paths,
                self.lc == old(self).lc,
                self.clocks_kept(*old(self)),
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
            final(self).events_spec() == old(self).events_spec(),
            final(self).keeps_later(*old(self)),
    {
        let ghost o = *self;
        let r = match &mut self.streams {
            Some(s) => {
                let room = s.send_room();
                let n = if data.len() as u64 > room {
                    room as usize
                } else {
                    data.len()
                };
                if n == 0 && !(fin && data.len() == 0) {
                    Ok(0)
                } else {
                    match s.write(id, slice_subrange(data, 0, n), fin && n == data.len()) {
                        Ok(()) => Ok(n),
                        Err(()) => Err(()),
                    }
                }
            },
            None => Err(()),
        };
        proof {
            self.lemma_keeps_streams(o);
        }
        r
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
            final(self).events_spec() == old(self).events_spec(),
            final(self).keeps_later(*old(self)),
    {
        let ghost o = *self;
        if let Some(s) = &mut self.streams {
            s.reset(id, code);
        }
        proof {
            self.lemma_keeps_streams(o);
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
            final(self).events_spec() == old(self).events_spec(),
            final(self).keeps_later(*old(self)),
    {
        let ghost o = *self;
        if let Some(s) = &mut self.streams {
            s.stop_sending(id, code);
        }
        proof {
            self.lemma_keeps_streams(o);
        }
    }

    /// `tail` is the reset token of an active CID we have used.
    pub closed spec fn reset_matches(&self, tail: Seq<u8>) -> bool {
        reset_match(self.peer_cids.entries(), tail)
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
            old(self).reset_matches(tail@) && old(self).phase_spec() is Open ==> final(self).phase_spec() is Draining,
            old(self).reset_matches(tail@) ==> !(final(self).phase_spec() is Open),
            !old(self).reset_matches(tail@) ==> final(self).phase_spec() == old(self).phase_spec(),
            forall|q: PathId| #[trigger] final(self).amp_trace(q) == old(self).amp_trace(q),
            final(self).crypto_kept(*old(self)),
            drained_kept(*final(self), *old(self)),
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
            final(self).keeps_later(*old(self)),
    {
        let ghost o = *self;
        let mut taken: Vec<StreamEvent> = Vec::new();
        core::mem::swap(&mut self.events, &mut taken);
        out.append(&mut taken);
        proof {
            self.lemma_keeps_streams(o);
        }
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
            final(self).keeps_later(*old(self)),
    {
        let ghost o = *self;
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
            self.lemma_keeps_streams(o);
        }
    }

    // =========================================================================
    // Transmit
    // =========================================================================

    /// The frames the latest `poll_transmit` took from `Streams::poll_frames`: each counts as sent,
    /// so each is in the datagram it returned (P8).
    pub closed spec fn polled(&self) -> Seq<SpecFrame> {
        self.polled@
    }

    /// The ack-eliciting packets in flight, across the spaces.
    closed spec fn inflight_total(&self) -> int {
        (self.sent_i.inflight_spec().len() + self.sent_h.inflight_spec().len()
            + self.sent_1.inflight_spec().len()) as int
    }

    closed spec fn active_dcid_spec(&self) -> Seq<u8> {
        self.paths.path(self.paths.active_spec()).dcid->0
    }

    /// The Destination Connection ID of a packet of space `k`.
    closed spec fn space_dcid(&self, k: PacketKind) -> Seq<u8> {
        match k {
            PacketKind::OneRtt => self.active_dcid_spec(),
            _ => self.ids@.client_scid,
        }
    }

    /// A packet's bytes before its packet number. A long header reserves a 2-byte Length.
    closed spec fn header_bytes_spec(&self, k: PacketKind) -> nat {
        match k {
            PacketKind::OneRtt => (1 + self.active_dcid_spec().len()) as nat,
            PacketKind::Initial => (7 + self.ids@.client_scid.len() + LOCAL_CID_LEN + 1 + 2) as nat,
            PacketKind::Handshake => (7 + self.ids@.client_scid.len() + LOCAL_CID_LEN + 2) as nat,
        }
    }

    /// What collecting frames leaves alone: all of `wf` but the frame sources.
    closed spec fn tx_kept(&self, o: Connection) -> bool {
        &&& self.idle == o.idle
        &&& self.hs_path == o.hs_path
        &&& self.ids == o.ids
        &&& self.local_tp == o.local_tp
        &&& self.peer_tp == o.peer_tp
        &&& self.paths == o.paths
        &&& self.lc == o.lc
        &&& self.recovery == o.recovery
        &&& self.recv_i == o.recv_i
        &&& self.recv_h == o.recv_h
        &&& self.recv_1 == o.recv_1
        &&& self.sent_i == o.sent_i
        &&& self.sent_h == o.sent_h
        &&& self.sent_1 == o.sent_1
        &&& self.live_i == o.live_i
        &&& self.live_h == o.live_h
        &&& self.complete == o.complete
        &&& self.crx_i == o.crx_i
        &&& self.crx_h == o.crx_h
        &&& self.crx_1 == o.crx_1
        &&& self.peer_cids.entries() == o.peer_cids.entries()
        &&& self.cid_updates == o.cid_updates
        &&& self.chal_used == o.chal_used
        &&& self.out_log@ == o.out_log@
    }

    /// A packet of space `k` that fits `room`, from `collect_frames` on state `self`.
    closed spec fn packet_ok(&self, p: SpecOutPacket, k: PacketKind, room: nat) -> bool {
        &&& p.kind == k
        &&& p.pn == self.sent(k).next_pn_spec()
        &&& p.dcid == self.space_dcid(k)
        &&& out_packet_wf(p, self.sent(k).largest_acked_spec())
        &&& out_packet_len(p) <= room + self.header_bytes_spec(k) + p.pn_len + AEAD_TAG_LEN + 3
        &&& ack_ok(p.frames, self.recv(k))
        &&& no_path_frames(p.frames)
    }

    fn sent_ref(&self, k: PacketKind) -> (r: &SentPackets)
        ensures
            *r == self.sent(k),
    {
        match k {
            PacketKind::Initial => &self.sent_i,
            PacketKind::Handshake => &self.sent_h,
            PacketKind::OneRtt => &self.sent_1,
        }
    }

    fn recv_ref(&self, k: PacketKind) -> (r: &RecvPns)
        ensures
            *r == self.recv(k),
    {
        match k {
            PacketKind::Initial => &self.recv_i,
            PacketKind::Handshake => &self.recv_h,
            PacketKind::OneRtt => &self.recv_1,
        }
    }

    proof fn lemma_header_bytes(&self, k: PacketKind)
        requires
            self.wf(),
        ensures
            self.header_bytes_spec(k) <= 40,
    {
        self.paths.lemma_wf();
        assert(path_ok(self.paths.path(self.paths.active_spec())));
    }

    /// `header_bytes_spec`.
    #[verifier::spinoff_prover]
    fn header_bytes(&self, k: PacketKind) -> (n: usize)
        requires
            self.wf(),
        ensures
            n == self.header_bytes_spec(k),
            n <= 40,
    {
        proof {
            self.paths.lemma_wf();
            assert(path_ok(self.paths.path(self.paths.active_spec())));
        }
        match k {
            PacketKind::OneRtt => match self.paths.dcid(self.paths.active()) {
                Some(d) => 1 + d.len(),
                None => {
                    proof {
                        assert(false);
                    }
                    0
                },
            },
            PacketKind::Initial => 7 + self.ids.client_scid().len() + LOCAL_CID_LEN + 1 + 2,
            PacketKind::Handshake => 7 + self.ids.client_scid().len() + LOCAL_CID_LEN + 2,
        }
    }

    /// The frame room a packet of space `k` has in `left` bytes of datagram; None on underflow. An
    /// unencodable packet number takes the longest encoding here: `collect_frames` closes on it.
    #[verifier::spinoff_prover]
    fn room_for(&self, k: PacketKind, left: usize) -> (r: Option<usize>)
        requires
            self.wf(),
            left <= MAX_DATAGRAM,
        ensures
            r matches Some(room) ==> room <= MAX_DATAGRAM && forall|n: nat|
                #[trigger] min_pn_len(self.sent(k).next_pn_spec(), self.sent(k).largest_acked_spec(), n) ==> room
                    + self.header_bytes_spec(k) + n + AEAD_TAG_LEN + 3 <= left,
            match r {
                Some(x) => self.room_spec(k, left as nat) == Some(x as nat),
                None => self.room_spec(k, left as nat) is None,
            },
    {
        proof {
            self.sent(k).lemma_wf();
        }
        let pn_len = match pn_encode_len(self.sent_ref(k).next_pn(), self.sent_ref(k).largest_acked()) {
            Some(n) => n as usize,
            None => 4,
        };
        proof {
            let pn = self.sent(k).next_pn_spec();
            let la = self.sent(k).largest_acked_spec();
            if pn_len < 4 {
                assert(!pn_len_ok(pn, la, 1) ==> pn_len != 1);
            }
            assert(pn_len as nat == (if pn_len_ok(pn, la, 1) { 1nat } else if pn_len_ok(pn, la, 2) { 2nat } else if pn_len_ok(pn, la, 3) { 3nat } else { 4nat })) by {
                assert(pn_len_ok(pn, la, pn_len as nat) || !pn_len_ok(pn, la, 3));
            }
        }
        let need = self.header_bytes(k) + pn_len + AEAD_TAG_LEN + 3;
        if left < need {
            return None;
        }
        Some(left - need)
    }

    /// The ACK for space `k`, if one goes in this packet: only with room for every remembered range
    /// (3d Task 2 binding), so it reports every ack-eliciting packet number not yet reported.
    #[verifier::spinoff_prover]
    fn start_frames(&self, k: PacketKind, room: usize, now: u64) -> (r: (Vec<Frame>, usize))
        requires
            self.wf(),
        ensures
            tx_frames(frames_view(r.0@), k, r.0@.len() as int, r.1 as nat, room as nat),
            r.0@.len() <= 1,
            ack_ok(frames_view(r.0@), self.recv(k)),
            r.0@.len() == 1 ==> frames_view(r.0@)[0] is Ack,
            self.recv(k).has_new() && self.recv(k).full_ack_fits(now, self.local_tp.ack_delay_exponent, room as int)
                ==> r.0@.len() == 1,
            forall|i: int|
                0 <= i < r.0@.len() ==> !ack_eliciting(
                    spec_frame_type(#[trigger] frames_view(r.0@)[i]),
                ),
    {
        let mut fs: Vec<Frame> = Vec::new();
        proof {
            assert(frames_view(fs@) =~= Seq::<SpecFrame>::empty());
        }
        if !self.recv_ref(k).has_new() {
            return (fs, room);
        }
        //= https://www.rfc-editor.org/rfc/rfc9000#section-13.2.6
        //# ACK frames MUST only be carried in a packet that has the same packet
        //# number space as the packet being acknowledged; see Section 12.1.
        //
        //= https://www.rfc-editor.org/rfc/rfc9000#section-13.2.6
        //# For
        //# instance, packets that are protected with 1-RTT keys MUST be
        //# acknowledged in packets that are also protected with 1-RTT keys.
        //
        //= https://www.rfc-editor.org/rfc/rfc9000#section-17.2.3
        //# An acknowledgment for a 1-RTT
        //# packet MUST be carried in a 1-RTT packet.
        //
        //= https://www.rfc-editor.org/rfc/rfc9000#section-13.2.6
        //= type=exception
        //= reason=We never accept 0-RTT.
        //# Packets that a client sends with 0-RTT packet protection MUST be
        //# acknowledged by the server in packets protected by 1-RTT keys.
        //
        //= https://www.rfc-editor.org/rfc/rfc9000#section-17.2.3
        //= type=exception
        //= reason=client-only
        //# A client MUST NOT send 0-RTT packets once it starts processing 1-RTT
        //# packets from the server.
        match self.recv_ref(k).build_ack(now, self.local_tp.ack_delay_exponent, room) {
            None => (fs, room),
            // Every range or none, so an ACK reports every packet number not yet reported.
            Some(a) => if a.ranges.len() + 1 != self.recv_ref(k).range_len() {
                (fs, room)
            } else {
                let ghost g = a@;
                let ghost rc = self.recv(k);
                let f = Frame::Ack(a);
                let n = frame_len(&f);
                let ghost sf = f@;
                fs.push(f);
                proof {
                    let d = if rc.kind_spec() is OneRtt {
                        ack_delay_field(now, rc.largest_time_spec(), self.local_tp@.ack_delay_exponent)
                    } else {
                        0
                    };
                    rc.lemma_wf();
                    assert(g == rc.ack_candidate(g.ranges.len() as nat, d));
                    assert(ack_full(g, rc));
                    assert(frames_view(fs@) =~= seq![sf]);
                    lemma_frames_bytes_push(Seq::<SpecFrame>::empty(), sf);
                    assert(seq![sf] =~= Seq::<SpecFrame>::empty().push(sf));
                }
                (fs, room - n)
            },
        }
    }

    /// One CRYPTO frame, sized for its offset, which is the one `poll_data` uses next. Not a loop on
    /// `next_off`: it can stay Some while `poll_data` sends nothing (`next_off`'s doc).
    #[verifier::spinoff_prover]
    fn crypto_frame(
        &mut self,
        k: PacketKind,
        left: &mut usize,
        fs: &mut Vec<Frame>,
        Ghost(base): Ghost<int>,
        Ghost(room): Ghost<nat>,
    )
        requires
            old(self).wf(),
            !(k is OneRtt),
            room <= MAX_DATAGRAM,
            tx_frames(frames_view(old(fs)@), k, base, *old(left) as nat, room),
        ensures
            final(self).wf(),
            final(self).tx_kept(*old(self)),
            final(self).now == old(self).now,
            final(self).streams == old(self).streams,
            final(self).polled == old(self).polled,
            tx_frames(frames_view(final(fs)@), k, base, *final(left) as nat, room),
            extends(frames_view(old(fs)@), frames_view(final(fs)@)),
    {
        proof {
            self.ctx_i.lemma_wf();
            self.ctx_h.lemma_wf();
        }
        let next = match k {
            PacketKind::Initial => self.ctx_i.next_off(),
            _ => self.ctx_h.next_off(),
        };
        let off = match next {
            Some(o) => o,
            None => return,
        };
        let head = 1 + varint_len(off) + 2;
        if *left <= head {
            return;
        }
        let max_len = *left - head;
        let chunk = match k {
            PacketKind::Initial => self.ctx_i.poll_data(max_len as u64, VARINT_MAX),
            _ => self.ctx_h.poll_data(max_len as u64, VARINT_MAX),
        };
        if let Some(c) = chunk {
            let n = head - 2 + varint_len(c.data.len() as u64) + c.data.len();
            let ghost sf0 = frames_view(fs@);
            let ghost left0 = *left as nat;
            let ghost g = SpecFrame::Crypto { offset: c.off, data: c.data@ };
            proof {
                lemma_crypto_len(c.off, c.data@);
            }
            fs.push(Frame::Crypto { offset: c.off, data: c.data });
            *left = *left - n;
            proof {
                assert(frames_view(fs@) =~= sf0.push(g));
                lemma_tx_push(sf0, g, k, base, left0, room, *left as nat);
            }
        }
    }

    /// HANDSHAKE_DONE, then the CIDs we owe the peer and the retirements we owe it. Sent is set here,
    /// with the frame: an ACK-only packet can go out while the frame waits for congestion window.
    #[verifier::spinoff_prover]
    fn control_frames(
        &mut self,
        left: &mut usize,
        fs: &mut Vec<Frame>,
        Ghost(base): Ghost<int>,
        Ghost(room): Ghost<nat>,
    )
        requires
            old(self).wf(),
            tx_frames(frames_view(old(fs)@), PacketKind::OneRtt, base, *old(left) as nat, room),
        ensures
            final(self).wf(),
            final(self).tx_kept(*old(self)),
            final(self).now == old(self).now,
            final(self).streams == old(self).streams,
            final(self).polled == old(self).polled,
            tx_frames(frames_view(final(fs)@), PacketKind::OneRtt, base, *final(left) as nat, room),
            extends(frames_view(old(fs)@), frames_view(final(fs)@)),
            final(self).hs_done == old(self).hs_done || (old(self).hs_done is Pending && final(self).hs_done is Sent),
            old(self).hs_done is Pending && final(self).hs_done is Sent ==> frames_view(
                final(fs)@,
            )[old(fs)@.len() as int] is HandshakeDone,
            // HANDSHAKE_DONE counts as Sent only with its frame; a CID leaves its queue only with one.
            final(self).local_cids.pending_spec().len() + final(self).peer_cids.retire_pending_spec().len()
                + final(fs)@.len() == old(self).local_cids.pending_spec().len()
                + old(self).peer_cids.retire_pending_spec().len() + old(fs)@.len() + (if old(self).hs_done is Pending
                && final(self).hs_done is Sent {
                1int
            } else {
                0int
            }),
    {
        let ghost n0 = fs@.len();
        self.handshake_done_frame(left, fs, Ghost(base), Ghost(room));
        proof {
            if fs@.len() == n0 + 1 {
                assert(frames_view(fs@)[n0 as int] == fs@.last()@);
            }
        }
        self.new_cid_frames(left, fs, Ghost(base), Ghost(room));
        self.retire_cid_frames(left, fs, Ghost(base), Ghost(room));
    }

    /// HANDSHAKE_DONE if it is owed and fits: it counts as Sent exactly when it is placed.
    #[verifier::spinoff_prover]
    fn handshake_done_frame(
        &mut self,
        left: &mut usize,
        fs: &mut Vec<Frame>,
        Ghost(base): Ghost<int>,
        Ghost(room): Ghost<nat>,
    )
        requires
            old(self).wf(),
            tx_frames(frames_view(old(fs)@), PacketKind::OneRtt, base, *old(left) as nat, room),
        ensures
            final(self).wf(),
            final(self).tx_kept(*old(self)),
            final(self).now == old(self).now,
            final(self).streams == old(self).streams,
            final(self).polled == old(self).polled,
            tx_frames(frames_view(final(fs)@), PacketKind::OneRtt, base, *final(left) as nat, room),
            extends(frames_view(old(fs)@), frames_view(final(fs)@)),
            (final(fs)@.len() == old(fs)@.len() + 1) <==> (old(self).hs_done is Pending
                && final(self).hs_done is Sent),
            final(fs)@.len() == old(fs)@.len() ==> final(self).hs_done == old(self).hs_done,
            final(fs)@.len() == old(fs)@.len() + 1 ==> final(fs)@.last()@ is HandshakeDone,
            final(fs)@.len() <= old(fs)@.len() + 1,
            final(self).local_cids == old(self).local_cids,
            final(self).peer_cids == old(self).peer_cids,
    {
        //= https://www.rfc-editor.org/rfc/rfc9000#section-19.20
        //# Servers MUST
        //# NOT send a HANDSHAKE_DONE frame before completing the handshake.
        // P9: this is 1-RTT, so `complete`; the long-header spaces do not permit the frame.
        if matches!(self.hs_done, HsDone::Pending) {
            let f = Frame::HandshakeDone;
            if try_place(f, left, fs, Ghost(PacketKind::OneRtt), Ghost(base), Ghost(room)) {
                self.hs_done = HsDone::Sent;
            }
        }
    }

    /// Each NEW_CONNECTION_ID that fits, stopping at the first that does not.
    #[verifier::spinoff_prover]
    fn new_cid_frames(
        &mut self,
        left: &mut usize,
        fs: &mut Vec<Frame>,
        Ghost(base): Ghost<int>,
        Ghost(room): Ghost<nat>,
    )
        requires
            old(self).wf(),
            tx_frames(frames_view(old(fs)@), PacketKind::OneRtt, base, *old(left) as nat, room),
        ensures
            final(self).wf(),
            final(self).tx_kept(*old(self)),
            final(self).now == old(self).now,
            final(self).streams == old(self).streams,
            final(self).polled == old(self).polled,
            tx_frames(frames_view(final(fs)@), PacketKind::OneRtt, base, *final(left) as nat, room),
            extends(frames_view(old(fs)@), frames_view(final(fs)@)),
            final(self).hs_done == old(self).hs_done,
            final(self).local_cids.pending_spec().len() + final(fs)@.len() == old(self).local_cids.pending_spec().len()
                + old(fs)@.len(),
            final(self).peer_cids == old(self).peer_cids,
    {
        let ghost s0 = *self;
        let ghost sf0 = frames_view(fs@);
        let ghost total = self.local_cids.pending_spec().len() + fs@.len();
        loop
            invariant
                self.wf(),
                self.tx_kept(s0),
                self.streams == s0.streams,
                self.polled == s0.polled,
                self.hs_done == s0.hs_done,
                tx_frames(frames_view(fs@), PacketKind::OneRtt, base, *left as nat, room),
                extends(sf0, frames_view(fs@)),
                self.local_cids.pending_spec().len() + fs@.len() == total,
                self.peer_cids == s0.peer_cids,
            decreases self.local_cids.pending_spec().len(),
        {
            let f = match self.local_cids.pending_frame() {
                Some(f) => f,
                None => break,
            };
            proof {
                assert(f@ is NewConnectionId);
            }
            if !try_place(f, left, fs, Ghost(PacketKind::OneRtt), Ghost(base), Ghost(room)) {
                break;
            }
            self.local_cids.commit_pending();
        }
    }

    /// Each RETIRE_CONNECTION_ID that fits, stopping at the first that does not.
    #[verifier::spinoff_prover]
    fn retire_cid_frames(
        &mut self,
        left: &mut usize,
        fs: &mut Vec<Frame>,
        Ghost(base): Ghost<int>,
        Ghost(room): Ghost<nat>,
    )
        requires
            old(self).wf(),
            tx_frames(frames_view(old(fs)@), PacketKind::OneRtt, base, *old(left) as nat, room),
        ensures
            final(self).wf(),
            final(self).tx_kept(*old(self)),
            final(self).now == old(self).now,
            final(self).streams == old(self).streams,
            final(self).polled == old(self).polled,
            tx_frames(frames_view(final(fs)@), PacketKind::OneRtt, base, *final(left) as nat, room),
            extends(frames_view(old(fs)@), frames_view(final(fs)@)),
            final(self).hs_done == old(self).hs_done,
            final(self).peer_cids.retire_pending_spec().len() + final(fs)@.len() == old(
                self,
            ).peer_cids.retire_pending_spec().len() + old(fs)@.len(),
            final(self).local_cids == old(self).local_cids,
    {
        let ghost s0 = *self;
        let ghost sf0 = frames_view(fs@);
        let ghost total = self.peer_cids.retire_pending_spec().len() + fs@.len();
        loop
            invariant
                self.wf(),
                self.tx_kept(s0),
                self.streams == s0.streams,
                self.polled == s0.polled,
                self.hs_done == s0.hs_done,
                tx_frames(frames_view(fs@), PacketKind::OneRtt, base, *left as nat, room),
                extends(sf0, frames_view(fs@)),
                self.peer_cids.retire_pending_spec().len() + fs@.len() == total,
                self.local_cids == s0.local_cids,
            decreases self.peer_cids.retire_pending_spec().len(),
        {
            let f = match self.peer_cids.pending_retire() {
                Some(f) => f,
                None => break,
            };
            if !try_place(f, left, fs, Ghost(PacketKind::OneRtt), Ghost(base), Ghost(room)) {
                break;
            }
            self.peer_cids.commit_retire();
        }
    }

    /// Everything `Streams::poll_frames` has that fits `left`. Each frame it returns counts as sent:
    /// `polled` records them for P8.
    #[verifier::spinoff_prover]
    fn stream_frames(
        &mut self,
        left: usize,
        fs: &mut Vec<Frame>,
        Ghost(base): Ghost<int>,
        Ghost(room): Ghost<nat>,
    )
        requires
            old(self).wf(),
            old(self).polled@.len() == 0,
            tx_frames(frames_view(old(fs)@), PacketKind::OneRtt, base, left as nat, room),
        ensures
            final(self).wf(),
            final(self).tx_kept(*old(self)),
            final(self).now == old(self).now,
            tx_frames(frames_view(final(fs)@), PacketKind::OneRtt, base, 0, room),
            extends(frames_view(old(fs)@), frames_view(final(fs)@)),
            final(self).polled@ == frames_view(final(fs)@).skip(old(fs)@.len() as int),
            final(fs)@.len() == old(fs)@.len() ==> final(fs)@ == old(fs)@,
    {
        let ghost s0 = self.streams->0;
        let ghost out0 = fs@;
        match &mut self.streams {
            Some(s) => {
                s.poll_frames(left, fs);
                proof {
                    lemma_polled(s0, out0, fs@, base, left as nat, room);
                }
            },
            None => {
                proof {
                    assert(frames_view(fs@).skip(out0.len() as int) =~= Seq::<SpecFrame>::empty());
                }
            },
        }
        self.polled = Ghost(frames_view(fs@).skip(out0.len() as int));
    }

    /// The frames after the ACK, in a packet of space `k`: the ACK, if any, is all of `old(fs)`.
    #[verifier::spinoff_prover]
    fn collect_others(
        &mut self,
        k: PacketKind,
        left: usize,
        fs: &mut Vec<Frame>,
        Ghost(room): Ghost<nat>,
    )
        requires
            old(self).wf(),
            old(self).polled@.len() == 0,
            room <= MAX_DATAGRAM,
            tx_frames(frames_view(old(fs)@), k, old(fs)@.len() as int, left as nat, room),
        ensures
            final(self).wf(),
            final(self).tx_kept(*old(self)),
            final(self).now == old(self).now,
            tx_frames(frames_view(final(fs)@), k, old(fs)@.len() as int, 0, room),
            extends(frames_view(old(fs)@), frames_view(final(fs)@)),
            in_tail(final(self).polled@, frames_view(final(fs)@), old(fs)@.len() as int),
            !(k is OneRtt) ==> final(self).polled == old(self).polled,
    {
        let n = fs.len();
        let ghost base = n as int;
        let mut left = left;
        match k {
            PacketKind::OneRtt => {
                self.control_frames(&mut left, fs, Ghost(base), Ghost(room));
                let ghost mid = fs@;
                self.stream_frames(left, fs, Ghost(base), Ghost(room));
                proof {
                    lemma_in_tail(frames_view(fs@), mid.len() as int, base);
                    assert(fs@.len() == n ==> fs@ == mid);
                }
            },
            _ => {
                self.crypto_frame(k, &mut left, fs, Ghost(base), Ghost(room));
                proof {
                    assert(self.polled@ =~= Seq::<SpecFrame>::empty());
                }
            },
        }
        // Nothing ack-eliciting was appended, so `left` still counts.
        if fs.len() == n && self.probe(k) {
            let _ = try_place(Frame::Ping, &mut left, fs, Ghost(k), Ghost(base), Ghost(room));
        }
    }

    fn probe(&self, k: PacketKind) -> (r: bool) {
        match k {
            PacketKind::Initial => self.probe_i,
            PacketKind::Handshake => self.probe_h,
            PacketKind::OneRtt => self.probe_1,
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-13.2.1
    //# An endpoint MUST acknowledge all ack-eliciting Initial and Handshake
    //# packets immediately and all ack-eliciting 0-RTT and 1-RTT packets
    //# within its advertised max_ack_delay, with the following exception.
    /// An ACK-only packet may go, and its ACK is due: a packet that elicits no ACK gets none alone.
    #[verifier::spinoff_prover]
    fn ack_due(&self, k: PacketKind, now: u64) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == ack_is_due(self.recv(k), spec_ms_to_us(self.local_tp.max_ack_delay), now),
            r ==> self.recv(k).ack_only_allowed(),
    {
        if !self.recv_ref(k).ack_only_allowed() {
            return false;
        }
        match self.recv_ref(k).ack_deadline(ms_to_us(self.local_tp.max_ack_delay)) {
            Some(d) => d <= now,
            None => false,
        }
    }

    /// The packet with these frames and packet number length, before the commit.
    #[verifier::spinoff_prover]
    fn make_packet(
        &self,
        k: PacketKind,
        fs: Vec<Frame>,
        pn_len: u8,
        Ghost(base): Ghost<int>,
        Ghost(room): Ghost<nat>,
    ) -> (p: OutPacket)
        requires
            self.wf(),
            fs@.len() >= 1,
            room <= MAX_DATAGRAM,
            tx_frames(frames_view(fs@), k, base, 0, room),
            min_pn_len(self.sent(k).next_pn_spec(), self.sent(k).largest_acked_spec(), pn_len as nat),
        ensures
            p@.kind == k,
            p@.pn == self.sent(k).next_pn_spec(),
            p@.dcid == self.space_dcid(k),
            p@.frames == frames_view(fs@),
            out_packet_wf(p@, self.sent(k).largest_acked_spec()),
            out_packet_len(p@) <= room + self.header_bytes_spec(k) + p@.pn_len + AEAD_TAG_LEN + 3,
    {
        proof {
            self.paths.lemma_wf();
            assert(path_ok(self.paths.path(self.paths.active_spec())));
        }
        let ghost frames = frames_view(fs@);
        let (dcid, scid, spin) = match k {
            PacketKind::OneRtt => {
                let d = match self.paths.dcid(self.paths.active()) {
                    Some(d) => slice_to_vec(d),
                    None => {
                        proof {
                            assert(false);
                        }
                        Vec::new()
                    },
                };
                (d, Vec::new(), self.spin)
            },
            _ => {
                let l = self.ids.local_scid();
                (slice_to_vec(self.ids.client_scid()), slice_to_vec(l.as_slice()), false)
            },
        };
        let mut p = OutPacket {
            kind: k,
            dcid,
            scid,
            pn: self.sent_ref(k).next_pn(),
            pn_len,
            frames: fs,
            padding: 0,
            spin,
        };
        proof {
            assert(p@.frames == frames);
        }
        add_sample_padding(&mut p);
        proof {
            lemma_room(p@, room, self.header_bytes_spec(k));
        }
        p
    }

    /// The frames of the next packet of space `k`, taken from their sources; None if nothing is due.
    /// `room` is for the frames alone (`room_for`).
    #[verifier::spinoff_prover]
    fn collect_frames(
        &mut self,
        k: PacketKind,
        room: usize,
        can_pad: bool,
        now: u64,
    ) -> (r: Option<(OutPacket, bool, bool)>)
        requires
            old(self).wf(),
            old(self).phase_spec() is Open,
            old(self).live(k),
            old(self).polled@.len() == 0,
            room <= MAX_DATAGRAM,
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            final(self).phase_spec() is Open ==> final(self).tx_kept(*old(self)),
            final(self).crypto_same(*old(self)),
            r is None ==> final(self).now == old(self).now,
            final(self).phase_spec() is Open || final(self).phase_spec() is Closed,
            r is None ==> final(self).polled@.len() == 0,
            !(k is OneRtt) ==> final(self).polled == old(self).polled,
            // §13.2.1: a due ACK that fits goes out.
            final(self).phase_spec() is Open && old(self).recv(k).has_new() && old(self).recv(k).full_ack_fits(
                now,
                old(self).local_tp.ack_delay_exponent,
                room as int,
            ) && ack_is_due(
                old(self).recv(k),
                spec_ms_to_us(old(self).local_tp.max_ack_delay),
                now,
            ) ==> r is Some,
            r matches Some((p, eliciting, ack_only)) ==> {
                &&& final(self).phase_spec() is Open
                &&& old(self).packet_ok(p@, k, room as nat)
                &&& eliciting == exists|i: int|
                    0 <= i < p@.frames.len() && ack_eliciting(spec_frame_type(#[trigger] p@.frames[i]))
                &&& ack_only == !eliciting
                &&& ack_only ==> old(self).recv(k).ack_only_allowed() && p@.frames[0] is Ack
                &&& eliciting ==> old(self).inflight_total() < MAX_INFLIGHT
                &&& polled_in_packet(final(self).polled@, p@)
                &&& k is Initial && eliciting ==> can_pad
            },
    {
        proof {
            self.sent(k).lemma_wf();
        }
        let pn_len = match pn_encode_len(self.sent_ref(k).next_pn(), self.sent_ref(k).largest_acked()) {
            Some(n) => n,
            None => {
                self.lc.close_silently();
                self.streams = None;
                return None;
            },
        };
        let (mut fs, left) = self.start_frames(k, room, now);
        let n = fs.len();
        let ghost s0 = *self;
        let ghost sf0 = frames_view(fs@);
        // §14.1: an Initial with ack-eliciting frames is padded to 1200, which `can_pad` allows.
        let total = self.sent_i.inflight_len() as u64 + self.sent_h.inflight_len() as u64
            + self.sent_1.inflight_len() as u64;
        let may_elicit = !(matches!(k, PacketKind::Initial) && !can_pad) && self.recovery.can_send(total);
        if may_elicit {
            self.collect_others(k, left, &mut fs, Ghost(room as nat));
        }
        assert(!may_elicit ==> fs@.len() == n);
        let eliciting = is_ack_eliciting(fs.as_slice());
        proof {
            lemma_eliciting(fs@, n as int);
            lemma_ack_ok_extends(sf0, frames_view(fs@), s0.recv(k), k, room as nat);
            lemma_polled_empty(self.polled@, frames_view(fs@), n as int);
        }
        if !eliciting && !(n == 1 && self.ack_due(k, now)) {
            return None;
        }
        let p = self.make_packet(k, fs, pn_len, Ghost(n as int), Ghost(room as nat));
        Some((p, eliciting, !eliciting))
    }

    /// The next packet of space `k` is sent: the one after takes a larger number.
    #[verifier::spinoff_prover]
    fn commit_pn(&mut self, k: PacketKind)
        requires
            old(self).wf(),
            old(self).sent(k).next_pn_spec() < PN_MAX,
        ensures
            final(self).wf(),
            final(self).sent_kept(*old(self), k),
            final(self).seen_kept(*old(self)),
            final(self).recv(k) == old(self).recv(k),
            final(self).sent(k).next_pn_spec() == old(self).sent(k).next_pn_spec() + 1,
            final(self).sent(k).inflight_spec() == old(self).sent(k).inflight_spec(),
            final(self).inflight_total() == old(self).inflight_total(),
            final(self).tx_fixed(*old(self)),
            forall|j: PacketKind| #[trigger] final(self).sent(j).inflight_spec() == old(self).sent(j).inflight_spec(),
    {
        //= https://www.rfc-editor.org/rfc/rfc9000#section-17.2.3
        //# New packet numbers MUST be used for any new packets that are sent; as
        //# described in Section 17.2.5.3, reusing packet numbers could
        //# compromise packet protection.
        let _ = match k {
            PacketKind::Initial => self.sent_i.take_pn(),
            PacketKind::Handshake => self.sent_h.take_pn(),
            PacketKind::OneRtt => self.sent_1.take_pn(),
        };
    }

    /// An ACK frame went in a packet of space `k`.
    #[verifier::spinoff_prover]
    fn commit_ack(&mut self, k: PacketKind, ack_only: bool)
        requires
            old(self).wf(),
            ack_only ==> old(self).recv(k).ack_only_allowed(),
        ensures
            final(self).wf(),
            final(self).sends_kept(*old(self)),
            final(self).seen_kept(*old(self)),
            final(self).recv(k).unreported() == Set::<u64>::empty(),
            final(self).tx_fixed(*old(self)),
    {
        match k {
            PacketKind::Initial => self.recv_i.on_ack_sent(ack_only),
            PacketKind::Handshake => self.recv_h.on_ack_sent(ack_only),
            PacketKind::OneRtt => self.recv_1.on_ack_sent(ack_only),
        }
    }

    /// Records ack-eliciting packet `p`, sent at `now`, keeping its retransmittable frames (3d D5).
    #[verifier::spinoff_prover]
    fn commit_record(&mut self, k: PacketKind, p: &OutPacket, now: u64)
        requires
            old(self).wf(),
            out_packet_sized(p@),
            p@.pn + 1 == old(self).sent(k).next_pn_spec(),
            !has_pn(old(self).sent(k).inflight_spec(), p@.pn),
            old(self).inflight_total() < MAX_INFLIGHT,
        ensures
            final(self).wf(),
            final(self).seen_kept(*old(self)),
            final(self).recv(k) == old(self).recv(k),
            final(self).sent_kept(*old(self), k),
            final(self).sent(k).next_pn_spec() == old(self).sent(k).next_pn_spec(),
            recorded(old(self).sent(k).inflight_spec(), final(self).sent(k).inflight_spec(), p@),
            final(self).tx_timers(*old(self), now),
    {
        let size = packet_len(p);
        let rec = SentPacket {
            pn: p.pn,
            time: now,
            size: size as u64,
            ack_eliciting: true,
            frames: record_frames(p.frames.as_slice()),
        };
        let ghost o = self.sent(k).inflight_spec();
        let ghost g = rec;
        proof {
            lemma_record_holds(p.frames@, g.frames@);
        }
        match k {
            PacketKind::Initial => {
                self.sent_i.on_sent(rec);
                self.probe_i = false;
            },
            PacketKind::Handshake => {
                self.sent_h.on_sent(rec);
                self.probe_h = false;
            },
            PacketKind::OneRtt => {
                self.sent_1.on_sent(rec);
                self.probe_1 = false;
            },
        }
        self.recovery.on_packet_sent(k, p.pn, size as u64, now);
        self.idle.on_eliciting_sent(now);
        proof {
            assert(self.sent(k).inflight_spec() == o.push(g));
            assert(o.push(g).drop_last() =~= o);
            assert(g.time == now);
            assert forall|j: PacketKind| j != k implies #[trigger] self.sent(j) == old(self).sent(j) by {
                match k {
                    PacketKind::Initial => { match j { PacketKind::Handshake => {}, PacketKind::OneRtt => {}, PacketKind::Initial => {} } },
                    PacketKind::Handshake => { match j { PacketKind::Handshake => {}, PacketKind::OneRtt => {}, PacketKind::Initial => {} } },
                    PacketKind::OneRtt => { match j { PacketKind::Handshake => {}, PacketKind::OneRtt => {}, PacketKind::Initial => {} } },
                }
            }
            self.lemma_tx_recorded(*old(self), k, g, now);
        }
    }

    /// Every other space's records and packet numbers, every `largest_acked`, and what
    /// `poll_transmit` may not move.
    closed spec fn sent_kept(&self, o: Connection, k: PacketKind) -> bool {
        &&& self.sends_kept_but(o)
        &&& !(k is Initial) ==> self.sent_i.next_pn_spec() == o.sent_i.next_pn_spec()
            && self.sent_i.inflight_spec() == o.sent_i.inflight_spec()
        &&& !(k is Handshake) ==> self.sent_h.next_pn_spec() == o.sent_h.next_pn_spec()
            && self.sent_h.inflight_spec() == o.sent_h.inflight_spec()
        &&& !(k is OneRtt) ==> self.sent_1.next_pn_spec() == o.sent_1.next_pn_spec()
            && self.sent_1.inflight_spec() == o.sent_1.inflight_spec()
        &&& self.sent_i.largest_acked_spec() == o.sent_i.largest_acked_spec()
        &&& self.sent_h.largest_acked_spec() == o.sent_h.largest_acked_spec()
        &&& self.sent_1.largest_acked_spec() == o.sent_1.largest_acked_spec()
    }

    /// `sent_kept` as `sent(j)`.
    proof fn lemma_sent_kept(&self, o: Connection, k: PacketKind)
        requires
            self.sent_kept(o, k),
        ensures
            forall|j: PacketKind| j != k ==> #[trigger] self.sent(j).next_pn_spec() == o.sent(j).next_pn_spec(),
            forall|j: PacketKind| #[trigger] self.sent(j).largest_acked_spec() == o.sent(j).largest_acked_spec(),
    {
        assert forall|j: PacketKind| j != k implies #[trigger] self.sent(j).next_pn_spec() == o.sent(j).next_pn_spec() by {
            match j {
                PacketKind::Initial => {},
                PacketKind::Handshake => {},
                PacketKind::OneRtt => {},
            }
        }
        assert forall|j: PacketKind| #[trigger] self.sent(j).largest_acked_spec() == o.sent(j).largest_acked_spec() by {
            match j {
                PacketKind::Initial => {},
                PacketKind::Handshake => {},
                PacketKind::OneRtt => {},
            }
        }
    }

    /// Every space has seen the same packet numbers.
    closed spec fn seen_kept(&self, o: Connection) -> bool {
        &&& self.recv_i.seen() == o.recv_i.seen()
        &&& self.recv_h.seen() == o.recv_h.seen()
        &&& self.recv_1.seen() == o.recv_1.seen()
    }

    proof fn lemma_seen_kept(&self, o: Connection)
        requires
            self.seen_kept(o),
        ensures
            forall|j: PacketKind| #[trigger] self.recv(j).seen() == o.recv(j).seen(),
    {
        assert forall|j: PacketKind| #[trigger] self.recv(j).seen() == o.recv(j).seen() by {
            match j {
                PacketKind::Initial => {},
                PacketKind::Handshake => {},
                PacketKind::OneRtt => {},
            }
        }
    }

    closed spec fn sends_kept_but(&self, o: Connection) -> bool {
        &&& self.out_log@ == o.out_log@
        &&& self.paths == o.paths
        &&& self.ids == o.ids
        &&& self.lc == o.lc
        &&& self.complete == o.complete
        &&& self.live_i == o.live_i
        &&& self.live_h == o.live_h
        &&& self.streams == o.streams
        &&& self.polled == o.polled
    }

    /// `sends_kept_but`, and every `sent`.
    closed spec fn sends_kept(&self, o: Connection) -> bool {
        &&& self.sends_kept_but(o)
        &&& self.sent_i == o.sent_i
        &&& self.sent_h == o.sent_h
        &&& self.sent_1 == o.sent_1
    }

    /// Commits `p`, from `collect_frames`: its packet number, its ACK and its record.
    #[verifier::spinoff_prover]
    fn commit_space_packet(&mut self, k: PacketKind, p: &OutPacket, eliciting: bool, ack_only: bool, now: u64)
        requires
            old(self).wf(),
            p@.kind == k,
            p@.pn == old(self).sent(k).next_pn_spec(),
            p@.pn < PN_MAX,
            out_packet_sized(p@),
            ack_ok(p@.frames, old(self).recv(k)),
            ack_only ==> old(self).recv(k).ack_only_allowed() && p@.frames[0] is Ack,
            eliciting ==> old(self).inflight_total() < MAX_INFLIGHT,
        ensures
            final(self).wf(),
            final(self).sent_kept(*old(self), k),
            final(self).sent(k).next_pn_spec() == p@.pn + 1,
            final(self).seen_kept(*old(self)),
            p@.frames[0] matches SpecFrame::Ack(a) ==> forall|u: u64|
                #[trigger] old(self).recv(k).unreported().contains(u) ==> ack_contains(a, u),
            p@.frames[0] is Ack ==> final(self).recv(k).unreported() == Set::<u64>::empty(),
            eliciting ==> recorded(old(self).sent(k).inflight_spec(), final(self).sent(k).inflight_spec(), p@),
            !eliciting ==> final(self).sent(k).inflight_spec() == old(self).sent(k).inflight_spec(),
            final(self).tx_timers(*old(self), now),
    {
        let ghost s0 = *self;
        proof {
            lemma_not_inflight(s0.sent(k));
        }
        self.commit_pn(k);
        let ghost s1 = *self;
        proof {
            self.lemma_tx_same(s0, now);
        }
        if matches!(p.frames[0], Frame::Ack(_)) {
            proof {
                //= https://www.rfc-editor.org/rfc/rfc9000#section-13.2.1
                //# Every packet SHOULD be acknowledged at least once, and ack-eliciting
                //# packets MUST be acknowledged at least once within the maximum delay
                //# an endpoint communicated using the max_ack_delay transport parameter;
                //# see Section 18.2.
                lemma_ack_reports(p@.frames[0]->Ack_0, s0.recv(k));
                assert(self.recv(k) == s0.recv(k));
            }
            self.commit_ack(k, ack_only);
            proof {
                assert forall|j: PacketKind| #[trigger] self.sent(j).inflight_spec() == s1.sent(j).inflight_spec() by {
                    assert(self.sent(j) == s1.sent(j)) by {
                        match j {
                            PacketKind::Initial => {},
                            PacketKind::Handshake => {},
                            PacketKind::OneRtt => {},
                        }
                    }
                }
                self.lemma_tx_same(s1, now);
                self.lemma_tx_trans(s1, s0, now);
            }
        }
        let ghost s2 = *self;
        if eliciting {
            self.commit_record(k, p, now);
            proof {
                self.lemma_tx_trans(s2, s0, now);
            }
        }
    }

    /// The next packet of space `k`, its frames taken and its packet number, ACK and record
    /// committed; the caller commits the datagram.
    #[verifier::spinoff_prover]
    fn build_space_packet(
        &mut self,
        k: PacketKind,
        room: usize,
        can_pad: bool,
        now: u64,
    ) -> (r: Option<(OutPacket, bool, bool)>)
        requires
            old(self).wf(),
            old(self).phase_spec() is Open,
            old(self).live(k),
            old(self).polled@.len() == 0,
            old(self).sent(k).next_pn_spec() < PN_MAX,
            room <= MAX_DATAGRAM,
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            r is None ==> final(self).polled@.len() == 0,
            r is None && final(self).phase_spec() is Open ==> final(self).tx_kept(*old(self)),
            r is None ==> final(self).now == old(self).now,
            final(self).tx_timers(*old(self), now),
            !(k is OneRtt) ==> final(self).polled == old(self).polled,
            r is None && final(self).phase_spec() is Open && old(self).recv(k).has_new() && old(self).recv(k).full_ack_fits(
                now,
                old(self).local_tp.ack_delay_exponent,
                room as int,
            ) ==> !ack_is_due(
                old(self).recv(k),
                spec_ms_to_us(old(self).local_tp.max_ack_delay),
                now,
            ),
            r matches Some((p, eliciting, _)) ==> {
                &&& old(self).packet_ok(p@, k, room as nat)
                &&& polled_in_packet(final(self).polled@, p@)
                &&& k is Initial && eliciting ==> can_pad
                &&& eliciting == exists|i: int|
                    0 <= i < p@.frames.len() && ack_eliciting(spec_frame_type(#[trigger] p@.frames[i]))
                &&& eliciting ==> recorded(old(self).sent(k).inflight_spec(), final(self).sent(k).inflight_spec(), p@)
                &&& !eliciting ==> final(self).sent(k).inflight_spec() == old(self).sent(k).inflight_spec()
                &&& final(self).sent(k).next_pn_spec() == p@.pn + 1
                &&& final(self).paths == old(self).paths
                &&& final(self).ids == old(self).ids
                &&& final(self).lc == old(self).lc
                &&& final(self).complete == old(self).complete
                &&& final(self).live_i == old(self).live_i
                &&& final(self).live_h == old(self).live_h
                &&& forall|j: PacketKind| j != k ==> #[trigger] final(self).sent(j).next_pn_spec()
                    == old(self).sent(j).next_pn_spec()
                &&& forall|j: PacketKind| #[trigger] final(self).sent(j).largest_acked_spec()
                    == old(self).sent(j).largest_acked_spec()
                &&& forall|j: PacketKind| #[trigger] final(self).recv(j).seen() == old(self).recv(j).seen()
            },
    {
        let ghost s0 = *self;
        let (p, eliciting, ack_only) = match self.collect_frames(k, room, can_pad, now) {
            Some(x) => x,
            None => {
                proof {
                    if self.phase_spec() is Open {
                        self.lemma_tx_kept_timers(s0, now);
                    } else {
                        self.lemma_tx_closed(s0, now);
                    }
                }
                return None;
            },
        };
        proof {
            self.lemma_tx_kept_timers(s0, now);
            assert(self.recv(k) == s0.recv(k));
            assert(self.sent(k) == s0.sent(k));
            assert(self.inflight_total() == s0.inflight_total());
        }
        let ghost s1 = *self;
        self.commit_space_packet(k, &p, eliciting, ack_only, now);
        proof {
            self.lemma_tx_trans(s1, s0, now);
            self.lemma_sent_kept(s1, k);
            assert(self.seen_kept(s0));
            self.lemma_seen_kept(s0);
            assert(s1.sent_i == s0.sent_i && s1.sent_h == s0.sent_h && s1.sent_1 == s0.sent_1);
            assert forall|j: PacketKind| #[trigger] s1.sent(j) == s0.sent(j) by {
                match j {
                    PacketKind::Initial => {},
                    PacketKind::Handshake => {},
                    PacketKind::OneRtt => {},
                }
            }
        }
        Some((p, eliciting, ack_only))
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-8.1
    //# Prior to validating the client address, servers MUST NOT send more
    //# than three times as many bytes as the number of bytes they have
    //# received.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-8.1
    //= type=exception
    //= reason=client-only
    //# Clients MUST ensure that UDP datagrams containing Initial packets
    //# have UDP payloads of at least 1200 bytes, adding PADDING frames as
    //# necessary.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-8.1
    //= type=exception
    //= reason=client-only
    //# To
    //# prevent this deadlock, clients MUST send a packet on a Probe Timeout
    //# (PTO); see Section 6.2 of [QUIC-RECOVERY].
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-8.1
    //= type=exception
    //= reason=client-only
    //# Specifically, the client
    //# MUST send an Initial packet in a UDP datagram that contains at least
    //# 1200 bytes if it does not have Handshake keys, and otherwise send a
    //# Handshake packet.
    /// `d` went out on `q`: the only `Paths::on_sent` and the only log push, so the budget's `Sent`
    /// entries are exactly the log (P1). The caller snapshots `next_pn` before committing `d`'s
    /// packets, which puts their numbers above every logged one.
    #[verifier::spinoff_prover]
    fn commit_datagram(&mut self, q: PathId, d: &OutDatagram)
        requires
            old(self).wf(),
            old(self).paths.has(q),
            d@.path == q,
            out_datagram_sized(d@),
            out_datagram_len(d@) <= old(self).paths.budget_spec(q),
            out_datagram_len(d@) <= MAX_DATAGRAM,
            forall|k: PacketKind|
                #[trigger] pns_fresh(
                    log_pns(old(self).out_log@, k),
                    packets_pns(d@.packets, k),
                    old(self).sent(k).next_pn_spec(),
                ),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log().push(d@),
            final(self).sends_only_logged(*old(self)),
            final(self).lc == old(self).lc,
            final(self).paths_charged(*old(self), q),
            forall|t: u64| #[trigger] final(self).tx_timers(*old(self), t),
            final(self).expiries_kept(*old(self)),
    {
        let ghost s0 = *self;
        let n = datagram_len(d);
        self.paths.on_sent(q, n as u64);
        self.out_log = Ghost(self.out_log@.push(d@));
        proof {
            self.lemma_committed(s0, q, d@);
            lemma_pn_step(s0.out_log@, d@, PacketKind::Initial, s0.sent(PacketKind::Initial).next_pn_spec());
            lemma_pn_step(s0.out_log@, d@, PacketKind::Handshake, s0.sent(PacketKind::Handshake).next_pn_spec());
            lemma_pn_step(s0.out_log@, d@, PacketKind::OneRtt, s0.sent(PacketKind::OneRtt).next_pn_spec());
            assert(self.amp_blocked_spec() || !s0.amp_blocked_spec());
            reveal(Connection::tx_timers);
            assert forall|t: u64| #[trigger] self.tx_timers(s0, t) by {
                assert forall|k: PacketKind| #[trigger] self.sent(k).inflight_spec() == s0.sent(k).inflight_spec() by {
                    match k {
                        PacketKind::Initial => {},
                        PacketKind::Handshake => {},
                        PacketKind::OneRtt => {},
                    }
                }
                assert forall|r: PathId|
                    #[trigger] self.paths.has(r) && timed(self.paths.path(r)) implies s0.paths.has(r) && (self.paths.path(r).challenge
                        == s0.paths.path(r).challenge && timed(s0.paths.path(r)) || t <= self.paths.path(r).challenge.unwrap().1) by {
                    assert(s0.paths.path(r).owed == self.paths.path(r).owed);
                }
            }
        }
    }

    /// `self`'s paths are `o`'s with `q` charged for a datagram: its budget and trace, nothing else.
    closed spec fn paths_charged(&self, o: Connection, q: PathId) -> bool {
        &&& kept(o.paths, self.paths, q)
        &&& self.paths.path(q).dcid == o.paths.path(q).dcid
        &&& self.paths.path(q).peer_used == o.paths.path(q).peer_used
        &&& self.paths.path(q).responses == o.paths.path(q).responses
        &&& self.paths.path(q).responses_taken == o.paths.path(q).responses_taken
        &&& self.paths.path(q).challenge == o.paths.path(q).challenge
    }

    /// Only the path's budget and the log differ.
    closed spec fn sends_only_logged(&self, o: Connection) -> bool {
        &&& self.sent_i == o.sent_i
        &&& self.sent_h == o.sent_h
        &&& self.sent_1 == o.sent_1
        &&& self.recv_i == o.recv_i
        &&& self.recv_h == o.recv_h
        &&& self.recv_1 == o.recv_1
        &&& self.polled == o.polled
        &&& self.complete == o.complete
    }

    proof fn lemma_only_logged(&self, o: Connection)
        requires
            self.sends_only_logged(o),
        ensures
            forall|j: PacketKind| #[trigger] self.sent(j) == o.sent(j),
            forall|j: PacketKind| #[trigger] self.recv(j) == o.recv(j),
    {
        assert forall|j: PacketKind| #[trigger] self.sent(j) == o.sent(j) by {
            match j {
                PacketKind::Initial => {},
                PacketKind::Handshake => {},
                PacketKind::OneRtt => {},
            }
        }
        assert forall|j: PacketKind| #[trigger] self.recv(j) == o.recv(j) by {
            match j {
                PacketKind::Initial => {},
                PacketKind::Handshake => {},
                PacketKind::OneRtt => {},
            }
        }
    }

    /// `self` is `o` with one datagram logged and counted on its path.
    proof fn lemma_committed(&self, o: Connection, q: PathId, d: SpecOutDatagram)
        requires
            o.wf(),
            o.paths.has(q),
            d.path == q,
            self.paths.wf(),
            kept(o.paths, self.paths, q),
            self.paths.amp_trace(q) == o.paths.amp_trace(q).push(AmpEv::Sent(out_datagram_len(d))),
            amp_ok(self.paths.amp_trace(q)),
            self.paths.path(q).dcid == o.paths.path(q).dcid,
            self.paths.path(q).peer_used == o.paths.path(q).peer_used,
            self.out_log@ == o.out_log@.push(d),
            self.peer_cids == o.peer_cids,
        ensures
            self.wf_amp(),
            self.wf_log_paths(),
            self.wf_dcids(),
    {
        let log = o.out_log@;
        let t = o.paths.amp_trace(q);
        assert(t.push(AmpEv::Sent(out_datagram_len(d))).drop_last() =~= t);
        assert(self.out_log@.drop_last() =~= log);
        self.paths.lemma_wf();
        assert(o.paths.has(q));
        assert(self.wf_amp()) by {
            assert forall|r: PathId| #[trigger] self.paths.has(r) implies amp_ok(
                self.paths.amp_trace(r),
            ) && sent_entries(self.paths.amp_trace(r)) == log_sends(self.out_log@, r) by {
                assert(path_ok(self.paths.path(r)));
                assert(o.paths.has(r));
            }
        }
        assert(self.wf_log_paths()) by {
            assert forall|i: int| 0 <= i < self.out_log@.len() implies #[trigger] self.paths.index_spec(
                self.out_log@[i].path,
            ) is Some by {
                if i < log.len() {
                    assert(self.out_log@[i] == log[i]);
                    assert(o.paths.index_spec(log[i].path) is Some);
                } else {
                    assert(self.out_log@[i] == d);
                    assert(self.paths.has(q));
                }
            }
        }
        self.lemma_dcids_same(o, q);
    }

    /// The Destination Connection ID of every packet: the long-header spaces end at `complete`.
    closed spec fn tx_dcid(&self) -> Seq<u8> {
        if self.complete {
            self.active_dcid_spec()
        } else {
            self.ids@.client_scid
        }
    }

    /// `p` is a packet `transmit_ok` accepts, by what `self` was before the datagram was built.
    closed spec fn packet_built(&self, p: SpecOutPacket) -> bool {
        &&& out_packet_wf(p, self.sent(p.kind).largest_acked_spec())
        &&& self.sent(p.kind).next_pn_spec() <= p.pn
        &&& p.dcid == self.tx_dcid()
        &&& p.kind is OneRtt ==> self.complete
        &&& no_path_frames(p.frames)
        &&& forall|j: int|
            0 <= j < p.frames.len() ==> (#[trigger] p.frames[j] matches SpecFrame::Ack(a) ==> forall|pn: u64|
                #[trigger] ack_contains(a, pn) ==> self.recv(p.kind).seen().contains(pn))
        &&& forall|j: int| 0 <= j < p.frames.len() && #[trigger] p.frames[j] is HandshakeDone ==> self.complete
    }

    /// `self` is `o` with the packets `s` built, not yet sent.
    closed spec fn built_ok(&self, o: Connection, s: Seq<SpecOutPacket>) -> bool {
        &&& self.paths == o.paths
        &&& self.ids == o.ids
        &&& self.lc == o.lc
        &&& self.complete == o.complete
        &&& self.live_i == o.live_i
        &&& self.live_h == o.live_h
        &&& self.out_log@ == o.out_log@
        &&& forall|j: PacketKind| #[trigger] self.sent(j).largest_acked_spec() == o.sent(j).largest_acked_spec()
        &&& forall|j: PacketKind| #[trigger] self.recv(j).seen() == o.recv(j).seen()
        &&& forall|j: PacketKind| o.sent(j).next_pn_spec() <= #[trigger] self.sent(j).next_pn_spec()
        &&& forall|i: int| 0 <= i < s.len() ==> o.packet_built(#[trigger] s[i])
        &&& forall|k: PacketKind|
            pns_built(#[trigger] packets_pns(s, k), o.sent(k).next_pn_spec(), self.sent(k).next_pn_spec())
    }

    /// `tx_kept` as `sent(j)`, `recv(j)` and `live(j)`.
    proof fn lemma_tx_kept(&self, o: Connection)
        requires
            self.tx_kept(o),
        ensures
            forall|j: PacketKind| #[trigger] self.sent(j) == o.sent(j),
            forall|j: PacketKind| #[trigger] self.recv(j) == o.recv(j),
            forall|j: PacketKind| #[trigger] self.live(j) == o.live(j),
    {
        assert forall|j: PacketKind| #[trigger] self.sent(j) == o.sent(j) by {
            match j {
                PacketKind::Initial => {},
                PacketKind::Handshake => {},
                PacketKind::OneRtt => {},
            }
        }
        assert forall|j: PacketKind| #[trigger] self.recv(j) == o.recv(j) by {
            match j {
                PacketKind::Initial => {},
                PacketKind::Handshake => {},
                PacketKind::OneRtt => {},
            }
        }
        assert forall|j: PacketKind| #[trigger] self.live(j) == o.live(j) by {
            match j {
                PacketKind::Initial => {},
                PacketKind::Handshake => {},
                PacketKind::OneRtt => {},
            }
        }
    }

    proof fn lemma_built_empty(&self, o: Connection)
        requires
            self.tx_kept(o),
        ensures
            self.built_ok(o, Seq::empty()),
    {
        self.lemma_tx_kept(o);
        assert forall|k: PacketKind|
            pns_built(#[trigger] packets_pns(Seq::empty(), k), o.sent(k).next_pn_spec(), self.sent(k).next_pn_spec()) by {
            assert(packets_pns(Seq::empty(), k) =~= Seq::<u64>::empty());
        }
    }

    /// A space that sent nothing changed nothing `built_ok` reads.
    proof fn lemma_built_kept(&self, c: Connection, o: Connection, s: Seq<SpecOutPacket>)
        requires
            c.built_ok(o, s),
            self.tx_kept(c),
        ensures
            self.built_ok(o, s),
    {
        self.lemma_tx_kept(c);
        assert forall|k: PacketKind|
            pns_built(#[trigger] packets_pns(s, k), o.sent(k).next_pn_spec(), self.sent(k).next_pn_spec()) by {
            assert(self.sent(k) == c.sent(k));
            assert(pns_built(packets_pns(s, k), o.sent(k).next_pn_spec(), c.sent(k).next_pn_spec()));
        }
        assert forall|j: PacketKind| o.sent(j).next_pn_spec() <= #[trigger] self.sent(j).next_pn_spec() by {
            assert(self.sent(j) == c.sent(j));
            assert(o.sent(j).next_pn_spec() <= c.sent(j).next_pn_spec());
        }
    }

    /// `p`, numbered from `c`'s space `p.kind`, joins `s` once `self` has taken its number.
    proof fn lemma_built_push(&self, c: Connection, o: Connection, s: Seq<SpecOutPacket>, p: SpecOutPacket)
        requires
            c.wf(),
            c.built_ok(o, s),
            c.live(p.kind),
            p.pn == c.sent(p.kind).next_pn_spec(),
            p.dcid == c.space_dcid(p.kind),
            out_packet_wf(p, c.sent(p.kind).largest_acked_spec()),
            ack_ok(p.frames, c.recv(p.kind)),
            no_path_frames(p.frames),
            self.paths == c.paths,
            self.ids == c.ids,
            self.lc == c.lc,
            self.complete == c.complete,
            self.live_i == c.live_i,
            self.live_h == c.live_h,
            self.out_log@ == c.out_log@,
            self.sent(p.kind).next_pn_spec() == p.pn + 1,
            forall|j: PacketKind| j != p.kind ==> #[trigger] self.sent(j).next_pn_spec() == c.sent(j).next_pn_spec(),
            forall|j: PacketKind| #[trigger] self.sent(j).largest_acked_spec() == c.sent(j).largest_acked_spec(),
            forall|j: PacketKind| #[trigger] self.recv(j).seen() == c.recv(j).seen(),
        ensures
            self.built_ok(o, s.push(p)),
    {
        let k = p.kind;
        let s2 = s.push(p);
        assert(c.wf_parts());
        assert(o.sent(k).largest_acked_spec() == c.sent(k).largest_acked_spec());
        assert(c.recv(k).seen() == o.recv(k).seen());
        assert(o.sent(k).next_pn_spec() <= c.sent(k).next_pn_spec());
        assert(p.dcid == o.tx_dcid()) by {
            match k {
                PacketKind::OneRtt => {},
                _ => {},
            }
        }
        assert forall|j: int| 0 <= j < p.frames.len() implies (#[trigger] p.frames[j] matches SpecFrame::Ack(a)
            ==> forall|pn: u64| #[trigger] ack_contains(a, pn) ==> o.recv(k).seen().contains(pn)) by {
            if let SpecFrame::Ack(a) = p.frames[j] {
                assert(ack_full(a, c.recv(k)));
            }
        }
        assert forall|j: int| 0 <= j < p.frames.len() && #[trigger] p.frames[j] is HandshakeDone implies o.complete by {
            assert(frame_permitted(spec_frame_type(p.frames[j]), k));
            match k {
                PacketKind::OneRtt => {},
                _ => {},
            }
        }
        assert(o.packet_built(p));
        assert forall|i: int| 0 <= i < s2.len() implies o.packet_built(#[trigger] s2[i]) by {
            if i < s.len() {
                assert(s2[i] == s[i]);
            }
        }
        assert(s2.drop_last() =~= s);
        assert(s2.last() == p);
        assert forall|j: PacketKind| o.sent(j).next_pn_spec() <= #[trigger] self.sent(j).next_pn_spec() by {
            assert(o.sent(j).next_pn_spec() <= c.sent(j).next_pn_spec());
        }
        assert forall|m: PacketKind|
            pns_built(#[trigger] packets_pns(s2, m), o.sent(m).next_pn_spec(), self.sent(m).next_pn_spec()) by {
            let a = packets_pns(s, m);
            assert(pns_built(a, o.sent(m).next_pn_spec(), c.sent(m).next_pn_spec()));
            if m == k {
                let b = packets_pns(s2, m);
                assert(b == a.push(p.pn));
                assert forall|x: int, y: int| 0 <= x < y < b.len() implies #[trigger] b[x] < #[trigger] b[y] by {
                    if y < a.len() {
                        assert(b[x] == a[x] && b[y] == a[y]);
                    } else {
                        assert(b[x] == a[x] && b[y] == p.pn);
                    }
                }
                assert forall|x: int| 0 <= x < b.len() implies #[trigger] b[x] < self.sent(m).next_pn_spec()
                    && o.sent(m).next_pn_spec() <= b[x] by {
                    if x < a.len() {
                        assert(b[x] == a[x]);
                    } else {
                        assert(b[x] == p.pn);
                    }
                }
            } else {
                assert(packets_pns(s2, m) == a);
                assert(self.sent(m).next_pn_spec() == c.sent(m).next_pn_spec());
            }
        }
    }

    /// `pad_datagram`'s `s2` is `s`, as far as `built_ok` reads.
    proof fn lemma_built_padded(&self, o: Connection, s: Seq<SpecOutPacket>, s2: Seq<SpecOutPacket>, i: int, x: nat)
        requires
            self.built_ok(o, s),
            0 <= i < s.len(),
            s2 == s.update(i, padded(s[i], x)),
            forall|m: int, la: Option<u64>|
                #![trigger out_packet_wf(s2[m], la)]
                0 <= m < s.len() && out_packet_wf(s[m], la) ==> out_packet_wf(s2[m], la),
        ensures
            self.built_ok(o, s2),
            has_eliciting_initial(s2) == has_eliciting_initial(s),
    {
        assert forall|m: int| 0 <= m < s2.len() implies o.packet_built(#[trigger] s2[m]) by {
            assert(o.packet_built(s[m]));
            assert(s2[m].kind == s[m].kind);
            assert(s2[m].frames == s[m].frames);
            assert(out_packet_wf(s[m], o.sent(s[m].kind).largest_acked_spec()));
            assert(out_packet_wf(s2[m], o.sent(s[m].kind).largest_acked_spec()));
        }
        assert forall|k: PacketKind|
            pns_built(#[trigger] packets_pns(s2, k), o.sent(k).next_pn_spec(), self.sent(k).next_pn_spec()) by {
            lemma_pns_padded(s, i, x, k);
            assert(pns_built(packets_pns(s, k), o.sent(k).next_pn_spec(), self.sent(k).next_pn_spec()));
        }
        if has_eliciting_initial(s) {
            let (a, b) = choose|a: int, b: int|
                0 <= a < s.len() && s[a].kind is Initial && 0 <= b < s[a].frames.len() && ack_eliciting(
                    spec_frame_type(#[trigger] s[a].frames[b]),
                );
            assert(s2[a].frames[b] == s[a].frames[b]);
        }
        if has_eliciting_initial(s2) {
            let (a, b) = choose|a: int, b: int|
                0 <= a < s2.len() && s2[a].kind is Initial && 0 <= b < s2[a].frames.len() && ack_eliciting(
                    spec_frame_type(#[trigger] s2[a].frames[b]),
                );
            assert(s[a].frames[b] == s2[a].frames[b]);
        }
    }

    /// What `commit_datagram` asks of the packets' numbers.
    proof fn lemma_built_fresh(&self, o: Connection, s: Seq<SpecOutPacket>)
        requires
            o.wf(),
            self.built_ok(o, s),
        ensures
            forall|k: PacketKind|
                #[trigger] pns_fresh(log_pns(self.out_log@, k), packets_pns(s, k), self.sent(k).next_pn_spec()),
    {
        assert(o.wf_pn());
        assert forall|k: PacketKind|
            #[trigger] pns_fresh(log_pns(self.out_log@, k), packets_pns(s, k), self.sent(k).next_pn_spec()) by {
            let l = log_pns(self.out_log@, k);
            let b = packets_pns(s, k);
            assert(pns_built(b, o.sent(k).next_pn_spec(), self.sent(k).next_pn_spec()));
            assert(pns_ok(l, o.sent(k).next_pn_spec())) by {
                match k {
                    PacketKind::Initial => {},
                    PacketKind::Handshake => {},
                    PacketKind::OneRtt => {},
                }
            }
            assert forall|i: int, j: int| 0 <= i < l.len() && 0 <= j < b.len() implies #[trigger] l[i] < #[trigger] b[j] by {
                assert(l[i] < o.sent(k).next_pn_spec());
                assert(o.sent(k).next_pn_spec() <= b[j]);
            }
        }
    }

    /// `transmit_ok` and P6, for the packets of `d`, once `self` has committed it after `c`.
    proof fn lemma_built_sent(&self, c: Connection, o: Connection, d: SpecOutDatagram)
        requires
            c.built_ok(o, d.packets),
            out_datagram_len(d) <= MAX_DATAGRAM,
            forall|j: PacketKind| #[trigger] self.sent(j) == c.sent(j),
            forall|j: PacketKind| #[trigger] self.recv(j) == c.recv(j),
            self.complete == c.complete,
            o.wf(),
            self.wf(),
            d.path == o.paths.active_spec(),
            self.paths_charged(c, d.path),
        ensures
            transmit_ok(o, *self, d),
            same_dcid(d),
            self.path_rules(o, d),
    {
        self.lemma_built_rules(c, o, d);
        assert forall|i: int| 0 <= i < d.packets.len() implies out_packet_wf(
            #[trigger] d.packets[i],
            self.sent(d.packets[i].kind).largest_acked_spec(),
        ) by {
            let k = d.packets[i].kind;
            assert(o.packet_built(d.packets[i]));
            assert(self.sent(k) == c.sent(k));
            assert(c.sent(k).largest_acked_spec() == o.sent(k).largest_acked_spec());
        }
        assert forall|i: int| 0 <= i < d.packets.len() implies o.sent((#[trigger] d.packets[i]).kind).next_pn_spec()
            <= d.packets[i].pn by {
            assert(o.packet_built(d.packets[i]));
        }
        assert forall|k: PacketKind| #[trigger] pns_ok(packets_pns(d.packets, k), self.sent(k).next_pn_spec()) by {
            assert(self.sent(k) == c.sent(k));
            assert(pns_built(packets_pns(d.packets, k), o.sent(k).next_pn_spec(), c.sent(k).next_pn_spec()));
        }
        assert forall|i: int, j: int| 0 <= i < d.packets.len() && 0 <= j < d.packets[i].frames.len() implies (
        #[trigger] d.packets[i].frames[j] matches SpecFrame::Ack(a) ==> forall|pn: u64|
            #[trigger] ack_contains(a, pn) ==> self.recv(d.packets[i].kind).seen().contains(pn)) by {
            let k = d.packets[i].kind;
            assert(o.packet_built(d.packets[i]));
            assert(self.recv(k) == c.recv(k));
            assert(c.recv(k).seen() == o.recv(k).seen());
        }
        assert forall|i: int, j: int|
            0 <= i < d.packets.len() && 0 <= j < d.packets[i].frames.len() && #[trigger] d.packets[i].frames[j]
                is HandshakeDone implies self.live(PacketKind::OneRtt) by {
            assert(o.packet_built(d.packets[i]));
        }
        assert forall|i: int, j: int| 0 <= i < d.packets.len() && 0 <= j < d.packets.len() implies #[trigger] d.packets[i].dcid
            == #[trigger] d.packets[j].dcid by {
            assert(o.packet_built(d.packets[i]));
            assert(o.packet_built(d.packets[j]));
        }
    }

    /// P12-P14 of a datagram from the data or close builders: on the active path, no PATH frame.
    proof fn lemma_built_rules(&self, c: Connection, o: Connection, d: SpecOutDatagram)
        requires
            c.built_ok(o, d.packets),
            o.wf(),
            self.wf(),
            d.path == o.paths.active_spec(),
            self.paths_charged(c, d.path),
        ensures
            self.path_rules(o, d),
    {
        reveal(Connection::path_rules);
        o.paths.lemma_wf();
        assert(self.paths.has(d.path)) by {
            assert(o.paths.has(d.path));
        }
        assert forall|i: int, j: int|
            0 <= i < d.packets.len() && 0 <= j < d.packets[i].frames.len() implies !(#[trigger] d.packets[i].frames[j]
            is PathChallenge) && !(d.packets[i].frames[j] is PathResponse) by {
            assert(o.packet_built(d.packets[i]));
        }
        assert(self.dcid_unshared(d)) by {
            assert(o.paths.path(d.path).dcid is Some);
            assert forall|i: int| 0 <= i < d.packets.len() && #[trigger] d.packets[i].kind is OneRtt implies self.dcid_held(
                d.path,
                d.packets[i].dcid,
            ) by {
                assert(o.packet_built(d.packets[i]));
                assert(self.paths.path(d.path).dcid == o.paths.path(d.path).dcid);
                self.lemma_held(d.path, d.packets[i].dcid);
            }
        }
    }

    /// §9.5 for a path holding `c`: the pair conjunct of `wf_dcids`.
    proof fn lemma_held(&self, q: PathId, c: Seq<u8>)
        requires
            self.wf(),
            self.paths.has(q),
            self.paths.path(q).dcid == Some(c),
        ensures
            self.dcid_held(q, c),
    {
    }

    /// Whether `paths.mtu_failed` holds for `q`.
    pub closed spec fn mtu_failed_at(&self, q: PathId) -> bool {
        self.paths.mtu_failed_spec(q)
    }

    /// Path `q` is in the path table.
    pub closed spec fn has_path(&self, q: PathId) -> bool {
        self.paths.has(q)
    }

    /// The path table is `o`'s.
    pub closed spec fn paths_kept(&self, o: Connection) -> bool {
        self.paths == o.paths
    }

    /// Path `q`'s amplification trace: its receives, sends and validation, in order (§8.1).
    pub closed spec fn amp_trace(&self, q: PathId) -> Seq<AmpEv> {
        self.paths.amp_trace(q)
    }

    /// How many bytes path `q` may be sent.
    pub closed spec fn budget_at(&self, q: PathId) -> u64 {
        self.paths.budget_spec(q)
    }

    /// P12 (§8.2.2): every PATH_RESPONSE in `d` is the oldest response `o` owed on `d`'s path, now
    /// moved to the taken ones. `wf` keeps the taken ones and the owed ones, in order, a subsequence
    /// of the challenges received on the path, so each echoes one challenge, once.
    pub closed spec fn responses_echoed(&self, o: Connection, d: SpecOutDatagram) -> bool {
        &&& one_response_at_most(d)
        &&& forall|i: int, j: int|
            0 <= i < d.packets.len() && 0 <= j < d.packets[i].frames.len() ==> (#[trigger] d.packets[i].frames[j] matches SpecFrame::PathResponse(
                x,
            ) ==> {
                let a = o.paths.path(d.path);
                let b = self.paths.path(d.path);
                &&& a.responses.len() > 0
                &&& x == a.responses[0]@
                &&& b.responses == a.responses.drop_first()
                &&& b.responses_taken == a.responses_taken.push(a.responses[0])
            })
    }

    /// §8.2.1 at the send: every PATH_CHALLENGE in `d` carries the data `self` owed on `d`'s path,
    /// which `next_challenge` drew.
    pub closed spec fn challenges_recorded(&self, d: SpecOutDatagram) -> bool {
        forall|i: int, j: int|
            0 <= i < d.packets.len() && 0 <= j < d.packets[i].frames.len() ==> (#[trigger] d.packets[i].frames[j] matches SpecFrame::PathChallenge(
                y,
            ) ==> {
                let a = self.paths.path(d.path);
                &&& a.owed
                &&& a.challenge is Some
                &&& y == a.challenge.unwrap().0@
            })
    }

    /// Path `q` holds DCID `c`, and any other path holding `c` has the `peer_used` `q` has.
    closed spec fn dcid_held(&self, q: PathId, c: Seq<u8>) -> bool {
        &&& self.paths.path(q).dcid == Some(c)
        &&& forall|r: PathId|
            #[trigger] self.paths.has(r) && r != q && self.paths.path(r).dcid == Some(c)
                ==> self.paths.path(r).peer_used == self.paths.path(q).peer_used
    }

    /// P14 (§9.5), per state, at this send: a 1-RTT packet of `d` goes under the DCID `d`'s path
    /// holds, shared only as the NAT-rebinding MAY allows.
    pub closed spec fn dcid_unshared(&self, d: SpecOutDatagram) -> bool {
        forall|i: int|
            0 <= i < d.packets.len() && #[trigger] d.packets[i].kind is OneRtt ==> self.dcid_held(
                d.path,
                d.packets[i].dcid,
            )
    }

    /// P12-P14 together, `o` the connection before the datagram and `self` after. Opaque so their
    /// quantifiers stay out of `data_datagram`, which only passes this on.
    #[verifier::opaque]
    closed spec fn path_rules(&self, o: Connection, d: SpecOutDatagram) -> bool {
        &&& self.responses_echoed(o, d)
        &&& o.challenges_recorded(d)
        &&& path_expanded(d, o.budget_at(d.path))
        &&& self.dcid_unshared(d)
    }

    /// `self` is `o` after a close of `n` bytes, sent as `o`'s closing state allowed: the first
    /// without a closing budget (the path's holds it), any later one charged to it.
    pub closed spec fn close_sent(&self, o: Connection, n: nat) -> bool {
        &&& n <= u64::MAX
        &&& o.lc.may_send_spec(n as u64)
        &&& self.lc.first_sent_spec()
        &&& !self.lc.owed_spec()
        &&& o.lc.first_sent_spec() ==> self.lc.budget_trace() == o.lc.budget_trace().push(AmpEv::Sent(n))
    }

    pub fn is_live(&self, k: PacketKind) -> (r: bool)
        ensures
            r == self.live(k),
    {
        match k {
            PacketKind::Initial => self.live_i,
            PacketKind::Handshake => self.live_h,
            PacketKind::OneRtt => self.complete,
        }
    }

    /// Adds the next packet of space `k`, if it is live, due and fits what is left of `budget`.
    #[verifier::spinoff_prover]
    fn add_space_packet(
        &mut self,
        k: PacketKind,
        budget: usize,
        can_pad: bool,
        now: u64,
        d: &mut OutDatagram,
        pad: &mut bool,
        Ghost(o): Ghost<Connection>,
    )
        requires
            o.wf(),
            old(self).wf(),
            old(self).phase_spec() is Open,
            old(self).polled@.len() == 0,
            old(self).live(k) ==> old(self).sent(k).next_pn_spec() < PN_MAX,
            old(d)@.packets.len() == 0 ==> now == old(self).now,
            old(self).built_ok(o, old(d)@.packets),
            old(d)@.packets.len() <= 2,
            out_datagram_sized(old(d)@),
            budget <= MAX_DATAGRAM,
            out_datagram_len(old(d)@) <= budget,
            *old(pad) == has_eliciting_initial(old(d)@.packets),
            *old(pad) ==> can_pad,
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            !(k is OneRtt) ==> final(self).polled@.len() == 0,
            !(final(self).phase_spec() is Open) ==> final(self).polled@.len() == 0,
            final(d)@.path == old(d)@.path,
            final(d)@.packets.len() == old(d)@.packets.len() ==> final(self).now == old(self).now,
            final(self).tx_timers(*old(self), now),
            final(self).phase_spec() is Open && old(d)@.packets.len() == 0 && final(d)@.packets.len() == 0
                && budget == old(self).left_for_ack() ==> later(final(self).ack_term(k), now),
            final(self).phase_spec() is Open && final(d)@.packets.len() == old(d)@.packets.len() ==> final(self).tx_kept(*old(self)),
            final(self).phase_spec() is Open ==> final(d)@.packets.len() >= old(d)@.packets.len(),
            final(self).phase_spec() is Open ==> {
                &&& final(self).built_ok(o, final(d)@.packets)
                &&& final(d)@.packets.len() <= old(d)@.packets.len() + 1
                &&& out_datagram_sized(final(d)@)
                &&& out_datagram_len(final(d)@) <= budget
                &&& *final(pad) == has_eliciting_initial(final(d)@.packets)
                &&& *final(pad) ==> can_pad
                &&& polled_placed(final(self).polled@, final(d)@)
                &&& forall|j: PacketKind| j != k ==> #[trigger] final(self).sent(j).next_pn_spec()
                    == old(self).sent(j).next_pn_spec()
            },
    {
        let ghost c = *self;
        let ghost s = d@.packets;
        proof {
            assert(polled_placed(self.polled@, d@));
            self.lemma_tx_same(c, now);
            assert(self.tx_kept(c));
        }
        if !self.is_live(k) {
            return;
        }
        let left = budget - datagram_len(d);
        let room = match self.room_for(k, left) {
            Some(r) => r,
            None => return,
        };
        let (p, eliciting, _) = match self.build_space_packet(k, room, can_pad, now) {
            Some(x) => x,
            None => {
                proof {
                    if self.phase_spec() is Open {
                        c.recv(k).lemma_owed_has_new();
                        self.lemma_ack_term_kept(c, k);
                        if s.len() == 0 {
                            assert(out_datagram_len(d@) == 0);
                            assert(left == budget);
                            if budget == c.left_for_ack() && c.ack_fits(k) && c.recv(k).eliciting_since_ack() > 0 {
                                assert(c.recv(k).full_ack_fits(now, c.local_tp.ack_delay_exponent, room as int));
                                assert(!ack_is_due(c.recv(k), spec_ms_to_us(c.local_tp.max_ack_delay), now));
                            }
                        }
                        self.lemma_built_kept(c, o, s);
                        self.lemma_tx_kept(c);
                        assert(polled_placed(self.polled@, d@));
                    }
                }
                return;
            },
        };
        let ghost v = p@;
        d.packets.push(p);
        if matches!(k, PacketKind::Initial) && eliciting {
            *pad = true;
        }
        proof {
            let s2 = s.push(v);
            assert(d@.packets =~= s2);
            assert(c.packet_ok(v, k, room as nat));
            self.lemma_built_push(c, o, s, v);
            assert(s2.drop_last() =~= s);
            assert(s2.last() == v);
            // `room_for`'s reservation, at the length `collect_frames` chose.
            assert(min_pn_len(c.sent(k).next_pn_spec(), c.sent(k).largest_acked_spec(), v.pn_len as nat));
            assert forall|i: int| 0 <= i < s2.len() implies out_packet_sized(#[trigger] s2[i]) by {
                if i < s.len() {
                    assert(s2[i] == s[i]);
                }
            }
            assert(in_tail(self.polled@, v.frames, 0));
            assert forall|i: int| 0 <= i < self.polled@.len() implies frame_in_datagram(d@, #[trigger] self.polled@[i]) by {
                assert(frame_from(v.frames, self.polled@[i], 0));
                let n = choose|n: int| 0 <= n < v.frames.len() && #[trigger] v.frames[n] == self.polled@[i];
                assert(d@.packets[s.len() as int] == v);
                assert(d@.packets[s.len() as int].frames[n] == self.polled@[i]);
            }
            if eliciting && k is Initial {
                let m = choose|m: int| 0 <= m < v.frames.len() && ack_eliciting(spec_frame_type(#[trigger] v.frames[m]));
                assert(s2[s.len() as int].frames[m] == v.frames[m]);
            }
            assert(has_eliciting_initial(s2) == *pad) by {
                if has_eliciting_initial(s2) {
                    let (a, b) = choose|a: int, b: int|
                        0 <= a < s2.len() && s2[a].kind is Initial && 0 <= b < s2[a].frames.len() && ack_eliciting(
                            spec_frame_type(#[trigger] s2[a].frames[b]),
                        );
                    if a == s.len() {
                        assert(s2[a].frames[b] == v.frames[b]);
                    } else {
                        assert(s2[a] == s[a]);
                    }
                }
                if has_eliciting_initial(s) {
                    let (a, b) = choose|a: int, b: int|
                        0 <= a < s.len() && s[a].kind is Initial && 0 <= b < s[a].frames.len() && ack_eliciting(
                            spec_frame_type(#[trigger] s[a].frames[b]),
                        );
                    assert(s2[a] == s[a]);
                }
            }
        }
    }

    /// Pads the packets built so far to 1200 bytes.
    #[verifier::spinoff_prover]
    fn pad_built(&self, d: &mut OutDatagram, Ghost(o): Ghost<Connection>)
        requires
            self.built_ok(o, old(d)@.packets),
            1 <= old(d)@.packets.len() <= 3,
            out_datagram_sized(old(d)@),
            out_datagram_len(old(d)@) <= MIN_INITIAL_DATAGRAM,
            polled_placed(self.polled@, old(d)@),
        ensures
            final(d)@.path == old(d)@.path,
            final(d)@.packets.len() == old(d)@.packets.len(),
            self.built_ok(o, final(d)@.packets),
            out_datagram_sized(final(d)@),
            out_datagram_len(final(d)@) == MIN_INITIAL_DATAGRAM,
            polled_placed(self.polled@, final(d)@),
            has_eliciting_initial(final(d)@.packets) == has_eliciting_initial(old(d)@.packets),
    {
        let ghost s = d@.packets;
        let ghost placed = self.polled@;
        pad_datagram(d, MIN_INITIAL_DATAGRAM);
        proof {
            let s2 = d@.packets;
            let i = choose|i: int|
                #![trigger s2[i]]
                0 <= i < s.len() && s2 == s.update(i, padded(s[i], (s2[i].padding - s[i].padding) as nat))
                    && s2[i].padding >= s[i].padding;
            self.lemma_built_padded(o, s, s2, i, (s2[i].padding - s[i].padding) as nat);
            assert forall|m: int| 0 <= m < placed.len() implies frame_in_datagram(d@, #[trigger] placed[m]) by {
                let (x, y) = choose|x: int, y: int|
                    0 <= x < s.len() && 0 <= y < s[x].frames.len() && #[trigger] s[x].frames[y] == placed[m];
                assert(s2[x].frames[y] == s[x].frames[y]);
            }
        }
    }

    /// A packet of each space with something due, into the empty `d`. The split keeps
    /// `data_datagram` within rlimit 3.
    #[verifier::spinoff_prover]
    fn add_spaces(
        &mut self,
        budget: usize,
        can_pad: bool,
        now: u64,
        d: &mut OutDatagram,
        pad: &mut bool,
        Ghost(o): Ghost<Connection>,
    )
        requires
            now == old(self).now,
            o.wf(),
            old(self).wf(),
            old(self).phase_spec() is Open,
            old(self).polled@.len() == 0,
            forall|k: PacketKind| #[trigger] old(self).live(k) ==> old(self).sent(k).next_pn_spec() < PN_MAX,
            old(self).built_ok(o, old(d)@.packets),
            old(d)@.packets.len() == 0,
            out_datagram_sized(old(d)@),
            budget <= MAX_DATAGRAM,
            budget == old(self).left_for_ack(),
            !*old(pad),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            !(final(self).phase_spec() is Open) ==> final(self).polled@.len() == 0,
            final(d)@.path == old(d)@.path,
            final(self).tx_timers(*old(self), now),
            final(self).phase_spec() is Open ==> {
                &&& final(self).built_ok(o, final(d)@.packets)
                &&& final(d)@.packets.len() <= 3
                &&& out_datagram_sized(final(d)@)
                &&& out_datagram_len(final(d)@) <= budget
                &&& *final(pad) == has_eliciting_initial(final(d)@.packets)
                &&& *final(pad) ==> can_pad
                &&& polled_placed(final(self).polled@, final(d)@)
                &&& final(d)@.packets.len() == 0 ==> final(self).acks_later(now)
            },
    {
        let ghost s00 = *self;
        proof {
            self.lemma_tx_same(s00, now);
            assert(has_eliciting_initial(d@.packets) == *pad);
            assert(out_datagram_len(d@) == 0);
            assert(self.live(PacketKind::Initial) ==> self.sent(PacketKind::Initial).next_pn_spec() < PN_MAX);
            assert(self.live(PacketKind::Handshake) ==> self.sent(PacketKind::Handshake).next_pn_spec() < PN_MAX);
            assert(self.live(PacketKind::OneRtt) ==> self.sent(PacketKind::OneRtt).next_pn_spec() < PN_MAX);
        }
        // A packet number that cannot be encoded closes silently (`collect_frames`). An earlier space's
        // packet is then recorded and unsent, harmless once Closed; OneRtt runs last, so no polled
        // frame is at risk.
        self.add_space_packet(PacketKind::Initial, budget, can_pad, now, d, pad, Ghost(o));
        if !matches!(self.lc.phase(), Phase::Open) {
            return;
        }
        let ghost s01 = *self;
        let ghost l0 = d@.packets.len();
        self.add_space_packet(PacketKind::Handshake, budget, can_pad, now, d, pad, Ghost(o));
        if !matches!(self.lc.phase(), Phase::Open) {
            proof {
                self.lemma_tx_trans(s01, s00, now);
            }
            return;
        }
        proof {
            self.lemma_tx_trans(s01, s00, now);
        }
        let ghost s02 = *self;
        let ghost l1 = d@.packets.len();
        self.add_space_packet(PacketKind::OneRtt, budget, can_pad, now, d, pad, Ghost(o));
        if !matches!(self.lc.phase(), Phase::Open) {
            proof {
                self.lemma_tx_trans(s02, s00, now);
            }
            return;
        }
        proof {
            self.lemma_tx_trans(s02, s00, now);
        }
        proof {
            if d@.packets.len() == 0 {
                assert(l0 == 0 && l1 == 0);
                self.lemma_no_packet_acks(s01, s02, now);
            }
        }
    }

    /// The ordinary datagram of the Open state: a packet of each space with something due.
    #[verifier::spinoff_prover]
    fn data_datagram(&mut self, now: u64, Ghost(o): Ghost<Connection>) -> (r: Option<OutDatagram>)
        requires
            now == old(self).now,
            o.wf(),
            old(self).wf(),
            old(self).phase_spec() is Open,
            old(self).polled@.len() == 0,
            old(self).tx_kept(o),
            forall|k: PacketKind| #[trigger] old(self).live(k) ==> old(self).sent(k).next_pn_spec() < PN_MAX,
        ensures
            final(self).wf(),
            final(self).out_log() == match r {
                Some(d) => old(self).out_log().push(d@),
                None => old(self).out_log(),
            },
            final(self).polled().len() > 0 ==> r is Some,
            r matches Some(d) ==> {
                &&& transmit_ok(o, *final(self), d@)
                &&& polled_placed(final(self).polled(), d@)
                &&& initial_padded(d@)
                &&& same_dcid(d@)
                &&& !o.mtu_failed_at(d@.path)
                &&& final(self).path_rules(o, d@)
            },
            final(self).tx_timers(*old(self), now),
            r is None ==> final(self).acks_later(now),
    {
        let ghost s00 = *self;
        proof {
            self.lemma_tx_same(s00, now);
        }
        // ponytail: one datagram per call (the shell loops), one CRYPTO frame per space per packet.
        let q = self.paths.active();
        proof {
            self.paths.lemma_wf();
        }
        //= https://www.rfc-editor.org/rfc/rfc9000#section-14.2
        //# If a QUIC endpoint determines that the PMTU between any pair of local
        //# and remote IP addresses cannot support the smallest allowed maximum
        //# datagram size of 1200 bytes, it MUST immediately cease sending QUIC
        //# packets, except for those in PMTU probes or those containing
        //# CONNECTION_CLOSE frames, on the affected path.
        // P17: the send gate, local to this body.
        if self.paths.mtu_failed(q) {
            proof {
                assert forall|k: PacketKind| later(#[trigger] self.ack_term(k), now) by {
                    assert(!self.ack_fits(k));
                }
            }
            return None;
        }
        //= https://www.rfc-editor.org/rfc/rfc9000#section-14.1
        //# The server MUST also limit the number of bytes it sends before
        //# validating the address of the client; see Section 8.
        let b = self.paths.budget(q);
        let budget = if b > MAX_DATAGRAM as u64 {
            MAX_DATAGRAM
        } else {
            b as usize
        };
        let can_pad = budget >= MIN_INITIAL_DATAGRAM;
        let mut d = OutDatagram { path: q, packets: Vec::new() };
        let mut pad = false;
        proof {
            self.lemma_built_empty(o);
            assert(d@.packets =~= Seq::<SpecOutPacket>::empty());
            assert(self.live(PacketKind::Initial) ==> self.sent(PacketKind::Initial).next_pn_spec() < PN_MAX);
            assert(self.live(PacketKind::Handshake) ==> self.sent(PacketKind::Handshake).next_pn_spec() < PN_MAX);
            assert(self.live(PacketKind::OneRtt) ==> self.sent(PacketKind::OneRtt).next_pn_spec() < PN_MAX);
        }
        self.add_spaces(budget, can_pad, now, &mut d, &mut pad, Ghost(o));
        if !matches!(self.lc.phase(), Phase::Open) {
            return None;
        }
        if d.packets.len() == 0 {
            proof {
                if self.polled@.len() > 0 {
                    assert(frame_in_datagram(d@, self.polled@[0]));
                }
            }
            return None;
        }
        //= https://www.rfc-editor.org/rfc/rfc9000#section-14.1
        //# Similarly, a server MUST expand the payload of all UDP
        //# datagrams carrying ack-eliciting Initial packets to at least the
        //# smallest allowed maximum datagram size of 1200 bytes.
        //
        //= https://www.rfc-editor.org/rfc/rfc9000#section-14.1
        //= type=exception
        //= reason=client-only
        //# A client MUST expand the payload of all UDP datagrams carrying
        //# Initial packets to at least the smallest allowed maximum datagram
        //# size of 1200 bytes by adding PADDING frames to the Initial packet or
        //# by coalescing the Initial packet; see Section 12.2.
        if pad {
            self.pad_built(&mut d, Ghost(o));
        }
        proof {
            self.lemma_built_fresh(o, d@.packets);
            assert(self.paths == o.paths);
        }
        let ghost c = *self;
        self.commit_datagram(q, &d);
        proof {
            self.lemma_only_logged(c);
            self.lemma_built_sent(c, o, d@);
            assert(self.tx_timers(c, now));
            self.lemma_tx_trans(c, s00, now);
        }
        Some(d)
    }

    /// The packet number length the next packet of space `k` takes; None if the space cannot number one.
    #[verifier::spinoff_prover]
    fn next_pn_len(&self, k: PacketKind) -> (r: Option<u8>)
        requires
            self.wf(),
        ensures
            r matches Some(n) ==> self.sent(k).next_pn_spec() < PN_MAX && min_pn_len(
                self.sent(k).next_pn_spec(),
                self.sent(k).largest_acked_spec(),
                n as nat,
            ),
    {
        proof {
            self.sent(k).lemma_wf();
        }
        if self.sent_ref(k).next_pn() >= PN_MAX {
            return None;
        }
        pn_encode_len(self.sent_ref(k).next_pn(), self.sent_ref(k).largest_acked())
    }

    /// The close's packet for space `k`; its packet number is not taken yet.
    #[verifier::spinoff_prover]
    fn close_packet(&self, k: PacketKind, pn_len: u8, app: bool, code: u64, reason: &[u8]) -> (p: OutPacket)
        requires
            self.wf(),
            code <= VARINT_MAX,
            reason@.len() <= 64,
            min_pn_len(self.sent(k).next_pn_spec(), self.sent(k).largest_acked_spec(), pn_len as nat),
        ensures
            self.close_built(p@, k),
    {
        let f = close_frame(app, code, reason, k);
        let ghost g = f@;
        proof {
            lemma_close_len(g);
        }
        let mut fs: Vec<Frame> = Vec::new();
        fs.push(f);
        proof {
            assert(frames_view(fs@) =~= seq![g]);
            assert(seq![g] =~= Seq::<SpecFrame>::empty().push(g));
            lemma_frames_bytes_push(Seq::<SpecFrame>::empty(), g);
            assert(frames_view(fs@)[0] == g);
            assert(CLOSE_FRAME_MAX <= MAX_DATAGRAM);
        }
        proof {
            self.lemma_header_bytes(k);
        }
        self.make_packet(k, fs, pn_len, Ghost(1int), Ghost(CLOSE_FRAME_MAX as nat))
    }

    /// `p` is `self`'s close for space `k`: one CONNECTION_CLOSE, under the next packet number.
    closed spec fn close_built(&self, p: SpecOutPacket, k: PacketKind) -> bool {
        &&& p.kind == k
        &&& p.pn == self.sent(k).next_pn_spec()
        &&& p.dcid == self.space_dcid(k)
        &&& out_packet_wf(p, self.sent(k).largest_acked_spec())
        &&& out_packet_len(p) <= CLOSE_PACKET_MAX
        &&& p.frames.len() == 1
        &&& p.frames[0] is ConnectionClose
    }

    /// `spaces` are distinct live spaces, at most 2 (`close_spaces`).
    closed spec fn spaces_ok(&self, spaces: Seq<PacketKind>) -> bool {
        &&& spaces.len() <= 2
        &&& forall|i: int| 0 <= i < spaces.len() ==> self.live(#[trigger] spaces[i])
        &&& forall|i: int, j: int| 0 <= i < j < spaces.len() ==> #[trigger] spaces[i] != #[trigger] spaces[j]
    }

    proof fn lemma_spaces_ok(&self, spaces: Seq<PacketKind>)
        requires
            self.wf(),
            self.complete ==> spaces == seq![PacketKind::OneRtt],
            !self.complete ==> spaces == spec_close_spaces(self.live_i, self.live_h, false),
        ensures
            self.spaces_ok(spaces),
    {
        if !self.complete {
            let i0 = if self.live_i {
                seq![PacketKind::Initial]
            } else {
                Seq::empty()
            };
            let h0 = if self.live_h {
                seq![PacketKind::Handshake]
            } else {
                Seq::empty()
            };
            assert(spaces =~= i0 + h0);
            assert forall|i: int| 0 <= i < spaces.len() implies self.live(#[trigger] spaces[i]) by {
                if self.live_i && i == 0 {
                    assert(spaces[i] == PacketKind::Initial);
                } else {
                    assert(spaces[i] == PacketKind::Handshake);
                }
            }
            assert forall|i: int, j: int| 0 <= i < j < spaces.len() implies #[trigger] spaces[i]
                != #[trigger] spaces[j] by {
                assert(spaces[i] == PacketKind::Initial && spaces[j] == PacketKind::Handshake);
            }
        } else {
            assert(spaces[0] == PacketKind::OneRtt);
        }
    }

    /// The close's packets, one per space; None if a space cannot number one.
    #[verifier::spinoff_prover]
    fn close_packets(&self, spaces: &Vec<PacketKind>, app: bool, code: u64, reason: &[u8]) -> (r: Option<Vec<OutPacket>>)
        requires
            self.wf(),
            code <= VARINT_MAX,
            reason@.len() <= 64,
            spaces@.len() <= 2,
        ensures
            r matches Some(ps) ==> {
                &&& ps@.len() == spaces@.len()
                &&& forall|i: int| 0 <= i < ps@.len() ==> self.close_built(#[trigger] ps@[i]@, spaces@[i])
                &&& forall|i: int| 0 <= i < ps@.len() ==> self.sent(#[trigger] spaces@[i]).next_pn_spec() < PN_MAX
                &&& packets_len(packets_view(ps@)) <= CLOSE_PACKET_MAX * ps@.len()
            },
    {
        let mut ps: Vec<OutPacket> = Vec::new();
        let mut j: usize = 0;
        proof {
            assert(packets_view(ps@) =~= Seq::<SpecOutPacket>::empty());
        }
        while j < spaces.len()
            invariant
                self.wf(),
                code <= VARINT_MAX,
                reason@.len() <= 64,
                spaces@.len() <= 2,
                j <= spaces@.len(),
                ps@.len() == j,
                forall|i: int| 0 <= i < j ==> self.close_built(#[trigger] ps@[i]@, spaces@[i]),
                forall|i: int| 0 <= i < j ==> self.sent(#[trigger] spaces@[i]).next_pn_spec() < PN_MAX,
                packets_len(packets_view(ps@)) <= CLOSE_PACKET_MAX * j,
            decreases spaces@.len() - j,
        {
            let k = spaces[j];
            let n = match self.next_pn_len(k) {
                Some(n) => n,
                None => return None,
            };
            let p = self.close_packet(k, n, app, code, reason);
            let ghost v = p@;
            let ghost s = packets_view(ps@);
            ps.push(p);
            proof {
                let s2 = packets_view(ps@);
                assert(s2 =~= s.push(v));
                assert(s2.drop_last() =~= s);
                assert(s2.last() == v);
            }
            j += 1;
        }
        Some(ps)
    }

    /// The numbers of `s`'s packets, built on `o` for the distinct spaces `spaces`, are taken.
    #[verifier::spinoff_prover]
    fn commit_close_pns(&mut self, spaces: &Vec<PacketKind>, Ghost(s): Ghost<Seq<SpecOutPacket>>, Ghost(o): Ghost<Connection>)
        requires
            o.wf(),
            old(self).wf(),
            old(self).tx_kept(o),
            old(self).spaces_ok(spaces@),
            s.len() == spaces@.len(),
            forall|i: int| 0 <= i < s.len() ==> old(self).close_built(#[trigger] s[i], spaces@[i]),
            forall|i: int| 0 <= i < s.len() ==> old(self).sent(#[trigger] spaces@[i]).next_pn_spec() < PN_MAX,
        ensures
            final(self).wf(),
            final(self).built_ok(o, s),
            final(self).polled == old(self).polled,
            final(self).tx_fixed(*old(self)),
    {
        let ghost c0 = *self;
        let mut j: usize = 0;
        proof {
            self.lemma_built_empty(o);
            assert(s.take(0) =~= Seq::<SpecOutPacket>::empty());
        }
        while j < spaces.len()
            invariant
                c0 == *old(self),
                o.wf(),
                c0.tx_kept(o),
                c0.spaces_ok(spaces@),
                s.len() == spaces@.len(),
                forall|i: int| 0 <= i < s.len() ==> c0.close_built(#[trigger] s[i], spaces@[i]),
                forall|i: int| 0 <= i < s.len() ==> c0.sent(#[trigger] spaces@[i]).next_pn_spec() < PN_MAX,
                self.wf(),
                j <= spaces@.len(),
                self.built_ok(o, s.take(j as int)),
                self.polled == c0.polled,
                self.tx_fixed(c0),
                forall|i: int| j <= i < s.len() ==> self.sent(#[trigger] spaces@[i]).next_pn_spec() == c0.sent(spaces@[i]).next_pn_spec(),
            decreases spaces@.len() - j,
        {
            let k = spaces[j];
            let ghost c = *self;
            let ghost v = s[j as int];
            proof {
                assert(c0.close_built(s[j as int], spaces@[j as int]));
                assert(c0.sent(spaces@[j as int]).next_pn_spec() < PN_MAX);
                assert(self.sent(k).next_pn_spec() == c0.sent(k).next_pn_spec());
            }
            self.commit_pn(k);
            proof {
                self.lemma_sent_kept(c, k);
                self.lemma_seen_kept(c);
                assert(c0.live(k));
                assert(c.live(k));
                c0.lemma_tx_kept(o);
                assert(c.sent(k).largest_acked_spec() == o.sent(k).largest_acked_spec());
                assert(c.space_dcid(k) == c0.space_dcid(k));
                assert forall|i: int| 0 <= i < v.frames.len() implies (#[trigger] v.frames[i] matches SpecFrame::Ack(a)
                    ==> i == 0 && ack_full(a, c.recv(k))) by {
                    assert(i == 0);
                }
                assert forall|i: int| 0 <= i < v.frames.len() implies !(#[trigger] v.frames[i] is PathChallenge) && !(
                v.frames[i] is PathResponse) by {
                    assert(i == 0);
                }
                self.lemma_built_push(c, o, s.take(j as int), v);
                assert(s.take(j as int + 1) =~= s.take(j as int).push(v));
                assert forall|i: int| j + 1 <= i < s.len() implies self.sent(#[trigger] spaces@[i]).next_pn_spec()
                    == c0.sent(spaces@[i]).next_pn_spec() by {
                    assert(spaces@[j as int] != spaces@[i]);
                }
            }
            j += 1;
        }
        proof {
            assert(s.take(s.len() as int) =~= s);
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-10.2.1
    //# An endpoint in the closing
    //# state sends a packet containing a CONNECTION_CLOSE frame in response
    //# to any incoming packet that it attributes to the connection.
    /// The Closing state's datagram, if a close is owed and within both budgets: the path's (§8.1) and
    /// the closing state's (`Lifecycle`). A packet number is taken only when the datagram goes.
    #[verifier::spinoff_prover]
    fn build_close(&mut self, Ghost(o): Ghost<Connection>) -> (r: Option<OutDatagram>)
        requires
            o.wf(),
            old(self).wf(),
            old(self).phase_spec() is Closing,
            old(self).polled@.len() == 0,
            old(self).tx_kept(o),
        ensures
            final(self).wf(),
            final(self).polled@.len() == 0,
            final(self).out_log() == match r {
                Some(d) => old(self).out_log().push(d@),
                None => old(self).out_log(),
            },
            r matches Some(d) ==> {
                &&& transmit_ok(o, *final(self), d@)
                &&& out_datagram_len(d@) <= MAX_DATAGRAM
                &&& only_close(d@)
                &&& same_dcid(d@)
                &&& final(self).close_sent(o, out_datagram_len(d@))
                &&& final(self).path_rules(o, d@)
            },
            final(self).lc.phase_spec() is Closed || (final(self).lc.phase_spec() is Closing
                && final(self).lc.deadline_spec() == old(self).lc.deadline_spec()),
            final(self).expiries_kept(*old(self)),
    {
        proof {
            self.paths.lemma_wf();
        }
        let q = self.paths.active();
        let (app, code, reason) = match self.lc.close_info() {
            Some((a, c, r)) => (*a, *c, slice_to_vec(r.as_slice())),
            None => return None,
        };
        let spaces = close_spaces(self.complete, self.live_i, self.live_h, self.complete);
        proof {
            self.lemma_spaces_ok(spaces@);
        }
        let ps = match self.close_packets(&spaces, app, code, reason.as_slice()) {
            Some(ps) => ps,
            None => {
                // A close needs a packet number: the space is out of them (§12.3), or the next one
                // can't be encoded against `largest_acked`.
                self.lc.close_silently();
                return None;
            },
        };
        if ps.len() == 0 {
            return None;
        }
        let d = OutDatagram { path: q, packets: ps };
        let ghost s = d@.packets;
        proof {
            assert forall|i: int| 0 <= i < s.len() implies out_packet_sized(#[trigger] s[i]) by {
                assert(s[i] == d.packets@[i]@);
                assert(self.close_built(d.packets@[i]@, spaces@[i]));
            }
            assert forall|i: int| 0 <= i < s.len() implies self.close_built(#[trigger] s[i], spaces@[i]) by {
                assert(s[i] == d.packets@[i]@);
            }
            assert(out_datagram_len(d@) <= CLOSE_PACKET_MAX * 2) by {
                assert(CLOSE_PACKET_MAX * s.len() <= CLOSE_PACKET_MAX * 2) by (nonlinear_arith)
                    requires
                        s.len() <= 2,
                ;
            }
        }
        let n = datagram_len(&d) as u64;
        //= https://www.rfc-editor.org/rfc/rfc9000#section-10.2.1
        //# An endpoint in the closing state MUST either discard
        //# packets received from an unvalidated address or limit the cumulative
        //# size of packets it sends to an unvalidated address to three times the
        //# size of packets it receives from that address.
        //
        //= https://www.rfc-editor.org/rfc/rfc9000#section-10.2.1
        //# To avoid being used for an amplification attack,
        //# such endpoints MUST limit the cumulative size of packets it sends to
        //# three times the cumulative size of the packets that are received and
        //# attributed to the connection.
        if n > self.paths.budget(q) || !self.lc.may_send_close(n) {
            return None;
        }
        let ghost c0 = *self;
        self.commit_close_pns(&spaces, Ghost(s), Ghost(o));
        proof {
            self.lemma_built_fresh(o, s);
            assert(self.paths == c0.paths);
        }
        let ghost c = *self;
        self.commit_datagram(q, &d);
        self.lc.on_close_sent(n);
        proof {
            self.lemma_only_logged(c);
            self.lemma_built_sent(c, o, d@);
            assert forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s[i].frames.len() implies #[trigger] s[i].frames[j]
                is ConnectionClose by {
                assert(c0.close_built(s[i], spaces@[i]));
                assert(j == 0);
            }
        }
        Some(d)
    }

    /// The length of the 1-RTT packet of PATH frames owed on `q`, with packet number length `n`.
    closed spec fn path_packet_len(&self, q: PathId, n: nat) -> nat {
        let p = self.paths.path(q);
        (1 + p.dcid->0.len() + n + 9 * ((if p.responses.len() > 0 {
            1int
        } else {
            0
        }) + (if p.owed {
            1int
        } else {
            0
        })) + AEAD_TAG_LEN) as nat
    }

    /// The first path in table order with a PATH frame owed, a DCID to send it under, and room for it:
    /// the path, whether to expand to 1200, and the packet number length, which is None if the next
    /// packet number cannot be encoded. Skipped paths keep what they are owed.
    #[verifier::spinoff_prover]
    fn choose_path(&self) -> (r: Option<(PathId, bool, Option<u8>)>)
        requires
            self.wf(),
        ensures
            r matches Some((q, padded, Some(n))) ==> {
                &&& self.paths.has(q)
                &&& self.paths.path(q).dcid is Some
                &&& self.paths.path(q).responses.len() > 0 || self.paths.path(q).owed
                &&& self.sent(PacketKind::OneRtt).next_pn_spec() < PN_MAX
                &&& min_pn_len(
                    self.sent(PacketKind::OneRtt).next_pn_spec(),
                    self.sent(PacketKind::OneRtt).largest_acked_spec(),
                    n as nat,
                )
                &&& padded == (self.paths.budget_spec(q) >= 1200)
                &&& !padded ==> self.path_packet_len(q, n as nat) <= self.paths.budget_spec(q)
                &&& self.paths.mtu_failed_spec(q) ==> padded
            },
    {
        let n = self.paths.len();
        let mut i: usize = 0;
        while i < n
            invariant
                self.wf(),
                n == self.paths.ids().len(),
                i <= n,
            decreases n - i,
        {
            let q = self.path_at(i);
            i += 1;
            let resp = self.paths.has_response(q);
            let chal = self.paths.challenge_owed(q);
            // §9.5: no DCID, nothing sent; there is no fallback to another CID.
            let dlen = match self.paths.dcid(q) {
                Some(c) => c.len(),
                None => continue,
            };
            if !resp && !chal {
                continue;
            }
            let pn_len = match self.next_pn_len(PacketKind::OneRtt) {
                Some(l) => l,
                None => return Some((q, false, None)),
            };
            proof {
                self.paths.lemma_wf();
                assert(path_ok(self.paths.path(q)));
            }
            let b = self.paths.budget(q);
            //= https://www.rfc-editor.org/rfc/rfc9000#section-8.2.1
            //# An endpoint MUST expand datagrams that contain a PATH_CHALLENGE frame
            //# to at least the smallest allowed maximum datagram size of 1200 bytes,
            //# unless the anti-amplification limit for the path does not permit
            //# sending a datagram of this size.
            //
            //= https://www.rfc-editor.org/rfc/rfc9000#section-8.2.2
            //# An endpoint MUST expand datagrams that contain a PATH_RESPONSE frame
            //# to at least the smallest allowed maximum datagram size of 1200 bytes.
            //
            //= https://www.rfc-editor.org/rfc/rfc9000#section-8.2.2
            //# However, an endpoint MUST NOT expand the
            //# datagram containing the PATH_RESPONSE if the resulting data exceeds
            //# the anti-amplification limit.
            let padded = b >= MIN_INITIAL_DATAGRAM as u64;
            let frames: usize = (if resp { 1 } else { 0 }) + (if chal { 1 } else { 0 });
            let len = 1 + dlen + pn_len as usize + 9 * frames + AEAD_TAG_LEN;
            // P17: a failed path is Validated, so `padded` holds there short of 2^64 bytes sent. Nothing
            // in `wf` says so, hence the guard.
            if padded || (len as u64 <= b && !self.paths.mtu_failed(q)) {
                return Some((q, padded, Some(pn_len)));
            }
        }
        None
    }

    /// The frames owed on `q`: its oldest response and its owed challenge, taken.
    #[verifier::spinoff_prover]
    fn take_path_frames(&mut self, q: PathId, padded: bool, now: u64) -> (r: Vec<Frame>)
        requires
            old(self).wf(),
            old(self).paths.has(q),
        ensures
            final(self).wf(),
            *final(self) == (Connection { paths: final(self).paths, ..*old(self) }),
            kept(old(self).paths, final(self).paths, q),
            ({
                let a = old(self).paths.path(q);
                let b = final(self).paths.path(q);
                &&& b.dcid == a.dcid
                &&& b.peer_used == a.peer_used
                &&& b.budget == a.budget
                &&& a.responses.len() > 0 ==> b.responses == a.responses.drop_first() && b.responses_taken
                    == a.responses_taken.push(a.responses[0])
                &&& a.owed ==> b.challenge is Some && b.challenge.unwrap().2 == padded
                &&& r@.len() == (if a.responses.len() > 0 { 1int } else { 0 }) + (if a.owed { 1int } else { 0 })
                &&& path_frames_ok(frames_view(r@))
                &&& frames_view(r@) == path_frames_of(a)
            }),
            final(self).tx_timers(*old(self), now),
    {
        let ghost s0 = *self;
        let mut fs: Vec<Frame> = Vec::new();
        proof {
            assert(frames_view(fs@) =~= Seq::<SpecFrame>::empty());
        }
        //= https://www.rfc-editor.org/rfc/rfc9000#section-8.2.2
        //# On receiving a PATH_CHALLENGE frame, an endpoint MUST respond by
        //# echoing the data contained in the PATH_CHALLENGE frame in a
        //# PATH_RESPONSE frame.
        //
        //= https://www.rfc-editor.org/rfc/rfc9000#section-8.2.2
        //# An endpoint MUST NOT send more than one PATH_RESPONSE frame in
        //# response to one PATH_CHALLENGE frame; see Section 13.3.
        if let Some(x) = self.paths.take_response(q) {
            let f = Frame::PathResponse(x);
            let ghost g = f@;
            fs.push(f);
            proof {
                assert(frames_view(fs@) =~= Seq::<SpecFrame>::empty().push(g));
                lemma_path_frame_push(Seq::<SpecFrame>::empty(), g);
            }
        }
        let ghost v1 = frames_view(fs@);
        if let Some(y) = self.paths.take_challenge(q, padded, now) {
            let f = Frame::PathChallenge(y);
            let ghost g = f@;
            fs.push(f);
            proof {
                assert(frames_view(fs@) =~= v1.push(g));
                lemma_path_frame_push(v1, g);
            }
        }
        proof {
            assert(frames_view(fs@) =~= path_frames_of(s0.paths.path(q)));
            self.lemma_path_edit(s0, q);
            self.lemma_dcids_same(s0, q);
            assert(self.tx_timers(s0, now)) by {
                reveal(Connection::tx_timers);
                assert forall|k: PacketKind| #[trigger] self.sent(k).inflight_spec() == s0.sent(k).inflight_spec() by {
                    match k {
                        PacketKind::Initial => {},
                        PacketKind::Handshake => {},
                        PacketKind::OneRtt => {},
                    }
                }
                assert(self.amp_blocked_spec() || !s0.amp_blocked_spec());
                assert forall|r: PathId|
                    #[trigger] self.paths.has(r) && timed(self.paths.path(r)) implies s0.paths.has(r) && (self.paths.path(r).challenge
                        == s0.paths.path(r).challenge && timed(s0.paths.path(r)) || now <= self.paths.path(r).challenge.unwrap().1) by {
                    if r != q {
                        assert(self.paths.path(r) == s0.paths.path(r));
                    }
                }
            }
        }
        fs
    }

    /// The 1-RTT packet of `fs` on `q`, under `q`'s DCID. Its packet number is not taken yet.
    #[verifier::spinoff_prover]
    fn path_packet(&self, q: PathId, fs: Vec<Frame>, pn_len: u8) -> (p: OutPacket)
        requires
            self.wf(),
            self.paths.has(q),
            self.paths.path(q).dcid is Some,
            1 <= fs@.len() <= 2,
            path_frames_ok(frames_view(fs@)),
            min_pn_len(self.sent(PacketKind::OneRtt).next_pn_spec(), self.sent(PacketKind::OneRtt).largest_acked_spec(), pn_len as nat),
        ensures
            p@.kind is OneRtt,
            p@.pn == self.sent(PacketKind::OneRtt).next_pn_spec(),
            Some(p@.dcid) == self.paths.path(q).dcid,
            p@.frames == frames_view(fs@),
            p@.pn_len == pn_len,
            p@.padding == 0,
            out_packet_wf(p@, self.sent(PacketKind::OneRtt).largest_acked_spec()),
            out_packet_len(p@) == 1 + p@.dcid.len() + pn_len + 9 * fs@.len() + AEAD_TAG_LEN,
    {
        proof {
            self.paths.lemma_wf();
            assert(path_ok(self.paths.path(q)));
            self.sent(PacketKind::OneRtt).lemma_wf();
        }
        let dcid = match self.paths.dcid(q) {
            Some(d) => slice_to_vec(d),
            None => {
                proof {
                    assert(false);
                }
                Vec::new()
            },
        };
        let ghost frames = frames_view(fs@);
        let p = OutPacket {
            kind: PacketKind::OneRtt,
            dcid,
            scid: Vec::new(),
            pn: self.sent_1.next_pn(),
            pn_len,
            frames: fs,
            padding: 0,
            spin: self.spin,
        };
        proof {
            assert(p@.frames == frames);
        }
        p
    }

    /// The one packet `p` of `d`, numbered `o`'s next, is fresh once `self` has taken its number.
    proof fn lemma_one_fresh(&self, o: Connection, d: SpecOutDatagram, p: SpecOutPacket)
        requires
            o.wf(),
            d.packets == seq![p],
            p.kind is OneRtt,
            p.pn == o.sent_1.next_pn_spec(),
            self.sent_1.next_pn_spec() == p.pn + 1,
            self.out_log@ == o.out_log@,
        ensures
            forall|k: PacketKind|
                #[trigger] pns_fresh(log_pns(self.out_log@, k), packets_pns(d.packets, k), self.sent(k).next_pn_spec()),
    {
        let s = d.packets;
        assert(o.wf_pn());
        assert forall|k: PacketKind|
            #[trigger] pns_fresh(log_pns(self.out_log@, k), packets_pns(s, k), self.sent(k).next_pn_spec()) by {
            let l = log_pns(self.out_log@, k);
            let b = packets_pns(s, k);
            lemma_one_packet(p, k);
            if k is OneRtt {
                assert(pns_ok(l, o.sent_1.next_pn_spec()));
                assert forall|i: int, j: int| 0 <= i < l.len() && 0 <= j < b.len() implies #[trigger] l[i] < #[trigger] b[j] by {
                    assert(b[j] == p.pn);
                    assert(l[i] < o.sent_1.next_pn_spec());
                }
            }
        }
    }

    /// `transmit_ok` and the shape of a one-packet datagram of PATH frames.
    proof fn lemma_one_sent(&self, o: Connection, d: SpecOutDatagram, p: SpecOutPacket)
        requires
            d.packets == seq![p],
            out_datagram_len(d) <= MAX_DATAGRAM,
            p.kind is OneRtt,
            p.pn == o.sent_1.next_pn_spec(),
            out_packet_wf(p, o.sent_1.largest_acked_spec()),
            forall|j: int|
                0 <= j < p.frames.len() ==> #[trigger] p.frames[j] is PathResponse || p.frames[j] is PathChallenge,
            self.sent_1.next_pn_spec() == p.pn + 1,
            self.sent_1.largest_acked_spec() == o.sent_1.largest_acked_spec(),
        ensures
            transmit_ok(o, *self, d),
            same_dcid(d),
            initial_padded(d),
    {
        let s = d.packets;
        assert(forall|i: int| 0 <= i < s.len() ==> i == 0 && #[trigger] s[i] == p);
        assert forall|k: PacketKind| #[trigger] pns_ok(packets_pns(s, k), self.sent(k).next_pn_spec()) by {
            lemma_one_packet(p, k);
        }
        if has_eliciting_initial(s) {
            let (a, b) = choose|a: int, b: int|
                0 <= a < s.len() && s[a].kind is Initial && 0 <= b < s[a].frames.len() && ack_eliciting(
                    spec_frame_type(#[trigger] s[a].frames[b]),
                );
            assert(s[a] == p);
        }
    }

    /// `send_path_datagram`'s timers: only the idle timer moved since `c2`, to `now` at the latest
    /// (split from `send_path_datagram` for the rlimit).
    #[verifier::spinoff_prover]
    proof fn lemma_idle_timers(&self, c2: Connection, s0: Connection, now: u64)
        requires
            c2.tx_timers(s0, now),
            *self == (Connection { idle: self.idle, ..c2 }),
            self.idle.last == c2.idle.last || self.idle.last == now,
        ensures
            self.tx_timers(s0, now),
    {
        reveal(Connection::tx_timers);
        if !(self.lc.phase_spec() is Closed) {
            assert forall|k: PacketKind|
                #[trigger] self.sent(k).inflight_spec() == s0.sent(k).inflight_spec() || (self.sent(k).inflight_spec().len() > 0
                    && now <= self.sent(k).inflight_spec().last().time) by {
                assert(c2.sent(k).inflight_spec() == s0.sent(k).inflight_spec() || (c2.sent(k).inflight_spec().len() > 0
                    && now <= c2.sent(k).inflight_spec().last().time));
                assert(self.sent(k) == c2.sent(k)) by {
                    match k {
                        PacketKind::Initial => {},
                        PacketKind::Handshake => {},
                        PacketKind::OneRtt => {},
                    }
                }
            }
            assert forall|r: PathId|
                #[trigger] self.paths.has(r) && timed(self.paths.path(r)) implies s0.paths.has(r) && (self.paths.path(r).challenge
                    == s0.paths.path(r).challenge && timed(s0.paths.path(r)) || now <= self.paths.path(r).challenge.unwrap().1) by {
                assert(c2.paths.has(r) && timed(c2.paths.path(r)));
            }
        }
    }

    /// Takes the frames owed on `q`, builds their packet and commits it. `q`'s budget was checked by
    /// `choose_path`, before anything was taken.
    #[verifier::spinoff_prover]
    fn send_path_datagram(&mut self, q: PathId, expand: bool, pn_len: u8, now: u64, Ghost(o): Ghost<Connection>) -> (d: OutDatagram)
        requires
            o.wf(),
            old(self).wf(),
            old(self).polled@.len() == 0,
            old(self).tx_kept(o),
            old(self).paths.has(q),
            old(self).paths.path(q).dcid is Some,
            old(self).paths.path(q).responses.len() > 0 || old(self).paths.path(q).owed,
            old(self).sent(PacketKind::OneRtt).next_pn_spec() < PN_MAX,
            min_pn_len(
                old(self).sent(PacketKind::OneRtt).next_pn_spec(),
                old(self).sent(PacketKind::OneRtt).largest_acked_spec(),
                pn_len as nat,
            ),
            expand == (old(self).paths.budget_spec(q) >= 1200),
            !expand ==> old(self).path_packet_len(q, pn_len as nat) <= old(self).paths.budget_spec(q),
            old(self).paths.mtu_failed_spec(q) ==> expand,
        ensures
            final(self).wf(),
            final(self).polled@.len() == 0,
            final(self).out_log() == old(self).out_log().push(d@),
            d@.path == q,
            transmit_ok(o, *final(self), d@),
            initial_padded(d@),
            same_dcid(d@),
            o.mtu_failed_at(q) ==> mtu_failed_frames(d@) && out_datagram_len(d@) == 1200,
            final(self).path_rules(o, d@),
            only_path_frames(d@),
            final(self).tx_timers(*old(self), now),
            // §8.2.3: only a sent challenge's real size can validate the MTU.
            o.paths.path(q).owed ==> final(self).paths.path(q).challenge is Some
                && final(self).paths.path(q).challenge.unwrap().2 == (out_datagram_len(d@) == 1200),
    {
        let ghost s0 = *self;
        let fs = self.take_path_frames(q, expand, now);
        let ghost sf = frames_view(fs@);
        let ghost s1 = *self;
        let p = self.path_packet(q, fs, pn_len);
        let ghost v = p@;
        let mut ps: Vec<OutPacket> = Vec::new();
        ps.push(p);
        let mut d = OutDatagram { path: q, packets: ps };
        proof {
            assert(d@.packets =~= seq![v]);
            lemma_one_packet(v, v.kind);
        }
        //= https://www.rfc-editor.org/rfc/rfc9000#section-8.2.3
        //# However, the endpoint MUST initiate
        //# another path validation with an expanded datagram to verify that the
        //# path supports the required MTU.
        if expand {
            pad_datagram(&mut d, MIN_INITIAL_DATAGRAM);
        }
        let ghost w = d@.packets[0];
        proof {
            assert(d@.packets =~= seq![w]);
            let la = s1.sent_1.largest_acked_spec();
            if expand {
                let i = choose|i: int|
                    #![trigger d@.packets[i]]
                    0 <= i < seq![v].len() && d@.packets == seq![v].update(
                        i,
                        padded(seq![v][i], (d@.packets[i].padding - seq![v][i].padding) as nat),
                    ) && d@.packets[i].padding >= seq![v][i].padding;
                assert(i == 0);
                assert(seq![v][0] == v);
                assert(out_packet_wf(seq![v][0], la));
                assert(out_packet_wf(d@.packets[0], la));
            }
        }
        self.commit_pn(PacketKind::OneRtt);
        proof {
            self.lemma_one_fresh(s1, d@, w);
            self.lemma_tx_same(s1, now);
            self.lemma_tx_trans(s1, s0, now);
        }
        let ghost c = *self;
        self.commit_datagram(q, &d);
        let ghost c2 = *self;
        // §10.1: these packets are ack-eliciting, though not recorded (E2).
        self.idle.on_eliciting_sent(now);
        proof {
            assert(c2.tx_timers(c, now));
            c2.lemma_tx_trans(c, s0, now);
            self.lemma_idle_timers(c2, s0, now);
            reveal(Connection::path_rules);
            self.lemma_one_sent(o, d@, w);
            lemma_path_frames_of(o.paths.path(q));
            assert(sf == path_frames_of(o.paths.path(q)));
            s1.paths.lemma_wf();
            assert(self.paths.has(q)) by {
                assert(s1.paths.has(q));
            }
            self.lemma_held(q, w.dcid);
            assert forall|i: int, j: int| 0 <= i < d@.packets.len() && 0 <= j < d@.packets[i].frames.len() implies #[trigger] d@.packets[i].frames[j]
                is PathResponse || d@.packets[i].frames[j] is PathChallenge by {
                assert(d@.packets[i] == w);
                assert(w.frames[j] == sf[j]);
            }
            assert(o.challenges_recorded(d@)) by {
                s0.paths.lemma_wf();
                assert(path_ok(o.paths.path(q))) by {
                    assert(o.paths.has(q));
                }
                assert forall|i: int, j: int| 0 <= i < d@.packets.len() && 0 <= j < d@.packets[i].frames.len() implies (#[trigger] d@.packets[i].frames[j] matches SpecFrame::PathChallenge(
                    y,
                ) ==> {
                    let a = o.paths.path(d@.path);
                    &&& a.owed
                    &&& a.challenge is Some
                    &&& y == a.challenge.unwrap().0@
                }) by {
                    assert(d@.packets[i] == w);
                    assert(w.frames[j] == sf[j]);
                }
            }
            assert(self.responses_echoed(o, d@)) by {
                assert forall|i1: int, j1: int, i2: int, j2: int|
                    0 <= i1 < d@.packets.len() && 0 <= j1 < d@.packets[i1].frames.len() && 0 <= i2 < d@.packets.len() && 0 <= j2
                        < d@.packets[i2].frames.len() && #[trigger] d@.packets[i1].frames[j1] is PathResponse
                        && #[trigger] d@.packets[i2].frames[j2] is PathResponse implies i1 == i2 && j1 == j2 by {
                    assert(d@.packets[i1] == w && d@.packets[i2] == w);
                    assert(w.frames[j1] == sf[j1] && w.frames[j2] == sf[j2]);
                }
                assert forall|i: int, j: int| 0 <= i < d@.packets.len() && 0 <= j < d@.packets[i].frames.len() implies (#[trigger] d@.packets[i].frames[j] matches SpecFrame::PathResponse(
                    x,
                ) ==> {
                    let a = o.paths.path(d@.path);
                    let b = self.paths.path(d@.path);
                    &&& a.responses.len() > 0
                    &&& x == a.responses[0]@
                    &&& b.responses == a.responses.drop_first()
                    &&& b.responses_taken == a.responses_taken.push(a.responses[0])
                }) by {
                    assert(d@.packets[i] == w);
                    assert(w.frames[j] == sf[j]);
                }
            }
            assert(self.dcid_unshared(d@)) by {
                assert forall|i: int| 0 <= i < d@.packets.len() && #[trigger] d@.packets[i].kind is OneRtt implies self.dcid_held(
                    d@.path,
                    d@.packets[i].dcid,
                ) by {
                    assert(d@.packets[i] == w);
                }
            }
        }
        d
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-8.2.2
    //# An endpoint MUST NOT delay transmission of a
    //# packet containing a PATH_RESPONSE frame unless constrained by
    //# congestion control.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-8.2.2
    //# A PATH_RESPONSE frame MUST be sent on the network path where the
    //# PATH_CHALLENGE frame was received.
    //= https://www.rfc-editor.org/rfc/rfc9000#section-9.4
    //= type=exception
    //= reason=One shared placeholder Recovery: old-path records acked after on_path_validated still raise cwnd. Path packets are unrecorded (E2), which covers only these. TRUSTED.md; Phase 6 closes it.
    //# Packets sent on the old path MUST NOT contribute to
    //# congestion control or RTT estimation for the new path.
    // ponytail: one shared Recovery, so old-path records acked after on_path_validated still raise cwnd; Phase 6 keeps per-path state.
    // ponytail: one datagram per owed response, outside congestion control (E2): on a validated path 62 bytes in draws 4800 out (77:1), attacker-paced; every owed response in one 1200-byte packet gives 19:1. Phase 6 decides, with E2.
    /// PATH_RESPONSE and PATH_CHALLENGE datagrams, ahead of data: one 1-RTT packet, not recorded (E2).
    /// A None with the connection still Open has left what `tx_kept` reads alone.
    #[verifier::spinoff_prover]
    fn build_path_datagram(&mut self, now: u64, Ghost(o): Ghost<Connection>) -> (r: Option<OutDatagram>)
        requires
            o.wf(),
            old(self).wf(),
            old(self).phase_spec() is Open,
            old(self).polled@.len() == 0,
            old(self).tx_kept(o),
        ensures
            r is None ==> final(self).now == old(self).now,
            final(self).wf(),
            final(self).polled@.len() == 0,
            final(self).out_log() == match r {
                Some(d) => old(self).out_log().push(d@),
                None => old(self).out_log(),
            },
            r is None && final(self).phase_spec() is Open ==> final(self).tx_kept(o),
            r matches Some(d) ==> {
                &&& transmit_ok(o, *final(self), d@)
                &&& initial_padded(d@)
                &&& same_dcid(d@)
                &&& o.mtu_failed_at(d@.path) ==> mtu_failed_frames(d@) && out_datagram_len(d@) == 1200
                &&& final(self).path_rules(o, d@)
                &&& only_path_frames(d@)
                &&& o.paths.path(d@.path).owed ==> final(self).paths.path(d@.path).challenge is Some
                    && final(self).paths.path(d@.path).challenge.unwrap().2 == (out_datagram_len(d@) == 1200)
            },
            final(self).tx_timers(*old(self), now),
    {
        let ghost s0 = *self;
        proof {
            self.lemma_tx_same(s0, now);
        }
        // PATH frames arrive only in 1-RTT.
        if !self.complete {
            return None;
        }
        match self.choose_path() {
            None => None,
            Some((_, _, None)) => {
                self.lc.close_silently();
                self.streams = None;
                proof {
                    self.lemma_tx_closed(s0, now);
                }
                None
            },
            Some((q, padded, Some(pn_len))) => Some(self.send_path_datagram(q, padded, pn_len, now, Ghost(o))),
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-8
    //# Therefore, after receiving packets from an address that is not yet
    //# validated, an endpoint MUST limit the amount of data it sends to the
    //# unvalidated address to three times the amount of data received from
    //# that address.
    /// One datagram, or None. P1 (§8, §8.1, §14.1): `commit_datagram` is the only `on_sent`, and it
    /// counts the padded datagram, so `wf_amp` bounds 3e's written bytes (`out_packet_len`), per path.
    #[verifier::spinoff_prover]
    pub fn poll_transmit(&mut self, now: u64) -> (r: Option<OutDatagram>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).out_log() == match r {
                Some(d) => old(self).out_log().push(d@),
                None => old(self).out_log(),
            },
            r matches Some(d) ==> transmit_ok(*old(self), *final(self), d@),
            final(self).polled().len() > 0 ==> r is Some,
            r matches Some(d) ==> polled_placed(final(self).polled(), d@),
            final(self).sent(PacketKind::Initial).inflight_spec().len() + final(self).sent(
                PacketKind::Handshake,
            ).inflight_spec().len() + final(self).sent(PacketKind::OneRtt).inflight_spec().len()
                <= MAX_INFLIGHT,
            // P2.
            r matches Some(d) ==> initial_padded(d@),
            // P3.
            old(self).phase_spec() is Draining || old(self).phase_spec() is Closed ==> r is None,
            r matches Some(d) ==> (old(self).phase_spec() is Closing ==> only_close(d@) && final(self).close_sent(
                *old(self),
                out_datagram_len(d@),
            )),
            // P6.
            r matches Some(d) ==> same_dcid(d@),
            // P17.
            r matches Some(d) ==> (old(self).mtu_failed_at(d@.path) ==> mtu_failed_frames(d@)),
            // P12.
            r matches Some(d) ==> final(self).responses_echoed(*old(self), d@),
            // §8.2.1: challenge data is what was drawn for the path.
            r matches Some(d) ==> old(self).challenges_recorded(d@),
            // P13.
            r matches Some(d) ==> path_expanded(d@, old(self).budget_at(d@.path)),
            // P14.
            r matches Some(d) ==> final(self).dcid_unshared(d@),
            // §12.3.
            old(self).phase_spec() is Open ==> forall|k: PacketKind|
                #[trigger] old(self).live(k) && old(self).sent(k).next_pn_spec() == PN_MAX ==> r is None
                    && final(self).phase_spec() is Closed,
            // A send moves no timer to `now` or before.
            now < u64::MAX && old(self).timers_later(now) ==> final(self).timers_later(now),
            // §13.2.1: nothing more to send, so no ACK that could go is due.
            r is None ==> final(self).acks_later(now),
            // The nonce's domain (3e `protect_ok`): every packet number is below 2^62 - 1.
            r matches Some(d) ==> forall|i: int|
                0 <= i < d@.packets.len() ==> (#[trigger] d@.packets[i]).pn < PN_MAX,
            final(self).crypto_kept(*old(self)),
            drained_kept(*final(self), *old(self)),
    {
        let ghost o = *old(self);
        let ghost n0 = now;
        proof {
            reveal(Connection::path_rules);
        }
        if now > self.now {
            self.now = now;
        }
        self.polled = Ghost(Seq::empty());
        match self.lc.phase() {
            //= https://www.rfc-editor.org/rfc/rfc9000#section-10.2.2
            //# While otherwise identical to the closing state, an
            //# endpoint in the draining state MUST NOT send any packets.
            Phase::Draining | Phase::Closed => return None,
            Phase::Closing => {
                let r = self.build_close(Ghost(o));
                proof {
                    if r is Some {
                        lemma_only_close(r->0@);
                        lemma_transmit_pn_max(o, *self, r->0@);
                    }
                    if n0 < u64::MAX && o.timers_later(n0) && !(self.lc.phase_spec() is Closed) {
                        assert(self.pto_spec() == o.pto_spec());
                        assert forall|q: PathId| #[trigger] self.paths.has(q) && timed(self.paths.path(q)) implies n0 < expiry(self.paths.path(q), self.pto_spec()) by {
                            assert(self.paths.path(q).challenge == o.paths.path(q).challenge);
                            assert(o.paths.has(q) && timed(o.paths.path(q)));
                        }
                    }
                }
                return r;
            },
            Phase::Open => {},
        }
        //= https://www.rfc-editor.org/rfc/rfc9000#section-12.3
        //# If the packet number for sending
        //# reaches 2^62-1, the sender MUST close the connection without sending
        //# a CONNECTION_CLOSE frame or any further packets; an endpoint MAY send
        //# a Stateless Reset (Section 10.3) in response to further packets that
        //# it receives.
        // Checked for every live space before anything is polled.
        if (self.live_i && self.sent_i.next_pn() >= PN_MAX) || (self.live_h && self.sent_h.next_pn() >= PN_MAX) || (
        self.complete && self.sent_1.next_pn() >= PN_MAX) {
            self.lc.close_silently();
            self.streams = None;
            return None;
        }
        proof {
            assert forall|k: PacketKind| #[trigger] o.live(k) implies o.sent(k).next_pn_spec() < PN_MAX by {
                match k {
                    PacketKind::Initial => {},
                    PacketKind::Handshake => {},
                    PacketKind::OneRtt => {},
                }
            }
        }
        proof {
            assert(self.tx_kept(o));
        }
        self.poll_open(Ghost(n0), Ghost(o))
    }

    /// `poll_transmit` once Open with every live space's packet number below `PN_MAX`: PATH frames
    /// first, then data. `o` is the connection `poll_transmit` was called on.
    #[verifier::spinoff_prover]
    fn poll_open(&mut self, Ghost(n0): Ghost<u64>, Ghost(o): Ghost<Connection>) -> (r: Option<OutDatagram>)
        requires
            o.wf(),
            old(self).wf(),
            old(self).phase_spec() is Open,
            old(self).polled@.len() == 0,
            old(self).tx_kept(o),
            o.now <= old(self).now,
            n0 <= old(self).now,
            forall|k: PacketKind| #[trigger] o.live(k) ==> o.sent(k).next_pn_spec() < PN_MAX,
        ensures
            final(self).wf(),
            final(self).out_log() == match r {
                Some(d) => o.out_log().push(d@),
                None => o.out_log(),
            },
            r matches Some(d) ==> transmit_ok(o, *final(self), d@),
            final(self).polled().len() > 0 ==> r is Some,
            r matches Some(d) ==> polled_placed(final(self).polled(), d@),
            r matches Some(d) ==> initial_padded(d@),
            r matches Some(d) ==> same_dcid(d@),
            r matches Some(d) ==> (o.mtu_failed_at(d@.path) ==> mtu_failed_frames(d@)),
            r matches Some(d) ==> final(self).responses_echoed(o, d@),
            r matches Some(d) ==> o.challenges_recorded(d@),
            r matches Some(d) ==> path_expanded(d@, o.budget_at(d@.path)),
            r matches Some(d) ==> final(self).dcid_unshared(d@),
            n0 < u64::MAX && o.timers_later(n0) ==> final(self).timers_later(n0),
            r is None ==> final(self).acks_later(n0),
            r matches Some(d) ==> forall|i: int|
                0 <= i < d@.packets.len() ==> (#[trigger] d@.packets[i]).pn < PN_MAX,
            final(self).crypto_kept(o),
            drained_kept(*final(self), o),
    {
        proof {
            reveal(Connection::path_rules);
        }
        let now = self.now;
        let ghost s0 = *self;
        proof {
            s0.lemma_tx_kept_timers(o, now);
        }
        if let Some(d) = self.build_path_datagram(now, Ghost(o)) {
            proof {
                self.lemma_tx_trans(s0, o, now);
                self.lemma_tx_crypto(o, now);
                if n0 < u64::MAX && o.timers_later(n0) {
                    self.lemma_tx_later(o, now, n0);
                }
                lemma_transmit_pn_max(o, *self, d@);
            }
            return Some(d);
        }
        if !matches!(self.lc.phase(), Phase::Open) {
            proof {
                self.lemma_tx_phase(s0, now);
                self.lemma_tx_trans(s0, o, now);
                self.lemma_tx_crypto(o, now);
            }
            return None;
        }
        let ghost s1 = *self;
        proof {
            self.lemma_tx_kept_timers(o, now);
            self.lemma_tx_kept(o);
            assert forall|k: PacketKind| #[trigger] self.live(k) implies self.sent(k).next_pn_spec() < PN_MAX by {
                assert(o.live(k));
                assert(self.sent(k) == o.sent(k));
            }
        }
        let r = self.data_datagram(now, Ghost(o));
        proof {
            self.lemma_tx_trans(s1, o, now);
            self.lemma_tx_crypto(o, now);
            if n0 < u64::MAX && o.timers_later(n0) {
                self.lemma_tx_later(o, now, n0);
            }
            if r is None && self.lc.phase_spec() is Open {
                assert forall|k: PacketKind| later(#[trigger] self.ack_term(k), n0) by {
                    assert(later(self.ack_term(k), now));
                }
            }
            if r is Some {
                lemma_transmit_pn_max(o, *self, r->0@);
            }
        }
        r
    }

    /// Test support (3d2 preflight M9): `sent(k)` jumps to packet number `next`, as if the numbers
    /// below it were used. `wf_pn` holds because `next` only grows.
    #[doc(hidden)]
    pub fn skip_pns_for_test(&mut self, k: PacketKind, next: u64)
        requires
            old(self).wf(),
            old(self).sent(k).next_pn_spec() <= next <= PN_MAX,
            old(self).sent(k).inflight_spec().len() == 0,
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            final(self).sent(k).next_pn_spec() == next,
    {
        match k {
            PacketKind::Initial => self.sent_i = SentPackets::new_at(next),
            PacketKind::Handshake => self.sent_h = SentPackets::new_at(next),
            PacketKind::OneRtt => self.sent_1 = SentPackets::new_at(next),
        }
    }

    // =========================================================================
    // Timers
    // =========================================================================

    /// Sending on the handshake path is blocked by §8.1 (RFC 9002 §6.2.2.1: no PTO then).
    closed spec fn amp_blocked_spec(&self) -> bool {
        !(self.paths.state_spec(self.hs_path) is Validated) && self.paths.budget_spec(self.hs_path) == 0
    }

    /// §10.1's deadline: `effective_idle_us` after `idle.last`.
    closed spec fn idle_term(&self) -> Option<u64> {
        let l = self.local_tp.max_idle_timeout;
        let p = match self.peer_tp {
            Some(t) => t.max_idle_timeout,
            None => 0u64,
        };
        if l == 0 && p == 0 {
            None
        } else {
            Some(
                spec_sat_add(
                    self.idle.last,
                    spec_max(spec_ms_to_us(spec_min_nz(l, p)), spec_sat3(self.pto_spec())),
                ),
            )
        }
    }

    /// The frame room `room_for` gives a packet of space `k` in `left` bytes.
    closed spec fn room_spec(&self, k: PacketKind, left: nat) -> Option<nat> {
        let pn = self.sent(k).next_pn_spec();
        let la = self.sent(k).largest_acked_spec();
        let n: nat = if pn_len_ok(pn, la, 1) { 1 } else if pn_len_ok(pn, la, 2) { 2 } else if pn_len_ok(pn, la, 3) { 3 } else { 4 };
        let need = self.header_bytes_spec(k) + n + AEAD_TAG_LEN + 3;
        if left < need { None } else { Some((left - need) as nat) }
    }

    /// A fresh datagram's budget on the active path.
    closed spec fn left_for_ack(&self) -> usize {
        let b = self.paths.budget_spec(self.paths.active_spec());
        if b > MAX_DATAGRAM { MAX_DATAGRAM } else { b as usize }
    }

    proof fn lemma_ack_term_kept(&self, o: Connection, k: PacketKind)
        requires
            self.tx_kept(o),
            self.now == o.now,
        ensures
            self.ack_term(k) == o.ack_term(k),
    {
        self.lemma_tx_kept(o);
        assert(self.active_dcid_spec() == o.active_dcid_spec());
        assert(self.header_bytes_spec(k) == o.header_bytes_spec(k));
        assert(self.room_spec(k, o.left_for_ack() as nat) == o.room_spec(k, o.left_for_ack() as nat));
    }

    /// No space built a packet, so none has an ACK due.
    proof fn lemma_no_packet_acks(&self, s01: Connection, s02: Connection, now: u64)
        requires
            s02.tx_kept(s01),
            self.tx_kept(s02),
            s02.now == s01.now,
            self.now == s02.now,
            later(s01.ack_term(PacketKind::Initial), now),
            later(s02.ack_term(PacketKind::Handshake), now),
            later(self.ack_term(PacketKind::OneRtt), now),
        ensures
            forall|k: PacketKind| later(#[trigger] self.ack_term(k), now),
    {
        let (i, h) = (PacketKind::Initial, PacketKind::Handshake);
        self.lemma_ack_term_kept(s02, i);
        s02.lemma_ack_term_kept(s01, i);
        self.lemma_ack_term_kept(s02, h);
        assert forall|k: PacketKind| later(#[trigger] self.ack_term(k), now) by {
            match k {
                PacketKind::Initial => {},
                PacketKind::Handshake => {},
                PacketKind::OneRtt => {},
            }
        }
    }

    /// A due ACK of space `k` can go in a fresh datagram on the active path: `data_datagram`'s send
    /// gate and budget, `start_frames`' room.
    closed spec fn ack_fits(&self, k: PacketKind) -> bool {
        let a = self.paths.active_spec();
        &&& !self.paths.mtu_failed_spec(a)
        &&& self.room_spec(k, self.left_for_ack() as nat) matches Some(r) && self.recv(k).full_ack_fits(
            self.now,
            self.local_tp.ack_delay_exponent,
            r as int,
        )
    }

    /// When space `k` owes an ACK, `RecvPns::ack_deadline` for a live space.
    closed spec fn ack_term(&self, k: PacketKind) -> Option<u64> {
        let r = self.recv(k);
        let first = r.first_unacked()->0;
        let m = spec_ms_to_us(self.local_tp.max_ack_delay);
        if !self.live(k) || r.eliciting_since_ack() == 0 || !self.ack_fits(k) {
            None
        } else {
            Some(
                match k {
                    PacketKind::OneRtt => if r.eliciting_since_ack() >= 2 || r.ack_blocked() {
                        first
                    } else if first + m > u64::MAX {
                        u64::MAX
                    } else {
                        (first + m) as u64
                    },
                    _ => first,
                },
            )
        }
    }

    /// When space `k`'s PTO fires: never for a dead space, with nothing in flight, or while §8.1
    /// blocks sending (RFC 9002 §6.2.2.1).
    closed spec fn pto_term(&self, k: PacketKind) -> Option<u64> {
        let s = self.sent(k).inflight_spec();
        if !self.live(k) || s.len() == 0 || self.amp_blocked_spec() {
            None
        } else {
            Some(
                crate::recovery::sat_add(
                    s.last().time,
                    self.recovery.pto_us_spec(k, self.peer_mad_spec()),
                ),
            )
        }
    }

    /// `r` is no later than every deadline `on_timeout` and `poll_transmit` act on, so a shell that
    /// sleeps until `r` misses none. A Closed connection has none: `lc.deadline` is stale there.
    pub closed spec fn timers_cover(&self, r: Option<u64>) -> bool {
        match self.lc.phase_spec() {
            Phase::Open => {
                &&& covers(r, self.idle_term())
                &&& forall|k: PacketKind| covers(r, #[trigger] self.ack_term(k))
                &&& forall|k: PacketKind| covers(r, #[trigger] self.pto_term(k))
                &&& forall|q: PathId|
                    #[trigger] self.paths.has(q) && timed(self.paths.path(q)) ==> covers(
                        r,
                        Some(expiry(self.paths.path(q), self.pto_spec())),
                    )
            },
            Phase::Closing | Phase::Draining => {
                &&& covers(r, self.lc.deadline_spec())
                &&& forall|q: PathId|
                    #[trigger] self.paths.has(q) && timed(self.paths.path(q)) ==> covers(
                        r,
                        Some(expiry(self.paths.path(q), self.pto_spec())),
                    )
            },
            Phase::Closed => r is None,
        }
    }

    /// Every validation's deadline is where it was: what a Closing send leaves.
    closed spec fn expiries_kept(&self, o: Connection) -> bool {
        &&& self.crypto_same(o)
        &&& self.paths.ids() == o.paths.ids()
        &&& self.recovery == o.recovery
        &&& self.peer_tp == o.peer_tp
        &&& forall|q: PathId|
            (#[trigger] self.paths.path(q)).challenge == o.paths.path(q).challenge && self.paths.path(q).owed
                == o.paths.path(q).owed
    }

    /// What the timer terms read, other than `paths` and `lc`, and the clock.
    closed spec fn clocks_kept(&self, o: Connection) -> bool {
        &&& self.now == o.now
        &&& self.idle == o.idle
        &&& self.local_tp == o.local_tp
        &&& self.peer_tp == o.peer_tp
        &&& self.hs_path == o.hs_path
        &&& self.recovery == o.recovery
        &&& self.sent_i == o.sent_i
        &&& self.sent_h == o.sent_h
        &&& self.sent_1 == o.sent_1
    }

    /// What a send leaves alone among what the timer terms read, and the Initial CRYPTO stream.
    closed spec fn tx_fixed(&self, o: Connection) -> bool {
        &&& self.crypto_same(o)
        &&& self.idle == o.idle
        &&& self.local_tp == o.local_tp
        &&& self.peer_tp == o.peer_tp
        &&& self.hs_path == o.hs_path
        &&& self.recovery == o.recovery
        &&& self.live_i == o.live_i
        &&& self.live_h == o.live_h
        &&& self.complete == o.complete
        &&& self.paths == o.paths
        &&& self.lc == o.lc
    }

    /// A send from `o` at `t` moved a timer only to a start at or after `t`, and left the
    /// CRYPTO streams alone (`crypto_same`).
    #[verifier::opaque]
    closed spec fn tx_timers(&self, o: Connection, t: u64) -> bool {
        &&& self.crypto_same(o)
        &&& self.lc.phase_spec() is Closed || {
            &&& self.lc.phase_spec() == o.lc.phase_spec()
            &&& self.paths.ids() == o.paths.ids()
            &&& self.local_tp == o.local_tp
            &&& self.peer_tp == o.peer_tp
            &&& self.hs_path == o.hs_path
            &&& self.recovery == o.recovery
            &&& self.live_i == o.live_i
            &&& self.live_h == o.live_h
            &&& self.complete == o.complete
            &&& self.idle.last == o.idle.last || t <= self.idle.last
            &&& forall|k: PacketKind|
                #[trigger] self.sent(k).inflight_spec() == o.sent(k).inflight_spec() || (self.sent(k).inflight_spec().len() > 0
                    && t <= self.sent(k).inflight_spec().last().time)
            &&& o.amp_blocked_spec() ==> self.amp_blocked_spec()
            &&& forall|q: PathId|
                #[trigger] self.paths.has(q) && timed(self.paths.path(q)) ==> o.paths.has(q) && (self.paths.path(q).challenge
                    == o.paths.path(q).challenge && timed(o.paths.path(q)) || t <= self.paths.path(q).challenge.unwrap().1)
        }
    }

    proof fn lemma_tx_trans(&self, m: Connection, o: Connection, t: u64)
        requires
            self.tx_timers(m, t),
            m.tx_timers(o, t),
        ensures
            self.tx_timers(o, t),
    {
        reveal(Connection::tx_timers);
        if !(self.lc.phase_spec() is Closed) {
            assert forall|k: PacketKind|
                #[trigger] self.sent(k).inflight_spec() == o.sent(k).inflight_spec() || (self.sent(k).inflight_spec().len() > 0
                    && t <= self.sent(k).inflight_spec().last().time) by {
                assert(self.sent(k).inflight_spec() == m.sent(k).inflight_spec() || (self.sent(k).inflight_spec().len() > 0
                    && t <= self.sent(k).inflight_spec().last().time));
                assert(m.sent(k).inflight_spec() == o.sent(k).inflight_spec() || (m.sent(k).inflight_spec().len() > 0
                    && t <= m.sent(k).inflight_spec().last().time));
            }
            assert forall|q: PathId|
                #[trigger] self.paths.has(q) && timed(self.paths.path(q)) implies o.paths.has(q) && (self.paths.path(q).challenge
                    == o.paths.path(q).challenge && timed(o.paths.path(q)) || t <= self.paths.path(q).challenge.unwrap().1) by {
                assert(m.paths.has(q));
                if self.paths.path(q).challenge == m.paths.path(q).challenge && timed(m.paths.path(q)) {
                    assert(m.paths.has(q) && timed(m.paths.path(q)));
                }
            }
        }
    }

    proof fn lemma_tx_closed(&self, o: Connection, t: u64)
        requires
            self.lc.phase_spec() is Closed,
            self.crypto_same(o),
        ensures
            self.tx_timers(o, t),
    {
        reveal(Connection::tx_timers);
    }

    proof fn lemma_tx_crypto(&self, o: Connection, t: u64)
        requires
            self.tx_timers(o, t),
        ensures
            self.crypto_kept(o),
            drained_kept(*self, o),
    {
        reveal(Connection::tx_timers);
    }

    proof fn lemma_tx_phase(&self, o: Connection, t: u64)
        requires
            self.tx_timers(o, t),
        ensures
            self.lc.phase_spec() == o.lc.phase_spec() || self.lc.phase_spec() is Closed,
    {
        reveal(Connection::tx_timers);
    }

    /// `commit_record`'s step: space `k` gained a record stamped `now`, and the idle timer may have restarted.
    proof fn lemma_tx_recorded(&self, o: Connection, k: PacketKind, g: SentPacket, now: u64)
        requires
            self.crypto_same(o),
            self.lc == o.lc,
            self.paths == o.paths,
            self.local_tp == o.local_tp,
            self.peer_tp == o.peer_tp,
            self.hs_path == o.hs_path,
            self.recovery == o.recovery,
            self.live_i == o.live_i,
            self.live_h == o.live_h,
            self.complete == o.complete,
            self.idle.last == o.idle.last || now <= self.idle.last,
            g.time == now,
            self.sent(k).inflight_spec() == o.sent(k).inflight_spec().push(g),
            forall|j: PacketKind| j != k ==> #[trigger] self.sent(j) == o.sent(j),
        ensures
            self.tx_timers(o, now),
    {
        reveal(Connection::tx_timers);
        assert forall|j: PacketKind|
            #[trigger] self.sent(j).inflight_spec() == o.sent(j).inflight_spec() || (self.sent(j).inflight_spec().len() > 0
                && now <= self.sent(j).inflight_spec().last().time) by {
            if j == k {
                assert(o.sent(k).inflight_spec().push(g).last() == g);
            }
        }
    }

    /// Collecting frames moved no timer.
    proof fn lemma_tx_kept_timers(&self, o: Connection, t: u64)
        requires
            self.tx_kept(o),
        ensures
            self.tx_timers(o, t),
    {
        reveal(Connection::tx_timers);
        self.lemma_tx_kept(o);
    }

    /// Nothing that a timer reads moved.
    proof fn lemma_tx_same(&self, o: Connection, t: u64)
        requires
            self.tx_fixed(o),
            forall|k: PacketKind| #[trigger] self.sent(k).inflight_spec() == o.sent(k).inflight_spec(),
        ensures
            self.tx_timers(o, t),
    {
        reveal(Connection::tx_timers);
    }

    proof fn lemma_tx_later(&self, o: Connection, t: u64, now: u64)
        requires
            o.lc.phase_spec() is Open,
            self.tx_timers(o, t),
            o.timers_later(now),
            now <= t,
            now < u64::MAX,
        ensures
            self.timers_later(now),
    {
        reveal(Connection::tx_timers);
        if self.lc.phase_spec() is Open {
            assert(self.pto_spec() == o.pto_spec());
            self.recovery.lemma_pto_pos(PacketKind::OneRtt, self.peer_mad_spec());
            assert(later(self.idle_term(), now));
            assert forall|k: PacketKind| later(#[trigger] self.pto_term(k), now) by {
                assert(later(o.pto_term(k), now));
                self.recovery.lemma_pto_pos(k, self.peer_mad_spec());
                assert(self.live(k) == o.live(k)) by {
                    match k {
                        PacketKind::Initial => {},
                        PacketKind::Handshake => {},
                        PacketKind::OneRtt => {},
                    }
                }
                assert(self.sent(k).inflight_spec() == o.sent(k).inflight_spec() || (self.sent(k).inflight_spec().len() > 0
                    && t <= self.sent(k).inflight_spec().last().time));
            }
            assert forall|q: PathId| #[trigger] self.paths.has(q) && timed(self.paths.path(q)) implies now < expiry(self.paths.path(q), self.pto_spec()) by {
                assert(o.paths.has(q));
                if self.paths.path(q).challenge == o.paths.path(q).challenge && timed(o.paths.path(q)) {
                    assert(o.paths.has(q) && timed(o.paths.path(q)));
                    assert(now < expiry(o.paths.path(q), o.pto_spec()));
                }
            }
        }
    }

    /// Every timer but the ACKs' is later than `now`: what `on_timeout(now, ..)` leaves.
    pub closed spec fn timers_later(&self, now: u64) -> bool {
        match self.lc.phase_spec() {
            Phase::Open => {
                &&& later(self.idle_term(), now)
                &&& forall|k: PacketKind| later(#[trigger] self.pto_term(k), now)
                &&& forall|q: PathId|
                    #[trigger] self.paths.has(q) && timed(self.paths.path(q)) ==> now < expiry(
                        self.paths.path(q),
                        self.pto_spec(),
                    )
            },
            Phase::Closing | Phase::Draining => {
                &&& later(self.lc.deadline_spec(), now)
                &&& forall|q: PathId|
                    #[trigger] self.paths.has(q) && timed(self.paths.path(q)) ==> now < expiry(
                        self.paths.path(q),
                        self.pto_spec(),
                    )
            },
            Phase::Closed => true,
        }
    }

    /// The clock `now()` reads.
    pub closed spec fn now_spec(&self) -> u64 {
        self.now
    }

    /// From `o`, the clock has not gone back, and every timer `o` had later than a `t` up to its
    /// clock still is: what a call between `on_timeout` and the `poll_transmit` loop must keep.
    /// Also the CRYPTO streams and completion unchanged, and no reopening, which every fn that
    /// keeps this keeps too (`lemma_keeps_crypto`).
    pub closed spec fn keeps_later(&self, o: Connection) -> bool {
        &&& o.now <= self.now
        &&& forall|t: u64| t < u64::MAX && t <= o.now && #[trigger] o.timers_later(t) ==> self.timers_later(t)
        &&& self.crypto_same(o)
        &&& self.lc.phase_spec() is Open ==> o.lc.phase_spec() is Open
    }

    pub proof fn lemma_keeps_crypto(&self, o: Connection)
        requires
            self.keeps_later(o),
        ensures
            self.crypto_kept(o),
            drained_kept(*self, o),
            self.phase_spec() is Open ==> o.phase_spec() is Open,
            self.live(PacketKind::OneRtt) == o.live(PacketKind::OneRtt),
    {
    }

    pub proof fn lemma_keeps_refl(&self)
        ensures
            self.keeps_later(*self),
    {
    }

    pub proof fn lemma_keeps_trans(&self, m: Connection, o: Connection)
        requires
            self.keeps_later(m),
            m.keeps_later(o),
        ensures
            self.keeps_later(o),
    {
        assert forall|t: u64| t < u64::MAX && t <= o.now && #[trigger] o.timers_later(t) implies self.timers_later(t) by {
            assert(m.timers_later(t));
        }
    }

    pub proof fn lemma_keeps_now(&self, o: Connection)
        requires
            self.keeps_later(o),
        ensures
            o.now_spec() <= self.now_spec(),
    {
    }

    pub proof fn lemma_keeps_elim(&self, o: Connection, t: u64)
        requires
            self.keeps_later(o),
            t < u64::MAX,
            t <= o.now_spec(),
            o.timers_later(t),
        ensures
            self.timers_later(t),
    {
    }

    /// Only `streams`, `events`, `cid_updates` and `tokens_registered` moved, and no timer reads
    /// them.
    proof fn lemma_keeps_streams(&self, o: Connection)
        requires
            *self == (Connection {
                streams: self.streams,
                events: self.events,
                cid_updates: self.cid_updates,
                tokens_registered: self.tokens_registered,
                ..o
            }),
        ensures
            self.keeps_later(o),
    {
        assert forall|t: u64| t < u64::MAX && t <= o.now && #[trigger] o.timers_later(t) implies self.timers_later(t) by {
            assert(self.pto_spec() == o.pto_spec());
            if self.lc.phase_spec() is Open {
                assert(self.idle_term() == o.idle_term());
                assert forall|k: PacketKind| later(#[trigger] self.pto_term(k), t) by {
                    assert(self.pto_term(k) == o.pto_term(k));
                    assert(later(o.pto_term(k), t));
                }
            }
        }
    }

    /// Every path `o` had is still here, its amplification trace only extended: the §8.1 counts
    /// of a datagram are never undone by what processing its packets does.
    closed spec fn amp_grew(&self, o: Connection) -> bool {
        forall|q: PathId| #[trigger] o.paths.has(q) ==> {
            &&& self.paths.has(q)
            &&& o.paths.amp_trace(q).len() <= self.paths.amp_trace(q).len()
            &&& forall|i: int|
                0 <= i < o.paths.amp_trace(q).len() ==> #[trigger] self.paths.amp_trace(q)[i]
                    == o.paths.amp_trace(q)[i]
        }
    }

    /// `amp_grew` composes.
    proof fn lemma_grew_trans(&self, m: Connection, o: Connection)
        requires
            self.amp_grew(m),
            m.amp_grew(o),
        ensures
            self.amp_grew(o),
    {
        assert forall|q: PathId| #[trigger] o.paths.has(q) implies {
            &&& self.paths.has(q)
            &&& o.paths.amp_trace(q).len() <= self.paths.amp_trace(q).len()
            &&& forall|i: int|
                0 <= i < o.paths.amp_trace(q).len() ==> #[trigger] self.paths.amp_trace(q)[i]
                    == o.paths.amp_trace(q)[i]
        } by {
            assert(m.paths.has(q));
            assert forall|i: int| 0 <= i < o.paths.amp_trace(q).len() implies #[trigger] self.paths.amp_trace(q)[i]
                == o.paths.amp_trace(q)[i] by {
                assert(m.paths.amp_trace(q)[i] == o.paths.amp_trace(q)[i]);
            }
        }
    }

    /// `o`'s paths are all here with their traces unchanged.
    proof fn lemma_grew_same(&self, o: Connection)
        requires
            forall|q: PathId| #[trigger] o.paths.has(q) ==> self.paths.has(q) && self.paths.amp_trace(q)
                == o.paths.amp_trace(q),
        ensures
            self.amp_grew(o),
    {
    }

    /// Every ACK timer is later than `now`: what draining `poll_transmit` leaves.
    pub closed spec fn acks_later(&self, now: u64) -> bool {
        self.lc.phase_spec() is Open ==> forall|k: PacketKind| later(#[trigger] self.ack_term(k), now)
    }

    /// `self` is `o` with PTOs fired: what `pto_term`, `idle_term` and the paths' expiries read, other
    /// than the `sent`s and a larger `pto_count`, is the same.
    proof fn lemma_pto_later(&self, o: Connection, k: PacketKind, t: u64)
        requires
            self.sent(k).inflight_spec() == o.sent(k).inflight_spec(),
            self.live(k) == o.live(k),
            self.paths == o.paths,
            self.hs_path == o.hs_path,
            self.peer_tp == o.peer_tp,
            o.recovery.pto_count_spec() <= self.recovery.pto_count_spec(),
            later(o.pto_term(k), t),
        ensures
            later(self.pto_term(k), t),
    {
        o.recovery.lemma_pto_grows(self.recovery, k, o.peer_mad_spec());
    }

    proof fn lemma_pto_spec_grows(&self, o: Connection)
        requires
            self.peer_tp == o.peer_tp,
            o.recovery.pto_count_spec() <= self.recovery.pto_count_spec(),
        ensures
            o.pto_spec() <= self.pto_spec(),
    {
        o.recovery.lemma_pto_grows(self.recovery, PacketKind::OneRtt, o.peer_mad_spec());
    }

    /// Open after step 6: the terms step 2, `fail_paths` and `fire_ptos` left later than `t` still are.
    proof fn lemma_after_timeout(&self, s3: Connection, s2: Connection, s5: Connection, t: u64, pto0: u64)
        requires
            self.lc.phase_spec() is Open,
            self.lc == s3.lc,
            self.frames_kept(s3),
            self.paths == s3.paths,
            self.clocks_kept(s3),
            forall|k: PacketKind| later(#[trigger] s3.pto_term(k), t),
            s3.lc == s5.lc,
            s3.paths == s5.paths,
            s3.idle == s2.idle,
            s3.local_tp == s2.local_tp,
            s3.peer_tp == s2.peer_tp,
            s2.recovery.pto_count_spec() <= s3.recovery.pto_count_spec(),
            s2.lc.phase_spec() is Open ==> later(s2.idle_term(), t),
            s5.lc == s2.lc || s5.lc.phase_spec() is Closed,
            pto0 == s2.pto_spec(),
            forall|q: PathId| #[trigger] s5.paths.has(q) && timed(s5.paths.path(q)) ==> t < expiry(s5.paths.path(q), pto0),
        ensures
            self.timers_later(t),
    {
        self.lemma_pto_spec_grows(s2);
        assert(later(self.idle_term(), t));
        assert forall|k: PacketKind| later(#[trigger] self.pto_term(k), t) by {
            assert(later(s3.pto_term(k), t));
            match k {
                PacketKind::Initial => {},
                PacketKind::Handshake => {},
                PacketKind::OneRtt => {},
            }
        }
        assert forall|q: PathId| #[trigger] self.paths.has(q) && timed(self.paths.path(q)) implies t < expiry(self.paths.path(q), self.pto_spec()) by {
            assert(s5.paths.has(q));
            assert(t < expiry(self.paths.path(q), pto0));
        }
    }

    proof fn lemma_timers_weaken(&self, t: u64, now: u64)
        requires
            now <= t,
            self.timers_later(t),
        ensures
            self.timers_later(now),
    {
        if self.lc.phase_spec() is Open {
            assert forall|k: PacketKind| later(#[trigger] self.pto_term(k), now) by {
                assert(later(self.pto_term(k), t));
            }
            assert forall|q: PathId| #[trigger] self.paths.has(q) && timed(self.paths.path(q)) implies now < expiry(self.paths.path(q), self.pto_spec()) by {
                assert(t < expiry(self.paths.path(q), self.pto_spec()));
            }
        } else if !(self.lc.phase_spec() is Closed) {
            assert forall|q: PathId| #[trigger] self.paths.has(q) && timed(self.paths.path(q)) implies now < expiry(self.paths.path(q), self.pto_spec()) by {
                assert(t < expiry(self.paths.path(q), self.pto_spec()));
            }
        }
    }

    /// What `on_timeout(now, ..)` guarantees of `self`, from `o`.
    pub closed spec fn timed_out(&self, o: Connection, now: u64) -> bool {
        // P15 (§9.3.2, §14.2), in every phase: the active path's challenge expired, so the active path
        // is usable.
        &&& expired(o.paths.path(o.paths.active_spec()), now, o.pto_spec()) ==> usable(
            self.paths.path(self.paths.active_spec()),
        ) || self.lc.phase_spec() is Closed
        // §10.1.
        &&& o.lc.phase_spec() is Open && o.idle_term() is Some && now >= o.idle_term()->0 ==> !(
        self.lc.phase_spec() is Open)
        // §10.2.
        &&& (o.lc.phase_spec() is Closing || o.lc.phase_spec() is Draining) && o.lc.deadline_spec() is Some
            && now >= o.lc.deadline_spec()->0 ==> self.lc.phase_spec() is Closed
    }

    #[verifier::spinoff_prover]
    fn idle_deadline(&self) -> (r: Option<u64>)
        requires
            self.wf(),
        ensures
            r == self.idle_term(),
    {
        let peer = match &self.peer_tp {
            Some(t) => Some(t.max_idle_timeout),
            None => None,
        };
        match effective_idle_us(self.local_tp.max_idle_timeout, peer, self.pto()) {
            Some(e) => Some(self.idle.deadline(e)),
            None => None,
        }
    }

    #[verifier::spinoff_prover]
    fn ack_deadline_of(&self, k: PacketKind) -> (r: Option<u64>)
        requires
            self.wf(),
        ensures
            r == self.ack_term(k),
    {
        if !self.is_live(k) {
            return None;
        }
        let q = self.paths.active();
        proof {
            self.paths.lemma_wf();
        }
        // An ACK that `data_datagram` cannot place keeps no deadline, or a shell sleeping until it
        // would spin. Only a receive or a change of active path changes that; `next_timeout` is
        // read again after both.
        if self.paths.mtu_failed(q) {
            return None;
        }
        let b = self.paths.budget(q);
        let left = if b > MAX_DATAGRAM as u64 { MAX_DATAGRAM } else { b as usize };
        let room = match self.room_for(k, left) {
            Some(r) => r,
            None => return None,
        };
        // A full ACK only grows with the clock (the ACK Delay field), so one that does not fit now
        // stays unplaceable until the budget changes.
        match self.recv_ref(k).build_ack(self.now, self.local_tp.ack_delay_exponent, room) {
            Some(a) => if a.ranges.len() + 1 != self.recv_ref(k).range_len() {
                return None;
            },
            None => return None,
        }
        self.recv_ref(k).ack_deadline(ms_to_us(self.local_tp.max_ack_delay))
    }

    #[verifier::spinoff_prover]
    fn pto_deadline_of(&self, k: PacketKind) -> (r: Option<u64>)
        requires
            self.wf(),
        ensures
            r == self.pto_term(k),
    {
        if !self.is_live(k) {
            return None;
        }
        let h = self.hs_path;
        let blocked = !matches!(self.paths.state(h), PathState::Validated) && self.paths.budget(h) == 0;
        self.recovery.pto_deadline(k, self.sent_ref(k).last_sent_time(), self.peer_mad(), blocked)
    }

    /// The earliest deadline of an Open connection.
    #[verifier::spinoff_prover]
    fn open_timeout(&self) -> (r: Option<u64>)
        requires
            self.wf(),
            self.lc.phase_spec() is Open,
        ensures
            self.timers_cover(r),
            forall|now: u64| #[trigger] self.timers_later(now) && self.acks_later(now) ==> later(r, now),
    {
        let m0 = self.idle_deadline();
        let m1 = earlier(m0, self.ack_deadline_of(PacketKind::Initial));
        let m2 = earlier(m1, self.ack_deadline_of(PacketKind::Handshake));
        let m3 = earlier(m2, self.ack_deadline_of(PacketKind::OneRtt));
        let m4 = earlier(m3, self.pto_deadline_of(PacketKind::Initial));
        let m5 = earlier(m4, self.pto_deadline_of(PacketKind::Handshake));
        let m6 = earlier(m5, self.pto_deadline_of(PacketKind::OneRtt));
        //= https://www.rfc-editor.org/rfc/rfc9000#section-9.4
        //# This timer SHOULD be set as described in Section 6.2.1 of
        //# [QUIC-RECOVERY] and MUST NOT be more aggressive.
        let pd = self.paths.deadline(self.pto());
        let m7 = earlier(m6, pd);
        proof {
            lemma_covers_chain(m7, m6, m5);
            lemma_covers_chain(m7, m5, m4);
            lemma_covers_chain(m7, m4, m3);
            lemma_covers_chain(m7, m3, m2);
            lemma_covers_chain(m7, m2, m1);
            lemma_covers_chain(m7, m1, m0);
            assert(covers(m7, self.idle_term()));
            assert forall|k: PacketKind| covers(m7, #[trigger] self.ack_term(k)) by {
                match k {
                    PacketKind::Initial => lemma_covers_chain(m7, m1, self.ack_term(k)),
                    PacketKind::Handshake => lemma_covers_chain(m7, m2, self.ack_term(k)),
                    PacketKind::OneRtt => lemma_covers_chain(m7, m3, self.ack_term(k)),
                }
            }
            assert forall|k: PacketKind| covers(m7, #[trigger] self.pto_term(k)) by {
                match k {
                    PacketKind::Initial => lemma_covers_chain(m7, m4, self.pto_term(k)),
                    PacketKind::Handshake => lemma_covers_chain(m7, m5, self.pto_term(k)),
                    PacketKind::OneRtt => lemma_covers_chain(m7, m6, self.pto_term(k)),
                }
            }
            assert forall|q: PathId| #[trigger] self.paths.has(q) && timed(self.paths.path(q)) implies covers(
                m7,
                Some(expiry(self.paths.path(q), self.pto_spec())),
            ) by {
                assert(pd is Some);
                assert(pd->0 <= expiry(self.paths.path(q), self.pto_spec()));
            }
            assert forall|now: u64| #[trigger] self.timers_later(now) && self.acks_later(now) implies later(m7, now) by {
                assert(later(self.ack_term(PacketKind::Initial), now));
                assert(later(self.ack_term(PacketKind::Handshake), now));
                assert(later(self.ack_term(PacketKind::OneRtt), now));
                assert(later(self.pto_term(PacketKind::Initial), now));
                assert(later(self.pto_term(PacketKind::Handshake), now));
                assert(later(self.pto_term(PacketKind::OneRtt), now));
                if let Some(d) = pd {
                    let q = choose|q: PathId| #[trigger] self.paths.has(q) && timed(self.paths.path(q)) && d == expiry(self.paths.path(q), self.pto_spec());
                    assert(self.paths.has(q) && timed(self.paths.path(q)));
                }
            }
        }
        m7
    }

    /// When to call `on_timeout` next. None once Closed, or if no timer runs.
    #[verifier::spinoff_prover]
    pub fn next_timeout(&self) -> (r: Option<u64>)
        requires
            self.wf(),
        ensures
            self.timers_cover(r),
            forall|now: u64| #[trigger] self.timers_later(now) && self.acks_later(now) ==> later(r, now),
    {
        match self.lc.phase() {
            Phase::Closed => None,
            Phase::Closing | Phase::Draining => self.close_timeout(),
            Phase::Open => self.open_timeout(),
        }
    }

    /// The earliest deadline of a Closing or Draining connection: its own, or a validation's, which
    /// `on_timeout` acts on until Closed (§9.3.2).
    #[verifier::spinoff_prover]
    fn close_timeout(&self) -> (r: Option<u64>)
        requires
            self.wf(),
            self.lc.phase_spec() is Closing || self.lc.phase_spec() is Draining,
        ensures
            self.timers_cover(r),
            forall|now: u64| #[trigger] self.timers_later(now) && self.acks_later(now) ==> later(r, now),
    {
        let pd = self.paths.deadline(self.pto());
        let r = earlier(self.lc.deadline(), pd);
        proof {
            assert forall|q: PathId| #[trigger] self.paths.has(q) && timed(self.paths.path(q)) implies covers(
                r,
                Some(expiry(self.paths.path(q), self.pto_spec())),
            ) by {
                assert(pd is Some);
                assert(pd->0 <= expiry(self.paths.path(q), self.pto_spec()));
            }
            assert forall|now: u64| #[trigger] self.timers_later(now) && self.acks_later(now) implies later(r, now) by {
                if let Some(d) = pd {
                    let q = choose|q: PathId| #[trigger] self.paths.has(q) && timed(self.paths.path(q)) && d == expiry(self.paths.path(q), self.pto_spec());
                    assert(self.paths.has(q) && timed(self.paths.path(q)));
                }
            }
        }
        r
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-13.3
    //# Upon detecting losses, a sender MUST take appropriate congestion
    //# control action.
    /// Space `k`'s PTO fired: everything in flight is lost (the placeholder, recovery.rs), its frames
    /// are requeued, and the space owes a probe (E8).
    #[verifier::spinoff_prover]
    fn fire_pto(&mut self, k: PacketKind, now: u64)
        requires
            old(self).wf(),
        ensures
            final(self).crypto_same(*old(self)),
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            final(self).paths == old(self).paths,
            final(self).lc == old(self).lc,
            final(self).idle == old(self).idle,
            final(self).local_tp == old(self).local_tp,
            final(self).peer_tp == old(self).peer_tp,
            final(self).hs_path == old(self).hs_path,
            final(self).sent(k).inflight_spec().len() == 0,
            forall|j: PacketKind| j != k ==> #[trigger] final(self).sent(j) == old(self).sent(j),
            old(self).recovery.pto_count_spec() <= final(self).recovery.pto_count_spec(),
            final(self).now == old(self).now,
    {
        let mut lost: Vec<SentPacket> = Vec::new();
        match k {
            PacketKind::Initial => self.sent_i.drain_inflight(&mut lost),
            PacketKind::Handshake => self.sent_h.drain_inflight(&mut lost),
            PacketKind::OneRtt => self.sent_1.drain_inflight(&mut lost),
        }
        self.recovery.on_packets_lost(k, lost.len(), now);
        let ghost s0 = *old(self);
        let ghost s1 = *self;
        let mut i: usize = 0;
        while i < lost.len()
            invariant
                i <= lost@.len(),
                self.wf(),
                self.frames_kept(s0),
                self.crypto_same(s0),
                self.paths == s0.paths,
                self.lc == s0.lc,
                self.clocks_kept(s1),
            decreases lost@.len() - i,
        {
            let frames = lost[i].frames.as_slice();
            let mut j: usize = 0;
            while j < frames.len()
                invariant
                    j <= frames@.len(),
                    self.wf(),
                    self.frames_kept(s0),
                    self.crypto_same(s0),
                    self.paths == s0.paths,
                    self.lc == s0.lc,
                    self.clocks_kept(s1),
                decreases frames@.len() - j,
            {
                self.on_lost_frame(k, &frames[j]);
                j += 1;
            }
            i += 1;
        }
        proof {
            self.recovery.lemma_wf();
        }
        self.recovery.on_pto_fired();
        match k {
            PacketKind::Initial => self.probe_i = true,
            PacketKind::Handshake => self.probe_h = true,
            PacketKind::OneRtt => self.probe_1 = true,
        }
    }

    /// Whether space `k`'s PTO has fired by `now`.
    #[verifier::spinoff_prover]
    fn pto_passed(&self, k: PacketKind, now: u64) -> (r: bool)
        requires
            self.wf(),
        ensures
            !r ==> later(self.pto_term(k), now),
    {
        match self.pto_deadline_of(k) {
            Some(d) => now >= d,
            None => false,
        }
    }

    /// Fires every space whose PTO passed: one left due would wake the shell again at `t`. Each
    /// firing lengthens the PTO, so a space it did not fire stays later than `t`.
    #[verifier::spinoff_prover]
    fn fire_ptos(&mut self, t: u64)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            final(self).crypto_same(*old(self)),
            final(self).paths == old(self).paths,
            final(self).lc == old(self).lc,
            final(self).idle == old(self).idle,
            final(self).local_tp == old(self).local_tp,
            final(self).peer_tp == old(self).peer_tp,
            final(self).hs_path == old(self).hs_path,
            old(self).recovery.pto_count_spec() <= final(self).recovery.pto_count_spec(),
            forall|k: PacketKind| later(#[trigger] final(self).pto_term(k), t),
            final(self).now == old(self).now,
    {
        let ghost s0 = *self;
        let i = PacketKind::Initial;
        let h = PacketKind::Handshake;
        let o = PacketKind::OneRtt;
        if self.pto_passed(i, t) {
            self.fire_pto(i, t);
        }
        let ghost s1 = *self;
        proof {
            assert(later(s1.pto_term(i), t));
        }
        if self.pto_passed(h, t) {
            self.fire_pto(h, t);
        }
        let ghost s2 = *self;
        proof {
            assert(later(s2.pto_term(h), t));
            self.lemma_pto_later(s1, i, t);
        }
        if self.pto_passed(o, t) {
            self.fire_pto(o, t);
        }
        proof {
            assert(later(self.pto_term(o), t));
            self.lemma_pto_later(s2, i, t);
            self.lemma_pto_later(s2, h, t);
            assert forall|k: PacketKind| later(#[trigger] self.pto_term(k), t) by {
                match k {
                    PacketKind::Initial => {},
                    PacketKind::Handshake => {},
                    PacketKind::OneRtt => {},
                }
            }
        }
    }

    /// Abandons every expired validation, and says whether the active path's was one. Only `paths`
    /// changes.
    #[verifier::spinoff_prover]
    fn expire_paths(&mut self, now: u64, pto0: u64) -> (active_failed: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).frames_kept(*old(self)),
            *final(self) == (Connection { paths: final(self).paths, ..*old(self) }),
            final(self).paths.active_spec() == old(self).paths.active_spec(),
            expired(old(self).paths.path(old(self).paths.active_spec()), now, pto0) ==> active_failed,
            forall|q: PathId|
                #[trigger] final(self).paths.has(q) && timed(final(self).paths.path(q)) ==> now < expiry(
                    final(self).paths.path(q),
                    pto0,
                ),
    {
        let ghost s = *self;
        let a = self.paths.active();
        let mut active_failed = false;
        loop
            invariant
                self.wf(),
                self.frames_kept(s),
                *self == (Connection { paths: self.paths, ..s }),
                self.paths.active_spec() == a,
                a == s.paths.active_spec(),
                !active_failed ==> self.paths.path(a) == s.paths.path(a),
            ensures
                self.wf(),
                self.frames_kept(s),
                *self == (Connection { paths: self.paths, ..s }),
                self.paths.active_spec() == a,
                expired(s.paths.path(a), now, pto0) ==> active_failed,
                forall|q: PathId|
                    #[trigger] self.paths.has(q) && timed(self.paths.path(q)) ==> now < expiry(
                        self.paths.path(q),
                        pto0,
                    ),
            decreases self.paths.timed_count(),
        {
            let ghost s1 = *self;
            proof {
                s1.paths.lemma_wf();
            }
            //= https://www.rfc-editor.org/rfc/rfc9000#section-9.4
            //# This timer SHOULD be set as described in Section 6.2.1 of
            //# [QUIC-RECOVERY] and MUST NOT be more aggressive.
            match self.paths.on_timeout(now, pto0) {
                None => {
                    proof {
                        assert(s1.paths.has(a));
                    }
                    break;
                },
                Some(f) => {
                    proof {
                        self.lemma_path_edit(s1, f);
                        self.lemma_dcids_same(s1, f);
                        assert(s1.paths.has(s1.hs_path));
                    }
                    if f == a {
                        active_failed = true;
                    }
                },
            }
        }
        active_failed
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-9.3.2
    //# To protect the connection from failing due to such a spurious
    //# migration, an endpoint MUST revert to using the last validated peer
    //# address when validation of a new peer address fails.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-9.3.2
    //# If an endpoint has no state about the last validated peer address, it
    //# MUST close the connection silently by discarding all connection
    //# state.
    // Both in every phase but Closed (`on_timeout`); `next_timeout` wakes for them in Closing and
    // Draining too.
    // ponytail: only two validated paths are remembered, so after 0→1→2 with both 1 and 2 failing we close although 0 might still work (liveness only); a longer validated history if migration chains matter.
    /// The active path is no longer usable: back to the last validated one, which `Paths::wf` makes
    /// usable. It takes an unused CID if it has lost its own, so `wf_dcids` holds; with none left,
    /// or no such path, the connection closes silently.
    #[verifier::spinoff_prover]
    fn fall_back(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).crypto_same(*old(self)),
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            final(self).frames_kept(*old(self)),
            final(self).lc == old(self).lc || final(self).lc.phase_spec() is Closed,
            usable(final(self).paths.path(final(self).paths.active_spec())) || final(self).lc.phase_spec() is Closed,
            final(self).clocks_kept(*old(self)),
            forall|q: PathId| #[trigger] final(self).paths.has(q) && timed(final(self).paths.path(q)) ==> timed(old(self).paths.path(q)) && final(self).paths.path(q).challenge == old(self).paths.path(q).challenge,
    {
        proof {
            self.paths.lemma_wf();
        }
        let v = match self.paths.last_validated() {
            Some(v) => v,
            None => {
                self.lc.close_silently();
                self.streams = None;
                return;
            },
        };
        if self.paths.dcid(v).is_none() {
            proof {
                self.lemma_weak_of_wf();
            }
            let ghost s0 = *self;
            if !self.fresh_dcid(v) {
                self.lc.close_silently();
                self.streams = None;
                return;
            }
            proof {
                assert forall|q: PathId| #[trigger] self.paths.has(q) implies self.not_stale(q) by {
                    if q != v {
                        assert(s0.paths.has(q));
                        assert(s0.not_stale(q));
                        if let Some(c) = self.paths.path(q).dcid {
                            assert(peer_has_cid(s0.peer_cids.entries(), c));
                            assert(peer_has_cid(self.peer_cids.entries(), c));
                        }
                    }
                }
                self.lemma_wf_of_weak();
            }
        }
        let ghost s1 = *self;
        self.paths.set_active(v);
        proof {
            self.lemma_active_set(s1, v);
        }
    }

    /// Steps 1 and 2: the closing, draining and idle deadlines.
    #[verifier::spinoff_prover]
    fn timeout_phase(&mut self, t: u64)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            final(self).frames_kept(*old(self)),
            final(self).paths == old(self).paths,
            final(self).clocks_kept(*old(self)),
            final(self).crypto_same(*old(self)),
            final(self).lc == old(self).lc || final(self).lc.phase_spec() is Closed,
            final(self).lc.phase_spec() is Open ==> later(final(self).idle_term(), t),
            !(final(self).lc.phase_spec() is Open) ==> final(self).lc.phase_spec() is Closed || later(final(self).lc.deadline_spec(), t),
            (old(self).lc.phase_spec() is Closing || old(self).lc.phase_spec() is Draining) && (old(self).lc.deadline_spec() matches Some(d) && t >= d) ==> final(self).lc.phase_spec() is Closed,
            old(self).lc.phase_spec() is Open && old(self).idle_term() is Some && t >= old(self).idle_term()->0 ==> !(final(self).lc.phase_spec() is Open),
    {
        // Step 1: the closing and draining deadlines.
        self.lc.on_timeout(t);
        if !matches!(self.lc.phase(), Phase::Open) {
            self.streams = None;
        }
        // Step 2.
        //= https://www.rfc-editor.org/rfc/rfc9000#section-10.1
        //# To avoid excessively small idle timeout periods, endpoints MUST
        //# increase the idle timeout period to be at least three times the
        //# current Probe Timeout (PTO).
        if matches!(self.lc.phase(), Phase::Open) {
            if let Some(d) = self.idle_deadline() {
                if t >= d {
                    self.lc.close_silently();
                    self.streams = None;
                }
            }
        }
        proof {
        }
    }

    /// Steps 4 and 5.
    #[verifier::spinoff_prover]
    fn fail_paths(&mut self, t: u64, pto0: u64)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            final(self).frames_kept(*old(self)),
            final(self).clocks_kept(*old(self)),
            final(self).crypto_same(*old(self)),
            final(self).lc == old(self).lc || final(self).lc.phase_spec() is Closed,
            expired(old(self).paths.path(old(self).paths.active_spec()), t, pto0) ==> usable(
                final(self).paths.path(final(self).paths.active_spec()),
            ) || final(self).lc.phase_spec() is Closed,
            forall|q: PathId|
                #[trigger] final(self).paths.has(q) && timed(final(self).paths.path(q)) ==> t < expiry(
                    final(self).paths.path(q),
                    pto0,
                ),
    {
        let active_failed = self.expire_paths(t, pto0);
        let ghost s4 = *self;
        proof {
            self.paths.lemma_wf();
        }
        let a = self.paths.active();
        if active_failed && (!matches!(self.paths.state(a), PathState::Validated) || self.paths.mtu_failed(a)) {
            self.fall_back();
        }
        proof {
            assert forall|q: PathId| #[trigger] self.paths.has(q) && timed(self.paths.path(q)) implies t < expiry(self.paths.path(q), pto0) by {
                assert(s4.paths.has(q));
                assert(timed(s4.paths.path(q)));
            }
        }
    }

    /// The timers `next_timeout` named. The clock never goes back, so a late or early `now` is safe.
    #[verifier::spinoff_prover]
    pub fn on_timeout(&mut self, now: u64, rand: &[u8; RAND_LEN])
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).out_log() == old(self).out_log(),
            final(self).timed_out(*old(self), now),
            final(self).timers_later(now),
            now <= final(self).now_spec(),
            final(self).crypto_kept(*old(self)),
            drained_kept(*final(self), *old(self)),
    {
        let ghost o = *self;
        if now > self.now {
            self.now = now;
        }
        let t = self.now;
        let pto0 = self.pto();
        self.timeout_phase(t);
        let ghost s2 = *self;
        // Steps 4 and 5, in every phase but Closed: §9.3.2 has no exception by state, and
        // `next_timeout` wakes at the earliest validation deadline in Closing and Draining too. A
        // revert in Closing moves the repeated CONNECTION_CLOSE to the validated address (it goes on
        // the active path, within its §8.1 budget and the closing byte cap); the silent close
        // outranks §10.2's SHOULD NOT on ending the closing or draining state early.
        if !matches!(self.lc.phase(), Phase::Closed) {
            self.fail_paths(t, pto0);
        }
        let ghost s5 = *self;
        // Step 3: every live space whose PTO passed.
        if matches!(self.lc.phase(), Phase::Open) {
            self.fire_ptos(t);
            let ghost s3 = *self;
            // Step 6.
            self.issue_cids(rand);
            proof {
                self.lemma_after_timeout(s3, s2, s5, t, pto0);
            }
        }
        proof {
            if self.lc.phase_spec() is Closing || self.lc.phase_spec() is Draining {
                assert(self.pto_spec() == pto0);
                assert(s2.lc == self.lc);
            }
            self.lemma_timers_weaken(t, now);
        }
    }

    /// What 3e's shell relies on: after `on_timeout(now)` and a `poll_transmit` loop to None, every
    /// timer is later than `now`, so sleeping until `next_timeout` cannot spin. Never called: its
    /// contract is the proof, from the three public contracts alone. That the loop ends is not
    /// proved, so it stops at `cap` as the shell does, and says nothing then.
    #[verifier::spinoff_prover]
    #[allow(dead_code)]
    fn settled_later(&mut self, now: u64, rand: &[u8; RAND_LEN], cap: usize) -> (r: Option<Option<u64>>)
        requires
            old(self).wf(),
            now < u64::MAX,
        ensures
            r matches Some(t) ==> later(t, now),
    {
        self.on_timeout(now, rand);
        let mut i: usize = 0;
        while i < cap
            invariant
                self.wf(),
                now < u64::MAX,
                self.timers_later(now),
            decreases cap - i,
        {
            if self.poll_transmit(now).is_none() {
                return Some(self.next_timeout());
            }
            i += 1;
        }
        None
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

    /// The end of the received CRYPTO data at level `k` (RFC 9001 §4.1.3).
    pub fn crypto_end(&self, k: PacketKind) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self.crypto_end_spec(k),
            self.crypto_base_spec(k) <= r,
            r > 0 ==> self.crypto_received(k, (r - 1) as nat),
            self.crypto_base_spec(k) <= self.crypto_contiguous_spec(k) <= r,
            // No byte at or past the end was received: `r` is the end of the data received.
            forall|p: nat| #[trigger] self.crypto_received(k, p) ==> p < r,
    {
        proof {
            reveal(crx_ok);
            match k {
                PacketKind::Initial => {
                    self.crx_i.lemma_wf();
                },
                PacketKind::Handshake => {
                    self.crx_h.lemma_wf();
                },
                PacketKind::OneRtt => {
                    self.crx_1.lemma_wf();
                },
            }
        }
        match k {
            PacketKind::Initial => self.crx_i.end(),
            PacketKind::Handshake => self.crx_h.end(),
            PacketKind::OneRtt => self.crx_1.end(),
        }
    }

    /// How far level `k`'s CRYPTO data has been read: with `crypto_end`, what is buffered out of
    /// order (RFC 9001 §4.1.3).
    pub fn crypto_base(&self, k: PacketKind) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self.crypto_base_spec(k),
    {
        match k {
            PacketKind::Initial => self.crx_i.start(),
            PacketKind::Handshake => self.crx_h.start(),
            PacketKind::OneRtt => self.crx_1.start(),
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-17.2
    //# Endpoints that receive a version 1 long header
    //# with a value larger than 20 MUST drop the packet.
    /// The length of the client's first Initial SCID, at most 20 (`HandshakeIds::wf`).
    pub fn client_scid_len(&self) -> (r: usize)
        requires
            self.wf(),
        ensures
            r == self.client_scid_spec().len(),
            r <= MAX_CID_LEN,
    {
        self.ids.client_scid().len()
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

    pub fn now(&self) -> (r: u64)
        ensures
            r == self.now_spec(),
    {
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

/// The three CRYPTO streams' `wf`, and a stream whose space is not live is drained. Opaque, so a
/// fn that changes neither a CRYPTO stream nor `live_i`, `live_h`, `complete` carries it by field
/// congruence; the fns that do (`on_crypto_frame`, `crypto_read`, `crypto_drop`, `discard`,
/// `on_handshake_complete`, `crypto_end`'s proof, the constructor) reveal it.
#[verifier::opaque]
spec fn crx_ok(i: CryptoStream, h: CryptoStream, o: CryptoStream, live_i: bool, live_h: bool, complete: bool) -> bool {
    &&& i.wf() && h.wf() && o.wf()
    &&& !live_i ==> i.drained() && i.buf_len_spec() == 0
    &&& !live_h ==> h.drained()
    &&& !complete ==> o.drained()
}

/// No level holds an unread in-order CRYPTO byte.
pub open spec fn crypto_all_drained(c: Connection) -> bool {
    forall|k: PacketKind| #[trigger] crypto_drained(c, k)
}

/// Level `k` holds no unread in-order CRYPTO byte: it has been read to its contiguous end.
pub open spec fn crypto_drained(c: Connection, k: PacketKind) -> bool {
    c.crypto_base_spec(k) == c.crypto_contiguous_spec(k)
}

/// Every level drained in `o` is drained in `c`.
pub open spec fn drained_kept(c: Connection, o: Connection) -> bool {
    forall|k: PacketKind| #[trigger] crypto_drained(o, k) ==> crypto_drained(c, k)
}

/// §8.1: trace `t1` starts with `t0` and then the receipt of an `n`-byte datagram. Opaque, so a
/// caller forwards it without unfolding sequence equality.
#[verifier::opaque]
pub open spec fn recv_counted(t0: Seq<AmpEv>, t1: Seq<AmpEv>, n: nat) -> bool {
    t1.len() > t0.len() && t1.take(t0.len() + 1 as int) == t0.push(AmpEv::Recv(n))
}

/// `a`, if any, is later than `now`.
pub open spec fn later(a: Option<u64>, now: u64) -> bool {
    a matches Some(d) ==> now < d
}

/// `r` is no later than `a`.
pub open spec fn covers(r: Option<u64>, a: Option<u64>) -> bool {
    a matches Some(d) ==> r matches Some(m) && m <= d
}

proof fn lemma_covers_chain(a: Option<u64>, b: Option<u64>, c: Option<u64>)
    requires
        covers(a, b),
        covers(b, c),
    ensures
        covers(a, c),
{
}

/// The earlier deadline; None only when both are.
fn earlier(a: Option<u64>, b: Option<u64>) -> (r: Option<u64>)
    ensures
        covers(r, a),
        covers(r, b),
        r == a || r == b,
{
    match (a, b) {
        (Some(x), Some(y)) => Some(if x <= y {
            x
        } else {
            y
        }),
        (Some(x), None) => Some(x),
        (None, y) => y,
    }
}

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

// =============================================================================
// Transmit: what the frame helpers and the commit say
// =============================================================================

/// What `poll_transmit` guarantees of a datagram it returns, `o` the connection before it and `c`
/// after.
pub open spec fn transmit_ok(o: Connection, c: Connection, d: SpecOutDatagram) -> bool {
    // P16.
    &&& out_datagram_len(d) <= MAX_DATAGRAM
    // P7.
    &&& forall|i: int|
        0 <= i < d.packets.len() ==> out_packet_wf(
            #[trigger] d.packets[i],
            c.sent(d.packets[i].kind).largest_acked_spec(),
        )
    // P4: fresh packet numbers, strictly increasing per space.
    &&& forall|i: int|
        0 <= i < d.packets.len() ==> o.sent((#[trigger] d.packets[i]).kind).next_pn_spec()
            <= d.packets[i].pn
    &&& forall|k: PacketKind| #[trigger] pns_ok(packets_pns(d.packets, k), c.sent(k).next_pn_spec())
    // P5.
    &&& forall|i: int, j: int|
        0 <= i < d.packets.len() && 0 <= j < d.packets[i].frames.len() ==> (
        #[trigger] d.packets[i].frames[j] matches SpecFrame::Ack(a) ==> forall|pn: u64|
            #[trigger] ack_contains(a, pn) ==> c.recv(d.packets[i].kind).seen().contains(pn))
    // P9.
    &&& forall|i: int, j: int|
        0 <= i < d.packets.len() && 0 <= j < d.packets[i].frames.len() && #[trigger] d.packets[i].frames[j]
            is HandshakeDone ==> c.live(PacketKind::OneRtt)
}

/// A packet of `s` is in its space's packet number list.
proof fn lemma_pns_member(s: Seq<SpecOutPacket>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        packets_pns(s, s[i].kind).contains(s[i].pn),
    decreases s.len(),
{
    let k = s[i].kind;
    let q = s.drop_last();
    if i == s.len() - 1 {
        assert(packets_pns(s, k) == packets_pns(q, k).push(s[i].pn));
        assert(packets_pns(s, k).last() == s[i].pn);
    } else {
        lemma_pns_member(q, i);
        assert(q[i] == s[i]);
        let a = packets_pns(q, k);
        let j = choose|j: int| 0 <= j < a.len() && a[j] == s[i].pn;
        if s.last().kind == k {
            assert(packets_pns(s, k) == a.push(s.last().pn));
            assert(packets_pns(s, k)[j] == s[i].pn);
        }
    }
}

/// Every packet of a datagram `transmit_ok` accepts has a packet number below `PN_MAX`: P4
/// puts it below its space's `next_pn`, which `SentPackets::wf` bounds by `PN_MAX`.
proof fn lemma_transmit_pn_max(o: Connection, c: Connection, d: SpecOutDatagram)
    requires
        c.wf(),
        transmit_ok(o, c, d),
    ensures
        forall|i: int| 0 <= i < d.packets.len() ==> (#[trigger] d.packets[i]).pn < PN_MAX,
{
    assert forall|i: int| 0 <= i < d.packets.len() implies (#[trigger] d.packets[i]).pn < PN_MAX by {
        let k = d.packets[i].kind;
        lemma_pns_member(d.packets, i);
        match k {
            PacketKind::Initial => c.sent_i.lemma_wf(),
            PacketKind::Handshake => c.sent_h.lemma_wf(),
            PacketKind::OneRtt => c.sent_1.lemma_wf(),
        }
        let s = packets_pns(d.packets, k);
        assert(pns_ok(s, c.sent(k).next_pn_spec()));
        let j = choose|j: int| 0 <= j < s.len() && s[j] == d.packets[i].pn;
        assert(s[j] < c.sent(k).next_pn_spec());
    }
}

/// A datagram with an ack-eliciting Initial in it.
pub open spec fn has_eliciting_initial(s: Seq<SpecOutPacket>) -> bool {
    exists|i: int, j: int|
        0 <= i < s.len() && s[i].kind is Initial && 0 <= j < s[i].frames.len() && ack_eliciting(
            spec_frame_type(#[trigger] s[i].frames[j]),
        )
}

/// P2 (§14.1): an ack-eliciting Initial goes out in exactly 1200 bytes.
pub open spec fn initial_padded(d: SpecOutDatagram) -> bool {
    has_eliciting_initial(d.packets) ==> out_datagram_len(d) == 1200
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-12.2
//# Senders MUST NOT coalesce QUIC packets
//# with different connection IDs into a single UDP datagram.
/// P6: one Destination Connection ID in a datagram.
pub open spec fn same_dcid(d: SpecOutDatagram) -> bool {
    forall|i: int, j: int|
        0 <= i < d.packets.len() && 0 <= j < d.packets.len() ==> #[trigger] d.packets[i].dcid
            == #[trigger] d.packets[j].dcid
}

/// P3: only CONNECTION_CLOSE.
pub open spec fn only_close(d: SpecOutDatagram) -> bool {
    forall|i: int, j: int|
        0 <= i < d.packets.len() && 0 <= j < d.packets[i].frames.len() ==> #[trigger] d.packets[i].frames[j]
            is ConnectionClose
}

/// P17 (§14.2): what a path that cannot carry 1200 bytes may be sent: probes, in a 1200-byte
/// datagram if one answers the peer, and CONNECTION_CLOSE.
pub open spec fn mtu_failed_frames(d: SpecOutDatagram) -> bool {
    forall|i: int, j: int|
        0 <= i < d.packets.len() && 0 <= j < d.packets[i].frames.len() ==> {
            &&& #[trigger] d.packets[i].frames[j] is PathChallenge || d.packets[i].frames[j] is PathResponse
                || d.packets[i].frames[j] is Padding || d.packets[i].frames[j] is ConnectionClose
            &&& d.packets[i].frames[j] is PathResponse ==> out_datagram_len(d) == 1200
        }
}

/// `d`'s frames are all PATH_CHALLENGE or PATH_RESPONSE; its padding is not a frame here.
pub open spec fn only_path_frames(d: SpecOutDatagram) -> bool {
    forall|i: int, j: int|
        0 <= i < d.packets.len() && 0 <= j < d.packets[i].frames.len() ==> #[trigger] d.packets[i].frames[j]
            is PathResponse || d.packets[i].frames[j] is PathChallenge
}

/// `d` has at most one PATH_RESPONSE frame.
pub open spec fn one_response_at_most(d: SpecOutDatagram) -> bool {
    forall|i1: int, j1: int, i2: int, j2: int|
        0 <= i1 < d.packets.len() && 0 <= j1 < d.packets[i1].frames.len() && 0 <= i2 < d.packets.len() && 0 <= j2
            < d.packets[i2].frames.len() && #[trigger] d.packets[i1].frames[j1] is PathResponse
            && #[trigger] d.packets[i2].frames[j2] is PathResponse ==> i1 == i2 && j1 == j2
}

/// A PATH_CHALLENGE or PATH_RESPONSE in `d`.
pub open spec fn carries_path_frame(d: SpecOutDatagram) -> bool {
    exists|i: int, j: int|
        0 <= i < d.packets.len() && 0 <= j < d.packets[i].frames.len() && (#[trigger] d.packets[i].frames[j]
            is PathChallenge || d.packets[i].frames[j] is PathResponse)
}

/// P13 (§8.2.1, §8.2.2): such a datagram is 1200 bytes, unless the path's budget, `budget` before
/// this send, was under that.
pub open spec fn path_expanded(d: SpecOutDatagram, budget: u64) -> bool {
    carries_path_frame(d) ==> out_datagram_len(d) == 1200 || budget < 1200
}

/// P8: every frame in `polled` is in `d`.
pub open spec fn polled_placed(polled: Seq<SpecFrame>, d: SpecOutDatagram) -> bool {
    forall|i: int| 0 <= i < polled.len() ==> frame_in_datagram(d, #[trigger] polled[i])
}

pub open spec fn frame_in_datagram(d: SpecOutDatagram, f: SpecFrame) -> bool {
    exists|m: int, n: int|
        0 <= m < d.packets.len() && 0 <= n < d.packets[m].frames.len() && #[trigger] d.packets[m].frames[n] == f
}

spec fn polled_in_packet(polled: Seq<SpecFrame>, p: SpecOutPacket) -> bool {
    in_tail(polled, p.frames, 0)
}

/// `n` is `pn_encode_len`'s answer.
spec fn min_pn_len(pn: u64, la: Option<u64>, n: nat) -> bool {
    &&& pn_len_ok(pn, la, n)
    &&& forall|m: nat| 1 <= m < n ==> !pn_len_ok(pn, la, m)
}

/// The frames so far: sendable in space `k`, ack-eliciting from `base` on, and with `left` bytes
/// still within `room`.
spec fn tx_frames(sf: Seq<SpecFrame>, k: PacketKind, base: int, left: nat, room: nat) -> bool {
    &&& 0 <= base <= sf.len()
    &&& frames_sendable(sf, k)
    &&& no_path_frames(sf)
    &&& forall|i: int| base <= i < sf.len() ==> ack_eliciting(spec_frame_type(#[trigger] sf[i]))
    &&& spec_frames_bytes(sf).len() + left <= room
}

/// No PATH_CHALLENGE or PATH_RESPONSE: `build_path_datagram` is their only sender.
spec fn no_path_frames(sf: Seq<SpecFrame>) -> bool {
    forall|i: int| 0 <= i < sf.len() ==> !(#[trigger] sf[i] is PathChallenge) && !(sf[i] is PathResponse)
}

spec fn extends(a: Seq<SpecFrame>, b: Seq<SpecFrame>) -> bool {
    &&& a.len() <= b.len()
    &&& forall|i: int| 0 <= i < a.len() ==> #[trigger] b[i] == a[i]
}

/// `f` is in `sf`, from `base` on.
spec fn frame_from(sf: Seq<SpecFrame>, f: SpecFrame, base: int) -> bool {
    exists|j: int| base <= j < sf.len() && #[trigger] sf[j] == f
}

spec fn in_tail(polled: Seq<SpecFrame>, sf: Seq<SpecFrame>, base: int) -> bool {
    forall|i: int| 0 <= i < polled.len() ==> frame_from(sf, #[trigger] polled[i], base)
}

/// `a` is the frame for every range `r` remembers, and reports only what it has seen.
spec fn ack_full(a: SpecAck, r: RecvPns) -> bool {
    &&& a.ranges.len() + 1 == r.range_count()
    &&& exists|d: u64| a == #[trigger] r.ack_candidate(a.ranges.len() as nat, d)
    &&& forall|pn: u64| #[trigger] ack_contains(a, pn) ==> r.seen().contains(pn)
}

/// An ACK comes first and only first, and is `ack_full`.
spec fn ack_ok(sf: Seq<SpecFrame>, r: RecvPns) -> bool {
    forall|i: int|
        0 <= i < sf.len() ==> (#[trigger] sf[i] matches SpecFrame::Ack(a) ==> i == 0 && ack_full(a, r))
}

/// `s` is `pns_ok`, and above everything in `log`.
pub open spec fn pns_fresh(log: Seq<u64>, s: Seq<u64>, next: u64) -> bool {
    &&& pns_ok(s, next)
    &&& forall|i: int, j: int| 0 <= i < log.len() && 0 <= j < s.len() ==> #[trigger] log[i] < #[trigger] s[j]
}

/// `RecvPns::ack_deadline`'s ensures as a test: an ACK-only packet may go, and its ACK is due.
spec fn ack_is_due(r: RecvPns, max_ack_delay_us: u64, now: u64) -> bool {
    &&& r.ack_only_allowed()
    &&& r.eliciting_since_ack() > 0
    &&& now >= match r.kind_spec() {
        PacketKind::OneRtt => if r.eliciting_since_ack() >= 2 || r.ack_blocked() {
            r.first_unacked()->0 as int
        } else if r.first_unacked()->0 + max_ack_delay_us > u64::MAX {
            u64::MAX as int
        } else {
            r.first_unacked()->0 + max_ack_delay_us
        },
        _ => r.first_unacked()->0 as int,
    }
}

/// Every retransmittable frame of `frames` is in the record's `rec`.
spec fn records(rec: Seq<SpecFrame>, frames: Seq<SpecFrame>) -> bool {
    forall|j: int| 0 <= j < frames.len() && retransmittable(#[trigger] frames[j]) ==> frame_from(rec, frames[j], 0)
}

/// `s` is `o` with one record pushed: `p`'s, holding its retransmittable frames.
spec fn recorded(o: Seq<SentPacket>, s: Seq<SentPacket>, p: SpecOutPacket) -> bool {
    &&& s.len() == o.len() + 1
    &&& s.drop_last() == o
    &&& s.last().pn == p.pn
    &&& records(s.last()@.frames, p.frames)
}

/// `record_frames`' second ensures, in `records`' terms.
proof fn lemma_record_holds(frames: Seq<Frame>, rec: Seq<Frame>)
    requires
        forall|j: int|
            0 <= j < frames.len() && retransmittable(#[trigger] frames[j]@) ==> frame_from(
                frames_view(rec),
                frames[j]@,
                0,
            ),
    ensures
        records(frames_view(rec), frames_view(frames)),
{
    let v = frames_view(frames);
    assert forall|j: int| 0 <= j < v.len() && retransmittable(#[trigger] v[j]) implies frame_from(
        frames_view(rec),
        v[j],
        0,
    ) by {
        assert(v[j] == frames[j]@);
    }
}

/// A record keeps these (3d D5).
pub open spec fn retransmittable(f: SpecFrame) -> bool {
    !(f is Padding || f is Ping || f is Ack || f is ConnectionClose || f is PathChallenge
        || f is PathResponse)
}

/// The room arithmetic: a packet whose frames fit `room`, with sample padding, against `hdr` bytes
/// of header (`header_bytes_spec`, whose 2-byte Length bounds the real one).
proof fn lemma_room(p: SpecOutPacket, room: nat, hdr: nat)
    requires
        out_packet_sized(p),
        frames_len(p) <= room,
        p.padding <= 3,
        hdr == match p.kind {
            PacketKind::OneRtt => 1 + p.dcid.len(),
            PacketKind::Initial => 7 + p.dcid.len() + p.scid.len() + 1 + 2,
            PacketKind::Handshake => 7 + p.dcid.len() + p.scid.len() + 2,
        },
    ensures
        out_packet_len(p) <= room + hdr + p.pn_len + AEAD_TAG_LEN + 3,
{
}

proof fn lemma_tx_push(sf: Seq<SpecFrame>, f: SpecFrame, k: PacketKind, base: int, left: nat, room: nat, left2: nat)
    requires
        tx_frames(sf, k, base, left, room),
        frame_wf(f),
        frame_permitted(spec_frame_type(f), k),
        ack_eliciting(spec_frame_type(f)),
        !(f is PathChallenge) && !(f is PathResponse),
        left2 + spec_frame_bytes(f).len() <= left,
    ensures
        tx_frames(sf.push(f), k, base, left2, room),
        extends(sf, sf.push(f)),
{
    lemma_frames_bytes_push(sf, f);
    let s2 = sf.push(f);
    assert forall|i: int| 0 <= i < s2.len() implies frame_wf(#[trigger] s2[i]) && frame_permitted(
        spec_frame_type(s2[i]),
        k,
    ) by {
        if i < sf.len() {
            assert(s2[i] == sf[i]);
        }
    }
    assert forall|i: int| 0 <= i < s2.len() implies !(#[trigger] s2[i] is PathChallenge) && !(s2[i] is PathResponse) by {
        if i < sf.len() {
            assert(s2[i] == sf[i]);
        }
    }
    assert forall|i: int| base <= i < s2.len() implies ack_eliciting(spec_frame_type(#[trigger] s2[i])) by {
        if i < sf.len() {
            assert(s2[i] == sf[i]);
        }
    }
}

proof fn lemma_frames_bytes_append(a: Seq<SpecFrame>, b: Seq<SpecFrame>)
    ensures
        spec_frames_bytes(a + b).len() == spec_frames_bytes(a).len() + spec_frames_bytes(b).len(),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        let l = b.last();
        let d = b.drop_last();
        assert(a + b =~= (a + d).push(l));
        assert(b =~= d.push(l));
        lemma_frames_bytes_push(a + d, l);
        lemma_frames_bytes_push(d, l);
        lemma_frames_bytes_append(a, d);
    }
}

/// A frame `poll_frames` returned elicits an ACK.
proof fn lemma_polled_eliciting(s: Streams, f: SpecFrame)
    requires
        polled_rule(s, f),
    ensures
        ack_eliciting(spec_frame_type(f)),
{
    if let SpecFrame::Stream { offset, fin, .. } = f {
        lemma_stream_type_bits(if offset > 0 { 4 } else { 0 }, if fin { 1 } else { 0 });
    }
}

/// `tx_frames` after `poll_frames`, which appended `out1.skip(out0.len())`.
proof fn lemma_polled(s0: Streams, out0: Seq<Frame>, out1: Seq<Frame>, base: int, left: nat, room: nat)
    requires
        tx_frames(frames_view(out0), PacketKind::OneRtt, base, left, room),
        ({
            let new = out1.skip(out0.len() as int);
            &&& out1.len() >= out0.len()
            &&& out1.subrange(0, out0.len() as int) == out0
            &&& frames_sendable(frames_view(new), PacketKind::OneRtt)
            &&& spec_frames_bytes(frames_view(new)).len() <= left
            &&& forall|k: int| 0 <= k < new.len() ==> polled_rule(s0, (#[trigger] new[k])@)
        }),
    ensures
        tx_frames(frames_view(out1), PacketKind::OneRtt, base, 0, room),
        extends(frames_view(out0), frames_view(out1)),
        out1.len() == out0.len() ==> out1 == out0,
{
    let n = out0.len() as int;
    let new = out1.skip(n);
    let v0 = frames_view(out0);
    let v1 = frames_view(out1);
    let vn = frames_view(new);
    assert(out1 =~= out0 + new) by {
        assert forall|i: int| 0 <= i < n implies out1[i] == out0[i] by {
            assert(out1.subrange(0, n)[i] == out1[i]);
        }
    }
    assert(v1 =~= v0 + vn);
    lemma_frames_bytes_append(v0, vn);
    assert forall|i: int| 0 <= i < v1.len() implies frame_wf(#[trigger] v1[i]) && frame_permitted(
        spec_frame_type(v1[i]),
        PacketKind::OneRtt,
    ) by {
        if i < n {
            assert(v1[i] == v0[i]);
        } else {
            assert(v1[i] == vn[i - n]);
        }
    }
    assert forall|i: int| 0 <= i < v1.len() implies !(#[trigger] v1[i] is PathChallenge) && !(v1[i] is PathResponse) by {
        if i < n {
            assert(v1[i] == v0[i]);
        } else {
            assert(v1[i] == vn[i - n]);
            assert(polled_rule(s0, new[i - n]@));
        }
    }
    assert forall|i: int| base <= i < v1.len() implies ack_eliciting(spec_frame_type(#[trigger] v1[i])) by {
        if i < n {
            assert(v1[i] == v0[i]);
        } else {
            assert(v1[i] == vn[i - n]);
            assert(polled_rule(s0, new[i - n]@));
            lemma_polled_eliciting(s0, v1[i]);
        }
    }
    assert forall|i: int| 0 <= i < v0.len() implies #[trigger] v1[i] == v0[i] by {}
}

proof fn lemma_in_tail(sf: Seq<SpecFrame>, mid: int, base: int)
    requires
        0 <= mid,
        base <= mid <= sf.len(),
    ensures
        in_tail(sf.skip(mid), sf, base),
{
    let t = sf.skip(mid);
    assert forall|i: int| 0 <= i < t.len() implies frame_from(sf, #[trigger] t[i], base) by {
        assert(sf[mid + i] == t[i]);
    }
}

/// With nothing past `n`, nothing was polled.
proof fn lemma_polled_empty(polled: Seq<SpecFrame>, sf: Seq<SpecFrame>, n: int)
    requires
        in_tail(polled, sf, n),
    ensures
        sf.len() as int <= n ==> polled.len() == 0,
{
    if sf.len() as int <= n && polled.len() > 0 {
        let _ = polled[0];
    }
}

/// `is_ack_eliciting`'s answer, for frames with an ACK before `n` and only ack-eliciting ones after.
proof fn lemma_eliciting(fs: Seq<Frame>, n: int)
    requires
        0 <= n <= fs.len(),
        forall|i: int| 0 <= i < n ==> !ack_eliciting(spec_frame_type(#[trigger] frames_view(fs)[i])),
        forall|i: int| n <= i < fs.len() ==> ack_eliciting(spec_frame_type(#[trigger] frames_view(fs)[i])),
    ensures
        (exists|i: int| 0 <= i < fs.len() && ack_eliciting(spec_frame_type(#[trigger] fs[i]@))) == (fs.len() > n),
        (exists|i: int|
            0 <= i < frames_view(fs).len() && ack_eliciting(spec_frame_type(#[trigger] frames_view(fs)[i])))
            == (fs.len() > n),
{
    let v = frames_view(fs);
    if fs.len() > n {
        assert(v[n] == fs[n]@);
        assert(ack_eliciting(spec_frame_type(fs[n]@)));
        assert(ack_eliciting(spec_frame_type(v[n])));
    } else {
        assert forall|i: int| 0 <= i < fs.len() implies !ack_eliciting(spec_frame_type(#[trigger] fs[i]@)) by {
            assert(v[i] == fs[i]@);
        }
    }
}

proof fn lemma_ack_ok_extends(a: Seq<SpecFrame>, b: Seq<SpecFrame>, r: RecvPns, k: PacketKind, room: nat)
    requires
        ack_ok(a, r),
        extends(a, b),
        tx_frames(b, k, a.len() as int, 0, room),
    ensures
        ack_ok(b, r),
{
    assert forall|i: int| 0 <= i < b.len() implies (#[trigger] b[i] matches SpecFrame::Ack(x) ==> i == 0
        && ack_full(x, r)) by {
        if i >= a.len() {
            assert(ack_eliciting(spec_frame_type(b[i])));
        } else {
            assert(b[i] == a[i]);
        }
    }
}

/// §13.2.1: the full frame reports every ack-eliciting packet number not yet reported.
proof fn lemma_ack_reports(a: SpecAck, r: RecvPns)
    requires
        r.wf(),
        ack_full(a, r),
    ensures
        forall|u: u64| #[trigger] r.unreported().contains(u) ==> ack_contains(a, u),
{
    assert forall|u: u64| #[trigger] r.unreported().contains(u) implies ack_contains(a, u) by {
        let d = choose|d: u64| a == #[trigger] r.ack_candidate(a.ranges.len() as nat, d);
        r.lemma_unreported_acked(u, d);
        assert((r.range_count() - 1) as nat == a.ranges.len() as nat);
    }
}

/// A CONNECTION_CLOSE's bytes, at most: a 64-byte reason under `lemma_close_len`.
#[allow(dead_code)]
const CLOSE_FRAME_MAX: usize = 83;

/// A close's packet, at most: `CLOSE_FRAME_MAX`, a 40-byte header and 4-byte number, and what `lemma_room`
/// adds. Two of them fit `MAX_DATAGRAM`.
#[allow(dead_code)]
const CLOSE_PACKET_MAX: usize = 146;

/// A datagram of nothing but CONNECTION_CLOSE passes P2 and P17.
proof fn lemma_only_close(d: SpecOutDatagram)
    requires
        only_close(d),
    ensures
        initial_padded(d),
        mtu_failed_frames(d),
{
    if has_eliciting_initial(d.packets) {
        let (a, b) = choose|a: int, b: int|
            0 <= a < d.packets.len() && d.packets[a].kind is Initial && 0 <= b < d.packets[a].frames.len()
                && ack_eliciting(spec_frame_type(#[trigger] d.packets[a].frames[b]));
        assert(d.packets[a].frames[b] is ConnectionClose);
    }
    assert forall|i: int, j: int| 0 <= i < d.packets.len() && 0 <= j < d.packets[i].frames.len() implies {
        &&& #[trigger] d.packets[i].frames[j] is PathChallenge || d.packets[i].frames[j] is PathResponse
            || d.packets[i].frames[j] is Padding || d.packets[i].frames[j] is ConnectionClose
        &&& d.packets[i].frames[j] is PathResponse ==> out_datagram_len(d) == 1200
    } by {
        assert(d.packets[i].frames[j] is ConnectionClose);
    }
}

/// `pns_ok`, and nothing below `low`.
spec fn pns_built(s: Seq<u64>, low: u64, next: u64) -> bool {
    &&& pns_ok(s, next)
    &&& forall|i: int| 0 <= i < s.len() ==> low <= #[trigger] s[i]
}

/// Padding changes no packet number.
proof fn lemma_pns_padded(s: Seq<SpecOutPacket>, i: int, x: nat, k: PacketKind)
    requires
        0 <= i < s.len(),
    ensures
        packets_pns(s.update(i, padded(s[i], x)), k) == packets_pns(s, k),
    decreases s.len(),
{
    let u = s.update(i, padded(s[i], x));
    if i == s.len() - 1 {
        assert(u.drop_last() =~= s.drop_last());
    } else {
        assert(u.drop_last() =~= s.drop_last().update(i, padded(s[i], x)));
        assert(s.drop_last()[i] == s[i]);
        lemma_pns_padded(s.drop_last(), i, x, k);
    }
}

/// `spec_frame_bytes` of a CONNECTION_CLOSE with a reason of at most 64 bytes.
proof fn lemma_close_len(f: SpecFrame)
    requires
        frame_wf(f),
        f matches SpecFrame::ConnectionClose { reason, .. } && reason.len() <= 64,
    ensures
        spec_frame_bytes(f).len() <= CLOSE_FRAME_MAX,
{
    if let SpecFrame::ConnectionClose { app, error_code, frame_type, reason } = f {
        theorem_serialize_matches_rfc(spec_frame_type(f));
        theorem_serialize_matches_rfc(error_code);
        theorem_serialize_matches_rfc(frame_type);
        theorem_serialize_matches_rfc(reason.len() as u64);
    }
}

proof fn lemma_not_inflight(s: SentPackets)
    requires
        s.wf(),
    ensures
        !has_pn(s.inflight_spec(), s.next_pn_spec()),
{
    s.lemma_wf();
    if has_pn(s.inflight_spec(), s.next_pn_spec()) {
        let i = choose|i: int| 0 <= i < s.inflight_spec().len() && (#[trigger] s.inflight_spec()[i]).pn == s.next_pn_spec();
        assert(s.inflight_spec()[i].pn < s.next_pn_spec());
    }
}

/// `log + d` is still `pns_ok`, for `d` above everything logged.
proof fn lemma_pn_step(log: Seq<SpecOutDatagram>, d: SpecOutDatagram, k: PacketKind, next: u64)
    requires
        pns_ok(log_pns(log, k), next),
        pns_fresh(log_pns(log, k), packets_pns(d.packets, k), next),
    ensures
        pns_ok(log_pns(log.push(d), k), next),
{
    let l = log.push(d);
    assert(l.drop_last() =~= log);
    assert(l.last() == d);
    let a = log_pns(log, k);
    let b = packets_pns(d.packets, k);
    let c = a + b;
    assert(log_pns(l, k) == c);
    assert forall|i: int, j: int| 0 <= i < j < c.len() implies #[trigger] c[i] < #[trigger] c[j] by {
        if j < a.len() {
            assert(c[i] == a[i] && c[j] == a[j]);
        } else if i < a.len() {
            assert(c[i] == a[i] && c[j] == b[j - a.len()]);
        } else {
            assert(c[i] == b[i - a.len()] && c[j] == b[j - a.len()]);
        }
    }
    assert forall|i: int| 0 <= i < c.len() implies #[trigger] c[i] < next by {
        if i < a.len() {
            assert(c[i] == a[i]);
        } else {
            assert(c[i] == b[i - a.len()]);
        }
    }
}

/// Copies a retransmittable frame; None for any other.
#[verifier::spinoff_prover]
fn copy_frame(f: &Frame) -> (r: Option<Frame>)
    ensures
        (r is Some) == retransmittable(f@),
        r matches Some(c) ==> c@ == f@,
{
    match f {
        Frame::Padding | Frame::Ping | Frame::Ack(_) | Frame::ConnectionClose { .. }
        | Frame::PathChallenge(_) | Frame::PathResponse(_) => None,
        Frame::ResetStream { stream_id, error_code, final_size } => Some(
            Frame::ResetStream { stream_id: *stream_id, error_code: *error_code, final_size: *final_size },
        ),
        Frame::StopSending { stream_id, error_code } => Some(
            Frame::StopSending { stream_id: *stream_id, error_code: *error_code },
        ),
        Frame::Crypto { offset, data } => Some(
            Frame::Crypto { offset: *offset, data: slice_to_vec(data.as_slice()) },
        ),
        Frame::Stream { stream_id, offset, data, fin } => Some(
            Frame::Stream { stream_id: *stream_id, offset: *offset, data: slice_to_vec(data.as_slice()), fin: *fin },
        ),
        Frame::MaxData(v) => Some(Frame::MaxData(*v)),
        Frame::MaxStreamData { stream_id, max } => Some(
            Frame::MaxStreamData { stream_id: *stream_id, max: *max },
        ),
        Frame::MaxStreams { bidi, max } => Some(Frame::MaxStreams { bidi: *bidi, max: *max }),
        Frame::DataBlocked(v) => Some(Frame::DataBlocked(*v)),
        Frame::StreamDataBlocked { stream_id, max } => Some(
            Frame::StreamDataBlocked { stream_id: *stream_id, max: *max },
        ),
        Frame::StreamsBlocked { bidi, max } => Some(Frame::StreamsBlocked { bidi: *bidi, max: *max }),
        Frame::NewConnectionId { seq, retire_prior_to, cid, reset_token } => Some(
            Frame::NewConnectionId {
                seq: *seq,
                retire_prior_to: *retire_prior_to,
                cid: slice_to_vec(cid.as_slice()),
                reset_token: *reset_token,
            },
        ),
        Frame::RetireConnectionId(v) => Some(Frame::RetireConnectionId(*v)),
        Frame::HandshakeDone => Some(Frame::HandshakeDone),
    }
}

/// The retransmittable frames of `frames`, for a record. The copy is one packet's bytes.
#[verifier::spinoff_prover]
fn record_frames(frames: &[Frame]) -> (r: Vec<Frame>)
    ensures
        forall|i: int|
            0 <= i < r@.len() ==> retransmittable(#[trigger] r@[i]@) && frame_from(
                frames_view(frames@),
                r@[i]@,
                0,
            ),
        forall|j: int|
            0 <= j < frames@.len() && retransmittable(#[trigger] frames@[j]@) ==> frame_from(
                frames_view(r@),
                frames@[j]@,
                0,
            ),
{
    let ghost fv = frames_view(frames@);
    let mut r: Vec<Frame> = Vec::new();
    let mut j: usize = 0;
    while j < frames.len()
        invariant
            j <= frames@.len(),
            fv == frames_view(frames@),
            forall|i: int|
                0 <= i < r@.len() ==> retransmittable(#[trigger] r@[i]@) && frame_from(fv, r@[i]@, 0),
            forall|m: int|
                0 <= m < j && retransmittable(#[trigger] frames@[m]@) ==> frame_from(
                    frames_view(r@),
                    frames@[m]@,
                    0,
                ),
        decreases frames@.len() - j,
    {
        if let Some(c) = copy_frame(&frames[j]) {
            let ghost r0 = r@;
            r.push(c);
            proof {
                let n = r0.len() as int;
                let v = frames_view(r@);
                assert(fv[j as int] == frames@[j as int]@);
                assert(v[n] == frames@[j as int]@);
                assert forall|i: int| 0 <= i < r@.len() implies retransmittable(#[trigger] r@[i]@) && frame_from(
                    fv,
                    r@[i]@,
                    0,
                ) by {
                    if i < n {
                        assert(r@[i] == r0[i]);
                    }
                }
                assert forall|m: int| 0 <= m < j + 1 && retransmittable(#[trigger] frames@[m]@) implies frame_from(
                    v,
                    frames@[m]@,
                    0,
                ) by {
                    if m < j {
                        let w = choose|w: int| 0 <= w < frames_view(r0).len() && #[trigger] frames_view(r0)[w] == frames@[m]@;
                        assert(v[w] == r0[w]@);
                        assert(frames_view(r0)[w] == r0[w]@);
                    }
                }
            }
        }
        j += 1;
    }
    r
}

// ponytail: measures a frame by serializing it into a scratch buffer, one small frame per call; a per-variant frame_len if 3e profiles this as hot.
/// The frame's encoded length.
fn frame_len(f: &Frame) -> (n: usize)
    requires
        frame_wf(f@),
    ensures
        n == spec_frame_bytes(f@).len(),
{
    let mut buf: Vec<u8> = Vec::new();
    serialize_frame(f, &mut buf);
    assert(buf@ =~= spec_frame_bytes(f@));
    buf.len()
}

/// Appends `f` if its encoding fits.
#[verifier::spinoff_prover]
fn try_place(
    f: Frame,
    left: &mut usize,
    fs: &mut Vec<Frame>,
    Ghost(k): Ghost<PacketKind>,
    Ghost(base): Ghost<int>,
    Ghost(room): Ghost<nat>,
) -> (placed: bool)
    requires
        tx_frames(frames_view(old(fs)@), k, base, *old(left) as nat, room),
        frame_wf(f@),
        frame_permitted(spec_frame_type(f@), k),
        ack_eliciting(spec_frame_type(f@)),
        !(f@ is PathChallenge) && !(f@ is PathResponse),
    ensures
        tx_frames(frames_view(final(fs)@), k, base, *final(left) as nat, room),
        extends(frames_view(old(fs)@), frames_view(final(fs)@)),
        !placed ==> final(fs)@ == old(fs)@ && *final(left) == *old(left),
        placed ==> final(fs)@.len() == old(fs)@.len() + 1 && final(fs)@.last()@ == f@,
{
    let n = frame_len(&f);
    if n > *left {
        return false;
    }
    let ghost sf = frames_view(fs@);
    let ghost left0 = *left as nat;
    let ghost g = f@;
    fs.push(f);
    *left = *left - n;
    proof {
        assert(frames_view(fs@) =~= sf.push(g));
        lemma_tx_push(sf, g, k, base, left0, room, *left as nat);
    }
    true
}

/// A datagram of the one packet `p`.
proof fn lemma_one_packet(p: SpecOutPacket, k: PacketKind)
    ensures
        packets_len(seq![p]) == out_packet_len(p),
        packets_pns(seq![p], k) == if k == p.kind {
            seq![p.pn]
        } else {
            Seq::<u64>::empty()
        },
{
    let s = seq![p];
    assert(s.drop_last() =~= Seq::<SpecOutPacket>::empty());
    assert(s.last() == p);
    assert(packets_len(s.drop_last()) == 0);
    assert(packets_pns(s.drop_last(), k) == Seq::<u64>::empty());
    assert(Seq::<u64>::empty().push(p.pn) =~= seq![p.pn]);
}

/// The frames owed on a path, in the order they go: its oldest response, then its owed challenge.
spec fn path_frames_of(a: SpecPath) -> Seq<SpecFrame> {
    (if a.responses.len() > 0 {
        seq![SpecFrame::PathResponse(a.responses[0]@)]
    } else {
        Seq::empty()
    }) + (if a.owed {
        seq![SpecFrame::PathChallenge(a.challenge.unwrap().0@)]
    } else {
        Seq::empty()
    })
}

/// `path_frames_of`, read frame by frame.
proof fn lemma_path_frames_of(a: SpecPath)
    ensures
        forall|j: int|
            0 <= j < path_frames_of(a).len() ==> (#[trigger] path_frames_of(a)[j] matches SpecFrame::PathResponse(x)
                ==> j == 0 && a.responses.len() > 0 && x == a.responses[0]@),
        forall|j: int|
            0 <= j < path_frames_of(a).len() ==> (#[trigger] path_frames_of(a)[j] matches SpecFrame::PathChallenge(y)
                ==> a.owed && y == a.challenge.unwrap().0@),
{
    let f = path_frames_of(a);
    if a.responses.len() > 0 && a.owed {
        assert(f[0] == SpecFrame::PathResponse(a.responses[0]@));
        assert(f[1] == SpecFrame::PathChallenge(a.challenge.unwrap().0@));
    } else if a.responses.len() > 0 {
        assert(f =~= seq![SpecFrame::PathResponse(a.responses[0]@)]);
    } else if a.owed {
        assert(f =~= seq![SpecFrame::PathChallenge(a.challenge.unwrap().0@)]);
    }
}

/// PATH frames only, 9 bytes each.
spec fn path_frames_ok(sf: Seq<SpecFrame>) -> bool {
    &&& frames_sendable(sf, PacketKind::OneRtt)
    &&& spec_frames_bytes(sf).len() == 9 * sf.len()
    &&& forall|j: int| 0 <= j < sf.len() ==> #[trigger] sf[j] is PathResponse || sf[j] is PathChallenge
}

proof fn lemma_path_frame_push(sf: Seq<SpecFrame>, f: SpecFrame)
    requires
        path_frames_ok(sf),
        f is PathChallenge || f is PathResponse,
        frame_wf(f),
    ensures
        path_frames_ok(sf.push(f)),
{
    lemma_frames_bytes_push(sf, f);
    lemma_path_frame_len(f);
    let s2 = sf.push(f);
    assert forall|j: int| 0 <= j < s2.len() implies frame_wf(#[trigger] s2[j]) && frame_permitted(
        spec_frame_type(s2[j]),
        PacketKind::OneRtt,
    ) && (s2[j] is PathResponse || s2[j] is PathChallenge) by {
        if j < sf.len() {
            assert(s2[j] == sf[j]);
        }
    }
}

/// A PATH_CHALLENGE or PATH_RESPONSE is 9 bytes.
proof fn lemma_path_frame_len(f: SpecFrame)
    requires
        frame_wf(f),
        f is PathChallenge || f is PathResponse,
    ensures
        spec_frame_bytes(f).len() == 9,
{
    theorem_serialize_matches_rfc(spec_frame_type(f));
}

/// `spec_frame_bytes` of a CRYPTO frame.
proof fn lemma_crypto_len(off: u64, d: Seq<u8>)
    requires
        off + d.len() <= VARINT_MAX,
    ensures
        spec_frame_bytes(SpecFrame::Crypto { offset: off, data: d }).len() == 1 + rfc_varint_min_len(off)
            + rfc_varint_min_len(d.len() as u64) + d.len(),
{
    theorem_serialize_matches_rfc(FRAME_CRYPTO);
    theorem_serialize_matches_rfc(off);
    theorem_serialize_matches_rfc(d.len() as u64);
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

    /// Test support: stream `id`'s acked and lost send-range counts (3d Task 1).
    #[doc(hidden)]
    pub fn send_range_counts(&self, id: u64) -> Option<(usize, usize)> {
        self.streams.as_ref().and_then(|s| s.send_range_counts(id))
    }

    /// Test support: the amplification budget of `q`, None when absent (the only reading of a
    /// path's receive count before `poll_transmit` exists).
    #[doc(hidden)]
    pub fn path_budget(&self, q: PathId) -> Option<u64> {
        self.paths.index(q).map(|_| self.paths.budget(q))
    }
}
