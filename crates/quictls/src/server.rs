//! The QUIC-TLS glue (RFC 9001 §4): `ServerHandshake` drives a `Connection` inside an `H3Server`.
//! After the pipeline hands a datagram's packets to the connection, the CRYPTO bytes of each level
//! go to TLS, and TLS's events go back in order: `Send` to the CRYPTO streams, `Secrets` to the
//! key slots, `PeerParams` to the connection's transport parameters, `Complete` to the handshake's
//! end, an error to CONNECTION_CLOSE. A key slot is emptied in the same call in which the
//! connection discards its space.
use vstd::prelude::*;

use crate::keys::*;
use h3::message::Response;
use quic::aead::*;
use quic::codes::{INTERNAL_ERROR, MAX_CID_LEN, PROTOCOL_VIOLATION, TRANSPORT_PARAMETER_ERROR};
#[allow(unused_imports)]
use quic::conn::*;
#[allow(unused_imports)]
use quic::datagram::*;
use quic::h3_server::*;
use quic::lifecycle::Phase;
use quic::payload::PacketKind;
use quic::pipeline::{accept_datagram, initial_dcid, refeed_one_rtt};
#[allow(unused_imports)]
use quic::protect::*;
use quic::route::CidUpdate;
use quic::tp::*;
use tls::codes::{CRYPTO_ERROR_BASE, TLS_RAND_LEN};
use tls::config::*;
use tls::flight::*;
#[allow(unused_imports)]
use tls::server::*;

verus! {

/// Fresh randomness for one `accept` or `receive`, filled by the shell: `conn` for the pipeline,
/// `refeed` for `refeed_one_rtt`, `complete` for `on_handshake_complete`, `tls` for `on_crypto`
/// (the ECDHE scalar and the PSS salt, so no derived `Debug`). No array goes to two `Connection`
/// calls, except in `accept`: `conn` goes through `accept_datagram` to both `Connection::accept`
/// and `Connection::on_datagram`, which draw disjoint parts of it (`accept` uses `[0..24]`; on the
/// accepting datagram `on_datagram` draws neither the PATH_CHALLENGE part nor the spin bit).
pub struct Rand {
    pub conn: [u8; RAND_LEN],
    pub refeed: [u8; RAND_LEN],
    pub complete: [u8; RAND_LEN],
    pub tls: [u8; TLS_RAND_LEN],
}

/// The glue's TLS calls, logged (ghost).
pub enum TlsCall {
    /// `on_crypto` was given bytes of `level` while TLS received at `current`.
    Fed { level: Level, current: Level },
    /// Keys above `lower` were installed with `unread` bytes left at `lower`.
    KeyChange { lower: Level, unread: nat },
}

pub open spec fn level_rank(l: Level) -> nat {
    match l {
        Level::Initial => 0,
        Level::Handshake => 1,
        Level::OneRtt => 2,
    }
}

//= https://www.rfc-editor.org/rfc/rfc9001#section-4.1.3
//# *  If the packet is from a previously installed encryption level, it
//# MUST NOT contain data that extends past the end of previously
//# received data in that flow.
//= https://www.rfc-editor.org/rfc/rfc9001#section-4.1.3
//# Implementations MUST treat any
//# violations of this requirement as a connection error of type
//# PROTOCOL_VIOLATION.
/// Some byte at or past `end` of level `k`'s CRYPTO stream arrived in a CRYPTO frame.
spec fn past_received(c: Connection, k: PacketKind, end: nat) -> bool {
    exists|p: nat| p >= end && #[trigger] c.crypto_received(k, p)
}

//= https://www.rfc-editor.org/rfc/rfc9001#section-4.1.3
//# *  If the packet is from a previously installed encryption level, it
//# MUST NOT contain data that extends past the end of previously
//# received data in that flow.
//= https://www.rfc-editor.org/rfc/rfc9001#section-4.1.3
//# Implementations MUST treat any
//# violations of this requirement as a connection error of type
//# PROTOCOL_VIOLATION.
/// `superseded`'s refusal: TLS has left Initial, and Initial CRYPTO data arrived at or past
/// `init_end`, the end of the Initial data received before the key change.
spec fn superseded_allowed_err(s: QuicServer) -> bool {
    !(s.level is Initial) && past_received(s.conn_spec(), PacketKind::Initial, s.init_end as nat)  // rfc-quantity: s.conn_spec(): the server's QUIC connection (QuicServer::conn_spec is h3.conn_spec()), whose CRYPTO receive history past_received reads: the flow of RFC 9001 §4.1.3
}

/// `superseded_allowed_err` is not vacuous: nothing received past `init_end`.
proof fn lemma_superseded_allowed_err_rejects(s: QuicServer)
    requires
        forall|p: nat| #[trigger] s.conn_spec().crypto_received(PacketKind::Initial, p) ==> p < s.init_end,
    ensures
        !superseded_allowed_err(s),
{
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-7.4
//# An endpoint MUST treat receipt of a transport parameter with an
//# invalid value as a connection error of type
//# TRANSPORT_PARAMETER_ERROR.
//= https://www.rfc-editor.org/rfc/rfc9000#section-7.3
//# An endpoint MUST treat the absence of the
//# initial_source_connection_id transport parameter from either endpoint
//# or the absence of the original_destination_connection_id transport
//# parameter from the server as a connection error of type
//# TRANSPORT_PARAMETER_ERROR.
//= https://www.rfc-editor.org/rfc/rfc9000#section-7.3
//# An endpoint MUST treat the following as a connection error of type
//# TRANSPORT_PARAMETER_ERROR or PROTOCOL_VIOLATION:
//= https://www.rfc-editor.org/rfc/rfc9000#section-7.3
//# a mismatch between values received from a peer in these transport
//# parameters and the value sent in the corresponding Destination or
//# Source Connection ID fields of Initial packets.
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2
//# Endpoints that receive a version 1 long header with a
//# value larger than 20 MUST drop the packet.
/// The client's transport parameters `b` are refusable on `c` with TRANSPORT_PARAMETER_ERROR: they
/// do not parse (`allowed_tp_err`), or their initial_source_connection_id is absent or not the
/// Source Connection ID of the client's first Initial. A parse error carries the §17.2 bound: `c`'s
/// ID is at most 20 bytes, so `allowed_tp_err`'s over-20 disjunct is a §7.3 mismatch
/// (`lemma_long_cid_mismatch`).
spec fn tp_allowed_err(c: Connection, b: Seq<u8>) -> bool {
    match rfc_transport_params(b, true) {
        Err(_) => allowed_tp_err(b) && c.client_scid_spec().len() <= MAX_CID_LEN,  // rfc-quantity: c.client_scid_spec(): the Source Connection ID field of the client's first Initial (RFC 9000 §7.3), tied by Connection::accept's ensures client_scid_spec() == first.scid@ (T5-M8' kills a re-anchor); its length bound <= 20 is §17.2's receiver rule via HandshakeIds::wf (Connection::client_scid_len)
        Ok(t) => t.initial_source_connection_id != Some(c.client_scid_spec()),  // rfc-quantity: c.client_scid_spec(): the Source Connection ID field of the client's first Initial (RFC 9000 §7.3), as on the Err arm
    }
}

/// The end of the Initial data `c` has received (RFC 9001 §4.1.3): every received byte is below
/// it, and the byte before it was received. `init_end` is set from it when TLS leaves Initial.
fn initial_end(c: &Connection) -> (r: u64)
    requires
        c.wf(),
    ensures
        r == c.crypto_end_spec(PacketKind::Initial),
        forall|p: nat| #[trigger] c.crypto_received(PacketKind::Initial, p) ==> p < r,
        r > 0 ==> c.crypto_received(PacketKind::Initial, (r - 1) as nat),
{
    c.crypto_end(PacketKind::Initial)
}

/// Under `tp_allowed_err`'s bound, a connection ID over 20 bytes is not the client's (§7.3 mismatch).
proof fn lemma_long_cid_mismatch(c: Connection, v: Seq<u8>)
    requires
        c.client_scid_spec().len() <= MAX_CID_LEN,
        v.len() > MAX_CID_LEN,
    ensures
        Some(v) != Some(c.client_scid_spec()),
{
}

/// `tp_allowed_err` is not vacuous: the client's own SCID as its initial_source_connection_id.
proof fn lemma_tp_allowed_err_rejects(c: Connection)
    requires
        c.client_scid_spec() == seq![0xabu8],
    ensures
        !tp_allowed_err(c, seq![0x0fu8, 0x01u8, 0xabu8]),
{
    lemma_allowed_tp_err_rejects();
}

fn rank(l: Level) -> (r: u8)
    ensures
        r == level_rank(l),
{
    match l {
        Level::Initial => 0,
        Level::Handshake => 1,
        Level::OneRtt => 2,
    }
}

/// The packet space of TLS level `l`.
pub open spec fn level_kind(l: Level) -> PacketKind {
    match l {
        Level::Initial => PacketKind::Initial,
        Level::Handshake => PacketKind::Handshake,
        Level::OneRtt => PacketKind::OneRtt,
    }
}

fn kind(l: Level) -> (k: PacketKind)
    ensures
        (k is OneRtt) == (l is OneRtt),
        k == level_kind(l),
{
    match l {
        Level::Initial => PacketKind::Initial,
        Level::Handshake => PacketKind::Handshake,
        Level::OneRtt => PacketKind::OneRtt,
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-16
//# This means that integers are encoded on 1, 2, 4, or 8 bytes and can
//# encode 6-, 14-, 30-, or 62-bit values, respectively.
//= https://www.rfc-editor.org/rfc/rfc9000#section-20.1
//# INTERNAL_ERROR (0x01):  The endpoint encountered an internal error
//# and cannot continue with the connection.
/// The close code `report` passes to the connection.
spec fn report_code(code: u64) -> u64 {
    if code <= 0x3fff_ffff_ffff_ffff { code } else { INTERNAL_ERROR }
}

/// `close` with no reason.
#[verifier::spinoff_prover]
fn shut(c: &mut Connection, code: u64, now: u64)
    requires
        old(c).wf(),
        code <= 0x3fff_ffff_ffff_ffff,
    ensures
        final(c).wf(),
        final(c).out_log() == old(c).out_log(),
        old(c).phase_spec() is Open ==> final(c).phase_spec() is Closing
            && final(c).close_spec() == Some((false, code, Seq::<u8>::empty())),
        !(old(c).phase_spec() is Open) ==> final(c).phase_spec() == old(c).phase_spec()
            && final(c).close_spec() == old(c).close_spec(),
        final(c).crypto_kept(*old(c)),
{
    let none: Vec<u8> = Vec::new();
    c.close(code, false, none.as_slice(), now);
    proof {
        c.lemma_keeps_crypto(*old(c));
    }
}

//= https://www.rfc-editor.org/rfc/rfc9001#section-4.8
//# A TLS alert is converted into a QUIC connection error.  The
//# AlertDescription value is added to 0x0100 to produce a QUIC error
//# code from the range reserved for CRYPTO_ERROR; see Section 20.1 of
//# [QUIC-TRANSPORT].  The resulting value is sent in a QUIC
//# CONNECTION_CLOSE frame of type 0x1c.
//= https://www.rfc-editor.org/rfc/rfc9001#section-4.8
//# As QUIC provides
//# alternative mechanisms for connection termination and the TLS
//# connection is only closed if an error is encountered, a QUIC endpoint
//# MUST treat any alert from TLS as if it were at the "fatal" level.
//= https://www.rfc-editor.org/rfc/rfc8446#section-6.2
//# Upon transmission or
//# receipt of a fatal alert message, both parties MUST immediately close
//# the connection.
//= https://www.rfc-editor.org/rfc/rfc8446#section-6.2
//# Whenever an implementation encounters a fatal error condition, it
//# SHOULD send an appropriate fatal alert and MUST close the connection
//# without sending or receiving any additional data.
//= https://www.rfc-editor.org/rfc/rfc8446#section-6.2
//# The phrases "terminate the connection with an X
//# alert" and "abort the handshake with an X alert" mean that the
//# implementation MUST send alert X if it sends any alert.
//= https://www.rfc-editor.org/rfc/rfc8446#section-6
//# Upon receiving an error alert, the TLS implementation
//# SHOULD indicate an error to the application and MUST NOT allow any
//# further data to be sent or received on the connection.
// Every TLS error is passed to a close, and the ensures pins its code: the alert as CRYPTO_ERROR_BASE + alert,
// which is how QUIC sends alert X; a transport code (0x0a, 0x0d) as it is; anything past VARINT_MAX as
// INTERNAL_ERROR. `tampered_finished_0x133`, `error_ranges` and `a2_closes_0x178` are regression checks.
// The closing state sends only CONNECTION_CLOSE (3d). The quoted sentence is about
// receiving an error alert, whose QUIC image is a peer CONNECTION_CLOSE: conn.rs enters draining,
// which sends and processes nothing (RFC 9000 §10.2.2). `on_crypto` also returns transport codes
// (0x0a, 0x0d), which close as they are.
//= https://www.rfc-editor.org/rfc/rfc8446#section-6
//= type=exception
//= reason=QUIC carries no TLS alert records (RFC 9001 §4.8): our alerts become CONNECTION_CLOSE codes, and the peer's close is a CONNECTION_CLOSE whatever its code.
//# All the alerts listed in Section 6.2 MUST be sent with
//# AlertLevel=fatal and MUST be treated as error alerts when received
//# regardless of the AlertLevel in the message.
//= https://www.rfc-editor.org/rfc/rfc8446#section-6
//= type=exception
//= reason=QUIC carries no TLS alert records (RFC 9001 §4.8): our alerts become CONNECTION_CLOSE codes, and the peer's close is a CONNECTION_CLOSE whatever its code.
//# Unknown Alert types
//# MUST be treated as error alerts.
/// TLS failed with `code`: close.
#[verifier::spinoff_prover]
fn report(c: &mut Connection, code: u64, now: u64)
    requires
        old(c).wf(),
    ensures
        final(c).wf(),
        final(c).out_log() == old(c).out_log(),
        old(c).phase_spec() is Open ==> final(c).phase_spec() is Closing
            && final(c).close_spec() == Some((false, report_code(code), Seq::<u8>::empty())),
        !(old(c).phase_spec() is Open) ==> final(c).phase_spec() == old(c).phase_spec()
            && final(c).close_spec() == old(c).close_spec(),
        final(c).crypto_kept(*old(c)),
{
    if CRYPTO_ERROR_BASE <= code && code <= CRYPTO_ERROR_BASE + 0xff {
        c.on_tls_alert((code - CRYPTO_ERROR_BASE) as u8, now);
    } else if code <= 0x3fff_ffff_ffff_ffff {
        shut(c, code, now);
    } else {
        shut(c, INTERNAL_ERROR, now);
    }
}

/// Whether `ev` holds `Secrets { Handshake }`, and whether it holds `Complete`.
spec fn spec_key_events(ev: Seq<SpecTlsEvent>) -> (bool, bool) {
    (
        exists|i: int| 0 <= i < ev.len() && #[trigger] spec_secrets_level(ev[i], Level::Handshake),
        exists|i: int| #![trigger ev[i]] 0 <= i < ev.len() && ev[i] is Complete,
    )
}

/// The CRYPTO bytes of level `l` handed to TLS so far.
spec fn tls_fed(s: QuicServer, l: Level) -> nat {
    match l {
        Level::Initial => s.fed_i as nat,
        Level::Handshake => s.fed_h as nat,
        Level::OneRtt => 0,
    }
}

/// RFC 9001 §4.1.3's "data from a previous encryption level that TLS has not consumed" at
/// level `l` (space `k`): bytes in TLS's reader, or bytes received at or past the end of what
/// was handed to TLS.
spec fn tls_unconsumed(s: QuicServer, l: Level, k: PacketKind) -> bool {
    spec_reader(s.hs@, l).len() > 0 || past_received(s.conn_spec(), k, tls_fed(s, l))  // rfc-quantity: s.conn_spec(): the server's QUIC connection (QuicServer::conn_spec is h3.conn_spec()), whose CRYPTO receive history past_received reads: the flow of RFC 9001 §4.1.3
}

//= https://www.rfc-editor.org/rfc/rfc9001#section-4.1.3
//# When TLS
//# provides keys for a higher encryption level, if there is data from
//# a previous encryption level that TLS has not consumed, this MUST
//# be treated as a connection error of type PROTOCOL_VIOLATION.
/// `key_changes`' refusal: the batch `ev` gives keys above a level whose data TLS has not
/// consumed: Handshake keys (`Secrets { Handshake }`) above Initial, 1-RTT keys (`Complete`)
/// above Initial and Handshake.
spec fn key_changes_allowed_err(s: QuicServer, ev: Seq<SpecTlsEvent>) -> bool {
    ||| (spec_key_events(ev).0 || spec_key_events(ev).1) && tls_unconsumed(s, Level::Initial, PacketKind::Initial)
    ||| spec_key_events(ev).1 && tls_unconsumed(s, Level::Handshake, PacketKind::Handshake)
}

/// `tls_unconsumed` is not vacuous: an empty reader and nothing received past what TLS has.
proof fn lemma_tls_unconsumed_rejects(s: QuicServer, l: Level, k: PacketKind)
    requires
        spec_reader(s.hs@, l).len() == 0,
        forall|p: nat| #[trigger] s.conn_spec().crypto_received(k, p) ==> p < tls_fed(s, l),
    ensures
        !tls_unconsumed(s, l, k),
{
}

/// `key_changes_allowed_err` is not vacuous: whatever the batch, nothing unconsumed at either level.
proof fn lemma_key_changes_allowed_err_rejects(s: QuicServer, ev: Seq<SpecTlsEvent>)
    requires
        spec_reader(s.hs@, Level::Initial).len() == 0,
        spec_reader(s.hs@, Level::Handshake).len() == 0,
        forall|p: nat| #[trigger] s.conn_spec().crypto_received(PacketKind::Initial, p) ==> p < s.fed_i,
        forall|p: nat| #[trigger] s.conn_spec().crypto_received(PacketKind::Handshake, p) ==> p < s.fed_h,
    ensures
        !key_changes_allowed_err(s, ev),
{
    lemma_tls_unconsumed_rejects(s, Level::Initial, PacketKind::Initial);
    lemma_tls_unconsumed_rejects(s, Level::Handshake, PacketKind::Handshake);
}

fn key_events(ev: &Vec<TlsEvent>) -> (r: (bool, bool))
    ensures
        r == spec_key_events(ev.deep_view()),
{
    let mut hs = false;
    let mut done = false;
    let mut i: usize = 0;
    while i < ev.len()
        invariant
            i <= ev@.len(),
            hs == exists|j: int| 0 <= j < i && #[trigger] spec_secrets_level(ev.deep_view()[j], Level::Handshake),
            done == exists|j: int| #![trigger ev.deep_view()[j]] 0 <= j < i && ev.deep_view()[j] is Complete,
        decreases ev.len() - i,
    {
        let ghost dv = ev.deep_view();
        assert(dv[i as int] == ev@[i as int].deep_view());
        match &ev[i] {
            TlsEvent::Secrets { level: Level::Handshake, .. } => hs = true,
            TlsEvent::Complete => done = true,
            _ => {},
        }
        i += 1;
        proof {
            let k = i - 1;
            if spec_secrets_level(dv[k], Level::Handshake) {
                assert(0 <= k < i && spec_secrets_level(dv[k], Level::Handshake));
            }
            if dv[k] is Complete {
                assert(0 <= k < i && dv[k] is Complete);
            }
        }
    }
    proof {
        assert(i == ev.deep_view().len());
    }
    (hs, done)
}

/// From `o` to `c`: an open `c` was open in `o`, every level drained in `o` still is, and a
/// completed handshake stays completed.
spec fn fed_kept(c: Connection, o: Connection) -> bool {
    &&& c.phase_spec() is Open ==> o.phase_spec() is Open && drained_kept(c, o)
    &&& o.live(PacketKind::OneRtt) ==> c.live(PacketKind::OneRtt)
}

pub struct QuicServer<'a> {
    h3: H3Server,
    hs: ServerHandshake<'a>,
    keys: [Option<KeyPair>; 3],
    /// TLS's receive level: Initial; Handshake at `Secrets { Handshake }`; OneRtt at `Complete`.
    level: Level,
    /// `crypto_end(Initial)` when `level` left Initial (`on_secrets`, or `on_complete`).
    init_end: u64,
    /// The Initial and Handshake CRYPTO bytes handed to TLS (`on_crypto`) so far.
    fed_i: u64,
    fed_h: u64,
    /// The connection when `level` left Initial: `init_end` is the end of what it had received.
    #[allow(dead_code)]
    init_rx: Ghost<Connection>,
    /// Only `wf` and `tls_log()` read it, which a plain `cargo build` erases.
    #[allow(dead_code)]
    log: Ghost<Seq<TlsCall>>,
}

impl<'a> QuicServer<'a> {
    pub closed spec fn conn_spec(&self) -> Connection {
        self.h3.conn_spec()
    }

    pub closed spec fn keys_spec(&self) -> Seq<Option<SpecKeyPair>> {
        self.keys.deep_view()
    }

    pub closed spec fn tls_log(&self) -> Seq<TlsCall> {
        self.log@
    }

    pub closed spec fn level_spec(&self) -> Level {
        self.level
    }

    /// `wf` but the key slots.
    spec fn core_ok(&self) -> bool {
        &&& self.h3.wf()
        &&& self.h3.history_ok()
        &&& self.hs.wf()
        // §4.1.3: never fed a level TLS has left.
        &&& forall|i: int|
            0 <= i < self.log@.len() ==> (#[trigger] self.log@[i] matches TlsCall::Fed { level, current }
                ==> level_rank(level) >= level_rank(current))
        // §4.1.3: nothing unread at a key change.
        &&& forall|i: int|
            0 <= i < self.log@.len() ==> (#[trigger] self.log@[i] matches TlsCall::KeyChange { unread, .. }
                ==> unread == 0)
        // §4.1.3: what TLS had at Initial when it left is read, so `init_end` is the end of the
        // Initial data received before the key change.
        &&& !(self.level is Initial) ==> self.h3.conn_spec().crypto_base_spec(PacketKind::Initial) >= self.init_end
        // §4.1.3's "end of previously received data": `init_end` is the end of the Initial data the
        // connection had received when TLS left Initial (`init_rx`), no more and no less.
        &&& !(self.level is Initial) ==> forall|p: nat| #[trigger] self.init_rx@.crypto_received(PacketKind::Initial, p) ==> p < self.init_end
        &&& !(self.level is Initial) && self.init_end > 0 ==> self.init_rx@.crypto_received(PacketKind::Initial, (self.init_end - 1) as nat)
        // `init_rx` is this connection's past: what it had received at Initial, it still has.
        &&& !(self.level is Initial) ==> forall|p: nat| #[trigger] self.init_rx@.crypto_received(PacketKind::Initial, p)
            ==> self.h3.conn_spec().crypto_received(PacketKind::Initial, p)
        // TLS leaves Initial at `Secrets { Handshake }` (`on_secrets`) or, if a batch has `Complete`
        // without it, at `on_complete`; both record `init_end` and `init_rx`.
        &&& self.level is Initial ==> self.init_end == 0
        // TLS receives at OneRtt only once the connection has completed (`on_complete`).
        &&& self.level is OneRtt ==> self.h3.conn_spec().live(PacketKind::OneRtt)
        // The bytes handed to TLS are the stream's prefix up to the read offset: while open, a
        // live space's offset moves only in `crypto_read`, which hands TLS exactly the bytes it
        // passes (`feed`).
        &&& self.h3.conn_spec().phase_spec() is Open && self.h3.conn_spec().live(PacketKind::Initial)
            ==> self.h3.conn_spec().crypto_base_spec(PacketKind::Initial) == self.fed_i
        &&& self.h3.conn_spec().phase_spec() is Open && self.h3.conn_spec().live(PacketKind::Handshake)
            ==> self.h3.conn_spec().crypto_base_spec(PacketKind::Handshake) == self.fed_h
        &&& self.fed_i <= self.h3.conn_spec().crypto_end_spec(PacketKind::Initial)
        // §4.1.3, at the key change: `init_end` is what TLS had been handed at Initial.
        &&& !(self.level is Initial) ==> self.init_end == self.fed_i
        // The peer's transport parameters are known only once TLS has left its ClientHello phases
        // (Start, HrrSent): `PeerParams` comes only from a call leaving them (`theorem_event_discipline`).
        &&& self.h3.conn_spec().peer_tp_known_spec() ==> spec_rank(self.hs@.phase) <= 1
    }

    /// No discarded keys (RFC 9001 §4.9.1, §4.9.2).
    spec fn keys_ok(&self) -> bool {
        &&& self.keys@[0] is Some ==> self.h3.conn_spec().live(PacketKind::Initial)
        &&& self.keys@[1] is Some ==> self.h3.conn_spec().live(PacketKind::Handshake)
    }

    /// Before completion, a connection that is no longer open holds no 1-RTT key (RFC 8446 §6).
    pub closed spec fn one_rtt_forgotten(&self) -> bool {
        !self.h3.conn_spec().live(PacketKind::OneRtt) && !(self.h3.conn_spec().phase_spec() is Open)
            ==> self.keys@[2] is None
    }

    /// Drops the 1-RTT keys of a connection that closed before completion.
    #[verifier::spinoff_prover]
    fn forget_failed(&mut self)
        requires
            old(self).core_ok(),
        ensures
            final(self).core_ok(),
            final(self).one_rtt_forgotten(),
            final(self).h3 == old(self).h3,
            final(self).keys@[0] == old(self).keys@[0],
            final(self).keys@[1] == old(self).keys@[1],
    {
        if !self.h3.conn().is_live(PacketKind::OneRtt) && !matches!(self.h3.conn().phase(), Phase::Open) {
            self.keys[2] = None;
        }
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.core_ok()
        &&& self.keys_ok()
    }

    proof fn lemma_push(&self, c: TlsCall)
        requires
            self.core_ok(),
            c matches TlsCall::Fed { level, current } ==> level_rank(level) >= level_rank(current),
            c matches TlsCall::KeyChange { unread, .. } ==> unread == 0,
        ensures
            ({
                let s = QuicServer { log: Ghost(self.log@.push(c)), ..*self };
                s.core_ok()
            }),
    {
        let l = self.log@.push(c);
        assert forall|i: int| 0 <= i < l.len() implies (#[trigger] l[i] matches TlsCall::Fed { level, current }
            ==> level_rank(level) >= level_rank(current)) by {
            if i < self.log@.len() {
                assert(l[i] == self.log@[i]);
            }
        }
        assert forall|i: int| 0 <= i < l.len() implies (#[trigger] l[i] matches TlsCall::KeyChange { unread, .. }
            ==> unread == 0) by {
            if i < self.log@.len() {
                assert(l[i] == self.log@[i]);
            }
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9001#section-4.9.1
    //# Thus, a client MUST discard Initial keys when it first sends a
    //# Handshake packet and a server MUST discard Initial keys when it first
    //# successfully processes a Handshake packet.
    //= https://www.rfc-editor.org/rfc/rfc9001#section-4.9.1
    //# Endpoints MUST NOT send
    //# Initial packets after this point.
    //= https://www.rfc-editor.org/rfc/rfc9001#section-4.9.2
    //# An endpoint MUST discard its Handshake keys when the TLS handshake is
    //# confirmed (Section 4.1.2).
    // The connection discards the space (3d: Initial on the first Handshake packet, Handshake at
    // completion, when a server's handshake is confirmed); this empties its slot after every
    // connection call, so no packet is protected or opened with discarded keys, and an Initial
    // packet has no key once Initial is discarded. The client's half binds clients.
    /// Empties each key slot whose space the connection has discarded.
    #[verifier::spinoff_prover]
    fn sync_keys(&mut self)
        requires
            old(self).core_ok(),
        ensures
            final(self).wf(),
            final(self).h3 == old(self).h3,
            final(self).hs == old(self).hs,
            final(self).level == old(self).level,
            final(self).init_end == old(self).init_end,
            final(self).fed_i == old(self).fed_i,
            final(self).fed_h == old(self).fed_h,
            final(self).log == old(self).log,
            final(self).keys@[2] == old(self).keys@[2],
            final(self).keys@[0] == old(self).keys@[0] || final(self).keys@[0] is None,
            final(self).keys@[1] == old(self).keys@[1] || final(self).keys@[1] is None,
    {
        if !self.h3.conn().is_live(PacketKind::Initial) {
            self.keys[0] = None;
        }
        if !self.h3.conn().is_live(PacketKind::Handshake) {
            self.keys[1] = None;
        }
    }

    /// The connection for the client Initial `d`, with TLS run on its CRYPTO data.
    #[verifier::spinoff_prover]
    pub fn accept(
        cfg: &'a ServerConfig,
        d: &[u8],
        path: PathId,
        now: u64,
        r: &Rand,
        local_tp: &TransportParams,
        app: &mut Vec<AppEvent>,
    ) -> (s: Option<QuicServer<'a>>)
        requires
            cfg.wf(),
        ensures
            s matches Some(q) ==> q.wf() && q.one_rtt_forgotten(),
            app_grew(old(app)@, final(app)@),
            s matches Some(q) ==> crypto_all_drained(q.conn_spec()),
    {
        let dcid = match initial_dcid(d) {
            Some(x) => x,
            None => return None,
        };
        if dcid.len() > MAX_CID_LEN {
            return None;
        }
        let keys = [Some(initial_keys(dcid.as_slice())), None, None];
        // `accept_datagram` checks that the accepting packet's DCID is `dcid`: the connection's
        // odcid is the DCID these keys come from (Task 2).
        let c = match accept_datagram(d, path, now, &r.conn, local_tp, &keys) {
            Some(c) => c,
            None => return None,
        };
        let mut tp: Vec<u8> = Vec::new();
        serialize_server_params(c.local_params(), &mut tp);
        let ghost cs = c;
        let mut s = QuicServer {
            h3: H3Server::new(c),
            hs: ServerHandshake::new(cfg, tp),
            keys,
            level: Level::Initial,
            init_end: 0,
            fed_i: 0,
            fed_h: 0,
            init_rx: Ghost(cs),
            log: Ghost(Seq::empty()),
        };
        s.sync_keys();
        s.tls_step(now, r);
        let ghost c0 = s.h3.conn_spec();
        s.h3.pump(app);
        proof {
            Connection::lemma_crypto_kept_elim(s.h3.conn_spec(), c0);
            if s.h3.conn_spec().phase_spec() is Open {
                lemma_all_drained_kept(s.h3.conn_spec(), c0);
            }
        }
        s.drop_if_closed();
        s.forget_failed();
        s.sync_keys();
        Some(s)
    }

    /// A datagram for this connection: the pipeline, TLS, the coalesced 1-RTT packet once TLS
    /// completes on it, then HTTP/3.
    pub fn receive(&mut self, d: &[u8], path: PathId, now: u64, r: &Rand, app: &mut Vec<AppEvent>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).one_rtt_forgotten(),
            app_grew(old(app)@, final(app)@),
            // Drain after the datagram: every CRYPTO byte it delivered in order has gone to TLS, or
            // been dropped because the connection closed.
            crypto_all_drained(final(self).conn_spec()),
    {
        hide(spec_on_crypto);
        let was = self.h3.conn().handshake_complete();
        let ghost c0 = self.h3.conn_spec();
        quic::pipeline::receive(self.h3.conn_mut(), d, path, now, &r.conn, &self.keys);
        proof {
            Connection::lemma_crypto_kept_elim(self.h3.conn_spec(), c0);
        }
        self.sync_keys();
        self.tls_step(now, r);
        let ghost ct = self.h3.conn_spec();
        if !was && self.h3.conn().handshake_complete() {
            let ghost c1 = self.h3.conn_spec();
            // The same datagram and path as the first pass, with its own randomness: the first
            // pass's `on_datagram` reset the challenge slices it drew.
            refeed_one_rtt(self.h3.conn_mut(), d, path, now, &r.refeed, &self.keys);
            proof {
                Connection::lemma_crypto_kept_elim(self.h3.conn_spec(), c1);
            }
            self.sync_keys();
            // The refed packet's 1-RTT CRYPTO bytes go to TLS now, not at the next datagram: any
            // such byte is unexpected_message, a close TLS requires at once. `r.tls` is not drawn
            // on: whatever this feed hands TLS, its answer is the same under any other randomness.
            proof {
                let cfg = self.hs.cfg_view();
                let tp = self.hs.tp_view();
                assert forall|st: SpecServerHs, data: Seq<u8>, r2: Seq<u8>| data.len() > 0 implies spec_on_crypto(
                    cfg,
                    tp,
                    st,
                    Level::OneRtt,
                    data,
                    r.tls@,
                ) == #[trigger] spec_on_crypto(cfg, tp, st, Level::OneRtt, data, r2) by {
                    lemma_one_rtt_rand_free(cfg, tp, st, data, r.tls@, r2);
                }
            }
            let _ = self.feed(Level::OneRtt, now, r, true);
            proof {
                let c = self.h3.conn_spec();
                self.h3.lemma_conn_wf();
                Connection::lemma_dead_drained(c);
                assert(c.live(PacketKind::OneRtt));
                if c.phase_spec() is Open {
                    lemma_all_drained(c);
                }
            }
        }
        let ghost c2 = self.h3.conn_spec();
        // SETTINGS goes out once 1-RTT is live.
        self.h3.pump(app);
        proof {
            Connection::lemma_crypto_kept_elim(self.h3.conn_spec(), c2);
            if self.h3.conn_spec().phase_spec() is Open {
                lemma_all_drained_kept(self.h3.conn_spec(), c2);
            }
        }
        self.drop_if_closed();
        self.forget_failed();
        self.sync_keys();
    }

    /// A connection that is no longer open has its unread CRYPTO bytes dropped: TLS reads no more.
    #[verifier::spinoff_prover]
    fn drop_if_closed(&mut self)
        requires
            old(self).core_ok(),
            old(self).conn_spec().phase_spec() is Open ==> crypto_all_drained(old(self).conn_spec()),
        ensures
            final(self).core_ok(),
            crypto_all_drained(final(self).conn_spec()),
    {
        if matches!(self.h3.conn().phase(), Phase::Open) {
            return;
        }
        let ghost c0 = self.h3.conn_spec();
        self.h3.conn_mut().crypto_drop();
        proof {
            Connection::lemma_crypto_kept_elim(self.h3.conn_spec(), c0);
        }
    }

    /// Clears `out`, then protects the next datagram into it and returns its path. A `Some` with
    /// an empty `out` means no packet had keys: send nothing, poll again.
    pub fn transmit(&mut self, now: u64, out: &mut Vec<u8>) -> (r: Option<PathId>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).one_rtt_forgotten(),
            r matches Some(q) ==> {
                let l = final(self).conn_spec().out_log().last();
                &&& final(self).conn_spec().out_log() == old(self).conn_spec().out_log().push(l)
                &&& l.path == q
                &&& final(out)@ == rfc_protect_datagram(l, old(self).keys_spec())
                &&& final(out)@.len() <= out_datagram_len(l) <= MAX_DATAGRAM
                &&& transmit_ok(old(self).conn_spec(), final(self).conn_spec(), l)
            },
            r is None ==> final(out)@ == Seq::<u8>::empty() && final(self).conn_spec().out_log()
                == old(self).conn_spec().out_log() && final(self).conn_spec().acks_later(now),
            now < u64::MAX && old(self).conn_spec().timers_later(now) ==> final(self).conn_spec().timers_later(now),
            drained_kept(final(self).conn_spec(), old(self).conn_spec()),
    {
        let ghost c0 = self.h3.conn_spec();
        let r = quic::pipeline::transmit(self.h3.conn_mut(), now, &self.keys, out);
        proof {
            Connection::lemma_crypto_kept_elim(self.h3.conn_spec(), c0);
        }
        self.forget_failed();
        self.sync_keys();
        r
    }

    pub fn on_timeout(&mut self, now: u64, rand: &[u8; RAND_LEN], app: &mut Vec<AppEvent>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).one_rtt_forgotten(),
            app_grew(old(app)@, final(app)@),
            now < u64::MAX ==> final(self).conn_spec().timers_later(now),
            now <= final(self).conn_spec().now_spec(),
            drained_kept(final(self).conn_spec(), old(self).conn_spec()),
    {
        let ghost c0 = self.h3.conn_spec();
        self.h3.on_timeout(now, rand, app);
        proof {
            Connection::lemma_crypto_kept_elim(self.h3.conn_spec(), c0);
        }
        self.forget_failed();
        self.sync_keys();
    }

    pub fn poll_cid_updates(&mut self, out: &mut Vec<CidUpdate>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).one_rtt_forgotten(),
            final(self).conn_spec().keeps_later(old(self).conn_spec()),
            drained_kept(final(self).conn_spec(), old(self).conn_spec()),
    {
        let ghost c0 = self.h3.conn_spec();
        self.h3.conn_mut().poll_cid_updates(out);
        proof {
            self.h3.conn_spec().lemma_keeps_crypto(c0);
            Connection::lemma_crypto_kept_elim(self.h3.conn_spec(), c0);
        }
        self.forget_failed();
        self.sync_keys();
    }

    pub fn on_reset_candidate(&mut self, tail: &[u8; 16], now: u64, app: &mut Vec<AppEvent>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).one_rtt_forgotten(),
            app_grew(old(app)@, final(app)@),
            drained_kept(final(self).conn_spec(), old(self).conn_spec()),
    {
        let ghost c0 = self.h3.conn_spec();
        self.h3.conn_mut().on_reset_candidate(tail, now);
        let ghost c1 = self.h3.conn_spec();
        self.h3.pump(app);
        proof {
            Connection::lemma_crypto_kept_trans(c0, c1, self.h3.conn_spec());
            Connection::lemma_crypto_kept_elim(self.h3.conn_spec(), c0);
        }
        self.forget_failed();
        self.sync_keys();
    }

    pub fn send_response(&mut self, id: u64, resp: &Response, app: &mut Vec<AppEvent>) -> (r: Result<
        (),
        SendError,
    >)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).one_rtt_forgotten(),
            app_grew(old(app)@, final(app)@),
            drained_kept(final(self).conn_spec(), old(self).conn_spec()),
    {
        let ghost c0 = self.h3.conn_spec();
        let r = self.h3.send_response(id, resp, app);
        proof {
            Connection::lemma_crypto_kept_elim(self.h3.conn_spec(), c0);
        }
        self.forget_failed();
        self.sync_keys();
        r
    }

    pub fn conn(&self) -> (r: &Connection)
        requires
            self.wf(),
        ensures
            *r == self.conn_spec(),
            r.wf(),
    {
        self.h3.conn()
    }

    /// The shell's wake sequence: `on_timeout(now)`, `poll_cid_updates`, then `transmit` until
    /// None; `next_timeout` is then later than `now`. Never called: its contract is the proof. It
    /// stops at `cap` as the shell does, and says nothing then.
    #[verifier::spinoff_prover]
    #[allow(dead_code)]
    fn settled_later(
        &mut self,
        now: u64,
        rand: &[u8; RAND_LEN],
        app: &mut Vec<AppEvent>,
        out: &mut Vec<u8>,
        cap: usize,
    ) -> (r: Option<Option<u64>>)
        requires
            old(self).wf(),
            now < u64::MAX,
        ensures
            r matches Some(t) ==> later(t, now),
    {
        self.on_timeout(now, rand, app);
        let ghost c1 = self.conn_spec();
        let mut v: Vec<CidUpdate> = Vec::new();
        self.poll_cid_updates(&mut v);
        proof {
            self.conn_spec().lemma_keeps_elim(c1, now);
        }
        let mut i: usize = 0;
        while i < cap
            invariant
                self.wf(),
                now < u64::MAX,
                self.conn_spec().timers_later(now),
            decreases cap - i,
        {
            if self.transmit(now, out).is_none() {
                return Some(self.conn().next_timeout());
            }
            i += 1;
        }
        None
    }

    // `crypto_read` gives each `on_crypto` at most the buffered CRYPTO bytes (`crypto_end -
    // crypto_base`), and `theorem_reader_bound` keeps each TLS reader under `4 + MAX_HS_BODY`.
    /// The CRYPTO data of this datagram to TLS, and TLS's events back. Before completion it feeds
    /// Initial and Handshake from TLS's level up; after, only OneRtt (1-RTT CRYPTO arrives only
    /// once complete: a 1-RTT packet is opened only then, RFC 9001 §5.7).
    #[verifier::spinoff_prover]
    fn tls_step(&mut self, now: u64, r: &Rand)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).conn_spec().out_log() == old(self).conn_spec().out_log(),
            // No 1-RTT key survives a handshake that failed before completion (RFC 8446 §6).
            final(self).hs@.phase is Failed && !(old(self).hs@.phase is Failed) && !old(self).conn_spec().live(PacketKind::OneRtt) ==> final(self).keys_spec()[2] is None,
            // After completion the 1-RTT keys stay, so a CONNECTION_CLOSE for a TLS failure goes
            // out under them (Initial and Handshake are discarded by then).
            old(self).conn_spec().live(PacketKind::OneRtt) ==> final(self).keys_spec()[2] == old(self).keys_spec()[2],
            // §4.1.3: Initial data past what TLS had when it left Initial.
            !(old(self).level_spec() is Initial) && old(self).conn_spec().crypto_end_spec(PacketKind::Initial)
                > old(self).init_end && old(self).conn_spec().phase_spec() is Open ==> !(final(self).conn_spec().phase_spec() is Open),
            // Drain after feed: at `tls_step`'s return no level holds an in-order byte TLS has not
            // been given (levels not live are drained by `Connection::wf`).
            final(self).conn_spec().phase_spec() is Open ==> crypto_all_drained(final(self).conn_spec()),
    {
        let ghost c0 = self.h3.conn_spec();
        proof {
            self.h3.lemma_conn_wf();
            Connection::lemma_dead_drained(c0);
        }
        let was = self.h3.conn().handshake_complete();
        if !self.superseded(now) {
            self.sync_keys();
            return ;
        }
        if was {
            // Initial and Handshake are discarded (`lemma_dead_drained`); OneRtt is read here.
            if !self.feed(Level::OneRtt, now, r, was) {
                self.sync_keys();
                return ;
            }
            proof {
                let c = self.h3.conn_spec();
                if c.phase_spec() is Open {
                    assert(crypto_drained(c0, PacketKind::Initial));
                    assert(crypto_drained(c0, PacketKind::Handshake));
                    lemma_all_drained(c);
                }
            }
        } else {
            // OneRtt is not live yet, so drained (`lemma_dead_drained`).
            let ghost l0 = self.level;
            if rank(self.level) == 0 && !self.feed(Level::Initial, now, r, was) {
                self.sync_keys();
                return ;
            }
            let ghost c1 = self.h3.conn_spec();
            proof {
                if c1.phase_spec() is Open {
                    assert(crypto_drained(c0, PacketKind::OneRtt));
                    assert(crypto_drained(c1, PacketKind::OneRtt));
                    assert(crypto_drained(c1, PacketKind::Initial));
                }
            }
            if rank(self.level) <= 1 && !self.feed(Level::Handshake, now, r, was) {
                self.sync_keys();
                return ;
            }
            proof {
                let c = self.h3.conn_spec();
                self.h3.lemma_conn_wf();
                Connection::lemma_dead_drained(c);
                if c.phase_spec() is Open {
                    assert(crypto_drained(c, PacketKind::OneRtt));
                    assert(crypto_drained(c, PacketKind::Initial));
                    // Not read here only once TLS is at OneRtt, so complete and Handshake discarded.
                    assert(crypto_drained(c, PacketKind::Handshake));
                    lemma_all_drained(c);
                }
            }
        }
        self.sync_keys();
    }

    //= https://www.rfc-editor.org/rfc/rfc9001#section-4.1.3
    //# *  If the packet is from a previously installed encryption level, it
    //# MUST NOT contain data that extends past the end of previously
    //# received data in that flow.
    //= https://www.rfc-editor.org/rfc/rfc9001#section-4.1.3
    //# Implementations MUST treat any
    //# violations of this requirement as a connection error of type
    //# PROTOCOL_VIOLATION.
    // Initial is the only level TLS leaves with its space still live: Handshake is discarded in
    // the call that leaves it, and its stream reset. Checked before `on_crypto`, which would say
    // 0x10a. Nothing at Initial is left to read: `core_ok` has `init_end <= crypto_base`.
    /// Step 1: once TLS has left Initial, Initial CRYPTO data past `init_end` closes with
    /// PROTOCOL_VIOLATION; a retransmission of old bytes does not.
    #[verifier::spinoff_prover]
    fn superseded(&mut self, now: u64) -> (cont: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).conn_spec().out_log() == old(self).conn_spec().out_log(),
            final(self).hs == old(self).hs,
            final(self).keys@[2] == old(self).keys@[2],
            final(self).level == old(self).level,
            !(old(self).level is Initial) && old(self).conn_spec().crypto_end_spec(PacketKind::Initial)
                > old(self).init_end && old(self).conn_spec().phase_spec() is Open ==> !cont && !(final(self).conn_spec().phase_spec() is Open),
            !cont ==> !(final(self).conn_spec().phase_spec() is Open),
            cont ==> final(self).h3 == old(self).h3,
            cont && !(old(self).level is Initial) ==> crypto_drained(final(self).conn_spec(), PacketKind::Initial),
            // Acceptance: a stop only for Initial data past the end of what was received before the
            // key change, with PROTOCOL_VIOLATION.
            !cont ==> !(old(self).level is Initial) && old(self).conn_spec().crypto_end_spec(PacketKind::Initial)
                > old(self).init_end,
            !cont && old(self).conn_spec().phase_spec() is Open ==> {
                &&& superseded_allowed_err(*old(self))
                &&& final(self).conn_spec().phase_spec() is Closing
                &&& final(self).conn_spec().close_spec() == Some((false, PROTOCOL_VIOLATION, Seq::<u8>::empty()))
            },
            // Rule 1b: every such datagram closes so.
            old(self).conn_spec().phase_spec() is Open && superseded_allowed_err(*old(self)) ==> !cont
                && final(self).conn_spec().phase_spec() is Closing && final(self).conn_spec().close_spec()
                == Some((false, PROTOCOL_VIOLATION, Seq::<u8>::empty())),
    {
        if matches!(self.level, Level::Initial) {
            return true;
        }
        let e = self.h3.conn().crypto_end(PacketKind::Initial);
        let ghost c0 = self.h3.conn_spec();
        if e > self.init_end {
            proof {
                assert(c0.crypto_received(PacketKind::Initial, (e - 1) as nat));
            }
            shut(self.h3.conn_mut(), PROTOCOL_VIOLATION, now);
            proof {
                Connection::lemma_crypto_kept_elim(self.h3.conn_spec(), c0);
            }
            self.sync_keys();
            return false;
        }
        self.sync_keys();
        true
    }

    /// Step 2 for one level: its newly contiguous CRYPTO bytes to TLS, then the events. False when
    /// the connection is to stop here (an error, or a close).
    #[verifier::spinoff_prover]
    fn feed(&mut self, l: Level, now: u64, r: &Rand, was: bool) -> (cont: bool)
        requires
            old(self).wf(),
            level_rank(l) >= level_rank(old(self).level),
            was ==> l is OneRtt,
        ensures
            final(self).wf(),
            final(self).conn_spec().out_log() == old(self).conn_spec().out_log(),
            cont && !(old(self).hs@.phase is Failed) ==> !(final(self).hs@.phase is Failed),
            final(self).hs@.phase is Failed && !(old(self).hs@.phase is Failed) && !was
                ==> final(self).keys@[2] is None,
            was ==> final(self).keys@[2] == old(self).keys@[2],
            !cont ==> !(final(self).conn_spec().phase_spec() is Open),
            fed_kept(final(self).conn_spec(), old(self).conn_spec()),
            final(self).conn_spec().phase_spec() is Open ==> crypto_drained(final(self).conn_spec(), level_kind(l)),
    {
        hide(spec_on_crypto);
        let mut b: Vec<u8> = Vec::new();
        let ghost c0 = self.h3.conn_spec();
        proof {
            self.h3.lemma_conn_wf();
            Connection::lemma_dead_drained(c0);
        }
        self.h3.conn_mut().crypto_read(kind(l), &mut b);
        // Bounds the count: what TLS has been handed is the stream up to the read offset.
        let _ = self.h3.conn().crypto_end(kind(l));
        proof {
            Connection::lemma_crypto_kept_but_elim(self.h3.conn_spec(), c0, Some(level_kind(l)));
        }
        proof {
            if b.len() > 0 {
                assert(c0.phase_spec() is Open);
                if !c0.live(level_kind(l)) {
                    assert(crypto_drained(c0, level_kind(l)));
                }
            }
        }
        if b.len() > 0 {
            match l {
                Level::Initial => self.fed_i = self.fed_i + b.len() as u64,
                Level::Handshake => self.fed_h = self.fed_h + b.len() as u64,
                Level::OneRtt => {},
            }
        }
        self.sync_keys();
        if b.len() == 0 {
            return true;
        }
        proof {
            self.lemma_push(TlsCall::Fed { level: l, current: self.level });
        }
        self.log = Ghost(self.log@.push(TlsCall::Fed { level: l, current: self.level }));
        let mut ev: Vec<TlsEvent> = Vec::new();
        assert(ev.deep_view() =~= Seq::<SpecTlsEvent>::empty());
        let ghost h0 = self.hs@;
        let ghost cfg = self.hs.cfg_view();
        let ghost tp = self.hs.tp_view();
        proof {
            lemma_fed(cfg, tp, h0, l, b@, r.tls@);
        }
        // TLS's step consumes exactly the bytes `crypto_read` handed over, which `fed` counts.
        let ghost step = spec_on_crypto(cfg, tp, h0, l, b@, r.tls@);
        match self.hs.on_crypto(l, b.as_slice(), &r.tls, &mut ev) {
            Err(code) => {
                proof {
                    assert(step.1 is Err ==> self.hs@ == step.0);
                }
                //= https://www.rfc-editor.org/rfc/rfc8446#section-6
                //# Servers and
                //# clients MUST forget the secret values and keys established in failed
                //# connections, with the exception of the PSKs associated with session
                //# tickets, which SHOULD be discarded if possible.
                // TLS dropped its secrets (4b); the glue holds no traffic secret, only packet keys.
                // The 1-RTT keys go unless the handshake had completed, when the CONNECTION_CLOSE
                // needs them; Initial and Handshake keys stay until their space is discarded, for
                // the same reason (TRUSTED: secret lifetime). No PSK exists.
                if !was {
                    self.keys[2] = None;
                }
                let ghost c1 = self.h3.conn_spec();
                report(self.h3.conn_mut(), code, now);
                proof {
                    Connection::lemma_crypto_kept_elim(self.h3.conn_spec(), c1);
                }
                self.sync_keys();
                false
            },
            Ok(()) => {
                proof {
                    assert(self.hs@ == step.0);
                }
                self.apply(ev, now, r)
            },
        }
    }

    /// TLS's events, in order. False when the connection is to stop here.
    #[verifier::spinoff_prover]
    fn apply(&mut self, ev: Vec<TlsEvent>, now: u64, r: &Rand) -> (ok: bool)
        requires
            old(self).wf(),
            forall|i: int| 0 <= i < ev.deep_view().len() ==> !spec_send_level(#[trigger] ev.deep_view()[i], Level::OneRtt),
            // `theorem_event_discipline`: one `PeerParams` at most, from a call that left the
            // ClientHello phases, so none were known before it (`core_ok`).
            forall|i: int| 0 <= i < ev.deep_view().len() && #[trigger] ev.deep_view()[i] is PeerParams
                ==> !old(self).conn_spec().peer_tp_known_spec() && old(self).hs@.phase is WaitFinished,
            forall|i: int, j: int|
                0 <= i < ev.deep_view().len() && 0 <= j < ev.deep_view().len() && #[trigger] ev.deep_view()[i] is PeerParams
                    && #[trigger] ev.deep_view()[j] is PeerParams ==> i == j,
            // `feed` hands TLS bytes only from an open connection.
            old(self).conn_spec().phase_spec() is Open,
        ensures
            final(self).wf(),
            final(self).conn_spec().out_log() == old(self).conn_spec().out_log(),
            final(self).hs == old(self).hs,
            !ok ==> !(final(self).conn_spec().phase_spec() is Open),
            fed_kept(final(self).conn_spec(), old(self).conn_spec()),
    {
        if !self.key_changes(&ev, now) {
            self.sync_keys();
            return false;
        }
        proof {
            // The Initial offset is what TLS was handed (live), or the end (discarded).
            self.h3.lemma_conn_wf();
            Connection::lemma_dead_drained(self.conn_spec());
        }
        let mut i: usize = 0;
        while i < ev.len()
            invariant
                self.wf(),
                self.conn_spec().out_log() == old(self).conn_spec().out_log(),
                self.hs == old(self).hs,
                forall|j: int| 0 <= j < ev.deep_view().len() ==> !spec_send_level(#[trigger] ev.deep_view()[j], Level::OneRtt),
                // `key_changes` saw nothing unread at Initial, and nothing is read or received here.
                (spec_key_events(ev.deep_view()).0 || spec_key_events(ev.deep_view()).1) && self.level is Initial
                    ==> self.conn_spec().crypto_end_spec(
                    PacketKind::Initial,
                ) <= self.conn_spec().crypto_base_spec(PacketKind::Initial) && self.conn_spec().crypto_end_spec(
                    PacketKind::Initial,
                ) <= self.fed_i,
                fed_kept(self.conn_spec(), old(self).conn_spec()),
                i <= ev.deep_view().len(),
                forall|j: int| i <= j < ev.deep_view().len() && #[trigger] ev.deep_view()[j] is PeerParams
                    ==> !self.conn_spec().peer_tp_known_spec() && self.hs@.phase is WaitFinished,
                forall|j: int, k: int|
                    0 <= j < ev.deep_view().len() && 0 <= k < ev.deep_view().len() && #[trigger] ev.deep_view()[j] is PeerParams
                        && #[trigger] ev.deep_view()[k] is PeerParams ==> j == k,
            decreases ev.len() - i,
        {
            let ghost c0 = self.conn_spec();
            let ghost dv = ev.deep_view();
            let ok = match &ev[i] {
                TlsEvent::PeerParams(b) => {
                    proof {
                        assert(dv[i as int] == ev@[i as int].deep_view());
                        assert(dv[i as int] is PeerParams);
                    }
                    let ok = self.on_params(b, now);
                    proof {
                        Connection::lemma_crypto_kept_base_elim(self.conn_spec(), c0);
                        assert forall|j: int| i < j < dv.len() implies !(#[trigger] dv[j] is PeerParams) by {
                            if dv[j] is PeerParams {
                                assert(dv[i as int] is PeerParams);
                            }
                        }
                    }
                    ok
                },
                TlsEvent::Send { level, data } => {
                    assert(ev.deep_view()[i as int] == ev@[i as int].deep_view());
                    self.on_send(*level, data);
                    proof {
                        Connection::lemma_crypto_kept_elim(self.conn_spec(), c0);
                    }
                    true
                },
                TlsEvent::Secrets { level, client, server } => {
                    proof {
                        assert(ev.deep_view()[i as int] == ev@[i as int].deep_view());
                        if *level is Handshake {
                            assert(spec_secrets_level(ev.deep_view()[i as int], Level::Handshake));
                        }
                    }
                    self.on_secrets(*level, client, server);
                    true
                },
                TlsEvent::Complete => {
                    proof {
                        assert(ev.deep_view()[i as int] == ev@[i as int].deep_view());
                        assert(ev.deep_view()[i as int] is Complete);
                    }
                    self.on_complete(now, r)
                },
            };
            if !ok {
                self.sync_keys();
                return false;
            }
            i += 1;
        }
        self.sync_keys();
        true
    }

    //= https://www.rfc-editor.org/rfc/rfc9001#section-4.1.3
    //# When TLS
    //# provides keys for a higher encryption level, if there is data from
    //# a previous encryption level that TLS has not consumed, this MUST
    //# be treated as a connection error of type PROTOCOL_VIOLATION.
    //= https://www.rfc-editor.org/rfc/rfc8446#section-5.1
    //# -  Handshake messages MUST NOT span key changes.
    //= https://www.rfc-editor.org/rfc/rfc8446#section-5.1
    //# Implementations
    //# MUST verify that all messages immediately preceding a key change
    //# align with a record boundary; if not, then they MUST terminate the
    //# connection with an "unexpected_message" alert.
    // QUIC has no records: bytes left at the lower level when its keys change are the misaligned
    // message, and RFC 9001 §4.1.3 makes the error PROTOCOL_VIOLATION.
    //= https://www.rfc-editor.org/rfc/rfc8446#section-5.1
    //# Because the
    //# ClientHello, EndOfEarlyData, ServerHello, Finished, and KeyUpdate
    //# messages can immediately precede a key change, implementations
    //# MUST send these messages in alignment with a record boundary.
    // Each `Send` carries whole messages of one level, so ours always end at a key change.
    /// The bytes of level `l` (space `k`) TLS has not consumed: in its reader, and still in QUIC's
    /// reassembly buffer out of order.
    spec fn unread(&self, l: Level, k: PacketKind) -> nat {
        let c = self.h3.conn_spec();
        spec_reader(self.hs@, l).len() + if c.crypto_end_spec(k) > tls_fed(*self, l) {
            (c.crypto_end_spec(k) - tls_fed(*self, l)) as nat
        } else {
            0
        }
    }

    #[verifier::spinoff_prover]
    fn unconsumed(&self, l: Level, k: PacketKind) -> (r: bool)
        requires
            self.core_ok(),
            !(l is OneRtt),
        ensures
            r == (self.unread(l, k) > 0),
            r == tls_unconsumed(*self, l, k),
    {
        let e = self.h3.conn().crypto_end(k);
        let f = match l {
            Level::Initial => self.fed_i,
            _ => self.fed_h,
        };
        proof {
            if e > f {
                assert(self.h3.conn_spec().crypto_received(k, (e - 1) as nat));
            }
        }
        self.hs.pending(l) || e > f
    }

    //= https://www.rfc-editor.org/rfc/rfc9001#section-4.1.3
    //# When TLS
    //# provides keys for a higher encryption level, if there is data from
    //# a previous encryption level that TLS has not consumed, this MUST
    //# be treated as a connection error of type PROTOCOL_VIOLATION.
    /// The pre-checks: none of `ev` is applied if TLS moves past a level with bytes unread there.
    #[verifier::spinoff_prover]
    fn key_changes(&mut self, ev: &Vec<TlsEvent>, now: u64) -> (ok: bool)
        requires
            old(self).wf(),
        ensures
            final(self).level == old(self).level,
            final(self).fed_i == old(self).fed_i,
            final(self).wf(),
            final(self).conn_spec().out_log() == old(self).conn_spec().out_log(),
            final(self).hs == old(self).hs,
            ok ==> final(self).h3 == old(self).h3,
            ok && (spec_key_events(ev.deep_view()).0 || spec_key_events(ev.deep_view()).1) ==> old(self).unread(
                Level::Initial,
                PacketKind::Initial,
            ) == 0,
            !ok ==> !(final(self).conn_spec().phase_spec() is Open),
            fed_kept(final(self).conn_spec(), old(self).conn_spec()),
            // Acceptance: keys for a higher level (Handshake at `Secrets { Handshake }`, 1-RTT at
            // `Complete`) with a lower level's data not consumed, and PROTOCOL_VIOLATION.
            !ok && old(self).conn_spec().phase_spec() is Open ==> {
                &&& key_changes_allowed_err(*old(self), ev.deep_view())
                &&& final(self).conn_spec().phase_spec() is Closing
                &&& final(self).conn_spec().close_spec() == Some((false, PROTOCOL_VIOLATION, Seq::<u8>::empty()))
            },
            // Rule 1b: every such batch closes so.
            old(self).conn_spec().phase_spec() is Open && key_changes_allowed_err(*old(self), ev.deep_view()) ==> !ok
                && final(self).conn_spec().phase_spec() is Closing && final(self).conn_spec().close_spec() == Some(
                (false, PROTOCOL_VIOLATION, Seq::<u8>::empty()),
            ),
    {
        let (to_hs, done) = key_events(ev);
        let ghost c0 = self.h3.conn_spec();
        // `Complete` gives 1-RTT keys, above Initial too: TLS leaves Initial there if the batch has
        // no `Secrets { Handshake }`.
        if (to_hs || done) && self.unconsumed(Level::Initial, PacketKind::Initial) {
            shut(self.h3.conn_mut(), PROTOCOL_VIOLATION, now);
            proof {
                Connection::lemma_crypto_kept_elim(self.h3.conn_spec(), c0);
            }
            self.sync_keys();
            return false;
        }
        if done && self.unconsumed(Level::Handshake, PacketKind::Handshake) {
            shut(self.h3.conn_mut(), PROTOCOL_VIOLATION, now);
            proof {
                Connection::lemma_crypto_kept_elim(self.h3.conn_spec(), c0);
            }
            self.sync_keys();
            return false;
        }
        if to_hs || done {
            let ghost c = TlsCall::KeyChange { lower: Level::Initial, unread: self.unread(Level::Initial, PacketKind::Initial) };
            proof {
                self.lemma_push(c);
            }
            self.log = Ghost(self.log@.push(c));
        }
        if done {
            let ghost c = TlsCall::KeyChange { lower: Level::Handshake, unread: self.unread(Level::Handshake, PacketKind::Handshake) };
            proof {
                self.lemma_push(c);
            }
            self.log = Ghost(self.log@.push(c));
        }
        self.sync_keys();
        true
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-7.4
    //# An endpoint MUST treat receipt of a transport parameter with an
    //# invalid value as a connection error of type
    //# TRANSPORT_PARAMETER_ERROR.
    //= https://www.rfc-editor.org/rfc/rfc9000#section-7.3
    //# An endpoint MUST treat the absence of the
    //# initial_source_connection_id transport parameter from either endpoint
    //# or the absence of the original_destination_connection_id transport
    //# parameter from the server as a connection error of type
    //# TRANSPORT_PARAMETER_ERROR.
    /// `PeerParams`: the client's transport parameters. No keys are installed on a connection
    /// they closed.
    #[verifier::spinoff_prover]
    fn on_params(&mut self, b: &Vec<u8>, now: u64) -> (ok: bool)
        requires
            old(self).wf(),
            // The first delivery (`apply`, from `theorem_event_discipline`).
            !old(self).conn_spec().peer_tp_known_spec(),
            old(self).hs@.phase is WaitFinished,
        ensures
            final(self).fed_i == old(self).fed_i,
            final(self).wf(),
            final(self).conn_spec().out_log() == old(self).conn_spec().out_log(),
            final(self).hs == old(self).hs,
            final(self).level == old(self).level,
            ok ==> final(self).conn_spec().crypto_end_spec(PacketKind::Initial) == old(self).conn_spec().crypto_end_spec(PacketKind::Initial),
            final(self).conn_spec().crypto_kept_base(old(self).conn_spec()),
            !ok ==> !(final(self).conn_spec().phase_spec() is Open),
            fed_kept(final(self).conn_spec(), old(self).conn_spec()),
            // Acceptance: a stop only for parameters RFC 9000 lets a server refuse, with
            // TRANSPORT_PARAMETER_ERROR.
            !ok && old(self).conn_spec().phase_spec() is Open ==> {
                &&& tp_allowed_err(old(self).conn_spec(), b@)
                &&& final(self).conn_spec().phase_spec() is Closing
                &&& final(self).conn_spec().close_spec() == Some((false, TRANSPORT_PARAMETER_ERROR, Seq::<u8>::empty()))
            },
            // Rule 1b: refusable parameters close so.
            old(self).conn_spec().phase_spec() is Open && (allowed_tp_err(b@) || tp_allowed_err(old(self).conn_spec(), b@)) ==> !ok
                && final(self).conn_spec().phase_spec() is Closing && final(self).conn_spec().close_spec() == Some(
                (false, TRANSPORT_PARAMETER_ERROR, Seq::<u8>::empty()),
            ),
    {
        let ghost c0 = self.h3.conn_spec();
        // The §17.2 bound `tp_allowed_err` carries.
        let _ = self.h3.conn().client_scid_len();
        proof {
            lemma_tp_err_allowed(b@);
        }
        match parse_transport_params(b.as_slice(), true) {
            Err(_) => {
                shut(self.h3.conn_mut(), TRANSPORT_PARAMETER_ERROR, now);
                proof {
                    Connection::lemma_crypto_kept_elim(self.h3.conn_spec(), c0);
                    Connection::lemma_crypto_kept_to_base(self.h3.conn_spec(), c0);
                }
                self.sync_keys();
                false
            },
            Ok(t) => {
                proof {
                    theorem_peer_tp_wf(b@);
                }
                self.h3.conn_mut().on_peer_params(&t, now);
                proof {
                    Connection::lemma_crypto_kept_base_elim(self.h3.conn_spec(), c0);
                }
                if !matches!(self.h3.conn().phase(), Phase::Open) {
                    self.sync_keys();
                    return false;
                }
                self.sync_keys();
                true
            },
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9001#section-4
    //# If QUIC needs to retransmit that data, it MUST use
    //# the same keys even if TLS has already updated to newer keys.
    //= https://www.rfc-editor.org/rfc/rfc9001#section-4.9
    //# If packets from a lower encryption level contain
    //# CRYPTO frames, frames that retransmit that data MUST be sent at the
    //# same encryption level.
    //= https://www.rfc-editor.org/rfc/rfc9001#section-4.9
    //# Though an endpoint might retain older keys, new data MUST be sent at
    //# the highest currently available encryption level.
    // Each level's bytes go to that level's CRYPTO stream, which 3d sends and retransmits only in
    // that level's space, under that space's key slot. `theorem_event_discipline` orders every
    // `Send { Handshake }` after `Secrets { Handshake }`, and TLS sends Initial only before it
    // has Handshake keys: new data is at the highest level there is.
    /// `Send`: TLS's bytes for `l` to that level's CRYPTO stream.
    #[verifier::spinoff_prover]
    fn on_send(&mut self, l: Level, data: &Vec<u8>)
        requires
            old(self).wf(),
            !(l is OneRtt),
        ensures
            final(self).fed_i == old(self).fed_i,
            final(self).wf(),
            final(self).conn_spec().out_log() == old(self).conn_spec().out_log(),
            final(self).hs == old(self).hs,
            final(self).level == old(self).level,
            final(self).conn_spec().crypto_end_spec(PacketKind::Initial) == old(self).conn_spec().crypto_end_spec(PacketKind::Initial),
            final(self).conn_spec().crypto_kept(old(self).conn_spec()),
            fed_kept(final(self).conn_spec(), old(self).conn_spec()),
    {
        let ghost c0 = self.h3.conn_spec();
        self.h3.conn_mut().crypto_write(kind(l), data.as_slice());
        proof {
            Connection::lemma_crypto_kept_elim(self.h3.conn_spec(), c0);
        }
        self.sync_keys();
    }

    /// TLS leaves Initial: `init_end` and `init_rx` record what the connection has received there.
    #[verifier::spinoff_prover]
    fn leave_initial(&mut self)
        requires
            old(self).h3.wf(),
            old(self).h3.conn_spec().crypto_end_spec(PacketKind::Initial) <= old(self).h3.conn_spec().crypto_base_spec(
                PacketKind::Initial,
            ),
            old(self).h3.conn_spec().crypto_end_spec(PacketKind::Initial) == old(self).fed_i,
        ensures
            *final(self) == (QuicServer { init_end: final(self).init_end, init_rx: final(self).init_rx, ..*old(self) }),
            final(self).init_end == old(self).fed_i,
            final(self).init_rx@ == old(self).h3.conn_spec(),
            final(self).init_end == old(self).h3.conn_spec().crypto_end_spec(PacketKind::Initial),
            final(self).init_end <= old(self).h3.conn_spec().crypto_base_spec(PacketKind::Initial),
            forall|p: nat| #[trigger] final(self).init_rx@.crypto_received(PacketKind::Initial, p) ==> p < final(self).init_end,
            final(self).init_end > 0 ==> final(self).init_rx@.crypto_received(PacketKind::Initial, (final(self).init_end - 1) as nat),
    {
        self.init_end = initial_end(self.h3.conn());
        self.init_rx = Ghost(self.h3.conn_spec());
    }

    /// `Secrets`: the packet keys of level `l`; at Handshake, TLS now receives there.
    #[verifier::spinoff_prover]
    fn on_secrets(&mut self, l: Level, client: &[u8; 32], server: &[u8; 32])
        requires
            old(self).wf(),
            l is Handshake && old(self).level is Initial ==> old(self).conn_spec().crypto_end_spec(PacketKind::Initial)
                <= old(self).conn_spec().crypto_base_spec(PacketKind::Initial) && old(self).conn_spec().crypto_end_spec(
                PacketKind::Initial,
            ) <= old(self).fed_i,
        ensures
            final(self).fed_i == old(self).fed_i,
            final(self).wf(),
            final(self).conn_spec().out_log() == old(self).conn_spec().out_log(),
            final(self).hs == old(self).hs,
            final(self).h3 == old(self).h3,
            !(l is Handshake) ==> final(self).level == old(self).level,
            l is Handshake ==> final(self).level is Handshake,
    {
        let kp = KeyPair { rx: packet_keys(client), tx: packet_keys(server) };
        match l {
            Level::Initial => self.keys[0] = Some(kp),
            Level::Handshake => {
                if matches!(self.level, Level::Initial) {
                    // Everything TLS had at Initial (`key_changes` saw nothing unread there).
                    self.leave_initial();
                }
                self.keys[1] = Some(kp);
                self.level = Level::Handshake;
            },
            Level::OneRtt => self.keys[2] = Some(kp),
        }
        self.sync_keys();
    }

    /// `Complete`: the handshake's end (`h3`, the only ALPN TLS negotiates). No more is applied to
    /// a connection it closed.
    #[verifier::spinoff_prover]
    fn on_complete(&mut self, now: u64, r: &Rand) -> (ok: bool)
        requires
            old(self).wf(),
            old(self).level is Initial ==> old(self).conn_spec().crypto_end_spec(PacketKind::Initial)
                <= old(self).conn_spec().crypto_base_spec(PacketKind::Initial) && old(self).conn_spec().crypto_end_spec(
                PacketKind::Initial,
            ) <= old(self).fed_i,
        ensures
            final(self).fed_i == old(self).fed_i,
            final(self).wf(),
            final(self).conn_spec().out_log() == old(self).conn_spec().out_log(),
            final(self).hs == old(self).hs,
            ok ==> final(self).level is OneRtt,
            !ok ==> final(self).level == old(self).level,
            !ok ==> !(final(self).conn_spec().phase_spec() is Open),
            fed_kept(final(self).conn_spec(), old(self).conn_spec()),
            final(self).conn_spec().peer_tp_known_spec() ==> old(self).conn_spec().peer_tp_known_spec(),
    {
        let alpn: &[u8] = &H3_ALPN;
        // `on_handshake_complete` sets HANDSHAKE_DONE owed in the call that completes, so the next
        // `transmit` sends it (`rustls_quic_handshake` sees it in the next datagram).
        //= https://www.rfc-editor.org/rfc/rfc9001#section-4.1.2
        //# The server MUST send a
        //# HANDSHAKE_DONE frame as soon as the handshake is complete.
        let ghost c0 = self.h3.conn_spec();
        self.h3.conn_mut().on_handshake_complete(alpn, now, &r.complete);
        proof {
            Connection::lemma_crypto_kept_elim(self.h3.conn_spec(), c0);
        }
        if !matches!(self.h3.conn().phase(), Phase::Open) {
            self.sync_keys();
            return false;
        }
        if matches!(self.level, Level::Initial) {
            // TLS leaves Initial here (no `Secrets { Handshake }` before it): as `on_secrets` does.
            self.leave_initial();
        }
        // Only a completed connection: `core_ok` ties OneRtt to completion.
        self.level = Level::OneRtt;
        self.sync_keys();
        true
    }
}

/// What a successful `on_crypto` on non-empty `data` gives `feed`: the level was not OneRtt
/// (never expected), a handshake not `Failed` stays so, and no event is `Send { OneRtt }`.
proof fn lemma_fed(
    cfg: Seq<SpecCertChain>,
    tp: Seq<u8>,
    s: SpecServerHs,
    l: Level,
    data: Seq<u8>,
    rand: Seq<u8>,
)
    requires
        data.len() > 0,
    ensures
        ({
            let (s2, res) = spec_on_crypto(cfg, tp, s, l, data, rand);
            &&& spec_rank(s2.phase) <= spec_rank(s.phase)
            &&& res matches Ok(evs) ==> {
                &&& !(l is OneRtt)
                &&& !(s.phase is Failed) ==> !(s2.phase is Failed)
                &&& forall|i: int| 0 <= i < evs.len() ==> !spec_send_level(#[trigger] evs[i], Level::OneRtt)
                &&& forall|i: int| 0 <= i < evs.len() && #[trigger] evs[i] is PeerParams ==> (s.phase is Start
                    || s.phase is HrrSent) && s2.phase is WaitFinished
                &&& forall|i: int, j: int|
                    0 <= i < evs.len() && 0 <= j < evs.len() && #[trigger] evs[i] is PeerParams
                        && #[trigger] evs[j] is PeerParams ==> i == j
            }
        }),
{
    hide(spec_drain);
    if !(s.phase is Failed) {
        lemma_ok_not_failed(cfg, tp, s, l, data, rand);
    }
    theorem_event_discipline(cfg, tp, s, l, data, rand);
}

/// All drained in `o`, and every level drained in `o` still is in `c`.
proof fn lemma_all_drained_kept(c: Connection, o: Connection)
    requires
        crypto_all_drained(o),
        drained_kept(c, o),
    ensures
        crypto_all_drained(c),
{
    assert forall|k: PacketKind| #[trigger] crypto_drained(c, k) by {
        assert(crypto_drained(o, k));
    }
}

/// The three levels drained: all are.
proof fn lemma_all_drained(c: Connection)
    requires
        crypto_drained(c, PacketKind::Initial),
        crypto_drained(c, PacketKind::Handshake),
        crypto_drained(c, PacketKind::OneRtt),
    ensures
        crypto_all_drained(c),
{
    assert forall|k: PacketKind| #[trigger] crypto_drained(c, k) by {
        match k {
            PacketKind::Initial => {},
            PacketKind::Handshake => {},
            PacketKind::OneRtt => {},
        }
    }
}

/// TLS's answer to non-empty 1-RTT CRYPTO data does not depend on its randomness: no phase
/// expects OneRtt, so it is the unexpected_message failure (or the earlier failure) either way.
/// `receive`'s second OneRtt feed therefore draws nothing from `r.tls`.
proof fn lemma_one_rtt_rand_free(
    cfg: Seq<SpecCertChain>,
    tp: Seq<u8>,
    s: SpecServerHs,
    data: Seq<u8>,
    r1: Seq<u8>,
    r2: Seq<u8>,
)
    requires
        data.len() > 0,
    ensures
        spec_on_crypto(cfg, tp, s, Level::OneRtt, data, r1) == spec_on_crypto(cfg, tp, s, Level::OneRtt, data, r2),
        spec_on_crypto(cfg, tp, s, Level::OneRtt, data, r1).1 is Err,
{
    hide(spec_drain);
}

} // verus!

impl QuicServer<'_> {
    /// Which key slots hold keys.
    #[doc(hidden)]
    pub fn key_slots(&self) -> [bool; 3] {
        [self.keys[0].is_some(), self.keys[1].is_some(), self.keys[2].is_some()]
    }
}


// Requirements on clients, on specification authors, and on TLS records, which QUIC replaces
//
// RFC 9001 §4.6.2, §4.9.3, §5.3, §5.6, §8.3: 0-RTT and the cipher suite. 4b negotiates only
// TLS_AES_128_GCM_SHA256 (0x1301), whose header protection is 3e's `quic::hp`; a cipher suite
// outside 4a's parser is skipped, never rejected, and 4b's `negotiate` picks 0x1301 from those
// that remain. No 0-RTT keys are ever derived (`Level` has no 0-RTT) and HTTP/3 0-RTT is declined.

//= https://www.rfc-editor.org/rfc/rfc9001#section-5.3
//# A cipher suite MUST NOT be
//# negotiated unless a header protection scheme is defined for the
//# cipher suite.
//= https://www.rfc-editor.org/rfc/rfc9001#section-5.3
//# An endpoint MUST NOT reject a ClientHello that offers a cipher suite
//# that it does not support, or it would be impossible to deploy a new
//# cipher suite.
// 0-RTT packets are dropped unopened by quic::protect::rfc_unprotect (3e); no 0-RTT keys exist.
//= https://www.rfc-editor.org/rfc/rfc9001#section-4.6.2
//# When rejecting 0-RTT, a server MUST NOT
//# process any 0-RTT packets, even if it could.
//= https://www.rfc-editor.org/rfc/rfc9001#section-4.6.2
//= type=exception
//= reason=Client-only: this endpoint is a server.
//# The client therefore MUST reset the state of all
//# streams, including application state bound to those streams.
//= https://www.rfc-editor.org/rfc/rfc9001#section-4.9.3
//= type=exception
//= reason=Vacuous: no 0-RTT keys are ever derived, and `Level` has no 0-RTT, so there are none to discard.
//# After receiving
//# a 1-RTT packet, servers MUST discard 0-RTT keys within a short time;
//# the RECOMMENDED time period is three times the Probe Timeout (PTO,
//# see [QUIC-RECOVERY]).
//= https://www.rfc-editor.org/rfc/rfc9001#section-5.6
//= type=exception
//= reason=Client-only: this endpoint is a server.
//# A client
//# therefore MUST NOT use 0-RTT for application data unless specifically
//# requested by the application that is in use.
//= https://www.rfc-editor.org/rfc/rfc9001#section-5.6
//= type=exception
//= reason=The application profile is HTTP/3 (RFC 9114), which declines 0-RTT here: 0-RTT packets are dropped unopened (3e) and no early_data is accepted.
//# An application protocol that uses QUIC MUST include a profile that
//# defines acceptable use of 0-RTT; otherwise, 0-RTT can only be used to
//# carry QUIC frames that do not carry application data.
//= https://www.rfc-editor.org/rfc/rfc9001#section-5.6
//= type=exception
//= reason=Vacuous: no 0-RTT keys are ever derived; every packet is protected with Initial, Handshake or 1-RTT keys.
//# A server MUST NOT use 0-RTT keys to protect packets; it uses 1-RTT
//# keys to protect acknowledgments of 0-RTT packets.
//= https://www.rfc-editor.org/rfc/rfc9001#section-5.6
//= type=exception
//= reason=Client-only: this endpoint is a server.
//# A client MUST NOT
//# attempt to decrypt 0-RTT packets it receives and instead MUST discard
//# them.
//= https://www.rfc-editor.org/rfc/rfc9001#section-5.6
//= type=exception
//= reason=Client-only: this endpoint is a server.
//# Once a client has installed 1-RTT keys, it MUST NOT send any more
//# 0-RTT packets.
//= https://www.rfc-editor.org/rfc/rfc9001#section-8.3
//= type=exception
//= reason=Client-only: this endpoint is a server.
//# Clients MUST NOT send the EndOfEarlyData message.
//= https://www.rfc-editor.org/rfc/rfc9001#section-8.3
//= type=exception
//= reason=Vacuous: 0-RTT packets are never decrypted (3e), so no frame in one is ever received.
//# A server MUST
//# treat receipt of a CRYPTO frame in a 0-RTT packet as a connection
//# error of type PROTOCOL_VIOLATION.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# An implementation may receive an unencrypted record of type
//# change_cipher_spec consisting of the single byte value 0x01 at any
//# time after the first ClientHello message has been sent or received
//# and before the peer's Finished message has been received and MUST
//# simply drop it without further processing.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# An
//# implementation which receives any other change_cipher_spec value or
//# which receives a protected change_cipher_spec record MUST abort the
//# handshake with an "unexpected_message" alert.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# If an implementation
//# detects a change_cipher_spec record received before the first
//# ClientHello message or after the peer's Finished message, it MUST be
//# treated as an unexpected record type (though stateless servers may
//# not be able to distinguish these cases from allowed cases).
//= https://www.rfc-editor.org/rfc/rfc8446#section-5
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# Implementations MUST NOT send record types not defined in this
//# document unless negotiated by some extension.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# If a TLS
//# implementation receives an unexpected record type, it MUST terminate
//# the connection with an "unexpected_message" alert.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.1
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# Any future content types MUST specify appropriate
//# rules.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.1
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# - Handshake messages MUST NOT be interleaved with other record
//# types.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.1
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# That is, if a handshake message is split over two or more
//# records, there MUST NOT be any other records between them.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.1
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# Implementations MUST NOT send zero-length fragments of Handshake
//# types, even if those fragments contain padding.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.1
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# Alert messages (Section 6) MUST NOT be fragmented across records, and
//# multiple alert messages MUST NOT be coalesced into a single
//# TLSPlaintext record.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.1
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# In other words, a record with an Alert type
//# MUST contain exactly one message.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.1
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# legacy_record_version: MUST be set to 0x0303 for all records
//# generated by a TLS 1.3 implementation other than an initial
//# ClientHello (i.e., one not generated after a HelloRetryRequest),
//# where it MAY also be 0x0301 for compatibility purposes.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.1
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# This
//# field is deprecated and MUST be ignored for all purposes.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.1
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# The length MUST NOT exceed 2^14 bytes.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.1
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# An
//# endpoint that receives a record that exceeds this length MUST
//# terminate the connection with a "record_overflow" alert.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.1
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# In order to maximize backward
//# compatibility, a record containing an initial ClientHello SHOULD have
//# version 0x0301 (reflecting TLS 1.0) and a record containing a second
//# ClientHello or a ServerHello MUST have version 0x0303 (reflecting
//# TLS 1.2).
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.1
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# Note that Application Data
//# records MUST NOT be written to the wire unprotected (see Section 2
//# for details).
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.2
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# The length
//# MUST NOT exceed 2^14 + 256 bytes.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.2
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# An
//# endpoint that receives a record that exceeds this length MUST
//# terminate the connection with a "record_overflow" alert.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.2
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# If the decryption fails, the receiver MUST terminate the connection
//# with a "bad_record_mac" alert.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.2
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# An AEAD algorithm used in TLS 1.3 MUST NOT produce an expansion
//# greater than 255 octets.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.2
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# An endpoint that receives a record from its
//# peer with TLSCiphertext.length larger than 2^14 + 256 octets MUST
//# terminate the connection with a "record_overflow" alert.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.3
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# Each sequence number is
//# set to zero at the beginning of a connection and whenever the key is
//# changed; the first record transmitted under a particular traffic key
//# MUST use sequence number 0.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.3
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# If a TLS implementation would need to wrap a sequence number, it MUST
//# either rekey (Section 4.6.3) or terminate the connection.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.3
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# An AEAD algorithm where N_MAX is less than 8 bytes
//# MUST NOT be used with TLS.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.4
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# Implementations MUST set the
//# padding octets to all zeros before encrypting.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.4
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# Implementations
//# MUST NOT send Handshake and Alert records that have a zero-length
//# TLSInnerPlaintext.content; if such a message is received, the
//# receiving implementation MUST terminate the connection with an
//# "unexpected_message" alert.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.4
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# Implementations MUST limit their scanning to the cleartext returned
//# from the AEAD decryption.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.4
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# If a receiving implementation does not
//# find a non-zero octet in the cleartext, it MUST terminate the
//# connection with an "unexpected_message" alert.
//= https://www.rfc-editor.org/rfc/rfc8446#section-5.4
//= type=exception
//= reason=TLS records are not used by QUIC (RFC 9001 §4): CRYPTO frames carry handshake bytes, packet protection is RFC 9001 §5 (quic::protect), and no change_cipher_spec is sent or accepted (RFC 9001 §8.4).
//# The presence of padding does not change the overall record size
//# limitations: the full encoded TLSInnerPlaintext MUST NOT exceed 2^14
//# + 1 octets.
//= https://www.rfc-editor.org/rfc/rfc8446#section-6.1
//= type=exception
//= reason=Replaced by QUIC: closure is CONNECTION_CLOSE (RFC 9001 §4.8, RFC 9000 §10.2); no close_notify is sent or read.
//# Any data received
//# after a closure alert has been received MUST be ignored.
//= https://www.rfc-editor.org/rfc/rfc8446#section-6.1
//= type=exception
//= reason=Replaced by QUIC: closure is CONNECTION_CLOSE (RFC 9001 §4.8, RFC 9000 §10.2); no close_notify is sent or read.
//# Any data received
//# after a closure alert has been received MUST be ignored.
//= https://www.rfc-editor.org/rfc/rfc8446#section-6.1
//= type=exception
//= reason=Replaced by QUIC: closure is CONNECTION_CLOSE (RFC 9001 §4.8, RFC 9000 §10.2); no close_notify is sent or read.
//# Each party MUST send a "close_notify" alert before closing its write
//# side of the connection, unless it has already sent some error alert.
//= https://www.rfc-editor.org/rfc/rfc8446#section-6.1
//= type=exception
//= reason=Replaced by QUIC: closure is CONNECTION_CLOSE (RFC 9001 §4.8, RFC 9000 §10.2); no close_notify is sent or read.
//# If the application protocol using TLS provides that any data may be
//# carried over the underlying transport after the TLS connection is
//# closed, the TLS implementation MUST receive a "close_notify" alert
//# before indicating end-of-data to the application layer.
