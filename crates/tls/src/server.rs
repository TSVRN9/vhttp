//! The server handshake state machine: RFC 8446 Appendix A.2 restricted to our features,
//! `START → RECVD_CH → NEGOTIATED → WAIT_FINISHED → CONNECTED` with the HelloRetryRequest
//! loop back to `START`. `WAIT_EOED`, `WAIT_FLIGHT2`'s client-certificate branch, `WAIT_CERT`
//! and `WAIT_CV` are never entered (no 0-RTT, no client authentication).
//!
//! `on_crypto` takes CRYPTO data at one level, frames handshake messages from it and runs
//! each through `spec_step`; the events of a call are returned only when the call succeeds.
//! There is no 0-RTT level and no client_early_traffic_secret (or binder key) is derived:
//! 0-RTT is never accepted.
use crate::client_hello::*;
use crate::codes::*;
use crate::config::*;
#[allow(unused_imports)]
use crate::ext::*;
use crate::flight::*;
use crate::handshake::*;
use crate::negotiate::*;
use crate::schedule::*;
use crate::server_msgs::*;
#[allow(unused_imports)] // spec-only under plain cargo
use crate::ch_ext::*;
#[allow(unused_imports)]
use crate::hkdf_label::*;
#[allow(unused_imports)]
use crate::pl::*;
#[allow(unused_imports)]
use crate::sign::*;
#[allow(unused_imports)]
use crypto::hmac::*;
#[allow(unused_imports)]
use crypto::p256::*;
#[allow(unused_imports)]
use crypto::sha256::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

//= https://www.rfc-editor.org/rfc/rfc8446#appendix-E.5
//# In addition, to avoid accidental misuse, TLS implementations MUST NOT
//# enable 0-RTT (either sending or accepting) unless specifically
//# requested by the application and MUST NOT automatically resend 0-RTT
//# data if it is rejected by the server unless instructed by the
//# application.
//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.4.2
//# If the
//# server cannot determine that the settings remembered by a client are
//# compatible with its current settings, it MUST NOT accept 0-RTT data.
// No 0-RTT level exists (`Level`), early_data is ignored (4a) and no client_early_traffic_secret
// (or binder key) is derived.
pub enum SpecPhase {
    Start,
    HrrSent,
    WaitFinished,
    Complete,
    Failed,
}

/// Every step lowers the rank; `Failed` and `Complete` are terminal.
pub open spec fn spec_rank(p: SpecPhase) -> nat {
    match p {
        SpecPhase::Start => 3,
        SpecPhase::HrrSent => 2,
        SpecPhase::WaitFinished => 1,
        _ => 0,
    }
}

pub struct SpecServerHs {
    pub phase: SpecPhase,
    pub initial: Seq<u8>,
    pub handshake: Seq<u8>,
    pub transcript: Seq<u8>,
    pub ch1: Option<SpecClientHello>,
    pub client_vd: Seq<u8>,
    pub err: u64,
}

//= https://www.rfc-editor.org/rfc/rfc8446#section-4
//# A peer which receives a
//# handshake message in an unexpected order MUST abort the handshake
//# with an "unexpected_message" alert.
/// The one message (level, type) each phase accepts; bytes at any other level, or of any
/// other type, are unexpected_message.
pub open spec fn spec_expected(p: SpecPhase) -> Option<(Level, u8)> {
    match p {
        SpecPhase::Start => Some((Level::Initial, HT_CLIENT_HELLO)),
        SpecPhase::HrrSent => Some((Level::Initial, HT_CLIENT_HELLO)),
        SpecPhase::WaitFinished => Some((Level::Handshake, HT_FINISHED)),
        _ => None,
    }
}

pub open spec fn spec_reader(s: SpecServerHs, l: Level) -> Seq<u8> {
    match l {
        Level::Initial => s.initial,
        Level::Handshake => s.handshake,
        Level::OneRtt => Seq::empty(),
    }
}

pub open spec fn spec_with_reader(s: SpecServerHs, l: Level, b: Seq<u8>) -> SpecServerHs {
    match l {
        Level::Initial => SpecServerHs { initial: b, ..s },
        Level::Handshake => SpecServerHs { handshake: b, ..s },
        Level::OneRtt => s,
    }
}

//= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.2
//# In that case, the client MUST send the same
//# ClientHello without modification, except as follows:
// ponytail: typed fields only; raw extension-list diff if a client is caught changing unknown extensions
/// Every typed field but `key_shares` (Decision 4). A mismatch is illegal_parameter.
pub open spec fn spec_same_except_shares(a: SpecClientHello, b: SpecClientHello) -> bool {
    &&& a.random == b.random
    &&& a.legacy_session_id == b.legacy_session_id
    &&& a.cipher_suites == b.cipher_suites
    &&& a.versions == b.versions
    &&& a.groups == b.groups
    &&& a.sig_algs == b.sig_algs
    &&& a.sig_algs_cert == b.sig_algs_cert
    &&& a.alpn == b.alpn
    &&& a.server_name == b.server_name
    &&& a.transport_params == b.transport_params
}

/// The secrets (transcript, CH1, expected Finished) are dropped; the readers are kept.
pub open spec fn spec_failed(s: SpecServerHs, e: u64) -> SpecServerHs {
    SpecServerHs {
        phase: SpecPhase::Failed,
        err: e,
        transcript: seq![],
        ch1: None,
        client_vd: zeros32(),
        ..s
    }
}

/// One complete message `m` (header included) of the type `spec_expected(s.phase)` names.
pub open spec fn spec_step(
    cfg: Seq<SpecCertChain>,
    tp: Seq<u8>,
    s: SpecServerHs,
    m: Seq<u8>,
    rand: Seq<u8>,
) -> Result<(SpecServerHs, Seq<SpecTlsEvent>), u64> {
    match s.phase {
        SpecPhase::Start => match rfc_client_hello(m.skip(4)) {
            Err(e) => Err(e),
            Ok(ch) => match rfc_negotiate(ch, cfg, false) {
                Err(e) => Err(e),
                Ok(Choice::Retry) => {
                    //= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.4
                    //# The value of selected_version in the HelloRetryRequest
                    //# "supported_versions" extension MUST be retained in the ServerHello,
                    //# and a client MUST abort the handshake with an "illegal_parameter"
                    //# alert if the value changes.
                    // by construction: the HelloRetryRequest and ServerHello both carry spec_sh_versions_bytes() (0x0304); the client-side abort is N/A (client-only)
                    let hrr = spec_hello_retry_request_bytes(ch.legacy_session_id, SECP256R1);
                    Ok(
                        (
                            SpecServerHs {
                                phase: SpecPhase::HrrSent,
                                transcript: spec_message_hash(m) + hrr,
                                ch1: Some(ch),
                                ..s
                            },
                            seq![SpecTlsEvent::Send { level: Level::Initial, data: hrr }],
                        ),
                    )
                },
                Ok(Choice::Proceed { chain, scheme, share }) => match spec_flight(
                    cfg,
                    tp,
                    m,
                    ch,
                    chain as nat,
                    scheme,
                    share as nat,
                    rand,
                ) {
                    Err(e) => Err(e),
                    Ok(f) => Ok(
                        (
                            SpecServerHs {
                                phase: SpecPhase::WaitFinished,
                                transcript: seq![],
                                ch1: None,
                                client_vd: f.client_vd,
                                ..s
                            },
                            f.events,
                        ),
                    ),
                },
            },
        },
        SpecPhase::HrrSent => match rfc_client_hello(m.skip(4)) {
            Err(e) => Err(e),
            Ok(ch) => if !spec_same_except_shares(s.ch1->Some_0, ch) {
                Err(ALERT_ILLEGAL_PARAMETER)
            } else {
                match rfc_negotiate(ch, cfg, true) {
                    Err(e) => Err(e),
                    // unreachable (negotiate::theorem_no_second_hrr)
                    Ok(Choice::Retry) => Err(ALERT_ILLEGAL_PARAMETER),
                    Ok(Choice::Proceed { chain, scheme, share }) => match spec_flight(
                        cfg,
                        tp,
                        s.transcript + m,
                        ch,
                        chain as nat,
                        scheme,
                        share as nat,
                        rand,
                    ) {
                        Err(e) => Err(e),
                        Ok(f) => Ok(
                            (
                                SpecServerHs {
                                    phase: SpecPhase::WaitFinished,
                                    transcript: seq![],
                                    ch1: None,
                                    client_vd: f.client_vd,
                                    ..s
                                },
                                f.events,
                            ),
                        ),
                    },
                }
            },
        },
        //= https://www.rfc-editor.org/rfc/rfc8446#section-4.6.1
        //# At any time after the server has received the client Finished
        //# message, it MAY send a NewSessionTicket message.
        // not taken: no NewSessionTicket is sent (PSK/resumption declined)
        //= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.4
        //# Any records following a Finished message MUST be encrypted under the
        //# appropriate application traffic key as described in Section 7.2.
        // by construction: Secrets{OneRtt} is the flight's last event, after the server Finished (theorem_flight_order); nothing is sent after it, and QUIC applies the keys
        SpecPhase::WaitFinished => match rfc_finished(m.skip(4)) {
            Err(e) => Err(e),
            Ok(vd) => if vd != s.client_vd {
                Err(ALERT_DECRYPT_ERROR)
            } else {
                Ok(
                    (
                        SpecServerHs { phase: SpecPhase::Complete, client_vd: zeros32(), ..s },
                        seq![SpecTlsEvent::Complete],
                    ),
                )
            },
        },
        // never reached: the drain steps only a phase with an expected message
        _ => Err(ALERT_UNEXPECTED_MESSAGE),
    }
}

/// Frames and steps messages at `level` while the phase expects one there.
pub open spec fn spec_drain(
    cfg: Seq<SpecCertChain>,
    tp: Seq<u8>,
    s: SpecServerHs,
    level: Level,
    rand: Seq<u8>,
    acc: Seq<SpecTlsEvent>,
) -> (SpecServerHs, Result<Seq<SpecTlsEvent>, u64>)
    decreases spec_rank(s.phase),
    via lemma_drain_decreases
{
    match spec_expected(s.phase) {
        None => (s, Ok(acc)),
        Some((l, ty)) => if l != level {
            (s, Ok(acc))
        } else {
            let buf = spec_reader(s, level);
            match rfc_next_message(buf, ty) {
                Err(e) => (spec_failed(s, e), Err(e)),
                Ok(None) => (s, Ok(acc)),
                Ok(Some(n)) => {
                    let s1 = spec_with_reader(s, level, buf.skip(n as int));
                    match spec_step(cfg, tp, s1, buf.take(n as int), rand) {
                        Err(e) => (spec_failed(s1, e), Err(e)),
                        Ok((s2, evs)) => spec_drain(cfg, tp, s2, level, rand, acc + evs),
                    }
                },
            }
        },
    }
}

#[via_fn]
proof fn lemma_drain_decreases(
    cfg: Seq<SpecCertChain>,
    tp: Seq<u8>,
    s: SpecServerHs,
    level: Level,
    rand: Seq<u8>,
    acc: Seq<SpecTlsEvent>,
) {
    hide(spec_step);
    if let Some((l, ty)) = spec_expected(s.phase) {
        let buf = spec_reader(s, level);
        if let Ok(Some(n)) = rfc_next_message(buf, ty) {
            let s1 = spec_with_reader(s, level, buf.skip(n as int));
            lemma_step_facts(cfg, tp, s1, buf.take(n as int), rand);
        }
    }
}

pub open spec fn spec_on_crypto(
    cfg: Seq<SpecCertChain>,
    tp: Seq<u8>,
    s: SpecServerHs,
    level: Level,
    data: Seq<u8>,
    rand: Seq<u8>,
) -> (SpecServerHs, Result<Seq<SpecTlsEvent>, u64>) {
    if s.phase is Failed {
        (s, Err(s.err))
    } else if data.len() > 0 && !(spec_expected(s.phase) matches Some((l, _)) && l == level) {
        //= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.2
        //# Because TLS 1.3 forbids renegotiation, if a server has negotiated
        //# TLS 1.3 and receives a ClientHello at any other time, it MUST
        //# terminate the connection with an "unexpected_message" alert.
        // Any Initial byte after the ServerHello, any byte after Complete, any OneRtt byte.
        //= https://www.rfc-editor.org/rfc/rfc8446#section-4.6.3
        //# Implementations
        //# that receive a KeyUpdate message prior to receiving a Finished
        //# message MUST terminate the connection with an "unexpected_message"
        //# alert.
        //= https://www.rfc-editor.org/rfc/rfc8446#section-4.6.3
        //# After sending a KeyUpdate message, the sender SHALL send all
        //# its traffic using the next generation of keys, computed as described
        //# in Section 7.2.
        // vacuous: TLS KeyUpdate is replaced by QUIC key update (RFC 9001 §6); any KeyUpdate is unexpected_message
        //= https://www.rfc-editor.org/rfc/rfc8446#section-4.6.3
        //# Upon receiving a KeyUpdate, the receiver MUST update
        //# its receiving keys.
        // vacuous: TLS KeyUpdate is replaced by QUIC key update (RFC 9001 §6); any KeyUpdate is unexpected_message
        //= https://www.rfc-editor.org/rfc/rfc8446#section-4.6.3
        //# If an implementation
        //# receives any other value, it MUST terminate the connection with an
        //# "illegal_parameter" alert.
        // vacuous: TLS KeyUpdate is replaced by QUIC key update (RFC 9001 §6); any KeyUpdate is unexpected_message
        //= https://www.rfc-editor.org/rfc/rfc8446#section-4.6.3
        //# If the request_update field is set to "update_requested", then the
        //# receiver MUST send a KeyUpdate of its own with request_update set to
        //# "update_not_requested" prior to sending its next Application Data
        //# record.
        // vacuous: TLS KeyUpdate is replaced by QUIC key update (RFC 9001 §6); any KeyUpdate is unexpected_message
        //= https://www.rfc-editor.org/rfc/rfc8446#section-4.6.3
        //# Both sender and receiver MUST encrypt their KeyUpdate messages with
        //# the old keys.
        // vacuous: TLS KeyUpdate is replaced by QUIC key update (RFC 9001 §6); any KeyUpdate is unexpected_message
        //= https://www.rfc-editor.org/rfc/rfc8446#section-4.6.3
        //# Additionally, both sides MUST enforce that a KeyUpdate
        //# with the old key is received before accepting any messages encrypted
        //# with the new key.
        // vacuous: TLS KeyUpdate is replaced by QUIC key update (RFC 9001 §6); any KeyUpdate is unexpected_message
        //= https://www.rfc-editor.org/rfc/rfc9001#section-6
        //# Endpoints
        //# MUST NOT send a TLS KeyUpdate message.
        // by construction: no KeyUpdate serializer exists
        //= https://www.rfc-editor.org/rfc/rfc9001#section-6
        //# Endpoints MUST treat the
        //# receipt of a TLS KeyUpdate message as a connection error of type
        //# 0x010a, equivalent to a fatal TLS alert of unexpected_message; see
        //# Section 4.8.
        // A KeyUpdate (type 24) at Handshake is not a Finished (rfc_next_message), and at OneRtt
        // nothing is ever expected: both are 0x10a.
        (spec_failed(s, ALERT_UNEXPECTED_MESSAGE), Err(ALERT_UNEXPECTED_MESSAGE))
    } else {
        spec_drain(cfg, tp, spec_with_reader(s, level, spec_reader(s, level) + data), level, rand, seq![])
    }
}

/// The M7 reader bound (and what keeps it inductive): the reader at the expected level holds
/// less than one maximal message, and nothing is buffered at Handshake before the flight.
pub open spec fn spec_readers_ok(s: SpecServerHs) -> bool {
    &&& (s.phase is Start || s.phase is HrrSent) ==> s.handshake.len() == 0
    &&& spec_expected(s.phase) matches Some((l, _)) ==> spec_reader(s, l).len() < 4 + MAX_HS_BODY
}

/// The state invariant beyond the brief's `wf` list: the transcript is kept only between the
/// HelloRetryRequest and ClientHello2, and is then short.
pub open spec fn spec_hs_inv(s: SpecServerHs) -> bool {
    &&& s.phase is HrrSent ==> s.transcript.len() <= 0x1000
    &&& !(s.phase is HrrSent) ==> s.transcript.len() == 0
    &&& (s.phase is HrrSent <==> s.ch1 is Some)
    &&& spec_readers_ok(s)
}

// =============================================================================
// Theorems
// =============================================================================

pub open spec fn spec_flight_shaped(f: Seq<SpecTlsEvent>) -> bool {
    &&& f.len() == 5
    &&& f[0] is PeerParams
    &&& f[1] matches SpecTlsEvent::Send { level: Level::Initial, .. }
    &&& f[2] matches SpecTlsEvent::Secrets { level: Level::Handshake, .. }
    &&& f[3] matches SpecTlsEvent::Send { level: Level::Handshake, .. }
    &&& f[4] matches SpecTlsEvent::Secrets { level: Level::OneRtt, .. }
}

proof fn lemma_flight_shape(
    cfg: Seq<SpecCertChain>,
    tp: Seq<u8>,
    t0: Seq<u8>,
    ch: SpecClientHello,
    chain: nat,
    scheme: u16,
    share: nat,
    rand: Seq<u8>,
)
    requires
        spec_flight(cfg, tp, t0, ch, chain, scheme, share, rand) is Ok,
    ensures
        ({
            let f = spec_flight(cfg, tp, t0, ch, chain, scheme, share, rand)->Ok_0;
            &&& spec_flight_shaped(f.events)
            &&& f.events[0] == SpecTlsEvent::PeerParams(ch.transport_params)
        }),
{
    hide(spec_sha256);
    hide(spec_hkdf_expand_label);
    hide(spec_hmac_sha256);
    hide(spec_finished_key);
    hide(spec_handshake_secret);
    hide(spec_master_secret);
    hide(spec_p256_public_key);
    hide(spec_p256_ecdh);
    hide(spec_encrypted_extensions_bytes);
    hide(spec_certificate_bytes);
    hide(spec_certificate_verify_bytes);
    hide(spec_finished_bytes);
    hide(spec_cv_signature);
    hide(spec_server_hello_bytes);
}

/// The phase moves only forward, a step to `WaitFinished` comes from a ClientHello phase,
/// and a step keeps the readers.
proof fn lemma_step_facts(
    cfg: Seq<SpecCertChain>,
    tp: Seq<u8>,
    s: SpecServerHs,
    m: Seq<u8>,
    rand: Seq<u8>,
)
    ensures
        spec_step(cfg, tp, s, m, rand) matches Ok((s2, evs)) ==> {
            &&& spec_rank(s2.phase) < spec_rank(s.phase)
            &&& s2.initial == s.initial
            &&& s2.handshake == s.handshake
            &&& s2.err == s.err
            &&& s2.phase is HrrSent ==> s.phase is Start && s2.ch1 is Some
            &&& s2.phase is WaitFinished ==> (s.phase is Start || s.phase is HrrSent)
            &&& s2.phase is Complete ==> s.phase is WaitFinished
            &&& !(s2.phase is Failed)
        },
{
    hide(spec_flight);
    hide(rfc_client_hello);
    hide(rfc_negotiate);
    hide(spec_message_hash);
    hide(spec_hello_retry_request_bytes);
}

/// The events of one step: the HelloRetryRequest, the five-event flight, or `Complete`.
proof fn lemma_step_events(
    cfg: Seq<SpecCertChain>,
    tp: Seq<u8>,
    s: SpecServerHs,
    m: Seq<u8>,
    rand: Seq<u8>,
)
    ensures
        spec_step(cfg, tp, s, m, rand) matches Ok((s2, evs)) ==> {
            ||| s.phase is Start && s2.phase is HrrSent && evs.len() == 1
                && (evs[0] matches SpecTlsEvent::Send { level: Level::Initial, .. })
            ||| (s.phase is Start || s.phase is HrrSent) && s2.phase is WaitFinished
                && spec_flight_shaped(evs) && rfc_client_hello(m.skip(4)) is Ok
                && evs[0] == SpecTlsEvent::PeerParams(rfc_client_hello(m.skip(4))->Ok_0.transport_params)
            ||| s.phase is WaitFinished && s2.phase is Complete && evs == seq![SpecTlsEvent::Complete]
        },
{
    hide(spec_flight);
    hide(rfc_client_hello);
    hide(rfc_negotiate);
    hide(spec_message_hash);
    hide(spec_hello_retry_request_bytes);
    if let Ok((s2, evs)) = spec_step(cfg, tp, s, m, rand) {
        let ch = rfc_client_hello(m.skip(4))->Ok_0;
        if s2.phase is WaitFinished {
            if s.phase is Start {
                if let Ok(Choice::Proceed { chain, scheme, share }) = rfc_negotiate(ch, cfg, false) {
                    lemma_flight_shape(cfg, tp, m, ch, chain as nat, scheme, share as nat, rand);
                }
            } else {
                if let Ok(Choice::Proceed { chain, scheme, share }) = rfc_negotiate(ch, cfg, true) {
                    lemma_flight_shape(
                        cfg,
                        tp,
                        s.transcript + m,
                        ch,
                        chain as nat,
                        scheme,
                        share as nat,
                        rand,
                    );
                }
            }
        }
    }
}

/// What one call's events look like, after `acc`.
spec fn spec_call_shape(x: Seq<SpecTlsEvent>, p: SpecPhase, p2: SpecPhase) -> bool {
    ||| x.len() == 0 && p2 == p
    ||| x == seq![SpecTlsEvent::Complete] && p is WaitFinished && p2 is Complete
    ||| x.len() == 1 && (x[0] matches SpecTlsEvent::Send { level: Level::Initial, .. }) && p is Start
        && p2 is HrrSent
    ||| spec_flight_shaped(x) && (p is Start || p is HrrSent) && p2 is WaitFinished
    ||| x.len() == 6 && (x[0] matches SpecTlsEvent::Send { level: Level::Initial, .. })
        && spec_flight_shaped(x.subrange(1, 6)) && p is Start && p2 is WaitFinished
}

proof fn lemma_drain_events(
    cfg: Seq<SpecCertChain>,
    tp: Seq<u8>,
    s: SpecServerHs,
    level: Level,
    rand: Seq<u8>,
    acc: Seq<SpecTlsEvent>,
)
    requires
        !(s.phase is Failed),
    ensures
        match spec_drain(cfg, tp, s, level, rand, acc) {
            (s2, Ok(evs)) => evs.len() >= acc.len() && evs.subrange(0, acc.len() as int) == acc
                && spec_call_shape(evs.subrange(acc.len() as int, evs.len() as int), s.phase, s2.phase),
            (s2, Err(_)) => s2.phase is Failed,
        },
    decreases spec_rank(s.phase),
{
    hide(spec_step);
    if let Some((l, ty)) = spec_expected(s.phase) {
        if l == level {
            let buf = spec_reader(s, level);
            if let Ok(Some(n)) = rfc_next_message(buf, ty) {
                let s1 = spec_with_reader(s, level, buf.skip(n as int));
                let m = buf.take(n as int);
                lemma_step_facts(cfg, tp, s1, m, rand);
                lemma_step_events(cfg, tp, s1, m, rand);
                if let Ok((s2, evs)) = spec_step(cfg, tp, s1, m, rand) {
                    let acc2 = acc + evs;
                    lemma_drain_events(cfg, tp, s2, level, rand, acc2);
                    let (s3, r) = spec_drain(cfg, tp, s2, level, rand, acc2);
                    if let Ok(all) = r {
                        assert(all.subrange(0, acc.len() as int) =~= acc2.subrange(0, acc.len() as int));
                        assert(acc2.subrange(0, acc.len() as int) =~= acc);
                        let rest = all.subrange(acc2.len() as int, all.len() as int);
                        let x = all.subrange(acc.len() as int, all.len() as int);
                        assert(x =~= evs + rest) by {
                            assert forall|k: int| 0 <= k < evs.len() implies x[k] == evs[k] by {
                                assert(all.subrange(0, acc2.len() as int)[acc.len() + k] == acc2[acc.len() + k]);
                            }
                        }
                        if s2.phase is HrrSent {
                            // The flight (or nothing) can follow the HelloRetryRequest.
                            if rest.len() == 0 {
                                assert(x =~= evs);
                            } else {
                                assert(spec_flight_shaped(rest));
                                assert(x.subrange(1, 6) =~= rest);
                            }
                        } else {
                            // After the flight or Finished nothing more is expected at `level`.
                            assert(s3 == s2 && all == acc2);
                            assert(rest.len() == 0);
                            assert(x =~= evs);
                        }
                    }
                }
            } else {
                assert(acc.subrange(0, acc.len() as int) =~= acc);
            }
        } else {
            assert(acc.subrange(0, acc.len() as int) =~= acc);
        }
    } else {
        assert(acc.subrange(0, acc.len() as int) =~= acc);
    }
}

/// A call that succeeds leaves the handshake not `Failed` (4c: the glue's 1-RTT key slot).
pub proof fn lemma_ok_not_failed(
    cfg: Seq<SpecCertChain>,
    tp: Seq<u8>,
    s: SpecServerHs,
    level: Level,
    data: Seq<u8>,
    rand: Seq<u8>,
)
    requires
        !(s.phase is Failed),
    ensures
        spec_on_crypto(cfg, tp, s, level, data, rand).1 is Ok ==> !(spec_on_crypto(cfg, tp, s, level, data, rand).0.phase is Failed),
{
    hide(spec_step);
    lemma_drain_events(cfg, tp, spec_with_reader(s, level, spec_reader(s, level) + data), level, rand, seq![]);
}

/// No `Send` ever follows `Failed`: it is absorbing.
pub proof fn theorem_failed_absorbing(
    cfg: Seq<SpecCertChain>,
    tp: Seq<u8>,
    s: SpecServerHs,
    level: Level,
    data: Seq<u8>,
    rand: Seq<u8>,
)
    requires
        s.phase is Failed,
    ensures
        spec_on_crypto(cfg, tp, s, level, data, rand) == (s, Err::<Seq<SpecTlsEvent>, u64>(s.err)),
{
}

/// `Complete` is emitted exactly for the expected client Finished.
pub proof fn theorem_complete_iff_finished(
    cfg: Seq<SpecCertChain>,
    tp: Seq<u8>,
    s: SpecServerHs,
    m: Seq<u8>,
    rand: Seq<u8>,
)
    requires
        spec_step(cfg, tp, s, m, rand) is Ok,
        spec_expected(s.phase) matches Some((_, ty)) && rfc_next_message(m, ty) == Ok::<
            Option<nat>,
            u64,
        >(Some(m.len())),
    ensures
        spec_step(cfg, tp, s, m, rand)->Ok_0.1.contains(SpecTlsEvent::Complete) <==> (s.phase is WaitFinished
            && m == spec_finished_bytes(s.client_vd)),
{
    hide(spec_flight);
    hide(rfc_client_hello);
    hide(rfc_negotiate);
    hide(spec_message_hash);
    hide(spec_hello_retry_request_bytes);
    lemma_step_events(cfg, tp, s, m, rand);
    let evs = spec_step(cfg, tp, s, m, rand)->Ok_0.1;
    if s.phase is WaitFinished {
        assert(evs[0] == SpecTlsEvent::Complete);
        theorem_hs_canonical(m, HT_FINISHED);
        assert(m.take(m.len() as int) =~= m);
        assert(m.subrange(4, m.len() as int) =~= m.skip(4));
    } else if evs.contains(SpecTlsEvent::Complete) {
        let i = choose|i: int| 0 <= i < evs.len() && evs[i] == SpecTlsEvent::Complete;
        assert(evs[i] == SpecTlsEvent::Complete);
    }
}

/// A step from `HrrSent` never reaches `HrrSent` again, and (unless the RNG drew the
/// HelloRetryRequest random itself, p = 2^-256) never sends a message carrying that random.
// ponytail: probability 2^-256; add an exec guard (internal_error) if a deterministic RNG is ever used
pub proof fn theorem_server_no_second_hrr(
    cfg: Seq<SpecCertChain>,
    tp: Seq<u8>,
    s: SpecServerHs,
    m: Seq<u8>,
    rand: Seq<u8>,
)
    requires
        s.phase is HrrSent,
        spec_step(cfg, tp, s, m, rand) is Ok,
    ensures
        ({
            let (s2, evs) = spec_step(cfg, tp, s, m, rand)->Ok_0;
            &&& !(s2.phase is HrrSent)
            &&& rand.len() == TLS_RAND_LEN && rand.subrange(0, 32) != HRR_RANDOM@ ==> forall|i: int|
                0 <= i < evs.len() ==> !(#[trigger] evs[i] matches SpecTlsEvent::Send {
                    level: Level::Initial,
                    data,
                } && data.subrange(6, 38) == HRR_RANDOM@)
        }),
{
    hide(spec_flight);
    hide(rfc_client_hello);
    hide(rfc_negotiate);
    hide(spec_message_hash);
    hide(spec_hello_retry_request_bytes);
    lemma_step_facts(cfg, tp, s, m, rand);
    lemma_step_events(cfg, tp, s, m, rand);
    let ch = rfc_client_hello(m.skip(4))->Ok_0;
    crate::negotiate::theorem_no_second_hrr(ch, cfg);
    if rand.len() == TLS_RAND_LEN {
        if let Ok(Choice::Proceed { chain, scheme, share }) = rfc_negotiate(ch, cfg, true) {
            lemma_after_hrr(ch, cfg);
            let t0 = s.transcript + m;
            theorem_flight_order(cfg, tp, t0, ch, chain as nat, scheme, share as nat, rand);
        }
    }
}

/// `rfc_negotiate` after a HelloRetryRequest proceeds only on CH2's single secp256r1 share.
proof fn lemma_after_hrr(ch: SpecClientHello, cfg: Seq<SpecCertChain>)
    ensures
        rfc_negotiate(ch, cfg, true) matches Ok(Choice::Proceed { share, .. }) ==> share == 0
            && (ch.key_shares matches Some(ks) && ks.len() == 1 && ks[0].group == SECP256R1),
{
}

pub open spec fn spec_send_level(e: SpecTlsEvent, l: Level) -> bool {
    e matches SpecTlsEvent::Send { level, .. } && level == l
}

pub open spec fn spec_secrets_level(e: SpecTlsEvent, l: Level) -> bool {
    e matches SpecTlsEvent::Secrets { level, .. } && level == l
}

/// In every successful call: no `Send { OneRtt }`; every `Send { Handshake }` follows a
/// `Secrets { Handshake }`; at most one `PeerParams`, and only in the call that reaches
/// `WaitFinished` from a ClientHello phase. The phase never moves back, so `PeerParams`
/// appears at most once per connection.
pub proof fn theorem_event_discipline(
    cfg: Seq<SpecCertChain>,
    tp: Seq<u8>,
    s: SpecServerHs,
    level: Level,
    data: Seq<u8>,
    rand: Seq<u8>,
)
    ensures
        ({
            let (s2, res) = spec_on_crypto(cfg, tp, s, level, data, rand);
            &&& spec_rank(s2.phase) <= spec_rank(s.phase)
            &&& res matches Ok(evs) ==> {
                &&& forall|i: int| 0 <= i < evs.len() ==> !spec_send_level(#[trigger] evs[i], Level::OneRtt)
                &&& forall|i: int|
                    0 <= i < evs.len() && spec_send_level(#[trigger] evs[i], Level::Handshake) ==> exists|
                        j: int,
                    |
                        0 <= j < i && spec_secrets_level(#[trigger] evs[j], Level::Handshake)
                &&& forall|i: int, j: int|
                    0 <= i < evs.len() && 0 <= j < evs.len() && #[trigger] evs[i] is PeerParams
                        && #[trigger] evs[j] is PeerParams ==> i == j
                &&& forall|i: int|
                    0 <= i < evs.len() && #[trigger] evs[i] is PeerParams ==> (s.phase is Start
                        || s.phase is HrrSent) && s2.phase is WaitFinished
            }
        }),
{
    hide(spec_step);
    if !(s.phase is Failed) && !(data.len() > 0 && !(spec_expected(s.phase) matches Some((l, _))
        && l == level)) {
        let s0 = spec_with_reader(s, level, spec_reader(s, level) + data);
        lemma_drain_events(cfg, tp, s0, level, rand, seq![]);
        let (s2, res) = spec_drain(cfg, tp, s0, level, rand, seq![]);
        if let Ok(evs) = res {
            assert(evs.subrange(0, evs.len() as int) =~= evs);
            if evs.len() == 6 {
                assert(evs.subrange(1, 6)[2] == evs[3]);
                assert forall|i: int|
                    0 <= i < evs.len() && spec_send_level(#[trigger] evs[i], Level::Handshake) implies exists|
                        j: int,
                    |
                        0 <= j < i && spec_secrets_level(#[trigger] evs[j], Level::Handshake) by {
                    assert(evs.subrange(1, 6)[i - 2] == evs[i - 1]);
                    assert(spec_secrets_level(evs[i - 1], Level::Handshake));
                }
                assert forall|i: int| 0 <= i < evs.len() implies !spec_send_level(
                    #[trigger] evs[i],
                    Level::OneRtt,
                ) by {
                    if i > 0 {
                        assert(evs.subrange(1, 6)[i - 1] == evs[i]);
                    }
                }
                assert forall|i: int| 0 <= i < evs.len() && #[trigger] evs[i] is PeerParams implies i
                    == 1 by {
                    if i > 0 {
                        assert(evs.subrange(1, 6)[i - 1] == evs[i]);
                    }
                }
            } else if evs.len() == 5 {
                assert forall|i: int|
                    0 <= i < evs.len() && spec_send_level(#[trigger] evs[i], Level::Handshake) implies exists|
                        j: int,
                    |
                        0 <= j < i && spec_secrets_level(#[trigger] evs[j], Level::Handshake) by {
                    assert(spec_secrets_level(evs[2], Level::Handshake));
                }
            }
        }
    }
}

/// The `PeerParams` of a step are that step's ClientHello's quic_transport_parameters (CH2's
/// after a HelloRetryRequest), and the step reaches `WaitFinished`.
pub proof fn theorem_peer_params(
    cfg: Seq<SpecCertChain>,
    tp: Seq<u8>,
    s: SpecServerHs,
    m: Seq<u8>,
    rand: Seq<u8>,
)
    ensures
        spec_step(cfg, tp, s, m, rand) matches Ok((s2, evs)) ==> forall|i: int|
            0 <= i < evs.len() && #[trigger] evs[i] is PeerParams ==> s2.phase is WaitFinished
                && evs[i] == SpecTlsEvent::PeerParams(rfc_client_hello(m.skip(4))->Ok_0.transport_params),
{
    hide(spec_step);
    lemma_step_events(cfg, tp, s, m, rand);
}

/// The M7 obligation: after any call the reader at the expected level holds less than
/// `4 + MAX_HS_BODY` bytes (an inductive invariant: `spec_readers_ok` is kept).
pub proof fn theorem_reader_bound(
    cfg: Seq<SpecCertChain>,
    tp: Seq<u8>,
    s: SpecServerHs,
    level: Level,
    data: Seq<u8>,
    rand: Seq<u8>,
)
    requires
        spec_readers_ok(s),
    ensures
        spec_readers_ok(spec_on_crypto(cfg, tp, s, level, data, rand).0),
{
    hide(spec_step);
    if !(s.phase is Failed) && !(data.len() > 0 && !(spec_expected(s.phase) matches Some((l, _))
        && l == level)) {
        let s0 = spec_with_reader(s, level, spec_reader(s, level) + data);
        if data.len() == 0 {
            assert(s0.initial =~= s.initial);
            assert(s0.handshake =~= s.handshake);
        }
        lemma_drain_readers(cfg, tp, s0, level, rand, seq![]);
    }
}

proof fn lemma_drain_readers(
    cfg: Seq<SpecCertChain>,
    tp: Seq<u8>,
    s: SpecServerHs,
    level: Level,
    rand: Seq<u8>,
    acc: Seq<SpecTlsEvent>,
)
    requires
        (s.phase is Start || s.phase is HrrSent) ==> s.handshake.len() == 0,
        spec_expected(s.phase) matches Some((l, _)) ==> (l != level ==> spec_reader(s, l).len() < 4
            + MAX_HS_BODY),
    ensures
        spec_readers_ok(spec_drain(cfg, tp, s, level, rand, acc).0),
    decreases spec_rank(s.phase),
{
    hide(spec_step);
    if let Some((l, ty)) = spec_expected(s.phase) {
        if l == level {
            let buf = spec_reader(s, level);
            if let Ok(Some(n)) = rfc_next_message(buf, ty) {
                let s1 = spec_with_reader(s, level, buf.skip(n as int));
                let m = buf.take(n as int);
                lemma_step_facts(cfg, tp, s1, m, rand);
                if let Ok((s2, evs)) = spec_step(cfg, tp, s1, m, rand) {
                    lemma_drain_readers(cfg, tp, s2, level, rand, acc + evs);
                }
            }
        }
    }
}

// =============================================================================
// Exec
// =============================================================================

pub struct ServerHandshake<'a> {
    cfg: &'a ServerConfig,
    local_tp: Vec<u8>,
    phase: SpecPhase,
    initial: HsReader,
    handshake: HsReader,
    transcript: Vec<u8>,
    ch1: Option<ClientHello>,
    client_vd: [u8; 32],
    err: u64,
}

impl<'a> View for ServerHandshake<'a> {
    type V = SpecServerHs;

    closed spec fn view(&self) -> SpecServerHs {
        SpecServerHs {
            phase: self.phase,
            initial: self.initial@,
            handshake: self.handshake@,
            transcript: self.transcript@,
            ch1: match self.ch1 {
                Some(c) => Some(c@),
                None => None,
            },
            client_vd: self.client_vd@,
            err: self.err,
        }
    }
}

proof fn lemma_or_xor(acc: u8, x: u8, y: u8)
    ensures
        ((acc | (x ^ y)) == 0) <==> (acc == 0 && x == y),
{
    assert(((acc | (x ^ y)) == 0) <==> (acc == 0 && x == y)) by (bit_vector);
}

//= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.4
//# Recipients of Finished messages MUST verify that the contents are
//# correct and if incorrect MUST terminate the connection with a
//# "decrypt_error" alert.
/// Constant-time style: every byte is read, no early exit (TRUSTED.md: the timing is unproven).
fn ct_eq32(a: &[u8; 32], b: &[u8; 32]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    let mut acc: u8 = 0;
    let mut i: usize = 0;
    while i < 32
        invariant
            i <= 32,
            (acc == 0) <==> (forall|j: int| 0 <= j < i ==> a@[j] == b@[j]),
        decreases 32 - i,
    {
        proof {
            lemma_or_xor(acc, a@[i as int], b@[i as int]);
        }
        acc = acc | (a[i] ^ b[i]);
        i += 1;
    }
    if acc == 0 {
        assert(a@ =~= b@);
    } else {
        let ghost j = choose|j: int| 0 <= j < 32 && a@[j] != b@[j];
        assert(a@[j] != b@[j]);
    }
    acc == 0
}

fn eq_bytes(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a@.len(),
            a@.len() == b@.len(),
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases a@.len() - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    assert(a@ =~= b@);
    true
}

fn eq_u16s(a: &Vec<u16>, b: &Vec<u16>) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a@.len(),
            a@.len() == b@.len(),
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases a@.len() - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    assert(a@ =~= b@);
    true
}

fn eq_opt_u16s(a: &Option<Vec<u16>>, b: &Option<Vec<u16>>) -> (r: bool)
    ensures
        r == (a.deep_view() == b.deep_view()),
{
    match (a, b) {
        (Some(x), Some(y)) => {
            assert(x.deep_view() =~= x@);
            assert(y.deep_view() =~= y@);
            eq_u16s(x, y)
        },
        (None, None) => true,
        _ => false,
    }
}

fn eq_opt_bytes(a: &Option<Vec<u8>>, b: &Option<Vec<u8>>) -> (r: bool)
    ensures
        r == (a.deep_view() == b.deep_view()),
{
    match (a, b) {
        (Some(x), Some(y)) => {
            assert(x.deep_view() =~= x@);
            assert(y.deep_view() =~= y@);
            eq_bytes(x.as_slice(), y.as_slice())
        },
        (None, None) => true,
        _ => false,
    }
}

fn eq_lists(a: &Vec<Vec<u8>>, b: &Vec<Vec<u8>>) -> (r: bool)
    ensures
        r == (a.deep_view() == b.deep_view()),
{
    if a.len() != b.len() {
        assert(a.deep_view().len() != b.deep_view().len());
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a@.len(),
            a@.len() == b@.len(),
            forall|k: int| 0 <= k < i ==> a.deep_view()[k] == b.deep_view()[k],
        decreases a@.len() - i,
    {
        assert(a.deep_view()[i as int] == a@[i as int]@);
        assert(b.deep_view()[i as int] == b@[i as int]@);
        if !eq_bytes(a[i].as_slice(), b[i].as_slice()) {
            assert(a.deep_view()[i as int] != b.deep_view()[i as int]);
            return false;
        }
        i += 1;
    }
    assert(a.deep_view() =~= b.deep_view());
    true
}

fn eq_opt_lists(a: &Option<Vec<Vec<u8>>>, b: &Option<Vec<Vec<u8>>>) -> (r: bool)
    ensures
        r == (a.deep_view() == b.deep_view()),
{
    match (a, b) {
        (Some(x), Some(y)) => eq_lists(x, y),
        (None, None) => true,
        _ => false,
    }
}

fn same_except_shares(a: &ClientHello, b: &ClientHello) -> (r: bool)
    ensures
        r == spec_same_except_shares(a@, b@),
{
    eq_bytes(a.random.as_slice(), b.random.as_slice()) && eq_bytes(
        a.legacy_session_id.as_slice(),
        b.legacy_session_id.as_slice(),
    ) && eq_u16s(&a.cipher_suites, &b.cipher_suites) && eq_u16s(&a.versions, &b.versions)
        && eq_opt_u16s(&a.groups, &b.groups) && eq_u16s(&a.sig_algs, &b.sig_algs) && eq_opt_u16s(
        &a.sig_algs_cert,
        &b.sig_algs_cert,
    ) && eq_opt_lists(&a.alpn, &b.alpn) && eq_opt_bytes(&a.server_name, &b.server_name)
        && eq_bytes(a.transport_params.as_slice(), b.transport_params.as_slice())
}

fn expected(p: &SpecPhase) -> (r: Option<(Level, u8)>)
    ensures
        r == spec_expected(*p),
{
    match p {
        SpecPhase::Start => Some((Level::Initial, HT_CLIENT_HELLO)),
        SpecPhase::HrrSent => Some((Level::Initial, HT_CLIENT_HELLO)),
        SpecPhase::WaitFinished => Some((Level::Handshake, HT_FINISHED)),
        _ => None,
    }
}

fn same_level(a: Level, b: Level) -> (r: bool)
    ensures
        r == (a == b),
{
    match (a, b) {
        (Level::Initial, Level::Initial) => true,
        (Level::Handshake, Level::Handshake) => true,
        (Level::OneRtt, Level::OneRtt) => true,
        _ => false,
    }
}

proof fn lemma_hrr_len(sid: Seq<u8>)
    requires
        sid.len() <= 32,
    ensures
        spec_hello_retry_request_bytes(sid, SECP256R1).len() <= 0x100,
{
    let sel = spec_be_bytes(SECP256R1 as nat, 2);
    assert(sel.len() == 2);
    lemma_ext_len(EXT_KEY_SHARE, sel);
    lemma_ext_len(EXT_SUPPORTED_VERSIONS, spec_be_bytes(TLS13 as nat, 2));
    assert(spec_be_bytes(TLS13 as nat, 2).len() == 2);
    let exts = spec_ext_bytes(EXT_KEY_SHARE, sel) + spec_sh_versions_bytes();
    assert(spec_be_bytes(LEGACY_VERSION as nat, 2).len() == 2);
    assert(spec_be_bytes(TLS_AES_128_GCM_SHA256 as nat, 2).len() == 2);
    lemma_vlen(32, sid);
    lemma_vlen(0xffff, exts);
    lemma_hs_len(HT_SERVER_HELLO, spec_hello_body_bytes(HRR_RANDOM@, sid, exts));
}

fn push_event(acc: &mut Vec<TlsEvent>, e: TlsEvent)
    ensures
        final(acc).deep_view() == old(acc).deep_view() + seq![e.deep_view()],
{
    let ghost e0 = e.deep_view();
    acc.push(e);
    assert(final(acc).deep_view() =~= old(acc).deep_view() + seq![e0]);
}

fn append_events(acc: &mut Vec<TlsEvent>, evs: &mut Vec<TlsEvent>)
    ensures
        final(acc).deep_view() == old(acc).deep_view() + old(evs).deep_view(),
        final(acc)@.len() == old(acc)@.len() + old(evs)@.len(),
{
    let ghost a = acc.deep_view();
    let ghost b = evs.deep_view();
    acc.append(evs);
    assert(final(acc).deep_view() =~= a + b);
}

impl<'a> ServerHandshake<'a> {
    pub closed spec fn cfg_view(&self) -> Seq<SpecCertChain> {
        self.cfg@
    }

    pub closed spec fn tp_view(&self) -> Seq<u8> {
        self.local_tp@
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.cfg_view().len() >= 1
        &&& forall|i: int| 0 <= i < self.cfg_view().len() ==> chain_wf(#[trigger] self.cfg_view()[i])
        &&& self.tp_view().len() <= 1024
        &&& self@.transcript.len() <= 0x2_0000
        &&& spec_hs_inv(self@)
    }

    pub fn new(cfg: &'a ServerConfig, local_tp: Vec<u8>) -> (r: ServerHandshake<'a>)
        requires
            cfg.wf(),
            local_tp@.len() <= 1024,
        ensures
            r.wf(),
            r@.phase is Start,
            r@.initial.len() == 0,
            r@.handshake.len() == 0,
            r.cfg_view() == cfg@,
            r.tp_view() == local_tp@,
    {
        ServerHandshake {
            cfg,
            local_tp,
            phase: SpecPhase::Start,
            initial: HsReader::new(),
            handshake: HsReader::new(),
            transcript: Vec::new(),
            ch1: None,
            client_vd: [0u8; 32],
            err: 0,
        }
    }

    /// Bytes left at `level` that no expected message will consume (RFC 9001 §4.1.3, 4c).
    pub fn pending(&self, level: Level) -> (r: bool)
        ensures
            r == !(spec_reader(self@, level).len() == 0),
    {
        match level {
            Level::Initial => !self.initial.is_empty(),
            Level::Handshake => !self.handshake.is_empty(),
            Level::OneRtt => false,
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc8446#appendix-E.5
    //# In order to allow applications to implement this kind of
    //# processing, TLS implementations MUST provide a way for the
    //# application to determine if the handshake has completed.
    pub fn is_complete(&self) -> (r: bool)
        ensures
            r == (self@.phase is Complete),
    {
        match self.phase {
            SpecPhase::Complete => true,
            _ => false,
        }
    }

    // Secrets are dropped from the state here; memory is not zeroised (TRUSTED: secret lifetime).
    fn fail(&mut self, e: u64)
        ensures
            final(self)@ == spec_failed(old(self)@, e),
            final(self).cfg == old(self).cfg,
            final(self).local_tp == old(self).local_tp,
    {
        self.phase = SpecPhase::Failed;
        self.err = e;
        self.transcript = Vec::new();
        self.ch1 = None;
        self.client_vd = [0u8; 32];
        assert(self.transcript@ =~= seq![]);
        assert(self.client_vd@ =~= zeros32());
    }

    /// `m` is one complete message of the expected type, header included.
    fn step(&mut self, m: &Vec<u8>, rand: &[u8; TLS_RAND_LEN], acc: &mut Vec<TlsEvent>) -> (r: Result<
        (),
        u64,
    >)
        requires
            old(self).wf_core(),
            spec_expected(old(self)@.phase) is Some,
            4 <= m@.len() <= 4 + MAX_HS_BODY,
        ensures
            final(self).cfg == old(self).cfg,
            final(self).local_tp == old(self).local_tp,
            final(self)@.initial == old(self)@.initial,
            final(self)@.handshake == old(self)@.handshake,
            match spec_step(old(self).cfg@, old(self).local_tp@, old(self)@, m@, rand@) {
                Err(e) => r == Err::<(), u64>(e),
                Ok((s2, evs)) => (r is Ok && final(self)@ == s2 && final(acc).deep_view() == old(
                    acc,
                ).deep_view() + evs) || (r == Err::<(), u64>(ALERT_INTERNAL_ERROR)
                    && s2.phase is WaitFinished),
            },
            r is Ok ==> final(self).wf_core(),
    {
        hide(spec_flight);
        hide(rfc_client_hello);
        hide(rfc_negotiate);
        hide(spec_message_hash);
        assert(MAX_HS_BODY == 0x1_0000) by (compute);
        let ghost s = self@;
        let ghost cfg = self.cfg@;
        let ghost tp = self.local_tp@;
        let body = slice_subrange(m.as_slice(), 4, m.len());
        assert(body@ =~= m@.skip(4));
        match self.phase {
            SpecPhase::WaitFinished => {
                let vd = match parse_finished(body) {
                    Ok(vd) => vd,
                    Err(e) => return Err(e),
                };
                if !ct_eq32(&vd, &self.client_vd) {
                    return Err(ALERT_DECRYPT_ERROR);
                }
                self.phase = SpecPhase::Complete;
                self.client_vd = [0u8; 32];
                assert(self.client_vd@ =~= zeros32());
                push_event(acc, TlsEvent::Complete);
                Ok(())
            },
            SpecPhase::Start | SpecPhase::HrrSent => {
                let ch = match parse_client_hello(body) {
                    Ok(ch) => ch,
                    Err(e) => return Err(e),
                };
                let after_hrr = match &self.ch1 {
                    Some(ch1) => {
                        if !same_except_shares(ch1, &ch) {
                            return Err(ALERT_ILLEGAL_PARAMETER);
                        }
                        true
                    },
                    None => false,
                };
                let choice = match negotiate(&ch, self.cfg, after_hrr) {
                    Ok(c) => c,
                    Err(e) => return Err(e),
                };
                //= https://www.rfc-editor.org/rfc/rfc8446#section-4.2
                //# Implementations MUST NOT send extension responses if the remote
                //# endpoint did not send the corresponding extension requests, with the
                //# exception of the "cookie" extension in the HelloRetryRequest.
                proof {
                    theorem_no_unsolicited(body@, self.cfg@, after_hrr);
                }
                match choice {
                    Choice::Retry => {
                        //= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.4
                        //# If a client receives a second
                        //# HelloRetryRequest in the same connection (i.e., where the ClientHello
                        //# was itself in response to a HelloRetryRequest), it MUST abort the
                        //# handshake with an "unexpected_message" alert.
                        // server side: never sends a second HRR (`theorem_server_no_second_hrr`); a CH2
                        // that would need one is illegal_parameter
                        if after_hrr {
                            return Err(ALERT_ILLEGAL_PARAMETER);
                        }
                        proof {
                            lemma_client_hello_ok(body@);
                            lemma_hrr_len(ch@.legacy_session_id);
                        }
                        let mut hrr: Vec<u8> = Vec::new();
                        assert(!spec_reserved_group(SECP256R1)) by (compute);
                        serialize_hello_retry_request(
                            ch.legacy_session_id.as_slice(),
                            SECP256R1,
                            &mut hrr,
                        );
                        let mut t = message_hash(m.as_slice());
                        t.extend_from_slice(hrr.as_slice());
                        assert(t@ =~= spec_message_hash(m@) + hrr@);
                        self.transcript = t;
                        self.ch1 = Some(ch);
                        self.phase = SpecPhase::HrrSent;
                        push_event(acc, TlsEvent::Send { level: Level::Initial, data: hrr });
                        Ok(())
                    },
                    Choice::Proceed { chain, scheme, share } => {
                        //= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.4
                        //# Servers MUST ensure that they negotiate the
                        //# same cipher suite when receiving a conformant updated ClientHello (if
                        //# the server selects the cipher suite as the first step in the
                        //# negotiation, then this will happen automatically).
                        // One suite, and CH2's cipher_suites equal CH1's (`spec_same_except_shares`).
                        // The `usize` bounds theorem_proceed_facts needs.
                        let _ = self.cfg.chains.len();
                        match &ch.key_shares {
                            Some(ks) => {
                                let _ = ks.len();
                            },
                            None => {},
                        }
                        proof {
                            theorem_proceed_facts(ch@, self.cfg@, after_hrr);
                        }
                        let mut t0: Vec<u8> = Vec::new();
                        core::mem::swap(&mut t0, &mut self.transcript);
                        t0.extend_from_slice(m.as_slice());
                        let ghost t = t0@;
                        proof {
                            if !after_hrr {
                                assert(t =~= m@);
                            }
                            // spec_step's Proceed arm, with these arguments to spec_flight:
                            assert(rfc_client_hello(m@.skip(4)) == Ok::<SpecClientHello, u64>(ch@));
                            assert(t == (if after_hrr { s.transcript + m@ } else { m@ }));
                        }
                        let (mut evs, vd) = match build_flight(
                            self.cfg,
                            self.local_tp.as_slice(),
                            t0,
                            &ch,
                            chain,
                            scheme,
                            share,
                            rand,
                        ) {
                            Ok(x) => x,
                            Err(e) => return Err(e),
                        };
                        self.phase = SpecPhase::WaitFinished;
                        self.ch1 = None;
                        self.client_vd = vd;
                        proof {
                            assert(self@.transcript == Seq::<u8>::empty());
                        }
                        append_events(acc, &mut evs);
                        Ok(())
                    },
                }
            },
            _ => Err(ALERT_UNEXPECTED_MESSAGE),
        }
    }

    spec fn wf_core(&self) -> bool {
        &&& self.cfg.wf()
        &&& self.local_tp@.len() <= 1024
        &&& self@.transcript.len() <= 0x2_0000
        &&& self@.phase is HrrSent ==> self@.transcript.len() <= 0x1000
        &&& !(self@.phase is HrrSent) ==> self@.transcript.len() == 0
        &&& (self@.phase is HrrSent <==> self@.ch1 is Some)
    }

    /// Feeds CRYPTO data received at `level`. Events are appended to `ev` only when the call
    /// succeeds; a failure is final (`Failed` returns its first error from then on).
    pub fn on_crypto(
        &mut self,
        level: Level,
        data: &[u8],
        rand: &[u8; TLS_RAND_LEN],
        ev: &mut Vec<TlsEvent>,
    ) -> (r: Result<(), u64>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).cfg_view() == old(self).cfg_view(),
            final(self).tp_view() == old(self).tp_view(),
            ({
                let (s2, res) = spec_on_crypto(
                    old(self).cfg_view(),
                    old(self).tp_view(),
                    old(self)@,
                    level,
                    data@,
                    rand@,
                );
                &&& res matches Err(e) ==> r == Err::<(), u64>(e) && final(self)@ == s2 && final(ev)@
                    == old(ev)@
                &&& res matches Ok(evs) ==> (r is Ok && final(self)@ == s2 && final(ev).deep_view()
                    == old(ev).deep_view() + evs) || (r == Err::<(), u64>(ALERT_INTERNAL_ERROR)
                    && final(self)@ == spec_failed(s2, ALERT_INTERNAL_ERROR) && final(ev)@ == old(ev)@)
            }),
    {
        hide(spec_step);
        let ghost cfg = self.cfg@;
        let ghost tp = self.local_tp@;
        let ghost s_in = self@;
        proof {
            theorem_reader_bound(cfg, tp, s_in, level, data@, rand@);
        }
        if let SpecPhase::Failed = self.phase {
            return Err(self.err);
        }
        let ok_level = match expected(&self.phase) {
            Some((l, _)) => same_level(l, level),
            None => false,
        };
        if data.len() > 0 && !ok_level {
            self.fail(ALERT_UNEXPECTED_MESSAGE);
            return Err(ALERT_UNEXPECTED_MESSAGE);
        }
        match level {
            Level::Initial => self.initial.push(data),
            Level::Handshake => self.handshake.push(data),
            Level::OneRtt => {},
        }
        assert(self@ == spec_with_reader(s_in, level, spec_reader(s_in, level) + data@)) by {
            if level is OneRtt {
                assert(self@.initial == s_in.initial);
            }
        }
        let ghost target = spec_drain(cfg, tp, self@, level, rand@, seq![]);
        let mut acc: Vec<TlsEvent> = Vec::new();
        assert(acc.deep_view() =~= Seq::<SpecTlsEvent>::empty());
        loop
            invariant
                self.wf_core(),
                self.cfg@ == cfg,
                self.local_tp@ == tp,
                self.cfg == old(self).cfg,
                self.local_tp == old(self).local_tp,
                spec_drain(cfg, tp, self@, level, rand@, acc.deep_view()) == target,
                target == spec_on_crypto(cfg, tp, s_in, level, data@, rand@),
                s_in == old(self)@,
                cfg == old(self).cfg_view(),
                tp == old(self).tp_view(),
                spec_readers_ok(target.0),
                ev@ == old(ev)@,
                !(self@.phase is Failed),
            ensures
                target == (self@, Ok::<Seq<SpecTlsEvent>, u64>(acc.deep_view())),
            decreases spec_rank(self@.phase),
        {
            let ghost s = self@;
            let ty = match expected(&self.phase) {
                Some((l, ty)) => {
                    if !same_level(l, level) {
                        break ;
                    }
                    ty
                },
                None => break ,
            };
            let next = match level {
                Level::Initial => self.initial.next_message(ty),
                Level::Handshake => self.handshake.next_message(ty),
                Level::OneRtt => Ok(None),
            };
            let m = match next {
                Err(e) => {
                    self.fail(e);
                    return Err(e);
                },
                Ok(None) => break ,
                Ok(Some(m)) => m,
            };
            let ghost n = m@.len();
            let ghost s1 = self@;
            assert(s1 == spec_with_reader(s, level, spec_reader(s, level).skip(n as int)));
            assert(m@ == spec_reader(s, level).take(n as int));
            let ghost a0 = acc.deep_view();
            proof {
                lemma_step_facts(cfg, tp, s1, m@, rand@);
            }
            match self.step(&m, rand, &mut acc) {
                Ok(()) => {},
                Err(e) => {
                    proof {
                        // build_flight's Err where the spec has a flight, which its ensures still allows for RSA keys: the spec drain
                        // stops there (nothing is expected at Initial any more), so `res` is Ok.
                        if let Ok((s2, evs)) = spec_step(cfg, tp, s1, m@, rand@) {
                            assert(level is Initial);
                            assert(spec_drain(cfg, tp, s2, level, rand@, a0 + evs) == (s2, Ok::<Seq<SpecTlsEvent>, u64>(a0 + evs)));
                        }
                    }
                    let ghost s_err = self@;
                    self.fail(e);
                    proof {
                        if let Ok((s2, evs)) = spec_step(cfg, tp, s1, m@, rand@) {
                            assert(s_err.initial == s2.initial && s_err.handshake == s2.handshake);
                            assert(self@ == spec_failed(s2, ALERT_INTERNAL_ERROR));
                        }
                    }
                    return Err(e);
                },
            }
        }
        append_events(ev, &mut acc);
        Ok(())
    }
}

} // verus!
