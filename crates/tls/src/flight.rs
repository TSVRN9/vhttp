//! The server flight (RFC 8446 §2, §4.1.3, §4.3.1, §4.4.2, §4.4.3, §4.4.4): ServerHello at the
//! Initial level, then EncryptedExtensions, Certificate, CertificateVerify and Finished at the
//! Handshake level, with the handshake and 1-RTT traffic secrets as events.
//!
//! There is no 0-RTT level: 0-RTT is never accepted (RFC 9114 §7.2.4.2).
use crate::client_hello::*;
use crate::codes::*;
use crate::config::*;
#[allow(unused_imports)] // spec-only under plain cargo
use crate::ext::*;
#[allow(unused_imports)]
use crate::handshake::*;
#[allow(unused_imports)]
use crate::hkdf_label::*;
#[allow(unused_imports)]
use crate::pl::*;
use crate::schedule::*;
use crate::server_msgs::*;
use crate::sign::*;
#[allow(unused_imports)]
use crypto::hmac::*;
use crypto::p256::*;
use crypto::sha256::*;
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Level {
    Initial,
    Handshake,
    OneRtt,
}

#[derive(Debug, PartialEq, Eq)]
pub enum TlsEvent {
    Send { level: Level, data: Vec<u8> },
    Secrets { level: Level, client: [u8; 32], server: [u8; 32] },
    PeerParams(Vec<u8>),
    Complete,
}

pub enum SpecTlsEvent {
    Send { level: Level, data: Seq<u8> },
    Secrets { level: Level, client: Seq<u8>, server: Seq<u8> },
    PeerParams(Seq<u8>),
    Complete,
}

impl DeepView for TlsEvent {
    type V = SpecTlsEvent;

    open spec fn deep_view(&self) -> SpecTlsEvent {
        match self {
            TlsEvent::Send { level, data } => SpecTlsEvent::Send { level: *level, data: data@ },
            TlsEvent::Secrets { level, client, server } => SpecTlsEvent::Secrets {
                level: *level,
                client: client@,
                server: server@,
            },
            TlsEvent::PeerParams(p) => SpecTlsEvent::PeerParams(p@),
            TlsEvent::Complete => SpecTlsEvent::Complete,
        }
    }
}

pub struct SpecFlight {
    pub events: Seq<SpecTlsEvent>,
    pub client_vd: Seq<u8>,
}

/// `t0` is the transcript up to and including the ClientHello being answered: `CH`, or
/// `message_hash(CH1) || HRR || CH2`. `rand` is `TLS_RAND_LEN` bytes: [0..32] the ServerHello
/// random, [32..64] the ECDHE scalar, [64..96] the PSS salt. The order is the requirement.
pub open spec fn spec_flight(
    cfg: Seq<SpecCertChain>,
    tp: Seq<u8>,
    t0: Seq<u8>,
    ch: SpecClientHello,
    chain: nat,
    scheme: u16,
    share: nat,
    rand: Seq<u8>,
) -> Result<SpecFlight, u64> {
    let d = rand.subrange(32, 64);
    let peer = ch.key_shares.unwrap()[share as int].key_exchange;
    match spec_p256_public_key(d) {
        // ponytail: an out-of-range scalar has probability ≈ 2^-32; internal_error, not a resample
        None => Err(ALERT_INTERNAL_ERROR),
        Some(pk) => match spec_p256_ecdh(d, peer) {
            None => Err(ALERT_ILLEGAL_PARAMETER),
            Some(z) => if z == zeros32() {
                Err(ALERT_ILLEGAL_PARAMETER)
            } else {
                let sh = spec_server_hello_bytes(
                    rand.subrange(0, 32),
                    ch.legacy_session_id,
                    SECP256R1,
                    pk,
                );
                let t1 = t0 + sh;
                let hs = spec_handshake_secret(z);
                let c_hs = spec_derive_secret(hs, LABEL_C_HS@, t1);
                let s_hs = spec_derive_secret(hs, LABEL_S_HS@, t1);
                let ee = spec_encrypted_extensions_bytes(tp);
                let cert = spec_certificate_bytes(cfg[chain as int].der);
                let t2 = t1 + ee + cert;
                match spec_cv_signature(
                    cfg[chain as int].key,
                    spec_sha256(t2),
                    rand.subrange(64, 96),
                ) {
                    None => Err(ALERT_INTERNAL_ERROR),
                    Some(sig) => {
                        let cv = spec_certificate_verify_bytes(scheme, sig);
                        let t3 = t2 + cv;
                        let fin = spec_finished_bytes(spec_verify_data(s_hs, t3));
                        let t4 = t3 + fin;
                        let m = spec_master_secret(hs);
                        Ok(
                            SpecFlight {
                                events: seq![
                                    SpecTlsEvent::PeerParams(ch.transport_params),
                                    SpecTlsEvent::Send { level: Level::Initial, data: sh },
                                    SpecTlsEvent::Secrets {
                                        level: Level::Handshake,
                                        client: c_hs,
                                        server: s_hs,
                                    },
                                    SpecTlsEvent::Send {
                                        level: Level::Handshake,
                                        data: ee + cert + cv + fin,
                                    },
                                    SpecTlsEvent::Secrets {
                                        level: Level::OneRtt,
                                        client: spec_derive_secret(m, LABEL_C_AP@, t4),
                                        server: spec_derive_secret(m, LABEL_S_AP@, t4),
                                    },
                                ],
                                client_vd: spec_verify_data(c_hs, t4),
                            },
                        )
                    },
                }
            },
        },
    }
}

// =============================================================================
// Theorems
// =============================================================================

/// The flight's shape. No `Send { OneRtt }` exists, and `Secrets { Handshake }` precedes the
/// only `Send { Handshake }`: the server handshake traffic secret is derived before
/// EncryptedExtensions is sent.
pub proof fn theorem_flight_order(
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
        rand.len() == TLS_RAND_LEN,
        ch.key_shares matches Some(ks) && share < ks.len() && ks[share as int].group == SECP256R1,
    ensures
        ({
            let f = spec_flight(cfg, tp, t0, ch, chain, scheme, share, rand)->Ok_0;
            &&& f.events.len() == 5
            &&& f.events[0] == SpecTlsEvent::PeerParams(ch.transport_params)
            &&& f.events[1] matches SpecTlsEvent::Send { level: Level::Initial, data }
                && data.subrange(6, 38) == rand.subrange(0, 32) && exists|pk: Seq<u8>|
                data == spec_server_hello_bytes(
                    rand.subrange(0, 32),
                    ch.legacy_session_id,
                    SECP256R1,
                    pk,
                )
            &&& f.events[2] matches SpecTlsEvent::Secrets { level: Level::Handshake, .. }
            &&& f.events[3] matches SpecTlsEvent::Send { level: Level::Handshake, .. }
            &&& f.events[4] matches SpecTlsEvent::Secrets { level: Level::OneRtt, .. }
            &&& forall|i: int|
                0 <= i < 5 ==> !(#[trigger] f.events[i] matches SpecTlsEvent::Send { level: Level::OneRtt, .. })
            &&& forall|i: int|
                0 <= i < 5 && (#[trigger] f.events[i] matches SpecTlsEvent::Send { level: Level::Handshake, .. })
                    ==> i == 3
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
    let d = rand.subrange(32, 64);
    let pk = spec_p256_public_key(d).unwrap();
    let random = rand.subrange(0, 32);
    lemma_sh_random(random, ch.legacy_session_id, pk);
}

/// The ServerHello random sits at [6..38], after the 4-byte header and legacy_version.
proof fn lemma_sh_random(random: Seq<u8>, sid: Seq<u8>, pk: Seq<u8>)
    requires
        random.len() == 32,
    ensures
        spec_server_hello_bytes(random, sid, SECP256R1, pk).subrange(6, 38) == random,
{
    let sh = spec_server_hello_bytes(random, sid, SECP256R1, pk);
    let exts = spec_sh_key_share_bytes(SECP256R1, pk) + spec_sh_versions_bytes();
    let body = spec_hello_body_bytes(random, sid, exts);
    assert(spec_be_bytes(LEGACY_VERSION as nat, 2).len() == 2);
    assert(spec_be_bytes(body.len(), 3).len() == 3);
    assert(body.subrange(2, 34) =~= random);
    assert(sh =~= seq![HT_SERVER_HELLO] + (spec_be_bytes(body.len(), 3) + body));
    assert(sh.subrange(6, 38) =~= body.subrange(2, 34));
}

// =============================================================================
// Lengths (the MAX_INPUT_LEN bound on every transcript hash)
// =============================================================================

pub(crate) proof fn lemma_vlen(ceiling: nat, c: Seq<u8>)
    ensures
        spec_vec_bytes(ceiling, c).len() == len_width(ceiling) + c.len(),
        len_width(ceiling) <= 3,
{
    assert(spec_be_bytes(c.len(), len_width(ceiling)).len() == len_width(ceiling));
}

pub(crate) proof fn lemma_hs_len(ty: u8, body: Seq<u8>)
    ensures
        spec_hs_bytes(ty, body).len() == 4 + body.len(),
{
    lemma_vlen(0xff_ffff, body);
}

pub(crate) proof fn lemma_ext_len(ty: u16, data: Seq<u8>)
    ensures
        spec_ext_bytes(ty, data).len() == 4 + data.len(),
{
    assert(spec_be_bytes(ty as nat, 2).len() == 2);
    lemma_vlen(0xffff, data);
}

proof fn lemma_sh_len(random: Seq<u8>, sid: Seq<u8>, kx: Seq<u8>)
    requires
        random.len() == 32,
        sid.len() <= 32,
        kx.len() <= 256,
    ensures
        spec_server_hello_bytes(random, sid, SECP256R1, kx).len() <= 0x1000,
{
    assert(spec_be_bytes(SECP256R1 as nat, 2).len() == 2);
    lemma_vlen(0xffff, kx);
    lemma_ext_len(EXT_KEY_SHARE, spec_be_bytes(SECP256R1 as nat, 2) + spec_vec_bytes(0xffff, kx));
    lemma_ext_len(EXT_SUPPORTED_VERSIONS, spec_be_bytes(TLS13 as nat, 2));
    assert(spec_be_bytes(TLS13 as nat, 2).len() == 2);
    let exts = spec_sh_key_share_bytes(SECP256R1, kx) + spec_sh_versions_bytes();
    assert(spec_be_bytes(LEGACY_VERSION as nat, 2).len() == 2);
    assert(spec_be_bytes(TLS_AES_128_GCM_SHA256 as nat, 2).len() == 2);
    lemma_vlen(32, sid);
    lemma_vlen(0xffff, exts);
    lemma_hs_len(HT_SERVER_HELLO, spec_hello_body_bytes(random, sid, exts));
}

proof fn lemma_ee_len(tp: Seq<u8>)
    requires
        tp.len() <= 1024,
    ensures
        spec_encrypted_extensions_bytes(tp).len() <= 0x1000,
{
    let names = spec_vec_bytes(255, H3_ALPN@);
    lemma_vlen(255, H3_ALPN@);
    lemma_vlen(0xffff, names);
    lemma_ext_len(EXT_ALPN, spec_vec_bytes(0xffff, names));
    lemma_ext_len(EXT_QUIC_TRANSPORT_PARAMETERS, tp);
    let exts = spec_ext_bytes(EXT_ALPN, spec_vec_bytes(0xffff, names)) + spec_ext_bytes(
        EXT_QUIC_TRANSPORT_PARAMETERS,
        tp,
    );
    lemma_vlen(0xffff, exts);
    lemma_hs_len(HT_ENCRYPTED_EXTENSIONS, spec_vec_bytes(0xffff, exts));
}

proof fn lemma_cert_len(chain: Seq<Seq<u8>>)
    requires
        cert_chain_ok(chain),
    ensures
        spec_certificate_bytes(chain).len() <= 0x100_0004,
{
    let entries = spec_cert_entries_bytes(chain);
    lemma_vlen(255, seq![]);
    lemma_vlen(0xff_ffff, entries);
    lemma_hs_len(HT_CERTIFICATE, spec_vec_bytes(255, seq![]) + spec_vec_bytes(0xff_ffff, entries));
}

proof fn lemma_fin_len(vd: Seq<u8>)
    ensures
        spec_finished_bytes(vd).len() == 4 + vd.len(),
{
    lemma_hs_len(HT_FINISHED, vd);
}

proof fn lemma_sig_len(key: SpecSigningKey, th: Seq<u8>, salt: Seq<u8>, sig: Seq<u8>)
    requires
        spec_cv_signature(key, th, salt) == Some(sig),
    ensures
        sig.len() <= 0xffff,
{
}

proof fn lemma_cv_len(scheme: u16, sig: Seq<u8>)
    requires
        sig.len() <= 0xffff,
    ensures
        spec_certificate_verify_bytes(scheme, sig).len() <= 0x1_0008,
{
    assert(spec_be_bytes(scheme as nat, 2).len() == 2);
    lemma_vlen(0xffff, sig);
    lemma_hs_len(
        HT_CERTIFICATE_VERIFY,
        spec_be_bytes(scheme as nat, 2) + spec_vec_bytes(0xffff, sig),
    );
}

// =============================================================================
// Exec
// =============================================================================

fn take32(b: &[u8; TLS_RAND_LEN], off: usize) -> (r: [u8; 32])
    requires
        off + 32 <= TLS_RAND_LEN,
    ensures
        r@ == b@.subrange(off as int, off + 32),
{
    let mut r = [0u8; 32];
    let mut i: usize = 0;
    while i < 32
        invariant
            i <= 32,
            off + 32 <= TLS_RAND_LEN,
            b@.len() == TLS_RAND_LEN,
            forall|j: int| 0 <= j < i ==> r@[j] == b@[off + j],
        decreases 32 - i,
    {
        r[i] = b[off + i];
        i += 1;
    }
    assert(r@ =~= b@.subrange(off as int, off + 32));
    r
}

fn is_zero(z: &[u8; 32]) -> (r: bool)
    ensures
        r == (z@ == zeros32()),
{
    let mut i: usize = 0;
    while i < 32
        invariant
            i <= 32,
            forall|j: int| 0 <= j < i ==> z@[j] == 0,
        decreases 32 - i,
    {
        if z[i] != 0 {
            assert(z@[i as int] != zeros32()[i as int]);
            return false;
        }
        i += 1;
    }
    assert(z@ =~= zeros32());
    true
}

fn append(t: &mut Vec<u8>, m: &[u8])
    ensures
        final(t)@ == old(t)@ + m@,
{
    t.extend_from_slice(m);
    assert(final(t)@ =~= old(t)@ + m@);
}

/// `(chain, scheme, share)` is a `Choice::Proceed` from `negotiate` (the facts of
/// `theorem_proceed_facts`). Returns the events and the client Finished verify_data to expect.
pub fn build_flight(
    cfg: &ServerConfig,
    local_tp: &[u8],
    t0: Vec<u8>,
    ch: &ClientHello,
    chain: usize,
    scheme: u16,
    share: usize,
    rand: &[u8; TLS_RAND_LEN],
) -> (r: Result<(Vec<TlsEvent>, [u8; 32]), u64>)
    requires
        cfg.wf(),
        local_tp@.len() <= 1024,
        t0@.len() <= 0x2_0000,
        exists|b: Seq<u8>| rfc_client_hello(b) == Ok::<SpecClientHello, u64>(ch@),
        chain < cfg@.len(),
        scheme == key_scheme(cfg@[chain as int].key),
        ch@.sig_algs.contains(scheme),
        ch@.key_shares matches Some(ks) && share < ks.len() && ks[share as int].group == SECP256R1,
        ch@.alpn matches Some(a) && a.contains(H3_ALPN@),
    ensures
        match spec_flight(cfg@, local_tp@, t0@, ch@, chain as nat, scheme, share as nat, rand@) {
            Err(e) => r == Err::<(Vec<TlsEvent>, [u8; 32]), u64>(e),
            Ok(f) => (r matches Ok((evs, vd)) ==> evs.deep_view() == f.events && vd@ == f.client_vd)
                && (r matches Err(e) ==> e == ALERT_INTERNAL_ERROR),
        },
        // The RSA shim's `None` is one-directional; ECDSA is exact.
        cfg@[chain as int].key is EcdsaP256 ==> (r is Ok <==> spec_flight(
            cfg@,
            local_tp@,
            t0@,
            ch@,
            chain as nat,
            scheme,
            share as nat,
            rand@,
        ) is Ok),
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
    let ghost b = choose|b: Seq<u8>| rfc_client_hello(b) == Ok::<SpecClientHello, u64>(ch@);
    proof {
        lemma_client_hello_ok(b);
    }
    let ks = match &ch.key_shares {
        Some(ks) => ks,
        None => {
            assert(false);
            return Err(ALERT_INTERNAL_ERROR);
        },
    };
    let peer = &ks[share].key_exchange;
    assert(ks.deep_view()[share as int] == ks@[share as int]@);
    let c = &cfg.chains[chain];
    assert(cfg@[chain as int] == c@);
    assert(chain_wf(cfg@[chain as int]));

    //= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.3
    //= type=exception
    //= reason=client-only
    //# Upon receiving a message with type server_hello, implementations MUST
    //# first examine the Random value and, if it matches this value, process
    //# it as described in Section 4.1.4).
    //= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.3
    //= type=exception
    //= reason=client-only
    //# A legacy TLS client performing renegotiation with TLS 1.2 or prior
    //# and which receives a TLS 1.3 ServerHello during renegotiation MUST
    //# abort the handshake with a "protocol_version" alert.
    //= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.3
    //# This structure is
    //# generated by the server and MUST be generated independently of the
    //# ClientHello.random.
    //= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.3
    //# but the remaining bytes MUST be random.
    // The ServerHello random is rand[0..32]; ch.random is never read.
    //= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.3
    //# TLS 1.3 servers which negotiate TLS 1.2 or below in
    //# response to a ClientHello MUST set the last 8 bytes of their Random
    //# value specially in their ServerHello.
    // vacuous: 4a rejects every ClientHello without 0x0304 (protocol_version), so we never negotiate ≤ 1.2
    //= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.3
    //# If negotiating TLS 1.2, TLS 1.3 servers MUST set the last 8 bytes of
    //# their Random value to the bytes:
    // vacuous: 4a rejects every ClientHello without 0x0304 (protocol_version), so we never negotiate ≤ 1.2
    //= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.3
    //# If negotiating TLS 1.1 or below, TLS 1.3 servers MUST, and TLS 1.2
    //# servers SHOULD, set the last 8 bytes of their ServerHello.Random
    //# value to the bytes:
    // vacuous: 4a rejects every ClientHello without 0x0304 (protocol_version), so we never negotiate ≤ 1.2
    let random = take32(rand, 0);
    let d = take32(rand, 32);
    let salt = take32(rand, 64);

    let pk = match p256_public_key(d.as_slice()) {
        Some(pk) => pk,
        None => return Err(ALERT_INTERNAL_ERROR),
    };
    assert(pk.deep_view() =~= pk@);
    // §4.2.8.2 "peers MUST validate": p256_ecdh is None for an invalid peer point.
    //= https://www.rfc-editor.org/rfc/rfc8446#section-7.4.2
    //# leading zeros found in this
    //# octet string MUST NOT be truncated.
    // The shared secret is the full 32-octet x-coordinate, a [u8; 32].
    let z = match p256_ecdh(d.as_slice(), peer.as_slice()) {
        Some(z) => z,
        None => return Err(ALERT_ILLEGAL_PARAMETER),
    };
    assert(z.deep_view() =~= z@);
    //= https://www.rfc-editor.org/rfc/rfc8446#section-7.4.2
    //# Implementations MUST check whether the computed Diffie-Hellman shared
    //# secret is the all-zero value and abort if so, as described in
    //# Section 6 of [RFC7748].
    if is_zero(&z) {
        return Err(ALERT_ILLEGAL_PARAMETER);
    }

    // ServerHello. legacy_session_id_echo is ch.legacy_session_id (empty, 4a).
    //= https://www.rfc-editor.org/rfc/rfc8446#section-2
    //# the server's share MUST
    //# be in the same group as one of the client's shares.
    // `share` indexes a secp256r1 KeyShareEntry (the requires), and ours is secp256r1.
    let mut t = t0;
    let mut sh: Vec<u8> = Vec::new();
    assert(!spec_reserved_group(SECP256R1)) by (compute);
    serialize_server_hello(&random, ch.legacy_session_id.as_slice(), SECP256R1, pk.as_slice(), &mut sh);
    append(&mut t, sh.as_slice());
    proof {
        lemma_sh_len(random@, ch@.legacy_session_id, pk@);
    }
    let ghost t1 = t@;
    let th1 = sha256(t.as_slice());
    let hs = handshake_secrets(&z, &th1);

    let mut data: Vec<u8> = Vec::new();
    //= https://www.rfc-editor.org/rfc/rfc8446#section-4.3.1
    //# In all handshakes, the server MUST send the EncryptedExtensions
    //# message immediately after the ServerHello message.
    //= https://www.rfc-editor.org/rfc/rfc8446#section-4.3.1
    //= type=exception
    //= reason=client-only
    //# The client MUST check EncryptedExtensions for the
    //# presence of any forbidden extensions and if any are found MUST abort
    //# the handshake with an "illegal_parameter" alert.
    let mut ee: Vec<u8> = Vec::new();
    serialize_encrypted_extensions(local_tp, &mut ee);
    append(&mut t, ee.as_slice());
    append(&mut data, ee.as_slice());
    proof {
        lemma_ee_len(local_tp@);
    }
    //= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.2
    //# The server MUST send a Certificate message whenever the agreed-upon
    //# key exchange method uses certificates for authentication
    //= https://www.rfc-editor.org/rfc/rfc8446#appendix-C.5
    //# applications
    //# MUST NOT use TLS in such a way absent explicit configuration or a
    //# specific application profile.
    // Every flight carries Certificate and CertificateVerify.
    //= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.2
    //# The sender's certificate MUST come in the first
    //# CertificateEntry in the list.
    //= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.2
    //# with the exception of the end-entity certificate which
    //# MUST be first.
    // trusted config: der[0] is the end-entity certificate (TRUSTED.md, config row); serialize_certificate keeps the order
    let mut cert: Vec<u8> = Vec::new();
    serialize_certificate(&c.der, &mut cert);
    append(&mut t, cert.as_slice());
    append(&mut data, cert.as_slice());
    proof {
        lemma_cert_len(c.der.deep_view());
    }
    let ghost t2 = t@;
    let th2 = sha256(t.as_slice());

    //= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.3
    //# Servers MUST send this message when authenticating
    //# via a certificate.
    let sig = match sign_cv(&c.key, &th2, &salt) {
        Ok(s) => s,
        Err(e) => return Err(e),
    };
    proof {
        lemma_sig_len(c.key@, th2@, salt@, sig@);
        if c.key@ is EcdsaP256 {
            assert(!spec_reserved_scheme(ECDSA_SECP256R1_SHA256)) by (compute);
        } else {
            assert(!spec_reserved_scheme(RSA_PSS_RSAE_SHA256)) by (compute);
        }
    }
    //= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.3
    //# When sent, this message MUST appear immediately after
    //# the Certificate message and immediately prior to the Finished
    //# message.
    // by construction: CV is appended to `data` right after the Certificate and right before the Finished
    let mut cv: Vec<u8> = Vec::new();
    serialize_certificate_verify(scheme, sig.as_slice(), &mut cv);
    append(&mut t, cv.as_slice());
    append(&mut data, cv.as_slice());
    proof {
        lemma_cv_len(scheme, sig@);
    }
    let ghost t3 = t@;
    let th3 = sha256(t.as_slice());
    let sfin = verify_data(&hs.server, &th3);
    let mut fin: Vec<u8> = Vec::new();
    serialize_finished(&sfin, &mut fin);
    append(&mut t, fin.as_slice());
    append(&mut data, fin.as_slice());
    proof {
        lemma_fin_len(sfin@);
    }
    let th4 = sha256(t.as_slice());
    let master = master_secret(&hs.hs);
    let (c_ap, s_ap) = app_secrets(&master, &th4);
    let cfin = verify_data(&hs.client, &th4);

    //= https://www.rfc-editor.org/rfc/rfc8446#section-4
    //# Protocol messages MUST be sent in the order defined in Section 4.4.1
    //# and shown in the diagrams in Section 2.
    // by construction: SH, then EE, Certificate, CertificateVerify, Finished, in spec_flight's order (theorem_flight_order)
    let mut evs: Vec<TlsEvent> = Vec::new();
    evs.push(TlsEvent::PeerParams(ch.transport_params.clone()));
    evs.push(TlsEvent::Send { level: Level::Initial, data: sh });
    evs.push(TlsEvent::Secrets { level: Level::Handshake, client: hs.client, server: hs.server });
    evs.push(TlsEvent::Send { level: Level::Handshake, data });
    //= https://www.rfc-editor.org/rfc/rfc8446#section-2
    //# Application Data MUST NOT be sent prior to sending the Finished
    //# message
    // The 1-RTT secrets are the last event, after the Finished; 3d sends no 1-RTT packet before
    // on_handshake_complete.
    evs.push(TlsEvent::Secrets { level: Level::OneRtt, client: c_ap, server: s_ap });
    Ok((evs, cfin))
}

} // verus!
