//! The TLS 1.3 key schedule (RFC 8446 §7.1, PSK absent) and the HRR `message_hash` (§4.4.1).
//!
//! No exporter or resumption secret is derived.
//
//= https://www.rfc-editor.org/rfc/rfc8446#section-7.5
//# Implementations MUST use the
//# exporter_master_secret unless explicitly specified by the
//# application.
// vacuous: no exporter is offered; QUIC (RFC 9001) uses none
//
//= https://www.rfc-editor.org/rfc/rfc8446#section-7.5
//= type=exception
//= reason=binds authors of future specifications, not an implementation
//# Future
//# specifications MUST NOT define a use of exporters that permit both an
//# empty context and no context with the same label.
//
// RFC 8446 §4.4.1: "when the server responds to a ClientHello with a HelloRetryRequest, the
// value of ClientHello1 is replaced with a special synthetic handshake message of handshake type
// "message_hash" containing Hash(ClientHello1). I.e.,
//   Transcript-Hash(ClientHello1, HelloRetryRequest, ... Mn) =
//       Hash(message_hash ||        /* Handshake type */
//            00 00 Hash.length  ||  /* Handshake message length (bytes) */
//            Hash(ClientHello1) ||  /* Hash of ClientHello1 */
//            HelloRetryRequest  || ... || Mn)"
//
// RFC 8446 §7.1 diagram, PSK-absent subset (PSK = 0; binder, early, exporter and resumption
// branches and the secret names elided, lines reflowed):
//                 0
//                 |
//                 v
//   PSK ->  HKDF-Extract = Early Secret
//                 |
//                 v
//           Derive-Secret(., "derived", "")
//                 |
//                 v
//   (EC)DHE -> HKDF-Extract = Handshake Secret
//                 |
//                 +-----> Derive-Secret(., "c hs traffic", ClientHello...ServerHello)
//                 +-----> Derive-Secret(., "s hs traffic", ClientHello...ServerHello)
//                 v
//           Derive-Secret(., "derived", "")
//                 |
//                 v
//      0 -> HKDF-Extract = Master Secret
//                 |
//                 +-----> Derive-Secret(., "c ap traffic", ClientHello...server Finished)
//                 +-----> Derive-Secret(., "s ap traffic", ClientHello...server Finished)
// "0" is "the 0-value consisting of a string of Hash.length bytes set to zeros".
use crate::codes::*;
use crate::hkdf_label::*;
use crypto::hkdf::*;
use crypto::hmac::*;
use crypto::sha256::*;
use vstd::prelude::*;

verus! {

pub open spec fn zeros32() -> Seq<u8> {
    Seq::new(32, |_i| 0u8)
}

/// `ch1` is the full ClientHello1 message, header included.
pub open spec fn spec_message_hash(ch1: Seq<u8>) -> Seq<u8> {
    seq![HT_MESSAGE_HASH, 0, 0, 32] + spec_sha256(ch1)
}

pub open spec fn spec_early_secret() -> Seq<u8> {
    spec_hkdf_extract(zeros32(), zeros32())
}

pub open spec fn spec_handshake_secret(ecdhe: Seq<u8>) -> Seq<u8> {
    spec_hkdf_extract(spec_derive_secret(spec_early_secret(), LABEL_DERIVED@, seq![]), ecdhe)
}

pub open spec fn spec_master_secret(hs: Seq<u8>) -> Seq<u8> {
    spec_hkdf_extract(spec_derive_secret(hs, LABEL_DERIVED@, seq![]), zeros32())
}

/// §4.4.4: finished_key = HKDF-Expand-Label(BaseKey, "finished", "", Hash.length).
pub open spec fn spec_finished_key(base: Seq<u8>) -> Seq<u8> {
    spec_hkdf_expand_label(base, LABEL_FINISHED@, seq![], 32)
}

/// §4.4.4: verify_data = HMAC(finished_key, Transcript-Hash(Handshake Context, Certificate*,
/// CertificateVerify*)).
pub open spec fn spec_verify_data(base: Seq<u8>, messages: Seq<u8>) -> Seq<u8> {
    spec_hmac_sha256(spec_finished_key(base), spec_sha256(messages))
}

pub fn message_hash(ch1: &[u8]) -> (r: Vec<u8>)
    requires
        ch1@.len() <= crypto::bytes::MAX_INPUT_LEN,
    ensures
        r@ == spec_message_hash(ch1@),
        r@.len() == 36,
{
    let h = sha256(ch1);
    let mut r: Vec<u8> = Vec::new();
    r.push(HT_MESSAGE_HASH);
    r.push(0);
    r.push(0);
    r.push(32);
    r.extend_from_slice(&h);
    assert(r@ =~= seq![HT_MESSAGE_HASH, 0, 0, 32] + h@);
    r
}

pub struct HsSecrets {
    pub hs: [u8; 32],
    pub client: [u8; 32],
    pub server: [u8; 32],
}

pub struct SpecHsSecrets {
    pub hs: Seq<u8>,
    pub client: Seq<u8>,
    pub server: Seq<u8>,
}

impl View for HsSecrets {
    type V = SpecHsSecrets;

    open spec fn view(&self) -> SpecHsSecrets {
        SpecHsSecrets { hs: self.hs@, client: self.client@, server: self.server@ }
    }
}

/// `Derive-Secret(secret, "derived", "")`.
fn derived(secret: &[u8; 32]) -> (r: [u8; 32])
    ensures
        r@ == spec_derive_secret(secret@, LABEL_DERIVED@, seq![]),
{
    let empty: Vec<u8> = Vec::new();
    let h = sha256(empty.as_slice());
    assert(empty@ == Seq::<u8>::empty());
    derive_secret(secret, &LABEL_DERIVED, &h)
}

fn zeros() -> (r: [u8; 32])
    ensures
        r@ == zeros32(),
{
    let r = [0u8; 32];
    assert(r@ =~= zeros32());
    r
}

/// `th` is Transcript-Hash(ClientHello...ServerHello).
pub fn handshake_secrets(ecdhe: &[u8; 32], th: &[u8; 32]) -> (r: HsSecrets)
    ensures
        r.hs@ == spec_handshake_secret(ecdhe@),
        r.client@ == spec_hkdf_expand_label(r.hs@, LABEL_C_HS@, th@, 32),
        r.server@ == spec_hkdf_expand_label(r.hs@, LABEL_S_HS@, th@, 32),
{
    let z = zeros();
    let early = hkdf_extract(z.as_slice(), z.as_slice());
    let salt = derived(&early);
    let hs = hkdf_extract(salt.as_slice(), ecdhe.as_slice());
    let client = derive_secret(&hs, &LABEL_C_HS, th);
    let server = derive_secret(&hs, &LABEL_S_HS, th);
    HsSecrets { hs, client, server }
}

pub fn master_secret(hs: &[u8; 32]) -> (r: [u8; 32])
    ensures
        r@ == spec_master_secret(hs@),
{
    let z = zeros();
    let salt = derived(hs);
    hkdf_extract(salt.as_slice(), z.as_slice())
}

/// `th` is Transcript-Hash(ClientHello...server Finished); returns (client, server).
pub fn app_secrets(master: &[u8; 32], th: &[u8; 32]) -> (r: ([u8; 32], [u8; 32]))
    ensures
        r.0@ == spec_hkdf_expand_label(master@, LABEL_C_AP@, th@, 32),
        r.1@ == spec_hkdf_expand_label(master@, LABEL_S_AP@, th@, 32),
{
    (derive_secret(master, &LABEL_C_AP, th), derive_secret(master, &LABEL_S_AP, th))
}

pub fn finished_key(base: &[u8; 32]) -> (r: [u8; 32])
    ensures
        r@ == spec_finished_key(base@),
{
    let empty: Vec<u8> = Vec::new();
    assert(empty@ == Seq::<u8>::empty());
    hkdf_expand_label_32(base, &LABEL_FINISHED, empty.as_slice())
}

/// `th` is Transcript-Hash(Handshake Context, Certificate*, CertificateVerify*).
pub fn verify_data(base: &[u8; 32], th: &[u8; 32]) -> (r: [u8; 32])
    ensures
        r@ == spec_hmac_sha256(spec_finished_key(base@), th@),
{
    let k = finished_key(base);
    hmac_sha256(k.as_slice(), th.as_slice())
}

} // verus!
