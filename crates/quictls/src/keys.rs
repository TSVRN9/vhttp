//! QUIC Initial secrets and packet keys (RFC 9001 §5.1, §5.2), for any destination connection ID.
use tls::hkdf_label::*;
use crypto::hkdf::*;
use quic::aead::*;
use vstd::prelude::*;

verus! {

// QUIC Initial secrets and packet keys (RFC 9001 §5.1, §5.2)
pub const LABEL_CLIENT_IN: [u8; 9] = *b"client in";
pub const LABEL_SERVER_IN: [u8; 9] = *b"server in";
pub const LABEL_QUIC_KEY: [u8; 8] = *b"quic key";
pub const LABEL_QUIC_IV: [u8; 7] = *b"quic iv";
pub const LABEL_QUIC_HP: [u8; 7] = *b"quic hp";

// RFC 9001 §5.2: initial_salt = 0x38762cf7f55934b34d179ae6a4c80cadccbb7f0a
pub const INITIAL_SALT: [u8; 20] = [
    0x38, 0x76, 0x2c, 0xf7, 0xf5, 0x59, 0x34, 0xb3, 0x4d, 0x17,
    0x9a, 0xe6, 0xa4, 0xc8, 0x0c, 0xad, 0xcc, 0xbb, 0x7f, 0x0a,
];

/// initial_secret = HKDF-Extract(initial_salt, client_dst_connection_id).
pub open spec fn rfc_initial_secret(dcid: Seq<u8>) -> Seq<u8> {
    spec_hkdf_extract(INITIAL_SALT@, dcid)
}

/// RFC 9001 §5.1: key, iv and hp from a traffic secret (AES-128-GCM sizes).
pub open spec fn rfc_packet_keys(secret: Seq<u8>) -> SpecKeys {
    SpecKeys {
        key: spec_hkdf_expand_label(secret, LABEL_QUIC_KEY@, seq![], 16),
        iv: spec_hkdf_expand_label(secret, LABEL_QUIC_IV@, seq![], 12),
        hp: spec_hkdf_expand_label(secret, LABEL_QUIC_HP@, seq![], 16),
    }
}

/// The server's view of the Initial keys: it receives under the client's secret and sends under
/// its own.
//= https://www.rfc-editor.org/rfc/rfc9001#section-5.2
//# The HKDF-Expand-Label function defined in TLS 1.3 MUST be used for
//# Initial packets even where the TLS versions offered do not include
//# TLS 1.3.
pub open spec fn rfc_initial_keys(dcid: Seq<u8>) -> SpecKeyPair {
    let init = rfc_initial_secret(dcid);
    SpecKeyPair {
        rx: rfc_packet_keys(spec_hkdf_expand_label(init, LABEL_CLIENT_IN@, seq![], 32)),
        tx: rfc_packet_keys(spec_hkdf_expand_label(init, LABEL_SERVER_IN@, seq![], 32)),
    }
}

fn expand_16(secret: &[u8; 32], label: &[u8]) -> (r: [u8; 16])
    requires
        label_ok(label@),
    ensures
        r@ == spec_hkdf_expand_label(secret@, label@, seq![], 16),
{
    let v = hkdf_expand_label(secret, label, &[], 16);
    let mut r = [0u8; 16];
    let mut i: usize = 0;
    while i < 16
        invariant
            i <= 16,
            v@.len() == 16,
            forall|j: int| 0 <= j < i ==> r@[j] == v@[j],
        decreases 16 - i,
    {
        r[i] = v[i];
        i += 1;
    }
    assert(r@ =~= v@);
    r
}

fn expand_12(secret: &[u8; 32], label: &[u8]) -> (r: [u8; 12])
    requires
        label_ok(label@),
    ensures
        r@ == spec_hkdf_expand_label(secret@, label@, seq![], 12),
{
    let v = hkdf_expand_label(secret, label, &[], 12);
    let mut r = [0u8; 12];
    let mut i: usize = 0;
    while i < 12
        invariant
            i <= 12,
            v@.len() == 12,
            forall|j: int| 0 <= j < i ==> r@[j] == v@[j],
        decreases 12 - i,
    {
        r[i] = v[i];
        i += 1;
    }
    assert(r@ =~= v@);
    r
}

pub fn packet_keys(secret: &[u8; 32]) -> (r: PacketKeys)
    ensures
        r@ == rfc_packet_keys(secret@),
{
    hide(spec_hkdf_expand_label);
    let key = expand_16(secret, &LABEL_QUIC_KEY);
    let iv = expand_12(secret, &LABEL_QUIC_IV);
    let hp = expand_16(secret, &LABEL_QUIC_HP);
    PacketKeys { key, iv, hp }
}

pub fn initial_keys(dcid: &[u8]) -> (r: KeyPair)
    requires
        dcid@.len() <= quic::codes::MAX_CID_LEN,
    ensures
        r@ == rfc_initial_keys(dcid@),
{
    hide(spec_hkdf_expand_label);
    let init = hkdf_extract(&INITIAL_SALT, dcid);
    let e: [u8; 0] = [];
    assert(e@ =~= Seq::<u8>::empty());
    let c = hkdf_expand_label_32(&init, &LABEL_CLIENT_IN, &e);
    let s = hkdf_expand_label_32(&init, &LABEL_SERVER_IN, &e);
    KeyPair { rx: packet_keys(&c), tx: packet_keys(&s) }
}

} // verus!
