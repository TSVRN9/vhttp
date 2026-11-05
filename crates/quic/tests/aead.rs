//! Phase 3e Task 2: AEAD packet protection against RFC 9001 Appendix A.2 and A.3.
mod common;
use common::*;
use quic::aead::*;
use quic::codes::PN_MAX;

const A2_HEADER: &str = "c300000001088394c8f03e5157080000449e00000002";
const A3_HEADER: &str = "c1000000010008f067a5502a4262b50040750001";

/// A.2's unprotected payload: the CRYPTO frame and 917 bytes of PADDING (1162 bytes).
fn a2_payload() -> Vec<u8> {
    let mut p = hex("060040f1");
    p.extend_from_slice(&A2_CRYPTO);
    p.extend([0; 917]);
    p
}

#[test]
fn nonce_vectors() {
    assert_eq!(nonce(&CLIENT.iv, 2).to_vec(), hex("fa044b2f42a3fd3b46fb255e"));
    assert_eq!(nonce(&SERVER.iv, 1).to_vec(), hex("0ac1493ca1905853b0bba03f"));
    assert_eq!(nonce(&[0; 12], PN_MAX).to_vec(), hex("000000003fffffffffffffff"));
}

#[test]
fn a3_seal() {
    assert_eq!(seal_packet(&SERVER, 1, &hex(A3_HEADER), &A3_PAYLOAD), A3[20..135]);
}

#[test]
fn a2_seal() {
    let p = a2_payload();
    assert_eq!(p.len(), 1162);
    assert_eq!(seal_packet(&CLIENT, 2, &hex(A2_HEADER), &p), A2[22..1200]);
}

#[test]
fn a3_open() {
    let h = hex(A3_HEADER);
    let ct = A3[20..135].to_vec();
    assert_eq!(open_packet(&SERVER, 1, &h, &ct), Some(A3_PAYLOAD.to_vec()));
    let mut bad = ct.clone();
    *bad.last_mut().unwrap() ^= 1;
    assert_eq!(open_packet(&SERVER, 1, &h, &bad), None);
    assert_eq!(open_packet(&SERVER, 2, &h, &ct), None);
    let mut h3 = h.clone();
    h3[0] = 0xc3;
    assert_eq!(open_packet(&SERVER, 1, &h3, &ct), None);
}

#[test]
fn a2_build() {
    assert_eq!(build(&hex(A2_HEADER), 18, 2, &a2_payload(), &CLIENT), A2);
    assert_eq!(build(&hex(A3_HEADER), 18, 1, &A3_PAYLOAD, &SERVER), A3);
}

#[test]
fn keys_debug_redacted() {
    let s = format!("{:?}", KeyPair { rx: CLIENT, tx: SERVER });
    // First bytes of each A.1 key, IV and HP key, in decimal and in hex.
    for leak in [
        "31, 54", "250, 4", "159, 80", "207, 58", "10, 193", "194, 6", "1f36", "fa04", "9f50", "cf3a", "0ac1",
        "c206", "1F36", "CF3A",
    ] {
        assert!(!s.contains(leak), "{s}");
    }
    assert!(s.contains("16 bytes") && s.contains("12 bytes"), "{s}");
}
