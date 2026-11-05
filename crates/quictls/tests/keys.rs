//! Phase 4c Task 1: RFC 9001 §5.1-§5.2 Initial secrets and packet keys against Appendix A.1.
#[path = "../../quic/tests/common/mod.rs"]
mod qc;
use qc::{hex, A2, A2_CRYPTO, A3, A3_PAYLOAD, S1};
use quic::ack::AckFrame;
use quic::aead::KeyPair;
use quic::frame::Frame;
use quic::payload::PacketKind;
use quic::datagram::OutPacket;
use quic::protect::protect;
use tls::codes::*;
use tls::hkdf_label::*;
use quictls::keys::*;

#[test]
fn a1_labels() {
    assert_eq!(hkdf_label(b"client in", &[], 32), hex("00200f746c73313320636c69656e7420696e00"));
    assert_eq!(hkdf_label(b"server in", &[], 32), hex("00200f746c7331332073657276657220696e00"));
    assert_eq!(hkdf_label(b"quic key", &[], 16), hex("00100e746c7331332071756963206b657900"));
    assert_eq!(hkdf_label(b"quic iv", &[], 12), hex("000c0d746c733133207175696320697600"));
    assert_eq!(hkdf_label(b"quic hp", &[], 16), hex("00100d746c733133207175696320687000"));
}

#[test]
fn a1_secrets() {
    let init = crypto::hkdf::hkdf_extract(&INITIAL_SALT, &qc::S1);
    assert_eq!(init.to_vec(), hex("7db5df06e7a69e432496adedb00851923595221596ae2ae9fb8115c1e9ed0a44"));
    let c = hkdf_expand_label_32(&init, &LABEL_CLIENT_IN, &[]);
    assert_eq!(c.to_vec(), hex("c00cf151ca5be075ed0ebfb5c80323c42d6b7db67881289af4008f1f6c357aea"));
    let s = hkdf_expand_label_32(&init, &LABEL_SERVER_IN, &[]);
    assert_eq!(s.to_vec(), hex("3c199828fd139efd216c155ad844cc81fb82fa8d7446fa7d78be803acdda951b"));
}

#[test]
fn a1_keys() {
    let k = initial_keys(&S1);
    assert_eq!(k.rx, qc::CLIENT);
    assert_eq!(k.tx, qc::SERVER);
    assert_eq!(k.rx.key.to_vec(), hex("1f369613dd76d5467730efcbe3b1a22d"));
    assert_eq!(k.tx.hp.to_vec(), hex("c206b8d9b9f0f37644430b490eeaa314"));
}

#[test]
fn a2_a3_under_derived_keys() {
    let k: KeyPair = initial_keys(&S1);
    let a2 = OutPacket {
        kind: PacketKind::Initial,
        dcid: S1.to_vec(),
        scid: vec![],
        pn: 2,
        pn_len: 4,
        frames: vec![Frame::Crypto { offset: 0, data: A2_CRYPTO.to_vec() }],
        padding: 917,
        spin: false,
    };
    let mut out = Vec::new();
    protect(&a2, &k.rx, &mut out);
    assert_eq!(out, A2);
    let ack = AckFrame { largest: 0, delay: 0, first_range: 0, ranges: vec![], ecn: None };
    let a3 = OutPacket {
        kind: PacketKind::Initial,
        dcid: vec![],
        scid: hex("f067a5502a4262b5"),
        pn: 1,
        pn_len: 2,
        frames: vec![Frame::Ack(ack), Frame::Crypto { offset: 0, data: A3_PAYLOAD[9..].to_vec() }],
        padding: 0,
        spin: false,
    };
    let mut out = Vec::new();
    protect(&a3, &k.tx, &mut out);
    assert_eq!(out, A3);
}

#[test]
fn codes_agree() {
    assert_eq!(PROTOCOL_VIOLATION, quic::codes::PROTOCOL_VIOLATION);
    assert_eq!(CRYPTO_BUFFER_EXCEEDED, quic::codes::CRYPTO_BUFFER_EXCEEDED);
    assert_eq!(CRYPTO_ERROR_BASE, quic::codes::CRYPTO_ERROR_BASE);
    assert_eq!(H3_ALPN, quic::conn::H3_ALPN);
    for a in [
        ALERT_UNEXPECTED_MESSAGE,
        ALERT_ILLEGAL_PARAMETER,
        ALERT_DECODE_ERROR,
        ALERT_PROTOCOL_VERSION,
        ALERT_MISSING_EXTENSION,
        ALERT_HANDSHAKE_FAILURE,
        ALERT_DECRYPT_ERROR,
        ALERT_INTERNAL_ERROR,
        ALERT_NO_APPLICATION_PROTOCOL,
    ] {
        assert!((CRYPTO_ERROR_BASE..=CRYPTO_ERROR_BASE + 0xff).contains(&a));
    }
}

#[test]
fn any_dcid() {
    assert!(initial_keys(&[0x83; 8]) != initial_keys(&S1));
    initial_keys(&[0u8; 20]);
    initial_keys(&[]);
}
