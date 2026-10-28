mod common;

use common::*;
use crypto::p256::p256_public_key;
use crypto::sha256::sha256;
use ring::signature::{
    RsaPublicKeyComponents, UnparsedPublicKey, ECDSA_P256_SHA256_ASN1, RSA_PSS_2048_8192_SHA256,
};
use tls::client_hello::*;
use tls::config::*;
use tls::flight::*;
use tls::schedule::*;
use tls::server_msgs::*;

type Flight = Result<(Vec<TlsEvent>, [u8; 32]), u64>;

fn s32(s: &str) -> [u8; 32] {
    hex(s).try_into().unwrap()
}

fn h(parts: &[&[u8]]) -> [u8; 32] {
    sha256(&parts.concat())
}

fn rsa_cfg() -> ServerConfig {
    ServerConfig {
        chains: vec![CertChain {
            der: vec![RSA_CERT.to_vec()],
            chain_schemes: vec![],
            key: SigningKey::Rsa(rsa_key()),
        }],
    }
}

fn ecdsa_cfg() -> ServerConfig {
    ServerConfig {
        chains: vec![CertChain {
            der: vec![ECDSA_CERT.to_vec()],
            chain_schemes: vec![],
            key: SigningKey::EcdsaP256(ECDSA_D),
        }],
    }
}

/// R5_CH2's typed fields, without its cookie, with ALPN `h3` and transport parameters `[1, 0]`.
fn ch2() -> ClientHello {
    let (head, mut e) = split_ch(R5_CH2);
    e.retain(|(t, _)| *t != 0x2c);
    e.push((0x10, vec![0, 3, 2, b'h', b'3']));
    e.push((0x39, vec![1, 0]));
    let m = join_ch(&head, &e);
    parse_client_hello(&m[4..]).expect("ch2 parses")
}

/// message_hash(R5_CH1) || R5_HRR || R5_CH2, the raw RFC 8448 §5 bytes.
fn t0() -> Vec<u8> {
    [&message_hash(R5_CH1)[..], R5_HRR, R5_CH2].concat()
}

fn rand() -> [u8; 96] {
    let d = hex("8c510601f9765bfb8ed693449a48989859b5cfa879cb9f5443c41c5ff10634ed");
    [&R5_SH[6..38], &d[..], &[0x33u8; 32][..]].concat().try_into().unwrap()
}

fn run(cfg: &ServerConfig, ch: &ClientHello, scheme: u16, rand: &[u8; 96]) -> Flight {
    build_flight(cfg, &[1, 0], t0(), ch, 0, scheme, 0, rand)
}

fn send_data(e: &TlsEvent, want: Level) -> Vec<u8> {
    match e {
        TlsEvent::Send { level, data } if *level == want => data.clone(),
        other => panic!("not Send {want:?}: {other:?}"),
    }
}

/// Checks the flight for `cert` against the RFC 8448 §5 values; returns the CertificateVerify
/// message and the content its signature covers.
fn check_flight(evs: &[TlsEvent], vd: &[u8; 32], cert: &[u8]) -> (Vec<u8>, Vec<u8>) {
    assert_eq!(evs.len(), 5);
    assert_eq!(evs[0], TlsEvent::PeerParams(vec![1, 0]));
    assert_eq!(evs[1], TlsEvent::Send { level: Level::Initial, data: R5_SH.to_vec() });
    let c_hs = s32("158aa7ab8855073582b41d674b4055cabcc534728f659314861b4e08e2011566");
    let s_hs = s32("3403e781e2af7b6508da28574f6e95a1abf162de83a97927c37672a4a0cef8a1");
    assert_eq!(evs[2], TlsEvent::Secrets { level: Level::Handshake, client: c_hs, server: s_hs });
    let data = send_data(&evs[3], Level::Handshake);
    let mut ee = Vec::new();
    serialize_encrypted_extensions(&[1, 0], &mut ee);
    let mut ct = Vec::new();
    serialize_certificate(&vec![cert.to_vec()], &mut ct);
    let n = ee.len() + ct.len();
    assert_eq!(&data[..ee.len()], &ee[..]);
    assert_eq!(&data[ee.len()..n], &ct[..]);
    let cv = data[n..data.len() - 36].to_vec();
    let fin = &data[data.len() - 36..];
    let t0 = t0();
    let th_cv = h(&[&t0, R5_SH, &ee, &ct, &cv]);
    let mut want_fin = Vec::new();
    serialize_finished(&verify_data(&s_hs, &th_cv), &mut want_fin);
    assert_eq!(fin, &want_fin[..]);
    let th4 = h(&[&t0, R5_SH, &data]);
    let hs = s32("ce022e5e6e81e50736d773f2d3adfce8220d049bf510f0dbfac927ef4243b148");
    let (c_ap, s_ap) = app_secrets(&master_secret(&hs), &th4);
    assert_eq!(evs[4], TlsEvent::Secrets { level: Level::OneRtt, client: c_ap, server: s_ap });
    assert_eq!(vd, &verify_data(&c_hs, &th4));
    let th_cert = h(&[&t0, R5_SH, &ee, &ct]);
    // RFC 8446 §4.4.3: 64 spaces, the context string, a 0 byte, then the transcript hash.
    let content = [&[0x20u8; 64][..], b"TLS 1.3, server CertificateVerify", &[0], &th_cert].concat();
    (cv, content)
}

#[test]
fn rfc8448_s5_flight() {
    let (evs, vd) = run(&rsa_cfg(), &ch2(), 0x0804, &rand()).expect("flight");
    let (cv, content) = check_flight(&evs, &vd, RSA_CERT);
    assert_eq!(&cv[..8], &hex("0f000104 0804 0100")[..]);
    let pk = RsaPublicKeyComponents { n: &RSA_N[..], e: &RSA_E[..] };
    pk.verify(&RSA_PSS_2048_8192_SHA256, &content, &cv[8..]).expect("RSA-PSS verifies");
}

#[test]
fn ecdsa_flight() {
    let (evs, vd) = run(&ecdsa_cfg(), &ch2(), 0x0403, &rand()).expect("flight");
    let (cv, content) = check_flight(&evs, &vd, ECDSA_CERT);
    assert_eq!(&cv[..1], &[0x0f]);
    assert_eq!(&cv[4..6], &[0x04, 0x03]);
    let n = u16::from_be_bytes([cv[6], cv[7]]) as usize;
    assert_eq!(cv.len(), 8 + n);
    let pk = p256_public_key(&ECDSA_D).unwrap();
    UnparsedPublicKey::new(&ECDSA_P256_SHA256_ASN1, pk)
        .verify(&content, &cv[8..])
        .expect("ECDSA verifies");
}

#[test]
fn bad_peer_share() {
    let mut flipped = P256_SHARE.to_vec();
    flipped[40] ^= 0x01;
    let mut compressed = vec![0x02];
    compressed.extend_from_slice(&P256_SHARE[1..33]);
    let zero = [&[0x04u8][..], &[0u8; 64][..]].concat();
    let ff = [&[0x04u8][..], &[0xffu8; 64][..]].concat();
    for kx in [zero, ff, compressed, flipped] {
        let mut ch = ch2();
        ch.key_shares.as_mut().unwrap()[0].key_exchange = kx.clone();
        assert_eq!(run(&ecdsa_cfg(), &ch, 0x0403, &rand()), Err(0x12f), "{kx:02x?}");
    }
}

#[test]
fn invalid_scalar() {
    let mut r = rand();
    r[32..64].copy_from_slice(&[0xff; 32]);
    assert_eq!(run(&ecdsa_cfg(), &ch2(), 0x0403, &r), Err(0x150));
}

#[test]
fn random_from_rand() {
    let a = rand();
    let mut b = rand();
    b[..32].copy_from_slice(&[0x77; 32]);
    let mut ch_b = ch2();
    ch_b.random = [0x55; 32];
    let sh = |ch: &ClientHello, r: &[u8; 96]| {
        let (evs, _) = run(&ecdsa_cfg(), ch, 0x0403, r).expect("flight");
        send_data(&evs[1], Level::Initial)
    };
    let sa = sh(&ch2(), &a);
    let sb = sh(&ch_b, &b);
    assert_eq!(&sa[6..38], &a[..32]);
    assert_eq!(&sb[6..38], &b[..32]);
    assert_eq!(sa[..6], sb[..6]);
    assert_eq!(sa[38..], sb[38..]);
}
