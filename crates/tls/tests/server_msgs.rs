mod common;

use common::*;
use tls::server_msgs::*;

fn sh(msg: &[u8], group: u16, kx: std::ops::Range<usize>) -> Vec<u8> {
    let mut out = Vec::new();
    serialize_server_hello(msg[6..38].try_into().unwrap(), &[], group, &msg[kx], &mut out);
    out
}

#[test]
fn rfc8448_s5_sh() {
    assert_eq!(sh(R5_SH, 0x0017, 52..117), R5_SH);
}

#[test]
fn rfc8448_s3_sh() {
    assert_eq!(sh(R3_SH, 0x001d, 52..84), R3_SH);
}

#[test]
fn rfc9001_a3_sh() {
    assert_eq!(&A3_SH[6..38], &hex("eefce7f7b37ba1d1632e96677825ddf73988cfc79825df566dc5430b9a045a12")[..]);
    assert_eq!(&A3_SH[52..84], &hex("9d3c940d89690b84d08a60993c144eca684d1081287c834d5311bcf32bb9da1a")[..]);
    assert_eq!(sh(A3_SH, 0x001d, 52..84), A3_SH);
}

#[test]
fn hrr_p256() {
    let mut out = Vec::new();
    serialize_hello_retry_request(&[], 0x0017, &mut out);
    assert_eq!(out.len(), 56);
    assert_eq!(
        out,
        hex("020000340303cf21ad74e59a6111be1d8c021e65b891c2a211167abb8c5e079e09e2c8a8339c00130100000c003300020017002b00020304")
    );
}

#[test]
fn sh_echo_32() {
    let mut out = Vec::new();
    serialize_server_hello(R5_SH[6..38].try_into().unwrap(), &[0xab; 32], 0x0017, &R5_SH[52..117], &mut out);
    assert_eq!(out.len(), 155);
    assert_eq!(&out[1..4], &[0, 0, 0x97]);
    assert_eq!(out[38], 0x20);
    assert_eq!(&out[39..71], &[0xab; 32]);
}

#[test]
fn ee_h3_tp() {
    let mut out = Vec::new();
    serialize_encrypted_extensions(&hex("010480007530"), &mut out);
    assert_eq!(out, hex("08000015001300100005000302683300390006010480007530"));
}

#[test]
fn ee_empty_tp() {
    let mut out = Vec::new();
    serialize_encrypted_extensions(&[], &mut out);
    assert_eq!(out, hex("0800000f000d00100005000302683300390000"));
}

#[test]
fn appends() {
    let mut out = vec![0xee];
    serialize_server_hello(R5_SH[6..38].try_into().unwrap(), &[], 0x0017, &R5_SH[52..117], &mut out);
    assert_eq!(out[0], 0xee);
    assert_eq!(&out[1..], R5_SH);
    let mut out = vec![0xee];
    serialize_hello_retry_request(&[], 0x0017, &mut out);
    assert_eq!(out[0], 0xee);
    let mut out = vec![0xee];
    serialize_encrypted_extensions(&[], &mut out);
    assert_eq!(out[0], 0xee);
}

#[test]
fn rfc8448_s5_certificate() {
    let der = R5_CERT[11..443].to_vec();
    assert_eq!(der.len(), 432);
    assert_eq!(&der[..4], &hex("308201ac")[..]);
    let mut out = Vec::new();
    serialize_certificate(&vec![der], &mut out);
    assert_eq!(out, R5_CERT);
}

#[test]
fn two_cert_chain() {
    let der = R5_CERT[11..443].to_vec();
    let mut out = Vec::new();
    serialize_certificate(&vec![der, vec![0x30, 0x00]], &mut out);
    assert_eq!(&out[..15], &hex(&"0b0001c0 00 0001bc 0001b0 308201ac".replace(' ', ""))[..]);
    assert_eq!(&out[out.len() - 10..], &hex(&"e1 0000 000002 3000 0000".replace(' ', ""))[..]);
    assert_eq!(out.len(), 4 + 0x1c0);
}

#[test]
fn rfc8448_s5_cv() {
    let mut out = Vec::new();
    serialize_certificate_verify(0x0804, &R5_CV[8..136], &mut out);
    assert_eq!(out, R5_CV);
}

#[test]
fn rfc8448_s5_finished() {
    let vd: [u8; 32] = hex("8863e6bfb0420a927fa27f34336a70ae426e968e3eb884945b96856dba3976d1")
        .try_into()
        .unwrap();
    let mut out = Vec::new();
    serialize_finished(&vd, &mut out);
    assert_eq!(out, R5_SFIN);
}

#[test]
fn finished_parse() {
    assert_eq!(parse_finished(&[0x11; 32]), Ok([0x11; 32]));
    assert_eq!(parse_finished(&[0x11; 31]), Err(0x132));
    assert_eq!(parse_finished(&[0x11; 33]), Err(0x132));
    assert_eq!(parse_finished(&[]), Err(0x132));
}

#[test]
fn appends_cert_cv_fin() {
    let mut out = vec![0xee];
    serialize_certificate(&vec![vec![1]], &mut out);
    serialize_certificate_verify(0x0804, &[], &mut out);
    serialize_finished(&[0; 32], &mut out);
    assert_eq!(out[0], 0xee);
    assert_eq!(out.len(), 1 + 14 + 8 + 36);
}

#[test]
fn reserved_edges() {
    for s in [0x0000, 0x0200, 0x0202, 0x0204, 0x0400, 0x0402, 0x0404, 0x0500, 0x0502, 0x0504, 0x0600, 0x0602, 0x0604, 0x06ff] {
        assert!(is_reserved_scheme(s), "{s:#x}");
    }
    for s in [0x0201, 0x0203, 0x0401, 0x0403, 0x0501, 0x0503, 0x0601, 0x0603, 0x0700, 0x0804, 0xfe00, 0xffff] {
        assert!(!is_reserved_scheme(s), "{s:#x}");
    }
    for g in [0x0000, 0x0001, 0x0016, 0x001a, 0x001c, 0xff01, 0xff02] {
        assert!(is_reserved_group(g), "{g:#x}");
    }
    for g in [0x0017, 0x0019, 0x001d, 0x001e, 0x001f, 0x0100, 0x01fc, 0xfe00, 0xff00, 0xff03] {
        assert!(!is_reserved_group(g), "{g:#x}");
    }
}
