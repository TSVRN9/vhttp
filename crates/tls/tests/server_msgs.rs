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
