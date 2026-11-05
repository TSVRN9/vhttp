#[path = "common/mod.rs"]
mod common;
use common::*;
use tls::config::*;

fn n_minus(k: u8) -> [u8; 32] {
    let mut n = [
        0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17,
        0x9e, 0x84, 0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63, 0x25, 0x51,
    ];
    n[31] -= k;
    n
}

#[test]
fn p256_signing_key_range() {
    let (_, q) = p256_signing_key(ECDSA_D).unwrap();
    assert!(ECDSA_CERT.windows(65).any(|w| w == q));
    assert!(p256_signing_key([0; 32]).is_none());
    assert!(p256_signing_key(n_minus(0)).is_none());
    assert!(p256_signing_key(n_minus(1)).is_some());
}
