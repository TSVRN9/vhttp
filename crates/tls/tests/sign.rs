mod common;

use common::*;
use ring::signature::{
    RsaPublicKeyComponents, UnparsedPublicKey, ECDSA_P256_SHA256_ASN1, RSA_PSS_2048_8192_SHA256,
};
use crypto::p256::p256_public_key;
use tls::config::SigningKey;
use tls::sign::*;

fn ec_verify(content: &[u8], sig: &[u8]) -> bool {
    let pk = p256_public_key(&ECDSA_D).unwrap();
    UnparsedPublicKey::new(&ECDSA_P256_SHA256_ASN1, pk).verify(content, sig).is_ok()
}

#[test]
fn cv_content_rfc8446_example() {
    // Copied from rfc8446.txt §4.4.3 by script (fx-4b-t4/rfcex.py).
    let want = hex("20202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020544c5320312e332c20736572766572204365727469666963617465566572696679000101010101010101010101010101010101010101010101010101010101010101");
    assert_eq!(want.len(), 130);
    assert_eq!(cv_content(&[0x01; 32]), want);
}

#[test]
fn ecdsa_verifies() {
    let key = SigningKey::EcdsaP256(ECDSA_D);
    let sig = sign_cv(&key, &[0x5a; 32], &[0; 32]).unwrap();
    assert_eq!(sig[0], 0x30);
    assert!(sig.len() <= 72);
    assert!(ec_verify(&cv_content(&[0x5a; 32]), &sig));
    assert_eq!(sign_cv(&key, &[0x5a; 32], &[0; 32]).unwrap(), sig);
    assert_eq!(sign_cv(&key, &[0x5a; 32], &[9; 32]).unwrap(), sig);
}

#[test]
fn rsa_verifies() {
    let key = SigningKey::Rsa(rsa_key());
    let content = cv_content(&[0x5a; 32]);
    let pk = RsaPublicKeyComponents { n: &RSA_N[..], e: &RSA_E[..] };
    let sig = sign_cv(&key, &[0x5a; 32], &[0x33; 32]).unwrap();
    assert_eq!(sig.len(), 256);
    pk.verify(&RSA_PSS_2048_8192_SHA256, &content, &sig).unwrap();
    let sig2 = sign_cv(&key, &[0x5a; 32], &[0x34; 32]).unwrap();
    assert_ne!(sig, sig2);
    pk.verify(&RSA_PSS_2048_8192_SHA256, &content, &sig2).unwrap();
}

#[test]
fn ecdsa_invalid_scalar() {
    let key = SigningKey::EcdsaP256([0; 32]);
    assert_eq!(sign_cv(&key, &[0x5a; 32], &[0; 32]), Err(0x150));
}

#[test]
fn wrong_context_fails() {
    let key = SigningKey::EcdsaP256(ECDSA_D);
    let sig = sign_cv(&key, &[0x5a; 32], &[0; 32]).unwrap();
    let mut content = cv_content(&[0x5a; 32]);
    assert_eq!(content[64], b'T');
    content[64] = b't';
    assert!(!ec_verify(&content, &sig));
}
