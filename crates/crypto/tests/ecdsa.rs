use crypto::ecdsa::{p256_ecdsa_sign, serialize_ecdsa_der};
use crypto::p256::p256_public_key;
use p256::ecdsa::signature::{Signer, Verifier};

fn h(s: &str) -> Vec<u8> {
    let s: String = s.chars().filter(|c| !c.is_whitespace()).collect();
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect()
}

const D: &str = "c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721";
const SAMPLE: &str = "efd48b2aacb6a8fd1140dd9cd45e81d69d2c877b56aaf991c34d0ea84eaf3716 f7cb1c942d657c41d436c7a1b6e29f65f3e900dbb9aff4064dc4ab2f843acda8";
const TEST: &str = "f1abb023518351cd71d881567b1ea663ed3efcf6c5132b354f28d3b0b7d38367 019f4113742a2b14bd25926b49c649155f267e60d3814b4c0cc84250e46f0083";

fn der(sig: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    serialize_ecdsa_der(sig, &mut out);
    out
}

#[test]
fn rfc6979_a25_sha256() {
    let d = h(D);
    assert_eq!(p256_ecdsa_sign(&d, b"sample").unwrap().to_vec(), h(SAMPLE));
    assert_eq!(p256_ecdsa_sign(&d, b"test").unwrap().to_vec(), h(TEST));
}

#[test]
fn ecdsa_scalar_range() {
    assert!(p256_ecdsa_sign(&[0u8; 32], b"sample").is_none());
    assert!(p256_ecdsa_sign(&h("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551"), b"sample").is_none());
    assert!(p256_ecdsa_sign(&h("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550"), b"sample").is_some());
}

#[test]
fn der_vectors() {
    assert_eq!(
        der(&h(SAMPLE)),
        h("3046022100efd48b2aacb6a8fd1140dd9cd45e81d69d2c877b56aaf991c34d0ea84eaf3716022100f7cb1c942d657c41d436c7a1b6e29f65f3e900dbb9aff4064dc4ab2f843acda8")
    );
    assert_eq!(
        der(&h(TEST)),
        h("3045022100f1abb023518351cd71d881567b1ea663ed3efcf6c5132b354f28d3b0b7d383670220019f4113742a2b14bd25926b49c649155f267e60d3814b4c0cc84250e46f0083")
    );
    let z31 = "00".repeat(31);
    assert_eq!(der(&h(&format!("{z31}01 {z31}01"))), h("3006020101020101"));
    assert_eq!(der(&[0u8; 64]), h("3006020100020100"));
    let z30 = "00".repeat(30);
    assert_eq!(
        der(&h(&format!("7f{z31} 0080{z30}"))),
        h(&format!("304402207f{z31} 022000 80{z30}"))
    );
    let mut out = vec![0xAA];
    serialize_ecdsa_der(&h(SAMPLE), &mut out);
    assert_eq!(out[0], 0xAA);
    assert_eq!(out[1..].to_vec(), der(&h(SAMPLE)));
}

const N_MINUS_1: &str = "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550";
const MSG_LENS: [usize; 7] = [0, 1, 55, 56, 64, 65, 1000];

fn pattern(i: usize) -> [u8; 32] {
    core::array::from_fn(|j| (i * 37 + j * 11 + 1) as u8)
}

// 46 pattern keys plus d = 1 and d = n - 1.
fn keys() -> Vec<Vec<u8>> {
    let mut ds: Vec<Vec<u8>> = (0..46).map(|i| pattern(i).to_vec()).collect();
    let mut one = vec![0u8; 32];
    one[31] = 1;
    ds.extend([one, h(N_MINUS_1)]);
    ds
}

fn msg(i: usize, len: usize) -> Vec<u8> {
    (0..len).map(|j| (j * 7 + i * 13 + 5) as u8).collect()
}

#[test]
fn sign_matches_rustcrypto() {
    for (i, d) in keys().iter().enumerate() {
        let sk = p256::ecdsa::SigningKey::from_bytes(d[..].try_into().unwrap()).unwrap();
        for len in MSG_LENS {
            let m = msg(i, len);
            let want: p256::ecdsa::Signature = sk.sign(&m);
            assert_eq!(p256_ecdsa_sign(d, &m).unwrap().to_vec(), want.to_bytes().to_vec(), "{d:02x?} len {len}");
        }
    }
}

#[test]
fn sign_verifies() {
    for (i, d) in keys().iter().enumerate() {
        let vk = p256::ecdsa::VerifyingKey::from_sec1_bytes(&p256_public_key(d).unwrap()).unwrap();
        for len in MSG_LENS {
            let m = msg(i, len);
            let sig = p256::ecdsa::Signature::from_slice(&p256_ecdsa_sign(d, &m).unwrap()).unwrap();
            assert!(vk.verify(&m, &sig).is_ok(), "{d:02x?} len {len}");
        }
    }
}

#[test]
#[ignore] // timing only; run with --release -- --ignored --nocapture
fn sign_speed() {
    let d = h(D);
    let t = std::time::Instant::now();
    std::hint::black_box(p256_ecdsa_sign(std::hint::black_box(&d), b"sample"));
    println!("p256_ecdsa_sign {:?}", t.elapsed());
}
