use crypto::ecdsa::{p256_ecdsa_sign, serialize_ecdsa_der};

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
