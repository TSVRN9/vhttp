use crypto::aes::aes128_encrypt_block;
use crypto::gcm::{aes128_gcm_open, aes128_gcm_seal};

fn h(s: &str) -> Vec<u8> {
    let s: String = s.chars().filter(|c| !c.is_whitespace()).collect();
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect()
}

#[test]
fn fips197_aes128() {
    assert_eq!(
        aes128_encrypt_block(&h("000102030405060708090a0b0c0d0e0f"), &h("00112233445566778899aabbccddeeff")).to_vec(),
        h("69c4e0d86a7b0430d8cdb78070b4c55a")
    );
    assert_eq!(
        aes128_encrypt_block(&h("2b7e151628aed2a6abf7158809cf4f3c"), &h("3243f6a8885a308d313198a2e0370734")).to_vec(),
        h("3925841d02dc09fbdc118597196a0b32")
    );
}

const K4: &str = "feffe9928665731c6d6a8f9467308308";
const IV4: &str = "cafebabefacedbaddecaf888";
const AAD4: &str = "feedfacedeadbeeffeedfacedeadbeefabaddad2";
const PT4: &str = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39";
const CT4: &str = "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091";
const T4: &str = "5bc94fbc3221a5db94fae95ae7121a47";

#[test]
fn gcm_spec_vectors() {
    let (k0, iv0) = (vec![0u8; 16], vec![0u8; 12]);
    let r = aes128_gcm_seal(&k0, &iv0, &[], &[]);
    assert_eq!(r, h("58e2fccefa7e3061367f1d57a4e7455a"));
    assert_eq!(aes128_gcm_open(&k0, &iv0, &[], &r), Some(vec![]));
    let r = aes128_gcm_seal(&k0, &iv0, &[], &[0u8; 16]);
    assert_eq!(r, h("0388dace60b6a392f328c2b971b2fe78ab6e47d42cec13bdf53a67b21257bddf"));
    let (k, iv, aad, pt) = (h(K4), h(IV4), h(AAD4), h(PT4));
    let r = aes128_gcm_seal(&k, &iv, &aad, &pt);
    assert_eq!(r, h(&format!("{CT4}{T4}")));
    assert_eq!(aes128_gcm_open(&k, &iv, &aad, &r), Some(pt));
}

#[test]
fn gcm_open_rejects() {
    let (k, iv, aad) = (h(K4), h(IV4), h(AAD4));
    let ct = h(&format!("{CT4}{T4}"));
    let mut a = ct.clone();
    *a.last_mut().unwrap() ^= 1;
    assert_eq!(aes128_gcm_open(&k, &iv, &aad, &a), None);
    let mut a = ct.clone();
    a[0] ^= 1;
    assert_eq!(aes128_gcm_open(&k, &iv, &aad, &a), None);
    assert_eq!(aes128_gcm_open(&k, &iv, &aad[1..], &ct), None);
    assert_eq!(aes128_gcm_open(&k, &iv, &aad, &ct[..15]), None);
    assert_eq!(aes128_gcm_open(&k, &iv, &aad, &[]), None);
}
