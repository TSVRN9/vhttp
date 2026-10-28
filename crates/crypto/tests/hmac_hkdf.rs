use crypto::hkdf::{hkdf_expand, hkdf_extract};
use crypto::hmac::hmac_sha256;

fn h(s: &str) -> Vec<u8> {
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect()
}

#[test]
fn rfc4231_hmac() {
    assert_eq!(
        hmac_sha256(&[0x0b; 20], b"Hi There").to_vec(),
        h("b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7")
    );
    assert_eq!(
        hmac_sha256(b"Jefe", b"what do ya want for nothing?").to_vec(),
        h("5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843")
    );
    assert_eq!(
        hmac_sha256(&[0xaa; 131], b"Test Using Larger Than Block-Size Key - Hash Key First").to_vec(),
        h("60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54")
    );
}

#[test]
fn rfc5869_hkdf() {
    let ikm = [0x0b; 22];
    let prk = hkdf_extract(&h("000102030405060708090a0b0c"), &ikm);
    assert_eq!(prk.to_vec(), h("077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5"));
    assert_eq!(
        hkdf_expand(&prk, &h("f0f1f2f3f4f5f6f7f8f9"), 42),
        h("3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865")
    );
    let prk = hkdf_extract(&[], &ikm);
    assert_eq!(prk.to_vec(), h("19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04"));
    assert_eq!(
        hkdf_expand(&prk, &[], 42),
        h("8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d9d201395faa4b61a96c8")
    );
    assert_eq!(hkdf_extract(&[0u8; 32], &ikm), prk);
}

#[test]
fn hkdf_expand_lengths() {
    let prk = h("19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04");
    assert!(hkdf_expand(&prk, &[], 0).is_empty());
    let big = hkdf_expand(&prk, &[], 8160);
    assert_eq!(big.len(), 8160);
    assert_eq!(
        big[..42],
        h("8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d9d201395faa4b61a96c8")[..]
    );
}
