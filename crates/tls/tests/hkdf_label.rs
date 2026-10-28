use crypto::sha256::sha256;
use tls::codes::*;
use tls::hkdf_label::*;

fn hex(s: &str) -> Vec<u8> {
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

fn s32(s: &str) -> [u8; 32] {
    hex(s).try_into().unwrap()
}

#[test]
fn labels_rfc8448() {
    assert_eq!(hkdf_label(b"key", &[], 16), hex("001009746c733133206b657900"));
    assert_eq!(hkdf_label(b"iv", &[], 12), hex("000c08746c73313320697600"));
    assert_eq!(hkdf_label(b"finished", &[], 32), hex("00200e746c7331332066696e697368656400"));
    assert_eq!(
        hkdf_label(b"derived", &sha256(b""), 32),
        hex("00200d746c733133206465726976656420e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
    );
    let h = hex("8aa8e828ec2f8a884fec95a3139de01c15a3daa7ff5bfc3f4bfcc21b438d7bf8");
    assert_eq!(
        hkdf_label(b"c hs traffic", &h, 32),
        hex("002012746c73313320632068732074726166666963208aa8e828ec2f8a884fec95a3139de01c15a3daa7ff5bfc3f4bfcc21b438d7bf8")
    );
    assert_eq!(hkdf_label(b"quic key", &[], 16), hex("00100e746c7331332071756963206b657900"));
}

#[test]
fn expand_label_rfc8448_s5() {
    let s = s32("3403e781e2af7b6508da28574f6e95a1abf162de83a97927c37672a4a0cef8a1");
    assert_eq!(hkdf_expand_label(&s, b"key", &[], 16), hex("4646bfac1712c426cd78d8a24a8a6f6b"));
    assert_eq!(hkdf_expand_label(&s, b"iv", &[], 12), hex("c7d395c08d62f297d13768ea"));
    let c = s32("158aa7ab8855073582b41d674b4055cabcc534728f659314861b4e08e2011566");
    assert_eq!(hkdf_expand_label(&c, b"key", &[], 16), hex("2f1f918663d590e7421149a29d94b0b6"));
    assert_eq!(hkdf_expand_label(&c, b"iv", &[], 12), hex("414d5485235e1a688793bd74"));
}

#[test]
fn derive_secret_derived() {
    let s = s32("33ad0a1c607ec03b09e6cd9893680ce210adf300aa1f2660e1b22e10f170f92a");
    assert_eq!(
        derive_secret(&s, b"derived", &sha256(b"")),
        s32("6f2615a108c702c5678f54fc9dbab69716c076189c48250cebeac3576c3611ba")
    );
}

#[test]
fn new_alert_sums() {
    assert_eq!(ALERT_HANDSHAKE_FAILURE, CRYPTO_ERROR_BASE + 40);
    assert_eq!(ALERT_DECRYPT_ERROR, CRYPTO_ERROR_BASE + 51);
    assert_eq!(ALERT_INTERNAL_ERROR, CRYPTO_ERROR_BASE + 80);
    assert_eq!(ALERT_NO_APPLICATION_PROTOCOL, CRYPTO_ERROR_BASE + 120);
}
