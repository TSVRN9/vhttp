use quic::codes::CRYPTO_BUFFER_EXCEEDED;
use quic::crypto_stream::*;

fn read(c: &mut CryptoStream) -> Vec<u8> {
    let mut out = Vec::new();
    c.read(&mut out);
    out
}

#[test]
fn crypto_reorder_4096() {
    let mut c = CryptoStream::new();
    assert_eq!(c.on_crypto(1, &[0x11; 4095]), Ok(()));
    assert_eq!(read(&mut c), b"");
    assert_eq!(c.on_crypto(0, &[0x10]), Ok(()));
    let mut want = vec![0x10];
    want.extend_from_slice(&[0x11; 4095]);
    assert_eq!(read(&mut c), want);
}

#[test]
fn crypto_limit() {
    assert_eq!(CryptoStream::new().on_crypto(16383, &[1]), Ok(()));
    assert_eq!(CryptoStream::new().on_crypto(16384, &[1]), Err(CRYPTO_BUFFER_EXCEEDED));
    let mut c = CryptoStream::new();
    assert_eq!(c.on_crypto(0, &[0; 100]), Ok(()));
    assert_eq!(read(&mut c).len(), 100);
    assert_eq!(c.on_crypto(16483, &[1]), Ok(()));
    assert_eq!(c.on_crypto(16484, &[1]), Err(CRYPTO_BUFFER_EXCEEDED));
}

#[test]
fn crypto_duplicate() {
    let mut c = CryptoStream::new();
    let d: Vec<u8> = (1..=10).collect();
    assert_eq!(c.on_crypto(0, &d), Ok(()));
    assert_eq!(read(&mut c), d);
    assert_eq!(c.on_crypto(0, &d), Ok(()));
    assert_eq!(read(&mut c), b"");
    assert_eq!(c.on_crypto(5, &[6, 7, 8, 9, 10, 11]), Ok(()));
    assert_eq!(read(&mut c), [11]);
}
