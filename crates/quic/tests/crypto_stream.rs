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
    assert_eq!(CryptoStream::new().on_crypto(1, &[1; 16384]), Ok(()));
    assert_eq!(CryptoStream::new().on_crypto(1, &[1; 16385]), Err(CRYPTO_BUFFER_EXCEEDED));
    let mut c = CryptoStream::new();
    assert_eq!(c.on_crypto(0, &[0; 100]), Ok(()));
    assert_eq!(read(&mut c).len(), 100);
    assert_eq!(c.on_crypto(101, &[1; 16383]), Ok(()));
    assert_eq!(c.on_crypto(20000, &[1]), Ok(()));
    assert_eq!(c.on_crypto(20001, &[1]), Err(CRYPTO_BUFFER_EXCEEDED));
}

#[test]
fn crypto_empty_past_window_ok() {
    let mut c = CryptoStream::new();
    assert_eq!(c.on_crypto(16385, &[]), Ok(()));
    assert_eq!(c.on_crypto(1 << 40, &[]), Ok(()));
    assert_eq!(c.end(), 0);
    assert_eq!(c.on_crypto(1, &[1; 16385]), Err(CRYPTO_BUFFER_EXCEEDED));
}

#[test]
fn crypto_empty_keeps_end() {
    let mut c = CryptoStream::new();
    assert_eq!(c.on_crypto(0, &[1; 10]), Ok(()));
    assert_eq!(c.on_crypto(100, &[]), Ok(()));
    assert_eq!(c.end(), 10);
    assert_eq!(read(&mut c), [1; 10]);
    assert_eq!(c.end(), 10);
}

/// The limit counts only out-of-order bytes (RFC 9000 §7.5), those past the contiguous end, so
/// unread in-order data does not use it up.
#[test]
fn crypto_window_from_contiguous() {
    let mut c = CryptoStream::new();
    assert_eq!(c.on_crypto(0, &[1; 13000]), Ok(()));
    assert_eq!(c.on_crypto(16000, &[2; 500]), Ok(()));
    assert_eq!(c.end(), 16500);
    assert_eq!(c.on_crypto(20000, &[3; 15884]), Ok(()));
    assert_eq!(c.on_crypto(40000, &[3]), Err(CRYPTO_BUFFER_EXCEEDED));
    assert_eq!(read(&mut c).len(), 13000);
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

#[test]
fn crypto_tail_then_in_order() {
    // Reviewer's pattern: a far byte pins a 16 KiB buffer, then 1-byte frames arrive in
    // order, each followed by a read. Each read must not copy the buffered tail.
    let t = std::time::Instant::now();
    let mut c = CryptoStream::new();
    assert_eq!(c.on_crypto(16383, &[0xff]), Ok(()));
    for off in 0..16382u64 {
        assert_eq!(c.on_crypto(off, &[off as u8]), Ok(()));
        assert_eq!(read(&mut c), [off as u8]);
    }
    assert_eq!(c.on_crypto(16382, &[0xfe]), Ok(()));
    assert_eq!(read(&mut c), [0xfe, 0xff]);
    assert!(t.elapsed().as_secs() < 5, "took {:?}", t.elapsed());
}

/// RFC 9000 §7.5's floor counts bytes held: one byte far past the contiguous end is one byte.
#[test]
fn crypto_far_single_byte_ok() {
    let mut c = CryptoStream::new();
    assert_eq!(c.on_crypto(20000, &[7]), Ok(()));
    assert_eq!(c.end(), 20001);
    assert_eq!(read(&mut c), b"");
    assert_eq!(c.on_crypto(0, &[1; 20000]), Ok(()));
    let mut want = vec![1; 20000];
    want.push(7);
    assert_eq!(read(&mut c), want);
}

/// The frame taking the held out-of-order bytes from 16384 to 16385 is refused; the one before
/// it is not, whatever the gaps between them.
#[test]
fn crypto_held_bytes_limit() {
    let mut c = CryptoStream::new();
    assert_eq!(c.on_crypto(1, &[1; 8192]), Ok(()));
    assert_eq!(c.on_crypto(100_000, &[2; 8191]), Ok(()));
    assert_eq!(c.on_crypto(1 << 40, &[3]), Ok(()));
    assert_eq!(c.on_crypto((1 << 40) + 10, &[4]), Err(CRYPTO_BUFFER_EXCEEDED));
    // Bytes that become in-order are not out-of-order: room again.
    assert_eq!(c.on_crypto(0, &[0]), Ok(()));
    assert_eq!(c.on_crypto((1 << 40) + 10, &[4]), Ok(()));
}

/// 4096 disjoint runs are held; a 4097th is refused, and a frame joining two runs frees one.
#[test]
fn crypto_range_limit() {
    let mut c = CryptoStream::new();
    for k in 0..4096u64 {
        assert_eq!(c.on_crypto(2 + 2 * k, &[k as u8]), Ok(()));
    }
    assert_eq!(c.on_crypto(2 + 2 * 4096, &[0]), Err(CRYPTO_BUFFER_EXCEEDED));
    assert_eq!(c.on_crypto(3, &[0]), Ok(()));
    assert_eq!(c.on_crypto(2 + 2 * 4096, &[0]), Ok(()));
}

/// The same out-of-order frame twice holds its bytes once.
#[test]
fn crypto_dup_ooo_not_double_counted() {
    let mut c = CryptoStream::new();
    assert_eq!(c.on_crypto(1, &[1; 10000]), Ok(()));
    assert_eq!(c.on_crypto(1, &[1; 10000]), Ok(()));
    assert_eq!(c.on_crypto(20000, &[2; 6384]), Ok(()));
    assert_eq!(c.on_crypto(30000, &[3]), Err(CRYPTO_BUFFER_EXCEEDED));
}

/// The out-of-order store's allocation stays bounded at the limits: 4096 one-byte runs take
/// at most twice their slots plus their bytes (Verus models lengths only, TRUSTED.md).
#[test]
fn crypto_ooo_capacity_bounded() {
    let mut c = CryptoStream::new();
    for k in 0..4096u64 {
        assert_eq!(c.on_crypto(2 + 2 * k, &[1]), Ok(()));
    }
    let slot = std::mem::size_of::<(u64, Vec<u8>)>();
    assert!(c.capacities().1 <= 2 * 4096 * slot + 4096, "{:?}", c.capacities());
}
