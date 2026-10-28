use h3::qpack::huffman::huffman_decode;
use h3::qpack::huffman_table::huff_code;

/// Reference encoder: codes packed MSB-first, final byte padded with ones (RFC 7541 §5.2).
fn encode(s: &[u8]) -> Vec<u8> {
    let (mut acc, mut n, mut out) = (0u64, 0u32, Vec::new());
    for &b in s {
        let (code, len) = huff_code(b as u16);
        acc = (acc << len) | code as u64;
        n += len as u32;
        while n >= 8 {
            n -= 8;
            out.push((acc >> n) as u8);
        }
    }
    if n > 0 {
        out.push(((acc << (8 - n)) | ((1 << (8 - n)) - 1)) as u8);
    }
    out
}

fn dec(hex: &str) -> Option<Vec<u8>> {
    let h: String = hex.split_whitespace().collect();
    let bytes: Vec<u8> = (0..h.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&h[i..i + 2], 16).unwrap())
        .collect();
    huffman_decode(&bytes)
}

#[test]
fn rfc7541_c4_strings() {
    assert_eq!(
        dec("f1e3 c2e5 f23a 6ba0 ab90 f4ff").as_deref(),
        Some(&b"www.example.com"[..])
    );
    assert_eq!(dec("a8eb 1064 9cbf").as_deref(), Some(&b"no-cache"[..]));
    assert_eq!(
        dec("25a8 49e9 5ba9 7d7f").as_deref(),
        Some(&b"custom-key"[..])
    );
    assert_eq!(
        dec("25a8 49e9 5bb8 e8b4 bf").as_deref(),
        Some(&b"custom-value"[..])
    );
}

#[test]
fn huffman_padding() {
    assert_eq!(huffman_decode(&[]), Some(vec![]));
    assert_eq!(huffman_decode(&[0xff]), None);
    // www.example.com is 89 bits, so its last byte holds 7 padding bits; clear the final one.
    let mut www = encode(b"www.example.com");
    assert_eq!(
        www,
        [0xf1, 0xe3, 0xc2, 0xe5, 0xf2, 0x3a, 0x6b, 0xa0, 0xab, 0x90, 0xf4, 0xff]
    );
    *www.last_mut().unwrap() = 0xfe;
    assert_eq!(huffman_decode(&www), None);
    assert_eq!(huffman_decode(&[0xff, 0xff, 0xff, 0xff]), None);
    for b in 0..=255u8 {
        assert_eq!(huffman_decode(&encode(&[b])), Some(vec![b]), "byte {b}");
    }
    let all: Vec<u8> = (0..=255).collect();
    assert_eq!(huffman_decode(&encode(&all)), Some(all));
}
