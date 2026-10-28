#![allow(dead_code)]

/// Decodes a hex string, ignoring whitespace.
pub fn hex(s: &str) -> Vec<u8> {
    let d: Vec<u8> = s.bytes().filter(|c| !c.is_ascii_whitespace()).collect();
    assert!(d.len() % 2 == 0, "odd hex length");
    d.chunks(2)
        .map(|p| u8::from_str_radix(std::str::from_utf8(p).unwrap(), 16).unwrap())
        .collect()
}

/// One length assert per vector; vectors are added by later tasks.
#[test]
fn vectors_intact() {
    assert_eq!(hex("00ff\n 13"), [0x00, 0xff, 0x13]);
}
