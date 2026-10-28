use crypto::sha256::{sha256, SHA256_H0, SHA256_K};

fn h(s: &str) -> Vec<u8> {
    let s: String = s.chars().filter(|c| !c.is_whitespace()).collect();
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect()
}

#[test]
fn fips180_examples() {
    assert_eq!(sha256(b"abc").to_vec(), h("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"));
    assert_eq!(
        sha256(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq").to_vec(),
        h("248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1")
    );
    assert_eq!(sha256(b"").to_vec(), h("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"));
}

// floor(root(x)) by binary search on u128
fn iroot(x: u128, k: u32, hi: u128) -> u128 {
    let (mut lo, mut hi) = (0u128, hi);
    while lo < hi {
        let m = lo + (hi - lo + 1) / 2;
        if m.pow(k) <= x { lo = m } else { hi = m - 1 }
    }
    lo
}

#[test]
fn sha256_constants_from_roots() {
    let mut primes = vec![];
    let mut n = 2u128;
    while primes.len() < 64 {
        if primes.iter().all(|p| n % p != 0) { primes.push(n) }
        n += 1;
    }
    for t in 0..64 {
        // 2^35 bounds the cube root of p<<96 (< 2^105)
        assert_eq!(SHA256_K[t], iroot(primes[t] << 96, 3, 1 << 36) as u32, "K[{t}]");
    }
    for i in 0..8 {
        assert_eq!(SHA256_H0[i], iroot(primes[i] << 64, 2, 1 << 40) as u32, "H0[{i}]");
    }
    assert_eq!((SHA256_K[0], SHA256_K[63], SHA256_H0[0], SHA256_H0[7]), (0x428a2f98, 0xc67178f2, 0x6a09e667, 0x5be0cd19));
}
