//! SHA-256 (FIPS 180-4): spec functions and an exec signature backed by the trusted shim.
#[allow(unused_imports)]
use crate::bytes::*;
use vstd::prelude::*;

verus! {

/// FIPS 180-4 §4.2.2: the sixty-four round constants.
pub const SHA256_K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
        0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
        0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
        0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
        0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
        0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
        0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
        0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// FIPS 180-4 §5.3.3: the initial hash value.
pub const SHA256_H0: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// FIPS 180-4 §3.2: addition modulo 2^32.
pub open spec fn add32(a: u32, b: u32) -> u32 {
    ((a + b) % 0x1_0000_0000int) as u32
}

/// FIPS 180-4 §3.2: ROTR^n(x) = (x >> n) | (x << (32 - n)).
pub open spec fn rotr(x: u32, n: u32) -> u32 {
    (x >> n) | (x << (32 - n))
}

/// FIPS 180-4 §4.1.2 (4.2): Ch(x, y, z).
pub open spec fn ch(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ ((!x) & z)
}

/// FIPS 180-4 §4.1.2 (4.3): Maj(x, y, z).
pub open spec fn maj(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ (x & z) ^ (y & z)
}

/// FIPS 180-4 §4.1.2 (4.4): Sigma0.
pub open spec fn bsig0(x: u32) -> u32 {
    rotr(x, 2) ^ rotr(x, 13) ^ rotr(x, 22)
}

/// FIPS 180-4 §4.1.2 (4.5): Sigma1.
pub open spec fn bsig1(x: u32) -> u32 {
    rotr(x, 6) ^ rotr(x, 11) ^ rotr(x, 25)
}

/// FIPS 180-4 §4.1.2 (4.6): sigma0.
pub open spec fn ssig0(x: u32) -> u32 {
    rotr(x, 7) ^ rotr(x, 18) ^ (x >> 3)
}

/// FIPS 180-4 §4.1.2 (4.7): sigma1.
pub open spec fn ssig1(x: u32) -> u32 {
    rotr(x, 17) ^ rotr(x, 19) ^ (x >> 10)
}

/// FIPS 180-4 §5.1.1: m, a 1 bit (0x80), k zero bits with l + 1 + k = 448 mod 512, then l as
/// a 64-bit big-endian bit length.
pub open spec fn sha256_pad(m: Seq<u8>) -> Seq<u8> {
    let zeros = (55 - m.len() as int) % 64int;
    m + seq![0x80u8] + Seq::new(zeros as nat, |i: int| 0u8) + i2osp(8 * m.len(), 8)
}

/// FIPS 180-4 §6.2.2 step 1: the message schedule word W_t of a 64-byte block.
pub open spec fn sha256_w(block: Seq<u8>, t: nat) -> u32
    decreases t,
{
    if t < 16 {
        os2ip(block.subrange(4 * t as int, 4 * t as int + 4)) as u32
    } else {
        add32(
            add32(
                add32(ssig1(sha256_w(block, (t - 2) as nat)), sha256_w(block, (t - 7) as nat)),
                ssig0(sha256_w(block, (t - 15) as nat)),
            ),
            sha256_w(block, (t - 16) as nat),
        )
    }
}

/// FIPS 180-4 §6.2.2 step 3: one round t on the working variables (a, b, c, d, e, f, g, h).
pub open spec fn sha256_round(block: Seq<u8>, v: Seq<u32>, t: nat) -> Seq<u32> {
    let t1 = add32(
        add32(add32(add32(v[7], bsig1(v[4])), ch(v[4], v[5], v[6])), SHA256_K@[t as int]),
        sha256_w(block, t),
    );
    let t2 = add32(bsig0(v[0]), maj(v[0], v[1], v[2]));
    seq![add32(t1, t2), v[0], v[1], v[2], add32(v[3], t1), v[4], v[5], v[6]]
}

/// FIPS 180-4 §6.2.2 step 3: the first n rounds, starting from the working variables v.
pub open spec fn sha256_rounds(block: Seq<u8>, v: Seq<u32>, n: nat) -> Seq<u32>
    decreases n,
{
    if n == 0 {
        v
    } else {
        sha256_round(block, sha256_rounds(block, v, (n - 1) as nat), (n - 1) as nat)
    }
}

/// FIPS 180-4 §6.2.2 steps 2-4: compress one 64-byte block into the hash value h.
pub open spec fn sha256_compress(h: Seq<u32>, block: Seq<u8>) -> Seq<u32> {
    let v = sha256_rounds(block, h, 64);
    Seq::new(8, |i: int| add32(h[i], v[i]))
}

/// FIPS 180-4 §6.2.2: fold the compression function over the 64-byte blocks of m.
pub open spec fn sha256_blocks(h: Seq<u32>, m: Seq<u8>) -> Seq<u32>
    decreases m.len(),
{
    if m.len() < 64 {
        h
    } else {
        sha256_blocks(sha256_compress(h, m.take(64)), m.skip(64))
    }
}

/// FIPS 180-4 §6.2.2 step 4: the words H_0..H_7 concatenated big-endian.
pub open spec fn sha256_words_be(w: Seq<u32>) -> Seq<u8>
    decreases w.len(),
{
    if w.len() == 0 {
        Seq::empty()
    } else {
        sha256_words_be(w.drop_last()) + i2osp(w.last() as nat, 4)
    }
}

/// FIPS 180-4 §6.2: SHA-256 of the message m (32 octets).
pub open spec fn spec_sha256(m: Seq<u8>) -> Seq<u8> {
    sha256_words_be(sha256_blocks(SHA256_H0@, sha256_pad(m)))
}

proof fn lemma_sha256_words_be_len(w: Seq<u32>)
    ensures
        sha256_words_be(w).len() == 4 * w.len(),
    decreases w.len(),
{
    if w.len() > 0 {
        lemma_sha256_words_be_len(w.drop_last());
        lemma_i2osp_len(w.last() as nat, 4);
    }
}

proof fn lemma_sha256_blocks_len(h: Seq<u32>, m: Seq<u8>)
    requires
        h.len() == 8,
    ensures
        sha256_blocks(h, m).len() == 8,
    decreases m.len(),
{
    if m.len() >= 64 {
        let c = sha256_compress(h, m.take(64));
        assert(c.len() == 8);
        lemma_sha256_blocks_len(c, m.skip(64));
    }
}

/// `spec_sha256` yields 32 octets.
pub proof fn lemma_spec_sha256_len(m: Seq<u8>)
    ensures
        spec_sha256(m).len() == 32,
{
    assert(SHA256_H0@.len() == 8);
    lemma_sha256_blocks_len(SHA256_H0@, sha256_pad(m));
    lemma_sha256_words_be_len(sha256_blocks(SHA256_H0@, sha256_pad(m)));
}

proof fn lemma_wrapping_add32(a: u32, b: u32)
    ensures
        vstd::wrapping::u32_specs::wrapping_add(a, b) == add32(a, b),
{
}

// FIPS 180-4 §3.2: addition modulo 2^32.
fn add32_exec(a: u32, b: u32) -> (r: u32)
    ensures
        r == add32(a, b),
{
    proof {
        lemma_wrapping_add32(a, b);
    }
    a.wrapping_add(b)
}

// FIPS 180-4 §4.1.2 (4.2).
fn ch_exec(x: u32, y: u32, z: u32) -> (r: u32)
    ensures
        r == ch(x, y, z),
{
    (x & y) ^ ((!x) & z)
}

// FIPS 180-4 §4.1.2 (4.3).
fn maj_exec(x: u32, y: u32, z: u32) -> (r: u32)
    ensures
        r == maj(x, y, z),
{
    (x & y) ^ (x & z) ^ (y & z)
}

// FIPS 180-4 §4.1.2 (4.4).
fn bsig0_exec(x: u32) -> (r: u32)
    ensures
        r == bsig0(x),
{
    ((x >> 2) | (x << 30)) ^ ((x >> 13) | (x << 19)) ^ ((x >> 22) | (x << 10))
}

// FIPS 180-4 §4.1.2 (4.5).
fn bsig1_exec(x: u32) -> (r: u32)
    ensures
        r == bsig1(x),
{
    ((x >> 6) | (x << 26)) ^ ((x >> 11) | (x << 21)) ^ ((x >> 25) | (x << 7))
}

// FIPS 180-4 §4.1.2 (4.6).
fn ssig0_exec(x: u32) -> (r: u32)
    ensures
        r == ssig0(x),
{
    ((x >> 7) | (x << 25)) ^ ((x >> 18) | (x << 14)) ^ (x >> 3)
}

// FIPS 180-4 §4.1.2 (4.7).
fn ssig1_exec(x: u32) -> (r: u32)
    ensures
        r == ssig1(x),
{
    ((x >> 17) | (x << 15)) ^ ((x >> 19) | (x << 13)) ^ (x >> 10)
}

proof fn bv_be32(b0: u32, b1: u32, b2: u32, b3: u32) by (bit_vector)
    requires
        b0 < 256,
        b1 < 256,
        b2 < 256,
        b3 < 256,
    ensures
        (b0 << 24) | (b1 << 16) | (b2 << 8) | b3 == b0 * 0x100_0000 + b1 * 0x1_0000 + b2 * 0x100
            + b3,
{
}

proof fn lemma_os2ip4(s: Seq<u8>)
    requires
        s.len() == 4,
    ensures
        os2ip(s) == s[0] * 0x100_0000 + s[1] * 0x1_0000 + s[2] * 0x100 + s[3],
{
    reveal_with_fuel(os2ip, 5);
    let s3 = s.drop_last();
    let s2 = s3.drop_last();
    let s1 = s2.drop_last();
    assert(s1.drop_last() =~= Seq::<u8>::empty());
    assert(s1 =~= seq![s[0]]);
    assert(s2 =~= seq![s[0], s[1]]);
    assert(s3 =~= seq![s[0], s[1], s[2]]);
}

// FIPS 180-4 §6.2.2 step 1: the message schedule W_0..W_63 of the block src[off..off + 64].
fn schedule(src: &[u8], off: usize) -> (w: [u32; 64])
    requires
        off + 64 <= src@.len(),
    ensures
        forall|j: int| 0 <= j < 64 ==> w@[j] == sha256_w(src@.subrange(off as int, off + 64), j as nat),
{
    let ghost block = src@.subrange(off as int, off + 64);
    let mut w = [0u32; 64];
    let mut t: usize = 0;
    while t < 16
        invariant
            off + 64 <= src.len(),
            block == src@.subrange(off as int, off + 64),
            t <= 16,
            forall|j: int| 0 <= j < t ==> w@[j] == sha256_w(block, j as nat),
        decreases 16 - t,
    {
        let i = off + 4 * t;
        let b0 = src[i] as u32;
        let b1 = src[i + 1] as u32;
        let b2 = src[i + 2] as u32;
        let b3 = src[i + 3] as u32;
        proof {
            let s = block.subrange(4 * t as int, 4 * t as int + 4);
            lemma_os2ip4(s);
            bv_be32(b0, b1, b2, b3);
            assert(s[0] == src@[i as int] && s[1] == src@[i + 1] && s[2] == src@[i + 2] && s[3]
                == src@[i + 3]);
        }
        w[t] = (b0 << 24) | (b1 << 16) | (b2 << 8) | b3;
        t += 1;
    }
    while t < 64
        invariant
            off + 64 <= src@.len(),
            block == src@.subrange(off as int, off + 64),
            16 <= t <= 64,
            forall|j: int| 0 <= j < t ==> w@[j] == sha256_w(block, j as nat),
        decreases 64 - t,
    {
        w[t] = add32_exec(
            add32_exec(add32_exec(ssig1_exec(w[t - 2]), w[t - 7]), ssig0_exec(w[t - 15])),
            w[t - 16],
        );
        t += 1;
    }
    w
}

// FIPS 180-4 §6.2.2 steps 1-4: compress the block src[off..off + 64] into h.
// Used by sha256 from Task 2 on, which drops this allow.
#[allow(dead_code)]
fn compress(h: &mut [u32; 8], src: &[u8], off: usize)
    requires
        off + 64 <= src@.len(),
    ensures
        final(h)@ == sha256_compress(old(h)@, src@.subrange(off as int, off + 64)),
{
    let ghost block = src@.subrange(off as int, off + 64);
    // FIPS 180-4 §6.2.2 step 1
    let w = schedule(src, off);
    // FIPS 180-4 §6.2.2 step 2
    let (mut a, mut b, mut c, mut d) = (h[0], h[1], h[2], h[3]);
    let (mut e, mut f, mut g, mut hh) = (h[4], h[5], h[6], h[7]);
    assert(seq![a, b, c, d, e, f, g, hh] =~= sha256_rounds(block, old(h)@, 0));
    // FIPS 180-4 §6.2.2 step 3
    // ponytail: one round per iteration, unroll if profiling shows it matters
    let mut t: usize = 0;
    while t < 64
        invariant
            t <= 64,
            h@ == old(h)@,
            forall|j: int| 0 <= j < 64 ==> w@[j] == sha256_w(block, j as nat),
            seq![a, b, c, d, e, f, g, hh] == sha256_rounds(block, old(h)@, t as nat),
        decreases 64 - t,
    {
        let t1 = add32_exec(
            add32_exec(add32_exec(add32_exec(hh, bsig1_exec(e)), ch_exec(e, f, g)), SHA256_K[t]),
            w[t],
        );
        let t2 = add32_exec(bsig0_exec(a), maj_exec(a, b, c));
        hh = g;
        g = f;
        f = e;
        e = add32_exec(d, t1);
        d = c;
        c = b;
        b = a;
        a = add32_exec(t1, t2);
        assert(seq![a, b, c, d, e, f, g, hh] =~= sha256_rounds(block, old(h)@, t as nat + 1));
        t += 1;
    }
    // FIPS 180-4 §6.2.2 step 4
    h[0] = add32_exec(h[0], a);
    h[1] = add32_exec(h[1], b);
    h[2] = add32_exec(h[2], c);
    h[3] = add32_exec(h[3], d);
    h[4] = add32_exec(h[4], e);
    h[5] = add32_exec(h[5], f);
    h[6] = add32_exec(h[6], g);
    h[7] = add32_exec(h[7], hh);
    assert(h@ =~= sha256_compress(old(h)@, block));
}

/// Trusted shim: the body is RustCrypto sha2; the ensures is the trusted statement.
#[verifier::external_body]
pub fn sha256(msg: &[u8]) -> (r: [u8; 32])
    requires
        msg@.len() <= MAX_INPUT_LEN,
    ensures
        r@ == spec_sha256(msg@),
{
    crate::shim::sha256(msg)
}

} // verus!
