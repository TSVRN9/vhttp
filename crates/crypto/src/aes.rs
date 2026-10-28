//! AES-128 block cipher (FIPS 197): spec and verified constant-time-style exec code.
#[allow(unused_imports)]
use crate::bytes::*;
use vstd::prelude::*;

verus! {

/// FIPS 197-upd1 §4.2 eq. (4.5) xtime: multiplication by x in GF(2^8) modulo x^8 + x^4 + x^3 + x + 1.
pub open spec fn xtime(b: u8) -> u8 {
    if b & 0x80 != 0 {
        ((b & 0x7f) << 1) ^ 0x1b
    } else {
        b << 1
    }
}

/// FIPS 197 §4.2: GF(2^8) product as shift-and-xtime over the low `n` bits of `b`.
pub open spec fn gmul_n(a: u8, b: u8, n: nat) -> u8
    decreases n,
{
    if n == 0 {
        0
    } else {
        (if b & 1 == 1 {
            a
        } else {
            0u8
        }) ^ gmul_n(xtime(a), b >> 1, (n - 1) as nat)
    }
}

/// FIPS 197 §4.2: GF(2^8) multiplication.
pub open spec fn gmul(a: u8, b: u8) -> u8 {
    gmul_n(a, b, 8)
}

/// FIPS 197-upd1 §4.4 eq. (4.11): b^n in GF(2^8).
pub open spec fn gpow(b: u8, n: nat) -> u8
    decreases n,
{
    if n == 0 {
        1
    } else {
        gmul(b, gpow(b, (n - 1) as nat))
    }
}

/// FIPS 197 §5.1.1: multiplicative inverse in GF(2^8), b^254, with 0 mapped to 0.
pub open spec fn ginv(b: u8) -> u8 {
    gpow(b, 254)
}

/// FIPS 197-upd1 §5.1.1 eq. (5.3): bit i of the affine transformation of x, with c = 0x63.
pub open spec fn sbox_bit(x: u8, i: nat) -> u8 {
    ((x >> (i as u8)) ^ (x >> (((i + 4) % 8) as u8)) ^ (x >> (((i + 5) % 8) as u8)) ^ (x >> (
    ((i + 6) % 8) as u8)) ^ (x >> (((i + 7) % 8) as u8)) ^ (0x63u8 >> (i as u8))) & 1
}

/// FIPS 197-upd1 §5.1.1 eq. (5.3): bits 0..n of the affine transformation of x, assembled into a byte.
pub open spec fn sbox_bits(x: u8, n: nat) -> u8
    decreases n,
{
    if n == 0 {
        0
    } else {
        sbox_bits(x, (n - 1) as nat) | (sbox_bit(x, (n - 1) as nat) << (((n - 1) as nat) as u8))
    }
}

/// FIPS 197 §5.1.1: SubBytes substitution of one byte, defined algebraically.
pub open spec fn sbox(b: u8) -> u8 {
    sbox_bits(ginv(b), 8)
}

/// FIPS 197 §5.2: RotWord.
pub open spec fn rot_word(w: Seq<u8>) -> Seq<u8> {
    seq![w[1], w[2], w[3], w[0]]
}

/// FIPS 197 §5.2: SubWord.
pub open spec fn sub_word(w: Seq<u8>) -> Seq<u8> {
    Seq::new(4, |i: int| sbox(w[i]))
}

/// FIPS 197 §5.2: Rcon[j] = x^(j-1) in GF(2^8), j >= 1.
pub open spec fn rcon(j: nat) -> u8
    decreases j,
{
    if j <= 1 {
        1
    } else {
        xtime(rcon((j - 1) as nat))
    }
}

/// FIPS 197 §5.2, Algorithm 2 (Nk = 4): word w[i] of the expanded key.
pub open spec fn key_word(key: Seq<u8>, i: nat) -> Seq<u8>
    decreases i,
{
    if i < 4 {
        key.subrange(4 * i as int, 4 * i + 4 as int)
    } else {
        let prev = key_word(key, (i - 1) as nat);
        let temp = if i % 4 == 0 {
            xor_bytes(sub_word(rot_word(prev)), seq![rcon(i / 4), 0u8, 0u8, 0u8])
        } else {
            prev
        };
        xor_bytes(key_word(key, (i - 4) as nat), temp)
    }
}

/// FIPS 197 §5.1.4: the round key for `round`, words w[4*round .. 4*round+3].
pub open spec fn round_key(key: Seq<u8>, round: nat) -> Seq<u8> {
    key_word(key, 4 * round) + key_word(key, 4 * round + 1) + key_word(key, 4 * round + 2)
        + key_word(key, 4 * round + 3)
}

/// FIPS 197 §5.1.1 SubBytes. State s[r][c] = s[r + 4c] (§3.4).
pub open spec fn sub_bytes(s: Seq<u8>) -> Seq<u8> {
    Seq::new(16, |i: int| sbox(s[i]))
}

/// FIPS 197 §5.1.2 ShiftRows: s'[r][c] = s[r][(c + r) mod 4].
pub open spec fn shift_rows(s: Seq<u8>) -> Seq<u8> {
    Seq::new(16, |i: int| s[i % 4 + 4 * (((i / 4) + (i % 4)) % 4)])
}

/// FIPS 197 §5.1.3 MixColumns: each column times the matrix 02 03 01 01 (rows rotated right).
pub open spec fn mix_columns(s: Seq<u8>) -> Seq<u8> {
    Seq::new(
        16,
        |i: int|
            {
                let r = i % 4;
                let c = i / 4;
                gmul(2, s[4 * c + r]) ^ gmul(3, s[4 * c + (r + 1) % 4]) ^ s[4 * c + (r + 2) % 4]
                    ^ s[4 * c + (r + 3) % 4]
            },
    )
}

/// FIPS 197 §5.1.4 AddRoundKey.
pub open spec fn add_round_key(s: Seq<u8>, key: Seq<u8>, round: nat) -> Seq<u8> {
    xor_bytes(s, round_key(key, round))
}

/// State after the initial AddRoundKey and `n` full rounds (FIPS 197 §5.1, Algorithm 1).
pub open spec fn aes128_rounds(key: Seq<u8>, block: Seq<u8>, n: nat) -> Seq<u8>
    decreases n,
{
    if n == 0 {
        add_round_key(block, key, 0)
    } else {
        add_round_key(
            mix_columns(shift_rows(sub_bytes(aes128_rounds(key, block, (n - 1) as nat)))),
            key,
            n,
        )
    }
}

/// FIPS 197 §5.1, Algorithm 1 (Nr = 10): the final round omits MixColumns.
pub open spec fn spec_aes128_encrypt(key: Seq<u8>, block: Seq<u8>) -> Seq<u8> {
    add_round_key(shift_rows(sub_bytes(aes128_rounds(key, block, 9))), key, 10)
}

// FIPS 197 §4.2 eq. (4.5): xtime as a masked xor, no branch on b.
proof fn bv_xtime(b: u8) by (bit_vector)
    ensures
        (b >> 7) * 0x1b <= 0x1b,
        ((b << 1) ^ (((b >> 7) * 0x1b) as u8)) == (if b & 0x80 != 0 {
            ((b & 0x7f) << 1) ^ 0x1b
        } else {
            b << 1
        }),
{
}

// FIPS 197 §4.2 eq. (4.5): constant-time xtime.
fn xtime_ct(b: u8) -> (r: u8)
    ensures
        r == xtime(b),
{
    proof {
        bv_xtime(b);
    }
    (b << 1) ^ ((b >> 7) * 0x1b)
}

// FIPS 197 §4.2: select a when bit 0 of b is set, as a mask.
proof fn bv_sel8(a: u8, b: u8) by (bit_vector)
    ensures
        (b & 1) * 0xff <= 0xff,
        (a & (((b & 1) * 0xff) as u8)) == (if b & 1 == 1 {
            a
        } else {
            0u8
        }),
{
}

// FIPS 197 §4.2: xor associativity and identity on bytes; 0u8 ^ p == p gives gmul_ct's
// invariant on loop entry (acc = 0).
proof fn bv_xor8(p: u8, q: u8, s: u8) by (bit_vector)
    ensures
        ((p ^ q) ^ s) == (p ^ (q ^ s)),
        (p ^ 0u8) == p,
        (0u8 ^ p) == p,
{
}

// FIPS 197 §4.2: constant-time GF(2^8) multiplication, 8 masked shift-and-xtime steps.
fn gmul_ct(a: u8, b: u8) -> (r: u8)
    ensures
        r == gmul(a, b),
{
    let mut acc: u8 = 0;
    let mut aa = a;
    let mut bb = b;
    let mut i: usize = 0;
    proof {
        bv_xor8(gmul(a, b), 0, 0);
    }
    while i < 8
        invariant
            i <= 8,
            (acc ^ gmul_n(aa, bb, (8 - i) as nat)) == gmul(a, b),
        decreases 8 - i,
    {
        proof {
            bv_sel8(aa, bb);
            bv_xor8(
                acc,
                if bb & 1 == 1 {
                    aa
                } else {
                    0u8
                },
                gmul_n(xtime(aa), bb >> 1, (8 - i - 1) as nat),
            );
        }
        acc = acc ^ (aa & ((bb & 1) * 0xff));
        aa = xtime_ct(aa);
        bb = bb >> 1;
        i += 1;
    }
    proof {
        bv_xor8(acc, 0, 0);
    }
    acc
}

spec fn sq(x: u8) -> u8 {
    gmul(x, x)
}

// FIPS 197 §5.1.1: x^254 by an addition chain of 13 multiplies.
spec fn ginv_chain(x: u8) -> u8 {
    let x2 = sq(x);
    let x3 = gmul(x2, x);
    let x6 = sq(x3);
    let x7 = gmul(x6, x);
    let x14 = sq(x7);
    let x15 = gmul(x14, x);
    let x30 = sq(x15);
    let x31 = gmul(x30, x);
    let x62 = sq(x31);
    let x63 = gmul(x62, x);
    let x126 = sq(x63);
    let x127 = gmul(x126, x);
    sq(x127)
}

// FIPS 197 §5.1.1: the affine map, written as byte rotations.
spec fn affine(x: u8) -> u8 {
    x ^ ((x << 1) | (x >> 7)) ^ ((x << 2) | (x >> 6)) ^ ((x << 3) | (x >> 5)) ^ ((x << 4) | (x >> 4))
        ^ 0x63
}

spec fn sbox_chunk_ok(lo: nat, hi: nat) -> bool
    decreases hi - lo,
{
    if lo >= hi {
        true
    } else {
        affine(ginv_chain(lo as u8)) == sbox(lo as u8) && sbox_chunk_ok(lo + 1, hi)
    }
}

proof fn lemma_sbox_chunk_0()
    ensures
        sbox_chunk_ok(0, 16),
{
    assert(sbox_chunk_ok(0, 16)) by (compute_only);
}

proof fn lemma_sbox_chunk_1()
    ensures
        sbox_chunk_ok(16, 32),
{
    assert(sbox_chunk_ok(16, 32)) by (compute_only);
}

proof fn lemma_sbox_chunk_2()
    ensures
        sbox_chunk_ok(32, 48),
{
    assert(sbox_chunk_ok(32, 48)) by (compute_only);
}

proof fn lemma_sbox_chunk_3()
    ensures
        sbox_chunk_ok(48, 64),
{
    assert(sbox_chunk_ok(48, 64)) by (compute_only);
}

proof fn lemma_sbox_chunk_4()
    ensures
        sbox_chunk_ok(64, 80),
{
    assert(sbox_chunk_ok(64, 80)) by (compute_only);
}

proof fn lemma_sbox_chunk_5()
    ensures
        sbox_chunk_ok(80, 96),
{
    assert(sbox_chunk_ok(80, 96)) by (compute_only);
}

proof fn lemma_sbox_chunk_6()
    ensures
        sbox_chunk_ok(96, 112),
{
    assert(sbox_chunk_ok(96, 112)) by (compute_only);
}

proof fn lemma_sbox_chunk_7()
    ensures
        sbox_chunk_ok(112, 128),
{
    assert(sbox_chunk_ok(112, 128)) by (compute_only);
}

proof fn lemma_sbox_chunk_8()
    ensures
        sbox_chunk_ok(128, 144),
{
    assert(sbox_chunk_ok(128, 144)) by (compute_only);
}

proof fn lemma_sbox_chunk_9()
    ensures
        sbox_chunk_ok(144, 160),
{
    assert(sbox_chunk_ok(144, 160)) by (compute_only);
}

proof fn lemma_sbox_chunk_10()
    ensures
        sbox_chunk_ok(160, 176),
{
    assert(sbox_chunk_ok(160, 176)) by (compute_only);
}

proof fn lemma_sbox_chunk_11()
    ensures
        sbox_chunk_ok(176, 192),
{
    assert(sbox_chunk_ok(176, 192)) by (compute_only);
}

proof fn lemma_sbox_chunk_12()
    ensures
        sbox_chunk_ok(192, 208),
{
    assert(sbox_chunk_ok(192, 208)) by (compute_only);
}

proof fn lemma_sbox_chunk_13()
    ensures
        sbox_chunk_ok(208, 224),
{
    assert(sbox_chunk_ok(208, 224)) by (compute_only);
}

proof fn lemma_sbox_chunk_14()
    ensures
        sbox_chunk_ok(224, 240),
{
    assert(sbox_chunk_ok(224, 240)) by (compute_only);
}

proof fn lemma_sbox_chunk_15()
    ensures
        sbox_chunk_ok(240, 256),
{
    assert(sbox_chunk_ok(240, 256)) by (compute_only);
}

proof fn lemma_sbox_chunk_elem(lo: nat, hi: nat, x: nat)
    requires
        sbox_chunk_ok(lo, hi),
        lo <= x < hi,
        x < 256,
    ensures
        affine(ginv_chain(x as u8)) == sbox(x as u8),
    decreases x - lo,
{
    if x > lo {
        lemma_sbox_chunk_elem(lo + 1, hi, x);
    }
}

// FIPS 197 §5.1.1: the chain-and-affine S-box equals the spec S-box on all 256 inputs.
proof fn lemma_sbox_chain(x: u8)
    ensures
        affine(ginv_chain(x)) == sbox(x),
{
    hide(sbox);
    hide(ginv_chain);
    hide(affine);
    hide(sbox_chunk_ok);
    lemma_sbox_chunk_0();
    lemma_sbox_chunk_1();
    lemma_sbox_chunk_2();
    lemma_sbox_chunk_3();
    lemma_sbox_chunk_4();
    lemma_sbox_chunk_5();
    lemma_sbox_chunk_6();
    lemma_sbox_chunk_7();
    lemma_sbox_chunk_8();
    lemma_sbox_chunk_9();
    lemma_sbox_chunk_10();
    lemma_sbox_chunk_11();
    lemma_sbox_chunk_12();
    lemma_sbox_chunk_13();
    lemma_sbox_chunk_14();
    lemma_sbox_chunk_15();
    lemma_sbox_chunk_elem(16 * (x / 16) as nat, 16 * (x / 16) as nat + 16, x as nat);
}

// FIPS 197 §5.1.1: constant-time S-box, no table and no branch on x.
// ponytail: S-box = 13 constant-time GF(2^8) multiplies (8 masked steps each) + affine, ≈<measured> µs per AES block (release, Task 5 gcm_64kib); upgrade: Boyar–Peralta bitsliced circuit, proved by the same chunk lemmas, or AES-NI behind an equivalence proof
pub(crate) fn sbox_ct(x: u8) -> (r: u8)
    ensures
        r == sbox(x),
{
    let x2 = gmul_ct(x, x);
    let x3 = gmul_ct(x2, x);
    let x6 = gmul_ct(x3, x3);
    let x7 = gmul_ct(x6, x);
    let x14 = gmul_ct(x7, x7);
    let x15 = gmul_ct(x14, x);
    let x30 = gmul_ct(x15, x15);
    let x31 = gmul_ct(x30, x);
    let x62 = gmul_ct(x31, x31);
    let x63 = gmul_ct(x62, x);
    let x126 = gmul_ct(x63, x63);
    let x127 = gmul_ct(x126, x);
    let y = gmul_ct(x127, x127);
    proof {
        lemma_sbox_chain(x);
    }
    y ^ ((y << 1) | (y >> 7)) ^ ((y << 2) | (y >> 6)) ^ ((y << 3) | (y >> 5)) ^ ((y << 4) | (y >> 4))
        ^ 0x63
}

// FIPS 197 §5.1.1 SubBytes.
fn sub_bytes_exec(s: &[u8; 16]) -> (r: [u8; 16])
    ensures
        r@ == sub_bytes(s@),
{
    hide(sbox);
    let mut r = [0u8; 16];
    let mut i: usize = 0;
    while i < 16
        invariant
            i <= 16,
            forall|j: int| 0 <= j < i ==> #[trigger] r@[j] == sbox(s@[j]),
        decreases 16 - i,
    {
        r[i] = sbox_ct(s[i]);
        i += 1;
    }
    assert(r@ =~= sub_bytes(s@));
    r
}

// FIPS 197 §5.1.2 ShiftRows; the index depends only on the public position i.
fn shift_rows_exec(s: &[u8; 16]) -> (r: [u8; 16])
    ensures
        r@ == shift_rows(s@),
{
    let mut r = [0u8; 16];
    let mut i: usize = 0;
    while i < 16
        invariant
            i <= 16,
            forall|j: int| 0 <= j < i ==> r@[j] == s@[j % 4 + 4 * (((j / 4) + (j % 4)) % 4)],
        decreases 16 - i,
    {
        r[i] = s[i % 4 + 4 * ((i / 4 + i % 4) % 4)];
        i += 1;
    }
    assert(r@ =~= shift_rows(s@));
    r
}

// FIPS 197 §5.1.3 MixColumns.
fn mix_columns_exec(s: &[u8; 16]) -> (r: [u8; 16])
    ensures
        r@ == mix_columns(s@),
{
    hide(gmul);
    let mut out = [0u8; 16];
    let mut i: usize = 0;
    while i < 16
        invariant
            i <= 16,
            forall|j: int|
                0 <= j < i ==> out@[j] == gmul(2, s@[4 * (j / 4) + j % 4]) ^ gmul(
                    3,
                    s@[4 * (j / 4) + (j % 4 + 1) % 4],
                ) ^ s@[4 * (j / 4) + (j % 4 + 2) % 4] ^ s@[4 * (j / 4) + (j % 4 + 3) % 4],
        decreases 16 - i,
    {
        let r = i % 4;
        let c = i / 4;
        out[i] = gmul_ct(2, s[4 * c + r]) ^ gmul_ct(3, s[4 * c + (r + 1) % 4]) ^ s[4 * c + (r + 2)
            % 4] ^ s[4 * c + (r + 3) % 4];
        i += 1;
    }
    assert(out@ =~= mix_columns(s@));
    out
}

// FIPS 197 §5.2: rk holds the 44 expanded-key words w[0..44] of key, 4 bytes each.
pub(crate) closed spec fn rk_ok(rk: Seq<u8>, key: Seq<u8>) -> bool {
    rk.len() == 176 && forall|j: nat|
        j < 44 ==> rk.subrange(4 * j as int, 4 * j + 4 as int) == #[trigger] key_word(key, j)
}

// FIPS 197 §5.1.4: round key `r` is bytes 16r..16r+16 of the expanded key.
proof fn lemma_round_key(rk: Seq<u8>, key: Seq<u8>, r: nat)
    requires
        rk_ok(rk, key),
        r <= 10,
    ensures
        rk.subrange(16 * r as int, 16 * r + 16 as int) =~= round_key(key, r),
{
    hide(key_word);
    let w0 = key_word(key, 4 * r);
    let w1 = key_word(key, 4 * r + 1);
    let w2 = key_word(key, 4 * r + 2);
    let w3 = key_word(key, 4 * r + 3);
    assert(rk.subrange(16 * r as int, 16 * r + 16 as int) =~= w0 + w1 + w2 + w3);
}

// FIPS 197 §5.1.4 AddRoundKey with round key `round` read from the expanded key.
fn add_round_key_exec(s: &[u8; 16], rk: &[u8; 176], round: usize, Ghost(key): Ghost<Seq<u8>>) -> (r:
    [u8; 16])
    requires
        rk_ok(rk@, key),
        round <= 10,
    ensures
        r@ == add_round_key(s@, key, round as nat),
{
    hide(key_word);
    let mut out = [0u8; 16];
    let mut i: usize = 0;
    while i < 16
        invariant
            i <= 16,
            round <= 10,
            forall|j: int| 0 <= j < i ==> #[trigger] out@[j] == s@[j] ^ rk@[16 * round + j],
        decreases 16 - i,
    {
        out[i] = s[i] ^ rk[16 * round + i];
        i += 1;
    }
    proof {
        lemma_round_key(rk@, key, round as nat);
    }
    assert(out@ =~= add_round_key(s@, key, round as nat));
    out
}

// FIPS 197 §5.2, Algorithm 2 (Nk = 4): the 44-word key schedule, one word per step.
#[verifier::spinoff_prover]
pub(crate) fn expand_key(key: &[u8]) -> (rk: [u8; 176])
    requires
        key@.len() == 16,
    ensures
        rk_ok(rk@, key@),
{
    hide(sbox);
    let mut rk = [0u8; 176];
    let mut i: usize = 0;
    while i < 16
        invariant
            key.len() == 16,
            i <= 16,
            forall|j: int| 0 <= j < i ==> rk@[j] == key@[j],
        decreases 16 - i,
    {
        rk[i] = key[i];
        i += 1;
    }
    assert forall|j: nat| j < 4 implies rk@.subrange(4 * j as int, 4 * j + 4 as int)
        == #[trigger] key_word(key@, j) by {
        assert(rk@.subrange(4 * j as int, 4 * j + 4 as int) =~= key@.subrange(
            4 * j as int,
            4 * j + 4 as int,
        ));
    }
    let mut i: usize = 4;
    let mut rc: u8 = 1;
    while i < 44
        invariant
            4 <= i <= 44,
            forall|j: nat|
                j < i ==> rk@.subrange(4 * j as int, 4 * j + 4 as int) == #[trigger] key_word(
                    key@,
                    j,
                ),
            rc == rcon((i / 4) as nat),
        decreases 44 - i,
    {
        let ghost old = rk@;
        let ghost prev = key_word(key@, (i - 1) as nat);
        let ghost back = key_word(key@, (i - 4) as nat);
        let p = 4 * (i - 1);
        let w0 = rk[p];
        let w1 = rk[p + 1];
        let w2 = rk[p + 2];
        let w3 = rk[p + 3];
        proof {
            assert(prev[0] == w0 && prev[1] == w1 && prev[2] == w2 && prev[3] == w3);
        }
        // FIPS 197 §5.2: temp = SubWord(RotWord(temp)) xor Rcon[i/Nk] when i mod Nk = 0.
        let (t0, t1, t2, t3) = if i % 4 == 0 {
            (sbox_ct(w1) ^ rc, sbox_ct(w2) ^ 0, sbox_ct(w3) ^ 0, sbox_ct(w0) ^ 0)
        } else {
            (w0, w1, w2, w3)
        };
        let ghost temp = if i % 4 == 0 {
            xor_bytes(sub_word(rot_word(prev)), seq![rcon((i / 4) as nat), 0u8, 0u8, 0u8])
        } else {
            prev
        };
        proof {
            assert(temp[0] == t0 && temp[1] == t1 && temp[2] == t2 && temp[3] == t3);
        }
        let q = 4 * (i - 4);
        let b0 = rk[q];
        let b1 = rk[q + 1];
        let b2 = rk[q + 2];
        let b3 = rk[q + 3];
        proof {
            assert(back[0] == b0 && back[1] == b1 && back[2] == b2 && back[3] == b3);
        }
        rk[4 * i] = b0 ^ t0;
        rk[4 * i + 1] = b1 ^ t1;
        rk[4 * i + 2] = b2 ^ t2;
        rk[4 * i + 3] = b3 ^ t3;
        proof {
            assert(key_word(key@, i as nat) == xor_bytes(back, temp));
            assert forall|j: nat| j < i + 1 implies rk@.subrange(4 * j as int, 4 * j + 4 as int)
                == #[trigger] key_word(key@, j) by {
                if j < i {
                    assert(rk@.subrange(4 * j as int, 4 * j + 4 as int) =~= old.subrange(
                        4 * j as int,
                        4 * j + 4 as int,
                    ));
                } else {
                    assert(rk@.subrange(4 * j as int, 4 * j + 4 as int) =~= xor_bytes(back, temp));
                }
            }
        }
        // FIPS 197 §5.2: Rcon[j + 1] = xtime(Rcon[j]) for j >= 1.
        if (i + 1) % 4 == 0 {
            proof {
                assert((i + 1) / 4 == i / 4 + 1);
            }
            rc = xtime_ct(rc);
        }
        i += 1;
    }
    rk
}

// FIPS 197 §5.1, Algorithm 1 (Nr = 10) on an expanded key.
#[verifier::spinoff_prover]
pub(crate) fn encrypt_rk(rk: &[u8; 176], Ghost(key): Ghost<Seq<u8>>, block: &[u8]) -> (r: [u8; 16])
    requires
        rk_ok(rk@, key),
        block@.len() == 16,
    ensures
        r@ == spec_aes128_encrypt(key, block@),
{
    hide(key_word);
    hide(sbox);
    hide(round_key);
    hide(sub_bytes);
    hide(shift_rows);
    hide(mix_columns);
    // FIPS 197 §5.1.4: the initial AddRoundKey, round key 0.
    let mut st = [0u8; 16];
    let mut k: usize = 0;
    while k < 16
        invariant
            block.len() == 16,
            k <= 16,
            forall|j: int| 0 <= j < k ==> #[trigger] st@[j] == block@[j] ^ rk@[j],
        decreases 16 - k,
    {
        st[k] = block[k] ^ rk[k];
        k += 1;
    }
    proof {
        lemma_round_key(rk@, key, 0);
        assert(st@ =~= add_round_key(block@, key, 0));
    }
    let mut r: usize = 1;
    while r < 10
        invariant
            1 <= r <= 10,
            rk_ok(rk@, key),
            st@ == aes128_rounds(key, block@, (r - 1) as nat),
        decreases 10 - r,
    {
        st = add_round_key_exec(
            &mix_columns_exec(&shift_rows_exec(&sub_bytes_exec(&st))),
            rk,
            r,
            Ghost(key),
        );
        r += 1;
    }
    // FIPS 197 §5.1: the final round omits MixColumns.
    add_round_key_exec(&shift_rows_exec(&sub_bytes_exec(&st)), rk, 10, Ghost(key))
}

/// FIPS 197 §5.1 (Nr = 10), §5.2 (Nk = 4); verified against spec_aes128_encrypt.
// ponytail: key schedule recomputed per call (40 S-boxes, ≈<measured>% of one block); add a pub
// expanded-key type if packet-rate profiling shows it
pub fn aes128_encrypt_block(key: &[u8], block: &[u8]) -> (r: [u8; 16])
    requires
        key@.len() == 16,
        block@.len() == 16,
    ensures
        r@ == spec_aes128_encrypt(key@, block@),
{
    let rk = expand_key(key);
    encrypt_rk(&rk, Ghost(key@), block)
}

} // verus!
