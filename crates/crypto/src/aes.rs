//! AES-128 block cipher (FIPS 197): spec and an exec signature backed by the trusted shim.
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

/// Trusted shim: the body is RustCrypto aes; the ensures is the trusted statement.
#[verifier::external_body]
pub fn aes128_encrypt_block(key: &[u8], block: &[u8]) -> (r: [u8; 16])
    requires
        key@.len() == 16,
        block@.len() == 16,
    ensures
        r@ == spec_aes128_encrypt(key@, block@),
{
    crate::shim::aes128_encrypt_block(key, block)
}

} // verus!
