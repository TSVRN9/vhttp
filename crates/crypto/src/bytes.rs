//! Shared octet-string specs (RFC 8017 §4).
use vstd::prelude::*;

verus! {

/// Every variable-length input is at most 2^60 bytes, so derived hash inputs stay below
/// FIPS 180-4's 2^64-bit limit.
pub const MAX_INPUT_LEN: usize = 0x1000_0000_0000_0000;

/// RFC 8017 §4.2 OS2IP: big-endian octet string to nonnegative integer.
pub open spec fn os2ip(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        (os2ip(s.drop_last()) * 256 + s.last() as nat) as nat
    }
}

/// RFC 8017 §4.1 I2OSP: integer to big-endian octet string of length `len`.
/// Callers ensure `x < 256^len`; otherwise the low `len` octets are kept.
pub open spec fn i2osp(x: nat, len: nat) -> Seq<u8>
    decreases len,
{
    if len == 0 {
        Seq::empty()
    } else {
        i2osp(x / 256, (len - 1) as nat).push((x % 256) as u8)
    }
}

/// `i2osp` yields exactly `len` octets.
pub proof fn lemma_i2osp_len(x: nat, len: nat)
    ensures
        i2osp(x, len).len() == len,
    decreases len,
{
    if len > 0 {
        lemma_i2osp_len(x / 256, (len - 1) as nat);
    }
}

/// Bytewise XOR; the result has the length of `a`.
pub open spec fn xor_bytes(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| a[i] ^ b[i])
}

/// OS2IP of a concatenation: the prefix is shifted left by the suffix's length in octets.
pub proof fn lemma_os2ip_append(a: Seq<u8>, b: Seq<u8>)
    ensures
        os2ip(a + b) == os2ip(a) * vstd::arithmetic::power::pow(256, b.len()) + os2ip(b),
    decreases b.len(),
{
    reveal(vstd::arithmetic::power::pow);
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        let b1 = b.drop_last();
        assert((a + b).drop_last() =~= a + b1);
        lemma_os2ip_append(a, b1);
        vstd::arithmetic::mul::lemma_mul_is_associative(
            os2ip(a) as int,
            vstd::arithmetic::power::pow(256, b1.len()),
            256,
        );
        vstd::arithmetic::mul::lemma_mul_is_commutative(
            256,
            vstd::arithmetic::power::pow(256, b1.len()),
        );
    }
}

/// I2OSP into la + lb octets splits into the high la octets and the low lb octets.
pub proof fn lemma_i2osp_append(x: nat, la: nat, lb: nat)
    ensures
        i2osp(x, la + lb) == i2osp((x as int / vstd::arithmetic::power::pow(256, lb)) as nat, la) + i2osp(
            (x as int % vstd::arithmetic::power::pow(256, lb)) as nat,
            lb,
        ),
    decreases lb,
{
    reveal(vstd::arithmetic::power::pow);
    if lb == 0 {
        assert(i2osp(x, la) + i2osp(0, 0) =~= i2osp(x, la));
    } else {
        let xi = x as int;
        let p1 = vstd::arithmetic::power::pow(256, (lb - 1) as nat);
        vstd::arithmetic::power::lemma_pow_positive(256, (lb - 1) as nat);
        let y = xi % (256 * p1);
        lemma_i2osp_append(x / 256, la, (lb - 1) as nat);
        vstd::arithmetic::div_mod::lemma_div_denominator(xi, 256, p1);
        vstd::arithmetic::div_mod::lemma_mod_breakdown(xi, 256, p1);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(xi / 256, p1);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(xi, 256 * p1);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
            y,
            256,
            (xi / 256) % p1,
            xi % 256,
        );
        assert(la + lb - 1 == la + (lb - 1) as nat);
        assert(i2osp(x, la + lb) =~= i2osp((xi / (256 * p1)) as nat, la) + i2osp(y as nat, lb));
    }
}

/// OS2IP of s is below 256^|s|.
pub proof fn lemma_os2ip_bound(s: Seq<u8>)
    ensures
        os2ip(s) < vstd::arithmetic::power::pow(256, s.len()),
    decreases s.len(),
{
    reveal(vstd::arithmetic::power::pow);
    if s.len() > 0 {
        lemma_os2ip_bound(s.drop_last());
    }
}

/// OS2IP inverts I2OSP for x < 256^len.
pub proof fn lemma_os2ip_i2osp(x: nat, len: nat)
    requires
        x < vstd::arithmetic::power::pow(256, len),
    ensures
        os2ip(i2osp(x, len)) == x,
    decreases len,
{
    reveal(vstd::arithmetic::power::pow);
    if len > 0 {
        let s = i2osp(x, len);
        assert(s.drop_last() =~= i2osp(x / 256, (len - 1) as nat));
        lemma_os2ip_i2osp(x / 256, (len - 1) as nat);
    }
}

/// I2OSP inverts OS2IP at the string's own length.
pub(crate) proof fn lemma_i2osp_os2ip(s: Seq<u8>)
    ensures
        i2osp(os2ip(s), s.len()) == s,
    decreases s.len(),
{
    if s.len() == 0 {
        assert(i2osp(0, 0) =~= s);
    } else {
        let d = s.drop_last();
        lemma_i2osp_os2ip(d);
        let x = os2ip(s);
        assert(x == os2ip(d) * 256 + s.last() as nat);
        assert(x / 256 == os2ip(d) && x % 256 == s.last() as nat) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                x as int,
                256,
                os2ip(d) as int,
                s.last() as int,
            );
        }
        assert(i2osp(x, s.len()) =~= s);
    }
}

/// A value below 256^k is held entirely in the string's low k octets.
pub(crate) proof fn lemma_os2ip_tail(s: Seq<u8>, k: nat)
    requires
        k <= s.len(),
        os2ip(s) < vstd::arithmetic::power::pow(256, k),
    ensures
        os2ip(s.subrange(s.len() - k, s.len() as int)) == os2ip(s),
{
    let a = s.subrange(0, s.len() - k);
    let b = s.subrange(s.len() - k, s.len() as int);
    let p = vstd::arithmetic::power::pow(256, k);
    assert(s =~= a + b);
    lemma_os2ip_append(a, b);
    vstd::arithmetic::mul::lemma_mul_basics(p);
    if os2ip(a) > 0 {
        vstd::arithmetic::power::lemma_pow_positive(256, k);
        vstd::arithmetic::mul::lemma_mul_inequality(1, os2ip(a) as int, p);
    }
}

} // verus!
