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

} // verus!
