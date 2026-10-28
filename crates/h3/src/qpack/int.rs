//! QPACK prefixed integers (RFC 9204 §4.1.1 / RFC 7541 §5.1): an RFC-transcribed spec, an
//! executable codec, and proofs that the two agree. Hand-written rather than Vest because the
//! prefix shares its first byte with caller-owned flag bits.
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

//= https://www.rfc-editor.org/rfc/rfc9204#section-4.1.1
//# QPACK implementations MUST be able to decode integers up to and
//# including 62 bits long.
pub const PREFIX_INT_MAX: u64 = 0x3FFF_FFFF_FFFF_FFFF;

/// Cap on continuation bytes (RFC 9204 §7.4 implementation limit). Nine bytes already carry
/// 63 bits even at N=1; the tenth is spare for zero padding.
pub const PREFIX_INT_MAX_CONT: usize = 10;

#[derive(Debug, PartialEq, Eq)]
pub enum PrefixInt {
    Incomplete,
    Value { value: u64, consumed: usize },
    TooLarge,
}

pub enum PrefixIntSpec {
    Incomplete,
    Value { value: nat, consumed: nat },
    TooLarge,
}

impl View for PrefixInt {
    type V = PrefixIntSpec;

    open spec fn view(&self) -> PrefixIntSpec {
        match self {
            PrefixInt::Incomplete => PrefixIntSpec::Incomplete,
            PrefixInt::Value { value, consumed } => PrefixIntSpec::Value {
                value: *value as nat,
                consumed: *consumed as nat,
            },
            PrefixInt::TooLarge => PrefixIntSpec::TooLarge,
        }
    }
}

// =============================================================================
// RFC 7541 §5.1 transcription
// =============================================================================

// RFC 7541 §5.1 (not in the Duvet config):
//   decode I from the next N bits
//   if I < 2^N - 1, return I
//   else
//       M = 0
//       repeat
//           B = next octet
//           I = I + (B & 127) * 2^M
//           M = M + 7
//       while B & 128 == 128
//       return I
// The limits (value <= 2^62 - 1, at most PREFIX_INT_MAX_CONT continuation bytes) are the
// RFC 9204 §7.4 implementation limits.
/// Continuation bytes: `b` is what remains, `k` continuation bytes are consumed, `acc` is `I`.
pub open spec fn rfc_prefix_cont(b: Seq<u8>, k: nat, acc: nat) -> PrefixIntSpec
    decreases b.len(),
{
    if b.len() == 0 {
        PrefixIntSpec::Incomplete
    } else if k >= PREFIX_INT_MAX_CONT {
        PrefixIntSpec::TooLarge
    } else {
        let nv = acc + (b[0] & 127u8) as nat * pow2(7 * k);
        if nv > PREFIX_INT_MAX {
            PrefixIntSpec::TooLarge
        } else if b[0] & 128u8 == 0 {
            PrefixIntSpec::Value { value: nv, consumed: k + 2 }
        } else {
            rfc_prefix_cont(b.skip(1), k + 1, nv)
        }
    }
}

//= https://www.rfc-editor.org/rfc/rfc9204#section-4.1.1
//# The format from [RFC7541] is used
//# unmodified.
/// `(value, bytes consumed)` of an N-bit prefix integer; the high bits of `b[0]` are flags.
pub open spec fn rfc_prefix_int(n: u8, b: Seq<u8>) -> PrefixIntSpec {
    if b.len() == 0 {
        PrefixIntSpec::Incomplete
    } else {
        let p = pow2(n as nat);
        let i = b[0] as nat % p;
        if i < p - 1 {
            PrefixIntSpec::Value { value: i, consumed: 1 }
        } else {
            rfc_prefix_cont(b.skip(1), 0, i)
        }
    }
}

// =============================================================================
// Serialization spec
// =============================================================================

pub open spec fn spec_prefix_cont_bytes(r: u64) -> Seq<u8>
    decreases r,
    via spec_cont_decreases
{
    if r < 128 {
        seq![r as u8]
    } else {
        seq![((r & 127) | 128) as u8].add(spec_prefix_cont_bytes(r >> 7))
    }
}

#[verifier::decreases_by]
proof fn spec_cont_decreases(r: u64) {
    if r >= 128 {
        assert((r >> 7) < r) by (bit_vector)
            requires
                r >= 128,
        ;
    }
}

/// Minimal encoding of `v` in an N-bit prefix under `flags`.
pub open spec fn spec_prefix_int_bytes(n: u8, flags: u8, v: u64) -> Seq<u8> {
    let m = (0xffu8 >> (8 - n) as u8);
    if v < m {
        seq![flags | v as u8]
    } else {
        seq![flags | m].add(spec_prefix_cont_bytes((v - m) as u64))
    }
}

// =============================================================================
// Lemmas
// =============================================================================

proof fn lemma_low_bits(n: u8, x: u8)
    requires
        1 <= n <= 8,
    ensures
        (0xffu8 >> (8 - n) as u8) as nat == pow2(n as nat) - 1,
        (x & (0xffu8 >> (8 - n) as u8)) as nat == x as nat % pow2(n as nat),
{
    lemma2_to64();
    if n == 1 {
        assert((0xffu8 >> 7u8) == 1u8) by (bit_vector);
        assert((x & (0xffu8 >> 7u8)) == x % 2u8) by (bit_vector);
        assert((x % 2u8) as nat == x as nat % 2nat);
    } else if n == 2 {
        assert((0xffu8 >> 6u8) == 3u8) by (bit_vector);
        assert((x & (0xffu8 >> 6u8)) == x % 4u8) by (bit_vector);
        assert((x % 4u8) as nat == x as nat % 4nat);
    } else if n == 3 {
        assert((0xffu8 >> 5u8) == 7u8) by (bit_vector);
        assert((x & (0xffu8 >> 5u8)) == x % 8u8) by (bit_vector);
        assert((x % 8u8) as nat == x as nat % 8nat);
    } else if n == 4 {
        assert((0xffu8 >> 4u8) == 15u8) by (bit_vector);
        assert((x & (0xffu8 >> 4u8)) == x % 16u8) by (bit_vector);
        assert((x % 16u8) as nat == x as nat % 16nat);
    } else if n == 5 {
        assert((0xffu8 >> 3u8) == 31u8) by (bit_vector);
        assert((x & (0xffu8 >> 3u8)) == x % 32u8) by (bit_vector);
        assert((x % 32u8) as nat == x as nat % 32nat);
    } else if n == 6 {
        assert((0xffu8 >> 2u8) == 63u8) by (bit_vector);
        assert((x & (0xffu8 >> 2u8)) == x % 64u8) by (bit_vector);
        assert((x % 64u8) as nat == x as nat % 64nat);
    } else if n == 7 {
        assert((0xffu8 >> 1u8) == 127u8) by (bit_vector);
        assert((x & (0xffu8 >> 1u8)) == x % 128u8) by (bit_vector);
        assert((x % 128u8) as nat == x as nat % 128nat);
    } else {
        assert((0xffu8 >> 0u8) == 255u8) by (bit_vector);
        assert((x & (0xffu8 >> 0u8)) == x) by (bit_vector);
        assert(x as nat % 256nat == x as nat);
    }
}

proof fn lemma_max_plus_one()
    ensures
        PREFIX_INT_MAX as nat + 1 == pow2(62),
{
    lemma2_to64();
    lemma_pow2_adds(31, 31);
}

/// A continuation encoding of `r` read after `k` bytes decodes to `acc + r * 2^(7k)`.
proof fn lemma_cont_roundtrip(r: u64, k: nat, acc: nat)
    requires
        k < PREFIX_INT_MAX_CONT,
        acc + r as nat * pow2(7 * k) <= PREFIX_INT_MAX,
    ensures
        rfc_prefix_cont(spec_prefix_cont_bytes(r), k, acc) == (PrefixIntSpec::Value {
            value: (acc + r as nat * pow2(7 * k)) as nat,
            consumed: k + 1 + spec_prefix_cont_bytes(r).len(),
        }),
    decreases r,
{
    let bytes = spec_prefix_cont_bytes(r);
    lemma_pow2_pos(7 * k);
    let pk = pow2(7 * k);
    if r < 128 {
        assert(bytes[0] == r as u8);
        assert((r as u8) & 127u8 == r as u8) by (bit_vector)
            requires
                r < 128,
        ;
        assert((r as u8) & 128u8 == 0u8) by (bit_vector)
            requires
                r < 128,
        ;
        assert(bytes.skip(1) =~= Seq::<u8>::empty());
    } else {
        let hi = r >> 7;
        assert((r >> 7) < r && (r >> 7) == r / 128 && (r & 127) == r % 128) by (bit_vector)
            requires
                r >= 128,
        ;
        let low = (r & 127) as nat;
        assert(bytes[0] == (((r & 127) | 128) as u8));
        assert(((((r & 127) | 128) as u8) & 127u8) as u64 == (r & 127)) by (bit_vector);
        assert(((((r & 127) | 128) as u8) & 128u8) != 0u8) by (bit_vector);
        // r * pk >= 128 * pk = pow2(7k + 7) <= MAX < pow2(62), so k < 8.
        lemma_pow2_adds(7 * k, 7);
        lemma_max_plus_one();
        lemma2_to64();
        assert(pow2(7) == 128);
        assert(r as nat * pk >= 128 * pk) by (nonlinear_arith)
            requires
                r >= 128,
                pk > 0,
        ;
        if 7 * k + 7 >= 62 {
            if 7 * k + 7 > 62 {
                lemma_pow2_strictly_increases(62, 7 * k + 7);
            }
            assert(false);
        }
        let nv = acc + low * pk;
        assert(r as nat * pk == low * pk + 128 * hi as nat * pk) by (nonlinear_arith)
            requires
                r as nat == low + 128 * hi as nat,
        ;
        lemma_pow2_adds(7 * k, 7);
        assert(7 * (k + 1) == 7 * k + 7);
        assert(hi as nat * pow2(7 * (k + 1)) == hi as nat * pk * 128) by (nonlinear_arith)
            requires
                pow2(7 * (k + 1)) == pk * 128,
        ;
        assert(nv + hi as nat * pow2(7 * (k + 1)) == acc + r as nat * pk) by (nonlinear_arith)
            requires
                r as nat * pk == low * pk + 128 * hi as nat * pk,
                hi as nat * pow2(7 * (k + 1)) == hi as nat * pk * 128,
                nv == acc + low * pk,
        ;
        assert(bytes.skip(1) =~= spec_prefix_cont_bytes(hi));
        lemma_cont_roundtrip(hi, k + 1, nv);
        assert(bytes.len() == 1 + spec_prefix_cont_bytes(hi).len());
    }
}

/// A serialized integer parses back to exactly its value and length.
pub proof fn theorem_prefix_int_roundtrip(n: u8, flags: u8, v: u64)
    requires
        1 <= n <= 8,
        v <= PREFIX_INT_MAX,
        flags as nat % pow2(n as nat) == 0,
    ensures
        rfc_prefix_int(n, spec_prefix_int_bytes(n, flags, v)) == (PrefixIntSpec::Value {
            value: v as nat,
            consumed: spec_prefix_int_bytes(n, flags, v).len(),
        }),
{
    let m = (0xffu8 >> (8 - n) as u8);
    let bytes = spec_prefix_int_bytes(n, flags, v);
    lemma_low_bits(n, flags);
    lemma_low_bits(n, bytes[0]);
    let p = pow2(n as nat);
    assert(flags & m == 0u8);
    if v < m {
        let x = v as u8;
        assert(x & m == x) by (bit_vector)
            requires
                x < m,
                m == (0xffu8 >> (8 - n) as u8),
                1 <= n <= 8,
        ;
        assert((flags | x) & m == x) by (bit_vector)
            requires
                flags & m == 0u8,
                x & m == x,
        ;
    } else {
        assert((flags | m) & m == m) by (bit_vector)
            requires
                flags & m == 0u8,
        ;
        let r = (v - m) as u64;
        lemma_pow2_pos(0);
        lemma2_to64();
        assert(pow2(0) == 1);
        assert(7 * 0 == 0);
        assert(m as nat + r as nat * pow2(7 * 0) == v as nat);
        lemma_cont_roundtrip(r, 0, m as nat);
        assert(bytes.skip(1) =~= spec_prefix_cont_bytes(r));
    }
}

proof fn lemma_cont_facts(b: Seq<u8>, k: nat, acc: nat, t: Seq<u8>)
    ensures
        rfc_prefix_cont(b, k, acc) matches PrefixIntSpec::Value { consumed, .. } ==> k + 2
            <= consumed <= k + 1 + b.len(),
        rfc_prefix_cont(b, k, acc) is Value ==> rfc_prefix_cont(b + t, k, acc) == rfc_prefix_cont(
            b,
            k,
            acc,
        ),
    decreases b.len(),
{
    if b.len() > 0 {
        assert((b + t)[0] == b[0]);
        assert((b + t).skip(1) =~= b.skip(1) + t);
        lemma_cont_facts(b.skip(1), k + 1, acc + (b[0] & 127u8) as nat * pow2(7 * k), t);
    }
}

/// A decoded integer occupies between 1 and `b.len()` bytes.
pub proof fn lemma_prefix_int_consumed(n: u8, b: Seq<u8>)
    ensures
        rfc_prefix_int(n, b) matches PrefixIntSpec::Value { consumed, .. } ==> 1 <= consumed
            <= b.len(),
{
    if b.len() > 0 {
        lemma_cont_facts(b.skip(1), 0, b[0] as nat % pow2(n as nat), Seq::empty());
    }
}

proof fn lemma_cont_incomplete_len(b: Seq<u8>, k: nat, acc: nat)
    requires
        k <= PREFIX_INT_MAX_CONT,
        rfc_prefix_cont(b, k, acc) is Incomplete,
    ensures
        b.len() + k <= PREFIX_INT_MAX_CONT,
    decreases b.len(),
{
    if b.len() > 0 {
        lemma_cont_incomplete_len(b.skip(1), k + 1, acc + (b[0] & 127u8) as nat * pow2(7 * k));
    }
}

/// An incomplete integer is at most a prefix byte plus PREFIX_INT_MAX_CONT continuation bytes.
pub proof fn lemma_prefix_int_incomplete_len(n: u8, b: Seq<u8>)
    requires
        rfc_prefix_int(n, b) is Incomplete,
    ensures
        b.len() <= 1 + PREFIX_INT_MAX_CONT,
{
    if b.len() > 0 {
        lemma_cont_incomplete_len(b.skip(1), 0, b[0] as nat % pow2(n as nat));
    }
}

/// Prefix stability: bytes after a complete integer don't change how it decodes.
pub proof fn lemma_prefix_int_append(n: u8, b: Seq<u8>, t: Seq<u8>)
    requires
        rfc_prefix_int(n, b) is Value,
    ensures
        rfc_prefix_int(n, b + t) == rfc_prefix_int(n, b),
{
    assert((b + t)[0] == b[0]);
    assert((b + t).skip(1) =~= b.skip(1) + t);
    lemma_cont_facts(b.skip(1), 0, b[0] as nat % pow2(n as nat), t);
}

// =============================================================================
// Executable codec
// =============================================================================

/// Decodes an N-bit prefix integer from the front of `buf`; the high `8 - n` bits of
/// `buf[0]` belong to the caller.
pub fn parse_prefix_int(n: u8, buf: &[u8]) -> (r: PrefixInt)
    requires
        1 <= n <= 8,
    ensures
        r@ == rfc_prefix_int(n, buf@),
{
    if buf.len() == 0 {
        return PrefixInt::Incomplete;
    }
    let mask: u8 = 0xffu8 >> (8 - n);
    proof {
        lemma_low_bits(n, buf@[0]);
    }
    let pre: u8 = buf[0] & mask;
    if pre < mask {
        return PrefixInt::Value { value: pre as u64, consumed: 1 };
    }
    let mut acc: u64 = pre as u64;
    let mut p: u64 = 1;
    let mut i: usize = 1;
    proof {
        lemma2_to64();
        assert(buf@.skip(1) == buf@.skip(i as int));
    }
    loop
        invariant
            1 <= i <= buf@.len(),
            i <= 11,
            acc <= PREFIX_INT_MAX,
            i <= 10 ==> p as nat == pow2(7 * (i - 1) as nat),
            i <= 10 ==> p > 0,
            rfc_prefix_int(n, buf@) == rfc_prefix_cont(buf@.skip(i as int), (i - 1) as nat, acc as nat),
        decreases buf@.len() - i,
    {
        if i >= buf.len() {
            proof {
                assert(buf@.skip(i as int).len() == 0);
            }
            return PrefixInt::Incomplete;
        }
        if i > PREFIX_INT_MAX_CONT {
            return PrefixInt::TooLarge;
        }
        let byte = buf[i];
        let d: u64 = (byte & 127) as u64;
        assert(d < 128) by (bit_vector)
            requires
                d == (byte & 127) as u64,
        ;
        proof {
            lemma_pow2_pos((7 * (i - 1)) as nat);
            assert(buf@.skip(i as int)[0] == byte);
            assert(buf@.skip(i as int).skip(1) =~= buf@.skip(i as int + 1));
        }
        let bound: u64 = (PREFIX_INT_MAX - acc) / p;
        if d > bound {
            proof {
                // d > floor(x / p) implies d * p > x.
                let x = (PREFIX_INT_MAX - acc) as nat;
                assert(d as nat * p as nat > x) by (nonlinear_arith)
                    requires
                        d > bound,
                        bound as nat == x / p as nat,
                        p > 0,
                ;
            }
            return PrefixInt::TooLarge;
        }
        proof {
            let x = (PREFIX_INT_MAX - acc) as nat;
            assert(d as nat * p as nat <= x) by (nonlinear_arith)
                requires
                    d <= bound,
                    bound as nat == x / p as nat,
                    p > 0,
            ;
            assert(d as u64 * p as u64 <= PREFIX_INT_MAX - acc);
        }
        acc = acc + d * p;
        if byte & 128 == 0 {
            return PrefixInt::Value { value: acc, consumed: i + 1 };
        }
        if i < PREFIX_INT_MAX_CONT {
            proof {
                lemma_pow2_adds((7 * (i - 1)) as nat, 7);
                lemma2_to64();
                assert(pow2(7) == 128);
                assert(7 * i == 7 * (i - 1) + 7);
                assert(p as nat * 128 == pow2(7 * i as nat)) by (nonlinear_arith)
                    requires
                        pow2(7 * i as nat) == pow2(7 * (i - 1) as nat) * pow2(7),
                        p as nat == pow2(7 * (i - 1) as nat),
                        pow2(7) == 128,
                ;
                lemma_pow2_adds(63, 1);
                if 7 * i < 63 {
                    lemma_pow2_strictly_increases(7 * i as nat, 63);
                }
                assert(pow2(64) == 0x1_0000_0000_0000_0000nat);
                assert(p as nat * 128 < 0x1_0000_0000_0000_0000nat);
            }
            p = p * 128;
        }
        i += 1;
    }
}

/// Appends the minimal N-bit prefix encoding of `v` under `flags`.
pub fn serialize_prefix_int(n: u8, flags: u8, v: u64, out: &mut Vec<u8>)
    requires
        1 <= n <= 8,
        v <= PREFIX_INT_MAX,
        flags as nat % pow2(n as nat) == 0,
    ensures
        final(out)@ == old(out)@.add(spec_prefix_int_bytes(n, flags, v)),
{
    let mask: u8 = 0xffu8 >> (8 - n);
    if v < mask as u64 {
        out.push(flags | v as u8);
        proof {
            assert(old(out)@.push(flags | v as u8) =~= old(out)@.add(spec_prefix_int_bytes(n, flags, v)));
        }
        return;
    }
    out.push(flags | mask);
    let ghost base = out@;
    let ghost r0 = (v - mask as u64) as u64;
    let mut r: u64 = v - mask as u64;
    proof {
        assert(base.add(spec_prefix_cont_bytes(r0)) =~= old(out)@.add(spec_prefix_int_bytes(n, flags, v)));
    }
    while r >= 128
        invariant
            out@.add(spec_prefix_cont_bytes(r)) == old(out)@.add(spec_prefix_int_bytes(n, flags, v)),
        decreases r,
    {
        let b = ((r & 127) | 128) as u8;
        proof {
            assert((r >> 7) < r) by (bit_vector)
                requires
                    r >= 128,
            ;
            assert(out@.push(b).add(spec_prefix_cont_bytes(r >> 7)) =~= out@.add(spec_prefix_cont_bytes(r)));
        }
        out.push(b);
        r = r >> 7;
    }
    proof {
        assert(out@.push(r as u8) =~= out@.add(spec_prefix_cont_bytes(r)));
    }
    out.push(r as u8);
}

} // verus!
