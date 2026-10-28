//! QUIC variable-length integers (RFC 9000 §16): an RFC-transcribed spec, a Vest format, and
//! proofs that the two agree.
use vest_lib::combinators::mapped::spec::FnSpecMapper;
use vest_lib::combinators::{Bind, Empty, Fixed, Mapped, Refined, Sum, U8};
use vest_lib::core::{exec::*, proof::*, spec::*};
use vstd::prelude::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use Sum::{Inl as L, Inr as R};

verus! {

// =============================================================================
// RFC 9000 transcription
// =============================================================================

//= https://www.rfc-editor.org/rfc/rfc9000#section-16
//# This means that integers are encoded on 1, 2, 4, or 8 bytes and can
//# encode 6-, 14-, 30-, or 62-bit values, respectively.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-16
//# | 11   | 8      | 62          | 0-4611686018427387903 |
/// Largest value a QUIC varint can carry (2^62 - 1).
pub const VARINT_MAX: u64 = 0x3FFF_FFFF_FFFF_FFFF;

//= https://www.rfc-editor.org/rfc/rfc9000#section-16
//# The QUIC variable-length integer encoding reserves the two most
//# significant bits of the first byte to encode the base-2 logarithm of
//# the integer encoding length in bytes.  The integer value is encoded
//# on the remaining bits, in network byte order.
//
//= https://www.rfc-editor.org/rfc/rfc9000#appendix-A.1
//# ReadVarint(data):
//#   // The length of variable-length integers is encoded in the
//#   // first two bits of the first byte.
//#   v = data.next_byte()
//#   prefix = v >> 6
//#   length = 1 << prefix
//#
//#   // Once the length is known, remove these bits and read any
//#   // remaining bytes.
//#   v = v & 0x3f
//#   repeat length-1 times:
//#     v = (v << 8) + data.next_byte()
//#   return v
/// Decodes a varint from the front of `b`, returning `(bytes consumed, value)`.
/// `None` when `b` is empty or shorter than the length its first byte announces.
pub open spec fn rfc_varint_decode(b: Seq<u8>) -> Option<(nat, u64)> {
    if b.len() == 0 {
        None
    } else {
        let v = b[0];
        let prefix = v >> 6;
        let length = (1u8 << prefix) as nat;
        if b.len() < length {
            None
        } else {
            Some((length, rfc_varint_read_remaining((v & 0x3f) as u64, b.subrange(1, length as int))))
        }
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#appendix-A.1
//#   repeat length-1 times:
//#     v = (v << 8) + data.next_byte()
/// The `repeat` loop of `ReadVarint`, over the `length - 1` bytes after the first.
pub open spec fn rfc_varint_read_remaining(v: u64, data: Seq<u8>) -> u64
    decreases data.len(),
{
    if data.len() == 0 {
        v
    } else {
        rfc_varint_read_remaining(((v << 8) + data[0] as u64) as u64, data.drop_first())
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-16
//# | 00   | 1      | 6           | 0-63                  |
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-16
//# | 01   | 2      | 14          | 0-16383               |
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-16
//# | 10   | 4      | 30          | 0-1073741823          |
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-16
//# | 11   | 8      | 62          | 0-4611686018427387903 |
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-16
//# Values do not need to be encoded on the minimum number of bytes
//# necessary, with the sole exception of the Frame Type field; see
//# Section 12.4.
/// The shortest encoding length (Table 4) for `v`.
pub open spec fn rfc_varint_min_len(v: u64) -> nat {
    if v <= 63 {
        1
    } else if v <= 16383 {
        2
    } else if v <= 0x3FFF_FFFF {
        4
    } else {
        8
    }
}

// =============================================================================
// Vest format
// =============================================================================

/// The bytes after the first, refined by the minimal-encoding check.
pub type QuicVarIntTrailing<const N: usize> = Refined<Fixed<N>, PredFnSpec<Seq<u8>>>;

/// Selected by the first byte's 2-bit prefix: 0, 1, 3 or 7 trailing bytes.
pub type QuicVarIntBody = Sum<
    Empty,
    Sum<QuicVarIntTrailing<1>, Sum<QuicVarIntTrailing<3>, QuicVarIntTrailing<7>>>,
>;

pub type QuicVarIntBodyVal = Sum<(), Sum<Seq<u8>, Sum<Seq<u8>, Seq<u8>>>>;

pub type QuicVarIntFmt = Mapped<
    Bind<U8, spec_fn(u8) -> QuicVarIntBody>,
    FnSpecMapper<(u8, QuicVarIntBodyVal), u64>,
>;

/// The `N` bytes after first byte `b1`; when `MINIMAL`, the decoded value must be at least
/// `min` (else a shorter encoding exists).
pub open spec fn quic_varint_trailing<const N: usize, const MINIMAL: bool>(
    b1: u8,
    min: u64,
) -> QuicVarIntTrailing<N> {
    Refined(
        Fixed::<N>,
        |r: Seq<u8>| MINIMAL ==> rfc_varint_read_remaining((b1 & 0x3f) as u64, r) >= min,
    )
}

/// `MINIMAL` rejects encodings longer than `rfc_varint_min_len` (needed for frame types,
/// RFC 9000 §12.4). The serializer always emits the minimal encoding.
pub open spec fn quic_varint_fmt<const MINIMAL: bool>() -> QuicVarIntFmt {
    Mapped {
        inner: Bind(
            U8,
            |b1: u8|
                match b1 >> 6 {
                    0 => L(Empty),
                    1 => R(L(quic_varint_trailing::<1, MINIMAL>(b1, 64))),
                    2 => R(R(L(quic_varint_trailing::<3, MINIMAL>(b1, 16384)))),
                    _ => R(R(R(quic_varint_trailing::<7, MINIMAL>(b1, 0x4000_0000)))),
                },
        ),
        mapper: (
            |p: (u8, QuicVarIntBodyVal)|
                match p {
                    (b1, L(_)) => rfc_varint_read_remaining((b1 & 0x3f) as u64, seq![]),
                    (b1, R(L(r))) => rfc_varint_read_remaining((b1 & 0x3f) as u64, r),
                    (b1, R(R(L(r)))) => rfc_varint_read_remaining((b1 & 0x3f) as u64, r),
                    (b1, R(R(R(r)))) => rfc_varint_read_remaining((b1 & 0x3f) as u64, r),
                },
            |v: u64|
                if v <= 63 {
                    (v as u8, L(()))
                } else if v <= 16383 {
                    ((0x40 | (v >> 8)) as u8, R(L(seq![v as u8])))
                } else if v <= 0x3FFF_FFFF {
                    (
                        (0x80 | (v >> 24)) as u8,
                        R(R(L(seq![(v >> 16) as u8, (v >> 8) as u8, v as u8]))),
                    )
                } else if v <= VARINT_MAX {
                    (
                        (0xC0 | (v >> 56)) as u8,
                        R(
                            R(
                                R(
                                    seq![
                                        (v >> 48) as u8,
                                        (v >> 40) as u8,
                                        (v >> 32) as u8,
                                        (v >> 24) as u8,
                                        (v >> 16) as u8,
                                        (v >> 8) as u8,
                                        v as u8,
                                    ],
                                ),
                            ),
                        ),
                    )
                } else {
                    // No encoding exists; prefix 00 with a trailing-bytes payload is inconsistent,
                    // so `consistent(v) <==> v <= VARINT_MAX`.
                    (0u8, R(R(R(seq![]))))
                },
        ),
    }
}

/// A QUIC variable-length integer. `QuicVarInt<false>` accepts any encoding length
/// (RFC 9000 §16); `QuicVarInt<true>` accepts only the minimal one (frame types, §12.4).
pub struct QuicVarInt<const MINIMAL: bool>;

mod derived_specs {
    use super::*;

    impl<const MINIMAL: bool> SpecParser for QuicVarInt<MINIMAL> {
        type PVal = u64;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            quic_varint_fmt::<MINIMAL>().spec_parse(ibuf)
        }
    }

    impl<const MINIMAL: bool> Consistency for QuicVarInt<MINIMAL> {
        type Val = u64;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            v <= VARINT_MAX
        }
    }

    impl<const MINIMAL: bool> SpecSerializerDps for QuicVarInt<MINIMAL> {
        type SValue = u64;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            quic_varint_fmt::<MINIMAL>().spec_serialize_dps(v, obuf)
        }
    }

    impl<const MINIMAL: bool> SpecSerializer for QuicVarInt<MINIMAL> {
        type SVal = u64;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            quic_varint_fmt::<MINIMAL>().spec_serialize(v)
        }
    }

    impl<const MINIMAL: bool> SpecByteLen for QuicVarInt<MINIMAL> {
        type T = u64;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            quic_varint_fmt::<MINIMAL>().byte_len(v)
        }
    }

}

mod derived_proofs {
    use super::*;

    impl<const MINIMAL: bool> SafeParser for QuicVarInt<MINIMAL> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            quic_varint_fmt::<MINIMAL>().lemma_parse_safe(ibuf);
        }
    }

    impl<const MINIMAL: bool> Productive for QuicVarInt<MINIMAL> {
        proof fn lemma_productive(&self, s: Seq<u8>) {
            quic_varint_fmt::<MINIMAL>().lemma_productive(s);
        }
    }

    impl SoundParser for QuicVarInt<true> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            lemma_fmt_sound_inv();
            quic_varint_fmt::<true>().lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            lemma_fmt_sound_inv();
            quic_varint_fmt::<true>().lemma_parse_sound_value(ibuf);
            if let Some((_, v)) = self.spec_parse(ibuf) {
                lemma_consistent_iff::<true>(v);
            }
        }
    }

    impl<const MINIMAL: bool> NonTailFmt for QuicVarInt<MINIMAL> {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            quic_varint_fmt::<MINIMAL>().lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            quic_varint_fmt::<MINIMAL>().lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<const MINIMAL: bool> GoodSerializer for QuicVarInt<MINIMAL> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            quic_varint_fmt::<MINIMAL>().lemma_serialize_len(v);
        }
    }

    impl<const MINIMAL: bool> SPRoundTripDps for QuicVarInt<MINIMAL> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            lemma_fmt_unambiguous::<MINIMAL>();
            lemma_consistent_iff::<MINIMAL>(v);
            quic_varint_fmt::<MINIMAL>().theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const MINIMAL: bool> NoLookAhead for QuicVarInt<MINIMAL> {
        proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
            quic_varint_fmt::<MINIMAL>().lemma_no_lookahead(i1, i2);
        }
    }

    impl NonMalleable for QuicVarInt<true> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            lemma_fmt_sound_inv();
            quic_varint_fmt::<true>().lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const MINIMAL: bool> EquivSerializersGeneral for QuicVarInt<MINIMAL> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            quic_varint_fmt::<MINIMAL>().lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const MINIMAL: bool> EquivSerializers for QuicVarInt<MINIMAL> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            quic_varint_fmt::<MINIMAL>().lemma_serialize_equiv_on_empty(v);
        }
    }

}

// =============================================================================
// Bit-packing lemmas, one pair per encoding length
// =============================================================================

proof fn lemma_len1(b0: u8)
    requires
        b0 >> 6 == 0,
    ensures
        ({
            let v = rfc_varint_read_remaining((b0 & 0x3f) as u64, seq![]);
            v <= 63 && v as u8 == b0
        }),
{
    reveal_with_fuel(rfc_varint_read_remaining, 1);
    assert(((b0 & 0x3f) as u64) <= 63 && ((b0 & 0x3f) as u64) as u8 == b0) by (bit_vector)
        requires
            b0 >> 6 == 0,
    ;
}

proof fn lemma_rev1(v: u64)
    requires
        v <= 63,
    ensures
        (v as u8) >> 6 == 0,
        rfc_varint_read_remaining(((v as u8) & 0x3f) as u64, seq![]) == v,
{
    reveal_with_fuel(rfc_varint_read_remaining, 1);
    assert((v as u8) >> 6 == 0 && (((v as u8) & 0x3f) as u64) == v) by (bit_vector)
        requires
            v <= 63,
    ;
}

proof fn bv_len2(b0: u8, r0: u8, a1: u64) by (bit_vector)
    requires
        b0 >> 6 == 1,
        a1 == ((((b0 & 0x3f) as u64) << 8) + r0 as u64) as u64,
    ensures
        a1 <= 16383,
        (0x40 | (a1 >> 8)) as u8 == b0,
        a1 as u8 == r0,
{
}

proof fn lemma_len2(b0: u8, r: Seq<u8>)
    requires
        b0 >> 6 == 1,
        r.len() == 1,
    ensures
        ({
            let v = rfc_varint_read_remaining((b0 & 0x3f) as u64, r);
            v <= 16383 && (0x40 | (v >> 8)) as u8 == b0 && seq![v as u8] == r
        }),
{
    reveal_with_fuel(rfc_varint_read_remaining, 2);
    let a1 = ((((b0 & 0x3f) as u64) << 8) + r[0] as u64) as u64;
    assert(r.drop_first().len() == 0);
    bv_len2(b0, r[0], a1);
    assert(seq![a1 as u8] =~= r);
}

proof fn bv_rev2(v: u64) by (bit_vector)
    requires
        63 < v <= 16383,
    ensures
        ((0x40 | (v >> 8)) as u8) >> 6 == 1,
        (((((0x40 | (v >> 8)) as u8) & 0x3f) as u64) << 8) + ((v as u8) as u64) == v,
{
}

proof fn lemma_rev2(v: u64)
    requires
        63 < v <= 16383,
    ensures
        ((0x40 | (v >> 8)) as u8) >> 6 == 1,
        rfc_varint_read_remaining((((0x40 | (v >> 8)) as u8) & 0x3f) as u64, seq![v as u8]) == v,
{
    reveal_with_fuel(rfc_varint_read_remaining, 2);
    bv_rev2(v);
    assert(seq![v as u8].drop_first() =~= seq![]);
}

proof fn bv_len4(b0: u8, r0: u8, r1: u8, r2: u8, a1: u64, a2: u64, a3: u64) by (bit_vector)
    requires
        b0 >> 6 == 2,
        a1 == ((((b0 & 0x3f) as u64) << 8) + r0 as u64) as u64,
        a2 == ((a1 << 8) + r1 as u64) as u64,
        a3 == ((a2 << 8) + r2 as u64) as u64,
    ensures
        a3 <= 0x3FFF_FFFF,
        (0x80 | (a3 >> 24)) as u8 == b0,
        (a3 >> 16) as u8 == r0,
        (a3 >> 8) as u8 == r1,
        a3 as u8 == r2,
{
}

proof fn lemma_len4(b0: u8, r: Seq<u8>)
    requires
        b0 >> 6 == 2,
        r.len() == 3,
    ensures
        ({
            let v = rfc_varint_read_remaining((b0 & 0x3f) as u64, r);
            v <= 0x3FFF_FFFF && (0x80 | (v >> 24)) as u8 == b0 && seq![
                (v >> 16) as u8,
                (v >> 8) as u8,
                v as u8,
            ] == r
        }),
{
    reveal_with_fuel(rfc_varint_read_remaining, 4);
    let a1 = ((((b0 & 0x3f) as u64) << 8) + r[0] as u64) as u64;
    let a2 = ((a1 << 8) + r[1] as u64) as u64;
    let a3 = ((a2 << 8) + r[2] as u64) as u64;
    let t1 = r.drop_first();
    let t2 = t1.drop_first();
    assert(t1[0] == r[1] && t2[0] == r[2] && t2.drop_first().len() == 0);
    bv_len4(b0, r[0], r[1], r[2], a1, a2, a3);
    assert(seq![(a3 >> 16) as u8, (a3 >> 8) as u8, a3 as u8] =~= r);
}

proof fn lemma_rev4(v: u64)
    requires
        16383 < v <= 0x3FFF_FFFF,
    ensures
        ((0x80 | (v >> 24)) as u8) >> 6 == 2,
        rfc_varint_read_remaining(
            (((0x80 | (v >> 24)) as u8) & 0x3f) as u64,
            seq![(v >> 16) as u8, (v >> 8) as u8, v as u8],
        ) == v,
{
    reveal_with_fuel(rfc_varint_read_remaining, 4);
    let b0 = (0x80 | (v >> 24)) as u8;
    let r = seq![(v >> 16) as u8, (v >> 8) as u8, v as u8];
    let a1 = ((((b0 & 0x3f) as u64) << 8) + r[0] as u64) as u64;
    let a2 = ((a1 << 8) + r[1] as u64) as u64;
    let a3 = ((a2 << 8) + r[2] as u64) as u64;
    let t1 = r.drop_first();
    let t2 = t1.drop_first();
    assert(t1[0] == r[1] && t2[0] == r[2] && t2.drop_first().len() == 0);
    bv_rev4(v, b0, a1, a2, a3);
}

proof fn bv_rev4(v: u64, b0: u8, a1: u64, a2: u64, a3: u64) by (bit_vector)
    requires
        16383 < v <= 0x3FFF_FFFF,
        b0 == (0x80 | (v >> 24)) as u8,
        a1 == ((((b0 & 0x3f) as u64) << 8) + ((v >> 16) as u8) as u64) as u64,
        a2 == ((a1 << 8) + ((v >> 8) as u8) as u64) as u64,
        a3 == ((a2 << 8) + (v as u8) as u64) as u64,
    ensures
        b0 >> 6 == 2,
        a3 == v,
{
}

/// Unrolls the `repeat` loop over 7 bytes, starting after the first step.
proof fn lemma_unroll7(a1: u64, r: Seq<u8>)
    requires
        r.len() == 7,
    ensures
        ({
            let a2 = ((a1 << 8) + r[1] as u64) as u64;
            let a3 = ((a2 << 8) + r[2] as u64) as u64;
            let a4 = ((a3 << 8) + r[3] as u64) as u64;
            let a5 = ((a4 << 8) + r[4] as u64) as u64;
            let a6 = ((a5 << 8) + r[5] as u64) as u64;
            let a7 = ((a6 << 8) + r[6] as u64) as u64;
            rfc_varint_read_remaining(a1, r.drop_first()) == a7
        }),
{
    reveal_with_fuel(rfc_varint_read_remaining, 7);
    let t1 = r.drop_first();
    let t2 = t1.drop_first();
    let t3 = t2.drop_first();
    let t4 = t3.drop_first();
    let t5 = t4.drop_first();
    let t6 = t5.drop_first();
    assert(t1[0] == r[1] && t2[0] == r[2] && t3[0] == r[3] && t4[0] == r[4] && t5[0] == r[5]
        && t6[0] == r[6] && t6.drop_first().len() == 0);
}

proof fn bv_len8(
    b0: u8,
    r0: u8,
    r1: u8,
    r2: u8,
    r3: u8,
    r4: u8,
    r5: u8,
    r6: u8,
    a1: u64,
    a2: u64,
    a3: u64,
    a4: u64,
    a5: u64,
    a6: u64,
    a7: u64,
) by (bit_vector)
    requires
        b0 >> 6 == 3,
        a1 == ((((b0 & 0x3f) as u64) << 8) + r0 as u64) as u64,
        a2 == ((a1 << 8) + r1 as u64) as u64,
        a3 == ((a2 << 8) + r2 as u64) as u64,
        a4 == ((a3 << 8) + r3 as u64) as u64,
        a5 == ((a4 << 8) + r4 as u64) as u64,
        a6 == ((a5 << 8) + r5 as u64) as u64,
        a7 == ((a6 << 8) + r6 as u64) as u64,
    ensures
        a7 <= 0x3FFF_FFFF_FFFF_FFFF,
        (0xC0 | (a7 >> 56)) as u8 == b0,
        (a7 >> 48) as u8 == r0,
        (a7 >> 40) as u8 == r1,
        (a7 >> 32) as u8 == r2,
        (a7 >> 24) as u8 == r3,
        (a7 >> 16) as u8 == r4,
        (a7 >> 8) as u8 == r5,
        a7 as u8 == r6,
{
}

proof fn bv_rev8(
    v: u64,
    b0: u8,
    a1: u64,
    a2: u64,
    a3: u64,
    a4: u64,
    a5: u64,
    a6: u64,
    a7: u64,
) by (bit_vector)
    requires
        0x3FFF_FFFF < v <= 0x3FFF_FFFF_FFFF_FFFF,
        b0 == (0xC0 | (v >> 56)) as u8,
        a1 == ((((b0 & 0x3f) as u64) << 8) + ((v >> 48) as u8) as u64) as u64,
        a2 == ((a1 << 8) + ((v >> 40) as u8) as u64) as u64,
        a3 == ((a2 << 8) + ((v >> 32) as u8) as u64) as u64,
        a4 == ((a3 << 8) + ((v >> 24) as u8) as u64) as u64,
        a5 == ((a4 << 8) + ((v >> 16) as u8) as u64) as u64,
        a6 == ((a5 << 8) + ((v >> 8) as u8) as u64) as u64,
        a7 == ((a6 << 8) + (v as u8) as u64) as u64,
    ensures
        b0 >> 6 == 3,
        a7 == v,
{
}

proof fn lemma_len8(b0: u8, r: Seq<u8>)
    requires
        b0 >> 6 == 3,
        r.len() == 7,
    ensures
        ({
            let v = rfc_varint_read_remaining((b0 & 0x3f) as u64, r);
            v <= VARINT_MAX && (0xC0 | (v >> 56)) as u8 == b0 && seq![
                (v >> 48) as u8,
                (v >> 40) as u8,
                (v >> 32) as u8,
                (v >> 24) as u8,
                (v >> 16) as u8,
                (v >> 8) as u8,
                v as u8,
            ] == r
        }),
{
    reveal_with_fuel(rfc_varint_read_remaining, 8);
    let a1 = ((((b0 & 0x3f) as u64) << 8) + r[0] as u64) as u64;
    let a2 = ((a1 << 8) + r[1] as u64) as u64;
    let a3 = ((a2 << 8) + r[2] as u64) as u64;
    let a4 = ((a3 << 8) + r[3] as u64) as u64;
    let a5 = ((a4 << 8) + r[4] as u64) as u64;
    let a6 = ((a5 << 8) + r[5] as u64) as u64;
    let a7 = ((a6 << 8) + r[6] as u64) as u64;
    lemma_unroll7(a1, r);
    bv_len8(b0, r[0], r[1], r[2], r[3], r[4], r[5], r[6], a1, a2, a3, a4, a5, a6, a7);
    assert(seq![
        (a7 >> 48) as u8,
        (a7 >> 40) as u8,
        (a7 >> 32) as u8,
        (a7 >> 24) as u8,
        (a7 >> 16) as u8,
        (a7 >> 8) as u8,
        a7 as u8,
    ] =~= r);
}

proof fn lemma_rev8(v: u64)
    requires
        0x3FFF_FFFF < v <= VARINT_MAX,
    ensures
        ((0xC0 | (v >> 56)) as u8) >> 6 == 3,
        rfc_varint_read_remaining(
            (((0xC0 | (v >> 56)) as u8) & 0x3f) as u64,
            seq![
                (v >> 48) as u8,
                (v >> 40) as u8,
                (v >> 32) as u8,
                (v >> 24) as u8,
                (v >> 16) as u8,
                (v >> 8) as u8,
                v as u8,
            ],
        ) == v,
{
    reveal_with_fuel(rfc_varint_read_remaining, 8);
    let b0 = (0xC0 | (v >> 56)) as u8;
    let r = seq![
        (v >> 48) as u8,
        (v >> 40) as u8,
        (v >> 32) as u8,
        (v >> 24) as u8,
        (v >> 16) as u8,
        (v >> 8) as u8,
        v as u8,
    ];
    let a1 = ((((b0 & 0x3f) as u64) << 8) + r[0] as u64) as u64;
    let a2 = ((a1 << 8) + r[1] as u64) as u64;
    let a3 = ((a2 << 8) + r[2] as u64) as u64;
    let a4 = ((a3 << 8) + r[3] as u64) as u64;
    let a5 = ((a4 << 8) + r[4] as u64) as u64;
    let a6 = ((a5 << 8) + r[5] as u64) as u64;
    let a7 = ((a6 << 8) + r[6] as u64) as u64;
    lemma_unroll7(a1, r);
    bv_rev8(v, b0, a1, a2, a3, a4, a5, a6, a7);
}

// =============================================================================
// Format invariants
// =============================================================================

proof fn lemma_consistent_iff<const MINIMAL: bool>(v: u64)
    ensures
        quic_varint_fmt::<MINIMAL>().consistent(v) <==> v <= VARINT_MAX,
{
    if v <= 63 {
        lemma_rev1(v);
    } else if v <= 16383 {
        lemma_rev2(v);
    } else if v <= 0x3FFF_FFFF {
        lemma_rev4(v);
    } else if v <= VARINT_MAX {
        lemma_rev8(v);
    }
}

proof fn lemma_fmt_unambiguous<const MINIMAL: bool>()
    ensures
        quic_varint_fmt::<MINIMAL>().unambiguous(),
{
    let fmt = quic_varint_fmt::<MINIMAL>();
    assert forall|v: u64| #[trigger] fmt.consistent(v) implies (fmt.mapper.0)((fmt.mapper.1)(v)) == v by {
        lemma_consistent_iff::<MINIMAL>(v);
        lemma_map_sound(v);
    }
}

/// `map(map_rev(v)) == v` for every encodable `v`.
proof fn lemma_map_sound(v: u64)
    requires
        v <= VARINT_MAX,
    ensures
        ({
            let m = quic_varint_fmt::<true>().mapper;
            (m.0)((m.1)(v)) == v
        }),
{
    if v <= 63 {
        lemma_rev1(v);
    } else if v <= 16383 {
        lemma_rev2(v);
    } else if v <= 0x3FFF_FFFF {
        lemma_rev4(v);
    } else {
        lemma_rev8(v);
    }
}

proof fn lemma_fmt_sound_inv()
    ensures
        quic_varint_fmt::<true>().sound_inv(),
        quic_varint_fmt::<true>().nonmal_inv(),
{
    let fmt = quic_varint_fmt::<true>();
    assert forall|x: (u8, QuicVarIntBodyVal)| #[trigger]
        fmt.inner.consistent(x) implies (fmt.mapper.1)((fmt.mapper.0)(x)) == x by {
        let (b0, body) = x;
        match body {
            L(_) => lemma_len1(b0),
            R(L(r)) => lemma_len2(b0, r),
            R(R(L(r))) => lemma_len4(b0, r),
            R(R(R(r))) => {
                assert(b0 >> 6 <= 3) by (bit_vector);
                lemma_len8(b0, r);
            },
        }
    }
}

// =============================================================================
// Equivalence with the RFC
// =============================================================================

/// Generic over `MINIMAL`: the format parses exactly the RFC decodings, restricted to the
/// shortest length when `MINIMAL`.
proof fn lemma_parse_matches_rfc<const MINIMAL: bool>(b: Seq<u8>)
    ensures
        QuicVarInt::<MINIMAL>.spec_parse(b) == (match rfc_varint_decode(b) {
            Some((n, v)) => if !MINIMAL || n == rfc_varint_min_len(v) {
                Some((n as int, v))
            } else {
                None
            },
            None => None,
        }),
{
    if b.len() > 0 {
        let b0 = b[0];
        let tail = b.subrange(1, b.len() as int);
        assert(b0 >> 6 <= 3) by (bit_vector);
        if b0 >> 6 == 0 {
            assert(1u8 << (b0 >> 6) == 1) by (bit_vector)
                requires
                    b0 >> 6 == 0,
            ;
            assert(b.subrange(1, 1) =~= seq![]);
            lemma_len1(b0);
        } else if b0 >> 6 == 1 {
            assert(1u8 << (b0 >> 6) == 2) by (bit_vector)
                requires
                    b0 >> 6 == 1,
            ;
            if b.len() >= 2 {
                assert(tail.subrange(0, 1) =~= b.subrange(1, 2));
                lemma_len2(b0, b.subrange(1, 2));
            }
        } else if b0 >> 6 == 2 {
            assert(1u8 << (b0 >> 6) == 4) by (bit_vector)
                requires
                    b0 >> 6 == 2,
            ;
            if b.len() >= 4 {
                assert(tail.subrange(0, 3) =~= b.subrange(1, 4));
                lemma_len4(b0, b.subrange(1, 4));
            }
        } else {
            assert(1u8 << (b0 >> 6) == 8) by (bit_vector)
                requires
                    b0 >> 6 == 3,
            ;
            if b.len() >= 8 {
                assert(tail.subrange(0, 7) =~= b.subrange(1, 8));
                lemma_len8(b0, b.subrange(1, 8));
            }
        }
    }
}

/// Vest's lenient parser is exactly RFC 9000 `ReadVarint`; the minimal parser accepts exactly
/// the RFC decodings that use the shortest length.
pub proof fn theorem_matches_rfc(b: Seq<u8>)
    ensures
        QuicVarInt::<false>.spec_parse(b) == (match rfc_varint_decode(b) {
            Some((n, v)) => Some((n as int, v)),
            None => None,
        }),
        QuicVarInt::<true>.spec_parse(b) is Some <==> (rfc_varint_decode(b) matches Some((n, v))
            && n == rfc_varint_min_len(v)),
        QuicVarInt::<true>.spec_parse(b) matches Some((n, v)) ==> rfc_varint_decode(b) == Some(
            (n as nat, v),
        ),
{
    lemma_parse_matches_rfc::<false>(b);
    lemma_parse_matches_rfc::<true>(b);
}

/// The serializer emits the minimal RFC encoding of `v`.
pub proof fn theorem_serialize_matches_rfc(v: u64)
    requires
        v <= VARINT_MAX,
    ensures
        rfc_varint_decode(QuicVarInt::<true>.spec_serialize(v)) == Some((rfc_varint_min_len(v), v)),
        QuicVarInt::<true>.spec_serialize(v).len() == rfc_varint_min_len(v),
{
    let s = QuicVarInt::<true>.spec_serialize(v);
    QuicVarInt::<true>.theorem_serialize_parse_roundtrip(v);
    theorem_matches_rfc(s);
}

/// The serializer emits the shift/OR encoding at the shortest length, so `byte_len` is the
/// RFC's `rfc_varint_min_len` for either `MINIMAL`.
proof fn lemma_serialize_bytes<const MINIMAL: bool>(v: u64)
    requires
        v <= VARINT_MAX,
    ensures
        QuicVarInt::<MINIMAL>.byte_len(v) == rfc_varint_min_len(v),
        QuicVarInt::<MINIMAL>.spec_serialize(v) == (if v <= 63 {
            seq![v as u8]
        } else if v <= 16383 {
            seq![(0x40 | (v >> 8)) as u8, v as u8]
        } else if v <= 0x3FFF_FFFF {
            seq![(0x80 | (v >> 24)) as u8, (v >> 16) as u8, (v >> 8) as u8, v as u8]
        } else {
            seq![
                (0xC0 | (v >> 56)) as u8,
                (v >> 48) as u8,
                (v >> 40) as u8,
                (v >> 32) as u8,
                (v >> 24) as u8,
                (v >> 16) as u8,
                (v >> 8) as u8,
                v as u8,
            ]
        }),
{
    let s = QuicVarInt::<MINIMAL>.spec_serialize(v);
    quic_varint_fmt::<MINIMAL>().lemma_serialize_len(v);
    assert(s.len() == QuicVarInt::<MINIMAL>.byte_len(v));
    if v <= 63 {
        assert(s =~= seq![v as u8]);
    } else if v <= 16383 {
        assert(s =~= seq![(0x40 | (v >> 8)) as u8, v as u8]);
    } else if v <= 0x3FFF_FFFF {
        assert(s =~= seq![(0x80 | (v >> 24)) as u8, (v >> 16) as u8, (v >> 8) as u8, v as u8]);
    } else {
        assert(s =~= seq![
            (0xC0 | (v >> 56)) as u8,
            (v >> 48) as u8,
            (v >> 40) as u8,
            (v >> 32) as u8,
            (v >> 24) as u8,
            (v >> 16) as u8,
            (v >> 8) as u8,
            v as u8,
        ]);
    }
}

/// One more `repeat` step: folding `s.push(x)` is folding `s`, then one step with `x`.
proof fn lemma_read_push(a: u64, s: Seq<u8>, x: u8)
    ensures
        rfc_varint_read_remaining(a, s.push(x)) == ((rfc_varint_read_remaining(a, s) << 8)
            + x as u64) as u64,
    decreases s.len(),
{
    reveal_with_fuel(rfc_varint_read_remaining, 2);
    if s.len() == 0 {
        assert(s.push(x).drop_first() =~= s);
        assert(s.push(x)[0] == x);
    } else {
        assert(s.push(x).drop_first() =~= s.drop_first().push(x));
        assert(s.push(x)[0] == s[0]);
        lemma_read_push(((a << 8) + s[0] as u64) as u64, s.drop_first(), x);
    }
}

proof fn bv_shl_or(a: u64, x: u8) by (bit_vector)
    ensures
        ((a << 8) + x as u64) as u64 == (a << 8) | (x as u64),
{
}

// =============================================================================
// Executable parser, serializer, prepare
// =============================================================================

/// Encoded length announced by the first byte's 2-bit prefix.
fn exec_len(b0: u8) -> (n: usize)
    ensures
        n == (1u8 << (b0 >> 6)) as nat,
        n == 1 || n == 2 || n == 4 || n == 8,
{
    proof {
        assert(b0 >> 6 <= 3) by (bit_vector);
    }
    if b0 >> 6 == 0 {
        assert(1u8 << (b0 >> 6) == 1) by (bit_vector)
            requires
                b0 >> 6 == 0,
        ;
        1
    } else if b0 >> 6 == 1 {
        assert(1u8 << (b0 >> 6) == 2) by (bit_vector)
            requires
                b0 >> 6 == 1,
        ;
        2
    } else if b0 >> 6 == 2 {
        assert(1u8 << (b0 >> 6) == 4) by (bit_vector)
            requires
                b0 >> 6 == 2,
        ;
        4
    } else {
        assert(1u8 << (b0 >> 6) == 8) by (bit_vector)
            requires
                b0 >> 6 == 3,
        ;
        8
    }
}

fn exec_min_len(v: u64) -> (n: usize)
    ensures
        n == rfc_varint_min_len(v),
{
    if v <= 63 {
        1
    } else if v <= 16383 {
        2
    } else if v <= 0x3FFF_FFFF {
        4
    } else {
        8
    }
}

impl<'i, const MINIMAL: bool> Parser<&'i [u8]> for QuicVarInt<MINIMAL> {
    type PT = u64;

    fn min_byte_len(&self) -> usize {
        1
    }

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        let b = *ibuf;
        proof {
            lemma_parse_matches_rfc::<MINIMAL>(b@);
        }
        if b.len() == 0 {
            return Err(ParseError::unexpected_eof());
        }
        let b0 = b[0];
        let n = exec_len(b0);
        if b.len() < n {
            return Err(ParseError::unexpected_eof());
        }
        let mut v: u64 = (b0 & 0x3f) as u64;
        let mut i: usize = 1;
        while i < n
            invariant
                1 <= i <= n <= b@.len(),
                v == rfc_varint_read_remaining((b0 & 0x3f) as u64, b@.subrange(1, i as int)),
            decreases n - i,
        {
            proof {
                lemma_read_push((b0 & 0x3f) as u64, b@.subrange(1, i as int), b@[i as int]);
                bv_shl_or(v, b@[i as int]);
                assert(b@.subrange(1, i as int).push(b@[i as int]) =~= b@.subrange(
                    1,
                    i as int + 1,
                ));
            }
            v = (v << 8) | (b[i] as u64);
            i += 1;
        }
        assert(b@.subrange(1, n as int) == b@.subrange(1, i as int));
        if MINIMAL && n != exec_min_len(v) {
            Err(ParseError::non_canonical())
        } else {
            Ok((n, v))
        }
    }
}

impl<Output: OutputBuf, const MINIMAL: bool> Serializer<Output, u64> for QuicVarInt<MINIMAL> {
    fn serialize_into(&self, v: &u64, obuf: &mut Output) {
        broadcast use vest_lib::core::exec::output::outbuf_lemmas;

        let v = *v;
        let ghost old_obuf = obuf@;
        proof {
            lemma_serialize_bytes::<MINIMAL>(v);
        }
        if v <= 63 {
            obuf.write_byte(v as u8);
        } else if v <= 16383 {
            obuf.write_byte((0x40 | (v >> 8)) as u8);
            obuf.write_byte(v as u8);
        } else if v <= 0x3FFF_FFFF {
            obuf.write_byte((0x80 | (v >> 24)) as u8);
            obuf.write_byte((v >> 16) as u8);
            obuf.write_byte((v >> 8) as u8);
            obuf.write_byte(v as u8);
        } else {
            obuf.write_byte((0xC0 | (v >> 56)) as u8);
            obuf.write_byte((v >> 48) as u8);
            obuf.write_byte((v >> 40) as u8);
            obuf.write_byte((v >> 32) as u8);
            obuf.write_byte((v >> 24) as u8);
            obuf.write_byte((v >> 16) as u8);
            obuf.write_byte((v >> 8) as u8);
            obuf.write_byte(v as u8);
        }
        assert(obuf@ =~= old_obuf + self.spec_serialize(v));
    }
}

impl<const MINIMAL: bool> Prepare<u64> for QuicVarInt<MINIMAL> {
    fn prepare(&self, v: &u64) -> (checked: Result<usize, PreSerializeError>) {
        if *v > VARINT_MAX {
            return Err(PreSerializeError::custom("QUIC varint exceeds 2^62 - 1"));
        }
        proof {
            lemma_serialize_bytes::<MINIMAL>(*v);
        }
        Ok(exec_min_len(*v))
    }
}

} // verus!
