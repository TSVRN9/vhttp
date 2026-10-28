//! HPACK/QPACK Huffman string decoding (RFC 7541 §5.2, used by RFC 9204 §4.1.2), proved sound
//! and complete against `rfc_huffman_decodes`. No encoder: responses use H=0 literals.
use super::huffman_table::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// =============================================================================
// Spec
// =============================================================================

/// MSB-first `len`-bit representation of `x`.
pub open spec fn bits_of(x: nat, len: nat) -> Seq<bool>
    decreases len,
{
    if len == 0 {
        Seq::empty()
    } else {
        bits_of(x / 2, (len - 1) as nat).push(x % 2 == 1)
    }
}

/// MSB-first bits of `spec_huff_code(sym)`.
pub open spec fn code_bits(sym: nat) -> Seq<bool> {
    bits_of(spec_huff_code(sym).0 as nat, spec_huff_code(sym).1)
}

/// Concatenation of `code_bits(s[i])`.
pub open spec fn encode_bits(s: Seq<u8>) -> Seq<bool>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        code_bits(s[0] as nat) + encode_bits(s.drop_first())
    }
}

/// Bit `t` is bit `7 - t % 8` of byte `t / 8` (MSB-first).
pub open spec fn bytes_to_bits(b: Seq<u8>) -> Seq<bool> {
    Seq::new(8 * b.len(), |t: int| (b[t / 8] >> ((7 - t % 8) as u8)) & 1u8 == 1u8)
}

// RFC 7541 §5.2 (not in the Duvet config): "The encoded data is the bitwise concatenation of the
// codes corresponding to each octet of the string literal." Padding: "A padding strictly longer
// than 7 bits MUST be treated as a decoding error. A padding not corresponding to the most
// significant bits of the code for the EOS symbol MUST be treated as a decoding error. A
// Huffman-encoded string literal containing the EOS symbol MUST be treated as a decoding error."
// EOS is 30 one-bits, so its prefixes up to 7 bits are `Seq::new(k, |_| true)`, and `s` (bytes
// only) cannot contain EOS: an embedded EOS leaves more than 7 bits for the padding.
//= https://www.rfc-editor.org/rfc/rfc9204#section-4.1.2
//# When Huffman encoding is enabled,
//# the Huffman table from Appendix B of [RFC7541] is used without
//# modification and the indicated length is the size of the string after
//# encoding.
pub open spec fn rfc_huffman_decodes(input: Seq<u8>, s: Seq<u8>) -> bool {
    exists|k: nat| k <= 7 && bytes_to_bits(input) == encode_bits(s) + #[trigger] ones(k)
}

/// `k` one-bits: the first `k` bits of EOS for `k <= 30`. Named only so the quantifier above has a
/// trigger (Verus rejects a lambda inside one).
pub open spec fn ones(k: nat) -> Seq<bool> {
    Seq::new(k, |_i: int| true)
}

// =============================================================================
// Bit-string lemmas
// =============================================================================

spec fn shr(x: nat, d: nat) -> nat
    decreases d,
{
    if d == 0 {
        x
    } else {
        shr(x / 2, (d - 1) as nat)
    }
}

proof fn lemma_bits_of_len(x: nat, l: nat)
    ensures
        bits_of(x, l).len() == l,
    decreases l,
{
    if l > 0 {
        lemma_bits_of_len(x / 2, (l - 1) as nat);
    }
}

proof fn lemma_bits_of_inj(x: nat, y: nat, l: nat)
    requires
        x < pow2(l),
        y < pow2(l),
        bits_of(x, l) == bits_of(y, l),
    ensures
        x == y,
    decreases l,
{
    if l == 0 {
        lemma2_to64();
    } else {
        let l1 = (l - 1) as nat;
        lemma_pow2_unfold(l);
        lemma_bits_of_len(x / 2, l1);
        lemma_bits_of_len(y / 2, l1);
        assert(bits_of(x, l).drop_last() == bits_of(x / 2, l1));
        assert(bits_of(y, l).drop_last() == bits_of(y / 2, l1));
        assert(bits_of(x, l).last() == (x % 2 == 1));
        assert(bits_of(y, l).last() == (y % 2 == 1));
        lemma_bits_of_inj(x / 2, y / 2, l1);
    }
}

/// The first `l` bits of a `(l + d)`-bit string are the string of `x >> d`.
proof fn lemma_shr_prefix(y: nat, l: nat, d: nat)
    ensures
        bits_of(y, l + d).subrange(0, l as int) == bits_of(shr(y, d), l),
    decreases d,
{
    lemma_bits_of_len(y, l + d);
    if d == 0 {
        assert(bits_of(y, l).subrange(0, l as int) =~= bits_of(y, l));
    } else {
        let d1 = (d - 1) as nat;
        assert((l + d - 1) as nat == l + d1);
        lemma_bits_of_len(y / 2, l + d1);
        lemma_shr_prefix(y / 2, l, d1);
        assert(bits_of(y, l + d).subrange(0, l as int) =~= bits_of(y / 2, l + d1).subrange(
            0,
            l as int,
        ));
    }
}

proof fn lemma_shr_bound(y: nat, l: nat, d: nat)
    requires
        y < pow2(l + d),
    ensures
        shr(y, d) < pow2(l),
    decreases d,
{
    if d > 0 {
        let d1 = (d - 1) as nat;
        lemma_pow2_unfold(l + d);
        assert((l + d - 1) as nat == l + d1);
        lemma_shr_bound(y / 2, l, d1);
    }
}

proof fn lemma_shr_mono(x: nat, y: nat, d: nat)
    requires
        x <= y,
    ensures
        shr(x, d) <= shr(y, d),
    decreases d,
{
    if d > 0 {
        lemma_shr_mono(x / 2, y / 2, (d - 1) as nat);
    }
}

// =============================================================================
// Table facts, checked against spec_huff_code (the generated canonical layout is not trusted)
// =============================================================================

spec fn sym_ok(a: nat) -> bool {
    let (c, l) = spec_huff_code(a);
    let (f, n, _o) = spec_huff_len_info(l);
    &&& 1 <= l <= 30
    &&& (c as nat) < pow2(l)
    &&& f <= c < f + n
}

/// Every byte's code lies in its length's window `[first, first + count)`.
proof fn lemma_sym_ok(a: nat)
    requires
        a < 256,
    ensures
        sym_ok(a),
{
    lemma2_to64();
}

/// `sorted[offset + j]` is the byte whose code is `first + j` at length `l`.
proof fn lemma_sorted(l: nat, j: nat)
    requires
        1 <= l <= 30,
        j < spec_huff_len_info(l).1,
    ensures
        ({
            let (f, _n, o) = spec_huff_len_info(l);
            let a = spec_huff_sorted(o + j);
            &&& o + j < 256
            &&& a < 256
            &&& spec_huff_code(a).0 as nat == f + j
            &&& spec_huff_code(a).1 == l
        }),
{
}

proof fn lemma_len_info(l: nat)
    requires
        1 <= l <= 30,
    ensures
        ({
            let (f, n, o) = spec_huff_len_info(l);
            &&& o + n <= 256
            &&& f + n <= 0x4000_0000
            &&& l < 30 ==> spec_huff_len_info(l + 1).0 == (f + n) * 2
        }),
{
}

/// Every code longer than `la` starts, in its first `la` bits, past the length-`la` window.
proof fn lemma_first_shr(la: nat, lb: nat)
    requires
        1 <= la < lb <= 30,
    ensures
        shr(spec_huff_len_info(lb).0, (lb - la) as nat) >= spec_huff_len_info(la).0
            + spec_huff_len_info(la).1,
    decreases lb,
{
    let l1 = (lb - 1) as nat;
    lemma_len_info(l1);
    let (f1, n1, _o) = spec_huff_len_info(l1);
    let fb = spec_huff_len_info(lb).0;
    assert(fb / 2 == f1 + n1);
    if lb > la + 1 {
        lemma_first_shr(la, l1);
        lemma_shr_mono(f1, f1 + n1, (l1 - la) as nat);
    }
    assert(shr(fb, (lb - la) as nat) == shr(fb / 2, (l1 - la) as nat));
}

/// No byte's code is a proper prefix of another's.
proof fn lemma_prefix_free(a: nat, b: nat)
    requires
        a < 256,
        b < 256,
        spec_huff_code(a).1 < spec_huff_code(b).1,
    ensures
        code_bits(b).subrange(0, spec_huff_code(a).1 as int) != code_bits(a),
{
    let (ca, la) = spec_huff_code(a);
    let (cb, lb) = spec_huff_code(b);
    let d = (lb - la) as nat;
    lemma_sym_ok(a);
    lemma_sym_ok(b);
    assert(lb == la + d);
    lemma_shr_prefix(cb as nat, la, d);
    lemma_shr_bound(cb as nat, la, d);
    lemma_first_shr(la, lb);
    lemma_shr_mono(spec_huff_len_info(lb).0, cb as nat, d);
    if code_bits(b).subrange(0, la as int) == code_bits(a) {
        lemma_bits_of_inj(ca as nat, shr(cb as nat, d), la);
    }
}

// =============================================================================
// Decoder state: pending bits `p` follow the decoded output
// =============================================================================

spec fn is_prefix(x: Seq<bool>, y: Seq<bool>) -> bool {
    x.len() <= y.len() && y.subrange(0, x.len() as int) == x
}

spec fn no_code_prefix(p: Seq<bool>) -> bool {
    forall|a: nat| a < 256 ==> !is_prefix(#[trigger] code_bits(a), p)
}

/// `p ++ rem` is some byte string's code followed by a valid padding.
spec fn decodable(p: Seq<bool>, rem: Seq<bool>) -> bool {
    exists|s: Seq<u8>, k: nat|
        #![trigger encode_bits(s), ones(k)]
        k <= 7 && p + rem == encode_bits(s) + ones(k)
}

proof fn lemma_code_len(a: nat)
    requires
        a < 256,
    ensures
        1 <= code_bits(a).len() == spec_huff_code(a).1 <= 30,
{
    lemma_sym_ok(a);
    lemma_bits_of_len(spec_huff_code(a).0 as nat, spec_huff_code(a).1);
}

proof fn lemma_encode_push(s: Seq<u8>, c: u8)
    ensures
        encode_bits(s.push(c)) == encode_bits(s) + code_bits(c as nat),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.push(c).drop_first() =~= Seq::<u8>::empty());
        assert(encode_bits(s.push(c).drop_first()) == Seq::<bool>::empty());
        assert(encode_bits(s.push(c)) =~= code_bits(c as nat));
    } else {
        assert(s.push(c).drop_first() =~= s.drop_first().push(c));
        lemma_encode_push(s.drop_first(), c);
        assert(encode_bits(s.push(c)) =~= encode_bits(s) + code_bits(c as nat));
    }
}

/// A valid decomposition of `p ++ rem` starts with a code longer than `p` (or has no code at all).
proof fn lemma_split(p: Seq<bool>, rem: Seq<bool>, s: Seq<u8>, k: nat)
    requires
        no_code_prefix(p),
        p + rem == encode_bits(s) + ones(k),
        s.len() > 0,
    ensures
        p.len() < code_bits(s[0] as nat).len(),
        encode_bits(s) + ones(k) == code_bits(s[0] as nat) + (encode_bits(s.drop_first()) + ones(
            k,
        )),
{
    let c = code_bits(s[0] as nat);
    let e = encode_bits(s.drop_first());
    assert(encode_bits(s) + ones(k) =~= c + (e + ones(k)));
    if c.len() <= p.len() {
        assert(p.subrange(0, c.len() as int) =~= (p + rem).subrange(0, c.len() as int));
        assert((c + (e + ones(k))).subrange(0, c.len() as int) =~= c);
        assert(is_prefix(code_bits(s[0] as nat), p));
    }
}

proof fn lemma_step_hit(p: Seq<bool>, b: bool, rem: Seq<bool>, c: nat)
    requires
        no_code_prefix(p),
        decodable(p, seq![b] + rem),
        c < 256,
        code_bits(c) == p.push(b),
    ensures
        decodable(Seq::empty(), rem),
{
    let (s, k) = choose|s: Seq<u8>, k: nat|
        #![trigger encode_bits(s), ones(k)]
        k <= 7 && p + (seq![b] + rem) == encode_bits(s) + ones(k);
    let q = p.push(b);
    let w = q + rem;
    assert(p + (seq![b] + rem) =~= w);
    if s.len() == 0 {
        assert(encode_bits(s) + ones(k) =~= ones(k));
        let k2 = (k - q.len()) as nat;
        assert(rem =~= encode_bits(Seq::<u8>::empty()) + ones(k2)) by {
            assert(forall|i: int| 0 <= i < rem.len() ==> rem[i] == w[q.len() + i]);
        }
        assert(Seq::<bool>::empty() + rem =~= rem);
    } else {
        lemma_split(p, seq![b] + rem, s, k);
        let cc = code_bits(s[0] as nat);
        let tail = encode_bits(s.drop_first()) + ones(k);
        lemma_code_len(c);
        lemma_code_len(s[0] as nat);
        if q.len() < cc.len() {
            assert(cc.subrange(0, q.len() as int) =~= w.subrange(0, q.len() as int));
            assert(w.subrange(0, q.len() as int) =~= q);
            lemma_prefix_free(c, s[0] as nat);
        }
        assert(q.len() == cc.len());
        assert(rem =~= w.subrange(q.len() as int, w.len() as int));
        assert(rem =~= tail);
        assert(Seq::<bool>::empty() + rem =~= rem);
    }
}

proof fn lemma_step_miss(p: Seq<bool>, b: bool, rem: Seq<bool>)
    requires
        no_code_prefix(p),
        decodable(p, seq![b] + rem),
        forall|a: nat| a < 256 ==> code_bits(a) != p.push(b),
    ensures
        p.len() + 1 < 30,
        decodable(p.push(b), rem),
{
    let (s, k) = choose|s: Seq<u8>, k: nat|
        #![trigger encode_bits(s), ones(k)]
        k <= 7 && p + (seq![b] + rem) == encode_bits(s) + ones(k);
    let q = p.push(b);
    let w = q + rem;
    assert(p + (seq![b] + rem) =~= w);
    if s.len() == 0 {
        assert(encode_bits(s) + ones(k) =~= ones(k));
    } else {
        lemma_split(p, seq![b] + rem, s, k);
        let cc = code_bits(s[0] as nat);
        lemma_code_len(s[0] as nat);
        if q.len() == cc.len() {
            assert(w.subrange(0, q.len() as int) =~= q);
            assert(cc =~= w.subrange(0, q.len() as int));
        }
    }
}

proof fn lemma_no_code_prefix_push(p: Seq<bool>, b: bool)
    requires
        no_code_prefix(p),
        forall|a: nat| a < 256 ==> code_bits(a) != p.push(b),
    ensures
        no_code_prefix(p.push(b)),
{
    let q = p.push(b);
    assert forall|a: nat| a < 256 implies !is_prefix(#[trigger] code_bits(a), q) by {
        let ca = code_bits(a);
        if is_prefix(ca, q) {
            if ca.len() <= p.len() {
                assert(p.subrange(0, ca.len() as int) =~= q.subrange(0, ca.len() as int));
                assert(is_prefix(code_bits(a), p));
            } else {
                assert(q.subrange(0, q.len() as int) =~= q);
            }
        }
    }
}

proof fn lemma_no_code_prefix_empty()
    ensures
        no_code_prefix(Seq::empty()),
{
    assert forall|a: nat| a < 256 implies !is_prefix(#[trigger] code_bits(a), Seq::empty()) by {
        lemma_code_len(a);
    }
}

proof fn lemma_final(p: Seq<bool>)
    requires
        no_code_prefix(p),
        decodable(p, Seq::empty()),
    ensures
        p.len() <= 7,
        p == ones(p.len()),
{
    let (s, k) = choose|s: Seq<u8>, k: nat|
        #![trigger encode_bits(s), ones(k)]
        k <= 7 && p + Seq::empty() == encode_bits(s) + ones(k);
    assert(p + Seq::empty() =~= p);
    if s.len() > 0 {
        lemma_split(p, Seq::empty(), s, k);
        lemma_code_len(s[0] as nat);
        assert(false);
    }
    assert(encode_bits(s) + ones(k) =~= ones(k));
}

proof fn lemma_decodes_imp(input: Seq<u8>, s: Seq<u8>)
    requires
        rfc_huffman_decodes(input, s),
    ensures
        decodable(Seq::empty(), bytes_to_bits(input)),
{
    let k = choose|k: nat| k <= 7 && bytes_to_bits(input) == encode_bits(s) + #[trigger] ones(k);
    assert(Seq::<bool>::empty() + bytes_to_bits(input) =~= bytes_to_bits(input));
}

spec fn state_ok(
    bits: Seq<bool>,
    t: int,
    out: Seq<u8>,
    acc: u32,
    len: u32,
    all_ones: bool,
) -> bool {
    let p = bits_of(acc as nat, len as nat);
    &&& 0 <= t <= bits.len()
    &&& len < 30
    &&& (acc as nat) < pow2(len as nat)
    &&& bits.subrange(0, t) == encode_bits(out) + p
    &&& all_ones == (p == ones(len as nat))
    &&& no_code_prefix(p)
    &&& decodable(Seq::empty(), bits) ==> decodable(p, bits.subrange(t, bits.len() as int))
}

// =============================================================================
// Exec
// =============================================================================

/// The byte whose code is `(acc, len)`.
fn lookup(acc: u32, len: u32) -> (r: Option<u8>)
    requires
        1 <= len <= 30,
    ensures
        match r {
            Some(c) => spec_huff_code(c as nat) == (acc, len as nat),
            None => forall|a: nat| a < 256 ==> #[trigger] spec_huff_code(a) != (acc, len as nat),
        },
{
    let (first, count, off) = huff_len_info(len);
    proof {
        lemma_len_info(len as nat);
    }
    if acc >= first && acc - first < count {
        proof {
            lemma_sorted(len as nat, (acc - first) as nat);
        }
        Some(huff_sorted(off + (acc - first)))
    } else {
        proof {
            assert forall|a: nat| a < 256 implies #[trigger] spec_huff_code(a) != (
                acc,
                len as nat,
            ) by {
                lemma_sym_ok(a);
            }
        }
        None
    }
}

/// Consumes bit `bits[t]`. `false` means no byte string decodes from `bits`.
fn feed_bit(
    out: &mut Vec<u8>,
    acc: &mut u32,
    len: &mut u32,
    all_ones: &mut bool,
    bit: bool,
    Ghost(bits): Ghost<Seq<bool>>,
    Ghost(t): Ghost<int>,
) -> (ok: bool)
    requires
        0 <= t < bits.len(),
        bits[t] == bit,
        state_ok(bits, t, old(out)@, *old(acc), *old(len), *old(all_ones)),
    ensures
        ok ==> state_ok(bits, t + 1, final(out)@, *final(acc), *final(len), *final(all_ones)),
        !ok ==> !decodable(Seq::empty(), bits),
{
    let ghost p = bits_of(*acc as nat, *len as nat);
    let ghost q = p.push(bit);
    let ghost rem = bits.subrange(t + 1, bits.len() as int);
    proof {
        assert(bits.subrange(t, bits.len() as int) =~= seq![bit] + rem);
        assert(bits.subrange(0, t + 1) =~= bits.subrange(0, t).push(bit));
        assert(encode_bits(old(out)@) + q =~= (encode_bits(old(out)@) + p).push(bit));
        lemma_pow2_unfold(*len as nat + 1);
        if *len < 29 {
            lemma_pow2_strictly_increases(*len as nat, 29);
        }
        lemma2_to64();
        lemma_bits_of_len(*acc as nat, *len as nat);
        if p == ones(*len as nat) && bit {
            assert(q =~= ones(*len as nat + 1));
        }
        if q == ones(*len as nat + 1) {
            assert(p =~= ones(*len as nat)) by {
                assert(forall|i: int| 0 <= i < p.len() ==> p[i] == q[i]);
            }
            assert(q[p.len() as int] == bit);
        }
    }
    *acc = *acc * 2 + if bit { 1 } else { 0 };
    *len = *len + 1;
    *all_ones = *all_ones && bit;
    proof {
        let x = *acc as nat;
        assert(x / 2 == *old(acc) as nat && (x % 2 == 1) == bit);
        assert(bits_of(x, *len as nat) == q);
    }
    match lookup(*acc, *len) {
        Some(c) => {
            proof {
                lemma_encode_push(old(out)@, c);
                lemma_no_code_prefix_empty();
                if decodable(Seq::empty(), bits) {
                    lemma_step_hit(p, bit, rem, c as nat);
                }
            }
            out.push(c);
            *acc = 0;
            *len = 0;
            *all_ones = true;
            proof {
                lemma2_to64();
                assert(bits_of(0, 0) =~= ones(0));
                assert(bits.subrange(0, t + 1) =~= encode_bits(out@) + bits_of(0, 0));
            }
            true
        },
        None => {
            proof {
                assert forall|a: nat| a < 256 implies code_bits(a) != q by {
                    lemma_sym_ok(a);
                    lemma_bits_of_len(spec_huff_code(a).0 as nat, spec_huff_code(a).1);
                    lemma_bits_of_len(*acc as nat, *len as nat);
                    if code_bits(a) == q {
                        lemma_bits_of_inj(spec_huff_code(a).0 as nat, *acc as nat, *len as nat);
                    }
                }
                lemma_no_code_prefix_push(p, bit);
                if decodable(Seq::empty(), bits) {
                    lemma_step_miss(p, bit, rem);
                }
            }
            *len < 30
        },
    }
}

/// Decodes a Huffman-coded string literal (RFC 7541 §5.2); `None` on any decoding error.
// ponytail: one bit per step with a per-length window lookup; a nibble/byte state table is the
// upgrade if header decoding shows up in profiles.
pub fn huffman_decode(input: &[u8]) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(s) ==> rfc_huffman_decodes(input@, s@),
        r is None ==> forall|s: Seq<u8>| !rfc_huffman_decodes(input@, s),
{
    let ghost bits = bytes_to_bits(input@);
    let mut out: Vec<u8> = Vec::new();
    let mut acc: u32 = 0;
    let mut len: u32 = 0;
    let mut all_ones = true;
    proof {
        lemma2_to64();
        lemma_no_code_prefix_empty();
        assert(bits.subrange(0, 0) =~= encode_bits(out@) + bits_of(0, 0));
        assert(bits_of(0, 0) =~= ones(0));
        assert(bits.subrange(0, bits.len() as int) =~= bits);
        assert(bits_of(0, 0) + bits =~= bits);
    }
    let mut i: usize = 0;
    while i < input.len()
        invariant
            i <= input.len(),
            bits == bytes_to_bits(input@),
            state_ok(bits, 8 * i, out@, acc, len, all_ones),
        decreases input.len() - i,
    {
        let byte = input[i];
        let mut j: u8 = 0;
        while j < 8
            invariant
                i < input.len(),
                j <= 8,
                byte == input@[i as int],
                bits == bytes_to_bits(input@),
                state_ok(bits, 8 * i + j, out@, acc, len, all_ones),
            decreases 8 - j,
        {
            let bit = (byte >> (7 - j)) & 1 == 1;
            proof {
                let t = 8 * i + j;
                assert(t / 8 == i && t % 8 == j as int);
                assert(bits[t] == bit);
            }
            let ok = feed_bit(
                &mut out,
                &mut acc,
                &mut len,
                &mut all_ones,
                bit,
                Ghost(bits),
                Ghost(8 * i + j),
            );
            if !ok {
                proof {
                    assert forall|s: Seq<u8>| !rfc_huffman_decodes(input@, s) by {
                        if rfc_huffman_decodes(input@, s) {
                            lemma_decodes_imp(input@, s);
                        }
                    }
                }
                return None;
            }
            j += 1;
        }
        i += 1;
    }
    proof {
        assert(bits.subrange(0, bits.len() as int) =~= bits);
        assert(bits.subrange(bits.len() as int, bits.len() as int) =~= Seq::<bool>::empty());
        assert(bits_of(acc as nat, len as nat) + Seq::empty() =~= bits_of(acc as nat, len as nat));
    }
    if len <= 7 && all_ones {
        proof {
            assert(bits == encode_bits(out@) + ones(len as nat));
        }
        Some(out)
    } else {
        proof {
            assert forall|s: Seq<u8>| !rfc_huffman_decodes(input@, s) by {
                if rfc_huffman_decodes(input@, s) {
                    lemma_decodes_imp(input@, s);
                    lemma_final(bits_of(acc as nat, len as nat));
                    lemma_bits_of_len(acc as nat, len as nat);
                }
            }
        }
        None
    }
}

} // verus!
