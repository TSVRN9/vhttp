//! RFC 8446 §4.2 extension blocks: a transcribed parse spec of an `Extension extensions<..>`
//! vector's content, a parser proven equal to it and canonical, and the ClientHello block
//! rules (no duplicate type of any value, pre_shared_key last, no CH-forbidden types).
use vstd::prelude::*;
use crate::codes::*;
use crate::pl::*;
use vstd::slice::{slice_subrange, slice_to_vec};

verus! {

// RFC 8446 §4.2: `struct { ExtensionType extension_type; opaque extension_data<0..2^16-1>; }`
#[derive(Debug, PartialEq, Eq)]
pub struct Ext {
    pub ty: u16,
    pub data: Vec<u8>,
}

pub struct SpecExt {
    pub ty: u16,
    pub data: Seq<u8>,
}

impl View for Ext {
    type V = SpecExt;

    open spec fn view(&self) -> SpecExt {
        SpecExt { ty: self.ty, data: self.data@ }
    }
}

impl DeepView for Ext {
    type V = SpecExt;

    open spec fn deep_view(&self) -> SpecExt {
        self@
    }
}

// =============================================================================
// RFC 8446 §4.2 transcription
// =============================================================================

/// The extensions in `b`, the content of an `Extension extensions<..>` vector.
pub open spec fn rfc_ext_list(b: Seq<u8>) -> Option<Seq<SpecExt>>
    decreases b.len(),
{
    if b.len() == 0 {
        Some(seq![])
    } else if b.len() < 2 {
        None
    } else {
        match rfc_vec(b.skip(2), 0, 0xffff) {
            None => None,
            Some((data, rest)) => match rfc_ext_list(rest) {
                None => None,
                Some(tail) => Some(seq![SpecExt { ty: be(b, 2) as u16, data }] + tail),
            },
        }
    }
}

pub open spec fn spec_ext_bytes(ty: u16, data: Seq<u8>) -> Seq<u8> {
    spec_be_bytes(ty as nat, 2) + spec_vec_bytes(0xffff, data)
}

pub open spec fn spec_ext_list_bytes(s: Seq<SpecExt>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![]
    } else {
        spec_ext_bytes(s[0].ty, s[0].data) + spec_ext_list_bytes(s.skip(1))
    }
}

//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2
//# There MUST NOT be more than one extension of the
//# same type in a given extension block.
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2
//# If an implementation receives an extension
//# which it recognizes and which is not specified for the message in
//# which it appears, it MUST abort the handshake with an
//# "illegal_parameter" alert.
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.11
//# The "pre_shared_key" extension MUST be the last extension in the
//# ClientHello (this facilitates implementation as described below).
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.11
//# Servers MUST check that it is the last extension and otherwise fail
//# the handshake with an "illegal_parameter" alert.
/// The ClientHello extension-block rules. Duplicates cover every type, unknown and GREASE
/// included; the RFC names no alert for them (Decision 7). oid_filters is recognized and
/// specified only for CertificateRequest (Decision 8).
pub open spec fn rfc_ch_ext_check(s: Seq<SpecExt>) -> Result<(), u64> {
    if exists|i: int, j: int| 0 <= i < j < s.len() && #[trigger] s[i].ty == #[trigger] s[j].ty {
        Err(ALERT_ILLEGAL_PARAMETER)
    } else if exists|i: int|
        0 <= i < s.len() && #[trigger] s[i].ty == EXT_PRE_SHARED_KEY && i != s.len() - 1
    {
        Err(ALERT_ILLEGAL_PARAMETER)
    } else if exists|i: int| 0 <= i < s.len() && #[trigger] s[i].ty == EXT_OID_FILTERS {
        Err(ALERT_ILLEGAL_PARAMETER)
    } else {
        Ok(())
    }
}

/// The data of the first extension of type `ty`.
pub open spec fn spec_find(s: Seq<SpecExt>, ty: u16) -> Option<Seq<u8>>
    decreases s.len(),
{
    if s.len() == 0 {
        None
    } else if s[0].ty == ty {
        Some(s[0].data)
    } else {
        spec_find(s.skip(1), ty)
    }
}

// =============================================================================
// Proofs
// =============================================================================

/// A parsed extension block is exactly the canonical encoding of its extensions.
pub proof fn theorem_ext_list_canonical(b: Seq<u8>)
    ensures
        rfc_ext_list(b) matches Some(s) ==> spec_ext_list_bytes(s) == b,
    decreases b.len(),
{
    if let Some(s) = rfc_ext_list(b) {
        if b.len() > 0 {
            let (data, rest) = rfc_vec(b.skip(2), 0, 0xffff).unwrap();
            theorem_ext_list_canonical(rest);
            lemma_be_canonical(b, 2);
            lemma_vec_canonical(b.skip(2), 0, 0xffff, data, rest);
            let tail = rfc_ext_list(rest).unwrap();
            assert(s.skip(1) =~= tail);
            assert(be(b, 2) as u16 as nat == be(b, 2));
            assert(b =~= b.take(2) + b.skip(2));
        }
    }
}

// =============================================================================
// Exec
// =============================================================================

pub fn parse_ext_list(b: &[u8]) -> (r: Option<Vec<Ext>>)
    ensures
        r.deep_view() == rfc_ext_list(b@),
{
    let mut v: Vec<Ext> = Vec::new();
    let mut pos: usize = 0;
    assert(b@.skip(0) =~= b@);
    assert(v.deep_view() + seq![] =~= seq![]);
    while pos < b.len()
        invariant
            pos <= b@.len(),
            rfc_ext_list(b@) == match rfc_ext_list(b@.skip(pos as int)) {
                Some(t) => Some(v.deep_view() + t),
                None => None,
            },
        decreases b@.len() - pos,
    {
        let ghost t = b@.skip(pos as int);
        let ty = match read_u16(b, pos) {
            Some(x) => x,
            None => return None,
        };
        let (s, e) = match read_vec(b, pos + 2, 0, 0xffff) {
            Some(se) => se,
            None => {
                assert(t.skip(2) =~= b@.skip(pos + 2));
                return None;
            },
        };
        assert(t.skip(2) =~= b@.skip(pos + 2));
        let data = slice_to_vec(slice_subrange(b, s, e));
        let ghost old_v = v.deep_view();
        v.push(Ext { ty, data });
        assert(v.deep_view() =~= old_v.push(SpecExt { ty: be(t, 2) as u16, data: data@ }));
        pos = e;
        proof {
            if let Some(tail) = rfc_ext_list(b@.skip(pos as int)) {
                assert(old_v + (seq![SpecExt { ty: be(t, 2) as u16, data: data@ }] + tail)
                    =~= v.deep_view() + tail);
            }
        }
    }
    assert(b@.skip(pos as int) =~= seq![]);
    assert(v.deep_view() + seq![] =~= v.deep_view());
    Some(v)
}

/// Bit `u % 64` of word `u / 64` of the seen table.
spec fn seen_bit(seen: Seq<u64>, u: int) -> bool {
    (seen[u / 64] >> ((u % 64) as u64)) & 1 == 1
}

proof fn lemma_bit_zero(c: u64)
    by (bit_vector)
    ensures
        (0u64 >> c) & 1 == 0,
{
}

proof fn lemma_bit_set_same(w: u64, b: u64)
    by (bit_vector)
    requires
        b < 64,
    ensures
        ((w | (1u64 << b)) >> b) & 1 == 1,
{
}

proof fn lemma_bit_set_other(w: u64, b: u64, c: u64)
    by (bit_vector)
    requires
        b < 64,
        c < 64,
        b != c,
    ensures
        ((w | (1u64 << b)) >> c) & 1 == (w >> c) & 1,
{
}

pub fn check_ch_exts(s: &Vec<Ext>) -> (r: Result<(), u64>)
    ensures
        r == rfc_ch_ext_check(s.deep_view()),
{
    let ghost d = s.deep_view();
    let n = s.len();
    // ponytail: an 8 KiB bitmap zeroed per ClientHello (twice with HRR) is the main CPU cost
    // of the unauthenticated HRR path, where no asymmetric crypto runs; sort the types and
    // scan for neighbours (O(n log n) in the extension count) if that fill shows in profiles.
    let mut seen: Vec<u64> = Vec::new();
    let mut w: usize = 0;
    while w < 1024
        invariant
            w <= 1024,
            seen@.len() == w,
            forall|k: int| 0 <= k < w ==> seen@[k] == 0,
        decreases 1024 - w,
    {
        seen.push(0);
        w += 1;
    }
    assert forall|u: int| 0 <= u < 0x1_0000 implies !#[trigger] seen_bit(seen@, u) by {
        lemma_bit_zero((u % 64) as u64);
    }
    let mut i: usize = 0;
    while i < n
        invariant
            n == s@.len(),
            d == s.deep_view(),
            d.len() == n,
            i <= n,
            seen@.len() == 1024,
            forall|u: int|
                0 <= u < 0x1_0000 ==> (#[trigger] seen_bit(seen@, u) <==> exists|k: int|
                    0 <= k < i && #[trigger] d[k].ty == u),
            forall|a: int, c: int| 0 <= a < c < i ==> #[trigger] d[a].ty != #[trigger] d[c].ty,
            forall|k: int| 0 <= k < i && #[trigger] d[k].ty == EXT_PRE_SHARED_KEY ==> k == n - 1,
            forall|k: int| 0 <= k < i ==> #[trigger] d[k].ty != EXT_OID_FILTERS,
        decreases n - i,
    {
        let ty = s[i].ty;
        assert(d[i as int].ty == ty);
        let wi = (ty / 64) as usize;
        let b = (ty % 64) as u64;
        let word = seen[wi];
        if (word >> b) & 1 == 1 {
            proof {
                assert(seen_bit(seen@, ty as int));
                let k = choose|k: int| 0 <= k < i && #[trigger] d[k].ty == ty;
                assert(0 <= k < i && d[k].ty == d[i as int].ty);
            }
            return Err(ALERT_ILLEGAL_PARAMETER);
        }
        assert(!seen_bit(seen@, ty as int));
        if (ty == EXT_PRE_SHARED_KEY && i != n - 1) || ty == EXT_OID_FILTERS {
            return Err(ALERT_ILLEGAL_PARAMETER);
        }
        let ghost old_seen = seen@;
        seen.set(wi, word | (1u64 << b));
        proof {
            assert forall|u: int| 0 <= u < 0x1_0000 implies (#[trigger] seen_bit(seen@, u)
                <==> exists|k: int| 0 <= k < i + 1 && #[trigger] d[k].ty == u) by {
                if u == ty as int {
                    lemma_bit_set_same(word, b);
                    assert(d[i as int].ty == u);
                } else {
                    if u / 64 == wi as int {
                        lemma_bit_set_other(word, b, (u % 64) as u64);
                    } else {
                        assert(seen@[u / 64] == old_seen[u / 64]);
                    }
                    assert(seen_bit(seen@, u) == seen_bit(old_seen, u));
                    if exists|k: int| 0 <= k < i + 1 && #[trigger] d[k].ty == u {
                        let k = choose|k: int| 0 <= k < i + 1 && #[trigger] d[k].ty == u;
                        assert(k != i);
                    }
                }
            }
        }
        i += 1;
    }
    Ok(())
}

/// The index of the first extension of type `ty`, tied to `spec_find`.
pub fn find_ext(s: &Vec<Ext>, ty: u16) -> (r: Option<usize>)
    ensures
        match r {
            Some(i) => i < s@.len() && s@[i as int].ty == ty && forall|k: int|
                0 <= k < i ==> #[trigger] s@[k].ty != ty,
            None => forall|k: int| 0 <= k < s@.len() ==> #[trigger] s@[k].ty != ty,
        },
        r matches Some(i) ==> spec_find(s.deep_view(), ty) == Some(s@[i as int].data@),
        r is None ==> spec_find(s.deep_view(), ty) is None,
{
    let ghost d = s.deep_view();
    let mut i: usize = 0;
    assert(d.skip(0) =~= d);
    while i < s.len()
        invariant
            i <= s@.len(),
            d == s.deep_view(),
            d.len() == s@.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] s@[k].ty != ty,
            spec_find(d, ty) == spec_find(d.skip(i as int), ty),
        decreases s@.len() - i,
    {
        assert(d.skip(i as int)[0] == s@[i as int]@);
        if s[i].ty == ty {
            return Some(i);
        }
        assert(d.skip(i as int).skip(1) =~= d.skip(i + 1));
        i += 1;
    }
    assert(d.skip(i as int).len() == 0);
    None
}

} // verus!
