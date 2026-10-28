//! HKDF-Expand-Label and Derive-Secret (RFC 8446 §7.1).
//
// RFC 8446 §7.1:
//   HKDF-Expand-Label(Secret, Label, Context, Length) =
//        HKDF-Expand(Secret, HkdfLabel, Length)
//   struct { uint16 length = Length;
//            opaque label<7..255> = "tls13 " + Label;
//            opaque context<0..255> = Context; } HkdfLabel;
//   Derive-Secret(Secret, Label, Messages) =
//        HKDF-Expand-Label(Secret, Label, Transcript-Hash(Messages), Hash.length)
use crate::codes::*;
use crate::pl::*;
use crypto::hkdf::*;
use vstd::prelude::*;

verus! {

pub open spec fn spec_hkdf_label(label: Seq<u8>, context: Seq<u8>, len: nat) -> Seq<u8> {
    spec_be_bytes(len, 2) + spec_vec_bytes(255, LABEL_PREFIX@ + label) + spec_vec_bytes(
        255,
        context,
    )
}

pub open spec fn spec_hkdf_expand_label(secret: Seq<u8>, label: Seq<u8>, context: Seq<u8>, len: nat) -> Seq<u8> {
    spec_hkdf_expand(secret, spec_hkdf_label(label, context, len), len)
}

/// `messages` is the §4.4.1 transcript as a byte string.
pub open spec fn spec_derive_secret(secret: Seq<u8>, label: Seq<u8>, messages: Seq<u8>) -> Seq<u8> {
    spec_hkdf_expand_label(secret, label, crypto::sha256::spec_sha256(messages), 32)
}

/// The `<7..255>` bound on the label, after the 6-byte prefix.
pub open spec fn label_ok(label: Seq<u8>) -> bool {
    1 <= label.len() <= 249
}

pub fn hkdf_label(label: &[u8], context: &[u8], len: u16) -> (r: Vec<u8>)
    requires
        label_ok(label@),
        context@.len() <= 255,
    ensures
        r@ == spec_hkdf_label(label@, context@, len as nat),
        r@.len() <= 2 + 1 + 255 + 1 + 255,
{
    let mut out: Vec<u8> = Vec::new();
    put_u16(&mut out, len);
    let mut full: Vec<u8> = Vec::new();
    full.extend_from_slice(&LABEL_PREFIX);
    full.extend_from_slice(label);
    assert(full@ =~= LABEL_PREFIX@ + label@);
    put_vec(&mut out, 255, &full);
    put_vec(&mut out, 255, context);
    proof {
        assert(len_width(255) == 1);
        assert(spec_be_bytes(len as nat, 2).len() == 2);
        assert(spec_be_bytes(context@.len(), 1).len() == 1);
        assert(spec_be_bytes((LABEL_PREFIX@ + label@).len(), 1).len() == 1);
    }
    out
}

pub fn hkdf_expand_label(secret: &[u8; 32], label: &[u8], context: &[u8], len: usize) -> (r: Vec<u8>)
    requires
        label_ok(label@),
        context@.len() <= 255,
        len <= 8160,
    ensures
        r@ == spec_hkdf_expand_label(secret@, label@, context@, len as nat),
        r@.len() == len,
{
    let info = hkdf_label(label, context, len as u16);
    let r = hkdf_expand(secret.as_slice(), &info, len);
    proof {
        lemma_spec_hkdf_expand_len(secret@, info@, len as nat);
    }
    r
}

pub fn derive_secret(secret: &[u8; 32], label: &[u8], transcript_hash: &[u8; 32]) -> (r: [u8; 32])
    requires
        label_ok(label@),
    ensures
        r@ == spec_hkdf_expand_label(secret@, label@, transcript_hash@, 32),
{
    let v = hkdf_expand_label(secret, label, transcript_hash.as_slice(), 32);
    let mut r = [0u8; 32];
    let mut i: usize = 0;
    while i < 32
        invariant
            i <= 32,
            v@.len() == 32,
            forall|j: int| 0 <= j < i ==> r@[j] == v@[j],
        decreases 32 - i,
    {
        r[i] = v[i];
        i += 1;
    }
    assert(r@ =~= v@);
    r
}

} // verus!
