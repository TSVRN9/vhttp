//! ClientHello extension bodies (RFC 8446 §4.2.x, RFC 7301 §3.1, RFC 6066 §3): one
//! transcribed spec and one parser per grammar, each consuming the whole `extension_data`.
use vstd::prelude::*;
use crate::pl::*;
use vstd::slice::{slice_subrange, slice_to_vec};

verus! {

#[derive(Debug, PartialEq, Eq)]
pub struct KeyShareEntry {
    pub group: u16,
    pub key_exchange: Vec<u8>,
}

pub struct SpecKeyShare {
    pub group: u16,
    pub key_exchange: Seq<u8>,
}

impl View for KeyShareEntry {
    type V = SpecKeyShare;

    open spec fn view(&self) -> SpecKeyShare {
        SpecKeyShare { group: self.group, key_exchange: self.key_exchange@ }
    }
}

impl DeepView for KeyShareEntry {
    type V = SpecKeyShare;

    open spec fn deep_view(&self) -> SpecKeyShare {
        self@
    }
}

// =============================================================================
// Transcription
// =============================================================================

/// `uint16` list in a `<floor..ceiling>` vector that is all of `d`.
pub open spec fn rfc_u16_vec(d: Seq<u8>, floor: nat, ceiling: nat) -> Option<Seq<u16>> {
    match rfc_vec_exact(d, floor, ceiling) {
        Some(c) => rfc_u16_list(c),
        None => None,
    }
}

//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.1
//# ProtocolVersion versions<2..254>;
pub open spec fn rfc_versions(d: Seq<u8>) -> Option<Seq<u16>> {
    rfc_u16_vec(d, 2, 254)
}

//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.7
//# NamedGroup named_group_list<2..2^16-1>;
pub open spec fn rfc_groups(d: Seq<u8>) -> Option<Seq<u16>> {
    rfc_u16_vec(d, 2, 0xffff)
}

//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.3
//# SignatureScheme supported_signature_algorithms<2..2^16-2>;
pub open spec fn rfc_sig_schemes(d: Seq<u8>) -> Option<Seq<u16>> {
    rfc_u16_vec(d, 2, 0xfffe)
}

//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.8
//# opaque key_exchange<1..2^16-1>;
/// `KeyShareEntry`s filling `b`.
pub open spec fn rfc_key_share_list(b: Seq<u8>) -> Option<Seq<SpecKeyShare>>
    decreases b.len(),
{
    if b.len() == 0 {
        Some(seq![])
    } else if b.len() < 2 {
        None
    } else {
        match rfc_vec(b.skip(2), 1, 0xffff) {
            None => None,
            Some((kx, rest)) => match rfc_key_share_list(rest) {
                None => None,
                Some(tail) => Some(
                    seq![SpecKeyShare { group: be(b, 2) as u16, key_exchange: kx }] + tail,
                ),
            },
        }
    }
}

//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.8
//# KeyShareEntry client_shares<0..2^16-1>;
pub open spec fn rfc_key_shares(d: Seq<u8>) -> Option<Seq<SpecKeyShare>> {
    match rfc_vec_exact(d, 0, 0xffff) {
        Some(c) => rfc_key_share_list(c),
        None => None,
    }
}

/// `opaque<floor..ceiling>` items filling `b`.
pub open spec fn rfc_vec_list(b: Seq<u8>, floor: nat, ceiling: nat) -> Option<Seq<Seq<u8>>>
    decreases b.len(),
{
    if b.len() == 0 {
        Some(seq![])
    } else {
        match rfc_vec(b, floor, ceiling) {
            None => None,
            Some((x, rest)) => match rfc_vec_list(rest, floor, ceiling) {
                None => None,
                Some(tail) => Some(seq![x] + tail),
            },
        }
    }
}

// RFC 7301 §3.1: `opaque ProtocolName<1..2^8-1>;` and `ProtocolName protocol_name_list<2..2^16-1>;`
pub open spec fn rfc_alpn(d: Seq<u8>) -> Option<Seq<Seq<u8>>> {
    match rfc_vec_exact(d, 2, 0xffff) {
        Some(c) => rfc_vec_list(c, 1, 255),
        None => None,
    }
}

// RFC 6066 §3: `ServerName server_name_list<1..2^16-1>`, each `NameType name_type;` then
// `opaque HostName<1..2^16-1>` for host_name(0); any other type is `opaque<0..2^16-1>`.
// RFC 6066 §3: "The ServerNameList MUST NOT contain more than one name of the same name_type."
// A second host_name is rejected here (decode_error upstream).
/// The host_name in the `ServerName`s filling `b`, if the list is well formed.
pub open spec fn rfc_sn_list(b: Seq<u8>) -> Option<Option<Seq<u8>>>
    decreases b.len(),
{
    if b.len() == 0 {
        Some(None)
    } else {
        match rfc_vec(b.skip(1), if b[0] == 0 { 1nat } else { 0nat }, 0xffff) {
            None => None,
            Some((x, rest)) => match rfc_sn_list(rest) {
                None => None,
                Some(tail) => if b[0] != 0 {
                    Some(tail)
                } else if tail is Some {
                    None
                } else {
                    Some(Some(x))
                },
            },
        }
    }
}

pub open spec fn rfc_server_name(d: Seq<u8>) -> Option<Option<Seq<u8>>> {
    match rfc_vec_exact(d, 1, 0xffff) {
        Some(c) => rfc_sn_list(c),
        None => None,
    }
}

//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.2
//# opaque cookie<1..2^16-1>;
pub open spec fn rfc_cookie_ok(d: Seq<u8>) -> bool {
    rfc_vec_exact(d, 1, 0xffff) is Some
}

//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.9
//# PskKeyExchangeMode ke_modes<1..255>;
pub open spec fn rfc_psk_modes(d: Seq<u8>) -> Option<Seq<u8>> {
    rfc_vec_exact(d, 1, 255)
}

/// `opaque<floor..ceiling>` items each followed by `trail` fixed bytes, filling `b`.
pub open spec fn rfc_vecs_ok(b: Seq<u8>, floor: nat, ceiling: nat, trail: nat) -> bool
    decreases b.len(),
{
    if b.len() == 0 {
        true
    } else {
        match rfc_vec(b, floor, ceiling) {
            None => false,
            Some((_, rest)) => rest.len() >= trail && rfc_vecs_ok(
                rest.skip(trail as int),
                floor,
                ceiling,
                trail,
            ),
        }
    }
}

//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.11
//# opaque identity<1..2^16-1>;
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.11
//# opaque PskBinderEntry<32..255>;
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.11
//# PskIdentity identities<7..2^16-1>;
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.11
//# PskBinderEntry binders<33..2^16-1>;
pub open spec fn rfc_offered_psks_ok(d: Seq<u8>) -> bool {
    match rfc_vec(d, 7, 0xffff) {
        None => false,
        Some((ids, rest)) => rfc_vecs_ok(ids, 1, 0xffff, 4) && match rfc_vec_exact(
            rest,
            33,
            0xffff,
        ) {
            None => false,
            Some(binders) => rfc_vecs_ok(binders, 32, 255, 0),
        },
    }
}

//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.10
//# struct {} Empty;
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.10
//# case client_hello:         Empty;
pub open spec fn rfc_early_data_ok(d: Seq<u8>) -> bool {
    d.len() == 0
}

// =============================================================================
// Exec
// =============================================================================

/// The `(start, end)` of the `<floor..ceiling>` vector that is all of `d`.
fn read_exact(d: &[u8], floor: usize, ceiling: usize) -> (r: Option<(usize, usize)>)
    requires
        ceiling < 0x100_0000,
    ensures
        r is None <==> rfc_vec_exact(d@, floor as nat, ceiling as nat) is None,
        r matches Some((s, e)) ==> s <= e && e == d@.len() && rfc_vec_exact(
            d@,
            floor as nat,
            ceiling as nat,
        ) == Some(d@.subrange(s as int, e as int)),
{
    assert(d@.skip(0) =~= d@);
    match read_vec(d, 0, floor, ceiling) {
        None => None,
        Some((s, e)) => {
            if e == d.len() {
                Some((s, e))
            } else {
                None
            }
        },
    }
}

pub fn parse_u16_vec(d: &[u8], floor: usize, ceiling: usize) -> (r: Option<Vec<u16>>)
    requires
        ceiling < 0x100_0000,
    ensures
        r.deep_view() == rfc_u16_vec(d@, floor as nat, ceiling as nat),
{
    match read_exact(d, floor, ceiling) {
        None => None,
        Some((s, e)) => parse_u16_list(slice_subrange(d, s, e)),
    }
}

pub fn parse_versions(d: &[u8]) -> (r: Option<Vec<u16>>)
    ensures
        r.deep_view() == rfc_versions(d@),
{
    parse_u16_vec(d, 2, 254)
}

pub fn parse_groups(d: &[u8]) -> (r: Option<Vec<u16>>)
    ensures
        r.deep_view() == rfc_groups(d@),
{
    parse_u16_vec(d, 2, 0xffff)
}

pub fn parse_sig_schemes(d: &[u8]) -> (r: Option<Vec<u16>>)
    ensures
        r.deep_view() == rfc_sig_schemes(d@),
{
    parse_u16_vec(d, 2, 0xfffe)
}

fn parse_key_share_list(b: &[u8]) -> (r: Option<Vec<KeyShareEntry>>)
    ensures
        r.deep_view() == rfc_key_share_list(b@),
{
    let mut v: Vec<KeyShareEntry> = Vec::new();
    let mut pos: usize = 0;
    assert(b@.skip(0) =~= b@);
    assert(v.deep_view() + seq![] =~= seq![]);
    while pos < b.len()
        invariant
            pos <= b@.len(),
            rfc_key_share_list(b@) == match rfc_key_share_list(b@.skip(pos as int)) {
                Some(t) => Some(v.deep_view() + t),
                None => None,
            },
        decreases b@.len() - pos,
    {
        let ghost t = b@.skip(pos as int);
        let group = match read_u16(b, pos) {
            Some(x) => x,
            None => return None,
        };
        assert(t.skip(2) =~= b@.skip(pos + 2));
        let (s, e) = match read_vec(b, pos + 2, 1, 0xffff) {
            Some(se) => se,
            None => return None,
        };
        let key_exchange = slice_to_vec(slice_subrange(b, s, e));
        let ghost old_v = v.deep_view();
        v.push(KeyShareEntry { group, key_exchange });
        assert(v.deep_view() =~= old_v.push(SpecKeyShare { group: be(t, 2) as u16, key_exchange: key_exchange@ }));
        pos = e;
        proof {
            if let Some(tail) = rfc_key_share_list(b@.skip(pos as int)) {
                assert(old_v + (seq![SpecKeyShare { group: be(t, 2) as u16, key_exchange: key_exchange@ }] + tail)
                    =~= v.deep_view() + tail);
            }
        }
    }
    assert(b@.skip(pos as int) =~= seq![]);
    assert(v.deep_view() + seq![] =~= v.deep_view());
    Some(v)
}

pub fn parse_key_shares(d: &[u8]) -> (r: Option<Vec<KeyShareEntry>>)
    ensures
        r.deep_view() == rfc_key_shares(d@),
{
    match read_exact(d, 0, 0xffff) {
        None => None,
        Some((s, e)) => parse_key_share_list(slice_subrange(d, s, e)),
    }
}

fn parse_vec_list(b: &[u8], floor: usize, ceiling: usize) -> (r: Option<Vec<Vec<u8>>>)
    requires
        ceiling < 0x100_0000,
    ensures
        r.deep_view() == rfc_vec_list(b@, floor as nat, ceiling as nat),
{
    let mut v: Vec<Vec<u8>> = Vec::new();
    let mut pos: usize = 0;
    assert(b@.skip(0) =~= b@);
    assert(v.deep_view() + seq![] =~= seq![]);
    while pos < b.len()
        invariant
            pos <= b@.len(),
            ceiling < 0x100_0000,
            rfc_vec_list(b@, floor as nat, ceiling as nat) == match rfc_vec_list(
                b@.skip(pos as int),
                floor as nat,
                ceiling as nat,
            ) {
                Some(t) => Some(v.deep_view() + t),
                None => None,
            },
        decreases b@.len() - pos,
    {
        let (s, e) = match read_vec(b, pos, floor, ceiling) {
            Some(se) => se,
            None => return None,
        };
        let x = slice_to_vec(slice_subrange(b, s, e));
        let ghost old_v = v.deep_view();
        assert(x.deep_view() =~= x@);
        v.push(x);
        assert(v.deep_view() =~= old_v.push(x@));
        pos = e;
        proof {
            if let Some(tail) = rfc_vec_list(b@.skip(pos as int), floor as nat, ceiling as nat) {
                assert(old_v + (seq![x@] + tail) =~= v.deep_view() + tail);
            }
        }
    }
    assert(b@.skip(pos as int) =~= seq![]);
    assert(v.deep_view() + seq![] =~= v.deep_view());
    Some(v)
}

pub fn parse_alpn(d: &[u8]) -> (r: Option<Vec<Vec<u8>>>)
    ensures
        r.deep_view() == rfc_alpn(d@),
{
    match read_exact(d, 2, 0xffff) {
        None => None,
        Some((s, e)) => parse_vec_list(slice_subrange(d, s, e), 1, 255),
    }
}

fn parse_sn_list(b: &[u8]) -> (r: Option<Option<Vec<u8>>>)
    ensures
        r.deep_view() == rfc_sn_list(b@),
{
    let mut first: Option<Vec<u8>> = None;
    let mut pos: usize = 0;
    assert(b@.skip(0) =~= b@);
    while pos < b.len()
        invariant
            pos <= b@.len(),
            rfc_sn_list(b@) == match rfc_sn_list(b@.skip(pos as int)) {
                None => None,
                Some(t) => if first is Some {
                    if t is Some {
                        None
                    } else {
                        Some(first.deep_view())
                    }
                } else {
                    Some(t)
                },
            },
        decreases b@.len() - pos,
    {
        let ghost t = b@.skip(pos as int);
        let is_host = b[pos] == 0;
        assert(t.skip(1) =~= b@.skip(pos + 1));
        let (s, e) = match read_vec(b, pos + 1, if is_host { 1 } else { 0 }, 0xffff) {
            Some(se) => se,
            None => return None,
        };
        if is_host {
            if first.is_some() {
                return None;
            }
            first = Some(slice_to_vec(slice_subrange(b, s, e)));
        }
        pos = e;
    }
    assert(b@.skip(pos as int) =~= seq![]);
    Some(first)
}

pub fn parse_server_name(d: &[u8]) -> (r: Option<Option<Vec<u8>>>)
    ensures
        r.deep_view() == rfc_server_name(d@),
{
    match read_exact(d, 1, 0xffff) {
        None => None,
        Some((s, e)) => parse_sn_list(slice_subrange(d, s, e)),
    }
}

pub fn cookie_ok(d: &[u8]) -> (r: bool)
    ensures
        r == rfc_cookie_ok(d@),
{
    read_exact(d, 1, 0xffff).is_some()
}

pub fn parse_psk_modes(d: &[u8]) -> (r: Option<Vec<u8>>)
    ensures
        r.deep_view() == rfc_psk_modes(d@),
{
    match read_exact(d, 1, 255) {
        None => None,
        Some((s, e)) => Some(slice_to_vec(slice_subrange(d, s, e))),
    }
}

fn vecs_ok(b: &[u8], floor: usize, ceiling: usize, trail: usize) -> (r: bool)
    requires
        ceiling < 0x100_0000,
        trail <= 4,
    ensures
        r == rfc_vecs_ok(b@, floor as nat, ceiling as nat, trail as nat),
{
    let mut pos: usize = 0;
    assert(b@.skip(0) =~= b@);
    while pos < b.len()
        invariant
            pos <= b@.len(),
            ceiling < 0x100_0000,
            trail <= 4,
            rfc_vecs_ok(b@, floor as nat, ceiling as nat, trail as nat) == rfc_vecs_ok(
                b@.skip(pos as int),
                floor as nat,
                ceiling as nat,
                trail as nat,
            ),
        decreases b@.len() - pos,
    {
        let e = match read_vec(b, pos, floor, ceiling) {
            Some((_, e)) => e,
            None => return false,
        };
        if b.len() - e < trail {
            return false;
        }
        assert(b@.skip(pos as int).skip((e - pos) as int) =~= b@.skip(e as int)) by {}
        assert(b@.skip(e as int).skip(trail as int) =~= b@.skip((e + trail) as int));
        pos = e + trail;
    }
    assert(b@.skip(pos as int) =~= seq![]);
    true
}

pub fn offered_psks_ok(d: &[u8]) -> (r: bool)
    ensures
        r == rfc_offered_psks_ok(d@),
{
    assert(d@.skip(0) =~= d@);
    let (s, e) = match read_vec(d, 0, 7, 0xffff) {
        Some(se) => se,
        None => return false,
    };
    if !vecs_ok(slice_subrange(d, s, e), 1, 0xffff, 4) {
        return false;
    }
    let rest = slice_subrange(d, e, d.len());
    assert(rest@ =~= d@.skip(e as int));
    match read_exact(rest, 33, 0xffff) {
        None => false,
        Some((s2, e2)) => vecs_ok(slice_subrange(rest, s2, e2), 32, 255, 0),
    }
}

pub fn early_data_ok(d: &[u8]) -> (r: bool)
    ensures
        r == rfc_early_data_ok(d@),
{
    d.len() == 0
}

} // verus!
