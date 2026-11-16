//! HTTP message validation for HTTP/3 (RFC 9114 §4.2-§4.4, §10.3) over decoded QPACK field lines:
//! request and trailer validation proved equal to RFC-transcribed specs, cookie merging, and a
//! response check that establishes `encode_field_section`'s preconditions. RFC 9110 field syntax
//! (§5.1 field-name = token, §5.5 field-content) is cited in plain comments: RFC 9110 is not in the
//! Duvet config.
use crate::codes::H3_MESSAGE_ERROR;
// Read only by `validate_request`'s requires, erased by a plain `cargo build`.
#[allow(unused_imports)]
use crate::limits::MAX_FIELD_SECTION_SIZE;
use byteq::capvec::CapVec;
// `fields_view` is ghost, erased by a plain `cargo build`.
#[allow(unused_imports)]
use crate::qpack::field_section::*;
use crate::qpack::int::PREFIX_INT_MAX;
use vstd::prelude::*;
use vstd::slice::slice_to_vec;

verus! {

type Fields = Seq<(Seq<u8>, Seq<u8>)>;

pub struct Request {
    pub method: Vec<u8>,
    pub scheme: Vec<u8>,
    pub authority: Vec<u8>,
    pub path: Vec<u8>,
    /// Regular fields in received order, with cookie lines merged.
    pub headers: Vec<FieldLine>,
}

pub enum RequestHead {
    Request(Request),
    /// A well-formed CONNECT, surfaced so the connection can answer 501.
    Connect { authority: Vec<u8> },
}

pub struct Response {
    pub status: u16,
    pub headers: Vec<FieldLine>,
    pub body: Vec<u8>,
}

pub struct SpecRequest {
    pub method: Seq<u8>,
    pub scheme: Seq<u8>,
    pub authority: Seq<u8>,
    pub path: Seq<u8>,
    pub headers: Fields,
}

pub enum SpecRequestHead {
    Request(SpecRequest),
    Connect { authority: Seq<u8> },
}

pub struct SpecResponse {
    pub status: u16,
    pub headers: Fields,
    pub body: Seq<u8>,
}

impl View for Request {
    type V = SpecRequest;

    open spec fn view(&self) -> SpecRequest {
        SpecRequest {
            method: self.method@,
            scheme: self.scheme@,
            authority: self.authority@,
            path: self.path@,
            headers: fields_view(self.headers@),
        }
    }
}

impl View for RequestHead {
    type V = SpecRequestHead;

    open spec fn view(&self) -> SpecRequestHead {
        match self {
            RequestHead::Request(r) => SpecRequestHead::Request(r@),
            RequestHead::Connect { authority } => SpecRequestHead::Connect {
                authority: authority@,
            },
        }
    }
}

impl View for Response {
    type V = SpecResponse;

    open spec fn view(&self) -> SpecResponse {
        SpecResponse {
            status: self.status,
            headers: fields_view(self.headers@),
            body: self.body@,
        }
    }
}

// Byte-string literals: a spec constant and an exec twin proved equal to it.
pub open spec fn lit_method() -> Seq<u8> {
    seq![58u8, 109u8, 101u8, 116u8, 104u8, 111u8, 100u8]
}

fn x_method() -> (r: [u8; 7])
    ensures
        r@ == lit_method(),
{
    let l = [58u8, 109u8, 101u8, 116u8, 104u8, 111u8, 100u8];
    assert(l@ =~= lit_method());
    l
}

pub open spec fn lit_scheme() -> Seq<u8> {
    seq![58u8, 115u8, 99u8, 104u8, 101u8, 109u8, 101u8]
}

fn x_scheme() -> (r: [u8; 7])
    ensures
        r@ == lit_scheme(),
{
    let l = [58u8, 115u8, 99u8, 104u8, 101u8, 109u8, 101u8];
    assert(l@ =~= lit_scheme());
    l
}

pub open spec fn lit_authority() -> Seq<u8> {
    seq![58u8, 97u8, 117u8, 116u8, 104u8, 111u8, 114u8, 105u8, 116u8, 121u8]
}

fn x_authority() -> (r: [u8; 10])
    ensures
        r@ == lit_authority(),
{
    let l = [58u8, 97u8, 117u8, 116u8, 104u8, 111u8, 114u8, 105u8, 116u8, 121u8];
    assert(l@ =~= lit_authority());
    l
}

pub open spec fn lit_path() -> Seq<u8> {
    seq![58u8, 112u8, 97u8, 116u8, 104u8]
}

fn x_path() -> (r: [u8; 5])
    ensures
        r@ == lit_path(),
{
    let l = [58u8, 112u8, 97u8, 116u8, 104u8];
    assert(l@ =~= lit_path());
    l
}

pub open spec fn lit_connection() -> Seq<u8> {
    seq![99u8, 111u8, 110u8, 110u8, 101u8, 99u8, 116u8, 105u8, 111u8, 110u8]
}

fn x_connection() -> (r: [u8; 10])
    ensures
        r@ == lit_connection(),
{
    let l = [99u8, 111u8, 110u8, 110u8, 101u8, 99u8, 116u8, 105u8, 111u8, 110u8];
    assert(l@ =~= lit_connection());
    l
}

pub open spec fn lit_keep_alive() -> Seq<u8> {
    seq![107u8, 101u8, 101u8, 112u8, 45u8, 97u8, 108u8, 105u8, 118u8, 101u8]
}

fn x_keep_alive() -> (r: [u8; 10])
    ensures
        r@ == lit_keep_alive(),
{
    let l = [107u8, 101u8, 101u8, 112u8, 45u8, 97u8, 108u8, 105u8, 118u8, 101u8];
    assert(l@ =~= lit_keep_alive());
    l
}

pub open spec fn lit_proxy_connection() -> Seq<u8> {
    seq![112u8, 114u8, 111u8, 120u8, 121u8, 45u8, 99u8, 111u8, 110u8, 110u8, 101u8, 99u8, 116u8, 105u8, 111u8, 110u8]
}

fn x_proxy_connection() -> (r: [u8; 16])
    ensures
        r@ == lit_proxy_connection(),
{
    let l = [112u8, 114u8, 111u8, 120u8, 121u8, 45u8, 99u8, 111u8, 110u8, 110u8, 101u8, 99u8, 116u8, 105u8, 111u8, 110u8];
    assert(l@ =~= lit_proxy_connection());
    l
}

pub open spec fn lit_transfer_encoding() -> Seq<u8> {
    seq![116u8, 114u8, 97u8, 110u8, 115u8, 102u8, 101u8, 114u8, 45u8, 101u8, 110u8, 99u8, 111u8, 100u8, 105u8, 110u8, 103u8]
}

fn x_transfer_encoding() -> (r: [u8; 17])
    ensures
        r@ == lit_transfer_encoding(),
{
    let l = [116u8, 114u8, 97u8, 110u8, 115u8, 102u8, 101u8, 114u8, 45u8, 101u8, 110u8, 99u8, 111u8, 100u8, 105u8, 110u8, 103u8];
    assert(l@ =~= lit_transfer_encoding());
    l
}

pub open spec fn lit_upgrade() -> Seq<u8> {
    seq![117u8, 112u8, 103u8, 114u8, 97u8, 100u8, 101u8]
}

fn x_upgrade() -> (r: [u8; 7])
    ensures
        r@ == lit_upgrade(),
{
    let l = [117u8, 112u8, 103u8, 114u8, 97u8, 100u8, 101u8];
    assert(l@ =~= lit_upgrade());
    l
}

pub open spec fn lit_te() -> Seq<u8> {
    seq![116u8, 101u8]
}

fn x_te() -> (r: [u8; 2])
    ensures
        r@ == lit_te(),
{
    let l = [116u8, 101u8];
    assert(l@ =~= lit_te());
    l
}

pub open spec fn lit_trailers() -> Seq<u8> {
    seq![116u8, 114u8, 97u8, 105u8, 108u8, 101u8, 114u8, 115u8]
}

fn x_trailers() -> (r: [u8; 8])
    ensures
        r@ == lit_trailers(),
{
    let l = [116u8, 114u8, 97u8, 105u8, 108u8, 101u8, 114u8, 115u8];
    assert(l@ =~= lit_trailers());
    l
}

pub open spec fn lit_cookie() -> Seq<u8> {
    seq![99u8, 111u8, 111u8, 107u8, 105u8, 101u8]
}

fn x_cookie() -> (r: [u8; 6])
    ensures
        r@ == lit_cookie(),
{
    let l = [99u8, 111u8, 111u8, 107u8, 105u8, 101u8];
    assert(l@ =~= lit_cookie());
    l
}

pub open spec fn lit_host() -> Seq<u8> {
    seq![104u8, 111u8, 115u8, 116u8]
}

fn x_host() -> (r: [u8; 4])
    ensures
        r@ == lit_host(),
{
    let l = [104u8, 111u8, 115u8, 116u8];
    assert(l@ =~= lit_host());
    l
}

pub open spec fn lit_content_length() -> Seq<u8> {
    seq![99u8, 111u8, 110u8, 116u8, 101u8, 110u8, 116u8, 45u8, 108u8, 101u8, 110u8, 103u8, 116u8, 104u8]
}

fn x_content_length() -> (r: [u8; 14])
    ensures
        r@ == lit_content_length(),
{
    let l = [99u8, 111u8, 110u8, 116u8, 101u8, 110u8, 116u8, 45u8, 108u8, 101u8, 110u8, 103u8, 116u8, 104u8];
    assert(l@ =~= lit_content_length());
    l
}

pub open spec fn lit_connect() -> Seq<u8> {
    seq![67u8, 79u8, 78u8, 78u8, 69u8, 67u8, 84u8]
}

fn x_connect() -> (r: [u8; 7])
    ensures
        r@ == lit_connect(),
{
    let l = [67u8, 79u8, 78u8, 78u8, 69u8, 67u8, 84u8];
    assert(l@ =~= lit_connect());
    l
}

pub open spec fn lit_http() -> Seq<u8> {
    seq![104u8, 116u8, 116u8, 112u8]
}

fn x_http() -> (r: [u8; 4])
    ensures
        r@ == lit_http(),
{
    let l = [104u8, 116u8, 116u8, 112u8];
    assert(l@ =~= lit_http());
    l
}

pub open spec fn lit_https() -> Seq<u8> {
    seq![104u8, 116u8, 116u8, 112u8, 115u8]
}

fn x_https() -> (r: [u8; 5])
    ensures
        r@ == lit_https(),
{
    let l = [104u8, 116u8, 116u8, 112u8, 115u8];
    assert(l@ =~= lit_https());
    l
}

pub open spec fn lit_semi() -> Seq<u8> {
    seq![59u8, 32u8]
}

fn x_semi() -> (r: [u8; 2])
    ensures
        r@ == lit_semi(),
{
    let l = [59u8, 32u8];
    assert(l@ =~= lit_semi());
    l
}

// =============================================================================
// Byte helpers
// =============================================================================

/// The cost constant of `eq_bytes_w`.
pub open spec fn c_eq() -> nat {
    1
}

/// `eq_bytes` with its cost: one unit for the length check, one per byte compared.
pub fn eq_bytes_w(a: &[u8], b: &[u8]) -> (r: (bool, Ghost<nat>))
    ensures
        r.0 == (a@ == b@),
        r.1@ <= c_eq() * ((if a@.len() <= b@.len() {
            a@.len()
        } else {
            b@.len()
        }) + 1),
{
    let ghost mut work: nat = 1;
    if a.len() != b.len() {
        return (false, Ghost(work));
    }
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a@.len() == b@.len(),
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
            work == i + 1,
        decreases a.len() - i,
    {
        if a[i] != b[i] {
            return (false, Ghost(work));
        }
        i += 1;
        proof {
            work = work + 1;
        }
    }
    assert(a@ =~= b@);
    (true, Ghost(work))
}

pub fn eq_bytes(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    eq_bytes_w(a, b).0
}

// =============================================================================
// RFC 9110 field syntax (Global Constraints), plus RFC 9114 §4.2 / §10.3 on the failure case
// =============================================================================

/// RFC 9110 §5.6.2 `tchar`, minus uppercase ALPHA: a byte allowed in a lowercase field name.
pub open spec fn tchar_lc_spec(b: u8) -> bool {
    b == 33 || b == 35 || b == 36 || b == 37 || b == 38 || b == 39 || b == 42 || b == 43 || b == 45
        || b == 46 || b == 94 || b == 95 || b == 96 || b == 124 || b == 126 || (48 <= b && b <= 57)
        || (97 <= b && b <= 122)
}

#[verifier::when_used_as_spec(tchar_lc_spec)]
pub fn tchar_lc(b: u8) -> (r: bool)
    ensures
        r == tchar_lc_spec(b),
{
    b == 33 || b == 35 || b == 36 || b == 37 || b == 38 || b == 39 || b == 42 || b == 43 || b == 45
        || b == 46 || b == 94 || b == 95 || b == 96 || b == 124 || b == 126 || (48 <= b && b <= 57)
        || (97 <= b && b <= 122)
}

/// RFC 9110 §5.5 `field-vchar`: VCHAR (0x21-0x7e) or obs-text (0x80-0xff).
pub open spec fn vchar_spec(b: u8) -> bool {
    (0x21 <= b && b <= 0x7e) || b >= 0x80
}

#[verifier::when_used_as_spec(vchar_spec)]
pub fn vchar(b: u8) -> (r: bool)
    ensures
        r == vchar_spec(b),
{
    (0x21 <= b && b <= 0x7e) || b >= 0x80
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.2
//# A request or
//# response containing uppercase characters in field names MUST be
//# treated as malformed.
//= https://www.rfc-editor.org/rfc/rfc9114#section-10.3
//# Requests or responses containing invalid field names MUST be treated
//# as malformed.
/// RFC 9110 §5.1: a non-empty run of lowercase `tchar`s.
pub open spec fn valid_field_name(n: Seq<u8>) -> bool {
    n.len() > 0 && forall|i: int| 0 <= i < n.len() ==> tchar_lc_spec(#[trigger] n[i])
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-10.3
//# Any request or response that contains a
//# character not permitted in a field value MUST be treated as
//# malformed.
/// RFC 9110 §5.5 `field-content`: empty, or first and last bytes are `field-vchar` and every
/// interior byte is `field-vchar`, SP or HTAB.
pub open spec fn valid_field_value(v: Seq<u8>) -> bool {
    v.len() == 0 || (vchar_spec(v[0]) && vchar_spec(v[v.len() - 1]) && forall|i: int|
        0 <= i < v.len() ==> vchar_spec(#[trigger] v[i]) || v[i] == 32 || v[i] == 9)
}

pub fn field_name_ok(n: &[u8]) -> (r: bool)
    ensures
        r == valid_field_name(n@),
{
    if n.len() == 0 {
        return false;
    }
    let mut i = 0;
    while i < n.len()
        invariant
            i <= n.len(),
            forall|k: int| 0 <= k < i ==> tchar_lc_spec(#[trigger] n@[k]),
        decreases n.len() - i,
    {
        if !tchar_lc(n[i]) {
            return false;
        }
        i += 1;
    }
    true
}

pub fn field_value_ok(v: &[u8]) -> (r: bool)
    ensures
        r == valid_field_value(v@),
{
    if v.len() == 0 {
        return true;
    }
    if !vchar(v[0]) || !vchar(v[v.len() - 1]) {
        return false;
    }
    let mut i = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            forall|k: int| 0 <= k < i ==> vchar_spec(#[trigger] v@[k]) || v@[k] == 32 || v@[k] == 9,
        decreases v.len() - i,
    {
        if !(vchar(v[i]) || v[i] == 32 || v[i] == 9) {
            return false;
        }
        i += 1;
    }
    true
}

// =============================================================================
// Specs over decoded field lines (name, value)
// =============================================================================

pub open spec fn is_pseudo(n: Seq<u8>) -> bool {
    n.len() > 0 && n[0] == 58
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.3
//# Endpoints MUST NOT
//# generate pseudo-header fields other than those defined in this
//# document.
//= https://www.rfc-editor.org/rfc/rfc9114#section-4.3.1
//# The following pseudo-header fields are defined for requests:
/// The request pseudo-headers this server accepts.
pub open spec fn request_pseudo(n: Seq<u8>) -> bool {
    n == lit_method() || n == lit_scheme() || n == lit_authority() || n == lit_path()
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.2
//# any
//# message containing connection-specific fields MUST be treated as
//# malformed.
pub open spec fn conn_specific(n: Seq<u8>) -> bool {
    n == lit_connection() || n == lit_keep_alive() || n == lit_proxy_connection() || n
        == lit_transfer_encoding() || n == lit_upgrade()
}

/// First index whose name is `name`.
pub open spec fn find_name(s: Fields, name: Seq<u8>) -> Option<int>
    decreases s.len(),
{
    if s.len() == 0 {
        None
    } else {
        match find_name(s.drop_last(), name) {
            Some(k) => Some(k),
            None => if s.last().0 == name {
                Some(s.len() - 1)
            } else {
                None
            },
        }
    }
}

proof fn lemma_find_name(s: Fields, name: Seq<u8>)
    ensures
        match find_name(s, name) {
            Some(k) => 0 <= k < s.len() && s[k].0 == name,
            None => forall|j: int| 0 <= j < s.len() ==> (#[trigger] s[j]).0 != name,
        },
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_find_name(s.drop_last(), name);
        assert forall|j: int| 0 <= j < s.len() - 1 implies s.drop_last()[j] == #[trigger] s[j] by {}
    }
}

/// Value of the first field named `name`.
pub open spec fn lookup(s: Fields, name: Seq<u8>) -> Option<Seq<u8>> {
    match find_name(s, name) {
        Some(k) => if 0 <= k < s.len() {
            Some(s[k].1)
        } else {
            None
        },
        None => None,
    }
}

pub open spec fn count_name(s: Fields, name: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        count_name(s.drop_last(), name) + if s.last().0 == name {
            1nat
        } else {
            0nat
        }
    }
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.3
//# Endpoints MUST treat a request or response that contains
//# undefined or invalid pseudo-header fields as malformed.
/// Every name is an accepted pseudo-header or a valid field name, and every value is valid. A
/// name starting with `:` is never a valid field name, so unknown pseudo-headers fail here.
pub open spec fn fields_syntax_ok(f: Fields) -> bool {
    forall|i: int|
        0 <= i < f.len() ==> (request_pseudo((#[trigger] f[i]).0) || valid_field_name(f[i].0))
            && valid_field_value(f[i].1)
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.3
//# All pseudo-header fields MUST appear in the header section before
//# regular header fields.
pub open spec fn pseudo_first(f: Fields) -> bool {
    forall|i: int, j: int|
        0 <= i < j < f.len() && !is_pseudo((#[trigger] f[i]).0) ==> !is_pseudo(
            (#[trigger] f[j]).0,
        )
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.3.1
//# All HTTP/3 requests MUST include exactly one value for the :method,
//# :scheme, and :path pseudo-header fields, unless the request is a
//# CONNECT request; see Section 4.4.
/// No request pseudo-header repeats. (Presence is checked in `rfc_validate_request`.) A repeated
/// `host` is rejected too: hardening, since RFC 9110 §5.3 says Host is not a list field, so a sender
/// MUST NOT repeat it.
pub open spec fn pseudo_once(f: Fields) -> bool {
    count_name(f, lit_method()) <= 1 && count_name(f, lit_scheme()) <= 1 && count_name(
        f,
        lit_authority(),
    ) <= 1 && count_name(f, lit_path()) <= 1 && count_name(f, lit_host()) <= 1
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.2
//# The only exception to this is the TE header field, which MAY be
//# present in an HTTP/3 request header; when it is, it MUST NOT contain
//# any value other than "trailers".
pub open spec fn no_conn_fields(f: Fields) -> bool {
    forall|i: int|
        0 <= i < f.len() ==> !conn_specific((#[trigger] f[i]).0) && (f[i].0 == lit_te() ==> f[i].1
            == lit_trailers())
}

/// Decimal value of the digits of `s` (a non-digit counts as 0).
pub open spec fn digits_val(s: Seq<u8>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        let c = s.last();
        digits_val(s.drop_last()) * 10 + if 48 <= c && c <= 57 {
            (c - 48) as int
        } else {
            0int
        }
    }
}

/// RFC 9110 §8.6 `Content-Length = 1*DIGIT`, here also required to fit a `u64`.
pub open spec fn cl_valid(v: Seq<u8>) -> bool {
    v.len() > 0 && (forall|i: int| 0 <= i < v.len() ==> 48 <= #[trigger] v[i] && v[i] <= 57)
        && digits_val(v) < 0x1_0000_0000_0000_0000
}

/// Every `content-length` value is valid and equal to the first one.
pub open spec fn cl_ok(f: Fields) -> bool {
    forall|i: int|
        0 <= i < f.len() && (#[trigger] f[i]).0 == lit_content_length() ==> cl_valid(f[i].1)
            && lookup(f, lit_content_length()) == Some(f[i].1)
}

pub open spec fn common_ok(f: Fields) -> bool {
    fields_syntax_ok(f) && pseudo_first(f) && pseudo_once(f) && no_conn_fields(f) && cl_ok(f)
}

/// `Some(n)` when the first `content-length` is valid.
pub open spec fn rfc_content_length(f: Fields) -> Option<u64> {
    match lookup(f, lit_content_length()) {
        Some(v) => if cl_valid(v) {
            Some(digits_val(v) as u64)
        } else {
            None
        },
        None => None,
    }
}

/// RFC 3986 section 3.1: schemes are case-insensitive. `lit` is lowercase.
pub open spec fn eq_ci(s: Seq<u8>, lit: Seq<u8>) -> bool {
    s.len() == lit.len() && forall|i: int|
        0 <= i < s.len() ==> (if 65 <= #[trigger] s[i] && s[i] <= 90 {
            (s[i] + 32) as u8
        } else {
            s[i]
        }) == lit[i]
}

pub open spec fn no_at(s: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i]) != 64u8
}

pub open spec fn is_digit(c: u8) -> bool {
    48 <= c && c <= 57
}

/// How many bytes at the end of `s` are digits.
pub open spec fn trailing_digits(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() > 0 && is_digit(s.last()) {
        trailing_digits(s.drop_last()) + 1
    } else {
        0
    }
}

// RFC 9110 §9.3.6 / §7.1: a CONNECT request-target is authority-form, `uri-host ":" port`, and
// the deprecated userinfo is excluded. `port` is `1*DIGIT` here: a tunnel needs a port.
/// `uri-host ":" port` with a non-empty host, a non-empty all-digit port and no `@`. The port is
/// the maximal run of trailing digits, so the byte before it must be the `:`.
pub open spec fn authority_form(a: Seq<u8>) -> bool {
    let d = trailing_digits(a);
    no_at(a) && d > 0 && d + 2 <= a.len() && a[a.len() - d - 1] == 58u8
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.3.1
//# If the :scheme pseudo-header field identifies a scheme that has a
//# mandatory authority component (including "http" and "https"), the
//# request MUST contain either an :authority pseudo-header field or a
//# Host header field.  If these fields are present, they MUST NOT be
//# empty.  If both fields are present, they MUST contain the same value.
//= https://www.rfc-editor.org/rfc/rfc9114#section-4.3.1
//# The authority MUST NOT include the
//# deprecated userinfo subcomponent for URIs of scheme "http" or
//# "https".
pub open spec fn authority_ok(scheme: Seq<u8>, a: Option<Seq<u8>>, h: Option<Seq<u8>>) -> bool {
    !(eq_ci(scheme, lit_http()) || eq_ci(scheme, lit_https())) || match (a, h) {
        (None, None) => false,
        (Some(x), None) => x.len() > 0 && no_at(x),
        (None, Some(y)) => y.len() > 0 && no_at(y),
        (Some(x), Some(y)) => x.len() > 0 && x == y && no_at(x),
    }
}

/// The authority handed to the application: `:authority`, else `host`, else empty.
pub open spec fn request_authority(a: Option<Seq<u8>>, h: Option<Seq<u8>>) -> Seq<u8> {
    match a {
        Some(x) => x,
        None => match h {
            Some(y) => y,
            None => Seq::empty(),
        },
    }
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.2.1
//# If a decompressed field
//# section contains multiple cookie field lines, these MUST be
//# concatenated into a single byte string using the two-byte delimiter
//# of "; " (ASCII 0x3b, 0x20) before being passed into a context other
//# than HTTP/2 or HTTP/3, such as an HTTP/1.1 connection, or a generic
//# HTTP server application.
/// Append `x` to the merged list: a cookie line after the first is joined onto the first with
/// "; ", at the first one's position.
pub open spec fn merge_step(acc: Fields, x: (Seq<u8>, Seq<u8>)) -> Fields {
    if x.0 != lit_cookie() {
        acc.push(x)
    } else {
        match find_name(acc, lit_cookie()) {
            Some(k) if 0 <= k < acc.len() => acc.update(
                k,
                (lit_cookie(), acc[k].1 + lit_semi() + x.1),
            ),
            _ => acc.push(x),
        }
    }
}

/// The regular (non-pseudo) fields in order, cookies merged.
pub open spec fn request_headers(s: Fields) -> Fields
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        let t = request_headers(s.drop_last());
        if is_pseudo(s.last().0) {
            t
        } else {
            merge_step(t, s.last())
        }
    }
}

/// Σ |name| + |value| over the lines.
pub open spec fn fields_bytes(s: Fields) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        fields_bytes(s.drop_last()) + s.last().0.len() + s.last().1.len()
    }
}

/// Σ (|value| + 2) over the cookie lines: `cookie_total` plus the 2 of a delimiter the last line does not need.
pub open spec fn ctotal(s: Fields) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        ctotal(s.drop_last()) + if s.last().0 == lit_cookie() {
            s.last().1.len() + 2
        } else {
            0
        }
    }
}

/// The merged cookie value's length: Σ cookie value lengths + 2·(count − 1), 0 with no cookie line.
pub open spec fn cookie_total(s: Fields) -> nat {
    if ctotal(s) >= 2 {
        (ctotal(s) - 2) as nat
    } else {
        0
    }
}

/// `build_headers`' `out` before the merge: the non-pseudo fields in order, cookie lines after the first dropped.
spec fn skel(s: Fields) -> Fields
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        let t = skel(s.drop_last());
        let x = s.last();
        if is_pseudo(x.0) || (x.0 == lit_cookie() && find_name(t, lit_cookie()) is Some) {
            t
        } else {
            t.push(x)
        }
    }
}

/// The "; "-join of every cookie value, `None` with no cookie line.
spec fn cjoin(s: Fields) -> Option<Seq<u8>>
    decreases s.len(),
{
    if s.len() == 0 {
        None
    } else {
        let j = cjoin(s.drop_last());
        let x = s.last();
        if x.0 == lit_cookie() {
            match j {
                None => Some(x.1),
                Some(v) => Some(v + lit_semi() + x.1),
            }
        } else {
            j
        }
    }
}

/// `skel` with the first cookie's value replaced by the join: `request_headers` in closed form
/// (`lemma_headers_join`).
spec fn joined(s: Fields) -> Fields {
    match (cjoin(s), find_name(skel(s), lit_cookie())) {
        (Some(v), Some(k)) => skel(s).update(k, (lit_cookie(), v)),
        _ => skel(s),
    }
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.3.1
//# All HTTP/3 requests MUST include exactly one value for the :method,
//# :scheme, and :path pseudo-header fields, unless the request is a
//# CONNECT request; see Section 4.4.
//= https://www.rfc-editor.org/rfc/rfc9114#section-4.3.1
//# This pseudo-header field MUST NOT be empty for "http" or "https"
//# URIs; "http" or "https" URIs that do not contain a path component
//# MUST include a value of / (ASCII 0x2f).
//= https://www.rfc-editor.org/rfc/rfc9114#section-4.4
//# *  The :method pseudo-header field is set to "CONNECT"
//# *  The :scheme and :path pseudo-header fields are omitted
//# *  The :authority pseudo-header field contains the host and port to
//# connect to (equivalent to the authority-form of the request-target
//# of CONNECT requests; see Section 7.1 of [HTTP]).
//= https://www.rfc-editor.org/rfc/rfc9114#section-4.4
//# A CONNECT request that does not conform
//# to these restrictions is malformed.
/// Any violation is `Err(H3_MESSAGE_ERROR)`.
pub open spec fn rfc_validate_request(f: Fields) -> Result<SpecRequestHead, u64> {
    if !common_ok(f) {
        Err(H3_MESSAGE_ERROR)
    } else {
        let a = lookup(f, lit_authority());
        match lookup(f, lit_method()) {
            None => Err(H3_MESSAGE_ERROR),
            Some(meth) => if meth == lit_connect() {
                match (lookup(f, lit_scheme()), lookup(f, lit_path()), a) {
                    (None, None, Some(auth)) if authority_form(auth) => Ok(
                        SpecRequestHead::Connect { authority: auth },
                    ),
                    _ => Err(H3_MESSAGE_ERROR),
                }
            } else {
                let h = lookup(f, lit_host());
                match (lookup(f, lit_scheme()), lookup(f, lit_path())) {
                    (Some(scheme), Some(path)) => if meth.len() > 0 && scheme.len() > 0
                        && path.len() > 0 && authority_ok(scheme, a, h) {
                        Ok(
                            SpecRequestHead::Request(
                                SpecRequest {
                                    method: meth,
                                    scheme,
                                    authority: request_authority(a, h),
                                    path,
                                    headers: request_headers(f),
                                },
                            ),
                        )
                    } else {
                        Err(H3_MESSAGE_ERROR)
                    },
                    _ => Err(H3_MESSAGE_ERROR),
                }
            },
        }
    }
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.3
//# Pseudo-header fields MUST NOT appear in trailer sections.
/// TE is connection-specific here: RFC 9114 §4.2 allows it only in a request header.
pub open spec fn rfc_validate_trailers(f: Fields) -> bool {
    forall|i: int|
        0 <= i < f.len() ==> !is_pseudo((#[trigger] f[i]).0) && valid_field_name(f[i].0)
            && valid_field_value(f[i].1) && !conn_specific(f[i].0) && f[i].0 != lit_te()
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.3
//# Pseudo-header fields defined for requests MUST NOT appear in
//# responses; pseudo-header fields defined for responses MUST NOT
//# appear in requests.
//= https://www.rfc-editor.org/rfc/rfc9114#section-4.2
//# An endpoint MUST NOT generate
//# an HTTP/3 field section containing connection-specific fields; any
//# message containing connection-specific fields MUST be treated as
//# malformed.
/// A response we may encode. `:status` is added by the encoder, so no header may be a
/// pseudo-header, and TE is connection-specific outside a request header (RFC 9114 §4.2).
/// Name and value lengths are `encode_field_section`'s precondition.
pub open spec fn resp_header_ok(h: (Seq<u8>, Seq<u8>)) -> bool {
    valid_field_name(h.0) && !is_pseudo(h.0) && valid_field_value(h.1) && !conn_specific(h.0)
        && h.0 != lit_te() && h.0.len() <= PREFIX_INT_MAX && h.1.len() <= PREFIX_INT_MAX
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.1.2
//# A request or response that is defined as having content when it
//# contains a Content-Length header field (Section 8.6 of [HTTP]) is
//# malformed if the value of the Content-Length header field does not
//# equal the sum of the DATA frame lengths received.
// RFC 9110 §8.6: "A server MUST NOT send a Content-Length header field in any response with
// a status code of 1xx (Informational) or 204 (No Content)." A response to HEAD (§9.3.2) and a
// 304 (§15.4.5) may carry the content-length a GET / 200 would have had; its syntax
// (`1*DIGIT`) still binds (§2.2).
/// A `content-length` header, if that is what `h` is: none on a 204; a valid value always;
/// equal to `body_len` except on a HEAD response or a 304.
pub open spec fn resp_cl_ok(h: (Seq<u8>, Seq<u8>), body_len: int, status: u16, head: bool) -> bool {
    h.0 == lit_content_length() ==> status != 204 && cl_valid(h.1) && (head || status == 304
        || digits_val(h.1) == body_len)
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.1
//# A response MAY consist of multiple messages when and only when one or
//# more interim responses (1xx; see Section 15.2 of [HTTP]) precede a
//# final response to the same request.
/// A final response we may send (`head`: it answers a HEAD request): status 200-599 (an
/// interim 1xx is never the whole response; HTTP/3 has no 101, RFC 9114 §4.5), valid headers,
/// content-length as `resp_cl_ok` allows, and no content for HEAD, 204, 205 or 304 (RFC 9110
/// §9.3.2, §15.3.5, §15.3.6, §15.4.5).
pub open spec fn valid_response(r: SpecResponse, head: bool) -> bool {
    &&& 200 <= r.status <= 599
    &&& forall|i: int|
        0 <= i < r.headers.len() ==> resp_header_ok(#[trigger] r.headers[i]) && resp_cl_ok(
            r.headers[i],
            r.body.len() as int,
            r.status,
            head,
        )
    &&& (head || r.status == 204 || r.status == 205 || r.status == 304) ==> r.body.len() == 0
}

// =============================================================================
// Exec twins
// =============================================================================

fn find_first(fields: &[FieldLine], lit: &[u8]) -> (r: Option<usize>)
    ensures
        match r {
            Some(k) => k < fields.len() && find_name(fields_view(fields@), lit@) == Some(k as int),
            None => find_name(fields_view(fields@), lit@) == None::<int>,
        },
{
    let mut i = 0;
    let mut r: Option<usize> = None;
    while i < fields.len()
        invariant
            i <= fields.len(),
            match r {
                Some(k) => k < i && find_name(fields_view(fields@).take(i as int), lit@) == Some(
                    k as int,
                ),
                None => find_name(fields_view(fields@).take(i as int), lit@) == None::<int>,
            },
        decreases fields.len() - i,
    {
        proof {
            let t = fields_view(fields@).take(i as int + 1);
            assert(t.drop_last() =~= fields_view(fields@).take(i as int));
            assert(t.last() == fields@[i as int]@);
        }
        if r.is_none() && eq_bytes(&fields[i].name, lit) {
            r = Some(i);
        }
        i += 1;
    }
    assert(fields_view(fields@).take(fields.len() as int) =~= fields_view(fields@));
    r
}

fn count_x(fields: &[FieldLine], lit: &[u8]) -> (c: usize)
    ensures
        c == count_name(fields_view(fields@), lit@),
{
    let mut i = 0;
    let mut c: usize = 0;
    while i < fields.len()
        invariant
            i <= fields.len(),
            c <= i,
            c == count_name(fields_view(fields@).take(i as int), lit@),
        decreases fields.len() - i,
    {
        proof {
            let t = fields_view(fields@).take(i as int + 1);
            assert(t.drop_last() =~= fields_view(fields@).take(i as int));
            assert(t.last() == fields@[i as int]@);
        }
        if eq_bytes(&fields[i].name, lit) {
            c += 1;
        }
        i += 1;
    }
    assert(fields_view(fields@).take(fields.len() as int) =~= fields_view(fields@));
    c
}

fn is_pseudo_x(n: &[u8]) -> (r: bool)
    ensures
        r == is_pseudo(n@),
{
    n.len() > 0 && n[0] == 58
}

fn is_request_pseudo_x(n: &[u8]) -> (r: bool)
    ensures
        r == request_pseudo(n@),
{
    eq_bytes(n, &x_method()) || eq_bytes(n, &x_scheme()) || eq_bytes(n, &x_authority())
        || eq_bytes(n, &x_path())
}

fn is_conn_specific_x(n: &[u8]) -> (r: bool)
    ensures
        r == conn_specific(n@),
{
    eq_bytes(n, &x_connection()) || eq_bytes(n, &x_keep_alive()) || eq_bytes(
        n,
        &x_proxy_connection(),
    ) || eq_bytes(n, &x_transfer_encoding()) || eq_bytes(n, &x_upgrade())
}

fn syntax_ok_x(fields: &[FieldLine]) -> (r: bool)
    ensures
        r == fields_syntax_ok(fields_view(fields@)),
{
    let ghost fv = fields_view(fields@);
    let mut i = 0;
    while i < fields.len()
        invariant
            i <= fields.len(),
            fv == fields_view(fields@),
            forall|k: int|
                0 <= k < i ==> (request_pseudo((#[trigger] fv[k]).0) || valid_field_name(fv[k].0))
                    && valid_field_value(fv[k].1),
        decreases fields.len() - i,
    {
        let f = &fields[i];
        proof {
            assert(fv[i as int] == fields@[i as int]@);
        }
        if !((is_request_pseudo_x(&f.name) || field_name_ok(&f.name)) && field_value_ok(&f.value)) {
            return false;
        }
        i += 1;
    }
    true
}

fn pseudo_first_x(fields: &[FieldLine]) -> (r: bool)
    ensures
        r == pseudo_first(fields_view(fields@)),
{
    let ghost fv = fields_view(fields@);
    let mut seen = false;
    let mut i = 0;
    while i < fields.len()
        invariant
            i <= fields.len(),
            fv == fields_view(fields@),
            seen == exists|k: int| 0 <= k < i && !is_pseudo((#[trigger] fv[k]).0),
            forall|a: int, b: int|
                0 <= a < b < i && !is_pseudo((#[trigger] fv[a]).0) ==> !is_pseudo(
                    (#[trigger] fv[b]).0,
                ),
        decreases fields.len() - i,
    {
        proof {
            assert(fv[i as int] == fields@[i as int]@);
        }
        let p = is_pseudo_x(&fields[i].name);
        if p && seen {
            proof {
                let a = choose|k: int| 0 <= k < i && !is_pseudo((#[trigger] fv[k]).0);
                assert(!pseudo_first(fv)) by {
                    if pseudo_first(fv) {
                        assert(0 <= a < i as int && !is_pseudo(fv[a].0));
                    }
                }
            }
            return false;
        }
        if !p {
            seen = true;
        }
        i += 1;
    }
    true
}

fn pseudo_once_x(fields: &[FieldLine]) -> (r: bool)
    ensures
        r == pseudo_once(fields_view(fields@)),
{
    count_x(fields, &x_method()) <= 1 && count_x(fields, &x_scheme()) <= 1 && count_x(
        fields,
        &x_authority(),
    ) <= 1 && count_x(fields, &x_path()) <= 1 && count_x(fields, &x_host()) <= 1
}

fn no_conn_x(fields: &[FieldLine]) -> (r: bool)
    ensures
        r == no_conn_fields(fields_view(fields@)),
{
    let ghost fv = fields_view(fields@);
    let mut i = 0;
    while i < fields.len()
        invariant
            i <= fields.len(),
            fv == fields_view(fields@),
            forall|k: int|
                0 <= k < i ==> !conn_specific((#[trigger] fv[k]).0) && (fv[k].0 == lit_te()
                    ==> fv[k].1 == lit_trailers()),
        decreases fields.len() - i,
    {
        let f = &fields[i];
        proof {
            assert(fv[i as int] == fields@[i as int]@);
        }
        if is_conn_specific_x(&f.name) || (eq_bytes(&f.name, &x_te()) && !eq_bytes(
            &f.value,
            &x_trailers(),
        )) {
            return false;
        }
        i += 1;
    }
    true
}

proof fn lemma_digits_nonneg(s: Seq<u8>)
    ensures
        digits_val(s) >= 0,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_digits_nonneg(s.drop_last());
    }
}

proof fn lemma_digits_mono(s: Seq<u8>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
    ensures
        digits_val(s.take(i)) <= digits_val(s.take(j)),
    decreases j - i,
{
    if i < j {
        lemma_digits_mono(s, i, j - 1);
        lemma_digits_nonneg(s.take(j - 1));
        assert(s.take(j).drop_last() =~= s.take(j - 1));
    }
}

/// The value of a `Content-Length` field value; `None` when it is not 1*DIGIT or overflows `u64`.
fn parse_cl(v: &[u8]) -> (r: Option<u64>)
    ensures
        match r {
            Some(x) => cl_valid(v@) && x as int == digits_val(v@),
            None => !cl_valid(v@),
        },
{
    let mut acc: u64 = 0;
    let mut i = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            forall|k: int| 0 <= k < i ==> 48 <= #[trigger] v@[k] && v@[k] <= 57,
            acc as int == digits_val(v@.take(i as int)),
        decreases v.len() - i,
    {
        let b = v[i];
        if b < 48 || b > 57 {
            return None;
        }
        let d = (b - 48) as u64;
        proof {
            assert(v@.take(i as int + 1).drop_last() =~= v@.take(i as int));
        }
        if acc > (u64::MAX - d) / 10 {
            proof {
                assert(acc as int * 10 + d as int >= 0x1_0000_0000_0000_0000);
                lemma_digits_mono(v@, i as int + 1, v@.len() as int);
                assert(v@.take(v@.len() as int) =~= v@);
            }
            return None;
        }
        acc = acc * 10 + d;
        i += 1;
    }
    assert(v@.take(v.len() as int) =~= v@);
    if v.len() == 0 {
        None
    } else {
        Some(acc)
    }
}

fn cl_ok_x(fields: &[FieldLine]) -> (r: bool)
    ensures
        r == cl_ok(fields_view(fields@)),
{
    let ghost fv = fields_view(fields@);
    let first = find_first(fields, &x_content_length());
    proof {
        lemma_find_name(fv, lit_content_length());
    }
    let k = match first {
        None => return true,
        Some(k) => k,
    };
    proof {
        assert(fv[k as int] == fields@[k as int]@);
    }
    let mut i = 0;
    while i < fields.len()
        invariant
            i <= fields.len(),
            k < fields.len(),
            fv == fields_view(fields@),
            find_name(fv, lit_content_length()) == Some(k as int),
            lookup(fv, lit_content_length()) == Some(fv[k as int].1),
            forall|j: int|
                0 <= j < i && (#[trigger] fv[j]).0 == lit_content_length() ==> cl_valid(fv[j].1)
                    && fv[j].1 == fv[k as int].1,
        decreases fields.len() - i,
    {
        let f = &fields[i];
        proof {
            assert(fv[i as int] == fields@[i as int]@);
        }
        if eq_bytes(&f.name, &x_content_length()) {
            let ok = match parse_cl(&f.value) {
                Some(_) => eq_bytes(&f.value, &fields[k].value),
                None => false,
            };
            if !ok {
                return false;
            }
        }
        i += 1;
    }
    true
}

fn common_ok_x(fields: &[FieldLine]) -> (r: bool)
    ensures
        r == common_ok(fields_view(fields@)),
{
    syntax_ok_x(fields) && pseudo_first_x(fields) && pseudo_once_x(fields) && no_conn_x(fields)
        && cl_ok_x(fields)
}

spec fn opt_view(o: Option<&[u8]>) -> Option<Seq<u8>> {
    match o {
        Some(x) => Some(x@),
        None => None,
    }
}

fn value_at(fields: &[FieldLine], i: Option<usize>) -> (r: Option<&[u8]>)
    requires
        match i {
            Some(k) => k < fields.len(),
            None => true,
        },
    ensures
        opt_view(r) == match i {
            Some(k) => Some(fields@[k as int].value@),
            None => None::<Seq<u8>>,
        },
{
    match i {
        Some(k) => Some(fields[k].value.as_slice()),
        None => None,
    }
}

fn eq_ci_x(s: &[u8], lit: &[u8]) -> (r: bool)
    ensures
        r == eq_ci(s@, lit@),
{
    if s.len() != lit.len() {
        return false;
    }
    let mut i = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            s@.len() == lit@.len(),
            forall|k: int|
                0 <= k < i ==> (if 65 <= #[trigger] s@[k] && s@[k] <= 90 {
                    (s@[k] + 32) as u8
                } else {
                    s@[k]
                }) == lit@[k],
        decreases s.len() - i,
    {
        let c = if 65 <= s[i] && s[i] <= 90 {
            s[i] + 32
        } else {
            s[i]
        };
        if c != lit[i] {
            return false;
        }
        i += 1;
    }
    true
}

/// A scheme we serve: "http" or "https", case-insensitively (RFC 3986 §3.1).
pub open spec fn http_scheme(s: Seq<u8>) -> bool {
    eq_ci(s, lit_http()) || eq_ci(s, lit_https())
}

pub fn is_http_scheme(s: &[u8]) -> (r: bool)
    ensures
        r == http_scheme(s@),
{
    eq_ci_x(s, &x_http()) || eq_ci_x(s, &x_https())
}

fn no_at_x(s: &[u8]) -> (r: bool)
    ensures
        r == no_at(s@),
{
    let mut i = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            forall|k: int| 0 <= k < i ==> (#[trigger] s@[k]) != 64u8,
        decreases s.len() - i,
    {
        if s[i] == 64 {
            return false;
        }
        i += 1;
    }
    true
}

proof fn lemma_trailing_digits(s: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
        forall|k: int| i <= k < s.len() ==> is_digit(#[trigger] s[k]),
        i == 0 || !is_digit(s[i - 1]),
    ensures
        trailing_digits(s) == s.len() - i,
    decreases s.len(),
{
    if s.len() > i {
        assert forall|k: int| i <= k < s.drop_last().len() implies is_digit(
            #[trigger] s.drop_last()[k],
        ) by {
            assert(s.drop_last()[k] == s[k]);
        }
        if i > 0 {
            assert(s.drop_last()[i - 1] == s[i - 1]);
        }
        lemma_trailing_digits(s.drop_last(), i);
    }
}

fn authority_form_x(a: &[u8]) -> (r: bool)
    ensures
        r == authority_form(a@),
{
    let mut i = a.len();
    while i > 0 && 48 <= a[i - 1] && a[i - 1] <= 57
        invariant
            i <= a.len(),
            forall|k: int| i <= k < a.len() ==> is_digit(#[trigger] a@[k]),
        decreases i,
    {
        i -= 1;
    }
    proof {
        lemma_trailing_digits(a@, i as int);
    }
    i < a.len() && i >= 2 && a[i - 1] == 58 && no_at_x(a)
}

fn authority_ok_x(scheme: &[u8], a: Option<&[u8]>, h: Option<&[u8]>) -> (r: bool)
    ensures
        r == authority_ok(scheme@, opt_view(a), opt_view(h)),
{
    if !(eq_ci_x(scheme, &x_http()) || eq_ci_x(scheme, &x_https())) {
        return true;
    }
    match (a, h) {
        (None, None) => false,
        (Some(x), None) => x.len() > 0 && no_at_x(x),
        (None, Some(y)) => y.len() > 0 && no_at_x(y),
        (Some(x), Some(y)) => x.len() > 0 && eq_bytes(x, y) && no_at_x(x),
    }
}

fn request_authority_x(a: Option<&[u8]>, h: Option<&[u8]>) -> (r: Vec<u8>)
    ensures
        r@ == request_authority(opt_view(a), opt_view(h)),
{
    match a {
        Some(x) => slice_to_vec(x),
        None => match h {
            Some(y) => slice_to_vec(y),
            None => Vec::new(),
        },
    }
}

/// Names are unchanged by `update`, so the position of the first `name` stays put.
proof fn lemma_find_name_update(s: Fields, k: int, x: (Seq<u8>, Seq<u8>), name: Seq<u8>)
    requires
        0 <= k < s.len(),
        x.0 == s[k].0,
    ensures
        find_name(s.update(k, x), name) == find_name(s, name),
    decreases s.len(),
{
    let u = s.update(k, x);
    if k < s.len() - 1 {
        assert(u.drop_last() =~= s.drop_last().update(k, x));
        lemma_find_name_update(s.drop_last(), k, x, name);
    } else {
        assert(u.drop_last() =~= s.drop_last());
    }
}

/// `fields_bytes` of a line followed by `rest`.
proof fn lemma_fields_bytes_prepend(x: (Seq<u8>, Seq<u8>), rest: Fields)
    ensures
        fields_bytes(seq![x] + rest) == x.0.len() + x.1.len() + fields_bytes(rest),
    decreases rest.len(),
{
    if rest.len() > 0 {
        assert((seq![x] + rest).drop_last() =~= seq![x] + rest.drop_last());
        assert((seq![x] + rest).last() == rest.last());
        lemma_fields_bytes_prepend(x, rest.drop_last());
    } else {
        let e = Seq::<(Seq<u8>, Seq<u8>)>::empty();
        assert((seq![x] + rest).drop_last() =~= e);
        assert((seq![x] + rest).last() == x);
        assert(fields_bytes(e) == 0);
        assert(rest =~= e);
    }
}

/// The lines the bounded decoder accepts fit its budget (RFC 9114 §4.2.2's size, Σ(|name| + |value| + 32)).
proof fn lemma_lines_size(b: Seq<u8>, left: u64)
    ensures
        rfc_field_lines_bounded(b, left) matches Ok(f) ==> fields_bytes(f) + 32 * f.len() <= left,
    decreases b.len(),
{
    if b.len() == 0 {
        assert(fields_bytes(Seq::<(Seq<u8>, Seq<u8>)>::empty()) == 0);
    } else {
        lemma_field_line_consumed(b);
        if let Some((f, c)) = rfc_field_line(b) {
            if field_line_size(f) <= left {
                let l2 = (left - field_line_size(f)) as u64;
                lemma_lines_size(b.skip(c as int), l2);
                if let Ok(rest) = rfc_field_lines_bounded(b.skip(c as int), l2) {
                    lemma_fields_bytes_prepend(f, rest);
                }
            }
        }
    }
}

/// A field section the bounded decoder accepts meets `validate_request`'s size precondition.
pub proof fn lemma_section_size(b: Seq<u8>, budget: u64)
    ensures
        rfc_decode_field_section_bounded(b, budget) matches Ok(f) ==> fields_bytes(f) + 32 * f.len() <= budget,
{
    if let Some(c) = rfc_section_start(b) {
        lemma_lines_size(b.skip(c as int), budget);
    }
}

/// One field line copied into exact buffers: two allocations, one unit per byte.
fn copy_line(f: &FieldLine) -> (r: (FieldLine, Ghost<nat>))
    ensures
        r.0@ == f@,
        r.1@ == f.name@.len() + f.value@.len() + 2,
{
    let mut n = CapVec::new(f.name.len());
    let Ghost(cn) = n.push_slice(f.name.as_slice());
    let mut v = CapVec::new(f.value.len());
    let Ghost(cv) = v.push_slice(f.value.as_slice());
    assert(n@ =~= f.name@);
    assert(v@ =~= f.value@);
    (FieldLine { name: n.into_vec(), value: v.into_vec() }, Ghost(cn + cv + 2))
}

proof fn lemma_cookie_not_pseudo()
    ensures
        !is_pseudo(lit_cookie()),
{
    assert(lit_cookie()[0] == 99u8);
}

/// The first `name` in `s.push(x)`.
proof fn lemma_find_name_push(s: Fields, x: (Seq<u8>, Seq<u8>), name: Seq<u8>)
    ensures
        find_name(s.push(x), name) == match find_name(s, name) {
            Some(k) => Some(k),
            None => if x.0 == name {
                Some(s.len() as int)
            } else {
                None
            },
        },
{
    assert(s.push(x).drop_last() =~= s);
}

/// A prefix is no larger.
proof fn lemma_take_le(s: Fields, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        fields_bytes(s.take(i)) <= fields_bytes(s),
        ctotal(s.take(i)) <= ctotal(s),
    decreases s.len(),
{
    if i < s.len() {
        assert(s.take(i) =~= s.drop_last().take(i));
        lemma_take_le(s.drop_last(), i);
    } else {
        assert(s.take(i) =~= s);
    }
}

/// `ctotal` is at most the field bytes plus 2 per line.
proof fn lemma_ctotal_le(s: Fields)
    ensures
        ctotal(s) <= fields_bytes(s) + 2 * s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_ctotal_le(s.drop_last());
    }
}

/// `skel` has a cookie exactly when there is a cookie line; the join's length is `ctotal - 2`.
proof fn lemma_skel_cookie(s: Fields)
    ensures
        (find_name(skel(s), lit_cookie()) is Some) == (cjoin(s) is Some),
        cjoin(s) is Some ==> cjoin(s)->0.len() + 2 == ctotal(s),
        cjoin(s) is None ==> ctotal(s) == 0,
    decreases s.len(),
{
    if s.len() > 0 {
        let t = s.drop_last();
        let x = s.last();
        lemma_skel_cookie(t);
        lemma_cookie_not_pseudo();
        if !is_pseudo(x.0) && !(x.0 == lit_cookie() && find_name(skel(t), lit_cookie()) is Some) {
            lemma_find_name_push(skel(t), x, lit_cookie());
        }
    }
}

/// D5: `request_headers` in closed form, its cookie (if any) where `skel`'s first cookie is.
proof fn lemma_headers_join(s: Fields)
    ensures
        request_headers(s) == joined(s),
        find_name(request_headers(s), lit_cookie()) == find_name(skel(s), lit_cookie()),
    decreases s.len(),
{
    if s.len() > 0 {
        let t = s.drop_last();
        let x = s.last();
        lemma_headers_join(t);
        lemma_skel_cookie(t);
        lemma_skel_cookie(s);
        lemma_cookie_not_pseudo();
        let st = skel(t);
        lemma_find_name(st, lit_cookie());
        if is_pseudo(x.0) {
        } else if x.0 != lit_cookie() {
            // skel(s) = st.push(x): the first cookie keeps its index, and an update commutes with the push.
            assert(skel(s) == st.push(x));
            assert(skel(s).drop_last() =~= st);
            match (cjoin(t), find_name(st, lit_cookie())) {
                (Some(v), Some(k)) => {
                    let u = st.update(k, (lit_cookie(), v));
                    lemma_find_name_update(st, k, (lit_cookie(), v), lit_cookie());
                    assert(u.push(x).drop_last() =~= u);
                    assert(u.push(x) =~= st.push(x).update(k, (lit_cookie(), v)));
                },
                _ => {
                    assert(st.push(x).drop_last() =~= st);
                },
            }
        } else {
            match (cjoin(t), find_name(st, lit_cookie())) {
                (Some(v), Some(k)) => {
                    // A later cookie: merge_step updates the first one in place.
                    let u = st.update(k, (lit_cookie(), v));
                    lemma_find_name_update(st, k, (lit_cookie(), v), lit_cookie());
                    assert(skel(s) == st);
                    assert(u.update(k, (lit_cookie(), u[k].1 + lit_semi() + x.1)) =~= st.update(
                        k,
                        (lit_cookie(), v + lit_semi() + x.1),
                    ));
                },
                _ => {
                    // The first cookie: pushed, and the join is its own value.
                    assert(skel(s) == st.push(x));
                    assert(skel(s).drop_last() =~= st);
                    assert(find_name(skel(s), lit_cookie()) == Some(st.len() as int));
                    assert(skel(s).update(st.len() as int, (lit_cookie(), x.1)) =~= skel(s));
                },
            }
        }
        // The join's update keeps the cookie's name, so its position.
        lemma_find_name(skel(s), lit_cookie());
        match (cjoin(s), find_name(skel(s), lit_cookie())) {
            (Some(v), Some(k)) => lemma_find_name_update(skel(s), k, (lit_cookie(), v), lit_cookie()),
            _ => {},
        }
    }
}

/// One step of `build_headers`' passes over `s.take(i + 1)`: field `i` against the closed form over `s.take(i)`.
proof fn lemma_join_step(s: Fields, i: int)
    requires
        0 <= i < s.len(),
    ensures
        ({
            let (p, q, x) = (s.take(i), s.take(i + 1), s[i]);
            &&& fields_bytes(q) == fields_bytes(p) + x.0.len() + x.1.len()
            &&& ctotal(q) == ctotal(p) + if x.0 == lit_cookie() {
                x.1.len() + 2
            } else {
                0nat
            }
            &&& (find_name(skel(p), lit_cookie()) is Some) == (cjoin(p) is Some)
            &&& cjoin(p) is Some ==> cjoin(p)->0.len() + 2 == ctotal(p)
            &&& cjoin(p) is None ==> ctotal(p) == 0
            &&& is_pseudo(x.0) ==> skel(q) == skel(p) && cjoin(q) == cjoin(p)
            &&& !is_pseudo(x.0) && x.0 != lit_cookie() ==> skel(q) == skel(p).push(x) && cjoin(q) == cjoin(p)
                && find_name(skel(q), lit_cookie()) == find_name(skel(p), lit_cookie())
            &&& x.0 == lit_cookie() && cjoin(p) is None ==> skel(q) == skel(p).push(x) && cjoin(q) == Some(x.1)
                && find_name(skel(q), lit_cookie()) == Some(skel(p).len() as int)
            &&& x.0 == lit_cookie() && cjoin(p) is Some ==> skel(q) == skel(p) && cjoin(q) == Some(
                cjoin(p)->0 + lit_semi() + x.1,
            )
        }),
{
    let (p, q, x) = (s.take(i), s.take(i + 1), s[i]);
    assert(q.drop_last() =~= p);
    assert(q.last() == x);
    lemma_skel_cookie(p);
    lemma_cookie_not_pseudo();
    lemma_find_name_push(skel(p), x, lit_cookie());
}

/// The cost constant of `build_headers`.
spec fn c_bh() -> nat {
    20
}

/// The per-line cost constant of `cookie_scan`.
spec fn c_scan() -> nat {
    8
}

/// Pass 1 of `build_headers`: the merged cookie value's length, one name compare per line.
fn cookie_scan(fields: &[FieldLine]) -> (r: (usize, Ghost<nat>))
    requires
        fields_bytes(fields_view(fields@)) + 2 * fields@.len() <= usize::MAX,
    ensures
        r.0 == cookie_total(fields_view(fields@)),
        r.1@ <= c_scan() * fields@.len() + 1,
{
    let ghost fv = fields_view(fields@);
    let ghost mut work: nat = 1;
    proof {
        lemma_ctotal_le(fv);
    }
    let ck = x_cookie();
    let mut t: usize = 0;
    let mut i = 0;
    while i < fields.len()
        invariant
            i <= fields.len(),
            fv == fields_view(fields@),
            ck@ == lit_cookie(),
            ctotal(fv) <= usize::MAX,
            t == ctotal(fv.take(i as int)),
            work <= c_scan() * i + 1,
        decreases fields.len() - i,
    {
        proof {
            lemma_join_step(fv, i as int);
            lemma_take_le(fv, i as int + 1);
            assert(fv[i as int] == fields@[i as int]@);
        }
        let (c, Ghost(ce)) = eq_bytes_w(fields[i].name.as_slice(), &ck);
        if c {
            t = t + fields[i].value.len() + 2;
        }
        i += 1;
        proof {
            work = work + 1 + ce;
        }
    }
    assert(fv.take(fields.len() as int) =~= fv);
    let r = if t >= 2 {
        t - 2
    } else {
        0
    };
    (r, Ghost(work))
}

/// Regular fields in order, with cookie lines merged. Pass 1 sizes the merged value; pass 2 copies each other field
/// into exact buffers and pushes every cookie value, "; "-joined, into one merged buffer of exactly that size, whose
/// line takes the first cookie's slot at the end.
fn build_headers(fields: &[FieldLine]) -> (r: (Vec<FieldLine>, Ghost<nat>))
    requires
        fields_bytes(fields_view(fields@)) + 2 * fields@.len() <= usize::MAX,
    ensures
        fields_view(r.0@) == request_headers(fields_view(fields@)),
        r.1@ <= c_bh() * (fields_bytes(fields_view(fields@)) + fields@.len() + 1),
{
    let ghost fv = fields_view(fields@);
    let (tot, Ghost(w1)) = cookie_scan(fields);
    let mut out: CapVec<FieldLine> = CapVec::new(fields.len());
    let mut merged: CapVec<u8> = CapVec::new(tot);
    let ghost mut work: nat = w1 + 2;
    let ck = x_cookie();
    let semi = x_semi();
    let mut first: Option<usize> = None;
    let mut i = 0;
    while i < fields.len()
        invariant
            i <= fields.len(),
            fv == fields_view(fields@),
            ck@ == lit_cookie(),
            semi@ == lit_semi(),
            tot == cookie_total(fv),
            out.wf(),
            out.cap() == fields.len(),
            merged.wf(),
            merged.cap() == tot,
            out@.len() <= i,
            out@.len() == skel(fv.take(i as int)).len(),
            first is None ==> cjoin(fv.take(i as int)) is None && merged@ == Seq::<u8>::empty(),
            first is None ==> forall|j: int|
                0 <= j < out@.len() ==> (#[trigger] out@[j])@ == skel(fv.take(i as int))[j],
            first matches Some(k) ==> k < out@.len() && find_name(skel(fv.take(i as int)), lit_cookie()) == Some(
                k as int,
            ) && cjoin(fv.take(i as int)) == Some(merged@),
            first matches Some(k) ==> forall|j: int|
                0 <= j < out@.len() && j != k ==> (#[trigger] out@[j])@ == skel(fv.take(i as int))[j],
            work <= w1 + 2 + 12 * i + fields_bytes(fv.take(i as int)),
        decreases fields.len() - i,
    {
        let f = &fields[i];
        let ghost p = fv.take(i as int);
        let ghost q = fv.take(i as int + 1);
        proof {
            lemma_join_step(fv, i as int);
            lemma_take_le(fv, i as int + 1);
            assert(fv[i as int] == f@);
        }
        let (c, Ghost(ce)) = eq_bytes_w(f.name.as_slice(), &ck);
        if is_pseudo_x(&f.name) {
            proof {
                work = work + 1 + ce;
            }
        } else if !c {
            let (l, Ghost(cl)) = copy_line(f);
            out.push(l);
            proof {
                work = work + 1 + ce + cl;
            }
        } else {
            let ghost mut cs: nat = 0;
            let ghost mut fst = false;
            match first {
                None => {
                    out.push(FieldLine { name: Vec::new(), value: Vec::new() });
                    first = Some(out.len() - 1);
                    proof {
                        fst = true;
                    }
                },
                Some(_) => {
                    let Ghost(c2) = merged.push_slice(&semi);
                    proof {
                        cs = c2;
                    }
                },
            }
            let Ghost(cv) = merged.push_slice(f.value.as_slice());
            proof {
                work = work + 1 + ce + cs + cv;
                if fst {
                    assert(merged@ =~= f.value@);
                }
            }
        }
        i += 1;
    }
    proof {
        assert(fv.take(fields.len() as int) =~= fv);
        lemma_skel_cookie(fv);
        lemma_headers_join(fv);
    }
    match first {
        Some(k) => {
            // Exactly full: pass 1's T is the join's length.
            assert(merged@.len() == tot);
            let mut nm = CapVec::new(6);
            let Ghost(cn) = nm.push_slice(&ck);
            assert(nm@ =~= lit_cookie());
            let ghost old_out = out@;
            out.set(k, FieldLine { name: nm.into_vec(), value: merged.into_vec() });
            proof {
                work = work + 1 + cn;
                assert(fields_view(out@) =~= skel(fv).update(k as int, (lit_cookie(), cjoin(fv)->0)));
            }
        },
        None => {
            proof {
                assert(fields_view(out@) =~= skel(fv));
            }
        },
    }
    (out.into_vec(), Ghost(work))
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.3
//# Endpoints MUST treat a request or response that contains
//# undefined or invalid pseudo-header fields as malformed.
/// Validate a decoded request header section. `Request.headers` holds the regular fields with
/// cookie lines merged.
pub fn validate_request(fields: &[FieldLine]) -> (r: Result<RequestHead, u64>)
    requires
        fields_bytes(fields_view(fields@)) + 32 * fields@.len() <= MAX_FIELD_SECTION_SIZE,
    ensures
        match r {
            Ok(h) => rfc_validate_request(fields_view(fields@)) == Ok::<SpecRequestHead, u64>(h@),
            Err(c) => rfc_validate_request(fields_view(fields@)) == Err::<SpecRequestHead, u64>(c),
        },
{
    let ghost fv = fields_view(fields@);
    if !common_ok_x(fields) {
        return Err(H3_MESSAGE_ERROR);
    }
    let mi = find_first(fields, &x_method());
    let si = find_first(fields, &x_scheme());
    let ai = find_first(fields, &x_authority());
    let pi = find_first(fields, &x_path());
    let hi = find_first(fields, &x_host());
    let m = match mi {
        Some(m) => m,
        None => return Err(H3_MESSAGE_ERROR),
    };
    let av = value_at(fields, ai);
    proof {
        assert(forall|k: int| 0 <= k < fields.len() ==> fv[k] == (#[trigger] fields@[k])@);
    }
    if eq_bytes(&fields[m].value, &x_connect()) {
        if si.is_none() && pi.is_none() {
            match av {
                Some(auth) if authority_form_x(auth) => {
                    return Ok(RequestHead::Connect { authority: slice_to_vec(auth) });
                },
                _ => return Err(H3_MESSAGE_ERROR),
            }
        }
        return Err(H3_MESSAGE_ERROR);
    }
    match (si, pi) {
        (Some(s), Some(p)) => {
            let hv = value_at(fields, hi);
            let scheme = fields[s].value.as_slice();
            if fields[m].value.len() > 0 && scheme.len() > 0 && fields[p].value.len() > 0
                && authority_ok_x(scheme, av, hv) {
                // Task 6 charges `wb` once `validate_request` returns its cost.
                let (headers, Ghost(wb)) = build_headers(fields);
                Ok(
                    RequestHead::Request(
                        Request {
                            method: slice_to_vec(&fields[m].value),
                            scheme: slice_to_vec(scheme),
                            authority: request_authority_x(av, hv),
                            path: slice_to_vec(&fields[p].value),
                            headers,
                        },
                    ),
                )
            } else {
                Err(H3_MESSAGE_ERROR)
            }
        },
        _ => Err(H3_MESSAGE_ERROR),
    }
}

pub fn validate_trailers(fields: &[FieldLine]) -> (r: bool)
    ensures
        r == rfc_validate_trailers(fields_view(fields@)),
{
    let ghost fv = fields_view(fields@);
    let mut i = 0;
    while i < fields.len()
        invariant
            i <= fields.len(),
            fv == fields_view(fields@),
            forall|k: int|
                0 <= k < i ==> !is_pseudo((#[trigger] fv[k]).0) && valid_field_name(fv[k].0)
                    && valid_field_value(fv[k].1) && !conn_specific(fv[k].0) && fv[k].0 != lit_te(),
        decreases fields.len() - i,
    {
        let f = &fields[i];
        proof {
            assert(fv[i as int] == fields@[i as int]@);
        }
        if is_pseudo_x(&f.name) || !field_name_ok(&f.name) || !field_value_ok(&f.value)
            || is_conn_specific_x(&f.name) || eq_bytes(&f.name, &x_te()) {
            return false;
        }
        i += 1;
    }
    true
}

/// The first `content-length` value, when present and valid (`validate_request` rejects the
/// others).
pub fn content_length(fields: &[FieldLine]) -> (r: Option<u64>)
    ensures
        r == rfc_content_length(fields_view(fields@)),
{
    match find_first(fields, &x_content_length()) {
        Some(k) => {
            proof {
                assert(fields_view(fields@)[k as int] == fields@[k as int]@);
            }
            match parse_cl(&fields[k].value) {
                Some(x) => Some(x),
                None => None,
            }
        },
        None => None,
    }
}

fn resp_header_ok_x(f: &FieldLine) -> (r: bool)
    ensures
        r == resp_header_ok(f@),
{
    field_name_ok(&f.name) && !is_pseudo_x(&f.name) && field_value_ok(&f.value)
        && !is_conn_specific_x(&f.name) && !eq_bytes(&f.name, &x_te())
        && f.name.len() as u64 <= PREFIX_INT_MAX
        && f.value.len() as u64 <= PREFIX_INT_MAX
}

fn resp_cl_ok_x(f: &FieldLine, body_len: usize, status: u16, head: bool) -> (r: bool)
    ensures
        r == resp_cl_ok(f@, body_len as int, status, head),
{
    if !eq_bytes(&f.name, &x_content_length()) {
        return true;
    }
    if status == 204 {
        return false;
    }
    match parse_cl(&f.value) {
        Some(x) => head || status == 304 || x == body_len as u64,
        None => false,
    }
}

pub fn check_response(r: &Response, head: bool) -> (ok: bool)
    ensures
        ok == valid_response(r@, head),
{
    if r.status < 200 || r.status > 599 {
        return false;
    }
    if (head || r.status == 204 || r.status == 205 || r.status == 304) && r.body.len() > 0 {
        return false;
    }
    let mut i = 0;
    while i < r.headers.len()
        invariant
            i <= r.headers.len(),
            forall|k: int|
                0 <= k < i ==> resp_header_ok(#[trigger] r.headers@[k]@) && resp_cl_ok(
                    r.headers@[k]@,
                    r.body@.len() as int,
                    r.status,
                    head,
                ),
        decreases r.headers.len() - i,
    {
        if !resp_header_ok_x(&r.headers[i]) || !resp_cl_ok_x(&r.headers[i], r.body.len(), r.status, head) {
            proof {
                assert(r@.headers[i as int] == r.headers@[i as int]@);
                assert(!valid_response(r@, head)) by {
                    if valid_response(r@, head) {
                        assert(resp_header_ok(r@.headers[i as int]));
                        assert(resp_cl_ok(r@.headers[i as int], r@.body.len() as int, r@.status, head));
                    }
                }
            }
            return false;
        }
        i += 1;
    }
    proof {
        assert forall|k: int| 0 <= k < r@.headers.len() implies resp_header_ok(
            #[trigger] r@.headers[k],
        ) && resp_cl_ok(r@.headers[k], r@.body.len() as int, r@.status, head) by {
            assert(r@.headers[k] == r.headers@[k]@);
        }
    }
    true
}

} // verus!
