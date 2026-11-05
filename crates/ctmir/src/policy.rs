//! The manifest's policy, as the translator takes it, and the manifest grammar (`policy_of`, a
//! spec) with its verified parser (`parse_manifests`). Keys and crate names are bytes.
//! `declassify` and `ghost` are the manifest's `declassify <path>` and `ghost <path>` lines
//! (`ghost_unit`: `ghost` is a Verus keyword), the semantics' `CallPolicy`.
//!
//! ```text
//! root <path>                          CT root; must resolve in its crate
//! cost-root <path>                     step-bound root; must resolve in its crate
//! label <path> secret(a,b) public(c)   labels for bodies that can't carry attributes
//! translate-crate <crate>              foreign crate whose bodies may be translated
//! internal-crate <crate>               another crate whose bodies are entered
//! declassify <crate>::ct::declassify   the declassify shim (`CallPolicy::declassify`)
//! ghost <path>                         a call that returns `()` and does nothing (`CallPolicy::ghost_unit`)
//! ```
//!
//! A line is its words (runs of bytes other than ASCII whitespace) up to the first word starting
//! with `#`; a path is its words joined by one space, so it may hold spaces
//! (`std::array::<impl [u8; 16]>::as_slice`). `intr` lines are obsolete (the std behaviour is
//! `ctmir::sem`'s std model) and rejected.
//!
//! Labels (in a `label` line and in `#[cfg_attr(ct_check, ct::secret(..), ct::public(..))]`):
//! only `secret(..)` is enforced, as "this param is secret". A `public(..)` name is a declaration
//! only; the checker accepts a declared-public param whose inferred label is secret. That is sound
//! for constant time (the theorem's argument agreement just covers that slot less), so never read
//! `public(..)` as a checked guarantee that the value is public. The labels the CT theorem uses
//! are the ones the `checked` line prints.
use crate::json::bytes_eq;
#[cfg(verus_keep_ghost)]
use crate::rel::{trim_spec, views};
#[cfg(verus_keep_ghost)]
use crate::sem::CallPolicy;
#[cfg(verus_keep_ghost)]
use crate::text::join;
use crate::text::{join_exec, put};
use vstd::prelude::*;

verus! {

pub struct Policy {
    pub roots: Vec<Vec<u8>>,
    pub cost_roots: Vec<Vec<u8>>,
    /// `label <path> secret(..) public(..)`: the path, the secret names, the public names.
    pub labels: Vec<(Vec<u8>, Vec<Vec<u8>>, Vec<Vec<u8>>)>,
    pub internal_crates: Vec<Vec<u8>>,
    pub translate_crates: Vec<Vec<u8>>,
    pub declassify: Vec<Vec<u8>>,
    pub ghost_unit: Vec<Vec<u8>>,
}

/// `k` is one of `v`'s byte strings.
pub open spec fn has(v: Seq<Vec<u8>>, k: Seq<u8>) -> bool { exists|i: int| 0 <= i < v.len() && (#[trigger] v[i])@ == k }

pub open spec fn set_of(v: Seq<Vec<u8>>) -> Set<Seq<u8>> { v.map_values(|x: Vec<u8>| x@).to_set() }

pub proof fn lemma_set_of(v: Seq<Vec<u8>>, k: Seq<u8>)
    ensures set_of(v).contains(k) == has(v, k),
{
    let w = v.map_values(|x: Vec<u8>| x@);
    w.to_set_ensures();
    if has(v, k) {
        let i = choose|i: int| 0 <= i < v.len() && (#[trigger] v[i])@ == k;
        assert(w[i] == k);
    }
    if w.contains(k) {
        let i = choose|i: int| 0 <= i < w.len() && w[i] == k;
        assert(v[i]@ == k);
    }
}

/// The semantics' view of the policy calls.
pub open spec fn cpol(pol: Policy) -> CallPolicy {
    CallPolicy { declassify: set_of(pol.declassify@), ghost_unit: set_of(pol.ghost_unit@) }
}

pub fn has_exec(v: &Vec<Vec<u8>>, k: &[u8]) -> (r: bool)
    ensures r == has(v@, k@),
{
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v@.len(), forall|j: int| 0 <= j < i ==> (#[trigger] v@[j])@ != k@,
        decreases v.len() - i,
    {
        if bytes_eq(v[i].as_slice(), k) { return true; }
        i += 1;
    }
    false
}

// ------------------------------------------------------------------ the manifest grammar

/// `t` cut at every `c`, from `i` on (a trailing `c` gives a last, empty, piece).
pub open spec fn split_from(t: Seq<u8>, c: u8, i: nat) -> Seq<Seq<u8>>
    decreases t.len() - i,
{
    let k = upto(t, c, i);
    if k >= t.len() || k < i { seq![t.subrange(i as int, t.len() as int)] }
    else { seq![t.subrange(i as int, k as int)] + split_from(t, c, k + 1) }
}

/// The first `c` at or after `i`, or `t.len()`.
pub open spec fn upto(t: Seq<u8>, c: u8, i: nat) -> nat
    decreases t.len() - i,
{
    if i >= t.len() { t.len() } else if t[i as int] == c { i } else { upto(t, c, i + 1) }
}

pub open spec fn split(t: Seq<u8>, c: u8) -> Seq<Seq<u8>> { split_from(t, c, 0) }

/// ASCII whitespace (`\t`, `\n`, vertical tab, form feed, `\r`, space).
pub open spec fn mws(c: u8) -> bool { c == 32 || (9 <= c && c <= 13) }

pub open spec fn skip_ws(l: Seq<u8>, i: nat) -> nat
    decreases l.len() - i,
{
    if i < l.len() && mws(l[i as int]) { skip_ws(l, i + 1) } else { i }
}

pub open spec fn word_end(l: Seq<u8>, i: nat) -> nat
    decreases l.len() - i,
{
    if i < l.len() && !mws(l[i as int]) { word_end(l, i + 1) } else { i }
}

/// The words of `l` from `i` on: its maximal runs of non-whitespace bytes.
pub open spec fn words_from(l: Seq<u8>, i: nat) -> Seq<Seq<u8>>
    decreases l.len() - i,
{
    let a = skip_ws(l, i);
    if a >= l.len() || a < i { seq![] } else {
        let b = word_end(l, a);
        if b <= a || b > l.len() { seq![] } else { seq![l.subrange(a as int, b as int)] + words_from(l, b) }
    }
}

pub open spec fn hashed(w: Seq<u8>) -> bool { w.len() > 0 && w[0] == 35u8 }

/// The first word at or after `i` that starts with `#`, or `ws.len()`.
pub open spec fn hash_at(ws: Seq<Seq<u8>>, i: nat) -> nat
    decreases ws.len() - i,
{
    if i >= ws.len() { ws.len() } else if hashed(ws[i as int]) { i } else { hash_at(ws, i + 1) }
}

/// A line's entry: its words before the comment.
pub open spec fn entry(l: Seq<u8>) -> Seq<Seq<u8>> {
    let ws = words_from(l, 0);
    ws.subrange(0, hash_at(ws, 0) as int)
}

/// The entries of lines `ls` that hold a word.
pub open spec fn ents_of(ls: Seq<Seq<u8>>) -> Seq<Seq<Seq<u8>>>
    decreases ls.len(),
{
    if ls.len() == 0 { seq![] } else {
        ents_of(ls.drop_last()) + if entry(ls.last()).len() > 0 { seq![entry(ls.last())] } else { Seq::<Seq<Seq<u8>>>::empty() }
    }
}

/// Every manifest's entries, in order.
pub open spec fn all_ents(ms: Seq<Seq<u8>>) -> Seq<Seq<Seq<u8>>>
    decreases ms.len(),
{
    if ms.len() == 0 { seq![] } else { all_ents(ms.drop_last()) + ents_of(split(ms.last(), 10u8)) }
}

/// The path of entry `e`: its words after the kind, joined by a space.
pub open spec fn path_of(e: Seq<Seq<u8>>) -> Seq<u8> { join(e.drop_first(), b" "@) }

/// The paths of the entries of kind `kind`, in order.
pub open spec fn paths_of(es: Seq<Seq<Seq<u8>>>, kind: Seq<u8>) -> Seq<Seq<u8>>
    decreases es.len(),
{
    if es.len() == 0 { seq![] } else {
        paths_of(es.drop_last(), kind) + if es.last()[0] == kind { seq![path_of(es.last())] } else { Seq::<Seq<u8>>::empty() }
    }
}

pub open spec fn starts(t: Seq<u8>, p: Seq<u8>) -> bool { p.len() <= t.len() && t.subrange(0, p.len() as int) == p }

pub open spec fn list_tok(t: Seq<u8>) -> bool { starts(t, b"secret("@) || starts(t, b"public("@) }

/// The first word at or after `i` that opens a list, or `ws.len()`.
pub open spec fn list_at(ws: Seq<Seq<u8>>, i: nat) -> nat
    decreases ws.len() - i,
{
    if i >= ws.len() { ws.len() } else if list_tok(ws[i as int]) { i } else { list_at(ws, i + 1) }
}

pub open spec fn name_byte(b: u8) -> bool { (48 <= b && b <= 57) || (65 <= b && b <= 90) || (97 <= b && b <= 122) || b == 95 }

pub open spec fn name_ok(n: Seq<u8>) -> bool { n.len() > 0 && forall|i: int| 0 <= i < n.len() ==> name_byte(#[trigger] n[i]) }

/// The names of a list word `secret(a,b)` / `public()`.
pub open spec fn list_names(t: Seq<u8>) -> Seq<Seq<u8>> {
    let inner = t.subrange(7, t.len() - 1);
    if inner.len() == 0 { seq![] } else { split(inner, 44u8) }
}

pub open spec fn list_ok(t: Seq<u8>) -> bool {
    &&& list_tok(t) && t.len() >= 8 && t[t.len() - 1] == 41u8
    &&& forall|k: int| 0 <= k < list_names(t).len() ==> name_ok(#[trigger] list_names(t)[k])
}

pub open spec fn distinct(ns: Seq<Seq<u8>>) -> bool { forall|i: int, j: int| 0 <= i < j < ns.len() ==> ns[i] != ns[j] }

/// A `label` line's words after the kind: `<path words> [secret(..)] [public(..)]`, each list at
/// most once and at least one present, names alphanumeric or `_`, each name at most once.
pub open spec fn label_spec(rest: Seq<Seq<u8>>) -> Option<(Seq<u8>, Seq<Seq<u8>>, Seq<Seq<u8>>)> {
    let i = list_at(rest, 0);
    let ls = rest.subrange(i as int, rest.len() as int);
    let sec0 = ls.len() > 0 && starts(ls[0], b"secret("@);
    let sec1 = ls.len() > 1 && starts(ls[1], b"secret("@);
    let sec = if sec0 { list_names(ls[0]) } else if sec1 { list_names(ls[1]) } else { seq![] };
    let pb = if ls.len() > 0 && !sec0 { list_names(ls[0]) } else if ls.len() > 1 && !sec1 { list_names(ls[1]) } else { seq![] };
    if i == 0 || ls.len() == 0 || ls.len() > 2 || (ls.len() == 2 && sec0 == sec1)
        || !(forall|k: int| 0 <= k < ls.len() ==> list_ok(#[trigger] ls[k])) || !distinct(sec + pb) { None }
    else { Some((join(rest.subrange(0, i as int), b" "@), sec, pb)) }
}

/// The `label` entries' parses, in order.
pub open spec fn labels_of(es: Seq<Seq<Seq<u8>>>) -> Seq<(Seq<u8>, Seq<Seq<u8>>, Seq<Seq<u8>>)>
    decreases es.len(),
{
    if es.len() == 0 { seq![] } else {
        labels_of(es.drop_last()) + if es.last()[0] == b"label"@ { seq![label_spec(es.last().drop_first())->Some_0] }
            else { Seq::<(Seq<u8>, Seq<Seq<u8>>, Seq<Seq<u8>>)>::empty() }
    }
}

pub open spec fn label_view(l: (Vec<u8>, Vec<Vec<u8>>, Vec<Vec<u8>>)) -> (Seq<u8>, Seq<Seq<u8>>, Seq<Seq<u8>>) { (l.0@, views(l.1@), views(l.2@)) }

/// **The manifest grammar**: `pol` is what manifests `ms` say, in order.
pub open spec fn policy_of(ms: Seq<Seq<u8>>, pol: Policy) -> bool {
    let es = all_ents(ms);
    &&& views(pol.roots@) == paths_of(es, b"root"@)
    &&& views(pol.cost_roots@) == paths_of(es, b"cost-root"@)
    &&& pol.labels@.map_values(|l: (Vec<u8>, Vec<Vec<u8>>, Vec<Vec<u8>>)| label_view(l)) == labels_of(es)
    &&& views(pol.internal_crates@) == paths_of(es, b"internal-crate"@)
    &&& views(pol.translate_crates@) == paths_of(es, b"translate-crate"@)
    &&& views(pol.declassify@) == paths_of(es, b"declassify"@)
    &&& views(pol.ghost_unit@) == paths_of(es, b"ghost"@)
}

// ------------------------------------------------------------------ the parser

proof fn lemma_step(es: Seq<Seq<Seq<u8>>>, k: int)
    requires 0 <= k < es.len(),
    ensures
        forall|kind: Seq<u8>| #[trigger] paths_of(es.subrange(0, k + 1), kind) == paths_of(es.subrange(0, k), kind)
            + if es[k][0] == kind { seq![path_of(es[k])] } else { Seq::<Seq<u8>>::empty() },
        labels_of(es.subrange(0, k + 1)) == labels_of(es.subrange(0, k))
            + if es[k][0] == b"label"@ { seq![label_spec(es[k].drop_first())->Some_0] } else { Seq::<(Seq<u8>, Seq<Seq<u8>>, Seq<Seq<u8>>)>::empty() },
{
    assert(es.subrange(0, k + 1).drop_last() =~= es.subrange(0, k));
}

pub proof fn lemma_views_push(v: Seq<Vec<u8>>, x: Vec<u8>)
    ensures views(v.push(x)) == views(v).push(x@),
{
    assert(views(v.push(x)) =~= views(v).push(x@));
}

pub fn sub(t: &[u8], a: usize, b: usize) -> (r: Vec<u8>)
    requires a <= b <= t@.len(),
    ensures r@ == t@.subrange(a as int, b as int),
{
    let mut v = Vec::new();
    let mut i = a;
    while i < b
        invariant a <= i <= b, b <= t@.len(), v@ == t@.subrange(a as int, i as int),
        decreases b - i,
    {
        v.push(t[i]);
        i += 1;
        proof { assert(v@ =~= t@.subrange(a as int, i as int)); }
    }
    v
}

pub fn split_exec(t: &[u8], c: u8) -> (r: Vec<Vec<u8>>)
    ensures views(r@) == split(t@, c),
{
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut s: usize = 0;
    let mut j: usize = 0;
    while j < t.len()
        invariant s <= j <= t@.len(), views(out@) + split_from(t@, c, s as nat) == split(t@, c),
            upto(t@, c, s as nat) == upto(t@, c, j as nat),
        decreases t.len() - j,
    {
        if t[j] == c {
            let piece = sub(t, s, j);
            let ghost o = out@;
            out.push(piece);
            proof {
                assert(views(out@) =~= views(o).push(piece@));
                assert(split_from(t@, c, s as nat) == seq![piece@] + split_from(t@, c, (j + 1) as nat));
                assert(views(out@) + split_from(t@, c, (j + 1) as nat) =~= views(o) + split_from(t@, c, s as nat));
            }
            s = j + 1;
        }
        j += 1;
    }
    let piece = sub(t, s, t.len());
    let ghost o = out@;
    out.push(piece);
    proof { assert(views(out@) =~= views(o) + split_from(t@, c, s as nat)); }
    out
}

fn is_mws(c: u8) -> (r: bool) ensures r == mws(c) { c == 32 || (9 <= c && c <= 13) }

pub fn words_exec(l: &[u8]) -> (r: Vec<Vec<u8>>)
    ensures views(r@) == words_from(l@, 0),
{
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;
    loop
        invariant i <= l@.len(), views(out@) + words_from(l@, i as nat) == words_from(l@, 0),
        decreases l.len() - i,
    {
        let mut a = i;
        while a < l.len() && is_mws(l[a])
            invariant i <= a <= l@.len(), skip_ws(l@, i as nat) == skip_ws(l@, a as nat),
            decreases l.len() - a,
        {
            a += 1;
        }
        if a >= l.len() { proof { assert(views(out@) =~= views(out@) + words_from(l@, i as nat)); } return out; }
        let mut b = a;
        while b < l.len() && !is_mws(l[b])
            invariant a <= b <= l@.len(), word_end(l@, a as nat) == word_end(l@, b as nat),
            decreases l.len() - b,
        {
            b += 1;
        }
        let w = sub(l, a, b);
        let ghost o = out@;
        out.push(w);
        proof {
            assert(views(out@) =~= views(o).push(w@));
            assert(views(out@) + words_from(l@, b as nat) =~= views(o) + words_from(l@, i as nat));
        }
        i = b;
    }
}

pub fn entry_exec(l: &[u8]) -> (r: Vec<Vec<u8>>)
    ensures views(r@) == entry(l@),
{
    let mut ws = words_exec(l);
    let ghost w0 = views(ws@);
    let mut h: usize = 0;
    while h < ws.len() && !(ws[h].len() > 0 && ws[h][0] == 35u8)
        invariant h <= ws@.len(), views(ws@) == w0, hash_at(w0, 0) == hash_at(w0, h as nat),
        decreases ws.len() - h,
    {
        h += 1;
    }
    ws.truncate(h);
    proof { assert(views(ws@) =~= w0.subrange(0, h as int)); }
    ws
}

pub fn has_bytes(v: &Vec<Vec<u8>>, k: &Vec<u8>) -> (r: bool)
    ensures r == has(v@, k@),
{
    has_exec(v, k.as_slice())
}

/// Entry `e`'s words after the kind.
fn rest_exec(e: &Vec<Vec<u8>>) -> (r: Vec<Vec<u8>>)
    requires e@.len() > 0,
    ensures views(r@) == views(e@).drop_first(),
{
    let mut rest: Vec<Vec<u8>> = Vec::new();
    let mut k: usize = 1;
    while k < e.len()
        invariant 1 <= k <= e@.len(), views(rest@) =~= views(e@).subrange(1, k as int),
        decreases e.len() - k,
    {
        let ghost o = rest@;
        rest.push(crate::text::copy(&e[k]));
        proof { lemma_views_push(o, rest@.last()); assert(rest@ == o.push(rest@.last())); }
        k += 1;
    }
    proof { assert(views(rest@) =~= views(e@).drop_first()); }
    rest
}

fn starts_exec(t: &Vec<u8>, p: &[u8]) -> (r: bool)
    ensures r == starts(t@, p@),
{
    if p.len() > t.len() { return false; }
    let mut i: usize = 0;
    while i < p.len()
        invariant i <= p@.len(), p@.len() <= t@.len(), forall|k: int| 0 <= k < i ==> t@[k] == p@[k],
        decreases p.len() - i,
    {
        if t[i] != p[i] { proof { assert(t@.subrange(0, p@.len() as int)[i as int] != p@[i as int]); } return false; }
        i += 1;
    }
    proof { assert(t@.subrange(0, p@.len() as int) =~= p@); }
    true
}

pub fn starts_pub(t: &Vec<u8>, p: &[u8]) -> (r: bool)
    ensures r == starts(t@, p@),
{
    starts_exec(t, p)
}

fn list_tok_exec(t: &Vec<u8>) -> (r: bool) ensures r == list_tok(t@) { starts_exec(t, b"secret(") || starts_exec(t, b"public(") }

/// A list word's names, if it is well formed.
fn list_exec(t: &Vec<u8>) -> (r: Option<Vec<Vec<u8>>>)
    ensures r matches Some(ns) ==> list_ok(t@) && views(ns@) == list_names(t@),
{
    if !(list_tok_exec(t) && t.len() >= 8 && t[t.len() - 1] == 41u8) { return None; }
    let inner = sub(t.as_slice(), 7, t.len() - 1);
    let ns = if inner.len() == 0 { Vec::new() } else { split_exec(inner.as_slice(), 44u8) };
    proof { assert(views(ns@) =~= list_names(t@)); }
    let mut k: usize = 0;
    while k < ns.len()
        invariant k <= ns@.len(), views(ns@) == list_names(t@), forall|i: int| 0 <= i < k ==> name_ok(#[trigger] list_names(t@)[i]),
        decreases ns.len() - k,
    {
        let n = &ns[k];
        if n.len() == 0 { return None; }
        let mut i: usize = 0;
        while i < n.len()
            invariant i <= n@.len(), forall|q: int| 0 <= q < i ==> name_byte(#[trigger] n@[q]),
            decreases n.len() - i,
        {
            let b = n[i];
            if !((48 <= b && b <= 57) || (65 <= b && b <= 90) || (97 <= b && b <= 122) || b == 95) { return None; }
            i += 1;
        }
        proof { assert(views(ns@)[k as int] == ns@[k as int]@); }
        k += 1;
    }
    Some(ns)
}

fn distinct_exec(ns: &Vec<Vec<u8>>) -> (r: bool)
    ensures r == distinct(views(ns@)),
{
    let ghost v = views(ns@);
    let mut j: usize = 0;
    while j < ns.len()
        invariant j <= ns@.len(), v == views(ns@), forall|a: int, b: int| 0 <= a < b < j ==> v[a] != v[b],
        decreases ns.len() - j,
    {
        let mut i: usize = 0;
        while i < j
            invariant i <= j < ns@.len(), v == views(ns@), forall|a: int| 0 <= a < i ==> v[a] != v[j as int],
                forall|a: int, b: int| 0 <= a < b < j ==> v[a] != v[b],
            decreases j - i,
        {
            if bytes_eq(ns[i].as_slice(), ns[j].as_slice()) { proof { assert(v[i as int] == v[j as int]); } return false; }
            i += 1;
        }
        j += 1;
    }
    true
}

/// A `label` line's words after the kind (`rest`), parsed.
pub fn label_exec(rest: &Vec<Vec<u8>>) -> (r: Option<(Vec<u8>, Vec<Vec<u8>>, Vec<Vec<u8>>)>)
    ensures r matches Some(l) ==> label_spec(views(rest@)) == Some(label_view(l)),
{
    let ghost rv = views(rest@);
    let mut i: usize = 0;
    while i < rest.len() && !list_tok_exec(&rest[i])
        invariant i <= rest@.len(), rv == views(rest@), list_at(rv, 0) == list_at(rv, i as nat),
        decreases rest.len() - i,
    {
        i += 1;
    }
    let n = rest.len() - i;
    if i == 0 || n == 0 || n > 2 { return None; }
    let ghost ls = rv.subrange(i as int, rv.len() as int);
    let a = match list_exec(&rest[i]) { Some(a) => a, None => return None };
    let sec0 = starts_exec(&rest[i], b"secret(");
    let (sec, pb) = if n == 2 {
        let b = match list_exec(&rest[i + 1]) { Some(b) => b, None => return None };
        let sec1 = starts_exec(&rest[i + 1], b"secret(");
        if sec0 == sec1 { return None; }
        if sec0 { (a, b) } else { (b, a) }
    } else if sec0 { (a, Vec::new()) } else { (Vec::new(), a) };
    let mut all: Vec<Vec<u8>> = Vec::new();
    let mut k: usize = 0;
    while k < sec.len()
        invariant k <= sec@.len(), views(all@) =~= views(sec@).subrange(0, k as int),
        decreases sec.len() - k,
    {
        let ghost o = all@;
        all.push(crate::text::copy(&sec[k]));
        proof { lemma_views_push(o, all@.last()); assert(all@ == o.push(all@.last())); }
        k += 1;
    }
    let mut k: usize = 0;
    while k < pb.len()
        invariant k <= pb@.len(), views(all@) =~= views(sec@) + views(pb@).subrange(0, k as int),
        decreases pb.len() - k,
    {
        let ghost o = all@;
        all.push(crate::text::copy(&pb[k]));
        proof { lemma_views_push(o, all@.last()); assert(all@ == o.push(all@.last())); }
        k += 1;
    }
    proof {
        assert(views(sec@).subrange(0, sec@.len() as int) =~= views(sec@));
        assert(views(pb@).subrange(0, pb@.len() as int) =~= views(pb@));
    }
    if !distinct_exec(&all) { return None; }
    let mut pw: Vec<Vec<u8>> = Vec::new();
    let mut k: usize = 0;
    while k < i
        invariant k <= i <= rest@.len(), views(pw@) =~= rv.subrange(0, k as int), rv == views(rest@),
        decreases i - k,
    {
        let ghost o = pw@;
        pw.push(crate::text::copy(&rest[k]));
        proof { lemma_views_push(o, pw@.last()); assert(pw@ == o.push(pw@.last())); }
        k += 1;
    }
    let path = join_exec(&pw, b" ");
    proof {
        assert(ls[0] == rv[i as int]);
        if n == 2 { assert(ls[1] == rv[i + 1]); }
        assert forall|k: int| 0 <= k < ls.len() implies list_ok(#[trigger] ls[k]) by { if k == 1 { assert(ls[1] == rv[i + 1]); } }
    }
    Some((path, sec, pb))
}

fn kind_is(e: &Vec<Vec<u8>>, k: &[u8]) -> (r: bool)
    requires e@.len() > 0,
    ensures r == (e@[0]@ == k@),
{
    bytes_eq(e[0].as_slice(), k)
}

/// `<c>::ct::declassify` with `c` a plain crate name.
fn declassify_shim(p: &Vec<u8>) -> bool {
    let tail: &[u8] = b"::ct::declassify";
    if p.len() <= tail.len() { return false; }
    let c = p.len() - tail.len();
    let mut i: usize = 0;
    while i < c
        invariant c <= p@.len(),
        decreases c - i,
    {
        let b = p[i];
        if !((48 <= b && b <= 57) || (65 <= b && b <= 90) || (97 <= b && b <= 122) || b == 95) { return false; }
        i += 1;
    }
    let mut k: usize = 0;
    while k < tail.len()
        invariant c + tail@.len() == p@.len(), k <= tail@.len(), p@.len() <= usize::MAX,
        decreases tail.len() - k,
    {
        if p[c + k] != tail[k] { return false; }
        k += 1;
    }
    true
}

fn err_line(mi: usize, n: usize, what: &[u8], line: &Vec<u8>) -> Vec<u8> {
    let mut e = Vec::new();
    put(&mut e, b"manifest ");
    let d = crate::text::dec((if mi < usize::MAX { mi + 1 } else { mi }) as u64);
    put(&mut e, d.as_slice());
    put(&mut e, b":");
    let d = crate::text::dec((if n < usize::MAX { n + 1 } else { n }) as u64);
    put(&mut e, d.as_slice());
    put(&mut e, b": ");
    put(&mut e, what);
    put(&mut e, b": ");
    put(&mut e, line.as_slice());
    e
}

/// The entries of manifests `ms`, each with its manifest and line index and the line.
fn ents_exec(ms: &Vec<Vec<u8>>) -> (r: (Vec<Vec<Vec<u8>>>, Vec<(usize, usize, Vec<u8>)>))
    ensures r.0@.map_values(|e: Vec<Vec<u8>>| views(e@)) == all_ents(views(ms@)), r.1@.len() == r.0@.len(),
        forall|i: int| 0 <= i < r.0@.len() ==> (#[trigger] r.0@[i])@.len() > 0,
{
    let ghost mv = views(ms@);
    let mut out: Vec<Vec<Vec<u8>>> = Vec::new();
    let mut at: Vec<(usize, usize, Vec<u8>)> = Vec::new();
    let mut k: usize = 0;
    while k < ms.len()
        invariant k <= ms@.len(), mv == views(ms@), at@.len() == out@.len(), forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i])@.len() > 0,
            out@.map_values(|e: Vec<Vec<u8>>| views(e@)) == all_ents(mv.subrange(0, k as int)),
        decreases ms.len() - k,
    {
        let ls = split_exec(ms[k].as_slice(), 10u8);
        let ghost base = all_ents(mv.subrange(0, k as int));
        let mut n: usize = 0;
        while n < ls.len()
            invariant n <= ls@.len(), k < ms@.len(), at@.len() == out@.len(), views(ls@) == split(ms@[k as int]@, 10u8),
                forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i])@.len() > 0,
                out@.map_values(|e: Vec<Vec<u8>>| views(e@)) == base + ents_of(views(ls@).subrange(0, n as int)),
            decreases ls.len() - n,
        {
            let e = entry_exec(ls[n].as_slice());
            let ghost o = out@;
            proof { assert(views(ls@).subrange(0, n + 1).drop_last() =~= views(ls@).subrange(0, n as int)); }
            if e.len() > 0 {
                let ghost ev = views(e@);
                out.push(e);
                at.push((k, n, crate::text::copy(&ls[n])));
                proof { assert(out@.map_values(|e: Vec<Vec<u8>>| views(e@)) =~= o.map_values(|e: Vec<Vec<u8>>| views(e@)).push(ev)); }
            }
            n += 1;
            proof { assert(out@.map_values(|e: Vec<Vec<u8>>| views(e@)) =~= base + ents_of(views(ls@).subrange(0, n as int))); }
        }
        proof {
            assert(views(ls@).subrange(0, ls@.len() as int) =~= views(ls@));
            assert(mv.subrange(0, k + 1).drop_last() =~= mv.subrange(0, k as int));
            assert(mv.subrange(0, k + 1).last() == ms@[k as int]@);
        }
        k += 1;
    }
    proof { assert(mv.subrange(0, ms@.len() as int) =~= mv); }
    (out, at)
}

/// **The manifest parser**: manifests `ms`, in order, as one `Policy`. `Err` names the manifest
/// (1-based, in `ms`'s order), the line and what is wrong.
pub fn parse_manifests(ms: &Vec<Vec<u8>>) -> (r: Result<Policy, Vec<u8>>)
    ensures r matches Ok(pol) ==> policy_of(views(ms@), pol),
{
    let (es, at) = ents_exec(ms);
    let ghost ev = es@.map_values(|e: Vec<Vec<u8>>| views(e@));
    let mut pol = Policy {
        roots: Vec::new(), cost_roots: Vec::new(), labels: Vec::new(), internal_crates: Vec::new(),
        translate_crates: Vec::new(), declassify: Vec::new(), ghost_unit: Vec::new(),
    };
    let mut k: usize = 0;
    while k < es.len()
        invariant
            k <= es@.len(), at@.len() == es@.len(), ev == es@.map_values(|e: Vec<Vec<u8>>| views(e@)),
            forall|i: int| 0 <= i < es@.len() ==> (#[trigger] es@[i])@.len() > 0,
            ({ let p = ev.subrange(0, k as int);
               &&& views(pol.roots@) == paths_of(p, b"root"@)
               &&& views(pol.cost_roots@) == paths_of(p, b"cost-root"@)
               &&& pol.labels@.map_values(|l: (Vec<u8>, Vec<Vec<u8>>, Vec<Vec<u8>>)| label_view(l)) == labels_of(p)
               &&& views(pol.internal_crates@) == paths_of(p, b"internal-crate"@)
               &&& views(pol.translate_crates@) == paths_of(p, b"translate-crate"@)
               &&& views(pol.declassify@) == paths_of(p, b"declassify"@)
               &&& views(pol.ghost_unit@) == paths_of(p, b"ghost"@) }),
        decreases es.len() - k,
    {
        let e = &es[k];
        let mi = at[k].0;
        let n = at[k].1;
        let line = &at[k].2;
        let ghost p0 = ev.subrange(0, k as int);
        proof {
            assert(ev.subrange(0, k + 1).drop_last() =~= p0);
            assert(ev.subrange(0, k + 1).last() == views(e@));
            assert(views(e@)[0] == e@[0]@);
        }
        proof {
            lemma_step(ev, k as int);
        }
        // the kinds are distinct words, so at most one holds (the verifier does not see the bytes of a literal)
        let (kr, kc, kl, ki) = (kind_is(e, b"root"), kind_is(e, b"cost-root"), kind_is(e, b"label"), kind_is(e, b"internal-crate"));
        let (kt, kd, kg) = (kind_is(e, b"translate-crate"), kind_is(e, b"declassify"), kind_is(e, b"ghost"));
        let nk: u8 = (if kr { 1u8 } else { 0 }) + (if kc { 1u8 } else { 0 }) + (if kl { 1u8 } else { 0 }) + (if ki { 1u8 } else { 0 })
            + (if kt { 1u8 } else { 0 }) + (if kd { 1u8 } else { 0 }) + (if kg { 1u8 } else { 0 });
        if nk > 1 { return Err(err_line(mi, n, b"unknown kind", line)); }
        let rest = rest_exec(e);
        let path = join_exec(&rest, b" ");
        proof { assert(path@ == path_of(views(e@))); }
        if kr {
            if rest.len() == 0 { return Err(err_line(mi, n, b"malformed root line", line)); }
            if has_bytes(&pol.roots, &path) { return Err(err_line(mi, n, b"duplicate root", line)); }
            let ghost o = pol.roots@;
            pol.roots.push(path);
            proof { lemma_views_push(o, pol.roots@.last()); assert(pol.roots@ == o.push(pol.roots@.last())); }
        } else if kc {
            if rest.len() == 0 { return Err(err_line(mi, n, b"malformed cost-root line", line)); }
            if has_bytes(&pol.cost_roots, &path) { return Err(err_line(mi, n, b"duplicate cost-root", line)); }
            let ghost o = pol.cost_roots@;
            pol.cost_roots.push(path);
            proof { lemma_views_push(o, pol.cost_roots@.last()); assert(pol.cost_roots@ == o.push(pol.cost_roots@.last())); }
        } else if kl {
            let l = match label_exec(&rest) { Some(l) => l, None => return Err(err_line(mi, n, b"malformed label line", line)) };
            let mut i: usize = 0;
            while i < pol.labels.len()
                decreases pol.labels.len() - i,
            {
                if bytes_eq(pol.labels[i].0.as_slice(), l.0.as_slice()) { return Err(err_line(mi, n, b"duplicate label path", line)); }
                i += 1;
            }
            let ghost o = pol.labels@;
            pol.labels.push(l);
            proof {
                assert(pol.labels@.map_values(|l: (Vec<u8>, Vec<Vec<u8>>, Vec<Vec<u8>>)| label_view(l))
                    =~= o.map_values(|l: (Vec<u8>, Vec<Vec<u8>>, Vec<Vec<u8>>)| label_view(l)).push(label_view(pol.labels@.last())));
            }
        } else if ki {
            if rest.len() != 1 { return Err(err_line(mi, n, b"malformed internal-crate line", line)); }
            let ghost o = pol.internal_crates@;
            pol.internal_crates.push(path);
            proof { lemma_views_push(o, pol.internal_crates@.last()); assert(pol.internal_crates@ == o.push(pol.internal_crates@.last())); }
        } else if kt {
            if rest.len() != 1 { return Err(err_line(mi, n, b"malformed translate-crate line", line)); }
            let ghost o = pol.translate_crates@;
            pol.translate_crates.push(path);
            proof { lemma_views_push(o, pol.translate_crates@.last()); assert(pol.translate_crates@ == o.push(pol.translate_crates@.last())); }
        } else if kd {
            if rest.len() == 0 { return Err(err_line(mi, n, b"malformed declassify line", line)); }
            if !declassify_shim(&path) { return Err(err_line(mi, n, b"declassify names only <crate>::ct::declassify", line)); }
            if has_bytes(&pol.declassify, &path) { return Err(err_line(mi, n, b"duplicate declassify path", line)); }
            let ghost o = pol.declassify@;
            pol.declassify.push(path);
            proof { lemma_views_push(o, pol.declassify@.last()); assert(pol.declassify@ == o.push(pol.declassify@.last())); }
        } else if kg {
            if rest.len() == 0 { return Err(err_line(mi, n, b"malformed ghost line", line)); }
            if has_bytes(&pol.ghost_unit, &path) { return Err(err_line(mi, n, b"duplicate ghost path", line)); }
            let ghost o = pol.ghost_unit@;
            pol.ghost_unit.push(path);
            proof { lemma_views_push(o, pol.ghost_unit@.last()); assert(pol.ghost_unit@ == o.push(pol.ghost_unit@.last())); }
        } else if kind_is(e, b"intr") {
            return Err(err_line(mi, n, b"intr lines are obsolete (the std model is ctmir::sem's): use declassify and ghost lines", line));
        } else {
            return Err(err_line(mi, n, b"unknown kind", line));
        }
        k += 1;
    }
    proof { assert(ev.subrange(0, es@.len() as int) =~= ev); }
    Ok(pol)
}

// ------------------------------------------------------------------ labels (`ct::` attributes)

/// The trimmed, nonempty pieces of `ps`.
pub open spec fn names_of(ps: Seq<Seq<u8>>) -> Seq<Seq<u8>>
    decreases ps.len(),
{
    if ps.len() == 0 { seq![] } else {
        let t = trim_spec(ps.last());
        names_of(ps.drop_last()) + if t.len() > 0 { seq![t] } else { Seq::<Seq<u8>>::empty() }
    }
}

/// One attribute `#[ct::<name>]` or `#[ct::<name>(<a>, <b>, ..)]`: whether `<name>` is `secret`
/// (else `public`; any other name is no attribute of ours), and its names (trimmed, empty ones
/// dropped), `None` for a bare attribute.
pub open spec fn attr_spec(a: Seq<u8>) -> Option<(bool, Option<Seq<Seq<u8>>>)> {
    if !(a.len() > 6 && starts(a, b"#[ct::"@) && a[a.len() - 1] == 93u8) { None } else {
        let inner = a.subrange(6, a.len() - 1);
        let p = upto(inner, 40u8, 0);
        let rest = inner.subrange((p + 1) as int, inner.len() as int);
        let bad_list = p < inner.len() && (rest.len() == 0 || rest[rest.len() - 1] != 41u8);
        let name = if p < inner.len() { trim_spec(inner.subrange(0, p as int)) } else { trim_spec(inner) };
        let list = if p < inner.len() { Some(names_of(split(rest.subrange(0, rest.len() - 1), 44u8))) } else { None };
        if bad_list { None }
        else if name == b"secret"@ { Some((true, list)) }
        else if name == b"public"@ { Some((false, list)) }
        else { None }
    }
}

/// The first `j` at or after `i` with `names[j] == n`, or `names.len()`.
pub open spec fn pos_of(names: Seq<Seq<u8>>, n: Seq<u8>, i: nat) -> nat
    decreases names.len() - i,
{
    if i >= names.len() { names.len() } else if names[i as int] == n { i } else { pos_of(names, n, i + 1) }
}

/// The parameters (among the first `n`) that are not ghost, in order.
pub open spec fn non_ghost(ghost: Seq<bool>, n: nat) -> Seq<nat>
    decreases n,
{
    if n == 0 { seq![] } else { non_ghost(ghost, (n - 1) as nat) + if !ghost[n - 1] { seq![(n - 1) as nat] } else { Seq::<nat>::empty() } }
}

/// The parameters list `l` names: each its first parameter of that name, which is not ghost.
pub open spec fn named(l: Seq<Seq<u8>>, names: Seq<Seq<u8>>, ghost: Seq<bool>) -> Option<Seq<nat>>
    decreases l.len(),
{
    if l.len() == 0 { Some(seq![]) } else {
        match named(l.drop_last(), names, ghost) {
            None => None,
            Some(ix) => {
                let j = pos_of(names, l.last(), 0);
                if j >= names.len() || ghost[j as int] { None } else { Some(ix.push(j)) }
            },
        }
    }
}

/// The parameters an attribute labels: a bare `ct::public` all non-ghost ones.
pub open spec fn idx_spec(secret: bool, list: Option<Seq<Seq<u8>>>, names: Seq<Seq<u8>>, ghost: Seq<bool>) -> Option<Seq<nat>> {
    match list {
        None => if secret { None } else { Some(non_ghost(ghost, names.len())) },
        Some(l) => named(l, names, ghost),
    }
}

/// `seen` with each of `ix` set to `v`, if none of them was set (0 = not named, 1 = public,
/// 2 = secret).
pub open spec fn mark(seen: Seq<u8>, ix: Seq<nat>, v: u8) -> Option<Seq<u8>>
    decreases ix.len(),
{
    if ix.len() == 0 { Some(seen) } else {
        match mark(seen, ix.drop_last(), v) {
            None => None,
            Some(s) => if ix.last() >= s.len() || s[ix.last() as int] != 0 { None } else { Some(s.update(ix.last() as int, v)) },
        }
    }
}

/// The labels after the first `n` attributes.
pub open spec fn seen_after(attrs: Seq<Seq<u8>>, names: Seq<Seq<u8>>, ghost: Seq<bool>, n: nat) -> Option<Seq<u8>>
    decreases n,
{
    if n == 0 { Some(Seq::new(names.len(), |j: int| 0u8)) } else {
        match seen_after(attrs, names, ghost, (n - 1) as nat) {
            None => None,
            Some(s) => match attr_spec(attrs[n - 1]) {
                None => None,
                Some((sec, list)) => match idx_spec(sec, list, names, ghost) {
                    None => None,
                    Some(ix) => mark(s, ix, if sec { 2u8 } else { 1u8 }),
                },
            },
        }
    }
}

/// **The labels grammar**: the labels the `ct::` attributes `attrs` declare for parameters
/// `names` (`ghost`: the parameters whose core type is `Unit`, which take no label). `None`: an
/// error; `Some(None)`: no attribute; `Some(Some(d))`: one entry per parameter, `true` = declared
/// secret. Every non-ghost parameter must be named exactly once across `secret(..)`/`public(..)`;
/// a bare `ct::public` names them all. A `label` line is rendered as these attributes.
pub open spec fn decl_spec(attrs: Seq<Seq<u8>>, names: Seq<Seq<u8>>, ghost: Seq<bool>) -> Option<Option<Seq<bool>>> {
    if attrs.len() == 0 { Some(None) } else {
        match seen_after(attrs, names, ghost, attrs.len()) {
            None => None,
            Some(s) => if exists|j: int| 0 <= j < names.len() && !ghost[j] && s[j] == 0 { None }
                else { Some(Some(Seq::new(names.len(), |j: int| s[j] == 2u8))) },
        }
    }
}

fn cat3(a: &[u8], b: &[u8], c: &[u8]) -> Vec<u8> {
    let mut e = Vec::new();
    put(&mut e, a);
    put(&mut e, b);
    put(&mut e, c);
    e
}

fn msg_of(s: &[u8]) -> Vec<u8> { cat3(s, b"", b"") }

fn attr_exec(a: &Vec<u8>) -> (r: Result<(bool, Option<Vec<Vec<u8>>>), Vec<u8>>)
    ensures r matches Ok((sec, list)) ==> attr_spec(a@) == Some((sec, match list { Some(l) => Some(views(l@)), None => None })),
{
    if !(a.len() > 6 && starts_exec(a, b"#[ct::") && a[a.len() - 1] == 93u8) { return Err(cat3(b"malformed attribute ", a.as_slice(), b"")); }
    let inner = sub(a.as_slice(), 6, a.len() - 1);
    let mut p: usize = 0;
    while p < inner.len() && inner[p] != 40u8
        invariant p <= inner@.len(), upto(inner@, 40u8, 0) == upto(inner@, 40u8, p as nat),
        decreases inner.len() - p,
    {
        p += 1;
    }
    let ghost gl: Option<Seq<Seq<u8>>> = None;
    let (name, list) = if p < inner.len() {
        let rest = sub(inner.as_slice(), p + 1, inner.len());
        if rest.len() == 0 || rest[rest.len() - 1] != 41u8 { return Err(cat3(b"malformed attribute ", a.as_slice(), b"")); }
        let l = sub(rest.as_slice(), 0, rest.len() - 1);
        let ps = split_exec(l.as_slice(), 44u8);
        let mut ns: Vec<Vec<u8>> = Vec::new();
        let mut k: usize = 0;
        while k < ps.len()
            invariant k <= ps@.len(), views(ns@) == names_of(views(ps@).subrange(0, k as int)),
            decreases ps.len() - k,
        {
            proof { assert(views(ps@).subrange(0, k + 1).drop_last() =~= views(ps@).subrange(0, k as int)); }
            let t = crate::lower_fn::trim(&ps[k]);
            if t.len() > 0 {
                let ghost o = ns@;
                ns.push(t);
                proof { lemma_views_push(o, ns@.last()); assert(ns@ == o.push(ns@.last())); }
            }
            k += 1;
        }
        proof {
            assert(views(ps@).subrange(0, ps@.len() as int) =~= views(ps@));
            gl = Some(views(ns@));
        }
        (crate::lower_fn::trim(&sub(inner.as_slice(), 0, p)), Some(ns))
    } else { (crate::lower_fn::trim(&inner), None) };
    proof { if p >= inner@.len() { gl = None; } }
    if bytes_eq(name.as_slice(), b"secret") { Ok((true, list)) }
    else if bytes_eq(name.as_slice(), b"public") { Ok((false, list)) }
    else { Err(cat3(b"unknown attribute ct::", name.as_slice(), b"")) }
}

/// The parameters an attribute labels (`idx_spec`).
fn idx_exec(secret: bool, list: &Option<Vec<Vec<u8>>>, names: &Vec<Vec<u8>>, ghost: &Vec<bool>) -> (r: Result<Vec<usize>, Vec<u8>>)
    requires ghost@.len() == names@.len(),
    ensures r matches Ok(ix) ==> idx_spec(secret, match list { Some(l) => Some(views(l@)), None => None }, views(names@), ghost@)
        == Some(ix@.map_values(|x: usize| x as nat)),
{
    let ghost nv = views(names@);
    let mut idx: Vec<usize> = Vec::new();
    match list {
        None => {
            if secret { return Err(msg_of(b"ct::secret needs a parameter list")); }
            let mut j: usize = 0;
            while j < names.len()
                invariant j <= names@.len(), ghost@.len() == names@.len(), idx@.map_values(|x: usize| x as nat) =~= non_ghost(ghost@, j as nat),
                decreases names.len() - j,
            {
                if !ghost[j] { idx.push(j); }
                j += 1;
            }
            proof { assert(nv.len() == names@.len()); }
        },
        Some(l) => {
            let ghost lv = views(l@);
            let mut k: usize = 0;
            while k < l.len()
                invariant k <= l@.len(), ghost@.len() == names@.len(), nv == views(names@), lv == views(l@),
                    named(lv.subrange(0, k as int), nv, ghost@) == Some(idx@.map_values(|x: usize| x as nat)),
                decreases l.len() - k,
            {
                let mut j: usize = 0;
                while j < names.len() && !bytes_eq(names[j].as_slice(), l[k].as_slice())
                    invariant j <= names@.len(), k < l@.len(), nv == views(names@), lv == views(l@),
                        pos_of(nv, lv[k as int], 0) == pos_of(nv, lv[k as int], j as nat),
                    decreases names.len() - j,
                {
                    j += 1;
                }
                proof { assert(lv.subrange(0, k + 1).drop_last() =~= lv.subrange(0, k as int)); assert(lv.subrange(0, k + 1).last() == lv[k as int]); }
                if j == names.len() { return Err(cat3(b"unknown parameter name ", l[k].as_slice(), b"")); }
                if ghost[j] { return Err(cat3(b"parameter ", l[k].as_slice(), b" is ghost/unit-typed and takes no label")); }
                let ghost o = idx@;
                idx.push(j);
                proof { assert(idx@.map_values(|x: usize| x as nat) =~= o.map_values(|x: usize| x as nat).push(j as nat)); }
                k += 1;
            }
            proof { assert(lv.subrange(0, l@.len() as int) =~= lv); }
        },
    }
    Ok(idx)
}

/// The labels the `ct::` attributes `attrs` declare (`decl_spec`); `Err` says why there are none.
pub fn decl_exec(attrs: &Vec<Vec<u8>>, names: &Vec<Vec<u8>>, ghost: &Vec<bool>) -> (r: Result<Option<Vec<bool>>, Vec<u8>>)
    requires ghost@.len() == names@.len(),
    ensures r matches Ok(d) ==> decl_spec(views(attrs@), views(names@), ghost@) == Some(match d { Some(v) => Some(v@), None => None }),
        r matches Ok(Some(d)) ==> d@.len() == names@.len(),
{
    if attrs.len() == 0 { return Ok(None); }
    let ghost av = views(attrs@);
    let ghost nv = views(names@);
    let mut seen: Vec<u8> = Vec::new();
    while seen.len() < names.len()
        invariant seen@.len() <= names@.len(), forall|j: int| 0 <= j < seen@.len() ==> seen@[j] == 0u8,
        decreases names.len() - seen.len(),
    {
        seen.push(0u8);
    }
    proof { assert(seen@ =~= Seq::new(names@.len(), |j: int| 0u8)); }
    let mut ai: usize = 0;
    while ai < attrs.len()
        invariant ai <= attrs@.len(), seen@.len() == names@.len(), ghost@.len() == names@.len(), av == views(attrs@), nv == views(names@),
            seen_after(av, nv, ghost@, ai as nat) == Some(seen@),
        decreases attrs.len() - ai,
    {
        let (secret, list) = attr_exec(&attrs[ai])?;
        let idx = idx_exec(secret, &list, names, ghost)?;
        let ghost ixv = idx@.map_values(|x: usize| x as nat);
        let v: u8 = if secret { 2u8 } else { 1u8 };
        let ghost s0 = seen@;
        let mut q: usize = 0;
        while q < idx.len()
            invariant q <= idx@.len(), seen@.len() == names@.len(), ixv == idx@.map_values(|x: usize| x as nat),
                mark(s0, ixv.subrange(0, q as int), v) == Some(seen@),
            decreases idx.len() - q,
        {
            proof { assert(ixv.subrange(0, q + 1).drop_last() =~= ixv.subrange(0, q as int)); assert(ixv.subrange(0, q + 1).last() == idx@[q as int] as nat); }
            let j = idx[q];
            if j >= seen.len() || seen[j] != 0 { return Err(cat3(b"parameter ", if j < names.len() { names[j].as_slice() } else { b"?" }, b" named twice")); }
            seen.set(j, v);
            q += 1;
        }
        proof {
            assert(ixv.subrange(0, idx@.len() as int) =~= ixv);
            assert(av[ai as int] == attrs@[ai as int]@);
        }
        ai += 1;
    }
    let mut d: Vec<bool> = Vec::new();
    let mut j: usize = 0;
    while j < names.len()
        invariant j <= names@.len(), seen@.len() == names@.len(), ghost@.len() == names@.len(), d@.len() == j,
            forall|k: int| 0 <= k < j ==> !ghost@[k] ==> seen@[k] != 0, forall|k: int| 0 <= k < j ==> d@[k] == (seen@[k] == 2u8),
        decreases names.len() - j,
    {
        if !ghost[j] && seen[j] == 0 {
            let mut e = cat3(b"parameter ", names[j].as_slice(), b" (#");
            let n = crate::text::dec(j as u64 + 1);
            put(&mut e, n.as_slice());
            put(&mut e, b") not named");
            return Err(e);
        }
        d.push(seen[j] == 2u8);
        j += 1;
    }
    proof {
        assert(d@ =~= Seq::new(nv.len(), |j: int| seen@[j] == 2u8));
        assert(attrs@.len() == av.len());
    }
    Ok(Some(d))
}

} // verus!
