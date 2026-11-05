//! The verified interpreter's values (`CVal`, viewed as `ctcore::sem::Val` by `cv`), frames, and
//! the in-place navigation and writes it runs `ctcore::sem`'s `read_at`/`write_at` with.
//! - A read navigates by reference and clones only the leaf (`nav`, `take`).
//! - A write takes the root value out of its frame slot, rebuilds along the path moving each
//!   child out and back (`set_at`, `push_at`), and puts it back: no copy of the untouched parts.
//! - A cursor inside a `Shr` snapshot is a path with `Snap` steps from a frame root (`XPE`), so a
//!   read through a shared reference does not copy the snapshot either.
#[cfg(verus_keep_ghost)]
use ctcore::sem::{get, nth, pad, put, read_at, write_at};
#[cfg(verus_keep_ghost)]
use ctcore::sem::{Frame, Loc, Root, Val, PE};
use vstd::prelude::*;

verus! {

pub enum CRoot { Local(usize), Slot(usize) }

pub enum CPE { Field(usize), Index(u128), Variant(usize) }

pub struct CLoc { pub root: CRoot, pub path: Vec<CPE> }

/// `ctcore::sem::Val` as an exec value.
pub enum CVal { Int(u128), Unit, Tup(Vec<CVal>), Adt(usize, Vec<CVal>), Arr(Vec<CVal>), Shr(Box<CVal>), Mut(CLoc) }

pub struct CFrame { pub locals: Vec<CVal>, pub slots: Vec<CVal> }

/// A cursor step: a path element, or `Snap` (into a `Shr` snapshot).
pub enum XPE { Field(usize), Index(u128), Variant(usize), Snap }

// ------------------------------------------------------------------ views

pub open spec fn root_v(r: CRoot) -> Root {
    match r { CRoot::Local(i) => Root::Local(i as nat), CRoot::Slot(j) => Root::Slot(j as nat) }
}

pub open spec fn pe_v(e: CPE) -> PE {
    match e { CPE::Field(i) => PE::Field(i as nat), CPE::Index(i) => PE::Index(i as nat), CPE::Variant(k) => PE::Variant(k as nat) }
}

pub open spec fn pes(p: Seq<CPE>) -> Seq<PE> { Seq::new(p.len(), |i: int| pe_v(p[i])) }

pub open spec fn loc_v(l: CLoc) -> Loc { Loc { root: root_v(l.root), path: pes(l.path@) } }

pub open spec fn cv(v: CVal) -> Val
    decreases v,
{
    match v {
        CVal::Int(n) => Val::Int(n),
        CVal::Unit => Val::Unit,
        CVal::Tup(vs) => Val::Tup(Seq::new(vs@.len(), |i: int| if 0 <= i < vs@.len() { cv(vs@[i]) } else { Val::Unit })),
        CVal::Adt(k, vs) => Val::Adt(k as nat, Seq::new(vs@.len(), |i: int| if 0 <= i < vs@.len() { cv(vs@[i]) } else { Val::Unit })),
        CVal::Arr(vs) => Val::Arr(Seq::new(vs@.len(), |i: int| if 0 <= i < vs@.len() { cv(vs@[i]) } else { Val::Unit })),
        CVal::Shr(b) => Val::Shr(Box::new(cv(*b))),
        CVal::Mut(l) => Val::Mut(loc_v(l)),
    }
}

pub open spec fn cvs(s: Seq<CVal>) -> Seq<Val> { Seq::new(s.len(), |i: int| cv(s[i])) }

pub open spec fn fv(f: CFrame) -> Frame { Frame { locals: cvs(f.locals@), slots: cvs(f.slots@) } }

/// `cv` of an aggregate is its constructor over `cvs` of its elements.
pub proof fn lemma_cv(v: CVal)
    ensures match v {
        CVal::Tup(vs) => cv(v) == Val::Tup(cvs(vs@)),
        CVal::Adt(k, vs) => cv(v) == Val::Adt(k as nat, cvs(vs@)),
        CVal::Arr(vs) => cv(v) == Val::Arr(cvs(vs@)),
        _ => true,
    },
{
    match v {
        CVal::Tup(vs) => {
            assert(cv(v)->Tup_0 =~= cvs(vs@));
        },
        CVal::Adt(k, vs) => {
            assert(cv(v)->Adt_1 =~= cvs(vs@));
        },
        CVal::Arr(vs) => {
            assert(cv(v)->Arr_0 =~= cvs(vs@));
        },
        _ => {},
    }
}

pub proof fn lemma_cvs_update(s: Seq<CVal>, i: int, x: CVal)
    requires 0 <= i < s.len(),
    ensures cvs(s.update(i, x)) == cvs(s).update(i, cv(x)),
{
    assert(cvs(s.update(i, x)) =~= cvs(s).update(i, cv(x)));
}

pub proof fn lemma_cvs_push(s: Seq<CVal>, x: CVal)
    ensures cvs(s.push(x)) == cvs(s).push(cv(x)),
{
    assert(cvs(s.push(x)) =~= cvs(s).push(cv(x)));
}

pub open spec fn xget(v: Val, e: XPE) -> Val {
    match e {
        XPE::Field(i) => get(v, PE::Field(i as nat)),
        XPE::Index(i) => get(v, PE::Index(i as nat)),
        XPE::Variant(k) => get(v, PE::Variant(k as nat)),
        XPE::Snap => match v { Val::Shr(b) => *b, _ => Val::Unit },
    }
}

pub open spec fn xread(v: Val, p: Seq<XPE>) -> Val
    decreases p.len(),
{
    if p.len() == 0 { v } else { xread(xget(v, p[0]), p.drop_first()) }
}

pub open spec fn xpe(e: CPE) -> XPE {
    match e { CPE::Field(i) => XPE::Field(i), CPE::Index(i) => XPE::Index(i), CPE::Variant(k) => XPE::Variant(k) }
}

/// A `Snap`-free cursor path as a location path.
pub open spec fn xpes(p: Seq<XPE>) -> Seq<PE> {
    Seq::new(p.len(), |i: int| match p[i] {
        XPE::Field(f) => PE::Field(f as nat),
        XPE::Index(x) => PE::Index(x as nat),
        XPE::Variant(k) => PE::Variant(k as nat),
        XPE::Snap => PE::Field(0),
    })
}

pub open spec fn no_snap(p: Seq<XPE>) -> bool { forall|i: int| 0 <= i < p.len() ==> !(#[trigger] p[i] is Snap) }

pub proof fn lemma_xread_push(v: Val, p: Seq<XPE>, e: XPE)
    ensures xread(v, p.push(e)) == xget(xread(v, p), e),
    decreases p.len(),
{
    if p.len() > 0 {
        assert(p.push(e).drop_first() =~= p.drop_first().push(e));
        assert(p.push(e)[0] == p[0]);
        lemma_xread_push(xget(v, p[0]), p.drop_first(), e);
    } else {
        reveal_with_fuel(xread, 2);
        assert(p.push(e).drop_first().len() == 0);
        assert(p.push(e)[0] == e);
    }
}

/// A `Snap`-free cursor reads as its location path.
pub proof fn lemma_xread_loc(v: Val, p: Seq<XPE>)
    requires no_snap(p),
    ensures xread(v, p) == read_at(v, xpes(p)),
    decreases p.len(),
{
    if p.len() > 0 {
        assert(xpes(p).drop_first() =~= xpes(p.drop_first()));
        assert(!(p[0] is Snap));
        lemma_xread_loc(xget(v, p[0]), p.drop_first());
    }
}

/// Reading after a mid-path `Variant` ignores the tag it sets.
proof fn lemma_xget_retag(k: nat, j: nat, vs: Seq<Val>, e: XPE)
    ensures xget(Val::Adt(k, vs), e) == xget(Val::Adt(j, vs), e),
{}

/// A write under an `Adt` through a nonempty path keeps the tag and builds the same fields
/// whatever the tag is.
pub proof fn lemma_write_retag(k: nat, j: nat, vs: Seq<Val>, path: Seq<PE>, w: Val)
    requires path.len() > 0,
    ensures ({
        let (a, b) = (write_at(Val::Adt(k, vs), path, w), write_at(Val::Adt(j, vs), path, w));
        a is Adt && b is Adt && a->Adt_0 == k && b->Adt_0 == j && a->Adt_1 == b->Adt_1
    }),
{
    assert(path.drop_first().len() == path.len() - 1);
}

// ------------------------------------------------------------------ cloning and equality

pub fn cclone(v: &CVal) -> (r: CVal)
    ensures cv(r) == cv(*v),
    decreases v,
{
    match v {
        CVal::Int(n) => CVal::Int(*n),
        CVal::Unit => CVal::Unit,
        CVal::Tup(vs) => { let r = CVal::Tup(clone_vec(vs)); proof { lemma_cv(r); lemma_cv(*v); } r },
        CVal::Adt(k, vs) => { let r = CVal::Adt(*k, clone_vec(vs)); proof { lemma_cv(r); lemma_cv(*v); } r },
        CVal::Arr(vs) => { let r = CVal::Arr(clone_vec(vs)); proof { lemma_cv(r); lemma_cv(*v); } r },
        CVal::Shr(b) => CVal::Shr(Box::new(cclone(&**b))),
        CVal::Mut(l) => CVal::Mut(clone_loc(l)),
    }
}

pub fn clone_vec(vs: &Vec<CVal>) -> (r: Vec<CVal>)
    ensures cvs(r@) == cvs(vs@),
    decreases vs,
{
    let mut r: Vec<CVal> = Vec::new();
    let mut i: usize = 0;
    while i < vs.len()
        invariant i <= vs@.len(), cvs(r@) == cvs(vs@.subrange(0, i as int)),
        decreases vs.len() - i,
    {
        let x = cclone(&vs[i]);
        proof { lemma_cvs_push(r@, x); assert(vs@.subrange(0, i + 1) =~= vs@.subrange(0, i as int).push(vs@[i as int])); lemma_cvs_push(vs@.subrange(0, i as int), vs@[i as int]); }
        r.push(x);
        i += 1;
    }
    proof { assert(vs@.subrange(0, vs@.len() as int) =~= vs@); }
    r
}

pub fn clone_cpe(e: &CPE) -> (r: CPE)
    ensures r == *e,
{
    match e { CPE::Field(i) => CPE::Field(*i), CPE::Index(i) => CPE::Index(*i), CPE::Variant(k) => CPE::Variant(*k) }
}

pub fn clone_loc(l: &CLoc) -> (r: CLoc)
    ensures loc_v(r) == loc_v(*l),
{
    let root = match l.root { CRoot::Local(i) => CRoot::Local(i), CRoot::Slot(j) => CRoot::Slot(j) };
    let mut path: Vec<CPE> = Vec::new();
    let mut i: usize = 0;
    while i < l.path.len()
        invariant i <= l.path@.len(), path@ == l.path@.subrange(0, i as int),
        decreases l.path.len() - i,
    {
        path.push(clone_cpe(&l.path[i]));
        proof { assert(path@ =~= l.path@.subrange(0, i + 1)); }
        i += 1;
    }
    proof { assert(path@ =~= l.path@); }
    CLoc { root, path }
}

/// `cv(a) == cv(b)`.
pub fn ceq(a: &CVal, b: &CVal) -> (r: bool)
    ensures r == (cv(*a) == cv(*b)),
    decreases a,
{
    proof { lemma_cv(*a); lemma_cv(*b); }
    match (a, b) {
        (CVal::Int(x), CVal::Int(y)) => *x == *y,
        (CVal::Unit, CVal::Unit) => true,
        (CVal::Tup(xs), CVal::Tup(ys)) => ceq_vec(xs, ys),
        (CVal::Adt(k, xs), CVal::Adt(j, ys)) => *k == *j && ceq_vec(xs, ys),
        (CVal::Arr(xs), CVal::Arr(ys)) => ceq_vec(xs, ys),
        (CVal::Shr(x), CVal::Shr(y)) => ceq(&**x, &**y),
        (CVal::Mut(l), CVal::Mut(m)) => {
            let r = match (&l.root, &m.root) { (CRoot::Local(i), CRoot::Local(j)) => *i == *j, (CRoot::Slot(i), CRoot::Slot(j)) => *i == *j, _ => false };
            proof { if loc_v(*l) == loc_v(*m) { assert(root_v(l.root) == root_v(m.root)); } }
            r && pes_eq(&l.path, &m.path)
        },
        _ => false,
    }
}

fn pes_eq(p: &Vec<CPE>, q: &Vec<CPE>) -> (r: bool)
    ensures r == (pes(p@) == pes(q@)),
{
    if p.len() != q.len() {
        proof { if pes(p@) == pes(q@) { assert(pes(p@).len() == pes(q@).len()); } }
        return false;
    }
    let mut i: usize = 0;
    while i < p.len()
        invariant i <= p@.len() == q@.len(), forall|k: int| 0 <= k < i ==> pe_v(#[trigger] p@[k]) == pe_v(q@[k]),
        decreases p.len() - i,
    {
        let same = match (&p[i], &q[i]) {
            (CPE::Field(x), CPE::Field(y)) => *x == *y,
            (CPE::Index(x), CPE::Index(y)) => *x == *y,
            (CPE::Variant(x), CPE::Variant(y)) => *x == *y,
            _ => false,
        };
        if !same {
            proof { if pes(p@) == pes(q@) { assert(pes(p@)[i as int] == pes(q@)[i as int]); } }
            return false;
        }
        i += 1;
    }
    proof { assert(pes(p@) =~= pes(q@)); }
    true
}

pub fn ceq_vec(xs: &Vec<CVal>, ys: &Vec<CVal>) -> (r: bool)
    ensures r == (cvs(xs@) == cvs(ys@)),
    decreases xs,
{
    if xs.len() != ys.len() {
        proof { if cvs(xs@) == cvs(ys@) { assert(cvs(xs@).len() == cvs(ys@).len()); } }
        return false;
    }
    let mut i: usize = 0;
    while i < xs.len()
        invariant i <= xs@.len() == ys@.len(), forall|q: int| 0 <= q < i ==> cv(#[trigger] xs@[q]) == cv(ys@[q]),
        decreases xs.len() - i,
    {
        if !ceq(&xs[i], &ys[i]) {
            proof { assert(cvs(xs@)[i as int] != cvs(ys@)[i as int]); }
            return false;
        }
        i += 1;
    }
    proof { assert(cvs(xs@) =~= cvs(ys@)); }
    true
}

// ------------------------------------------------------------------ reads by reference

/// A navigation result: `None` reads `Unit`; `Some(x)` with tag `None` reads `cv(*x)`; with tag
/// `Some(j)`, `x` is an `Adt` read with its variant set to `j` (a trailing `Variant`).
pub open spec fn nav_ok(r: (Option<&CVal>, Option<usize>), t: Val) -> bool {
    match r.0 {
        None => t == Val::Unit,
        Some(x) => match r.1 {
            None => cv(*x) == t,
            Some(j) => cv(*x) is Adt && t == Val::Adt(j as nat, cv(*x)->Adt_1),
        },
    }
}

pub fn nav<'a>(v: &'a CVal, p: &Vec<XPE>, k: usize) -> (r: (Option<&'a CVal>, Option<usize>))
    requires k <= p@.len(),
    ensures nav_ok(r, xread(cv(*v), p@.subrange(k as int, p@.len() as int))),
    decreases p@.len() - k,
{
    let ghost rest = p@.subrange(k as int, p@.len() as int);
    if k == p.len() {
        return (Some(v), None);
    }
    proof {
        assert(rest.drop_first() =~= p@.subrange(k + 1, p@.len() as int));
        assert(rest[0] == p@[k as int]);
        lemma_cv(*v);
    }
    match (&p[k], v) {
        (XPE::Field(i), CVal::Tup(vs)) => {
            if *i < vs.len() { nav(&vs[*i], p, k + 1) } else { proof { lemma_xread_unit(rest.drop_first()); } (None, None) }
        },
        (XPE::Field(i), CVal::Adt(_, vs)) => {
            if *i < vs.len() { nav(&vs[*i], p, k + 1) } else { proof { lemma_xread_unit(rest.drop_first()); } (None, None) }
        },
        (XPE::Index(i), CVal::Arr(vs)) => {
            if *i < vs.len() as u128 { nav(&vs[*i as usize], p, k + 1) } else { proof { lemma_xread_unit(rest.drop_first()); } (None, None) }
        },
        (XPE::Variant(j), CVal::Adt(_t, _vs)) => {
            if k + 1 == p.len() {
                proof { assert(rest.drop_first().len() == 0); }
                (Some(v), Some(*j))
            } else {
                proof {
                    let rr = rest.drop_first();
                    assert(rr.len() > 0);
                    lemma_xget_retag(*j as nat, *_t as nat, cvs(_vs@), rr[0]);
                    assert(xget(cv(*v), rest[0]) == Val::Adt(*j as nat, cvs(_vs@)));
                    assert(xread(Val::Adt(*j as nat, cvs(_vs@)), rr) == xread(cv(*v), rr));
                }
                nav(v, p, k + 1)
            }
        },
        (XPE::Snap, CVal::Shr(b)) => nav(&**b, p, k + 1),
        _ => {
            proof { lemma_xread_unit(rest.drop_first()); }
            (None, None)
        },
    }
}

pub proof fn lemma_read_at_unit(p: Seq<PE>)
    ensures read_at(Val::Unit, p) == Val::Unit,
    decreases p.len(),
{
    if p.len() > 0 { lemma_read_at_unit(p.drop_first()); }
}

pub proof fn lemma_xread_unit(p: Seq<XPE>)
    ensures xread(Val::Unit, p) == Val::Unit,
    decreases p.len(),
{
    if p.len() > 0 { lemma_xread_unit(p.drop_first()); }
}

/// The value a navigation result reads, cloned.
pub fn take(r: (Option<&CVal>, Option<usize>)) -> (v: CVal)
    ensures forall|t: Val| nav_ok(r, t) ==> cv(v) == t,
{
    match r {
        (None, _) => CVal::Unit,
        (Some(x), None) => cclone(x),
        (Some(x), Some(j)) => match x {
            CVal::Adt(_, vs) => { let v = CVal::Adt(j, clone_vec(vs)); proof { lemma_cv(v); lemma_cv(*x); } v },
            _ => { proof { lemma_cv(*x); } CVal::Unit },
        },
    }
}

/// `as_int` of what a navigation result reads.
pub fn take_int(r: (Option<&CVal>, Option<usize>)) -> (n: u128)
    ensures forall|t: Val| nav_ok(r, t) ==> n == ctcore::sem::as_int(t),
{
    match r {
        (Some(x), None) => match x { CVal::Int(n) => *n, _ => 0 },
        (Some(_x), Some(_)) => { proof { lemma_cv(*_x); } 0 },
        (None, _) => 0,
    }
}

pub open spec fn base_v(fr: Frame, r: Root) -> Val {
    match r { Root::Local(i) => nth(fr.locals, i), Root::Slot(j) => nth(fr.slots, j) }
}

pub fn base<'a>(fr: &'a CFrame, r: &CRoot) -> (b: Option<&'a CVal>)
    ensures match b { None => base_v(fv(*fr), root_v(*r)) == Val::Unit, Some(x) => cv(*x) == base_v(fv(*fr), root_v(*r)) },
{
    match r {
        CRoot::Local(i) => if *i < fr.locals.len() { Some(&fr.locals[*i]) } else { None },
        CRoot::Slot(j) => if *j < fr.slots.len() { Some(&fr.slots[*j]) } else { None },
    }
}

/// Navigation from a frame root.
pub fn at<'a>(fr: &'a CFrame, r: &CRoot, p: &Vec<XPE>) -> (res: (Option<&'a CVal>, Option<usize>))
    ensures nav_ok(res, xread(base_v(fv(*fr), root_v(*r)), p@)),
{
    proof { assert(p@.subrange(0, p@.len() as int) =~= p@); }
    match base(fr, r) {
        Some(x) => nav(x, p, 0),
        None => { proof { lemma_xread_unit(p@); } (None, None) },
    }
}

// ------------------------------------------------------------------ writes in place

/// Moves `vs[i]` out, leaving `Unit`.
pub fn take_at(vs: &mut Vec<CVal>, i: usize) -> (x: CVal)
    requires i < old(vs)@.len(),
    ensures x == old(vs)@[i as int], final(vs)@ == old(vs)@.update(i as int, CVal::Unit),
{
    let mut x = CVal::Unit;
    std::mem::swap(&mut x, &mut vs[i]);
    x
}

/// `write_at(cv(v), pes(p[k..]), cv(w))`.
pub fn set_at(v: CVal, p: &Vec<CPE>, k: usize, w: CVal) -> (r: CVal)
    requires k <= p@.len(),
    ensures cv(r) == write_at(cv(v), pes(p@.subrange(k as int, p@.len() as int)), cv(w)),
    decreases p@.len() - k,
{
    let ghost path = pes(p@.subrange(k as int, p@.len() as int));
    if k == p.len() {
        return w;
    }
    proof {
        assert(path.drop_first() =~= pes(p@.subrange(k + 1, p@.len() as int)));
        assert(path[0] == pe_v(p@[k as int]));
        lemma_cv(v);
    }
    let ghost v0 = cv(v);
    match (&p[k], v) {
        (CPE::Field(i), CVal::Tup(mut vs)) => {
            let ghost o = vs@;
            pad_vec(&mut vs, *i);
            let ghost pd = vs@;
            let x = take_at(&mut vs, *i);
            proof { assert(cv(x) == nth(cvs(o), *i as nat)); }
            let y = set_at(x, p, k + 1, w);
            vs.set(*i, y);
            proof { assert(vs@ == pd.update(*i as int, y)); lemma_cvs_update(pd, *i as int, y); }
            let r = CVal::Tup(vs);
            proof { lemma_cv(r); }
            r
        },
        (CPE::Field(i), CVal::Adt(t, mut vs)) => {
            let ghost o = vs@;
            pad_vec(&mut vs, *i);
            let ghost pd = vs@;
            let x = take_at(&mut vs, *i);
            proof { assert(cv(x) == nth(cvs(o), *i as nat)); }
            let y = set_at(x, p, k + 1, w);
            vs.set(*i, y);
            proof { assert(vs@ == pd.update(*i as int, y)); lemma_cvs_update(pd, *i as int, y); }
            let r = CVal::Adt(t, vs);
            proof { lemma_cv(r); }
            r
        },
        (CPE::Index(i), CVal::Arr(mut vs)) => {
            if *i < vs.len() as u128 {
                let ghost o = vs@;
                let x = take_at(&mut vs, *i as usize);
                let y = set_at(x, p, k + 1, w);
                vs.set(*i as usize, y);
                proof {
                    assert(vs@ == o.update(*i as int, y));
                    lemma_cvs_update(o, *i as int, y);
                }
                let r = CVal::Arr(vs);
                proof { lemma_cv(r); }
                r
            } else {
                let r = CVal::Arr(vs);
                proof { lemma_cv(r); }
                r
            }
        },
        (CPE::Variant(_j), CVal::Adt(t, vs)) => {
            if k + 1 == p.len() {
                proof { assert(path.drop_first().len() == 0); lemma_cv(w); }
                match w {
                    CVal::Adt(_, ws) => { let r = CVal::Adt(t, ws); proof { lemma_cv(r); } r },
                    _ => { let r = CVal::Adt(t, vs); proof { lemma_cv(r); } r },
                }
            } else {
                let ghost fs = cvs(vs@);
                let r = set_at(CVal::Adt(t, vs), p, k + 1, w);
                proof {
                    lemma_cv(CVal::Adt(t, vs));
                    lemma_write_retag(t as nat, *_j as nat, fs, path.drop_first(), cv(w));
                }
                r
            }
        },
        (_, v) => {
            proof { assert(v0 == cv(v)); }
            v
        },
    }
}

/// `vs` padded with `Unit` to at least `i + 1` elements.
fn pad_vec(vs: &mut Vec<CVal>, i: usize)
    ensures cvs(final(vs)@) == pad(cvs(old(vs)@), (i + 1) as nat), i < final(vs)@.len(),
        final(vs)@.len() == if old(vs)@.len() <= i { i + 1 } else { old(vs)@.len() as int },
        forall|q: int| 0 <= q < old(vs)@.len() ==> #[trigger] final(vs)@[q] == old(vs)@[q],
        forall|q: int| old(vs)@.len() <= q < final(vs)@.len() ==> #[trigger] final(vs)@[q] == CVal::Unit,
{
    let ghost o = vs@;
    while vs.len() <= i
        invariant o.len() <= vs@.len(), vs@.len() <= (if o.len() <= i { i + 1 } else { o.len() as int }),
            forall|q: int| 0 <= q < o.len() ==> #[trigger] vs@[q] == o[q],
            forall|q: int| o.len() <= q < vs@.len() ==> #[trigger] vs@[q] == CVal::Unit,
        decreases i + 1 - vs@.len(),
    {
        vs.push(CVal::Unit);
    }
    proof {
        if o.len() <= i {
            assert(cvs(vs@) =~= cvs(o) + Seq::new((i + 1 - o.len()) as nat, |j: int| Val::Unit));
        } else {
            assert(vs@ =~= o);
        }
    }
}

/// `grow`'s write: when `read_at(cv(v), path)` is `Arr(s)`, `write_at(cv(v), path, Arr(s + xs))`;
/// otherwise `v` itself.
pub open spec fn push_spec(v: Val, path: Seq<PE>, xs: Seq<Val>) -> Val {
    match read_at(v, path) { Val::Arr(s) => write_at(v, path, Val::Arr(s + xs)), _ => v }
}

/// `push_spec` when the leaf is an `Arr`: the leaf's elements extended by `xs`.
pub fn push_at(v: CVal, p: &Vec<CPE>, k: usize, xs: Vec<CVal>) -> (r: CVal)
    requires k <= p@.len(), read_at(cv(v), pes(p@.subrange(k as int, p@.len() as int))) is Arr,
    ensures cv(r) == push_spec(cv(v), pes(p@.subrange(k as int, p@.len() as int)), cvs(xs@)),
    decreases p@.len() - k,
{
    let ghost path = pes(p@.subrange(k as int, p@.len() as int));
    proof { lemma_cv(v); }
    if k == p.len() {
        match v {
            CVal::Arr(mut vs) => {
                let ghost o = vs@;
                let mut ys = xs;
                let ghost xo = ys@;
                vs.append(&mut ys);
                let r = CVal::Arr(vs);
                proof { lemma_cv(r); assert(vs@ == o + xo); assert(cvs(vs@) =~= cvs(o) + cvs(xo)); }
                return r;
            },
            _ => { return v; },
        }
    }
    proof {
        assert(path.drop_first() =~= pes(p@.subrange(k + 1, p@.len() as int)));
        assert(path[0] == pe_v(p@[k as int]));
    }
    proof { lemma_read_at_unit(path.drop_first()); }
    match (&p[k], v) {
        (CPE::Field(i), CVal::Tup(mut vs)) => {
            let ghost o = vs@;
            let x = take_at(&mut vs, *i);
            let y = push_at(x, p, k + 1, xs);
            vs.set(*i, y);
            proof { assert(vs@ == o.update(*i as int, y)); lemma_cvs_update(o, *i as int, y); assert(pad(cvs(o), (*i + 1) as nat) == cvs(o)); }
            let r = CVal::Tup(vs);
            proof { lemma_cv(r); }
            r
        },
        (CPE::Field(i), CVal::Adt(t, mut vs)) => {
            let ghost o = vs@;
            let x = take_at(&mut vs, *i);
            let y = push_at(x, p, k + 1, xs);
            vs.set(*i, y);
            proof { assert(vs@ == o.update(*i as int, y)); lemma_cvs_update(o, *i as int, y); assert(pad(cvs(o), (*i + 1) as nat) == cvs(o)); }
            let r = CVal::Adt(t, vs);
            proof { lemma_cv(r); }
            r
        },
        (CPE::Index(i), CVal::Arr(mut vs)) => {
            if *i >= vs.len() as u128 {
                let r = CVal::Arr(vs);
                proof { lemma_cv(r); }
                return r;
            }
            let ghost o = vs@;
            let x = take_at(&mut vs, *i as usize);
            let y = push_at(x, p, k + 1, xs);
            vs.set(*i as usize, y);
            proof { assert(vs@ == o.update(*i as int, y)); lemma_cvs_update(o, *i as int, y); }
            let r = CVal::Arr(vs);
            proof { lemma_cv(r); }
            r
        },
        (CPE::Variant(_j), CVal::Adt(t, vs)) => {
            let ghost fs = cvs(vs@);
            let ghost rr = path.drop_first();
            proof {
                lemma_cv(CVal::Adt(t, vs));
                if rr.len() == 0 { assert(read_at(Val::Adt(*_j as nat, fs), rr) == Val::Adt(*_j as nat, fs)); }
                assert(rr.len() > 0);
                assert(get(Val::Adt(t as nat, fs), rr[0]) == get(Val::Adt(*_j as nat, fs), rr[0]));
                assert(read_at(cv(CVal::Adt(t, vs)), rr) == read_at(Val::Adt(*_j as nat, fs), rr));
            }
            let ghost sv = read_at(cv(CVal::Adt(t, vs)), rr)->Arr_0;
            let r = push_at(CVal::Adt(t, vs), p, k + 1, xs);
            proof { lemma_write_retag(t as nat, *_j as nat, fs, rr, Val::Arr(sv + cvs(xs@))); }
            r
        },
        (_, v) => v,
    }
}

/// `path` as cursor steps.
pub fn xpath_of(path: &Vec<CPE>) -> (r: Vec<XPE>)
    ensures no_snap(r@), xpes(r@) == pes(path@), r@.len() == path@.len(),
{
    let mut r: Vec<XPE> = Vec::new();
    let mut i: usize = 0;
    while i < path.len()
        invariant i <= path@.len(), r@.len() == i, no_snap(r@), forall|q: int| 0 <= q < i ==> #[trigger] r@[q] == xpe(path@[q]),
        decreases path.len() - i,
    {
        r.push(match &path[i] { CPE::Field(f) => XPE::Field(*f), CPE::Index(x) => XPE::Index(*x), CPE::Variant(k) => XPE::Variant(*k) });
        i += 1;
    }
    proof { assert(xpes(r@) =~= pes(path@)); }
    r
}

/// A `Snap`-free cursor path as a location path.
pub fn cpath_of(path: &Vec<XPE>) -> (r: Vec<CPE>)
    requires no_snap(path@),
    ensures pes(r@) == xpes(path@),
{
    let mut r: Vec<CPE> = Vec::new();
    let mut i: usize = 0;
    while i < path.len()
        invariant i <= path@.len(), r@.len() == i, no_snap(path@), forall|q: int| 0 <= q < i ==> pe_v(#[trigger] r@[q]) == xpes(path@)[q],
        decreases path.len() - i,
    {
        let e = match &path[i] { XPE::Field(f) => CPE::Field(*f), XPE::Index(x) => CPE::Index(*x), XPE::Variant(k) => CPE::Variant(*k), XPE::Snap => CPE::Field(0) };
        proof { assert(!(path@[i as int] is Snap)); }
        r.push(e);
        i += 1;
    }
    proof { assert(pes(r@) =~= xpes(path@)); }
    r
}

} // verus!
