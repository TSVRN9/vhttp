//! The MIR evaluator, part two: exec mirrors of `sem`'s terminators and block runs, and
//! `mir_eval`, proved against `mir_run`. A `Done`, `Panic` or `Fuel` it reports is `mir_run`'s;
//! `GaveUp` (a cap, a count past `u64`, an `Unsup` arm, an arm the evaluator leaves out) claims
//! nothing (addendum decision 2). Only in-subset instances run: the ghost witness `(s, rs)` of
//! `in_subset` makes every block the run enters `block_ok`, so no block is checked at run time.
use crate::eval::*;
use crate::eval_tab::*;
use crate::interp_val::*;
use crate::mir::*;
use crate::policy::{has_exec, Policy};
#[cfg(verus_keep_ghost)]
use crate::policy::{cpol, lemma_set_of};
#[cfg(verus_keep_ghost)]
use crate::sem::*;
use crate::sem::StdFn;
#[cfg(verus_keep_ghost)]
use ctcore::sem::{get, put, read_at, write_at, Event, Frame, PE};
use ctcore::sem::Val;
use vstd::prelude::*;

verus! {

pub enum Ev { Done(CFrame, u64), Panic, Fuel, GaveUp }

/// Addendum decision 2: each outcome the evaluator reports is the spec's.
pub open spec fn ev_ok(o: Out, r: Ev) -> bool {
    match r {
        Ev::Done(f, n) => o matches Out::Done(g, _, s) && fv(f) == g && n as nat == s,
        Ev::Panic => o is Panic,
        Ev::Fuel => o is Fuel,
        Ev::GaveUp => true,
    }
}

/// A terminator's outcome: a jump (or a `Return`) with its steps, the frame updated in place.
pub enum St { Jump(usize, u64), Ret(u64), Panic, Fuel, GaveUp }

pub open spec fn st_ok(f1: Frame, r: St, st: Step) -> bool {
    match r {
        St::Jump(t, n) => st matches Step::Jump(t2, f2, _, s2) && t2 == t as nat && f2 == f1 && s2 == n as nat,
        St::Ret(n) => st matches Step::Stop(Out::Done(f2, _, s2)) && f2 == f1 && s2 == n as nat,
        St::Panic => st matches Step::Stop(Out::Panic),
        St::Fuel => st matches Step::Stop(Out::Fuel),
        St::GaveUp => true,
    }
}

// ------------------------------------------------------------------ the subset witness

/// What `closed` gives for a block of an instance in `s`.
proof fn lemma_in(m: MirCrate, pol: CallPolicy, s: Set<nat>, rs: spec_fn(nat) -> Set<nat>, j: nat, b: Body, bb: nat)
    requires closed(m, pol, s, rs), s.contains(j), inst_body(m, j) == Some(b), rs(j).contains(bb),
    ensures bb < b.blocks@.len(), block_ok(m, pol, b, b.blocks@[bb as int]),
        succs_in(b.blocks@[bb as int].terminator.kind, rs(j)), callees_in(m, pol, b, b.blocks@[bb as int].terminator.kind, s),
{
    assert(body_in(m, pol, s, rs, j));
}

proof fn lemma_entry_in(m: MirCrate, pol: CallPolicy, s: Set<nat>, rs: spec_fn(nat) -> Set<nat>, j: nat)
    requires closed(m, pol, s, rs), s.contains(j),
    ensures inst_body(m, j) is Some, rs(j).contains(0),
{
    assert(body_in(m, pol, s, rs, j));
}

// ------------------------------------------------------------------ terminators

/// `SwitchInt`'s target: the first branch whose value is `d` (`find`), else `otherwise`.
fn switch_target(tg: &SwitchTargets, d: u128) -> (t: usize)
    ensures t as nat == match find(tg.branches@, |br: (u128, BasicBlockIdx)| br.0 == d) {
            Some(j) => tg.branches@[j as int].1 as nat,
            None => tg.otherwise as nat,
        },
        t == tg.otherwise || exists|k: int| 0 <= k < tg.branches@.len() && t == (#[trigger] tg.branches@[k]).1,
{
    let mut k: usize = 0;
    while k < tg.branches.len()
        invariant k <= tg.branches@.len(), forall|l: int| 0 <= l < k ==> (#[trigger] tg.branches@[l]).0 != d,
        decreases tg.branches.len() - k,
    {
        if tg.branches[k].0 == d {
            proof { crate::look::lemma_find(tg.branches@, |br: (u128, BasicBlockIdx)| br.0 == d, k as nat); }
            return tg.branches[k].1;
        }
        k += 1;
    }
    proof { crate::look::lemma_find(tg.branches@, |br: (u128, BasicBlockIdx)| br.0 == d, k as nat); }
    tg.otherwise
}

fn e_switch(m: &MirCrate, tb: &Tabs, fr: &CFrame, x: &Operand, tg: &SwitchTargets) -> (r: St)
    requires tabs_ok(*m, *tb),
    ensures st_ok(fv(*fr), r, switch_step(*m, fv(*fr), *x, *tg)),
        r matches St::Jump(t, _) ==> t == tg.otherwise || exists|k: int| 0 <= k < tg.branches@.len() && t == (#[trigger] tg.branches@[k]).1,
{
    match e_eval_op(m, tb, fr, x) {
        Ok((CVal::Int(d), k)) => {
            if k == u64::MAX { return St::GaveUp; }
            St::Jump(switch_target(tg, d), 1 + k)
        },
        Ok((_v, _)) => { proof { lemma_cv(_v); } St::Panic },
        Err(Halt::Panic) => St::Panic,
        Err(Halt::GaveUp) => St::GaveUp,
    }
}

fn e_assert(m: &MirCrate, tb: &Tabs, fr: &CFrame, x: &Operand, expected: bool, target: BasicBlockIdx) -> (r: St)
    requires tabs_ok(*m, *tb),
    ensures st_ok(fv(*fr), r, assert_step(*m, fv(*fr), *x, expected, target)), r matches St::Jump(t, _) ==> t == target,
{
    match e_eval_op(m, tb, fr, x) {
        Ok((CVal::Int(c), k)) => {
            if (c == 0 || c == 1) && (c == 1) == expected {
                if k == u64::MAX { return St::GaveUp; }
                St::Jump(target, 1 + k)
            } else { St::Panic }
        },
        Ok((_v, _)) => { proof { lemma_cv(_v); } St::Panic },
        Err(Halt::Panic) => St::Panic,
        Err(Halt::GaveUp) => St::GaveUp,
    }
}

// ------------------------------------------------------------------ values, loads, `mut_free`

pub open spec fn all_mf(s: Seq<Val>) -> bool { forall|i: int| 0 <= i < s.len() ==> mut_free(#[trigger] s[i]) }

/// `mut_free` of an aggregate is `mut_free` of each element.
proof fn lemma_mf_seq(v: Val)
    requires v is Tup || v is Arr || v is Adt,
    ensures mut_free(v) == all_mf(match v { Val::Tup(s) => s, Val::Arr(s) => s, Val::Adt(_, s) => s, _ => seq![] }),
{
    let s = match v { Val::Tup(s) => s, Val::Arr(s) => s, Val::Adt(_, s) => s, _ => seq![] };
    if all_mf(s) {
        assert forall|i: int| 0 <= i < s.len() implies mut_free(#[trigger] s[i]) by {};
    } else {
        let i = choose|i: int| 0 <= i < s.len() && !mut_free(#[trigger] s[i]);
        assert(!mut_free(s[i]));
    }
}

pub fn x_mut_free(v: &CVal) -> (r: bool)
    ensures r == mut_free(cv(*v)),
    decreases v,
{
    proof { lemma_cv(*v); }
    match v {
        CVal::Mut(_) => false,
        CVal::Tup(vs) => { proof { lemma_mf_seq(cv(*v)); } mf_vec(vs) },
        CVal::Adt(_, vs) => { proof { lemma_mf_seq(cv(*v)); } mf_vec(vs) },
        CVal::Arr(vs) => { proof { lemma_mf_seq(cv(*v)); } mf_vec(vs) },
        CVal::Shr(b) => x_mut_free(&**b),
        _ => true,
    }
}

fn mf_vec(vs: &Vec<CVal>) -> (r: bool)
    ensures r == all_mf(cvs(vs@)),
    decreases vs,
{
    let mut i: usize = 0;
    while i < vs.len()
        invariant i <= vs@.len(), forall|q: int| 0 <= q < i ==> mut_free(#[trigger] cvs(vs@)[q]),
        decreases vs.len() - i,
    {
        if !x_mut_free(&vs[i]) {
            proof { assert(cvs(vs@)[i as int] == cv(vs@[i as int])); }
            return false;
        }
        proof { assert(cvs(vs@)[i as int] == cv(vs@[i as int])); }
        i += 1;
    }
    true
}

/// `mut_free` of what a navigation result reads.
fn nav_mut_free(n: (Option<&CVal>, Option<usize>), Ghost(t): Ghost<Val>) -> (r: bool)
    requires nav_ok(n, t),
    ensures r == mut_free(t),
{
    match n {
        (Some(x), None) => x_mut_free(x),
        (Some(x), Some(_)) => {
            proof { lemma_cv(*x); }
            match x { CVal::Adt(_, vs) => { proof { lemma_mf_seq(t); } mf_vec(vs) }, _ => false }
        },
        (None, _) => true,
    }
}

/// `load`, by reference.
pub fn loc_nav<'a>(fr: &'a CFrame, l: &CLoc) -> (r: Option<(Option<&'a CVal>, Option<usize>)>)
    ensures match r {
        Some(n) => load(fv(*fr), loc_v(*l)) matches Some(v) && nav_ok(n, v),
        None => load(fv(*fr), loc_v(*l)) is None,
    },
{
    let xp = xpath_of(&l.path);
    proof { lemma_xread_loc(base_v(fv(*fr), root_v(l.root)), xp@); }
    if !root_in(fr, &l.root) { return None; }
    Some(at(fr, &l.root, &xp))
}

// ------------------------------------------------------------------ std rows and leaves

/// A std row's or leaf's result against its spec: the value, the frame and the extra cost.
pub open spec fn std_ok(r: R<(CVal, u64)>, sp: Option<(Val, Frame, Seq<Event>, nat)>, f1: Frame) -> bool {
    match r {
        Ok((v, x)) => sp matches Some((w, f2, _, y)) && w == cv(v) && f2 == f1 && y == x as nat,
        Err(Halt::Panic) => sp is None,
        Err(Halt::GaveUp) => true,
    }
}

/// `shr_arr` of an owned value: its elements, moved out.
fn own_shr_arr(v: CVal) -> (r: Option<Vec<CVal>>)
    ensures match shr_arr(cv(v)) { Some(xs) => r matches Some(ys) && cvs(ys@) == xs, None => r is None },
{
    proof { lemma_cv(v); }
    match v {
        CVal::Shr(b) => { proof { lemma_cv(*b); } match *b { CVal::Arr(xs) => Some(xs), _ => None } },
        _ => None,
    }
}

fn int_arg_x(v: &CVal) -> (r: Option<u128>)
    ensures r == int_arg(cv(*v)),
{
    proof { lemma_cv(*v); }
    match v { CVal::Int(n) => Some(*n), _ => None }
}

/// `mut_arr`'s location and length.
fn mut_arr_x(fr: &CFrame, v: &CVal) -> (r: Option<(CLoc, usize)>)
    ensures match mut_arr(fv(*fr), cv(*v)) {
        Some((l, xs)) => r matches Some((cl, n)) && loc_v(cl) == l && xs.len() == n,
        None => r is None,
    },
{
    proof { lemma_cv(*v); }
    match v {
        CVal::Mut(l) => match loc_nav(fr, l) {
            Some(n) => match nav_arr_len(n, Ghost(load(fv(*fr), loc_v(*l))->Some_0)) { Some(k) => Some((clone_loc(l), k)), None => None },
            None => None,
        },
        _ => None,
    }
}

/// `vs`, moved out element by element.
fn split3(vs: Vec<CVal>) -> (r: (CVal, CVal, CVal))
    requires vs@.len() == 3,
    ensures cv(r.0) == cvs(vs@)[0], cv(r.1) == cvs(vs@)[1], cv(r.2) == cvs(vs@)[2],
{
    let mut vs = vs;
    let c = vs.pop().unwrap();
    let b = vs.pop().unwrap();
    let a = vs.pop().unwrap();
    (a, b, c)
}

fn split2(vs: Vec<CVal>) -> (r: (CVal, CVal))
    requires vs@.len() == 2,
    ensures cv(r.0) == cvs(vs@)[0], cv(r.1) == cvs(vs@)[1],
{
    let mut vs = vs;
    let b = vs.pop().unwrap();
    let a = vs.pop().unwrap();
    (a, b)
}

fn split1(vs: Vec<CVal>) -> (r: CVal)
    requires vs@.len() == 1,
    ensures cv(r) == cvs(vs@)[0],
{
    let mut vs = vs;
    vs.pop().unwrap()
}

/// `write_at` through one more step is `put` at the old path's leaf.
proof fn lemma_write_push(v: Val, p: Seq<PE>, e: PE, w: Val)
    ensures write_at(v, p.push(e), w) == write_at(v, p, put(read_at(v, p), e, w)),
    decreases p.len(),
{
    if p.len() == 0 {
        assert(p.push(e).drop_first().len() == 0);
        assert(p.push(e)[0] == e);
        reveal_with_fuel(write_at, 2);
    } else {
        assert(p.push(e).drop_first() =~= p.drop_first().push(e));
        assert(p.push(e)[0] == p[0]);
        lemma_write_push(get(v, p[0]), p.drop_first(), e, w);
    }
}

/// Appends `ys` to the `Arr` at `l` in place: `store` of the longer array.
fn push_loc(fr: &mut CFrame, l: &CLoc, ys: Vec<CVal>)
    requires load(fv(*old(fr)), loc_v(*l)) matches Some(Val::Arr(_)),
    ensures store(fv(*old(fr)), loc_v(*l), Val::Arr(load(fv(*old(fr)), loc_v(*l))->Some_0->Arr_0 + cvs(ys@))) == Some(fv(*final(fr))),
{
    proof { assert(l.path@.subrange(0, l.path@.len() as int) =~= l.path@); }
    match l.root {
        CRoot::Local(i) => {
            let ghost o = fr.locals@;
            let x = take_at(&mut fr.locals, i);
            let y = push_at(x, &l.path, 0, ys);
            fr.locals.set(i, y);
            proof { assert(fr.locals@ == o.update(i as int, y)); lemma_cvs_update(o, i as int, y); }
        },
        CRoot::Slot(j) => {
            let ghost o = fr.slots@;
            let x = take_at(&mut fr.slots, j);
            let y = push_at(x, &l.path, 0, ys);
            fr.slots.set(j, y);
            proof { assert(fr.slots@ == o.update(j as int, y)); lemma_cvs_update(o, j as int, y); }
        },
    }
}

#[allow(unused_variables)] // used in the specs
fn std_push(m: &MirCrate, dty: Option<Ty>, vs: Vec<CVal>, fr: &mut CFrame) -> (r: R<(CVal, u64)>)
    ensures std_ok(r, std_apply(*m, StdFn::VecPush, dty, cvs(vs@), fv(*old(fr))), fv(*final(fr))),
{
    if vs.len() != 2 { return Err(Halt::Panic); }
    let (a, x) = split2(vs);
    let (l, n) = match mut_arr_x(fr, &a) { Some(r) => r, None => return Err(Halt::Panic) };
    if n == usize::MAX { return Err(Halt::Panic); }
    let mut ys: Vec<CVal> = Vec::new();
    ys.push(x);
    proof {
        let xs = load(fv(*fr), loc_v(l))->Some_0->Arr_0;
        assert(cvs(ys@) =~= seq![cvs(vs@)[1]]);
        assert(xs.push(cvs(vs@)[1]) =~= xs + cvs(ys@));
    }
    push_loc(fr, &l, ys);
    Ok((CVal::Unit, 0))
}

#[allow(unused_variables)] // used in the specs
fn std_extend(m: &MirCrate, dty: Option<Ty>, vs: Vec<CVal>, fr: &mut CFrame) -> (r: R<(CVal, u64)>)
    ensures std_ok(r, std_apply(*m, StdFn::VecExtendFromSlice, dty, cvs(vs@), fv(*old(fr))), fv(*final(fr))),
{
    if vs.len() != 2 { return Err(Halt::Panic); }
    let (a, b) = split2(vs);
    let (l, n) = match mut_arr_x(fr, &a) { Some(r) => r, None => return Err(Halt::Panic) };
    let ys = match own_shr_arr(b) { Some(ys) => ys, None => return Err(Halt::Panic) };
    if n as u128 + ys.len() as u128 > 0xffff_ffff_ffff_ffff { return Err(Halt::Panic); }
    let k = ys.len() as u64;
    push_loc(fr, &l, ys);
    Ok((CVal::Unit, k))
}

#[allow(unused_variables)] // used in the specs
fn std_set(m: &MirCrate, dty: Option<Ty>, vs: Vec<CVal>, fr: &mut CFrame) -> (r: R<(CVal, u64)>)
    ensures std_ok(r, std_apply(*m, StdFn::VecSet, dty, cvs(vs@), fv(*old(fr))), fv(*final(fr))),
{
    if vs.len() != 3 { return Err(Halt::Panic); }
    let (a, b, w) = split3(vs);
    let (l, n) = match mut_arr_x(fr, &a) { Some(r) => r, None => return Err(Halt::Panic) };
    let i = match int_arg_x(&b) { Some(i) => i, None => return Err(Halt::Panic) };
    if i >= n as u128 { return Err(Halt::Panic); }
    let ghost f0 = fv(*fr);
    let ghost lv = loc_v(l);
    let ghost xs = load(f0, lv)->Some_0->Arr_0;
    let root = l.root;
    let mut path = l.path;
    let ghost p0 = path@;
    path.push(CPE::Index(i));
    let l2 = CLoc { root, path };
    proof {
        assert(pes(l2.path@) =~= pes(p0).push(PE::Index(i as nat)));
        lemma_write_push(base_v(f0, lv.root), lv.path, PE::Index(i as nat), cv(w));
        assert(put(Val::Arr(xs), PE::Index(i as nat), cv(w)) == Val::Arr(xs.update(i as int, cv(w))));
    }
    match e_store(fr, &l2, w) { Ok(()) => Ok((CVal::Unit, 0)), Err(_) => Err(Halt::Panic) }
}

/// The frame-preserving rows over a shared array argument.
#[allow(unused_variables)] // used in the specs
fn std_slices(m: &MirCrate, f: &StdFn, dty: Option<Ty>, vs: Vec<CVal>, fr: &CFrame) -> (r: R<(CVal, u64)>)
    requires *f is VecAsSlice || *f is ArrayAsSlice || *f is VecLen || *f is VecIndex || *f is SliceSubrange || *f is SliceToVec,
    ensures std_ok(r, std_apply(*m, *f, dty, cvs(vs@), fv(*fr)), fv(*fr)),
{
    let ghost vv = cvs(vs@);
    match f {
        StdFn::VecAsSlice | StdFn::ArrayAsSlice => {
            if vs.len() != 1 { return Err(Halt::Panic); }
            let a = split1(vs);
            proof { lemma_cv(a); }
            let ok = match &a { CVal::Shr(b) => { proof { lemma_cv(**b); } matches!(**b, CVal::Arr(_)) }, _ => false };
            if ok { Ok((a, 0)) } else { Err(Halt::Panic) }
        },
        StdFn::VecLen => {
            if vs.len() != 1 { return Err(Halt::Panic); }
            match own_shr_arr(split1(vs)) { Some(xs) => Ok((CVal::Int(xs.len() as u128), 0)), None => Err(Halt::Panic) }
        },
        StdFn::VecIndex => {
            if vs.len() != 2 { return Err(Halt::Panic); }
            let (a, b) = split2(vs);
            let i = match int_arg_x(&b) { Some(i) => i, None => return Err(Halt::Panic) };
            let mut xs = match own_shr_arr(a) { Some(xs) => xs, None => return Err(Halt::Panic) };
            if i >= xs.len() as u128 { return Err(Halt::Panic); }
            let ghost xo = xs@;
            let x = take_at(&mut xs, i as usize);
            proof { assert(cv(x) == cvs(xo)[i as int]); }
            Ok((CVal::Shr(Box::new(x)), 0))
        },
        StdFn::SliceSubrange => {
            if vs.len() != 3 { return Err(Halt::Panic); }
            let (a, b, c) = split3(vs);
            let lo = match int_arg_x(&b) { Some(i) => i, None => return Err(Halt::Panic) };
            let hi = match int_arg_x(&c) { Some(i) => i, None => return Err(Halt::Panic) };
            let mut xs = match own_shr_arr(a) { Some(xs) => xs, None => return Err(Halt::Panic) };
            if !(lo <= hi && hi <= xs.len() as u128) { return Err(Halt::Panic); }
            let ghost xo = cvs(xs@);
            let (lo, hi) = (lo as usize, hi as usize);
            let mut out: Vec<CVal> = Vec::new();
            let mut q = lo;
            while q < hi
                invariant lo <= q <= hi <= xs@.len(), xo.len() == xs@.len(), out@.len() == q - lo,
                    forall|z: int| 0 <= z < q - lo ==> cv(#[trigger] out@[z]) == xo[lo + z],
                    forall|z: int| q <= z < xs@.len() ==> cv(#[trigger] xs@[z]) == xo[z],
                decreases hi - q,
            {
                out.push(take_at(&mut xs, q));
                q += 1;
            }
            let v = CVal::Arr(out);
            proof { lemma_cv(v); assert(cvs(out@) =~= xo.subrange(lo as int, hi as int)); }
            Ok((CVal::Shr(Box::new(v)), 0))
        },
        _ => {
            if vs.len() != 1 { return Err(Halt::Panic); }
            match own_shr_arr(split1(vs)) {
                Some(xs) => {
                    let k = xs.len() as u64;
                    let v = CVal::Arr(xs);
                    proof { lemma_cv(v); }
                    Ok((v, k))
                },
                None => Err(Halt::Panic),
            }
        },
    }
}

fn t_sized(m: &MirCrate, tb: &Tabs, t: Ty) -> (r: bool)
    requires tabs_ok(*m, *tb),
    ensures r == sized(*m, t),
{
    match t_rigid(m, tb, t) {
        Some(r) => !(matches!(r, RigidTy::Str) || matches!(r, RigidTy::Slice(_)) || matches!(r, RigidTy::Dynamic(_, _))),
        None => false,
    }
}

/// `zst_dest(m, t)`, through `Tabs` (`GaveUp` past a cap).
fn t_zst_dest(m: &MirCrate, tb: &Tabs, t: Ty) -> (r: R<bool>)
    requires tabs_ok(*m, *tb),
    ensures r matches Ok(z) ==> z == zst_dest(*m, t), !(r matches Err(Halt::Panic)),
{
    let tf = match crate::look::x_tfuel(m) { Some(f) => f, None => return Err(Halt::GaveUp) };
    if !t_sized(m, tb, t) { return Ok(false); }
    let ul = match crate::eval_const::e_unit_like(m, tb, t, tf, false) { Ok(_) => true, Err(Halt::Panic) => false, Err(Halt::GaveUp) => return Err(Halt::GaveUp) };
    Ok(ul && match t_layout(m, tb, t) { Some(l) => l.size.num_bits == 0, None => true })
}

/// A ghost result: the destination type's `ul_val`, if it is a `zst_dest`.
#[allow(unused_variables)] // used in the specs
fn ghost_unit(m: &MirCrate, tb: &Tabs, dty: Option<Ty>, fr: &CFrame) -> (r: R<(CVal, u64)>)
    requires tabs_ok(*m, *tb),
    ensures std_ok(r, match dty {
        Some(t) => if zst_dest(*m, t) { Some((ul_val(*m, t), fv(*fr), seq![], 0nat)) } else { None },
        None => None,
    }, fv(*fr)),
{
    let t = match dty { Some(t) => t, None => return Err(Halt::Panic) };
    if !t_zst_dest(m, tb, t)? { return Err(Halt::Panic); }
    Ok((crate::eval_const::e_ul_val(m, tb, t)?, 0))
}

/// `std_apply`: a std row's result, the frame in place, and its extra cost.
pub fn e_std_apply(m: &MirCrate, tb: &Tabs, f: &StdFn, dty: Option<Ty>, vs: Vec<CVal>, fr: &mut CFrame) -> (r: R<(CVal, u64)>)
    requires tabs_ok(*m, *tb),
    ensures std_ok(r, std_apply(*m, *f, dty, cvs(vs@), fv(*old(fr))), fv(*final(fr))),
{
    match f {
        StdFn::VecNew | StdFn::VecWithCapacity => {
            let ok = match f {
                StdFn::VecNew => vs.len() == 0,
                _ => vs.len() == 1 && { proof { lemma_cv(vs@[0]); } matches!(vs[0], CVal::Int(_)) },
            };
            if !ok { return Err(Halt::Panic); }
            let v = CVal::Arr(Vec::new());
            proof { lemma_cv(v); assert(cvs(Seq::<CVal>::empty()) =~= Seq::<Val>::empty()); }
            Ok((v, 0))
        },
        StdFn::VecPush => std_push(m, dty, vs, fr),
        StdFn::VecExtendFromSlice => std_extend(m, dty, vs, fr),
        StdFn::VecSet => std_set(m, dty, vs, fr),
        StdFn::Wrapping(op, it) => {
            if vs.len() != 2 { return Err(Halt::Panic); }
            let (a, b) = split2(vs);
            match (int_arg_x(&a), int_arg_x(&b)) {
                (Some(x), Some(y)) => Ok((CVal::Int(crate::interp_arith::binop_exec(op, it, x, y)), 0)),
                _ => Err(Halt::Panic),
            }
        },
        StdFn::GhostNew => ghost_unit(m, tb, dty, fr),
        _ => std_slices(m, f, dty, vs, fr),
    }
}

/// `leaf_call`: a policy or std-model call.
pub fn e_leaf_call(m: &MirCrate, tb: &Tabs, pol: &Policy, key: &[u8], g: &GenericArgs, dty: Option<Ty>, vs: Vec<CVal>, fr: &mut CFrame)
    -> (r: R<(CVal, u64)>)
    requires tabs_ok(*m, *tb),
    ensures std_ok(r, leaf_call(*m, cpol(*pol), key@, *g, dty, cvs(vs@), fv(*old(fr))), fv(*final(fr))),
{
    proof { lemma_set_of(pol.declassify@, key@); lemma_set_of(pol.ghost_unit@, key@); }
    if has_exec(&pol.declassify, key) {
        if vs.len() != 1 { return Err(Halt::Panic); }
        Ok((split1(vs), 0))
    } else if has_exec(&pol.ghost_unit, key) {
        ghost_unit(m, tb, dty, fr)
    } else {
        match crate::look::x_std_model(m, key, g) { Some(f) => e_std_apply(m, tb, &f, dty, vs, fr), None => Err(Halt::Panic) }
    }
}

// ------------------------------------------------------------------ body calls

/// A body call's result against `body_call`.
pub open spec fn bc_ok(r: Result<(CVal, u64), Ev>, sp: Result<(Val, Frame, Seq<Event>, nat), Out>, f1: Frame) -> bool {
    match r {
        Ok((v, x)) => sp matches Ok((w, f2, _, y)) && w == cv(v) && f2 == f1 && y == x as nat,
        Err(Ev::Panic) => sp matches Err(Out::Panic),
        Err(Ev::Fuel) => sp matches Err(Out::Fuel),
        Err(_) => true,
    }
}

/// `args_ok`.
#[verifier::loop_isolation(false)]
fn e_args_ok(m: &MirCrate, tb: &Tabs, cb: &Body, fr: &CFrame, vs: &Vec<CVal>) -> (r: bool)
    requires tabs_ok(*m, *tb),
    ensures r == args_ok(*m, *cb, fv(*fr), cvs(vs@)),
{
    if !(vs.len() == cb.arg_count && cb.arg_count < cb.locals.len()) { return false; }
    let ghost vv = cvs(vs@);
    let mut q: usize = 0;
    while q < vs.len()
        invariant q <= vs@.len() == cb.arg_count < cb.locals@.len(), tabs_ok(*m, *tb), vv == cvs(vs@),
            forall|p: int| 0 <= p < q ==> arg_ok(*m, *cb, fv(*fr), vv, p),
        decreases vs.len() - q,
    {
        proof { lemma_cv(vs@[q as int]); }
        let ok = if t_is_mut_ref(m, tb, cb.locals[q + 1].ty) {
            match &vs[q] {
                CVal::Mut(l) => match loc_nav(fr, l) { Some(n) => nav_mut_free(n, Ghost(load(fv(*fr), loc_v(*l))->Some_0)), None => false },
                _ => false,
            }
        } else {
            x_mut_free(&vs[q])
        };
        proof { assert(cvs(vs@)[q as int] == cv(vs@[q as int])); }
        if !ok { proof { assert(!arg_ok(*m, *cb, fv(*fr), vv, q as int)); } return false; }
        q += 1;
    }
    true
}

/// `call_slots` (the `&mut` pointees, copied in) and each `&mut` argument's location.
#[verifier::loop_isolation(false)]
fn e_call_slots(m: &MirCrate, tb: &Tabs, cb: &Body, fr: &CFrame, vs: &Vec<CVal>) -> (r: (Vec<CVal>, Vec<Option<CLoc>>))
    requires tabs_ok(*m, *tb), args_ok(*m, *cb, fv(*fr), cvs(vs@)),
    ensures cvs(r.0@) == call_slots(*m, *cb, fv(*fr), cvs(vs@)), r.1@.len() == vs@.len(),
        forall|q: int| 0 <= q < vs@.len() && is_mut_ref(*m, cb.locals@[q + 1].ty) ==> ((#[trigger] r.1@[q]) matches Some(l) && cvs(vs@)[q] == Val::Mut(loc_v(l))),
{
    let ghost vv = cvs(vs@);
    let mut sl: Vec<CVal> = Vec::new();
    let mut ls: Vec<Option<CLoc>> = Vec::new();
    let mut q: usize = 0;
    while q < vs.len()
        invariant q <= vs@.len(), tabs_ok(*m, *tb), vv == cvs(vs@), args_ok(*m, *cb, fv(*fr), vv), sl@.len() == q, ls@.len() == q,
            forall|p: int| 0 <= p < q ==> cv(#[trigger] sl@[p]) == call_slots(*m, *cb, fv(*fr), vv)[p],
            forall|p: int| 0 <= p < q && is_mut_ref(*m, cb.locals@[p + 1].ty) ==> ((#[trigger] ls@[p]) matches Some(l) && vv[p] == Val::Mut(loc_v(l))),
        decreases vs.len() - q,
    {
        proof { lemma_cv(vs@[q as int]); assert(arg_ok(*m, *cb, fv(*fr), vv, q as int)); }
        if t_is_mut_ref(m, tb, cb.locals[q + 1].ty) {
            match &vs[q] {
                CVal::Mut(l) => {
                    let x = match loc_nav(fr, l) { Some(n) => take(n), None => CVal::Unit };
                    sl.push(x);
                    ls.push(Some(clone_loc(l)));
                },
                _ => { sl.push(CVal::Unit); ls.push(None); },
            }
        } else {
            sl.push(CVal::Unit);
            ls.push(None);
        }
        q += 1;
    }
    proof { assert(cvs(sl@) =~= call_slots(*m, *cb, fv(*fr), vv)); }
    (sl, ls)
}

proof fn lemma_wb_none(m: MirCrate, cb: Body, fr: Frame, vs: Seq<Val>, cs: Seq<Val>, k: nat, n: nat)
    requires k <= n, write_back(m, cb, fr, vs, cs, k) is None,
    ensures write_back(m, cb, fr, vs, cs, n) is None,
    decreases n - k,
{
    if k < n { lemma_wb_none(m, cb, fr, vs, cs, k, (n - 1) as nat); }
}

/// `write_back`: the callee's final slots stored at the `&mut` arguments' locations, in order.
#[verifier::loop_isolation(false)]
fn e_write_back(m: &MirCrate, tb: &Tabs, cb: &Body, Ghost(vv): Ghost<Seq<Val>>, ls: &Vec<Option<CLoc>>, cs: Vec<CVal>, fr: &mut CFrame) -> (r: bool)
    requires tabs_ok(*m, *tb), vv.len() < cb.locals@.len(), ls@.len() == vv.len(),
        forall|q: int| 0 <= q < vv.len() && is_mut_ref(*m, cb.locals@[q + 1].ty) ==> ((#[trigger] ls@[q]) matches Some(l) && vv[q] == Val::Mut(loc_v(l))),
    ensures match write_back(*m, *cb, fv(*old(fr)), vv, cvs(cs@), vv.len()) { Some(f) => r && f == fv(*final(fr)), None => !r },
{
    let ghost f0 = fv(*fr);
    let ghost c0 = cvs(cs@);
    let mut cs = cs;
    let mut q: usize = 0;
    while q < ls.len()
        invariant q <= ls@.len() == vv.len() < cb.locals@.len(), tabs_ok(*m, *tb), cs@.len() == c0.len(),
            forall|p: int| q <= p < cs@.len() ==> cv(#[trigger] cs@[p]) == c0[p],
            forall|p: int| 0 <= p < vv.len() && is_mut_ref(*m, cb.locals@[p + 1].ty) ==> ((#[trigger] ls@[p]) matches Some(l) && vv[p] == Val::Mut(loc_v(l))),
            write_back(*m, *cb, f0, vv, c0, q as nat) == Some(fv(*fr)),
        decreases ls.len() - q,
    {
        proof { if (q as int) < cs@.len() { assert(c0[q as int] == cv(cs@[q as int])); } }
        if t_is_mut_ref(m, tb, cb.locals[q + 1].ty) {
            if !(q < cs.len() && x_mut_free(&cs[q])) {
                proof {
                    assert(write_back(*m, *cb, f0, vv, c0, (q + 1) as nat) is None);
                    lemma_wb_none(*m, *cb, f0, vv, c0, (q + 1) as nat, vv.len()); }
                return false;
            }
            let l = match &ls[q] { Some(l) => l, None => { proof { assert(false); } return false } };
            let x = take_at(&mut cs, q);
            match e_store(fr, l, x) {
                Ok(()) => {},
                Err(_) => {
                    proof {
                        assert(write_back(*m, *cb, f0, vv, c0, (q + 1) as nat) is None);
                        lemma_wb_none(*m, *cb, f0, vv, c0, (q + 1) as nat, vv.len()); }
                    return false;
                },
            }
        }
        q += 1;
    }
    true
}

/// `return_to`: the callee's (mut-free) return value, and the caller's frame after write-back.
fn e_return_to(m: &MirCrate, tb: &Tabs, cb: &Body, Ghost(vv): Ghost<Seq<Val>>, ls: &Vec<Option<CLoc>>, cf: CFrame, fr: &mut CFrame)
    -> (r: Option<CVal>)
    requires tabs_ok(*m, *tb), vv.len() < cb.locals@.len(), ls@.len() == vv.len(),
        forall|q: int| 0 <= q < vv.len() && is_mut_ref(*m, cb.locals@[q + 1].ty) ==> ((#[trigger] ls@[q]) matches Some(l) && vv[q] == Val::Mut(loc_v(l))),
    ensures match return_to(*m, *cb, fv(*old(fr)), vv, fv(cf)) {
        Some((w, f2)) => r matches Some(v) && cv(v) == w && f2 == fv(*final(fr)),
        None => r is None,
    },
{
    let CFrame { locals: mut cl, slots: cs } = cf;
    if cl.len() == 0 || !x_mut_free(&cl[0]) { return None; }
    if !e_write_back(m, tb, cb, Ghost(vv), ls, cs, fr) { return None; }
    let ghost c0 = cvs(cl@);
    let v = take_at(&mut cl, 0);
    proof { assert(cv(v) == c0[0]); }
    Some(v)
}

/// The callee's run, on 1 less fuel.
fn e_sub_run(m: &MirCrate, tb: &Tabs, pol: &Policy, Ghost(s): Ghost<Set<nat>>, Ghost(rs): Ghost<spec_fn(nat) -> Set<nat>>,
    j: usize, cf: CFrame, fuel: u64) -> (r: Ev)
    requires tabs_ok(*m, *tb), closed(*m, cpol(*pol), s, rs), s.contains(j as nat), fuel > 0,
    ensures ev_ok(mir_run(*m, cpol(*pol), j as nat, fv(cf), (fuel - 1) as nat), r),
    decreases fuel, 0nat,
{
    hide(mir_run);
    hide(closed);
    e_run(m, tb, pol, Ghost(s), Ghost(rs), j, cf, fuel - 1)
}

/// `body_call`: the fuel check, `args_ok`, entry with the `&mut` slots, the run on 1 less fuel,
/// then `return_to` with write-back in parameter order.
fn e_body_call(m: &MirCrate, tb: &Tabs, pol: &Policy, Ghost(s): Ghost<Set<nat>>, Ghost(rs): Ghost<spec_fn(nat) -> Set<nat>>,
    j: usize, cb: &Body, vs: Vec<CVal>, fr: &mut CFrame, fuel: u64) -> (r: Result<(CVal, u64), Ev>)
    requires tabs_ok(*m, *tb), closed(*m, cpol(*pol), s, rs), s.contains(j as nat), inst_body(*m, j as nat) == Some(*cb),
    ensures bc_ok(r, body_call(*m, cpol(*pol), j as nat, *cb, cvs(vs@), fv(*old(fr)), fuel as nat), fv(*final(fr))),
    decreases fuel, 1nat,
{
    if fuel == 0 { return Err(Ev::Fuel); }
    if !e_args_ok(m, tb, cb, fr, &vs) { return Err(Ev::Panic); }
    let ghost vv = cvs(vs@);
    let (sl, ls) = e_call_slots(m, tb, cb, fr, &vs);
    let cf = match e_mir_entry(m, tb, j, vs, sl) { Ok(cf) => cf, Err(_) => return Err(Ev::GaveUp) };
    match e_sub_run(m, tb, pol, Ghost(s), Ghost(rs), j, cf, fuel) {
        Ev::Done(cf2, n) => match e_return_to(m, tb, cb, Ghost(vv), &ls, cf2, fr) {
            Some(v) => Ok((v, n)),
            None => Err(Ev::Panic),
        },
        Ev::Panic => Err(Ev::Panic),
        Ev::Fuel => Err(Ev::Fuel),
        Ev::GaveUp => Err(Ev::GaveUp),
    }
}

// ------------------------------------------------------------------ calls and drops

fn e_call_step(m: &MirCrate, tb: &Tabs, pol: &Policy, Ghost(s): Ghost<Set<nat>>, Ghost(rs): Ghost<spec_fn(nat) -> Set<nat>>,
    b: &Body, func: &Operand, args: &Vec<Operand>, dest: &Place, tgt: usize, fr: &mut CFrame, fuel: u64) -> (r: St)
    requires tabs_ok(*m, *tb), closed(*m, cpol(*pol), s, rs),
        callee_of(*m, *func) matches Some((j2, g)) ==> is_leaf(*m, cpol(*pol), m.insts@[j2 as int].key@, g) || s.contains(j2),
    ensures st_ok(fv(*final(fr)), r, call_step(*m, cpol(*pol), *b, *func, args@, *dest, tgt as nat, fv(*old(fr)), fuel as nat)),
        r matches St::Jump(t, _) ==> t == tgt,
    decreases fuel, 3nat,
{
    let (j2, g) = match t_callee_of(m, tb, func) { Some(x) => x, None => return St::GaveUp };
    let (vs, k1) = match e_eval_ops(m, tb, fr, args) { Ok(x) => x, Err(Halt::Panic) => return St::Panic, Err(Halt::GaveUp) => return St::GaveUp };
    let c = match e_eval_place(fr, dest) { Ok(c) => c, Err(_) => return St::Panic };
    if !c.loc { return St::Panic; }
    let l = cur_loc(c);
    let key = m.insts[j2].key.as_slice();
    let (v, x) = if crate::look::x_is_leaf(m, pol, key, g) {
        match e_leaf_call(m, tb, pol, key, g, t_place_ty(m, tb, b, dest), vs, fr) {
            Ok(r) => r,
            Err(Halt::Panic) => return St::Panic,
            Err(Halt::GaveUp) => return St::GaveUp,
        }
    } else {
        let cb = match t_inst_body(m, tb, j2) { Some(cb) => cb, None => return St::GaveUp };
        match e_body_call(m, tb, pol, Ghost(s), Ghost(rs), j2, cb, vs, fr, fuel) {
            Ok(r) => r,
            Err(Ev::Panic) => return St::Panic,
            Err(Ev::Fuel) => return St::Fuel,
            Err(_) => return St::GaveUp,
        }
    };
    match e_store(fr, &l, v) { Ok(()) => {}, Err(_) => return St::Panic }
    if k1 == u64::MAX || 1 + k1 > u64::MAX - x { return St::GaveUp; }
    St::Jump(tgt, 1 + k1 + x)
}

fn t_vec_int(m: &MirCrate, tb: &Tabs, t: Ty) -> (r: bool)
    requires tabs_ok(*m, *tb),
    ensures r == vec_int(*m, t),
{
    match t_vec_elem(m, tb, t) {
        Some(e) => match t_int_ty(m, tb, e) { Some(it) => !matches!(it, ctcore::syntax::IntTy::Bool), None => false },
        None => false,
    }
}

fn e_drop_step(m: &MirCrate, tb: &Tabs, pol: &Policy, Ghost(s): Ghost<Set<nat>>, Ghost(rs): Ghost<spec_fn(nat) -> Set<nat>>,
    b: &Body, place: &Place, tgt: usize, fr: &mut CFrame, fuel: u64) -> (r: St)
    requires tabs_ok(*m, *tb), closed(*m, cpol(*pol), s, rs),
        place_ty(*m, *b, *place) matches Some(t) ==> (drop_row(*m, t) matches Some(d) ==>
            (d.empty || vec_int(*m, t) || (glue_of(*m, d.glue) matches Some((j2, _)) && s.contains(j2)))),
    ensures st_ok(fv(*final(fr)), r, drop_step(*m, cpol(*pol), *b, *place, tgt as nat, fv(*old(fr)), fuel as nat)),
        r matches St::Jump(t, _) ==> t == tgt,
    decreases fuel, 3nat,
{
    let t = match t_place_ty(m, tb, b, place) { Some(t) => t, None => return St::GaveUp };
    let c = match e_eval_place(fr, place) { Ok(c) => c, Err(_) => return St::Panic };
    if !c.loc { return St::Panic; }
    let d = match t_drop_row(m, tb, t) { Some(d) => d, None => return St::GaveUp };
    if d.empty || t_vec_int(m, tb, t) { return St::Jump(tgt, 1); }
    let j2 = match t_inst_idx(m, tb, d.glue) { Some(j2) => j2, None => return St::GaveUp };
    let gb = match t_inst_body(m, tb, j2) { Some(gb) => gb, None => return St::GaveUp };
    e_drop_glue(m, tb, pol, Ghost(s), Ghost(rs), j2, gb, cur_loc(c), tgt, fr, fuel)
}

/// Drop glue: `body_call` on `&mut place` (slot 0, written back), costing 2 plus its steps.
fn e_drop_glue(m: &MirCrate, tb: &Tabs, pol: &Policy, Ghost(s): Ghost<Set<nat>>, Ghost(rs): Ghost<spec_fn(nat) -> Set<nat>>,
    j2: usize, gb: &Body, l: CLoc, tgt: usize, fr: &mut CFrame, fuel: u64) -> (r: St)
    requires tabs_ok(*m, *tb), closed(*m, cpol(*pol), s, rs), s.contains(j2 as nat), inst_body(*m, j2 as nat) == Some(*gb),
    ensures st_ok(fv(*final(fr)), r, match body_call(*m, cpol(*pol), j2 as nat, *gb, seq![Val::Mut(loc_v(l))], fv(*old(fr)), fuel as nat) {
            Ok((_, f2, e2, s2)) => Step::Jump(tgt as nat, f2, e2, 2 + s2),
            Err(o) => Step::Stop(o),
        }),
    decreases fuel, 2nat,
{
    hide(body_call);
    hide(closed);
    let ml = CVal::Mut(l);
    let mut vs: Vec<CVal> = Vec::new();
    vs.push(ml);
    proof { assert(cvs(vs@) =~= seq![cv(ml)]); }
    match e_body_call(m, tb, pol, Ghost(s), Ghost(rs), j2, gb, vs, fr, fuel) {
        Ok((_, s2)) => if s2 > u64::MAX - 2 { St::GaveUp } else { St::Jump(tgt, 2 + s2) },
        Err(Ev::Panic) => St::Panic,
        Err(Ev::Fuel) => St::Fuel,
        Err(_) => St::GaveUp,
    }
}

/// `step_term`.
#[allow(unused_variables)] // used in the specs
fn e_step_term(m: &MirCrate, tb: &Tabs, pol: &Policy, Ghost(s): Ghost<Set<nat>>, Ghost(rs): Ghost<spec_fn(nat) -> Set<nat>>,
    j: usize, b: &Body, bb: usize, fr: &mut CFrame, fuel: u64) -> (r: St)
    requires
        tabs_ok(*m, *tb), closed(*m, cpol(*pol), s, rs), bb < b.blocks@.len(), fuel > 0,
        succs_in(b.blocks@[bb as int].terminator.kind, rs(j as nat)),
        callees_in(*m, cpol(*pol), *b, b.blocks@[bb as int].terminator.kind, s),
    ensures
        st_ok(fv(*final(fr)), r, step_term(*m, cpol(*pol), *b, b.blocks@[bb as int].terminator.kind, fv(*old(fr)), fuel as nat)),
        r matches St::Jump(t, _) ==> rs(j as nat).contains(t as nat),
    decreases fuel, 4nat,
{
    match &b.blocks[bb].terminator.kind {
        TerminatorKind::Goto { target } => St::Jump(*target, 1),
        TerminatorKind::SwitchInt { discr, targets } => e_switch(m, tb, fr, discr, targets),
        TerminatorKind::Assert { cond, expected, msg: _, target, unwind: _ } => e_assert(m, tb, fr, cond, *expected, *target),
        TerminatorKind::Return => St::Ret(1),
        TerminatorKind::Unreachable | TerminatorKind::Abort => St::Panic,
        TerminatorKind::Drop { place, target, unwind: _ } => e_drop_step(m, tb, pol, Ghost(s), Ghost(rs), b, place, *target, fr, fuel),
        TerminatorKind::Call { func, args, destination, target, unwind: _ } => match target {
            Some(t) => e_call_step(m, tb, pol, Ghost(s), Ghost(rs), b, func, args, destination, *t, fr, fuel),
            None => St::Panic,
        },
        _ => St::GaveUp,
    }
}

// ------------------------------------------------------------------ runs

/// `cur` is what remains of `o0` after `k` steps.
pub open spec fn rel_out(o0: Out, cur: Out, k: nat) -> bool {
    match cur {
        Out::Done(g, _, n) => o0 matches Out::Done(g0, _, n0) && g0 == g && n0 == n + k,
        Out::Panic => o0 is Panic,
        Out::Fuel => o0 is Fuel,
        Out::Unsup => o0 is Unsup,
    }
}

/// `run_block` from block `bb` of instance `j`'s body, looping over the jumps.
#[verifier::loop_isolation(false)]
fn e_blocks(m: &MirCrate, tb: &Tabs, pol: &Policy, Ghost(s): Ghost<Set<nat>>, Ghost(rs): Ghost<spec_fn(nat) -> Set<nat>>,
    j: usize, b: &Body, fr: CFrame, fuel: u64) -> (r: Ev)
    requires
        tabs_ok(*m, *tb), closed(*m, cpol(*pol), s, rs), s.contains(j as nat), inst_body(*m, j as nat) == Some(*b),
    ensures ev_ok(run_block(*m, cpol(*pol), *b, 0, fv(fr), fuel as nat), r),
    decreases fuel, 5nat,
{
    let ghost p = cpol(*pol);
    let ghost o0 = run_block(*m, p, *b, 0, fv(fr), fuel as nat);
    proof { lemma_entry_in(*m, p, s, rs, j as nat); }
    let mut fr = fr;
    let mut bb: usize = 0;
    let mut fc: u64 = fuel;
    let mut steps: u64 = 0;
    loop
        invariant
            fc <= fuel, rs(j as nat).contains(bb as nat),
            rel_out(o0, run_block(*m, p, *b, bb as nat, fv(fr), fc as nat), steps as nat),
        decreases fc,
    {
        if fc == 0 { return Ev::Fuel; }
        proof { lemma_in(*m, p, s, rs, j as nat, *b, bb as nat); }
        let ghost f0 = fv(fr);
        let blk = &b.blocks[bb];
        let n1 = match e_exec_stmts(m, tb, b, &mut fr, &blk.statements) {
            Ok(n) => n,
            Err(Halt::Panic) => return Ev::Panic,
            Err(Halt::GaveUp) => return Ev::GaveUp,
        };
        let st = e_step_term(m, tb, pol, Ghost(s), Ghost(rs), j, b, bb, &mut fr, fc);
        match st {
            St::Jump(t, n2) => {
                if steps > u64::MAX - n1 || steps + n1 > u64::MAX - n2 { return Ev::GaveUp; }
                steps = steps + n1 + n2;
                bb = t;
            },
            St::Ret(n2) => {
                if steps > u64::MAX - n1 || steps + n1 > u64::MAX - n2 { return Ev::GaveUp; }
                return Ev::Done(fr, steps + n1 + n2);
            },
            St::Panic => return Ev::Panic,
            St::Fuel => return Ev::Fuel,
            St::GaveUp => return Ev::GaveUp,
        }
        fc = fc - 1;
    }
}

/// `mir_run` of instance `j` from `fr`.
pub fn e_run(m: &MirCrate, tb: &Tabs, pol: &Policy, Ghost(s): Ghost<Set<nat>>, Ghost(rs): Ghost<spec_fn(nat) -> Set<nat>>,
    j: usize, fr: CFrame, fuel: u64) -> (r: Ev)
    requires tabs_ok(*m, *tb), closed(*m, cpol(*pol), s, rs), s.contains(j as nat),
    ensures ev_ok(mir_run(*m, cpol(*pol), j as nat, fv(fr), fuel as nat), r),
    decreases fuel, 6nat,
{
    match t_inst_body(m, tb, j) {
        Some(b) => e_blocks(m, tb, pol, Ghost(s), Ghost(rs), j, b, fr, fuel),
        None => Ev::GaveUp,
    }
}

/// **The evaluator.** A `Done`, `Panic` or `Fuel` is `mir_run`'s from `mir_entry` (addendum
/// decision 2).
pub fn mir_eval(m: &MirCrate, tb: &Tabs, pol: &Policy, i: usize, args: &Vec<CVal>, slots: &Vec<CVal>, fuel: u64) -> (r: Ev)
    requires tabs_ok(*m, *tb), in_subset(*m, cpol(*pol), i as nat),
    ensures ev_ok(mir_run(*m, cpol(*pol), i as nat, mir_entry(*m, i as nat, cvs(args@), cvs(slots@)), fuel as nat), r),
{
    let ghost (s, rs) = choose|s: Set<nat>, rs: spec_fn(nat) -> Set<nat>| #[trigger] closed(*m, cpol(*pol), s, rs) && s.contains(i as nat);
    match e_mir_entry(m, tb, i, clone_vec(args), clone_vec(slots)) {
        Ok(fr) => e_run(m, tb, pol, Ghost(s), Ghost(rs), i, fr, fuel),
        Err(_) => Ev::GaveUp,
    }
}

} // verus!
