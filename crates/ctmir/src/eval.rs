//! The MIR evaluator, part one: exec mirrors of `sem`'s places, operands, rvalues, statements and
//! entry frame, each proved to give the spec's result. A mirror's `Ok(x)` is the spec's `Some` of
//! `x`'s view, its `Err(Halt::Panic)` is the spec's `None`, and `Err(Halt::GaveUp)` claims nothing.
//! Lookups go through `Tabs` (`eval_tab`); no events are built; frames are updated in place
//! (`interp_val`), and a read navigates by reference and clones only what it returns.
use crate::eval_const::*;
use crate::eval_tab::*;
#[allow(unused_imports)]
use crate::interp_arith::*;
use crate::interp_val::*;
use crate::look::{x_tfuel, x_ty_free};
use crate::mir::*;
#[cfg(verus_keep_ghost)]
use crate::sem::*;
#[cfg(verus_keep_ghost)]
use crate::sim_entry::{pointee, wt_args};
#[cfg(verus_keep_ghost)]
use ctcore::sem::{bits, Event, Frame, Loc, Root, PE};
use ctcore::sem::Val;
use ctcore::syntax::{BinOp as COp, IntTy as CTy, UnOp as CUn};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

verus! {

/// Why an evaluation stopped short of a value: `Panic` claims the spec gives `None` (or
/// `Out::Panic`); `GaveUp` (a cap, a count past `u64`, an arm the evaluator leaves out) claims
/// nothing.
pub enum Halt { Panic, GaveUp }

pub type R<T> = Result<T, Halt>;

/// A value-and-charge mirror's contract against a spec giving value, events and charge.
pub open spec fn r_val(r: R<(CVal, u64)>, s: Option<(Val, Seq<Event>, nat)>) -> bool {
    match r {
        Ok((v, k)) => s matches Some((w, _, j)) && w == cv(v) && j == k as nat,
        Err(Halt::Panic) => s is None,
        Err(Halt::GaveUp) => true,
    }
}

pub open spec fn r_vals(r: R<(Vec<CVal>, u64)>, s: Option<(Seq<Val>, Seq<Event>, nat)>) -> bool {
    match r {
        Ok((vs, k)) => s matches Some((ws, _, j)) && ws == cvs(vs@) && j == k as nat,
        Err(Halt::Panic) => s is None,
        Err(Halt::GaveUp) => true,
    }
}

// ------------------------------------------------------------------ cursors

/// An evaluated place: at a location (`loc`, a `Snap`-free path from a frame root), or inside a
/// snapshot reached through a `Shr` (`Snap` steps).
pub struct ECur { pub root: CRoot, pub path: Vec<XPE>, pub loc: bool }

pub open spec fn ecur_v(fr: Frame, c: ECur) -> PRes {
    if c.loc { PRes::At(Loc { root: root_v(c.root), path: xpes(c.path@) }) } else { PRes::Snap(xread(base_v(fr, root_v(c.root)), c.path@)) }
}

pub open spec fn ecur_wf(c: ECur) -> bool { c.loc ==> no_snap(c.path@) }

pub open spec fn xpe_pe(e: XPE) -> PE {
    match e { XPE::Field(f) => PE::Field(f as nat), XPE::Index(x) => PE::Index(x as nat), XPE::Variant(k) => PE::Variant(k as nat), XPE::Snap => PE::Field(0) }
}

fn root_in(fr: &CFrame, r: &CRoot) -> (b: bool)
    ensures b == root_val(fv(*fr), root_v(*r)) is Some,
{
    match r { CRoot::Local(i) => *i < fr.locals.len(), CRoot::Slot(j) => *j < fr.slots.len() }
}

fn copy_root(r: &CRoot) -> (s: CRoot)
    ensures s == *r,
{
    match r { CRoot::Local(i) => CRoot::Local(*i), CRoot::Slot(j) => CRoot::Slot(*j) }
}

/// What a cursor reads: its snapshot, or its location's value when the root is in the frame.
proof fn lemma_cur_val(fr: Frame, c: ECur)
    requires ecur_wf(c),
    ensures
        pres_val(fr, ecur_v(fr, c)) == if !c.loc || root_val(fr, root_v(c.root)) is Some { Some(xread(base_v(fr, root_v(c.root)), c.path@)) } else { None::<Val> },
{
    if c.loc { lemma_xread_loc(base_v(fr, root_v(c.root)), c.path@); }
}

/// The cursor's value by reference; `None` exactly when `pres_val` is `None`.
fn cur_nav<'a>(fr: &'a CFrame, c: &ECur) -> (r: Option<(Option<&'a CVal>, Option<usize>)>)
    requires ecur_wf(*c),
    ensures match r {
        Some(n) => pres_val(fv(*fr), ecur_v(fv(*fr), *c)) == Some(xread(base_v(fv(*fr), root_v(c.root)), c.path@))
            && nav_ok(n, xread(base_v(fv(*fr), root_v(c.root)), c.path@)),
        None => pres_val(fv(*fr), ecur_v(fv(*fr), *c)) is None,
    },
{
    proof { lemma_cur_val(fv(*fr), *c); }
    if c.loc && !root_in(fr, &c.root) { return None; }
    Some(at(fr, &c.root, &c.path))
}

/// One non-`Snap` step pushed onto a cursor: `extend`.
#[allow(unused_variables)] // used in the specs
fn cur_push(fr: &CFrame, c: ECur, e: XPE) -> (d: ECur)
    requires ecur_wf(c), !(e is Snap),
    ensures ecur_wf(d), ecur_v(fv(*fr), d) == extend(ecur_v(fv(*fr), c), xpe_pe(e)), d.root == c.root, d.loc == c.loc,
{
    let ghost f = fv(*fr);
    let ghost p0 = c.path@;
    let mut d = c;
    d.path.push(e);
    proof {
        assert(xpes(p0.push(e)) =~= xpes(p0).push(xpe_pe(e)));
        lemma_xread_push(base_v(f, root_v(d.root)), p0, e);
        if d.loc { assert(no_snap(d.path@)) by { assert forall|i: int| 0 <= i < d.path@.len() implies !(#[trigger] d.path@[i] is Snap) by { if i < p0.len() { assert(d.path@[i] == p0[i]); } } } }
    }
    d
}

// ------------------------------------------------------------------ projections (`proj_step`)

pub open spec fn step_ok(fr: Frame, c: ECur, e: ProjectionElem, r: R<ECur>) -> bool {
    match r {
        Ok(d) => ecur_wf(d) && (proj_step(fr, ecur_v(fr, c), e) matches Some((q, _)) && q == ecur_v(fr, d)),
        Err(Halt::Panic) => proj_step(fr, ecur_v(fr, c), e) is None,
        Err(Halt::GaveUp) => false,
    }
}

#[allow(unused_variables)] // used in the specs
fn e_deref(fr: &CFrame, c: ECur, n: (Option<&CVal>, Option<usize>)) -> (r: R<ECur>)
    requires ecur_wf(c),
        pres_val(fv(*fr), ecur_v(fv(*fr), c)) == Some(xread(base_v(fv(*fr), root_v(c.root)), c.path@)),
        nav_ok(n, xread(base_v(fv(*fr), root_v(c.root)), c.path@)),
    ensures step_ok(fv(*fr), c, ProjectionElem::Deref, r),
{
    let ghost f = fv(*fr);
    let ghost v = xread(base_v(f, root_v(c.root)), c.path@);
    match n {
        (Some(x), None) => match x {
            CVal::Mut(l) => if c.loc {
                let d = ECur { root: copy_root(&l.root), path: xpath_of(&l.path), loc: true };
                Ok(d)
            } else { Err(Halt::Panic) },
            CVal::Shr(_) => {
                let ghost p0 = c.path@;
                let mut d = c;
                d.path.push(XPE::Snap);
                d.loc = false;
                proof { lemma_xread_push(base_v(f, root_v(d.root)), p0, XPE::Snap); }
                Ok(d)
            },
            _ => { proof { lemma_cv(*x); } Err(Halt::Panic) },
        },
        (Some(_x), Some(_)) => { proof { lemma_cv(*_x); } Err(Halt::Panic) },
        (None, _) => Err(Halt::Panic),
    }
}

/// The length of the array a navigation result reads, if it reads one.
fn nav_arr_len(n: (Option<&CVal>, Option<usize>), Ghost(t): Ghost<Val>) -> (r: Option<usize>)
    requires nav_ok(n, t),
    ensures match r { Some(k) => t is Arr && t->Arr_0.len() == k, None => !(t is Arr) },
{
    match n {
        (Some(x), None) => { proof { lemma_cv(*x); } match x { CVal::Arr(vs) => Some(vs.len()), _ => None } },
        (Some(_x), Some(_)) => None,
        (None, _) => None,
    }
}

fn e_index(fr: &CFrame, c: ECur, n: (Option<&CVal>, Option<usize>), x: usize) -> (r: R<ECur>)
    requires ecur_wf(c),
        pres_val(fv(*fr), ecur_v(fv(*fr), c)) == Some(xread(base_v(fv(*fr), root_v(c.root)), c.path@)),
        nav_ok(n, xread(base_v(fv(*fr), root_v(c.root)), c.path@)),
    ensures step_ok(fv(*fr), c, ProjectionElem::Index(x), r),
{
    let i = if x < fr.locals.len() { match &fr.locals[x] { CVal::Int(i) => *i, _ => return Err(Halt::Panic) } } else { return Err(Halt::Panic) };
    let len = match nav_arr_len(n, Ghost(xread(base_v(fv(*fr), root_v(c.root)), c.path@))) { Some(k) => k, None => return Err(Halt::Panic) };
    if i < len as u128 { Ok(cur_push(fr, c, XPE::Index(i))) } else { Err(Halt::Panic) }
}

fn e_cindex(fr: &CFrame, c: ECur, n: (Option<&CVal>, Option<usize>), offset: u64, min_length: u64, from_end: bool) -> (r: R<ECur>)
    requires ecur_wf(c),
        pres_val(fv(*fr), ecur_v(fv(*fr), c)) == Some(xread(base_v(fv(*fr), root_v(c.root)), c.path@)),
        nav_ok(n, xread(base_v(fv(*fr), root_v(c.root)), c.path@)),
    ensures step_ok(fv(*fr), c, ProjectionElem::ConstantIndex { offset, min_length, from_end }, r),
{
    let len = match nav_arr_len(n, Ghost(xread(base_v(fv(*fr), root_v(c.root)), c.path@))) { Some(k) => k as u64, None => return Err(Halt::Panic) };
    if len >= min_length && (if from_end { 1 <= offset && offset <= len } else { offset < len }) {
        let idx = if from_end { len - offset } else { offset };
        Ok(cur_push(fr, c, XPE::Index(idx as u128)))
    } else {
        Err(Halt::Panic)
    }
}

fn e_proj(fr: &CFrame, c: ECur, e: &ProjectionElem) -> (r: R<ECur>)
    requires ecur_wf(c),
    ensures step_ok(fv(*fr), c, *e, r),
{
    let n = match cur_nav(fr, &c) { Some(n) => n, None => return Err(Halt::Panic) };
    match e {
        ProjectionElem::Deref => e_deref(fr, c, n),
        ProjectionElem::Field(i, _) => Ok(cur_push(fr, c, XPE::Field(*i))),
        ProjectionElem::Index(x) => e_index(fr, c, n, *x),
        ProjectionElem::ConstantIndex { offset, min_length, from_end } => e_cindex(fr, c, n, *offset, *min_length, *from_end),
        ProjectionElem::Downcast(k) => Ok(cur_push(fr, c, XPE::Variant(*k))),
        _ => Err(Halt::Panic),
    }
}

proof fn lemma_places_none(fr: Frame, base: PRes, ps: Seq<ProjectionElem>, k: nat, n: nat)
    requires k <= n, places(fr, base, ps, k) is None,
    ensures places(fr, base, ps, n) is None,
    decreases n - k,
{
    if k < n { lemma_places_none(fr, base, ps, k, (n - 1) as nat); }
}

/// `eval_place`'s place.
pub fn e_eval_place(fr: &CFrame, p: &Place) -> (r: R<ECur>)
    ensures
        r matches Ok(c) ==> ecur_wf(c) && (eval_place(fv(*fr), *p) matches Some((q, _)) && q == ecur_v(fv(*fr), c)),
        r matches Err(Halt::Panic) ==> eval_place(fv(*fr), *p) is None,
        !(r matches Err(Halt::GaveUp)),
{
    let ghost f = fv(*fr);
    let ghost base = PRes::At(Loc { root: Root::Local(p.local as nat), path: seq![] });
    let mut c = ECur { root: CRoot::Local(p.local), path: Vec::new(), loc: true };
    proof { assert(xpes(c.path@) =~= Seq::<PE>::empty()); }
    let mut k: usize = 0;
    while k < p.projection.len()
        invariant k <= p.projection@.len(), f == fv(*fr), ecur_wf(c), base == PRes::At(Loc { root: Root::Local(p.local as nat), path: seq![] }),
            places(f, base, p.projection@, k as nat) matches Some((q, _)) && q == ecur_v(f, c),
        decreases p.projection.len() - k,
    {
        let ghost c0 = c;
        c = match e_proj(fr, c, &p.projection[k]) {
            Ok(d) => d,
            Err(h) => {
                proof {
                    assert(proj_step(f, ecur_v(f, c0), p.projection@[k as int]) is None);
                    assert(places(f, base, p.projection@, (k + 1) as nat) is None);
                    lemma_places_none(f, base, p.projection@, (k + 1) as nat, p.projection@.len());
                }
                return Err(h);
            },
        };
        k += 1;
    }
    Ok(c)
}

/// What a place reads, by reference.
fn e_place_nav<'a>(fr: &'a CFrame, p: &Place) -> (r: R<(Option<&'a CVal>, Option<usize>)>)
    ensures
        r matches Ok(n) ==> read_place(fv(*fr), *p) matches Some((w, _)) && nav_ok(n, w),
        r matches Err(Halt::Panic) ==> read_place(fv(*fr), *p) is None,
        !(r matches Err(Halt::GaveUp)),
{
    let c = e_eval_place(fr, p)?;
    match cur_nav(fr, &c) { Some(n) => Ok(n), None => Err(Halt::Panic) }
}

pub fn e_read_place(fr: &CFrame, p: &Place) -> (r: R<CVal>)
    ensures
        r matches Ok(v) ==> read_place(fv(*fr), *p) matches Some((w, _)) && w == cv(v),
        r matches Err(Halt::Panic) ==> read_place(fv(*fr), *p) is None,
        !(r matches Err(Halt::GaveUp)),
{
    let n = e_place_nav(fr, p)?;
    Ok(take(n))
}

// ------------------------------------------------------------------ operands

pub fn e_eval_op(m: &MirCrate, tb: &Tabs, fr: &CFrame, op: &Operand) -> (r: R<(CVal, u64)>)
    requires tabs_ok(*m, *tb),
    ensures r_val(r, eval_op(*m, fv(*fr), *op)),
{
    match op {
        Operand::Copy(p) | Operand::Move(p) => Ok((e_read_place(fr, p)?, 0)),
        Operand::Constant(c) => e_const_val(m, tb, c),
        _ => Err(Halt::Panic),
    }
}

proof fn lemma_ops_none(m: MirCrate, fr: Frame, ops: Seq<Operand>, k: nat, n: nat)
    requires k <= n, eval_ops(m, fr, ops, k) is None,
    ensures eval_ops(m, fr, ops, n) is None,
    decreases n - k,
{
    if k < n { lemma_ops_none(m, fr, ops, k, (n - 1) as nat); }
}

pub fn e_eval_ops(m: &MirCrate, tb: &Tabs, fr: &CFrame, ops: &Vec<Operand>) -> (r: R<(Vec<CVal>, u64)>)
    requires tabs_ok(*m, *tb),
    ensures r_vals(r, eval_ops(*m, fv(*fr), ops@, ops@.len())),
{
    let ghost f = fv(*fr);
    let mut vs: Vec<CVal> = Vec::new();
    let mut c: u64 = 0;
    let mut i: usize = 0;
    proof { assert(cvs(vs@) =~= Seq::<Val>::empty()); }
    while i < ops.len()
        invariant i <= ops@.len(), tabs_ok(*m, *tb), f == fv(*fr),
            eval_ops(*m, f, ops@, i as nat) matches Some((ws, _, j)) && ws == cvs(vs@) && j == c as nat,
        decreases ops.len() - i,
    {
        match e_eval_op(m, tb, fr, &ops[i]) {
            Ok((v, k)) => {
                if c > u64::MAX - k { return Err(Halt::GaveUp); }
                proof { lemma_cvs_push(vs@, v); }
                vs.push(v);
                c = c + k;
            },
            Err(Halt::Panic) => {
                proof { lemma_ops_none(*m, f, ops@, (i + 1) as nat, ops@.len()); }
                return Err(Halt::Panic);
            },
            Err(Halt::GaveUp) => return Err(Halt::GaveUp),
        }
        i += 1;
    }
    Ok((vs, c))
}

// ------------------------------------------------------------------ arithmetic guards

/// `md(t) - 1`.
fn md_m1(t: &CTy) -> (r: u128)
    ensures r as int == md(*t) - 1,
{
    proof { lemma_md(*t); }
    if is_wide(t) { u128::MAX } else { md_exec(t) - 1 }
}

/// `bin_ok` for the ops the evaluator runs (`e_rv_bin` gives up on the `*Unchecked` ones).
#[allow(unused_variables)] // used in the specs
pub fn x_bin_ok(op: &BinOp, it: &CTy, rt: &CTy, a: u128, c: u128) -> (r: bool)
    requires !(*op is AddUnchecked || *op is SubUnchecked || *op is MulUnchecked || *op is ShlUnchecked || *op is ShrUnchecked),
    ensures r == bin_ok(*op, *it, *rt, a, c),
{
    match op {
        BinOp::Div | BinOp::Rem => {
            proof { lemma_read(*it, a); lemma_read(*it, c); lemma_md(*it); }
            let uc = uval_exec(it, c);
            if uc == 0 { return false; }
            let ua = uval_exec(it, a);
            !(is_signed(it) && ua == half_exec(it) && uc == md_m1(it))
        },
        _ => true,
    }
}

fn core_bin_exec(op: &BinOp) -> (r: Option<COp>)
    ensures r == core_bin(*op),
{
    match op {
        BinOp::Add | BinOp::AddUnchecked => Some(COp::Add),
        BinOp::Sub | BinOp::SubUnchecked => Some(COp::Sub),
        BinOp::Mul | BinOp::MulUnchecked => Some(COp::Mul),
        BinOp::Div => Some(COp::Div),
        BinOp::Rem => Some(COp::Rem),
        BinOp::BitXor => Some(COp::BitXor),
        BinOp::BitAnd => Some(COp::BitAnd),
        BinOp::BitOr => Some(COp::BitOr),
        BinOp::Shl | BinOp::ShlUnchecked => Some(COp::Shl),
        BinOp::Shr | BinOp::ShrUnchecked => Some(COp::Shr),
        BinOp::Eq => Some(COp::Eq),
        BinOp::Lt => Some(COp::Lt),
        BinOp::Le => Some(COp::Le),
        BinOp::Ne => Some(COp::Ne),
        BinOp::Ge => Some(COp::Ge),
        BinOp::Gt => Some(COp::Gt),
        _ => None,
    }
}

/// An int operand: its bit pattern and charge.
fn e_op_int(m: &MirCrate, tb: &Tabs, fr: &CFrame, op: &Operand) -> (r: R<(u128, u64)>)
    requires tabs_ok(*m, *tb),
    ensures
        r matches Ok((a, k)) ==> eval_op(*m, fv(*fr), *op) matches Some((Val::Int(b), _, j)) && b == a && j == k as nat,
        r matches Err(Halt::Panic) ==> !(eval_op(*m, fv(*fr), *op) matches Some((Val::Int(_), _, _))),
{
    match e_eval_op(m, tb, fr, op)? {
        (CVal::Int(a), k) => Ok((a, k)),
        (_v, _) => { proof { lemma_cv(_v); } Err(Halt::Panic) },
    }
}

// ------------------------------------------------------------------ rvalues

fn e_rv_bin(m: &MirCrate, tb: &Tabs, b: &Body, fr: &CFrame, op: &BinOp, x: &Operand, y: &Operand) -> (r: R<(CVal, u64)>)
    requires tabs_ok(*m, *tb),
    ensures r_val(r, rv_bin(*m, *b, fv(*fr), *op, *x, *y)),
{
    if matches!(op, BinOp::AddUnchecked | BinOp::SubUnchecked | BinOp::MulUnchecked | BinOp::ShlUnchecked | BinOp::ShrUnchecked) {
        return Err(Halt::GaveUp);
    }
    let cop = match core_bin_exec(op) { Some(c) => c, None => return Err(Halt::Panic) };
    let (a, kx) = e_op_int(m, tb, fr, x)?;
    let (c, ky) = e_op_int(m, tb, fr, y)?;
    let it = match t_op_ty(m, tb, b, x) { Some(t) => match t_int_ty(m, tb, t) { Some(it) => it, None => return Err(Halt::Panic) }, None => return Err(Halt::Panic) };
    let rt = match t_op_ty(m, tb, b, y) { Some(t) => match t_int_ty(m, tb, t) { Some(rt) => rt, None => return Err(Halt::Panic) }, None => return Err(Halt::Panic) };
    if !x_bin_ok(op, &it, &rt, a, c) { return Err(Halt::Panic); }
    if kx > u64::MAX - ky { return Err(Halt::GaveUp); }
    Ok((CVal::Int(binop_exec(&cop, &it, a, c)), kx + ky))
}

fn e_rv_notneg(m: &MirCrate, tb: &Tabs, b: &Body, fr: &CFrame, op: &UnOp, x: &Operand) -> (r: R<(CVal, u64)>)
    requires tabs_ok(*m, *tb), *op is Not || *op is Neg,
    ensures r_val(r, rv_un(*m, *b, fv(*fr), *op, *x)),
{
    let (a, k) = e_op_int(m, tb, fr, x)?;
    let it = match t_op_ty(m, tb, b, x) { Some(t) => match t_int_ty(m, tb, t) { Some(it) => it, None => return Err(Halt::Panic) }, None => return Err(Halt::Panic) };
    match op {
        UnOp::Not => Ok((CVal::Int(unop_exec(&CUn::Not, &it, a)), k)),
        _ => if is_signed(&it) { Ok((CVal::Int(unop_exec(&CUn::Neg, &it, a)), k)) } else { Err(Halt::Panic) },
    }
}

/// The length of the slice a reference value points to (`rv_un`'s `PtrMetadata` pointee).
fn ptr_len(fr: &CFrame, v: &CVal) -> (r: Option<usize>)
    ensures ({
        let pointee = match cv(*v) { Val::Shr(bx) => Some(*bx), Val::Mut(l) => load(fv(*fr), l), _ => None };
        match r { Some(n) => pointee matches Some(Val::Arr(vs)) && vs.len() == n, None => !(pointee matches Some(Val::Arr(_))) }
    }),
{
    match v {
        CVal::Shr(bx) => nav_arr_len((Some(&**bx), None), Ghost(cv(**bx))),
        CVal::Mut(l) => {
            let xp = xpath_of(&l.path);
            proof { lemma_xread_loc(base_v(fv(*fr), root_v(l.root)), xp@); }
            if !root_in(fr, &l.root) { return None; }
            nav_arr_len(at(fr, &l.root, &xp), Ghost(xread(base_v(fv(*fr), root_v(l.root)), xp@)))
        },
        _ => None,
    }
}

fn e_rv_ptrmeta(m: &MirCrate, tb: &Tabs, b: &Body, fr: &CFrame, x: &Operand) -> (r: R<(CVal, u64)>)
    requires tabs_ok(*m, *tb),
    ensures r_val(r, rv_un(*m, *b, fv(*fr), UnOp::PtrMetadata, *x)),
{
    let tx = match t_op_ty(m, tb, b, x) { Some(t) => t, None => return Err(Halt::Panic) };
    let slice = match t_rigid(m, tb, tx) {
        Some(RigidTy::Ref(_, p, _)) => matches!(t_rigid(m, tb, *p), Some(RigidTy::Slice(_))),
        _ => false,
    };
    if !slice { return Err(Halt::Panic); }
    let (n, k) = match x {
        Operand::Copy(p) | Operand::Move(p) => match e_place_nav(fr, p)? {
            (Some(v), None) => (ptr_len(fr, v), 0u64),
            (Some(_v), Some(_)) => { proof { lemma_cv(*_v); } (None, 0) },
            (None, _) => (None, 0),
        },
        Operand::Constant(c) => {
            let (v, k) = e_const_val(m, tb, c)?;
            (ptr_len(fr, &v), k)
        },
        _ => return Err(Halt::Panic),
    };
    match n { Some(n) => Ok((CVal::Int(n as u128), k)), None => Err(Halt::Panic) }
}

fn e_rv_un(m: &MirCrate, tb: &Tabs, b: &Body, fr: &CFrame, op: &UnOp, x: &Operand) -> (r: R<(CVal, u64)>)
    requires tabs_ok(*m, *tb),
    ensures r_val(r, rv_un(*m, *b, fv(*fr), *op, *x)),
{
    match op {
        UnOp::Not | UnOp::Neg => e_rv_notneg(m, tb, b, fr, op, x),
        UnOp::PtrMetadata => e_rv_ptrmeta(m, tb, b, fr, x),
        _ => Err(Halt::Panic),
    }
}

fn e_rv_cast(m: &MirCrate, tb: &Tabs, b: &Body, fr: &CFrame, ck: &CastKind, x: &Operand, to: Ty) -> (r: R<(CVal, u64)>)
    requires tabs_ok(*m, *tb),
    ensures r_val(r, rv_cast(*m, *b, fv(*fr), *ck, *x, to)),
{
    let (v, k) = e_eval_op(m, tb, fr, x)?;
    let tx = match t_op_ty(m, tb, b, x) { Some(t) => t, None => return Err(Halt::Panic) };
    proof { lemma_cv(v); }
    match ck {
        CastKind::IntToInt => match (v, t_int_ty(m, tb, tx), t_int_ty(m, tb, to)) {
            (CVal::Int(a), Some(f), Some(t)) => Ok((CVal::Int(cast_exec(&f, &t, a)), k)),
            _ => Err(Halt::Panic),
        },
        CastKind::PointerCoercion(PointerCoercion::Unsize) => match (t_rigid(m, tb, tx), t_rigid(m, tb, to)) {
            (Some(RigidTy::Ref(_, p, _)), Some(RigidTy::Ref(_, q, _))) =>
                if matches!(t_rigid(m, tb, *p), Some(RigidTy::Array(_, _))) && matches!(t_rigid(m, tb, *q), Some(RigidTy::Slice(_))) {
                    Ok((v, k))
                } else { Err(Halt::Panic) },
            _ => Err(Halt::Panic),
        },
        CastKind::PointerCoercion(PointerCoercion::ClosureFnPointer(_)) | CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer(_)) =>
            if matches!(v, CVal::Unit) { Ok((CVal::Unit, k)) } else { Err(Halt::Panic) },
        CastKind::Subtype => Ok((v, k)),
        _ => Err(Halt::Panic),
    }
}

fn e_rv_agg(m: &MirCrate, tb: &Tabs, fr: &CFrame, ak: &AggregateKind, ops: &Vec<Operand>) -> (r: R<(CVal, u64)>)
    requires tabs_ok(*m, *tb),
    ensures r_val(r, rv_agg(*m, fv(*fr), *ak, ops@)),
{
    match ak {
        AggregateKind::Array(_) | AggregateKind::Tuple | AggregateKind::Adt(_, _, _, _, None) => {},
        _ => return Err(Halt::Panic),
    }
    let (vs, k) = e_eval_ops(m, tb, fr, ops)?;
    let v = match ak {
        AggregateKind::Array(_) => CVal::Arr(vs),
        AggregateKind::Tuple => CVal::Tup(vs),
        AggregateKind::Adt(_, var, _, _, _) => CVal::Adt(*var, vs),
        _ => CVal::Unit,
    };
    proof { lemma_cv(v); }
    Ok((v, k))
}

fn e_rv_repeat(m: &MirCrate, tb: &Tabs, fr: &CFrame, x: &Operand, c: &TyConst) -> (r: R<(CVal, u64)>)
    requires tabs_ok(*m, *tb),
    ensures r_val(r, match (eval_op(*m, fv(*fr), *x), const_usize(*m, c.id)) {
        (Some((v, e, k)), Some(n)) => Some((Val::Arr(Seq::new(n as nat, |_i: int| v)), e, k)),
        _ => None,
    }),
{
    let (v, k) = e_eval_op(m, tb, fr, x)?;
    let n = match t_const_usize(m, tb, c.id) { Some(n) => n, None => return Err(Halt::Panic) };
    if n > CAP { return Err(Halt::GaveUp); }
    let w = CVal::Arr(repeat(&v, n));
    proof { lemma_cv(w); }
    Ok((w, k))
}

fn e_rv_ref(fr: &CFrame, bk: &BorrowKind, p: &Place) -> (r: R<(CVal, u64)>)
    ensures r_val(r, rv_ref(fv(*fr), *bk, *p)),
{
    match bk {
        BorrowKind::Shared => Ok((CVal::Shr(Box::new(e_read_place(fr, p)?)), 0)),
        BorrowKind::Mut { .. } => {
            let c = e_eval_place(fr, p)?;
            if !c.loc { return Err(Halt::Panic); }
            Ok((CVal::Mut(cur_loc(c)), 0))
        },
        _ => Err(Halt::Panic),
    }
}

fn e_rv_len(fr: &CFrame, p: &Place) -> (r: R<(CVal, u64)>)
    ensures r_val(r, match read_place(fv(*fr), *p) { Some((Val::Arr(vs), e)) => Some((Val::Int(vs.len() as u128), e, 0nat)), _ => None }),
{
    let n = e_place_nav(fr, p)?;
    match nav_arr_len(n, Ghost(read_place(fv(*fr), *p)->Some_0.0)) {
        Some(n) => Ok((CVal::Int(n as u128), 0)),
        None => Err(Halt::Panic),
    }
}

/// The variant a navigation result reads, if it reads an `Adt`; `Unit` gives `Err(true)`.
fn nav_variant(n: (Option<&CVal>, Option<usize>), Ghost(t): Ghost<Val>) -> (r: Result<usize, bool>)
    requires nav_ok(n, t),
    ensures match r {
        Ok(k) => t is Adt && t->Adt_0 == k,
        Err(u) => !(t is Adt) && (u == (t is Unit)),
    },
{
    match n {
        (Some(x), None) => { proof { lemma_cv(*x); } match x { CVal::Adt(k, _) => Ok(*k), CVal::Unit => Err(true), _ => Err(false) } },
        (Some(_x), Some(j)) => Ok(j),
        (None, _) => Err(true),
    }
}

fn e_rv_discr(m: &MirCrate, tb: &Tabs, b: &Body, fr: &CFrame, p: &Place) -> (r: R<(CVal, u64)>)
    requires tabs_ok(*m, *tb),
    ensures r_val(r, rv_discr(*m, *b, fv(*fr), *p)),
{
    let n = e_place_nav(fr, p)?;
    let t = match t_place_ty(m, tb, b, p) { Some(t) => t, None => return Err(Halt::Panic) };
    let a = match t_adt_row(m, tb, t) { Some(a) => a, None => return Err(Halt::Panic) };
    match a.kind {
        AdtKind::Enum => match nav_variant(n, Ghost(read_place(fv(*fr), *p)->Some_0.0)) {
            Ok(k) => if k < a.variants.len() {
                match a.variants[k].discr { Some(d) => Ok((CVal::Int(d), 0)), None => Err(Halt::Panic) }
            } else { Err(Halt::Panic) },
            Err(true) => {
                if !(a.variants.len() == 1 && a.variants[0].discr.is_some()) { return Err(Halt::Panic); }
                let tf = match x_tfuel(m) { Some(f) => f, None => return Err(Halt::GaveUp) };
                e_unit_like(m, tb, t, tf, true)?;
                match a.variants[0].discr { Some(d) => Ok((CVal::Int(d), 0)), None => Err(Halt::Panic) }
            },
            Err(false) => Err(Halt::Panic),
        },
        AdtKind::Struct => Ok((CVal::Int(0), 0)),
        _ => Err(Halt::Panic),
    }
}

/// `eval_rv`: an rvalue's value and constant charges. `CheckedBinaryOp` gives up (the translator
/// never lowers it).
pub fn e_eval_rv(m: &MirCrate, tb: &Tabs, b: &Body, fr: &CFrame, rv: &Rvalue) -> (r: R<(CVal, u64)>)
    requires tabs_ok(*m, *tb),
    ensures r_val(r, eval_rv(*m, *b, fv(*fr), *rv)),
{
    match rv {
        Rvalue::Use(x, _) => e_eval_op(m, tb, fr, x),
        Rvalue::BinaryOp(op, x, y) => e_rv_bin(m, tb, b, fr, op, x, y),
        Rvalue::CheckedBinaryOp(_, _, _) => Err(Halt::GaveUp),
        Rvalue::UnaryOp(op, x) => e_rv_un(m, tb, b, fr, op, x),
        Rvalue::Cast(ck, x, to) => e_rv_cast(m, tb, b, fr, ck, x, *to),
        Rvalue::Aggregate(ak, ops) => e_rv_agg(m, tb, fr, ak, ops),
        Rvalue::Repeat(x, c) => e_rv_repeat(m, tb, fr, x, c),
        Rvalue::Ref(_, bk, p) => e_rv_ref(fr, bk, p),
        Rvalue::Len(p) => e_rv_len(fr, p),
        Rvalue::Discriminant(p) => e_rv_discr(m, tb, b, fr, p),
        Rvalue::CopyForDeref(p) => Ok((e_read_place(fr, p)?, 0)),
        _ => Err(Halt::Panic),
    }
}

// ------------------------------------------------------------------ stores and statements

/// `store`: the frame updated in place.
pub fn e_store(fr: &mut CFrame, l: &CLoc, w: CVal) -> (r: R<()>)
    ensures
        r matches Ok(()) ==> store(fv(*old(fr)), loc_v(*l), cv(w)) == Some(fv(*final(fr))),
        r matches Err(Halt::Panic) ==> store(fv(*old(fr)), loc_v(*l), cv(w)) is None,
        !(r matches Err(Halt::GaveUp)),
{
    proof { assert(l.path@.subrange(0, l.path@.len() as int) =~= l.path@); }
    match l.root {
        CRoot::Local(i) => if i < fr.locals.len() {
            let ghost o = fr.locals@;
            let x = take_at(&mut fr.locals, i);
            let y = set_at(x, &l.path, 0, w);
            fr.locals.set(i, y);
            proof { assert(fr.locals@ == o.update(i as int, y)); lemma_cvs_update(o, i as int, y); }
            Ok(())
        } else { Err(Halt::Panic) },
        CRoot::Slot(j) => if j < fr.slots.len() {
            let ghost o = fr.slots@;
            let x = take_at(&mut fr.slots, j);
            let y = set_at(x, &l.path, 0, w);
            fr.slots.set(j, y);
            proof { assert(fr.slots@ == o.update(j as int, y)); lemma_cvs_update(o, j as int, y); }
            Ok(())
        } else { Err(Halt::Panic) },
    }
}

/// A location cursor as a location.
fn cur_loc(c: ECur) -> (l: CLoc)
    requires c.loc, no_snap(c.path@),
    ensures loc_v(l) == (Loc { root: root_v(c.root), path: xpes(c.path@) }),
{
    CLoc { root: c.root, path: cpath_of(&c.path) }
}

fn e_assign(m: &MirCrate, tb: &Tabs, b: &Body, fr: &mut CFrame, p: &Place, rv: &Rvalue) -> (r: R<u64>)
    requires tabs_ok(*m, *tb),
    ensures ({
        let s = match (eval_rv(*m, *b, fv(*old(fr)), *rv), eval_place(fv(*old(fr)), *p)) {
            (Some((v, e1, k)), Some((PRes::At(l), e2))) => match store(fv(*old(fr)), l, v) {
                Some(fr2) => Some((fr2, e1 + e2, 1 + k)),
                None => None,
            },
            _ => None,
        };
        &&& r matches Ok(n) ==> s matches Some((f, _, k)) && f == fv(*final(fr)) && k == n as nat
        &&& r matches Err(Halt::Panic) ==> s is None
    }),
{
    let (v, k) = e_eval_rv(m, tb, b, fr, rv)?;
    let c = e_eval_place(fr, p)?;
    if !c.loc { return Err(Halt::Panic); }
    if k == u64::MAX { return Err(Halt::GaveUp); }
    let l = cur_loc(c);
    e_store(fr, &l, v)?;
    Ok(1 + k)
}

fn e_set_discr(fr: &mut CFrame, place: &Place, variant_index: usize) -> (r: R<u64>)
    ensures ({
        let s = match eval_place(fv(*old(fr)), *place) {
            Some((PRes::At(l), e)) => match load(fv(*old(fr)), l) {
                Some(Val::Adt(_, vs)) => match store(fv(*old(fr)), l, Val::Adt(variant_index as nat, vs)) {
                    Some(fr2) => Some((fr2, e, 1nat)),
                    None => None,
                },
                _ => None,
            },
            _ => None,
        };
        &&& r matches Ok(n) ==> s matches Some((f, _, k)) && f == fv(*final(fr)) && k == n as nat
        &&& r matches Err(Halt::Panic) ==> s is None
    }),
{
    let c = e_eval_place(fr, place)?;
    if !c.loc { return Err(Halt::Panic); }
    let nv = match cur_nav(fr, &c) {
        Some((Some(x), _)) => match x {
            CVal::Adt(_, vs) => {
                let nv = CVal::Adt(variant_index, clone_vec(vs));
                proof { lemma_cv(nv); lemma_cv(*x); }
                nv
            },
            _ => { proof { lemma_cv(*x); } return Err(Halt::Panic) },
        },
        _ => return Err(Halt::Panic),
    };
    let l = cur_loc(c);
    e_store(fr, &l, nv)?;
    Ok(1)
}

fn e_exec_stmt(m: &MirCrate, tb: &Tabs, b: &Body, fr: &mut CFrame, s: &Statement) -> (r: R<u64>)
    requires tabs_ok(*m, *tb),
    ensures
        r matches Ok(n) ==> exec_stmt(*m, *b, fv(*old(fr)), *s) matches Some((f, _, k)) && f == fv(*final(fr)) && k == n as nat,
        r matches Err(Halt::Panic) ==> exec_stmt(*m, *b, fv(*old(fr)), *s) is None,
{
    proof { reveal(exec_stmt); }
    match &s.kind {
        StatementKind::Assign(p, rv) => e_assign(m, tb, b, fr, p, rv),
        StatementKind::SetDiscriminant { place, variant_index } => e_set_discr(fr, place, *variant_index),
        StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop | StatementKind::FakeRead(_, _)
        | StatementKind::PlaceMention(_) | StatementKind::AscribeUserType { .. } | StatementKind::Coverage(_)
        | StatementKind::ConstEvalCounter => Ok(0),
        _ => Err(Halt::Panic),
    }
}

proof fn lemma_stmts_none(m: MirCrate, b: Body, fr: Frame, ss: Seq<Statement>, k: nat, n: nat)
    requires k <= n, exec_stmts(m, b, fr, ss, k) is None,
    ensures exec_stmts(m, b, fr, ss, n) is None,
    decreases n - k,
{
    if k < n { lemma_stmts_none(m, b, fr, ss, k, (n - 1) as nat); }
}

/// `exec_stmts` over a block's statements: the frame in place and the steps.
pub fn e_exec_stmts(m: &MirCrate, tb: &Tabs, b: &Body, fr: &mut CFrame, ss: &Vec<Statement>) -> (r: R<u64>)
    requires tabs_ok(*m, *tb),
    ensures
        r matches Ok(n) ==> exec_stmts(*m, *b, fv(*old(fr)), ss@, ss@.len()) matches Some((f, _, s)) && fv(*final(fr)) == f && s == n as nat,
        r matches Err(Halt::Panic) ==> exec_stmts(*m, *b, fv(*old(fr)), ss@, ss@.len()) is None,
{
    let ghost f0 = fv(*fr);
    let mut n: u64 = 0;
    let mut k: usize = 0;
    while k < ss.len()
        invariant k <= ss@.len(), tabs_ok(*m, *tb), f0 == fv(*old(fr)),
            exec_stmts(*m, *b, f0, ss@, k as nat) matches Some((f, _, s)) && f == fv(*fr) && s == n as nat,
        decreases ss.len() - k,
    {
        match e_exec_stmt(m, tb, b, fr, &ss[k]) {
            Ok(x) => {
                if n > u64::MAX - x { return Err(Halt::GaveUp); }
                n = n + x;
            },
            Err(Halt::Panic) => {
                proof { lemma_stmts_none(*m, *b, f0, ss@, (k + 1) as nat, ss@.len()); }
                return Err(Halt::Panic);
            },
            Err(Halt::GaveUp) => return Err(Halt::GaveUp),
        }
        k += 1;
    }
    Ok(n)
}

// ------------------------------------------------------------------ the entry frame

/// `mir_entry`: parameter `k` is `args[k - 1]` (moved, not cloned), or `Mut(Slot(k - 1))` at a
/// `&mut` type; every other local holds `ul_val` of its type.
pub fn e_mir_entry(m: &MirCrate, tb: &Tabs, i: usize, args: Vec<CVal>, slots: Vec<CVal>) -> (r: R<CFrame>)
    requires tabs_ok(*m, *tb),
    ensures r matches Ok(fr) ==> fv(fr) == mir_entry(*m, i as nat, cvs(args@), cvs(slots@)),
{
    let b = match t_inst_body(m, tb, i) {
        Some(b) => b,
        None => {
            let fr = CFrame { locals: Vec::new(), slots };
            proof { assert(cvs(fr.locals@) =~= Seq::<Val>::empty()); }
            return Ok(fr);
        },
    };
    let ghost a0 = cvs(args@);
    let mut args = args;
    let mut locals: Vec<CVal> = Vec::new();
    let mut k: usize = 0;
    while k < b.locals.len()
        invariant
            k <= b.locals@.len(), tabs_ok(*m, *tb), args@.len() == a0.len(),
            forall|q: int| 0 <= q && k - 1 <= q < args@.len() ==> cv(#[trigger] args@[q]) == a0[q],
            locals@.len() == k, forall|q: int| 0 <= q < k ==> cv(#[trigger] locals@[q]) == entry_local(*m, *b, a0, q),
        decreases b.locals.len() - k,
    {
        let v = if 1 <= k && k <= b.arg_count && k - 1 < args.len() {
            if t_is_mut_ref(m, tb, b.locals[k].ty) {
                let v = CVal::Mut(CLoc { root: CRoot::Slot(k - 1), path: Vec::new() });
                proof { assert(pes(Seq::<CPE>::empty()) =~= Seq::<PE>::empty()); }
                v
            } else {
                take_at(&mut args, k - 1)
            }
        } else {
            e_ul_val(m, tb, b.locals[k].ty)?
        };
        locals.push(v);
        k += 1;
    }
    let fr = CFrame { locals, slots };
    proof { assert(cvs(fr.locals@) =~= Seq::new(b.locals@.len(), |q: int| entry_local(*m, *b, a0, q))); }
    Ok(fr)
}

// ------------------------------------------------------------------ well-typed arguments

/// `n < 2^bits(it)`.
fn int_fits(it: &CTy, n: u128) -> (r: bool)
    ensures r == ((n as int) < pow2(bits(*it))),
{
    proof { lemma_md(*it); }
    if is_wide(it) { true } else { n < md_exec(it) }
}

fn wt_elems(m: &MirCrate, tb: &Tabs, e: Ty, vs: &Vec<CVal>) -> (r: bool)
    requires tabs_ok(*m, *tb),
    ensures r ==> forall|i: int| 0 <= i < vs@.len() ==> wt_rec(*m, e, #[trigger] cvs(vs@)[i]),
    decreases vs,
{
    let mut i: usize = 0;
    while i < vs.len()
        invariant i <= vs@.len(), tabs_ok(*m, *tb), forall|q: int| 0 <= q < i ==> wt_rec(*m, e, #[trigger] cvs(vs@)[q]),
        decreases vs.len() - i,
    {
        if !x_wt_rec(m, tb, e, &vs[i]) { return false; }
        i += 1;
    }
    true
}

fn wt_fields(m: &MirCrate, tb: &Tabs, ts: &Vec<Ty>, vs: &Vec<CVal>) -> (r: bool)
    requires tabs_ok(*m, *tb),
    ensures r ==> vs@.len() == ts@.len() && forall|i: int| 0 <= i < vs@.len() ==> wt_rec(*m, ts@[i], #[trigger] cvs(vs@)[i]),
    decreases vs,
{
    if vs.len() != ts.len() { return false; }
    let mut i: usize = 0;
    while i < vs.len()
        invariant i <= vs@.len(), vs@.len() == ts@.len(), tabs_ok(*m, *tb),
            forall|q: int| 0 <= q < i ==> wt_rec(*m, ts@[q], #[trigger] cvs(vs@)[q]),
        decreases vs.len() - i,
    {
        if !x_wt_rec(m, tb, ts[i], &vs[i]) { return false; }
        i += 1;
    }
    true
}

/// The `Unit` arm of `wt_rec` at the pattern-stripped type `t` with rigid kind `r`.
fn wt_unit(m: &MirCrate, tb: &Tabs, t: Ty, r: &RigidTy) -> (b: bool)
    requires tabs_ok(*m, *tb), rigid(*m, t) == Some(*r),
    ensures b ==> (*r is FnDef || *r is Closure || *r is FnPtr
        || (*r matches RigidTy::Ref(_, p, Mutability::Not) && rigid(*m, p) matches Some(RigidTy::Str))
        || (unit_like(*m, t, tfuel(*m), true) is Some && !ul_arr(*m, t))),
{
    if matches!(r, RigidTy::FnDef(_, _) | RigidTy::Closure(_, _) | RigidTy::FnPtr(_)) { return true; }
    if let RigidTy::Ref(_, p, Mutability::Not) = r {
        if matches!(t_rigid(m, tb, *p), Some(RigidTy::Str)) { return true; }
    }
    let tf = match x_tfuel(m) { Some(f) => f, None => return false };
    match e_unit_like(m, tb, t, tf, true) { Ok(_) => !t_has_arr(m, tb, t, tf), Err(_) => false }
}

/// `wt_rec` (one-way: it may reject more).
pub fn x_wt_rec(m: &MirCrate, tb: &Tabs, ty: Ty, v: &CVal) -> (r: bool)
    requires tabs_ok(*m, *tb),
    ensures r ==> wt_rec(*m, ty, cv(*v)),
    decreases v,
{
    let t = match t_rigid(m, tb, ty) { Some(RigidTy::Pat(base, _)) => *base, _ => ty };
    proof { assert(t == strip_pat(*m, ty)); lemma_cv(*v); }
    let r = match t_rigid(m, tb, t) { Some(r) => r, None => return false };
    if let Some(it) = crate::look::x_int_of(r) {
        return match v { CVal::Int(n) => int_fits(&it, *n), _ => false };
    }
    match v {
        CVal::Tup(vs) => match r { RigidTy::Tuple(ts) => wt_fields(m, tb, ts, vs), _ => false },
        CVal::Arr(vs) => match r {
            RigidTy::Array(e, c) => t_const_usize(m, tb, c.id) == Some(vs.len() as u64) && wt_elems(m, tb, *e, vs),
            RigidTy::Slice(e) => wt_elems(m, tb, *e, vs),
            RigidTy::Adt(_, _) => match t_vec_elem(m, tb, t) { Some(e) => wt_elems(m, tb, e, vs), None => false },
            _ => false,
        },
        CVal::Adt(k, vs) => match (r, t_adt_row(m, tb, t)) {
            (RigidTy::Adt(_, _), Some(a)) => t_vec_elem(m, tb, t).is_none() && !a.is_box && !matches!(a.kind, AdtKind::Union)
                && *k < a.variants.len() && wt_fields(m, tb, &a.variants[*k].fields, vs),
            _ => false,
        },
        CVal::Shr(bx) => match r { RigidTy::Ref(_, p, Mutability::Not) => x_wt_rec(m, tb, *p, &**bx), _ => false },
        CVal::Mut(_) => matches!(r, RigidTy::Ref(_, _, Mutability::Mut)),
        CVal::Unit => wt_unit(m, tb, t, r),
        CVal::Int(_) => false,
    }
}

/// `wt_val(m, ty, cv(v))` (one-way).
fn x_wt_val(m: &MirCrate, tb: &Tabs, ty: Ty, v: &CVal, tf: usize) -> (r: bool)
    requires tabs_ok(*m, *tb), tf as nat == tfuel(*m),
    ensures r ==> wt_val(*m, ty, cv(*v)),
{
    x_ty_free(m, ty, tf, true) && x_wt_rec(m, tb, ty, v)
}

/// The entry arguments are well-typed for `insts[i]`'s signature (one-way: it may reject more).
#[verifier::loop_isolation(false)]
pub fn x_wt_args(m: &MirCrate, tb: &Tabs, i: usize, args: &Vec<CVal>, slots: &Vec<CVal>) -> (r: bool)
    requires tabs_ok(*m, *tb),
    ensures r ==> wt_args(*m, i as nat, cvs(args@), cvs(slots@)),
{
    let b = match t_inst_body(m, tb, i) { Some(b) => b, None => return false };
    if !(args.len() == b.arg_count && slots.len() == b.arg_count && b.arg_count < b.locals.len()) { return false; }
    let tf = match x_tfuel(m) { Some(f) => f, None => return false };
    let mut j: usize = 0;
    while j < b.arg_count
        invariant
            j <= b.arg_count, b.arg_count < b.locals@.len(), args@.len() == b.arg_count, slots@.len() == b.arg_count,
            tabs_ok(*m, *tb), tf as nat == tfuel(*m),
            forall|q: int| 0 <= q < j ==> {
                &&& wt_val(*m, b.locals@[q + 1].ty, #[trigger] cvs(args@)[q])
                &&& if is_mut_ref(*m, b.locals@[q + 1].ty) { wt_val(*m, pointee(*m, b.locals@[q + 1].ty), cvs(slots@)[q]) } else { cvs(slots@)[q] == Val::Unit }
            },
        decreases b.arg_count - j,
    {
        let t = b.locals[j + 1].ty;
        if !x_wt_val(m, tb, t, &args[j], tf) { return false; }
        let ok = match t_rigid(m, tb, t) {
            Some(RigidTy::Ref(_, p, Mutability::Mut)) => x_wt_val(m, tb, *p, &slots[j], tf),
            _ => matches!(slots[j], CVal::Unit),
        };
        if !ok { return false; }
        proof {
            assert(cvs(args@)[j as int] == cv(args@[j as int]));
            assert(cvs(slots@)[j as int] == cv(slots@[j as int]));
            assert(wt_val(*m, b.locals@[j + 1].ty, cvs(args@)[j as int]));
            if is_mut_ref(*m, b.locals@[j + 1].ty) {
                assert(wt_val(*m, pointee(*m, b.locals@[j + 1].ty), cvs(slots@)[j as int]));
            } else {
                assert(cvs(slots@)[j as int] == Val::Unit);
            }
            assert forall|q: int| 0 <= q < j + 1 implies {
                &&& wt_val(*m, b.locals@[q + 1].ty, #[trigger] cvs(args@)[q])
                &&& if is_mut_ref(*m, b.locals@[q + 1].ty) { wt_val(*m, pointee(*m, b.locals@[q + 1].ty), cvs(slots@)[q]) } else { cvs(slots@)[q] == Val::Unit }
            } by {
                if q < j { assert(cvs(args@)[q] == cvs(args@)[q]); }
            };
        }
        j += 1;
    }
    true
}

} // verus!
