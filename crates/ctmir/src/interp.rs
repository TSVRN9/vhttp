//! The verified core interpreter (spec §Verified interpreter): runs a `ctcore::Program` on exec
//! values, proved to give the final return local, slots and steps of `ctcore::sem::run_fn` from
//! `init_entry`. It interprets core, not MIR; `theorem_sim` relates the two for completed MIR runs.
//! Differences from the spec that do not change the frame or the steps:
//! - no events are built (the ensures speak of the frame and the steps only);
//! - a run loops over the blocks of one activation (the spec recurses per block); calls recurse;
//! - frames are updated in place (`interp_val`).
#[allow(unused_imports)]
use crate::interp_arith::*;
#[allow(unused_imports)]
use crate::interp_val::*;
#[cfg(verus_keep_ghost)]
use ctcore::sem::*;
use ctcore::syntax::*;
use ctcore::sem::Val;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ cursors

/// A place-walk cursor: at a location (`loc`, a `Snap`-free path), or inside a snapshot.
pub struct XCur { pub root: CRoot, pub path: Vec<XPE>, pub loc: bool }

pub open spec fn xcur_v(fr: Frame, c: XCur) -> Cur {
    if c.loc { Cur::L(Loc { root: root_v(c.root), path: xpes(c.path@) }) } else { Cur::V(xread(base_v(fr, root_v(c.root)), c.path@)) }
}

pub open spec fn xcur_wf(c: XCur) -> bool { c.loc ==> no_snap(c.path@) }

/// `read_loc` of a cursor's location is its `xread`.
proof fn lemma_cur_read(fr: Frame, c: XCur)
    requires xcur_wf(c), c.loc,
    ensures read_loc(fr, Loc { root: root_v(c.root), path: xpes(c.path@) }) == xread(base_v(fr, root_v(c.root)), c.path@),
{
    lemma_xread_loc(base_v(fr, root_v(c.root)), c.path@);
}

fn local_int(fr: &CFrame, x: usize) -> (n: u128)
    ensures n == as_int(read_loc(fv(*fr), local_loc(x as nat))),
{
    if x < fr.locals.len() {
        match &fr.locals[x] { CVal::Int(n) => *n, _ => 0 }
    } else {
        0
    }
}

/// The location a cursor's leaf `Mut` points to, if its leaf is a `Mut`.
fn mut_leaf(fr: &CFrame, c: &XCur) -> (r: Option<CLoc>)
    ensures match r {
        Some(l) => xread(base_v(fv(*fr), root_v(c.root)), c.path@) == Val::Mut(loc_v(l)),
        None => !(xread(base_v(fv(*fr), root_v(c.root)), c.path@) is Mut),
    },
{
    let r = at(fr, &c.root, &c.path);
    match r {
        (Some(x), None) => match x { CVal::Mut(l) => Some(clone_loc(l)), _ => None },
        (Some(_x), Some(_)) => { proof { lemma_cv(*_x); } None },
        (None, _) => None,
    }
}

fn walk_exec(fr: &CFrame, pl: &Place) -> (c: XCur)
    ensures xcur_wf(c), xcur_v(fv(*fr), c) == place_walk(fv(*fr), *pl).0,
{
    let ghost f = fv(*fr);
    let mut c = XCur { root: CRoot::Local(pl.local), path: Vec::new(), loc: true };
    proof { assert(xpes(c.path@) =~= Seq::<PE>::empty()); }
    let mut k: usize = 0;
    while k < pl.proj.len()
        invariant k <= pl.proj@.len(), xcur_wf(c), f == fv(*fr),
            walk(f, pl.proj@, k as nat, xcur_v(f, c)).0 == place_walk(f, *pl).0,
        decreases pl.proj.len() - k,
    {
        let ghost c0 = xcur_v(f, c);
        let ghost s1 = step(f, c0, pl.proj@[k as int]).0;
        proof { assert(walk(f, pl.proj@, k as nat, c0).0 == walk(f, pl.proj@, (k + 1) as nat, s1).0); }
        let ghost p0 = c.path@;
        match &pl.proj[k] {
            Proj::Deref => {
                if c.loc {
                    proof { lemma_cur_read(f, c); }
                    match mut_leaf(fr, &c) {
                        Some(l2) => {
                            let np = xpath_of(&l2.path);
                            c = XCur { root: l2.root, path: np, loc: true };
                        },
                        None => {
                            c.path.push(XPE::Snap);
                            c.loc = false;
                            proof { lemma_xread_push(base_v(f, root_v(c.root)), p0, XPE::Snap); }
                        },
                    }
                } else {
                    c.path.push(XPE::Snap);
                    proof { lemma_xread_push(base_v(f, root_v(c.root)), p0, XPE::Snap); }
                }
            },
            Proj::Field(i) => {
                c.path.push(XPE::Field(*i));
                proof { lemma_xread_push(base_v(f, root_v(c.root)), p0, XPE::Field(*i)); lemma_push_wf(p0, XPE::Field(*i)); }
            },
            Proj::Index(x) => {
                let i = local_int(fr, *x);
                c.path.push(XPE::Index(i));
                proof { lemma_xread_push(base_v(f, root_v(c.root)), p0, XPE::Index(i)); lemma_push_wf(p0, XPE::Index(i)); }
            },
            Proj::ConstIndex(n) => {
                c.path.push(XPE::Index(*n as u128));
                proof { lemma_xread_push(base_v(f, root_v(c.root)), p0, XPE::Index(*n as u128)); lemma_push_wf(p0, XPE::Index(*n as u128)); }
            },
            Proj::Downcast(n) => {
                c.path.push(XPE::Variant(*n));
                proof { lemma_xread_push(base_v(f, root_v(c.root)), p0, XPE::Variant(*n)); lemma_push_wf(p0, XPE::Variant(*n)); }
            },
        }
        proof { assert(xcur_v(f, c) == s1); }
        k += 1;
    }
    c
}

proof fn lemma_push_wf(p: Seq<XPE>, e: XPE)
    requires !(e is Snap),
    ensures no_snap(p) ==> no_snap(p.push(e)), xpes(p.push(e)) == xpes(p).push(match e {
        XPE::Field(f) => PE::Field(f as nat), XPE::Index(x) => PE::Index(x as nat), XPE::Variant(k) => PE::Variant(k as nat), XPE::Snap => PE::Field(0),
    }),
{
    assert(xpes(p.push(e)) =~= xpes(p).push(match e {
        XPE::Field(f) => PE::Field(f as nat), XPE::Index(x) => PE::Index(x as nat), XPE::Variant(k) => PE::Variant(k as nat), XPE::Snap => PE::Field(0),
    }));
}

/// What a cursor reads (`read_place` once the walk is done).
proof fn lemma_cur_val(fr: Frame, c: XCur)
    requires xcur_wf(c),
    ensures (match xcur_v(fr, c) { Cur::L(l) => read_loc(fr, l), Cur::V(v) => v }) == xread(base_v(fr, root_v(c.root)), c.path@),
{
    if c.loc { lemma_cur_read(fr, c); }
}

pub fn read_place_exec(fr: &CFrame, pl: &Place) -> (v: CVal)
    ensures cv(v) == read_place(fv(*fr), *pl).0,
{
    let c = walk_exec(fr, pl);
    proof { lemma_cur_val(fv(*fr), c); }
    take(at(fr, &c.root, &c.path))
}

fn read_int(fr: &CFrame, pl: &Place) -> (n: u128)
    ensures n == as_int(read_place(fv(*fr), *pl).0),
{
    let c = walk_exec(fr, pl);
    proof { lemma_cur_val(fv(*fr), c); }
    take_int(at(fr, &c.root, &c.path))
}

pub fn place_loc_exec(fr: &CFrame, pl: &Place) -> (r: Option<CLoc>)
    ensures match place_loc(fv(*fr), *pl) { Some((l, _)) => r matches Some(x) && loc_v(x) == l, None => r is None },
{
    let c = walk_exec(fr, pl);
    if c.loc { Some(CLoc { root: c.root, path: cpath_of(&c.path) }) } else { None }
}

// ------------------------------------------------------------------ writes

pub fn write_loc_exec(fr: &mut CFrame, l: &CLoc, w: CVal)
    ensures fv(*final(fr)) == write_loc(fv(*old(fr)), loc_v(*l), cv(w)),
{
    proof { assert(l.path@.subrange(0, l.path@.len() as int) =~= l.path@); }
    match l.root {
        CRoot::Local(i) => if i < fr.locals.len() {
            let ghost o = fr.locals@;
            let x = take_at(&mut fr.locals, i);
            let y = set_at(x, &l.path, 0, w);
            fr.locals.set(i, y);
            proof { assert(fr.locals@ == o.update(i as int, y)); lemma_cvs_update(o, i as int, y); }
        },
        CRoot::Slot(j) => if j < fr.slots.len() {
            let ghost o = fr.slots@;
            let x = take_at(&mut fr.slots, j);
            let y = set_at(x, &l.path, 0, w);
            fr.slots.set(j, y);
            proof { assert(fr.slots@ == o.update(j as int, y)); lemma_cvs_update(o, j as int, y); }
        },
    }
}

pub fn assign_exec(fr: &mut CFrame, pl: &Place, v: CVal)
    ensures fv(*final(fr)) == assign(fv(*old(fr)), *pl, cv(v)).0,
{
    match place_loc_exec(fr, pl) {
        Some(l) => write_loc_exec(fr, &l, v),
        None => {},
    }
}

// ------------------------------------------------------------------ operands and rvalues

pub fn const_cval(c: &ConstVal) -> (v: CVal)
    ensures cv(v) == const_val(*c),
    decreases c,
{
    match c {
        ConstVal::Int(n) => CVal::Int(*n),
        ConstVal::Unit => CVal::Unit,
        ConstVal::Arr(cs) => {
            let vs = const_vec(cs);
            let v = CVal::Arr(vs);
            proof { lemma_cv(v); assert(cvs(vs@) =~= const_val(*c)->Arr_0); }
            v
        },
        ConstVal::Shr(b) => CVal::Shr(Box::new(const_cval(&**b))),
    }
}

fn const_vec(cs: &Vec<ConstVal>) -> (vs: Vec<CVal>)
    ensures vs@.len() == cs@.len(), forall|q: int| 0 <= q < cs@.len() ==> cv(#[trigger] vs@[q]) == const_val(cs@[q]),
    decreases cs,
{
    let mut vs: Vec<CVal> = Vec::new();
    let mut i: usize = 0;
    while i < cs.len()
        invariant i <= cs@.len(), vs@.len() == i, forall|q: int| 0 <= q < i ==> cv(#[trigger] vs@[q]) == const_val(cs@[q]),
        decreases cs.len() - i,
    {
        vs.push(const_cval(&cs[i]));
        i += 1;
    }
    vs
}

pub fn eval_op_exec(fr: &CFrame, op: &Operand) -> (v: CVal)
    ensures cv(v) == eval_op(fv(*fr), *op).0,
{
    match op {
        Operand::Copy(pl) => read_place_exec(fr, pl),
        Operand::Const(_, n) => CVal::Int(*n),
        Operand::Lit(c) => const_cval(c),
    }
}

fn op_int(fr: &CFrame, op: &Operand) -> (n: u128)
    ensures n == as_int(eval_op(fv(*fr), *op).0),
{
    match op {
        Operand::Copy(pl) => read_int(fr, pl),
        Operand::Const(_, n) => *n,
        Operand::Lit(c) => match c { ConstVal::Int(n) => *n, _ => 0 },
    }
}

pub fn op_vals_exec(fr: &CFrame, ops: &Vec<Operand>) -> (vs: Vec<CVal>)
    ensures cvs(vs@) == op_vals(fv(*fr), ops@),
{
    let mut vs: Vec<CVal> = Vec::new();
    let mut i: usize = 0;
    while i < ops.len()
        invariant i <= ops@.len(), vs@.len() == i, forall|q: int| 0 <= q < i ==> cv(#[trigger] vs@[q]) == eval_op(fv(*fr), ops@[q]).0,
        decreases ops.len() - i,
    {
        vs.push(eval_op_exec(fr, &ops[i]));
        i += 1;
    }
    proof { assert(cvs(vs@) =~= op_vals(fv(*fr), ops@)); }
    vs
}

/// `elems(fr, t).len()` for what `r` reads.
fn elems_len(fr: &CFrame, r: (Option<&CVal>, Option<usize>)) -> (n: usize)
    ensures forall|t: Val| nav_ok(r, t) ==> n == elems(fv(*fr), t).len(),
{
    match r {
        (Some(x), None) => {
            proof { lemma_cv(*x); }
            match x {
                CVal::Arr(vs) => vs.len(),
                CVal::Shr(b) => { proof { lemma_cv(**b); } match &**b { CVal::Arr(vs) => vs.len(), _ => 0 } },
                CVal::Mut(l) => {
                    let xp = xpath_of(&l.path);
                    proof { lemma_xread_loc(base_v(fv(*fr), root_v(l.root)), xp@); }
                    match at(fr, &l.root, &xp) {
                        (Some(y), None) => { proof { lemma_cv(*y); } match y { CVal::Arr(vs) => vs.len(), _ => 0 } },
                        (Some(_y), Some(_)) => { proof { lemma_cv(*_y); } 0 },
                        (None, _) => 0,
                    }
                },
                _ => 0,
            }
        },
        (Some(_x), Some(_)) => { proof { lemma_cv(*_x); } 0 },
        (None, _) => 0,
    }
}

/// `elems(fr, cv(v))`.
fn elems_exec(fr: &CFrame, v: CVal) -> (r: Vec<CVal>)
    ensures cvs(r@) == elems(fv(*fr), cv(v)),
{
    proof { lemma_cv(v); }
    match v {
        CVal::Arr(vs) => vs,
        CVal::Shr(b) => { proof { lemma_cv(*b); } match *b { CVal::Arr(vs) => vs, _ => Vec::new() } },
        CVal::Mut(l) => {
            let xp = xpath_of(&l.path);
            proof { lemma_xread_loc(base_v(fv(*fr), root_v(l.root)), xp@); }
            let t = take(at(fr, &l.root, &xp));
            proof { lemma_cv(t); }
            match t { CVal::Arr(vs) => vs, _ => Vec::new() }
        },
        _ => Vec::new(),
    }
}

fn discr_of(r: (Option<&CVal>, Option<usize>)) -> (n: u128)
    ensures forall|t: Val| nav_ok(r, t) ==> n == (match t { Val::Adt(k, _) => k as u128, _ => 0 }),
{
    match r {
        (Some(x), None) => { proof { lemma_cv(*x); } match x { CVal::Adt(k, _) => *k as u128, _ => 0 } },
        (Some(_x), Some(j)) => { proof { lemma_cv(*_x); } j as u128 },
        (None, _) => 0,
    }
}

pub fn eval_rv_exec(fr: &CFrame, rv: &Rvalue) -> (v: CVal)
    ensures cv(v) == eval_rv(fv(*fr), *rv).0,
{
    match rv {
        Rvalue::Use(op) => eval_op_exec(fr, op),
        Rvalue::Bin(op, ty, a, b) => {
            let (x, y) = (op_int(fr, a), op_int(fr, b));
            CVal::Int(binop_exec(op, ty, x, y))
        },
        Rvalue::Un(op, ty, a) => CVal::Int(unop_exec(op, ty, op_int(fr, a))),
        Rvalue::Cast(from, to, a) => CVal::Int(cast_exec(from, to, op_int(fr, a))),
        Rvalue::Len(pl) => {
            let c = walk_exec(fr, pl);
            proof { lemma_cur_val(fv(*fr), c); }
            CVal::Int(elems_len(fr, at(fr, &c.root, &c.path)) as u128)
        },
        Rvalue::Discr(pl) => {
            let c = walk_exec(fr, pl);
            proof { lemma_cur_val(fv(*fr), c); }
            CVal::Int(discr_of(at(fr, &c.root, &c.path)))
        },
        Rvalue::Aggregate(kind, ops) => {
            let vs = op_vals_exec(fr, ops);
            let v = match kind {
                AggKind::Tuple => CVal::Tup(vs),
                AggKind::Array => CVal::Arr(vs),
                AggKind::Adt(k) => CVal::Adt(*k, vs),
            };
            proof { lemma_cv(v); }
            v
        },
        Rvalue::Repeat(op, n) => {
            let x = eval_op_exec(fr, op);
            let mut vs: Vec<CVal> = Vec::new();
            let mut i: u64 = 0;
            while i < *n
                invariant i <= *n, vs@.len() == i, forall|q: int| 0 <= q < i ==> cv(#[trigger] vs@[q]) == cv(x),
                decreases *n - i,
            {
                vs.push(cclone(&x));
                i += 1;
            }
            let v = CVal::Arr(vs);
            proof { lemma_cv(v); assert(cvs(vs@) =~= Seq::new(*n as nat, |j: int| cv(x))); }
            v
        },
        Rvalue::RefShr(pl) => CVal::Shr(Box::new(read_place_exec(fr, pl))),
        Rvalue::RefMut(pl) => match place_loc_exec(fr, pl) {
            Some(l) => CVal::Mut(l),
            None => CVal::Unit,
        },
    }
}

// ------------------------------------------------------------------ statements

pub fn exec_stmt_exec(fr: &mut CFrame, s: &Stmt)
    ensures fv(*final(fr)) == exec_stmt(fv(*old(fr)), *s).0,
{
    match s {
        Stmt::Assign(pl, rv) => {
            let v = eval_rv_exec(fr, rv);
            assign_exec(fr, pl, v);
        },
        Stmt::SetDiscr(pl, k) => match place_loc_exec(fr, pl) {
            Some(l) => {
                let xp = xpath_of(&l.path);
                proof { lemma_xread_loc(base_v(fv(*fr), root_v(l.root)), xp@); }
                let v = take(at(fr, &l.root, &xp));
                proof { lemma_cv(v); }
                let nv = match v { CVal::Adt(_, vs) => CVal::Adt(*k, vs), v => v };
                proof { lemma_cv(nv); }
                write_loc_exec(fr, &l, nv);
            },
            None => {},
        },
    }
}

pub fn exec_stmts_exec(fr: &mut CFrame, ss: &Vec<Stmt>)
    ensures fv(*final(fr)) == exec_stmts(ss@, 0, fv(*old(fr))).0,
{
    let ghost f0 = fv(*fr);
    let mut k: usize = 0;
    while k < ss.len()
        invariant k <= ss@.len(), exec_stmts(ss@, k as nat, fv(*fr)).0 == exec_stmts(ss@, 0, f0).0,
        decreases ss.len() - k,
    {
        let ghost f1 = fv(*fr);
        exec_stmt_exec(fr, &ss[k]);
        proof { assert(exec_stmts(ss@, k as nat, f1).0 == exec_stmts(ss@, (k + 1) as nat, fv(*fr)).0); }
        k += 1;
    }
}

// ------------------------------------------------------------------ intrinsics

fn nth_take(vs: &mut Vec<CVal>, i: usize) -> (x: CVal)
    ensures cv(x) == nth(cvs(old(vs)@), i as nat), final(vs)@.len() == old(vs)@.len(),
        forall|q: int| 0 <= q < old(vs)@.len() && q != i ==> #[trigger] final(vs)@[q] == old(vs)@[q],
{
    if i < vs.len() { take_at(vs, i) } else { CVal::Unit }
}

/// Appends `xs` to the `Arr` at `l` (whose leaf is one).
fn push_loc(fr: &mut CFrame, l: &CLoc, xs: Vec<CVal>)
    requires read_loc(fv(*old(fr)), loc_v(*l)) is Arr,
    ensures fv(*final(fr)) == write_loc(fv(*old(fr)), loc_v(*l), Val::Arr(read_loc(fv(*old(fr)), loc_v(*l))->Arr_0 + cvs(xs@))),
{
    proof { assert(l.path@.subrange(0, l.path@.len() as int) =~= l.path@); }
    match l.root {
        CRoot::Local(i) => {
            if i >= fr.locals.len() { proof { lemma_read_at_unit(pes(l.path@)); } return; }
            let ghost o = fr.locals@;
            let x = take_at(&mut fr.locals, i);
            let y = push_at(x, &l.path, 0, xs);
            fr.locals.set(i, y);
            proof { assert(fr.locals@ == o.update(i as int, y)); lemma_cvs_update(o, i as int, y); }
        },
        CRoot::Slot(j) => {
            if j >= fr.slots.len() { proof { lemma_read_at_unit(pes(l.path@)); } return; }
            let ghost o = fr.slots@;
            let x = take_at(&mut fr.slots, j);
            let y = push_at(x, &l.path, 0, xs);
            fr.slots.set(j, y);
            proof { assert(fr.slots@ == o.update(j as int, y)); lemma_cvs_update(o, j as int, y); }
        },
    }
}

/// The length of the `Arr` at `l`, if its leaf is one.
fn arr_len_at(fr: &CFrame, l: &CLoc) -> (n: Option<usize>)
    ensures match n { Some(n) => read_loc(fv(*fr), loc_v(*l)) matches Val::Arr(s) && s.len() == n, None => !(read_loc(fv(*fr), loc_v(*l)) is Arr) },
{
    let xp = xpath_of(&l.path);
    proof { lemma_xread_loc(base_v(fv(*fr), root_v(l.root)), xp@); }
    match at(fr, &l.root, &xp) {
        (Some(y), None) => { proof { lemma_cv(*y); } match y { CVal::Arr(vs) => Some(vs.len()), _ => None } },
        (Some(_y), Some(_)) => { proof { lemma_cv(*_y); } None },
        (None, _) => None,
    }
}

/// `grow(fv(fr), cv(m), cvs(xs))`: `false` for its `None`.
fn grow_exec(fr: &mut CFrame, m: &CVal, xs: Vec<CVal>) -> (ok: bool)
    ensures match grow(fv(*old(fr)), cv(*m), cvs(xs@)) { Some(f) => ok && fv(*final(fr)) == f, None => !ok },
{
    match m {
        CVal::Mut(l) => match arr_len_at(fr, l) {
            None => true,
            Some(n) => {
                if n as u128 + xs.len() as u128 > 0xffff_ffff_ffff_ffff {
                    return false;
                }
                push_loc(fr, l, xs);
                true
            },
        },
        _ => { proof { lemma_cv(*m); } true },
    }
}

fn int_of(v: &CVal) -> (n: u128)
    ensures n == as_int(cv(*v)),
{
    match v { CVal::Int(n) => *n, _ => { proof { lemma_cv(*v); } 0 } }
}

/// `intr_cost` from the argument values.
pub open spec fn icost(k: Intrinsic, fr: Frame, vs: Seq<Val>) -> nat {
    match k {
        Intrinsic::VecExtendFromSlice => elems(fr, nth(vs, 1)).len(),
        Intrinsic::SliceToVec => elems(fr, nth(vs, 0)).len(),
        _ => 0,
    }
}

/// The frame-changing intrinsics: `VecPush`, `VecExtendFromSlice`, `VecSet`.
fn intr_mut(k: &Intrinsic, fr: &mut CFrame, a0: CVal, a1: CVal, a2: CVal, Ghost(vv): Ghost<Seq<Val>>) -> (r: Option<(CVal, u64)>)
    requires *k is VecPush || *k is VecExtendFromSlice || *k is VecSet,
        cv(a0) == nth(vv, 0), cv(a1) == nth(vv, 1), cv(a2) == nth(vv, 2),
    ensures match intr_eff(*k, fv(*old(fr)), vv) {
        Some((f1, v, _)) => r matches Some((x, n)) && fv(*final(fr)) == f1 && cv(x) == v && n as nat == icost(*k, fv(*old(fr)), vv),
        None => r is None,
    },
{
    match k {
        Intrinsic::VecPush => {
            let mut xs = Vec::new();
            xs.push(a1);
            proof { assert(cvs(xs@) =~= seq![nth(vv, 1)]); }
            if !grow_exec(fr, &a0, xs) { return None; }
            Some((CVal::Unit, 0))
        },
        Intrinsic::VecExtendFromSlice => {
            let xs = elems_exec(fr, a1);
            let n = xs.len() as u64;
            if !grow_exec(fr, &a0, xs) { return None; }
            Some((CVal::Unit, n))
        },
        _ => {
            let i = int_of(&a1);
            match a0 {
                CVal::Mut(l) => {
                    let mut path = l.path;
                    let ghost lp = path@;
                    path.push(CPE::Index(i));
                    let l2 = CLoc { root: l.root, path };
                    proof { assert(pes(l2.path@) =~= pes(lp).push(PE::Index(i as nat))); }
                    write_loc_exec(fr, &l2, a2);
                },
                _ => { proof { lemma_cv(a0); } },
            }
            Some((CVal::Unit, 0))
        },
    }
}

/// The other intrinsics: no frame change.
fn intr_pure(k: &Intrinsic, fr: &CFrame, a0: CVal, a1: CVal, a2: CVal, Ghost(vv): Ghost<Seq<Val>>) -> (r: Option<(CVal, u64)>)
    requires !(*k is VecPush || *k is VecExtendFromSlice || *k is VecSet),
        cv(a0) == nth(vv, 0), cv(a1) == nth(vv, 1), cv(a2) == nth(vv, 2),
    ensures match intr_eff(*k, fv(*fr), vv) {
        Some((f1, v, _)) => r matches Some((x, n)) && f1 == fv(*fr) && cv(x) == v && n as nat == icost(*k, fv(*fr), vv),
        None => r is None,
    },
{
    match k {
        Intrinsic::Declassify => Some((a0, 0)),
        Intrinsic::GhostUnit => Some((CVal::Unit, 0)),
        Intrinsic::VecNew | Intrinsic::VecWithCapacity => {
            let v = CVal::Arr(Vec::new());
            proof { lemma_cv(v); assert(cvs(Seq::<CVal>::empty()) =~= Seq::<Val>::empty()); }
            Some((v, 0))
        },
        Intrinsic::VecAsSlice | Intrinsic::ArrayAsSlice => Some((a0, 0)),
        Intrinsic::VecLen => {
            let n = elems_exec(fr, a0).len();
            Some((CVal::Int(n as u128), 0))
        },
        Intrinsic::VecIndex => {
            let i = int_of(&a1);
            let mut s = elems_exec(fr, a0);
            let q: usize = if i < s.len() as u128 { i as usize } else { s.len() };
            let x = nth_take(&mut s, q);
            Some((CVal::Shr(Box::new(x)), 0))
        },
        Intrinsic::SliceSubrange => {
            let s = elems_exec(fr, a0);
            let (lo, hi) = (int_of(&a1), int_of(&a2));
            let h: usize = if hi < s.len() as u128 { hi as usize } else { s.len() };
            let l: usize = if lo < h as u128 { lo as usize } else { h };
            let mut out: Vec<CVal> = Vec::new();
            let mut q = l;
            while q < h
                invariant l <= q <= h <= s@.len(), out@.len() == q - l, forall|z: int| 0 <= z < q - l ==> cv(#[trigger] out@[z]) == cv(s@[l + z]),
                decreases h - q,
            {
                out.push(cclone(&s[q]));
                q += 1;
            }
            let v = CVal::Arr(out);
            proof { lemma_cv(v); assert(cvs(out@) =~= cvs(s@).subrange(l as int, h as int)); }
            Some((CVal::Shr(Box::new(v)), 0))
        },
        Intrinsic::SliceToVec => {
            let s = elems_exec(fr, a0);
            let n = s.len() as u64;
            let v = CVal::Arr(s);
            proof { lemma_cv(v); }
            Some((v, n))
        },
        Intrinsic::Wrapping(op, ty) => Some((CVal::Int(binop_exec(op, ty, int_of(&a0), int_of(&a1))), 0)),
        _ => None,
    }
}

/// `exec_intr`: the cost, or `None`.
pub fn exec_intr_exec(k: &Intrinsic, fr: &mut CFrame, args: &Vec<Operand>, dst: &Place) -> (r: Option<u64>)
    ensures match exec_intr(*k, fv(*old(fr)), args@, *dst) {
        Some((f2, _, x)) => r == Some(x as u64) && x <= u64::MAX && fv(*final(fr)) == f2,
        None => r is None,
    },
{
    let ghost f0 = fv(*fr);
    let mut vs = op_vals_exec(fr, args);
    let ghost vv = cvs(vs@);
    proof { assert(op_vals(f0, args@) == vv); assert(intr_cost(*k, f0, args@) == icost(*k, f0, vv)); }
    let a0 = nth_take(&mut vs, 0);
    let a1 = nth_take(&mut vs, 1);
    let a2 = nth_take(&mut vs, 2);
    let r = match k {
        Intrinsic::VecPush | Intrinsic::VecExtendFromSlice | Intrinsic::VecSet => intr_mut(k, fr, a0, a1, a2, Ghost(vv)),
        _ => intr_pure(k, fr, a0, a1, a2, Ghost(vv)),
    };
    match r {
        None => None,
        Some((res, cost)) => {
            assign_exec(fr, dst, res);
            Some(cost)
        },
    }
}

// ------------------------------------------------------------------ calls

pub open spec fn wb_v(wb: Seq<Option<CLoc>>) -> Seq<Option<Loc>> {
    Seq::new(wb.len(), |j: int| match wb[j] { Some(l) => Some(loc_v(l)), None => None })
}

pub fn call_enter_exec(p: &Program, g: usize, fr: &CFrame, args: &Vec<Operand>) -> (r: (CFrame, Vec<Option<CLoc>>))
    ensures fv(r.0) == call_enter(*p, g as nat, fv(*fr), args@).0, wb_v(r.1@) == call_enter(*p, g as nat, fv(*fr), args@).1,
{
    let ghost f = fv(*fr);
    let mut vs = op_vals_exec(fr, args);
    let ghost vv = cvs(vs@);
    let n: usize = if g < p.fns.len() { p.fns[g].locals.len() } else { 0 };
    let mut slots: Vec<CVal> = Vec::new();
    let mut wb: Vec<Option<CLoc>> = Vec::new();
    let mut lv: Vec<CVal> = Vec::new();
    let mut j: usize = 0;
    while j < vs.len()
        invariant j <= vs@.len() == vv.len(), slots@.len() == j, wb@.len() == j, lv@.len() == j,
            forall|q: int| j <= q < vs@.len() ==> cv(#[trigger] vs@[q]) == vv[q],
            forall|q: int| 0 <= q < j ==> cv(#[trigger] slots@[q]) == (match vv[q] { Val::Mut(l) => read_loc(f, l), _ => Val::Unit }),
            forall|q: int| 0 <= q < j ==> (#[trigger] wb_v(wb@)[q]) == (match vv[q] { Val::Mut(l) => Some(l), _ => None }),
            forall|q: int| 0 <= q < j ==> cv(#[trigger] lv@[q]) == (match vv[q] { Val::Mut(_) => Val::Mut(Loc { root: Root::Slot(q as nat), path: seq![] }), v => v }),
            f == fv(*fr),
        decreases vs.len() - j,
    {
        let ghost wb0 = wb@;
        let x = take_at(&mut vs, j);
        proof { lemma_cv(x); }
        match x {
            CVal::Mut(l) => {
                let xp = xpath_of(&l.path);
                proof { lemma_xread_loc(base_v(f, root_v(l.root)), xp@); }
                slots.push(take(at(fr, &l.root, &xp)));
                let m = CVal::Mut(CLoc { root: CRoot::Slot(j), path: Vec::new() });
                proof { assert(pes(Seq::<CPE>::empty()) =~= Seq::<PE>::empty()); }
                lv.push(m);
                wb.push(Some(l));
            },
            x => {
                slots.push(CVal::Unit);
                wb.push(None);
                lv.push(x);
            },
        }
        proof {
            assert(wb@ == wb0.push(wb@[j as int]));
            assert(forall|q: int| 0 <= q < j ==> #[trigger] wb_v(wb@)[q] == wb_v(wb0)[q]);
            assert(wb_v(wb@)[j as int] == (match wb@[j as int] { Some(l) => Some(loc_v(l)), None => None }));
        }
        j += 1;
    }
    let mut locals: Vec<CVal> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n, locals@.len() == i, lv@.len() == vv.len(),
            forall|q: int| 0 <= q < i ==> cv(#[trigger] locals@[q]) == (if 1 <= q <= vv.len() {
                match vv[q - 1] { Val::Mut(_) => Val::Mut(Loc { root: Root::Slot((q - 1) as nat), path: seq![] }), v => v } } else { Val::Unit }),
            forall|q: int| i <= q + 1 && 0 <= q < lv@.len() ==> cv(#[trigger] lv@[q]) == (match vv[q] { Val::Mut(_) => Val::Mut(Loc { root: Root::Slot(q as nat), path: seq![] }), v => v }),
        decreases n - i,
    {
        let x = if 1 <= i && i <= lv.len() { take_at(&mut lv, i - 1) } else { CVal::Unit };
        locals.push(x);
        i += 1;
    }
    let ghost ce = call_enter(*p, g as nat, f, args@);
    proof {
        assert(op_vals(f, args@) == vv);
        assert(cvs(locals@) =~= ce.0.locals);
        assert(cvs(slots@) =~= ce.0.slots);
        assert(wb_v(wb@) =~= ce.1);
    }
    (CFrame { locals, slots }, wb)
}

pub fn call_leave_exec(fr: &mut CFrame, callee: CFrame, wb: &Vec<Option<CLoc>>, dst: &Place)
    ensures fv(*final(fr)) == call_leave(fv(*old(fr)), fv(callee), wb_v(wb@), *dst).0,
{
    let ghost f0 = fv(*fr);
    let ghost cs = cvs(callee.slots@);
    let CFrame { locals: mut cl, slots: mut sl } = callee;
    let mut j: usize = 0;
    while j < wb.len()
        invariant j <= wb@.len(), sl@.len() == cs.len(),
            forall|q: int| j <= q < sl@.len() ==> cv(#[trigger] sl@[q]) == cs[q],
            fv(*fr) == write_back(f0, cs, wb_v(wb@).subrange(0, j as int)),
        decreases wb.len() - j,
    {
        let ghost f1 = fv(*fr);
        let ghost s1 = sl@;
        proof { assert(wb_v(wb@).subrange(0, j + 1).drop_last() =~= wb_v(wb@).subrange(0, j as int)); }
        match &wb[j] {
            Some(l) => {
                let x = nth_take(&mut sl, j);
                write_loc_exec(fr, l, x);
            },
            None => {},
        }
        proof { assert(forall|q: int| j < q < sl@.len() ==> #[trigger] sl@[q] == s1[q]); }
        j += 1;
    }
    proof { assert(wb_v(wb@).subrange(0, wb@.len() as int) =~= wb_v(wb@)); }
    let r = nth_take(&mut cl, 0);
    assign_exec(fr, dst, r);
}

// ------------------------------------------------------------------ runs

/// A run's final frame and steps.
pub open spec fn fs(r: Res) -> Option<(Frame, nat)> { match r { Some((g, _, n)) => Some((g, n)), None => None } }

pub open spec fn plus(o: Option<(Frame, nat)>, n: nat) -> Option<(Frame, nat)> { match o { Some((g, m)) => Some((g, m + n)), None => None } }

/// `cur` is what remains of `s0` after `k` steps: both `None`, or the same frame with `k` more
/// steps in `s0`.
pub open spec fn rel(s0: Option<(Frame, nat)>, cur: Option<(Frame, nat)>, k: nat) -> bool {
    &&& (s0 is None <==> cur is None)
    &&& s0 is Some ==> s0->Some_0.0 == cur->Some_0.0 && s0->Some_0.1 == cur->Some_0.1 + k
}

pub open spec fn run_ok(s: Res, r: Option<(CFrame, u64)>) -> bool {
    &&& r matches Some((f2, n)) ==> s matches Some((g, _, m)) && fv(f2) == g && n as nat == m
    &&& s is None ==> r is None
    &&& (s is Some && s->Some_0.2 <= u64::MAX) ==> r is Some
}

/// What `run_from` does after a block's statements (frame `f1`), its frame and steps less the
/// block's own.
pub open spec fn after(p: Program, f: nat, f1: Frame, fuel1: nat, term: Term) -> Option<(Frame, nat)> {
    match term {
        Term::Goto(b2) => fs(run_from(p, f, b2 as nat, f1, fuel1)),
        Term::Switch(op, ts, o) => fs(run_from(p, f, switch_target(ts@, 0, as_int(eval_op(f1, op).0), o) as nat, f1, fuel1)),
        Term::Assert(op, e, b2) => if (as_int(eval_op(f1, op).0) != 0) == e { fs(run_from(p, f, b2 as nat, f1, fuel1)) } else { None },
        Term::Return => Some((f1, 0)),
        Term::Abort => None,
        Term::Call(Callee::Fn(g), args, dst, next) => {
            let (cf, wb, _) = call_enter(p, g as nat, f1, args@);
            match run_from(p, g as nat, 0, cf, fuel1) {
                Some((cf2, _, cn)) => plus(fs(run_from(p, f, next as nat, call_leave(f1, cf2, wb, dst).0, fuel1)), cn),
                None => None,
            }
        },
        Term::Call(Callee::Intr(k), args, dst, next) => match exec_intr(k, f1, args@, dst) {
            Some((f2, _, x)) => plus(fs(run_from(p, f, next as nat, f2, fuel1)), x),
            None => None,
        },
    }
}

proof fn lemma_unfold(p: Program, f: nat, b: nat, fr: Frame, fuel: nat)
    requires fuel > 0, f < p.fns@.len(), b < p.fns@[f as int].blocks@.len(),
    ensures ({
        let blk = p.fns@[f as int].blocks@[b as int];
        fs(run_from(p, f, b, fr, fuel)) == plus(after(p, f, exec_stmts(blk.stmts@, 0, fr).0, (fuel - 1) as nat, blk.term), blk.stmts@.len() + 1)
    }),
{
    let blk = p.fns@[f as int].blocks@[b as int];
    match blk.term {
        Term::Call(Callee::Fn(_), _, _, _) => lemma_unfold_call(p, f, b, fr, fuel),
        Term::Call(Callee::Intr(_), _, _, _) => lemma_unfold_intr(p, f, b, fr, fuel),
        _ => lemma_unfold_jump(p, f, b, fr, fuel),
    }
}

proof fn lemma_stop(p: Program, f: nat, b: nat, fr: Frame, fuel: nat)
    requires fuel == 0 || f >= p.fns@.len() || b >= p.fns@[f as int].blocks@.len(),
    ensures run_from(p, f, b, fr, fuel) is None,
{}

proof fn lemma_unfold_jump(p: Program, f: nat, b: nat, fr: Frame, fuel: nat)
    requires fuel > 0, f < p.fns@.len(), b < p.fns@[f as int].blocks@.len(), !(p.fns@[f as int].blocks@[b as int].term is Call),
    ensures ({
        let blk = p.fns@[f as int].blocks@[b as int];
        fs(run_from(p, f, b, fr, fuel)) == plus(after(p, f, exec_stmts(blk.stmts@, 0, fr).0, (fuel - 1) as nat, blk.term), blk.stmts@.len() + 1)
    }),
{
    hide(exec_intr);
    hide(call_enter);
    hide(call_leave);
    hide(exec_stmts);
    hide(eval_op);
}

proof fn lemma_unfold_call(p: Program, f: nat, b: nat, fr: Frame, fuel: nat)
    requires fuel > 0, f < p.fns@.len(), b < p.fns@[f as int].blocks@.len(), p.fns@[f as int].blocks@[b as int].term matches Term::Call(Callee::Fn(_), _, _, _),
    ensures ({
        let blk = p.fns@[f as int].blocks@[b as int];
        fs(run_from(p, f, b, fr, fuel)) == plus(after(p, f, exec_stmts(blk.stmts@, 0, fr).0, (fuel - 1) as nat, blk.term), blk.stmts@.len() + 1)
    }),
{
    hide(exec_intr);
    hide(call_enter);
    hide(call_leave);
    hide(exec_stmts);
    hide(eval_op);
}

proof fn lemma_unfold_intr(p: Program, f: nat, b: nat, fr: Frame, fuel: nat)
    requires fuel > 0, f < p.fns@.len(), b < p.fns@[f as int].blocks@.len(), p.fns@[f as int].blocks@[b as int].term matches Term::Call(Callee::Intr(_), _, _, _),
    ensures ({
        let blk = p.fns@[f as int].blocks@[b as int];
        fs(run_from(p, f, b, fr, fuel)) == plus(after(p, f, exec_stmts(blk.stmts@, 0, fr).0, (fuel - 1) as nat, blk.term), blk.stmts@.len() + 1)
    }),
{
    hide(exec_intr);
    hide(call_enter);
    hide(call_leave);
    hide(exec_stmts);
    hide(eval_op);
}

fn switch_exec(ts: &Vec<(u128, usize)>, v: u128, otherwise: usize) -> (r: usize)
    ensures r == switch_target(ts@, 0, v, otherwise),
{
    let mut k: usize = 0;
    while k < ts.len()
        invariant k <= ts@.len(), switch_target(ts@, k as nat, v, otherwise) == switch_target(ts@, 0, v, otherwise),
        decreases ts.len() - k,
    {
        if ts[k].0 == v { return ts[k].1; }
        k += 1;
    }
    otherwise
}

/// A call terminator from frame `fr`: the callee's steps, with `fr` the frame after `call_leave`;
/// `None` when the callee's run is `None` or past `u64` steps.
fn call_exec(p: &Program, g: usize, fr: &mut CFrame, args: &Vec<Operand>, dst: &Place, fuel: u64) -> (r: Option<u64>)
    ensures ({
        let (cf, wb, _) = call_enter(*p, g as nat, fv(*old(fr)), args@);
        let s = run_from(*p, g as nat, 0, cf, fuel as nat);
        &&& r matches Some(cn) ==> s matches Some((cf2, _, m)) && m == cn && fv(*final(fr)) == call_leave(fv(*old(fr)), cf2, wb, *dst).0
        &&& r is None ==> (s is None || s->Some_0.2 > u64::MAX)
    }),
    decreases fuel + 1, 0nat,
{
    hide(run_from);
    hide(call_enter);
    hide(call_leave);
    let (cf, wb) = call_enter_exec(p, g, fr, args);
    match run_exec(p, g, cf, fuel) {
        None => None,
        Some((cf2, cn)) => {
            call_leave_exec(fr, cf2, &wb, dst);
            Some(cn)
        },
    }
}

#[verifier::loop_isolation(false)]
pub fn run_exec(p: &Program, f: usize, fr: CFrame, fuel: u64) -> (r: Option<(CFrame, u64)>)
    ensures run_ok(run_from(*p, f as nat, 0, fv(fr), fuel as nat), r),
    decreases fuel, 1nat,
{
    hide(run_from);
    hide(call_enter);
    hide(call_leave);
    hide(exec_intr);
    hide(exec_stmts);
    let ghost s0 = fs(run_from(*p, f as nat, 0, fv(fr), fuel as nat));
    let mut fr = fr;
    let mut b: usize = 0;
    let mut fc: u64 = fuel;
    let mut steps: u64 = 0;
    loop
        invariant fc <= fuel, rel(s0, fs(run_from(*p, f as nat, b as nat, fv(fr), fc as nat)), steps as nat),
        decreases fc,
    {
        if fc == 0 || f >= p.fns.len() || b >= p.fns[f].blocks.len() {
            proof { lemma_stop(*p, f as nat, b as nat, fv(fr), fc as nat); }
            return None;
        }
        let blk = &p.fns[f].blocks[b];
        proof { lemma_unfold(*p, f as nat, b as nat, fv(fr), fc as nat); }
        exec_stmts_exec(&mut fr, &blk.stmts);
        if blk.stmts.len() as u128 + 1 + steps as u128 > u64::MAX as u128 {
            return None;
        }
        steps = steps + blk.stmts.len() as u64 + 1;
        let ghost a = after(*p, f as nat, fv(fr), (fc - 1) as nat, blk.term);
        proof { assert(rel(s0, a, steps as nat)); }
        match &blk.term {
            Term::Goto(b2) => { b = *b2; },
            Term::Switch(op, ts, otherwise) => {
                let v = op_int(&fr, op);
                b = switch_exec(ts, v, *otherwise);
            },
            Term::Assert(op, expected, b2) => {
                let v = op_int(&fr, op);
                if (v != 0) != *expected { return None; }
                b = *b2;
            },
            Term::Return => { return Some((fr, steps)); },
            Term::Abort => { return None; },
            Term::Call(Callee::Fn(g), args, dst, next) => {
                match call_exec(p, *g, &mut fr, args, dst, fc - 1) {
                    None => { return None; },
                    Some(cn) => {
                        if steps > u64::MAX - cn { return None; }
                        steps = steps + cn;
                    },
                }
                b = *next;
            },
            Term::Call(Callee::Intr(k), args, dst, next) => {
                match exec_intr_exec(k, &mut fr, args, dst) {
                    None => { return None; },
                    Some(x) => {
                        if steps > u64::MAX - x { return None; }
                        steps = steps + x;
                    },
                }
                b = *next;
            },
        }
        fc = fc - 1;
    }
}

pub fn init_entry_exec(p: &Program, g: usize, args: &Vec<CVal>, slots: &Vec<CVal>) -> (fr: CFrame)
    ensures fv(fr) == init_entry(*p, g as nat, cvs(args@), cvs(slots@)),
{
    let sl = clone_vec(slots);
    if g >= p.fns.len() {
        let fr = CFrame { locals: Vec::new(), slots: sl };
        proof { assert(cvs(fr.locals@) =~= Seq::<Val>::empty()); }
        return fr;
    }
    let body = &p.fns[g];
    let mut locals: Vec<CVal> = Vec::new();
    let mut i: usize = 0;
    while i < body.locals.len()
        invariant i <= body.locals@.len(), locals@.len() == i, body == p.fns@[g as int],
            forall|q: int| 0 <= q < i ==> cv(#[trigger] locals@[q]) == (if 1 <= q <= body.nargs {
                if body.locals@[q] is Mut { Val::Mut(Loc { root: Root::Slot((q - 1) as nat), path: seq![] }) } else { nth(cvs(args@), (q - 1) as nat) }
            } else { Val::Unit }),
        decreases body.locals.len() - i,
    {
        let x = if 1 <= i && i <= body.nargs {
            match &body.locals[i] {
                Ty::Mut(_) => {
                    let m = CVal::Mut(CLoc { root: CRoot::Slot(i - 1), path: Vec::new() });
                    proof { assert(pes(Seq::<CPE>::empty()) =~= Seq::<PE>::empty()); }
                    m
                },
                _ => if i - 1 < args.len() { cclone(&args[i - 1]) } else { CVal::Unit },
            }
        } else {
            CVal::Unit
        };
        locals.push(x);
        i += 1;
    }
    let fr = CFrame { locals, slots: sl };
    proof { assert(cvs(fr.locals@) =~= init_entry(*p, g as nat, cvs(args@), cvs(slots@)).locals); }
    fr
}

/// **The interpreter.** `r` is the return local, the slots and the steps of `run_fn` from
/// `init_entry` when that run completes within `u64` steps, and `None` when it does not complete.
pub fn interp(p: &Program, g: usize, args: &Vec<CVal>, slots: &Vec<CVal>, fuel: u64) -> (r: Option<(CVal, Vec<CVal>, u64)>)
    ensures ({
        let s = run_fn(*p, g as nat, init_entry(*p, g as nat, cvs(args@), cvs(slots@)), fuel as nat);
        &&& r matches Some((ret, sl, n)) ==> s matches Some((fr, _, m)) && cv(ret) == nth(fr.locals, 0) && cvs(sl@) == fr.slots && n as nat == m
        &&& s is None ==> r is None
        &&& (s is Some && s->Some_0.2 <= u64::MAX) ==> r is Some
    }),
{
    let fr = init_entry_exec(p, g, args, slots);
    match run_exec(p, g, fr, fuel) {
        Some((f2, n)) => {
            let CFrame { locals: mut l, slots: sl } = f2;
            let ret = nth_take(&mut l, 0);
            Some((ret, sl, n))
        },
        None => None,
    }
}

} // verus!
