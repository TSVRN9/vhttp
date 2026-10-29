//! CT typing (spec; trusted, frozen from the end of Phase 8a Task 3): labels, the supported
//! subset `wf`, the per-construct rules of the design's CT typing table, agreement of two frames,
//! the `Mut` label-consistency invariant `plc`, and the trace relation `diverge`.
//!
//! The core values carry no types, so the design's "`Mut` only as a top-level local type" is
//! enforced in two halves: `wf` restricts the declared local types, and the typing rules let a
//! `Mut` value flow only into an empty-projection `Mut`-typed local (`mut_pl`). `plc` is the
//! resulting run-time invariant.
#[allow(unused_imports)]
use crate::sem::*;
#[allow(unused_imports)]
use crate::syntax::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ labels

/// Labels of one function's locals (true = secret). Slot `j` has the label of local `1 + j`.
pub struct FnLab { pub locals: Vec<bool> }

pub open spec fn lab(l: FnLab, x: nat) -> bool { l.locals@[x as int] }

pub open spec fn slot_lab(l: FnLab, j: nat) -> bool { l.locals@[(1 + j) as int] }

pub open spec fn root_lab(l: FnLab, r: Root) -> bool {
    match r { Root::Local(x) => lab(l, x), Root::Slot(j) => slot_lab(l, j) }
}

// ------------------------------------------------------------------ wf: the supported subset

/// `t` contains `Mut` anywhere, including at the top.
pub open spec fn ty_has_mut(t: Ty) -> bool
    decreases t,
{
    match t {
        Ty::Int(_) => false,
        Ty::Unit => false,
        Ty::Tuple(ts) => exists|i: int| 0 <= i < ts@.len() && ty_has_mut(#[trigger] ts@[i]),
        Ty::Adt(vs) => exists|i: int, k: int| 0 <= i < vs@.len() && 0 <= k < vs@[i]@.len() && ty_has_mut(#[trigger] vs@[i]@[k]),
        Ty::Array(e, _) => ty_has_mut(*e),
        Ty::Slice(e) => ty_has_mut(*e),
        Ty::Vec(e) => ty_has_mut(*e),
        Ty::Shr(e) => ty_has_mut(*e),
        Ty::Mut(_) => true,
    }
}

/// A non-return local's type: `Mut` only at the top level.
pub open spec fn wf_local_ty(t: Ty) -> bool {
    match t { Ty::Mut(inner) => !ty_has_mut(*inner), _ => !ty_has_mut(t) }
}

/// Every block target is in range; a `Fn` callee is in range and gets one arg per parameter.
pub open spec fn wf_term(p: Program, f: nat, t: Term) -> bool {
    let n = p.fns@[f as int].blocks@.len();
    match t {
        Term::Goto(b) => b < n,
        Term::Switch(_, ts, o) => o < n && forall|k: int| 0 <= k < ts@.len() ==> (#[trigger] ts@[k]).1 < n,
        Term::Assert(_, _, b) => b < n,
        Term::Call(Callee::Fn(g), args, _, next) =>
            g < p.fns@.len() && args@.len() == p.fns@[g as int].nargs && next < n,
        Term::Call(Callee::Intr(_), _, _, next) => next < n,
        Term::Return => true,
        Term::Abort => true,
    }
}

/// The trigger predicate for `wf_body`'s quantifier over blocks.
pub open spec fn wf_block(p: Program, f: nat, blk: Block) -> bool { wf_term(p, f, blk.term) }

/// At least one block; local 0 and the parameters exist; `Mut` only as the top-level type of a
/// local other than 0; every target in range.
pub open spec fn wf_body(p: Program, f: nat) -> bool {
    let b = p.fns@[f as int];
    &&& b.blocks@.len() >= 1
    &&& b.nargs < b.locals@.len()
    &&& !ty_has_mut(b.locals@[0])
    &&& forall|i: int| 0 < i < b.locals@.len() ==> wf_local_ty(#[trigger] b.locals@[i])
    &&& forall|i: int| 0 <= i < b.blocks@.len() ==> #[trigger] wf_block(p, f, b.blocks@[i])
}

pub open spec fn wf(p: Program) -> bool {
    forall|f: nat| f < p.fns@.len() ==> #[trigger] wf_body(p, f)
}

// ------------------------------------------------------------------ per-construct typing

/// The place is an empty-projection `Mut`-typed local: the only place whose value may be a `Mut`.
pub open spec fn mut_pl(b: Body, pl: Place) -> bool {
    pl.proj@.len() == 0 && pl.local < b.locals@.len() && b.locals@[pl.local as int] is Mut
}

/// The operand may yield a `Mut` value.
pub open spec fn mut_op(b: Body, op: Operand) -> bool {
    match op { Operand::Copy(pl) => mut_pl(b, pl), _ => false }
}

/// `rd(pl)` = `lab(pl.local)`, also through `Deref` (`plc`) and for snapshots.
pub open spec fn sec_op(b: Body, l: FnLab, op: Operand) -> bool {
    match op {
        Operand::Copy(pl) => lab(l, pl.local as nat),
        Operand::Const(_, _) => false,
        Operand::Lit(_) => false,
    }
}

pub open spec fn ok_place(b: Body, l: FnLab, pl: Place) -> bool {
    &&& pl.local < b.locals@.len()
    // rule: Index(x) projection, anywhere | x public
    &&& forall|k: int| 0 <= k < pl.proj@.len() && (#[trigger] pl.proj@[k]) is Index ==>
            pl.proj@[k]->Index_0 < b.locals@.len() && !lab(l, pl.proj@[k]->Index_0 as nat)
}

pub open spec fn ok_op(b: Body, l: FnLab, op: Operand) -> bool {
    match op { Operand::Copy(pl) => ok_place(b, l, pl), _ => true }
}

pub open spec fn div_like(op: BinOp) -> bool { op is Div || op is Rem }

pub open spec fn shift_like(op: BinOp) -> bool { op is Shl || op is Shr }

/// No `&mut` of an empty-projection `Mut`-typed local, so a `Mut` never targets one.
pub open spec fn refmut_ok(b: Body, pl: Place) -> bool {
    b.locals@[pl.local as int] is Mut ==> pl.proj@.len() > 0 && pl.proj@[0] is Deref
}

pub open spec fn sec_rv(b: Body, l: FnLab, rv: Rvalue) -> bool {
    match rv {
        // rule: other Use/Bin/Un/Cast/Aggregate/Repeat | join of their operands
        Rvalue::Use(op) => sec_op(b, l, op),
        Rvalue::Bin(_, _, x, y) => sec_op(b, l, x) || sec_op(b, l, y),
        Rvalue::Un(_, _, x) => sec_op(b, l, x),
        Rvalue::Cast(_, _, x) => sec_op(b, l, x),
        // rule: Len, Discr | public (D7)
        Rvalue::Len(_) => false,
        Rvalue::Discr(_) => false,
        Rvalue::Aggregate(_, ops) => exists|i: int| 0 <= i < ops@.len() && sec_op(b, l, #[trigger] ops@[i]),
        Rvalue::Repeat(x, _) => sec_op(b, l, x),
        // rule: RefShr(pl) | rd(pl)
        Rvalue::RefShr(pl) => lab(l, pl.local as nat),
        // rule: RefMut(pl) | wr(pl)
        Rvalue::RefMut(pl) => lab(l, pl.local as nat),
    }
}

pub open spec fn ok_rv(b: Body, l: FnLab, rv: Rvalue) -> bool {
    match rv {
        Rvalue::Use(op) => ok_op(b, l, op),
        Rvalue::Bin(op, _, x, y) => {
            &&& ok_op(b, l, x) && ok_op(b, l, y)
            // rule: Bin Div/Rem | both operands public
            &&& div_like(op) ==> !sec_op(b, l, x) && !sec_op(b, l, y)
            // rule: Bin Shl/Shr | rhs public
            &&& shift_like(op) ==> !sec_op(b, l, y)
        },
        Rvalue::Un(_, _, x) => ok_op(b, l, x),
        Rvalue::Cast(_, _, x) => ok_op(b, l, x),
        Rvalue::Len(pl) => ok_place(b, l, pl),
        Rvalue::Discr(pl) => ok_place(b, l, pl),
        // rule: wf (Mut not inside aggregates)
        Rvalue::Aggregate(_, ops) => forall|i: int| 0 <= i < ops@.len() ==> ok_op(b, l, #[trigger] ops@[i]) && !mut_op(b, ops@[i]),
        Rvalue::Repeat(x, _) => ok_op(b, l, x) && !mut_op(b, x),
        // rule: wf (Mut not inside a snapshot)
        Rvalue::RefShr(pl) => ok_place(b, l, pl) && !mut_pl(b, pl),
        Rvalue::RefMut(pl) => ok_place(b, l, pl) && refmut_ok(b, pl),
    }
}

pub open spec fn ok_stmt(b: Body, l: FnLab, s: Stmt) -> bool {
    match s {
        Stmt::Assign(pl, rv) => ok_place(b, l, pl) && ok_rv(b, l, rv) && match rv {
            // rule: RefMut(pl) | lab(dst) == wr(pl)
            Rvalue::RefMut(q) => mut_pl(b, pl) && lab(l, pl.local as nat) == lab(l, q.local as nat),
            // rule: Assign(pl, rv) | if the value type contains Mut, ==
            Rvalue::Use(op) => if mut_op(b, op) {
                mut_pl(b, pl) && sec_op(b, l, op) == lab(l, pl.local as nat)
            } else {
                sec_op(b, l, op) ==> lab(l, pl.local as nat)
            },
            // rule: Assign(pl, rv) | lab(rv) ⊑ wr(pl)
            _ => sec_rv(b, l, rv) ==> lab(l, pl.local as nat),
        },
        Stmt::SetDiscr(pl, _) => ok_place(b, l, pl),
    }
}

/// `sec_op` of arg `i`.
pub open spec fn sa(b: Body, l: FnLab, args: Seq<Operand>, i: int) -> bool { sec_op(b, l, args[i]) }

pub open spec fn ok_intr(b: Body, l: FnLab, k: Intrinsic, args: Seq<Operand>, dst: Place) -> bool {
    let ld = lab(l, dst.local as nat);
    &&& ok_place(b, l, dst)
    &&& forall|i: int| 0 <= i < args.len() ==> ok_op(b, l, #[trigger] args[i])
    &&& match k {
        // rule: Call(Intr) | Declassify result may be public
        Intrinsic::Declassify => args.len() == 1 && !mut_op(b, args[0]),
        Intrinsic::GhostUnit => true,
        Intrinsic::VecNew => args.len() == 0,
        // rule: Call(Intr) | VecWithCapacity n public
        Intrinsic::VecWithCapacity => args.len() == 1 && !sa(b, l, args, 0),
        // rule: Call(Intr) | VecPush value ⊑ target
        Intrinsic::VecPush => args.len() == 2 && !mut_op(b, args[1]) && (sa(b, l, args, 1) ==> sa(b, l, args, 0)),
        // rule: Call(Intr) | VecExtendFromSlice value ⊑ target
        Intrinsic::VecExtendFromSlice => args.len() == 2 && (sa(b, l, args, 1) ==> sa(b, l, args, 0)),
        // rule: Call(Intr) | VecAsSlice result ⊒ source
        Intrinsic::VecAsSlice => args.len() == 1 && !mut_op(b, args[0]) && (sa(b, l, args, 0) ==> ld),
        // rule: Call(Intr) | ArrayAsSlice result ⊒ source
        Intrinsic::ArrayAsSlice => args.len() == 1 && !mut_op(b, args[0]) && (sa(b, l, args, 0) ==> ld),
        // rule: Call(Intr) | VecLen public
        Intrinsic::VecLen => args.len() == 1,
        // rule: Call(Intr) | VecSet i public; value ⊑ target
        Intrinsic::VecSet => args.len() == 3 && !sa(b, l, args, 1) && !mut_op(b, args[2])
            && (sa(b, l, args, 2) ==> sa(b, l, args, 0)),
        // rule: Call(Intr) | VecIndex i public; result ⊒ source
        Intrinsic::VecIndex => args.len() == 2 && !sa(b, l, args, 1) && (sa(b, l, args, 0) ==> ld),
        // rule: Call(Intr) | SliceSubrange lo, hi public; result ⊒ source
        Intrinsic::SliceSubrange => args.len() == 3 && !sa(b, l, args, 1) && !sa(b, l, args, 2)
            && (sa(b, l, args, 0) ==> ld),
        // rule: Call(Intr) | SliceToVec result ⊒ source
        Intrinsic::SliceToVec => args.len() == 1 && (sa(b, l, args, 0) ==> ld),
        // rule: Call(Intr(Wrapping(op, ty))) | as Bin
        Intrinsic::Wrapping(op, _) => {
            &&& args.len() == 2
            &&& div_like(op) ==> !sa(b, l, args, 0) && !sa(b, l, args, 1)
            &&& shift_like(op) ==> !sa(b, l, args, 1)
            &&& sa(b, l, args, 0) || sa(b, l, args, 1) ==> ld
        },
    }
}

/// Arg `j` of a call to a fn with body `gb` and labels `gl`.
pub open spec fn ok_arg(b: Body, l: FnLab, gb: Body, gl: FnLab, j: int, a: Operand) -> bool {
    &&& ok_op(b, l, a)
    // rule: Call(Fn(g)) | each arg ⊑ g's param label
    &&& sec_op(b, l, a) ==> lab(gl, (1 + j) as nat)
    // rule: Call(Fn(g)) | == for Mut-typed params
    &&& gb.locals@[1 + j] is Mut ==> sec_op(b, l, a) == lab(gl, (1 + j) as nat)
    // rule: wf (a Mut arg only into a Mut-typed param)
    &&& mut_op(b, a) ==> gb.locals@[1 + j] is Mut
}

pub open spec fn ok_term(p: Program, ls: Seq<FnLab>, f: nat, t: Term) -> bool {
    let b = p.fns@[f as int];
    let l = ls[f as int];
    match t {
        Term::Goto(_) => true,
        // rule: Switch, Assert | condition public
        Term::Switch(op, _, _) => ok_op(b, l, op) && !sec_op(b, l, op),
        Term::Assert(op, _, _) => ok_op(b, l, op) && !sec_op(b, l, op),
        Term::Call(Callee::Fn(g), args, dst, _) => {
            let gb = p.fns@[g as int];
            let gl = ls[g as int];
            &&& forall|j: int| 0 <= j < args@.len() ==> ok_arg(b, l, gb, gl, j, #[trigger] args@[j])
            &&& ok_place(b, l, dst)
            // rule: Call(Fn(g)) | g's return label ⊑ wr(dst)
            &&& lab(gl, 0) ==> lab(l, dst.local as nat)
        },
        Term::Call(Callee::Intr(k), args, dst, _) => ok_intr(b, l, k, args@, dst),
        Term::Return => true,
        Term::Abort => true,
    }
}

// ------------------------------------------------------------------ per-program typing

/// The trigger predicate for `ok_body`'s quantifier over blocks.
pub open spec fn ok_block(p: Program, ls: Seq<FnLab>, f: nat, blk: Block) -> bool {
    &&& forall|i: int| 0 <= i < blk.stmts@.len() ==> ok_stmt(p.fns@[f as int], ls[f as int], #[trigger] blk.stmts@[i])
    &&& ok_term(p, ls, f, blk.term)
}

pub open spec fn ok_body(p: Program, ls: Seq<FnLab>, f: nat) -> bool {
    forall|i: int| 0 <= i < p.fns@[f as int].blocks@.len() ==> #[trigger] ok_block(p, ls, f, p.fns@[f as int].blocks@[i])
}

pub open spec fn ok_prog(p: Program, ls: Seq<FnLab>) -> bool {
    &&& wf(p)
    &&& ls.len() == p.fns@.len()
    &&& forall|f: nat| #![trigger ok_body(p, ls, f)] f < p.fns@.len() ==>
            ls[f as int].locals@.len() == p.fns@[f as int].locals@.len() && ok_body(p, ls, f)
}

/// Every declared-secret parameter `j` of fn `f` is secret in `ls` (`decl[f]` has one entry per
/// argument; `None` declares nothing).
pub open spec fn decl_ok(decl: Seq<Option<Vec<bool>>>, ls: Seq<FnLab>) -> bool {
    forall|f: int, j: int| 0 <= f < decl.len() && decl[f] is Some && 0 <= j < decl[f]->Some_0@.len()
        && #[trigger] decl[f]->Some_0@[j]
        ==> f < ls.len() && 1 + j < ls[f].locals@.len() && ls[f].locals@[1 + j]
}

// ------------------------------------------------------------------ agreement

/// Same constructors, lengths, variants and `Mut` locs; `Int`s always related.
pub open spec fn shape_eq(a: Val, b: Val) -> bool
    decreases a,
{
    match a {
        Val::Int(_) => b is Int,
        Val::Unit => b is Unit,
        Val::Tup(xs) => match b {
            Val::Tup(ys) => xs.len() == ys.len() && forall|i: int| 0 <= i < xs.len() ==> shape_eq(#[trigger] xs[i], ys[i]),
            _ => false,
        },
        Val::Adt(k, xs) => match b {
            Val::Adt(k2, ys) => k == k2 && xs.len() == ys.len() && forall|i: int| 0 <= i < xs.len() ==> shape_eq(#[trigger] xs[i], ys[i]),
            _ => false,
        },
        Val::Arr(xs) => match b {
            Val::Arr(ys) => xs.len() == ys.len() && forall|i: int| 0 <= i < xs.len() ==> shape_eq(#[trigger] xs[i], ys[i]),
            _ => false,
        },
        Val::Shr(x) => match b {
            Val::Shr(y) => shape_eq(*x, *y),
            _ => false,
        },
        Val::Mut(l1) => b == Val::Mut(l1),
    }
}

/// Two values of a location labelled `s`: equal if public, `shape_eq` if secret.
pub open spec fn val_rel(s: bool, a: Val, b: Val) -> bool {
    if s { shape_eq(a, b) } else { a == b }
}

pub open spec fn agree(p: Program, ls: Seq<FnLab>, f: nat, fr1: Frame, fr2: Frame) -> bool {
    let b = p.fns@[f as int];
    let l = ls[f as int];
    &&& fr1.locals.len() == b.locals@.len() && fr2.locals.len() == b.locals@.len()
    &&& fr1.slots.len() == fr2.slots.len()
    &&& forall|x: int| #![trigger fr1.locals[x]] #![trigger fr2.locals[x]] 0 <= x < fr1.locals.len() ==>
            val_rel(lab(l, x as nat), fr1.locals[x], fr2.locals[x])
    &&& forall|j: int| #![trigger fr1.slots[j]] #![trigger fr2.slots[j]] 0 <= j < fr1.slots.len() ==>
            val_rel(slot_lab(l, j as nat), fr1.slots[j], fr2.slots[j])
}

/// No `Mut` anywhere inside (including inside snapshots).
pub open spec fn no_mut(v: Val) -> bool
    decreases v,
{
    match v {
        Val::Tup(vs) => forall|i: int| 0 <= i < vs.len() ==> no_mut(#[trigger] vs[i]),
        Val::Adt(_, vs) => forall|i: int| 0 <= i < vs.len() ==> no_mut(#[trigger] vs[i]),
        Val::Arr(vs) => forall|i: int| 0 <= i < vs.len() ==> no_mut(#[trigger] vs[i]),
        Val::Shr(x) => no_mut(*x),
        Val::Mut(_) => false,
        _ => true,
    }
}

/// A root that can hold a `Mut` target: a slot, or a local that is not `Mut`-typed (so the
/// target holds no `Mut`).
pub open spec fn root_ok(b: Body, fr: Frame, r: Root) -> bool {
    match r {
        Root::Local(x) => x < fr.locals.len() && !(b.locals@[x as int] is Mut),
        Root::Slot(j) => j < fr.slots.len(),
    }
}

/// A `Mut` target with root label `s`.
pub open spec fn tgt_ok(b: Body, l: FnLab, fr: Frame, loc: Loc, s: bool) -> bool {
    root_lab(l, loc.root) == s && root_ok(b, fr, loc.root)
}

/// `Mut` label consistency: a `Mut(loc)` sits only at the top of a `Mut`-typed local `x`, and
/// its target's root label equals `lab(x)`; every other local and every slot holds no `Mut`.
pub open spec fn plc(p: Program, ls: Seq<FnLab>, f: nat, fr: Frame) -> bool {
    let b = p.fns@[f as int];
    let l = ls[f as int];
    &&& fr.locals.len() == b.locals@.len()
    &&& fr.slots.len() == b.nargs
    &&& forall|x: int| #![trigger fr.locals[x]] 0 <= x < fr.locals.len() ==> match fr.locals[x] {
            Val::Mut(loc) => b.locals@[x] is Mut && tgt_ok(b, l, fr, loc, lab(l, x as nat)),
            v => no_mut(v),
        }
    &&& forall|j: int| 0 <= j < fr.slots.len() ==> no_mut(#[trigger] fr.slots[j])
}

/// The entry arguments of fn `f`: one per parameter (ignored for `Mut`-typed ones, whose local
/// holds `Mut(Slot(j), [])`), public ones equal and secret ones `shape_eq`, holding no `Mut`;
/// one slot per parameter, related by the slot label, holding no `Mut`.
pub open spec fn args_agree(p: Program, ls: Seq<FnLab>, f: nat, a1: Seq<Val>, a2: Seq<Val>, s1: Seq<Val>, s2: Seq<Val>) -> bool {
    let b = p.fns@[f as int];
    let l = ls[f as int];
    &&& a1.len() == b.nargs && a2.len() == b.nargs && s1.len() == b.nargs && s2.len() == b.nargs
    &&& forall|j: int| #![trigger a1[j]] #![trigger a2[j]] 0 <= j < b.nargs && !(b.locals@[1 + j] is Mut) ==>
            val_rel(lab(l, (1 + j) as nat), a1[j], a2[j]) && no_mut(a1[j]) && no_mut(a2[j])
    &&& forall|j: int| #![trigger s1[j]] #![trigger s2[j]] 0 <= j < b.nargs ==>
            val_rel(slot_lab(l, j as nat), s1[j], s2[j]) && no_mut(s1[j]) && no_mut(s2[j])
}

/// The outputs: the return value (local 0) and the `&mut` slots.
pub open spec fn out_agree(p: Program, ls: Seq<FnLab>, f: nat, fr1: Frame, fr2: Frame) -> bool {
    let l = ls[f as int];
    &&& val_rel(lab(l, 0), nth(fr1.locals, 0), nth(fr2.locals, 0))
    &&& fr1.slots.len() == fr2.slots.len()
    &&& forall|j: int| #![trigger fr1.slots[j]] #![trigger fr2.slots[j]] 0 <= j < fr1.slots.len() ==>
            val_rel(slot_lab(l, j as nat), fr1.slots[j], fr2.slots[j])
}

// ------------------------------------------------------------------ trace relations

/// The traces first differ at index `i`, at two different `Declass` events.
pub open spec fn dv_at(t1: Seq<Event>, t2: Seq<Event>, i: int) -> bool {
    &&& 0 <= i < t1.len() && i < t2.len()
    &&& t1.take(i) == t2.take(i)
    &&& t1[i] is Declass && t2[i] is Declass && t1[i] != t2[i]
}

pub open spec fn diverge(t1: Seq<Event>, t2: Seq<Event>) -> bool {
    exists|i: int| #[trigger] dv_at(t1, t2, i)
}

} // verus!
