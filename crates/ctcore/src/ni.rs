//! Lockstep non-interference (Phase 8a Task 4): two runs of a well-typed program from agreeing
//! frames either emit equal traces and step counts and end in agreeing frames, or their traces
//! first differ at a `Declass` event. This task covers statements, intrinsics and intra-function
//! control flow, under the temporary premise `no_fn_calls` (Task 5 adds calls).
#[allow(unused_imports)]
use crate::ct::*;
#[allow(unused_imports)]
use crate::ct_lemmas::*;
#[allow(unused_imports)]
use crate::sem::*;
#[allow(unused_imports)]
use crate::syntax::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ statement forms

/// The trigger predicate for `no_fn_calls`.
pub open spec fn nfc_block(blk: Block) -> bool {
    !(blk.term matches Term::Call(Callee::Fn(_), _, _, _))
}

/// Temporary premise of this task: no block calls a fn (Task 5 deletes it).
pub open spec fn no_fn_calls(p: Program) -> bool {
    forall|f: nat, b: int| f < p.fns@.len() && 0 <= b < p.fns@[f as int].blocks@.len()
        ==> #[trigger] nfc_block(p.fns@[f as int].blocks@[b])
}

pub open spec fn ni_ok(p: Program, ls: Seq<FnLab>, f: nat, r1: Res, r2: Res) -> bool {
    let (fin1, t1, n1) = r1.unwrap();
    let (fin2, t2, n2) = r2.unwrap();
    (t1 == t2 && n1 == n2 && agree(p, ls, f, fin1, fin2) && plc(p, ls, f, fin1) && plc(p, ls, f, fin2))
        || diverge(t1, t2)
}

pub open spec fn ni_pre(p: Program, ls: Seq<FnLab>, f: nat, b: nat, fr1: Frame, fr2: Frame, fuel: nat) -> bool {
    &&& ok_prog(p, ls)
    &&& f < p.fns@.len()
    &&& b < p.fns@[f as int].blocks@.len()
    &&& agree(p, ls, f, fr1, fr2) && plc(p, ls, f, fr1) && plc(p, ls, f, fr2)
    &&& run_from(p, f, b, fr1, fuel) is Some && run_from(p, f, b, fr2, fuel) is Some
}

// ------------------------------------------------------------------ trace algebra

pub proof fn dv_append(t1: Seq<Event>, t2: Seq<Event>, x: Seq<Event>, y: Seq<Event>)
    requires diverge(t1, t2),
    ensures diverge(t1 + x, t2 + y),
{
    let i = choose|i: int| dv_at(t1, t2, i);
    assert((t1 + x).take(i) =~= t1.take(i));
    assert((t2 + y).take(i) =~= t2.take(i));
    assert(dv_at(t1 + x, t2 + y, i));
}

pub proof fn dv_prefix(pre: Seq<Event>, t1: Seq<Event>, t2: Seq<Event>)
    requires diverge(t1, t2),
    ensures diverge(pre + t1, pre + t2),
{
    let i = choose|i: int| dv_at(t1, t2, i);
    let j = pre.len() + i;
    assert((pre + t1).take(j) =~= pre + t1.take(i));
    assert((pre + t2).take(j) =~= pre + t2.take(i));
    assert(dv_at(pre + t1, pre + t2, j));
}

// ------------------------------------------------------------------ statements

/// Both frames take `pl := v_i` for values related at `lab(pl.local)`.
pub proof fn lemma_assign_agree(p: Program, ls: Seq<FnLab>, f: nat, fr1: Frame, fr2: Frame, pl: Place, v1: Val, v2: Val)
    requires
        agree(p, ls, f, fr1, fr2), plc(p, ls, f, fr1), plc(p, ls, f, fr2),
        ok_place(p.fns@[f as int], ls[f as int], pl), val_rel(lab(ls[f as int], pl.local as nat), v1, v2),
    ensures
        assign(fr1, pl, v1).1 == assign(fr2, pl, v2).1,
        agree(p, ls, f, assign(fr1, pl, v1).0, assign(fr2, pl, v2).0),
{
    lemma_place_loc_agree(p, ls, f, fr1, fr2, pl);
    lemma_place_plc(p, ls, f, fr1, pl);
    if let Some((loc, _)) = place_loc(fr1, pl) {
        lemma_write_loc_agree(p, ls, f, fr1, fr2, loc, v1, v2);
    }
}

pub proof fn ni_assign(p: Program, ls: Seq<FnLab>, f: nat, pl: Place, rv: Rvalue, fr1: Frame, fr2: Frame)
    requires
        ok_stmt(p.fns@[f as int], ls[f as int], Stmt::Assign(pl, rv)),
        agree(p, ls, f, fr1, fr2), plc(p, ls, f, fr1), plc(p, ls, f, fr2),
    ensures ({
        let s = Stmt::Assign(pl, rv);
        &&& exec_stmt(fr1, s).1 == exec_stmt(fr2, s).1
        &&& agree(p, ls, f, exec_stmt(fr1, s).0, exec_stmt(fr2, s).0)
        &&& plc(p, ls, f, exec_stmt(fr1, s).0) && plc(p, ls, f, exec_stmt(fr2, s).0)
    }),
{
    let (b, l) = (p.fns@[f as int], ls[f as int]);
    // rule: Assign | lab(rv) ⊑ wr(pl), in every arm (RefMut and Mut moves with ==)
    assert(sec_rv(b, l, rv) ==> lab(l, pl.local as nat));
    lemma_eval_rv_agree(p, ls, f, fr1, fr2, rv);
    let (v1, v2) = (eval_rv(fr1, rv).0, eval_rv(fr2, rv).0);
    if !lab(l, pl.local as nat) { assert(v1 == v2); } else { assert(shape_eq(v1, v2)); }
    lemma_assign_agree(p, ls, f, fr1, fr2, pl, v1, v2);
    lemma_plc_stmt(p, ls, f, fr1, Stmt::Assign(pl, rv));
    lemma_plc_stmt(p, ls, f, fr2, Stmt::Assign(pl, rv));
}

pub proof fn ni_setdiscr(p: Program, ls: Seq<FnLab>, f: nat, pl: Place, k: usize, fr1: Frame, fr2: Frame)
    requires
        ok_stmt(p.fns@[f as int], ls[f as int], Stmt::SetDiscr(pl, k)),
        agree(p, ls, f, fr1, fr2), plc(p, ls, f, fr1), plc(p, ls, f, fr2),
    ensures ({
        let s = Stmt::SetDiscr(pl, k);
        &&& exec_stmt(fr1, s).1 == exec_stmt(fr2, s).1
        &&& agree(p, ls, f, exec_stmt(fr1, s).0, exec_stmt(fr2, s).0)
        &&& plc(p, ls, f, exec_stmt(fr1, s).0) && plc(p, ls, f, exec_stmt(fr2, s).0)
    }),
{
    lemma_place_loc_agree(p, ls, f, fr1, fr2, pl);
    if let Some((loc, _)) = place_loc(fr1, pl) {
        let (o1, o2) = (read_loc(fr1, loc), read_loc(fr2, loc));
        lemma_read_loc_agree(p, ls, f, fr1, fr2, loc);
        let w1 = match o1 { Val::Adt(_, vs) => Val::Adt(k as nat, vs), v => v };
        let w2 = match o2 { Val::Adt(_, vs) => Val::Adt(k as nat, vs), v => v };
        if let (Val::Adt(_, xs), Val::Adt(_, ys)) = (o1, o2) {
            assert forall|i: int| 0 <= i < xs.len() implies shape_eq(#[trigger] xs[i], ys[i]) by {}
        }
        assert(val_rel(root_lab(ls[f as int], loc.root), w1, w2));
        lemma_write_loc_agree(p, ls, f, fr1, fr2, loc, w1, w2);
    }
    lemma_plc_setdiscr(p, ls, f, fr1, pl, k);
    lemma_plc_setdiscr(p, ls, f, fr2, pl, k);
}

pub proof fn ni_stmt(p: Program, ls: Seq<FnLab>, f: nat, s: Stmt, fr1: Frame, fr2: Frame)
    requires
        ok_stmt(p.fns@[f as int], ls[f as int], s),
        agree(p, ls, f, fr1, fr2), plc(p, ls, f, fr1), plc(p, ls, f, fr2),
    ensures
        exec_stmt(fr1, s).1 == exec_stmt(fr2, s).1,
        agree(p, ls, f, exec_stmt(fr1, s).0, exec_stmt(fr2, s).0),
        plc(p, ls, f, exec_stmt(fr1, s).0), plc(p, ls, f, exec_stmt(fr2, s).0),
{
    match s {
        Stmt::Assign(pl, rv) => ni_assign(p, ls, f, pl, rv, fr1, fr2),
        Stmt::SetDiscr(pl, k) => ni_setdiscr(p, ls, f, pl, k, fr1, fr2),
    }
}

pub proof fn ni_stmts(p: Program, ls: Seq<FnLab>, f: nat, ss: Seq<Stmt>, k: nat, fr1: Frame, fr2: Frame)
    requires
        k <= ss.len(),
        forall|i: int| 0 <= i < ss.len() ==> ok_stmt(p.fns@[f as int], ls[f as int], #[trigger] ss[i]),
        agree(p, ls, f, fr1, fr2), plc(p, ls, f, fr1), plc(p, ls, f, fr2),
    ensures
        exec_stmts(ss, k, fr1).1 == exec_stmts(ss, k, fr2).1,
        agree(p, ls, f, exec_stmts(ss, k, fr1).0, exec_stmts(ss, k, fr2).0),
        plc(p, ls, f, exec_stmts(ss, k, fr1).0), plc(p, ls, f, exec_stmts(ss, k, fr2).0),
    decreases ss.len() - k,
{
    if k < ss.len() {
        let s = ss[k as int];
        ni_stmt(p, ls, f, s, fr1, fr2);
        ni_stmts(p, ls, f, ss, k + 1, exec_stmt(fr1, s).0, exec_stmt(fr2, s).0);
    }
}

// ------------------------------------------------------------------ intrinsics

/// The premises of an intrinsic call.
pub open spec fn intr_pre(p: Program, ls: Seq<FnLab>, f: nat, k: Intrinsic, args: Seq<Operand>, dst: Place, fr1: Frame, fr2: Frame) -> bool {
    &&& ok_intr(p.fns@[f as int], ls[f as int], k, args, dst)
    &&& agree(p, ls, f, fr1, fr2) && plc(p, ls, f, fr1) && plc(p, ls, f, fr2)
}

/// Two-frame facts about the value of intrinsic arg `j` and its `elems`.
pub open spec fn iarg(p: Program, ls: Seq<FnLab>, f: nat, fr1: Frame, fr2: Frame, args: Seq<Operand>, j: int) -> bool {
    let (b, l) = (p.fns@[f as int], ls[f as int]);
    let (v1, v2) = (nth(op_vals(fr1, args), j as nat), nth(op_vals(fr2, args), j as nat));
    let s = sa(b, l, args, j);
    &&& val_rel(s, v1, v2) && shape_eq(v1, v2)
    &&& (v1 matches Val::Mut(m) ==> v2 == v1 && root_lab(l, m.root) == s)
    &&& elems(fr1, v1).len() == elems(fr2, v2).len()
    &&& forall|i: int| 0 <= i < elems(fr1, v1).len() ==> shape_eq(#[trigger] elems(fr1, v1)[i], elems(fr2, v2)[i])
    &&& !s ==> elems(fr1, v1) == elems(fr2, v2)
}

/// The intrinsic's own effects: both fail, or both succeed with agreeing frames and either equal
/// events and a result related at `lab(dst)`, or (`Declassify` only) diverging events.
pub open spec fn eff_rel(p: Program, ls: Seq<FnLab>, f: nat, k: Intrinsic, args: Seq<Operand>, dst: Place, fr1: Frame, fr2: Frame) -> bool {
    let (o1, o2) = (intr_eff(k, fr1, op_vals(fr1, args)), intr_eff(k, fr2, op_vals(fr2, args)));
    let ld = lab(ls[f as int], dst.local as nat);
    (o1 is None && o2 is None) || (o1 is Some && o2 is Some && {
        let ((g1, r1, e1), (g2, r2, e2)) = (o1.unwrap(), o2.unwrap());
        agree(p, ls, f, g1, g2) && ((e1 == e2 && val_rel(ld, r1, r2)) || (k is Declassify && diverge(e1, e2)))
    })
}

/// `ni_intr`'s conclusion on the two `exec_intr` results.
pub open spec fn intr_ok(p: Program, ls: Seq<FnLab>, f: nat, k: Intrinsic, o1: Option<(Frame, Seq<Event>, nat)>, o2: Option<(Frame, Seq<Event>, nat)>) -> bool {
    (o1 is None && o2 is None) || (o1 is Some && o2 is Some && {
        let ((g1, e1, x1), (g2, e2, x2)) = (o1.unwrap(), o2.unwrap());
        x1 == x2 && ((e1 == e2 && agree(p, ls, f, g1, g2) && plc(p, ls, f, g1) && plc(p, ls, f, g2))
            || (k is Declassify && diverge(e1, e2)))
    })
}

pub proof fn lemma_iarg(p: Program, ls: Seq<FnLab>, f: nat, fr1: Frame, fr2: Frame, args: Seq<Operand>, j: int)
    requires
        agree(p, ls, f, fr1, fr2), plc(p, ls, f, fr1), plc(p, ls, f, fr2),
        0 <= j < args.len(), ok_op(p.fns@[f as int], ls[f as int], args[j]),
    ensures iarg(p, ls, f, fr1, fr2, args, j),
{
    let (b, l) = (p.fns@[f as int], ls[f as int]);
    let (v1, v2) = (nth(op_vals(fr1, args), j as nat), nth(op_vals(fr2, args), j as nat));
    assert(v1 == eval_op(fr1, args[j]).0 && v2 == eval_op(fr2, args[j]).0);
    lemma_eval_op_agree(p, ls, f, fr1, fr2, args[j]);
    lemma_eval_op_plc(p, ls, f, fr1, args[j]);
    if let Val::Mut(m) = v1 {
        let x = args[j]->Copy_0.local as int;
        assert(match fr1.locals[x] { Val::Mut(m) => b.locals@[x] is Mut && tgt_ok(b, l, fr1, m, lab(l, x as nat)), v => no_mut(v) });
        lemma_read_loc_agree(p, ls, f, fr1, fr2, m);
    }
    lemma_elems_shape(p, ls, f, fr1, fr2, v1, v2);
}

/// `grow` at a shared target whose root label is `s`, with values related at `s`.
pub proof fn lemma_grow_agree(p: Program, ls: Seq<FnLab>, f: nat, fr1: Frame, fr2: Frame, m1: Val, m2: Val, xs1: Seq<Val>, xs2: Seq<Val>, s: bool)
    requires
        agree(p, ls, f, fr1, fr2), shape_eq(m1, m2),
        m1 matches Val::Mut(l) ==> m2 == m1 && root_lab(ls[f as int], l.root) == s,
        xs1.len() == xs2.len(), forall|i: int| 0 <= i < xs1.len() ==> shape_eq(#[trigger] xs1[i], xs2[i]),
        !s ==> xs1 == xs2,
    ensures
        (grow(fr1, m1, xs1) is None && grow(fr2, m2, xs2) is None)
            || (grow(fr1, m1, xs1) is Some && grow(fr2, m2, xs2) is Some
                && agree(p, ls, f, grow(fr1, m1, xs1).unwrap(), grow(fr2, m2, xs2).unwrap())),
{
    if let Val::Mut(l) = m1 {
        lemma_read_loc_agree(p, ls, f, fr1, fr2, l);
        if let (Val::Arr(a1), Val::Arr(a2)) = (read_loc(fr1, l), read_loc(fr2, l)) {
            let (w1, w2) = (a1 + xs1, a2 + xs2);
            if s {
                assert forall|i: int| 0 <= i < w1.len() implies shape_eq(#[trigger] w1[i], w2[i]) by {
                    if i < a1.len() { assert(w1[i] == a1[i] && w2[i] == a2[i]); }
                    else { assert(w1[i] == xs1[i - a1.len()] && w2[i] == xs2[i - a1.len()]); }
                }
            }
            if a1.len() + xs1.len() <= USIZE_MAX {
                lemma_write_loc_agree(p, ls, f, fr1, fr2, l, Val::Arr(w1), Val::Arr(w2));
            }
        }
    }
}

pub proof fn ni_i_declassify(p: Program, ls: Seq<FnLab>, f: nat, k: Intrinsic, args: Seq<Operand>, dst: Place, fr1: Frame, fr2: Frame)
    requires intr_pre(p, ls, f, k, args, dst, fr1, fr2), k is Declassify,
    ensures eff_rel(p, ls, f, k, args, dst, fr1, fr2),
{
    lemma_iarg(p, ls, f, fr1, fr2, args, 0);
    let (a1, a2) = (nth(op_vals(fr1, args), 0), nth(op_vals(fr2, args), 0));
    let (e1, e2) = (seq![Event::Declass(a1)], seq![Event::Declass(a2)]);
    if a1 == a2 {
        lemma_shape_refl(a1);
    } else {
        // rule: Call(Intr) | Declassify result may be public: the runs diverge here
        assert(e1.take(0) =~= e2.take(0));
        assert(dv_at(e1, e2, 0));
    }
}

pub proof fn ni_i_ghost_unit(p: Program, ls: Seq<FnLab>, f: nat, k: Intrinsic, args: Seq<Operand>, dst: Place, fr1: Frame, fr2: Frame)
    requires intr_pre(p, ls, f, k, args, dst, fr1, fr2), k is GhostUnit,
    ensures eff_rel(p, ls, f, k, args, dst, fr1, fr2),
{
}

pub proof fn ni_i_vec_new(p: Program, ls: Seq<FnLab>, f: nat, k: Intrinsic, args: Seq<Operand>, dst: Place, fr1: Frame, fr2: Frame)
    requires intr_pre(p, ls, f, k, args, dst, fr1, fr2), k is VecNew,
    ensures eff_rel(p, ls, f, k, args, dst, fr1, fr2),
{
    lemma_shape_refl(Val::Arr(seq![]));
}

pub proof fn ni_i_with_capacity(p: Program, ls: Seq<FnLab>, f: nat, k: Intrinsic, args: Seq<Operand>, dst: Place, fr1: Frame, fr2: Frame)
    requires intr_pre(p, ls, f, k, args, dst, fr1, fr2), k is VecWithCapacity,
    ensures eff_rel(p, ls, f, k, args, dst, fr1, fr2),
{
    lemma_iarg(p, ls, f, fr1, fr2, args, 0);
    // rule: Call(Intr) | VecWithCapacity n public
    assert(!sa(p.fns@[f as int], ls[f as int], args, 0));
    lemma_shape_refl(Val::Arr(seq![]));
}

pub proof fn ni_i_push(p: Program, ls: Seq<FnLab>, f: nat, k: Intrinsic, args: Seq<Operand>, dst: Place, fr1: Frame, fr2: Frame)
    requires intr_pre(p, ls, f, k, args, dst, fr1, fr2), k is VecPush,
    ensures eff_rel(p, ls, f, k, args, dst, fr1, fr2),
{
    let (b, l) = (p.fns@[f as int], ls[f as int]);
    lemma_iarg(p, ls, f, fr1, fr2, args, 0);
    lemma_iarg(p, ls, f, fr1, fr2, args, 1);
    let (vs1, vs2) = (op_vals(fr1, args), op_vals(fr2, args));
    let (xs1, xs2) = (seq![nth(vs1, 1)], seq![nth(vs2, 1)]);
    // rule: Call(Intr) | VecPush value ⊑ target
    assert(sa(b, l, args, 1) ==> sa(b, l, args, 0));
    if !sa(b, l, args, 0) { assert(xs1 =~= xs2); }
    lemma_grow_agree(p, ls, f, fr1, fr2, nth(vs1, 0), nth(vs2, 0), xs1, xs2, sa(b, l, args, 0));
}

pub proof fn ni_i_extend(p: Program, ls: Seq<FnLab>, f: nat, k: Intrinsic, args: Seq<Operand>, dst: Place, fr1: Frame, fr2: Frame)
    requires intr_pre(p, ls, f, k, args, dst, fr1, fr2), k is VecExtendFromSlice,
    ensures eff_rel(p, ls, f, k, args, dst, fr1, fr2),
{
    let (b, l) = (p.fns@[f as int], ls[f as int]);
    lemma_iarg(p, ls, f, fr1, fr2, args, 0);
    lemma_iarg(p, ls, f, fr1, fr2, args, 1);
    let (vs1, vs2) = (op_vals(fr1, args), op_vals(fr2, args));
    // rule: Call(Intr) | VecExtendFromSlice value ⊑ target
    assert(sa(b, l, args, 1) ==> sa(b, l, args, 0));
    lemma_grow_agree(p, ls, f, fr1, fr2, nth(vs1, 0), nth(vs2, 0), elems(fr1, nth(vs1, 1)), elems(fr2, nth(vs2, 1)), sa(b, l, args, 0));
}

/// `VecAsSlice` and `ArrayAsSlice` (one arm of `intr_eff`).
pub proof fn ni_i_as_slice(p: Program, ls: Seq<FnLab>, f: nat, k: Intrinsic, args: Seq<Operand>, dst: Place, fr1: Frame, fr2: Frame)
    requires intr_pre(p, ls, f, k, args, dst, fr1, fr2), k is VecAsSlice || k is ArrayAsSlice,
    ensures eff_rel(p, ls, f, k, args, dst, fr1, fr2),
{
    lemma_iarg(p, ls, f, fr1, fr2, args, 0);
    // rule: Call(Intr) | VecAsSlice/ArrayAsSlice result ⊒ source
    assert(sa(p.fns@[f as int], ls[f as int], args, 0) ==> lab(ls[f as int], dst.local as nat));
}

pub proof fn ni_i_vec_len(p: Program, ls: Seq<FnLab>, f: nat, k: Intrinsic, args: Seq<Operand>, dst: Place, fr1: Frame, fr2: Frame)
    requires intr_pre(p, ls, f, k, args, dst, fr1, fr2), k is VecLen,
    ensures eff_rel(p, ls, f, k, args, dst, fr1, fr2),
{
    lemma_iarg(p, ls, f, fr1, fr2, args, 0);
}

pub proof fn ni_i_vec_set(p: Program, ls: Seq<FnLab>, f: nat, k: Intrinsic, args: Seq<Operand>, dst: Place, fr1: Frame, fr2: Frame)
    requires intr_pre(p, ls, f, k, args, dst, fr1, fr2), k is VecSet,
    ensures eff_rel(p, ls, f, k, args, dst, fr1, fr2),
{
    let (b, l) = (p.fns@[f as int], ls[f as int]);
    lemma_iarg(p, ls, f, fr1, fr2, args, 0);
    lemma_iarg(p, ls, f, fr1, fr2, args, 1);
    lemma_iarg(p, ls, f, fr1, fr2, args, 2);
    let (vs1, vs2) = (op_vals(fr1, args), op_vals(fr2, args));
    // rule: Call(Intr) | VecSet i public; value ⊑ target
    assert(!sa(b, l, args, 1));
    assert(sa(b, l, args, 2) ==> sa(b, l, args, 0));
    if let Val::Mut(m) = nth(vs1, 0) {
        let i = as_int(nth(vs1, 1));
        let loc = Loc { root: m.root, path: m.path.push(PE::Index(i as nat)) };
        lemma_write_loc_agree(p, ls, f, fr1, fr2, loc, nth(vs1, 2), nth(vs2, 2));
    }
}

pub proof fn ni_i_vec_index(p: Program, ls: Seq<FnLab>, f: nat, k: Intrinsic, args: Seq<Operand>, dst: Place, fr1: Frame, fr2: Frame)
    requires intr_pre(p, ls, f, k, args, dst, fr1, fr2), k is VecIndex,
    ensures eff_rel(p, ls, f, k, args, dst, fr1, fr2),
{
    let (b, l) = (p.fns@[f as int], ls[f as int]);
    lemma_iarg(p, ls, f, fr1, fr2, args, 0);
    lemma_iarg(p, ls, f, fr1, fr2, args, 1);
    let (vs1, vs2) = (op_vals(fr1, args), op_vals(fr2, args));
    // rule: Call(Intr) | VecIndex i public; result ⊒ source
    assert(!sa(b, l, args, 1));
    assert(sa(b, l, args, 0) ==> lab(l, dst.local as nat));
    let i = as_int(nth(vs1, 1)) as nat;
    let (s1, s2) = (elems(fr1, nth(vs1, 0)), elems(fr2, nth(vs2, 0)));
    if i < s1.len() { assert(shape_eq(s1[i as int], s2[i as int])); }
    assert(shape_eq(nth(s1, i), nth(s2, i)));
}

pub proof fn ni_i_subrange(p: Program, ls: Seq<FnLab>, f: nat, k: Intrinsic, args: Seq<Operand>, dst: Place, fr1: Frame, fr2: Frame)
    requires intr_pre(p, ls, f, k, args, dst, fr1, fr2), k is SliceSubrange,
    ensures eff_rel(p, ls, f, k, args, dst, fr1, fr2),
{
    let (b, l) = (p.fns@[f as int], ls[f as int]);
    lemma_iarg(p, ls, f, fr1, fr2, args, 0);
    lemma_iarg(p, ls, f, fr1, fr2, args, 1);
    lemma_iarg(p, ls, f, fr1, fr2, args, 2);
    let (vs1, vs2) = (op_vals(fr1, args), op_vals(fr2, args));
    // rule: Call(Intr) | SliceSubrange lo, hi public; result ⊒ source
    assert(!sa(b, l, args, 1) && !sa(b, l, args, 2));
    assert(sa(b, l, args, 0) ==> lab(l, dst.local as nat));
    let (s1, s2) = (elems(fr1, nth(vs1, 0)), elems(fr2, nth(vs2, 0)));
    let (lo, hi) = (as_int(nth(vs1, 1)), as_int(nth(vs1, 2)));
    let h = if (hi as nat) < s1.len() { hi as int } else { s1.len() as int };
    let lw = if (lo as int) < h { lo as int } else { h };
    let (a1, a2) = (s1.subrange(lw, h), s2.subrange(lw, h));
    assert forall|i: int| 0 <= i < a1.len() implies shape_eq(#[trigger] a1[i], a2[i]) by {
        assert(a1[i] == s1[i + lw] && a2[i] == s2[i + lw]);
    }
    assert(shape_eq(Val::Arr(a1), Val::Arr(a2)));
    assert(shape_eq(Val::Shr(Box::new(Val::Arr(a1))), Val::Shr(Box::new(Val::Arr(a2)))));
    assert(intr_eff(k, fr1, vs1) == Some((fr1, Val::Shr(Box::new(Val::Arr(a1))), seq![Event::Range(lo, hi)])));
    assert(intr_eff(k, fr2, vs2) == Some((fr2, Val::Shr(Box::new(Val::Arr(a2))), seq![Event::Range(lo, hi)])));
}

pub proof fn ni_i_to_vec(p: Program, ls: Seq<FnLab>, f: nat, k: Intrinsic, args: Seq<Operand>, dst: Place, fr1: Frame, fr2: Frame)
    requires intr_pre(p, ls, f, k, args, dst, fr1, fr2), k is SliceToVec,
    ensures eff_rel(p, ls, f, k, args, dst, fr1, fr2),
{
    lemma_iarg(p, ls, f, fr1, fr2, args, 0);
    // rule: Call(Intr) | SliceToVec result ⊒ source
    assert(sa(p.fns@[f as int], ls[f as int], args, 0) ==> lab(ls[f as int], dst.local as nat));
    let (s1, s2) = (elems(fr1, nth(op_vals(fr1, args), 0)), elems(fr2, nth(op_vals(fr2, args), 0)));
    assert forall|i: int| 0 <= i < s1.len() implies shape_eq(#[trigger] s1[i], s2[i]) by {}
    assert(shape_eq(Val::Arr(s1), Val::Arr(s2)));
}

pub proof fn ni_i_wrapping(p: Program, ls: Seq<FnLab>, f: nat, k: Intrinsic, args: Seq<Operand>, dst: Place, fr1: Frame, fr2: Frame)
    requires intr_pre(p, ls, f, k, args, dst, fr1, fr2), k is Wrapping,
    ensures eff_rel(p, ls, f, k, args, dst, fr1, fr2),
{
    let (b, l) = (p.fns@[f as int], ls[f as int]);
    lemma_iarg(p, ls, f, fr1, fr2, args, 0);
    lemma_iarg(p, ls, f, fr1, fr2, args, 1);
    let (vs1, vs2) = (op_vals(fr1, args), op_vals(fr2, args));
    if let Intrinsic::Wrapping(op, ty) = k {
        // rule: Call(Intr(Wrapping(op, ty))) | as Bin
        assert(div_like(op) ==> !sa(b, l, args, 0) && !sa(b, l, args, 1));
        assert(shift_like(op) ==> !sa(b, l, args, 1));
        assert(sa(b, l, args, 0) || sa(b, l, args, 1) ==> lab(l, dst.local as nat));
        let (a1, b1) = (as_int(nth(vs1, 0)), as_int(nth(vs1, 1)));
        let (a2, b2) = (as_int(nth(vs2, 0)), as_int(nth(vs2, 1)));
        assert(op_ev(op, a1, b1) == op_ev(op, a2, b2));
    }
}

/// Dispatch to the per-intrinsic lemmas.
pub proof fn ni_intr_eff(p: Program, ls: Seq<FnLab>, f: nat, k: Intrinsic, args: Seq<Operand>, dst: Place, fr1: Frame, fr2: Frame)
    requires intr_pre(p, ls, f, k, args, dst, fr1, fr2),
    ensures eff_rel(p, ls, f, k, args, dst, fr1, fr2),
{
    match k {
        Intrinsic::Declassify => ni_i_declassify(p, ls, f, k, args, dst, fr1, fr2),
        Intrinsic::GhostUnit => ni_i_ghost_unit(p, ls, f, k, args, dst, fr1, fr2),
        Intrinsic::VecNew => ni_i_vec_new(p, ls, f, k, args, dst, fr1, fr2),
        Intrinsic::VecWithCapacity => ni_i_with_capacity(p, ls, f, k, args, dst, fr1, fr2),
        Intrinsic::VecPush => ni_i_push(p, ls, f, k, args, dst, fr1, fr2),
        Intrinsic::VecExtendFromSlice => ni_i_extend(p, ls, f, k, args, dst, fr1, fr2),
        Intrinsic::VecAsSlice | Intrinsic::ArrayAsSlice => ni_i_as_slice(p, ls, f, k, args, dst, fr1, fr2),
        Intrinsic::VecLen => ni_i_vec_len(p, ls, f, k, args, dst, fr1, fr2),
        Intrinsic::VecSet => ni_i_vec_set(p, ls, f, k, args, dst, fr1, fr2),
        Intrinsic::VecIndex => ni_i_vec_index(p, ls, f, k, args, dst, fr1, fr2),
        Intrinsic::SliceSubrange => ni_i_subrange(p, ls, f, k, args, dst, fr1, fr2),
        Intrinsic::SliceToVec => ni_i_to_vec(p, ls, f, k, args, dst, fr1, fr2),
        Intrinsic::Wrapping(_, _) => ni_i_wrapping(p, ls, f, k, args, dst, fr1, fr2),
    }
}

pub proof fn ni_intr(p: Program, ls: Seq<FnLab>, f: nat, k: Intrinsic, args: Seq<Operand>, dst: Place, fr1: Frame, fr2: Frame)
    requires
        ok_intr(p.fns@[f as int], ls[f as int], k, args, dst),
        agree(p, ls, f, fr1, fr2), plc(p, ls, f, fr1), plc(p, ls, f, fr2),
    ensures intr_ok(p, ls, f, k, exec_intr(k, fr1, args, dst), exec_intr(k, fr2, args, dst)),
{
    let l = ls[f as int];
    ni_intr_eff(p, ls, f, k, args, dst, fr1, fr2);
    if args.len() > 0 { lemma_iarg(p, ls, f, fr1, fr2, args, 0); }
    if args.len() > 1 { lemma_iarg(p, ls, f, fr1, fr2, args, 1); }
    assert(intr_cost(k, fr1, args) == intr_cost(k, fr2, args));
    lemma_ops_ev_agree(p, ls, f, fr1, fr2, args);
    let (o1, o2) = (intr_eff(k, fr1, op_vals(fr1, args)), intr_eff(k, fr2, op_vals(fr2, args)));
    if o1 is Some {
        if k is VecPush || k is VecExtendFromSlice || k is VecSet {
            lemma_plc_intr_write(p, ls, f, fr1, k, args, dst);
            lemma_plc_intr_write(p, ls, f, fr2, k, args, dst);
        } else {
            lemma_plc_intr_val(p, ls, f, fr1, k, args, dst);
            lemma_plc_intr_val(p, ls, f, fr2, k, args, dst);
        }
        lemma_plc_intr(p, ls, f, fr1, k, args, dst);
        lemma_plc_intr(p, ls, f, fr2, k, args, dst);
        let ((g1, r1, ie1), (g2, r2, ie2)) = (o1.unwrap(), o2.unwrap());
        let oe = ops_ev(fr1, args);
        if ie1 == ie2 && val_rel(lab(l, dst.local as nat), r1, r2) {
            lemma_assign_agree(p, ls, f, g1, g2, dst, r1, r2);
        } else {
            dv_prefix(oe, ie1, ie2);
            dv_append(oe + ie1, oe + ie2, assign(g1, dst, r1).1, assign(g2, dst, r2).1);
        }
    }
}

// ------------------------------------------------------------------ blocks and terminators

/// A block's typing and wf facts, and NI over its statements.
pub proof fn lemma_block(p: Program, ls: Seq<FnLab>, f: nat, b: nat, fr1: Frame, fr2: Frame)
    requires
        ok_prog(p, ls), f < p.fns@.len(), b < p.fns@[f as int].blocks@.len(),
        agree(p, ls, f, fr1, fr2), plc(p, ls, f, fr1), plc(p, ls, f, fr2),
    ensures ({
        let blk = p.fns@[f as int].blocks@[b as int];
        let (g1, g2) = (exec_stmts(blk.stmts@, 0, fr1), exec_stmts(blk.stmts@, 0, fr2));
        &&& ok_term(p, ls, f, blk.term) && wf_term(p, f, blk.term)
        &&& g1.1 == g2.1 && agree(p, ls, f, g1.0, g2.0) && plc(p, ls, f, g1.0) && plc(p, ls, f, g2.0)
    }),
{
    let blk = p.fns@[f as int].blocks@[b as int];
    assert(ok_body(p, ls, f));
    assert(ok_block(p, ls, f, blk));
    assert(wf_body(p, f));
    assert(wf_block(p, f, blk));
    ni_stmts(p, ls, f, blk.stmts@, 0, fr1, fr2);
}

/// The rule for branch conditions, in a small context so that dropping it fails here.
pub proof fn lemma_cond_public(p: Program, ls: Seq<FnLab>, f: nat, t: Term)
    requires ok_term(p, ls, f, t),
    ensures
        t matches Term::Switch(op, _, _) ==> ok_op(p.fns@[f as int], ls[f as int], op) && !sec_op(p.fns@[f as int], ls[f as int], op),
        t matches Term::Assert(op, _, _) ==> ok_op(p.fns@[f as int], ls[f as int], op) && !sec_op(p.fns@[f as int], ls[f as int], op),
{
    // rule: Switch, Assert | condition public
}

/// A switch target is one of the in-range targets.
pub proof fn lemma_switch_target(ts: Seq<(u128, usize)>, k: nat, v: u128, o: usize, n: nat)
    requires k <= ts.len(), o < n, forall|i: int| 0 <= i < ts.len() ==> (#[trigger] ts[i]).1 < n,
    ensures switch_target(ts, k, v, o) < n,
    decreases ts.len() - k,
{
    if k < ts.len() {
        assert(ts[k as int].1 < n);
        lemma_switch_target(ts, k + 1, v, o, n);
    }
}

pub proof fn ni_goto(p: Program, ls: Seq<FnLab>, f: nat, b: nat, fr1: Frame, fr2: Frame, fuel: nat)
    requires ni_pre(p, ls, f, b, fr1, fr2, fuel), no_fn_calls(p), p.fns@[f as int].blocks@[b as int].term is Goto,
    ensures ni_ok(p, ls, f, run_from(p, f, b, fr1, fuel), run_from(p, f, b, fr2, fuel)),
    decreases fuel, 0nat,
{
    let blk = p.fns@[f as int].blocks@[b as int];
    lemma_block(p, ls, f, b, fr1, fr2);
    let (g1, t1) = exec_stmts(blk.stmts@, 0, fr1);
    let (g2, t2) = exec_stmts(blk.stmts@, 0, fr2);
    let n1 = blk.stmts@.len() + 1;
    let fu = (fuel - 1) as nat;
    if let Term::Goto(b2) = blk.term {
        let (r1, r2) = (run_from(p, f, b2 as nat, g1, fu), run_from(p, f, b2 as nat, g2, fu));
        assert(run_from(p, f, b, fr1, fuel) == match r1 { Some((h, t, n)) => Some((h, t1 + t, n1 + n)), None => None });
        assert(run_from(p, f, b, fr2, fuel) == match r2 { Some((h, t, n)) => Some((h, t2 + t, n1 + n)), None => None });
        ni_local(p, ls, f, b2 as nat, g1, g2, fu);
        if diverge(r1.unwrap().1, r2.unwrap().1) { dv_prefix(t1, r1.unwrap().1, r2.unwrap().1); }
    }
}

pub proof fn ni_switch(p: Program, ls: Seq<FnLab>, f: nat, b: nat, fr1: Frame, fr2: Frame, fuel: nat)
    requires ni_pre(p, ls, f, b, fr1, fr2, fuel), no_fn_calls(p), p.fns@[f as int].blocks@[b as int].term is Switch,
    ensures ni_ok(p, ls, f, run_from(p, f, b, fr1, fuel), run_from(p, f, b, fr2, fuel)),
    decreases fuel, 0nat,
{
    let blk = p.fns@[f as int].blocks@[b as int];
    lemma_block(p, ls, f, b, fr1, fr2);
    let (g1, t1) = exec_stmts(blk.stmts@, 0, fr1);
    let (g2, t2) = exec_stmts(blk.stmts@, 0, fr2);
    let n1 = blk.stmts@.len() + 1;
    let fu = (fuel - 1) as nat;
    if let Term::Switch(op, ts, o) = blk.term {
        let bd = p.fns@[f as int];
        lemma_cond_public(p, ls, f, blk.term);
        lemma_eval_op_agree(p, ls, f, g1, g2, op);
        let (v, e) = eval_op(g1, op);
        let pre = t1 + e + seq![Event::Cond(as_int(v))];
        let tg = switch_target(ts@, 0, as_int(v), o);
        lemma_switch_target(ts@, 0, as_int(v), o, bd.blocks@.len());
        let (r1, r2) = (run_from(p, f, tg as nat, g1, fu), run_from(p, f, tg as nat, g2, fu));
        assert(run_from(p, f, b, fr1, fuel) == match r1 { Some((h, t, n)) => Some((h, pre + t, n1 + n)), None => None });
        assert(run_from(p, f, b, fr2, fuel) == match r2 { Some((h, t, n)) => Some((h, pre + t, n1 + n)), None => None });
        ni_local(p, ls, f, tg as nat, g1, g2, fu);
        if diverge(r1.unwrap().1, r2.unwrap().1) { dv_prefix(pre, r1.unwrap().1, r2.unwrap().1); }
    }
}

pub proof fn ni_assert(p: Program, ls: Seq<FnLab>, f: nat, b: nat, fr1: Frame, fr2: Frame, fuel: nat)
    requires ni_pre(p, ls, f, b, fr1, fr2, fuel), no_fn_calls(p), p.fns@[f as int].blocks@[b as int].term is Assert,
    ensures ni_ok(p, ls, f, run_from(p, f, b, fr1, fuel), run_from(p, f, b, fr2, fuel)),
    decreases fuel, 0nat,
{
    let blk = p.fns@[f as int].blocks@[b as int];
    lemma_block(p, ls, f, b, fr1, fr2);
    let (g1, t1) = exec_stmts(blk.stmts@, 0, fr1);
    let (g2, t2) = exec_stmts(blk.stmts@, 0, fr2);
    let n1 = blk.stmts@.len() + 1;
    let fu = (fuel - 1) as nat;
    if let Term::Assert(op, expected, b2) = blk.term {
        lemma_cond_public(p, ls, f, blk.term);
        lemma_eval_op_agree(p, ls, f, g1, g2, op);
        let (v, e) = eval_op(g1, op);
        let pre = t1 + e + seq![Event::Cond(as_int(v))];
        assert((as_int(v) != 0) == expected);
        let (r1, r2) = (run_from(p, f, b2 as nat, g1, fu), run_from(p, f, b2 as nat, g2, fu));
        assert(run_from(p, f, b, fr1, fuel) == match r1 { Some((h, t, n)) => Some((h, pre + t, n1 + n)), None => None });
        assert(run_from(p, f, b, fr2, fuel) == match r2 { Some((h, t, n)) => Some((h, pre + t, n1 + n)), None => None });
        ni_local(p, ls, f, b2 as nat, g1, g2, fu);
        if diverge(r1.unwrap().1, r2.unwrap().1) { dv_prefix(pre, r1.unwrap().1, r2.unwrap().1); }
    }
}

pub proof fn ni_call_intr(p: Program, ls: Seq<FnLab>, f: nat, b: nat, fr1: Frame, fr2: Frame, fuel: nat)
    requires ni_pre(p, ls, f, b, fr1, fr2, fuel), no_fn_calls(p), p.fns@[f as int].blocks@[b as int].term matches Term::Call(Callee::Intr(_), _, _, _),
    ensures ni_ok(p, ls, f, run_from(p, f, b, fr1, fuel), run_from(p, f, b, fr2, fuel)),
    decreases fuel, 0nat,
{
    let blk = p.fns@[f as int].blocks@[b as int];
    lemma_block(p, ls, f, b, fr1, fr2);
    let (g1, t1) = exec_stmts(blk.stmts@, 0, fr1);
    let (g2, t2) = exec_stmts(blk.stmts@, 0, fr2);
    let n1 = blk.stmts@.len() + 1;
    let fu = (fuel - 1) as nat;
    if let Term::Call(Callee::Intr(k), args, dst, next) = blk.term {
        ni_intr(p, ls, f, k, args@, dst, g1, g2);
        let ((h1, e1, x1), (h2, e2, x2)) = (exec_intr(k, g1, args@, dst).unwrap(), exec_intr(k, g2, args@, dst).unwrap());
        let (r1, r2) = (run_from(p, f, next as nat, h1, fu), run_from(p, f, next as nat, h2, fu));
        assert(run_from(p, f, b, fr1, fuel) == match r1 { Some((h, t, n)) => Some((h, (t1 + e1) + t, n1 + x1 + n)), None => None });
        assert(run_from(p, f, b, fr2, fuel) == match r2 { Some((h, t, n)) => Some((h, (t2 + e2) + t, n1 + x2 + n)), None => None });
        let (u1, u2) = (r1.unwrap().1, r2.unwrap().1);
        if e1 == e2 && agree(p, ls, f, h1, h2) && plc(p, ls, f, h1) && plc(p, ls, f, h2) {
            ni_local(p, ls, f, next as nat, h1, h2, fu);
            if diverge(u1, u2) { dv_prefix(t1 + e1, u1, u2); }
        } else {
            dv_prefix(t1, e1, e2);
            dv_append(t1 + e1, t1 + e2, u1, u2);
        }
    }
}

pub proof fn ni_return(p: Program, ls: Seq<FnLab>, f: nat, b: nat, fr1: Frame, fr2: Frame, fuel: nat)
    requires ni_pre(p, ls, f, b, fr1, fr2, fuel), no_fn_calls(p), p.fns@[f as int].blocks@[b as int].term is Return,
    ensures ni_ok(p, ls, f, run_from(p, f, b, fr1, fuel), run_from(p, f, b, fr2, fuel)),
    decreases fuel, 0nat,
{
    let blk = p.fns@[f as int].blocks@[b as int];
    lemma_block(p, ls, f, b, fr1, fr2);
}

/// Lockstep NI of two runs from block `b` of fn `f` (no fn calls).
pub proof fn ni_local(p: Program, ls: Seq<FnLab>, f: nat, b: nat, fr1: Frame, fr2: Frame, fuel: nat)
    requires ni_pre(p, ls, f, b, fr1, fr2, fuel), no_fn_calls(p),
    ensures ni_ok(p, ls, f, run_from(p, f, b, fr1, fuel), run_from(p, f, b, fr2, fuel)),
    decreases fuel, 1nat,
{
    let blk = p.fns@[f as int].blocks@[b as int];
    assert(nfc_block(blk));
    match blk.term {
        Term::Goto(_) => ni_goto(p, ls, f, b, fr1, fr2, fuel),
        Term::Switch(_, _, _) => ni_switch(p, ls, f, b, fr1, fr2, fuel),
        Term::Assert(_, _, _) => ni_assert(p, ls, f, b, fr1, fr2, fuel),
        Term::Call(Callee::Intr(_), _, _, _) => ni_call_intr(p, ls, f, b, fr1, fr2, fuel),
        Term::Return => ni_return(p, ls, f, b, fr1, fr2, fuel),
        // Abort: the runs are None; Call(Fn): excluded by no_fn_calls
        _ => {},
    }
}

} // verus!
