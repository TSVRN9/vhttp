//! Lemmas over the CT typing: shape agreement, places, operands, rvalues and `plc`.
#[allow(unused_imports)]
use crate::ct::*;
#[allow(unused_imports)]
use crate::sem::*;
#[allow(unused_imports)]
use crate::syntax::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ shape_eq

pub proof fn lemma_shape_refl(a: Val)
    ensures shape_eq(a, a),
    decreases a,
{
    match a {
        Val::Tup(xs) => { assert forall|i: int| 0 <= i < xs.len() implies shape_eq(#[trigger] xs[i], xs[i]) by { lemma_shape_refl(xs[i]); } },
        Val::Adt(_, xs) => { assert forall|i: int| 0 <= i < xs.len() implies shape_eq(#[trigger] xs[i], xs[i]) by { lemma_shape_refl(xs[i]); } },
        Val::Arr(xs) => { assert forall|i: int| 0 <= i < xs.len() implies shape_eq(#[trigger] xs[i], xs[i]) by { lemma_shape_refl(xs[i]); } },
        Val::Shr(x) => lemma_shape_refl(*x),
        _ => {},
    }
}

pub proof fn lemma_shape_sym(a: Val, b: Val)
    requires shape_eq(a, b),
    ensures shape_eq(b, a),
    decreases a,
{
    match a {
        Val::Tup(xs) => if let Val::Tup(ys) = b {
            assert forall|i: int| 0 <= i < ys.len() implies shape_eq(#[trigger] ys[i], xs[i]) by { lemma_shape_sym(xs[i], ys[i]); }
        },
        Val::Adt(_, xs) => if let Val::Adt(_, ys) = b {
            assert forall|i: int| 0 <= i < ys.len() implies shape_eq(#[trigger] ys[i], xs[i]) by { lemma_shape_sym(xs[i], ys[i]); }
        },
        Val::Arr(xs) => if let Val::Arr(ys) = b {
            assert forall|i: int| 0 <= i < ys.len() implies shape_eq(#[trigger] ys[i], xs[i]) by { lemma_shape_sym(xs[i], ys[i]); }
        },
        Val::Shr(x) => if let Val::Shr(y) = b { lemma_shape_sym(*x, *y); },
        _ => {},
    }
}

pub proof fn lemma_shape_trans(a: Val, b: Val, c: Val)
    requires shape_eq(a, b), shape_eq(b, c),
    ensures shape_eq(a, c),
    decreases a,
{
    match a {
        Val::Tup(xs) => if let Val::Tup(ys) = b { if let Val::Tup(zs) = c {
            assert forall|i: int| 0 <= i < xs.len() implies shape_eq(#[trigger] xs[i], zs[i]) by { lemma_shape_trans(xs[i], ys[i], zs[i]); }
        } },
        Val::Adt(_, xs) => if let Val::Adt(_, ys) = b { if let Val::Adt(_, zs) = c {
            assert forall|i: int| 0 <= i < xs.len() implies shape_eq(#[trigger] xs[i], zs[i]) by { lemma_shape_trans(xs[i], ys[i], zs[i]); }
        } },
        Val::Arr(xs) => if let Val::Arr(ys) = b { if let Val::Arr(zs) = c {
            assert forall|i: int| 0 <= i < xs.len() implies shape_eq(#[trigger] xs[i], zs[i]) by { lemma_shape_trans(xs[i], ys[i], zs[i]); }
        } },
        Val::Shr(x) => if let Val::Shr(y) = b { if let Val::Shr(z) = c { lemma_shape_trans(*x, *y, *z); } },
        _ => {},
    }
}

/// `val_rel` at either label implies `shape_eq`.
pub proof fn lemma_rel_shape(s: bool, a: Val, b: Val)
    requires val_rel(s, a, b),
    ensures shape_eq(a, b),
{
    if !s { lemma_shape_refl(a); }
}

pub proof fn lemma_get_shape(v1: Val, v2: Val, e: PE)
    requires shape_eq(v1, v2),
    ensures shape_eq(get(v1, e), get(v2, e)),
{
    match (v1, v2) {
        (Val::Tup(xs), Val::Tup(ys)) => if let PE::Field(i) = e { if i < xs.len() { assert(shape_eq(xs[i as int], ys[i as int])); } },
        (Val::Adt(_, xs), Val::Adt(_, ys)) => match e {
            PE::Field(i) => if i < xs.len() { assert(shape_eq(xs[i as int], ys[i as int])); },
            PE::Variant(k) => {
                assert forall|i: int| 0 <= i < xs.len() implies shape_eq(#[trigger] xs[i], ys[i]) by {}
            },
            _ => {},
        },
        (Val::Arr(xs), Val::Arr(ys)) => if let PE::Index(i) = e { if i < xs.len() { assert(shape_eq(xs[i as int], ys[i as int])); } },
        _ => {},
    }
}

pub proof fn lemma_read_at_shape(v1: Val, v2: Val, path: Seq<PE>)
    requires shape_eq(v1, v2),
    ensures shape_eq(read_at(v1, path), read_at(v2, path)),
    decreases path.len(),
{
    if path.len() > 0 {
        lemma_get_shape(v1, v2, path[0]);
        lemma_read_at_shape(get(v1, path[0]), get(v2, path[0]), path.drop_first());
    }
}

// ------------------------------------------------------------------ places: agreement

/// No `Index` projection reads a secret or out-of-range local.
pub open spec fn idx_ok(b: Body, l: FnLab, ps: Seq<Proj>) -> bool {
    forall|k: int| 0 <= k < ps.len() && (#[trigger] ps[k]) is Index ==>
        ps[k]->Index_0 < b.locals@.len() && !lab(l, ps[k]->Index_0 as nat)
}

/// Two place-walk cursors of a place whose local is labelled `s`.
pub open spec fn crel(l: FnLab, c1: Cur, c2: Cur, s: bool) -> bool {
    match c1 {
        Cur::L(a) => c2 == Cur::L(a) && root_lab(l, a.root) == s,
        Cur::V(v1) => match c2 { Cur::V(v2) => val_rel(s, v1, v2), _ => false },
    }
}

pub proof fn lemma_read_loc_agree(p: Program, ls: Seq<FnLab>, f: nat, fr1: Frame, fr2: Frame, loc: Loc)
    requires agree(p, ls, f, fr1, fr2),
    ensures
        val_rel(root_lab(ls[f as int], loc.root), read_loc(fr1, loc), read_loc(fr2, loc)),
        shape_eq(read_loc(fr1, loc), read_loc(fr2, loc)),
{
    let s = root_lab(ls[f as int], loc.root);
    let (v1, v2) = match loc.root {
        Root::Local(i) => (nth(fr1.locals, i), nth(fr2.locals, i)),
        Root::Slot(j) => (nth(fr1.slots, j), nth(fr2.slots, j)),
    };
    match loc.root {
        Root::Local(i) => if i < fr1.locals.len() { assert(val_rel(s, fr1.locals[i as int], fr2.locals[i as int])); },
        Root::Slot(j) => if j < fr1.slots.len() { assert(val_rel(s, fr1.slots[j as int], fr2.slots[j as int])); },
    }
    assert(val_rel(s, v1, v2));
    if s { lemma_read_at_shape(v1, v2, loc.path); } else { lemma_shape_refl(read_loc(fr1, loc)); }
}

/// Under `plc`, a location reads a `Mut` only when it is an empty-path local holding it.
pub proof fn lemma_read_loc_mut(p: Program, ls: Seq<FnLab>, f: nat, fr: Frame, loc: Loc)
    requires plc(p, ls, f, fr),
    ensures
        no_mut(read_loc(fr, loc)) || (loc.path.len() == 0 && (loc.root matches Root::Local(x)
            && x < fr.locals.len() && read_loc(fr, loc) == fr.locals[x as int] && fr.locals[x as int] is Mut)),
{
    let v = match loc.root {
        Root::Local(i) => nth(fr.locals, i),
        Root::Slot(j) => nth(fr.slots, j),
    };
    if !(v is Mut) {
        match loc.root {
            Root::Local(i) => if i < fr.locals.len() { assert(no_mut(fr.locals[i as int])); },
            Root::Slot(j) => if j < fr.slots.len() { assert(no_mut(fr.slots[j as int])); },
        }
        lemma_read_at_no_mut(v, loc.path);
    } else if loc.path.len() > 0 {
        lemma_read_at_no_mut(Val::Unit, loc.path.drop_first());
    }
}

pub proof fn lemma_step_agree(p: Program, ls: Seq<FnLab>, f: nat, fr1: Frame, fr2: Frame, c1: Cur, c2: Cur, pr: Proj, s: bool)
    requires
        agree(p, ls, f, fr1, fr2), plc(p, ls, f, fr1), crel(ls[f as int], c1, c2, s),
        pr is Index ==> pr->Index_0 < p.fns@[f as int].locals@.len() && !lab(ls[f as int], pr->Index_0 as nat),
    ensures
        step(fr1, c1, pr).1 == step(fr2, c2, pr).1,
        crel(ls[f as int], step(fr1, c1, pr).0, step(fr2, c2, pr).0, s),
{
    let l = ls[f as int];
    match pr {
        Proj::Deref => match c1 {
            Cur::L(a) => {
                lemma_read_loc_agree(p, ls, f, fr1, fr2, a);
                let v1 = read_loc(fr1, a);
                if v1 is Mut {
                    lemma_read_loc_mut(p, ls, f, fr1, a);
                    if let Root::Local(x) = a.root { assert(fr1.locals[x as int] == v1); }
                }
            },
            Cur::V(v1) => {},
        },
        Proj::Index(x) => {
            assert(fr1.locals[x as int] == fr2.locals[x as int]);
        },
        _ => match c1 {
            Cur::L(_) => {},
            Cur::V(v1) => if let Cur::V(v2) = c2 {
                if s {
                    let e = match pr { Proj::Field(i) => PE::Field(i as nat), Proj::ConstIndex(k) => PE::Index(k as nat), Proj::Downcast(k) => PE::Variant(k as nat), _ => PE::Field(0) };
                    lemma_get_shape(v1, v2, e);
                }
            },
        },
    }
}

pub proof fn lemma_walk_agree(p: Program, ls: Seq<FnLab>, f: nat, fr1: Frame, fr2: Frame, ps: Seq<Proj>, k: nat, c1: Cur, c2: Cur, s: bool)
    requires
        agree(p, ls, f, fr1, fr2), plc(p, ls, f, fr1), idx_ok(p.fns@[f as int], ls[f as int], ps),
        k <= ps.len(), crel(ls[f as int], c1, c2, s),
    ensures
        walk(fr1, ps, k, c1).1 == walk(fr2, ps, k, c2).1,
        crel(ls[f as int], walk(fr1, ps, k, c1).0, walk(fr2, ps, k, c2).0, s),
    decreases ps.len() - k,
{
    if k < ps.len() {
        assert(ps[k as int] is Index ==> ps[k as int]->Index_0 < p.fns@[f as int].locals@.len());
        lemma_step_agree(p, ls, f, fr1, fr2, c1, c2, ps[k as int], s);
        lemma_walk_agree(p, ls, f, fr1, fr2, ps, k + 1, step(fr1, c1, ps[k as int]).0, step(fr2, c2, ps[k as int]).0, s);
    }
}

pub proof fn lemma_read_place_agree(p: Program, ls: Seq<FnLab>, f: nat, fr1: Frame, fr2: Frame, pl: Place)
    requires
        agree(p, ls, f, fr1, fr2), plc(p, ls, f, fr1), plc(p, ls, f, fr2),
        ok_place(p.fns@[f as int], ls[f as int], pl),
    ensures
        read_place(fr1, pl).1 == read_place(fr2, pl).1,
        !lab(ls[f as int], pl.local as nat) ==> read_place(fr1, pl).0 == read_place(fr2, pl).0,
        shape_eq(read_place(fr1, pl).0, read_place(fr2, pl).0),
{
    let s = lab(ls[f as int], pl.local as nat);
    let c0 = Cur::L(local_loc(pl.local as nat));
    lemma_walk_agree(p, ls, f, fr1, fr2, pl.proj@, 0, c0, c0, s);
    match place_walk(fr1, pl).0 {
        Cur::L(a) => lemma_read_loc_agree(p, ls, f, fr1, fr2, a),
        Cur::V(v1) => lemma_rel_shape(s, v1, read_place(fr2, pl).0),
    }
}

// ------------------------------------------------------------------ no_mut

pub proof fn lemma_get_no_mut(v: Val, e: PE)
    requires no_mut(v),
    ensures no_mut(get(v, e)),
{
    match (v, e) {
        (Val::Tup(vs), PE::Field(i)) => if i < vs.len() { assert(no_mut(vs[i as int])); },
        (Val::Adt(_, vs), PE::Field(i)) => if i < vs.len() { assert(no_mut(vs[i as int])); },
        (Val::Arr(vs), PE::Index(i)) => if i < vs.len() { assert(no_mut(vs[i as int])); },
        (Val::Adt(_, vs), PE::Variant(_)) => { assert forall|i: int| 0 <= i < vs.len() implies no_mut(#[trigger] vs[i]) by {} },
        _ => {},
    }
}

pub proof fn lemma_read_at_no_mut(v: Val, path: Seq<PE>)
    requires no_mut(v),
    ensures no_mut(read_at(v, path)),
    decreases path.len(),
{
    if path.len() > 0 {
        lemma_get_no_mut(v, path[0]);
        lemma_read_at_no_mut(get(v, path[0]), path.drop_first());
    }
}

// ------------------------------------------------------------------ writes: shape

/// `pad(xs, i + 1).update(i, w)` keeps pointwise `shape_eq`.
pub proof fn lemma_fields_put_shape(xs: Seq<Val>, ys: Seq<Val>, i: nat, w1: Val, w2: Val)
    requires
        xs.len() == ys.len(), forall|k: int| 0 <= k < xs.len() ==> shape_eq(#[trigger] xs[k], ys[k]),
        shape_eq(w1, w2),
    ensures ({
        let (a, b) = (pad(xs, i + 1).update(i as int, w1), pad(ys, i + 1).update(i as int, w2));
        a.len() == b.len() && forall|k: int| 0 <= k < a.len() ==> shape_eq(#[trigger] a[k], b[k])
    }),
{
    let (a, b) = (pad(xs, i + 1).update(i as int, w1), pad(ys, i + 1).update(i as int, w2));
    assert forall|k: int| 0 <= k < a.len() implies shape_eq(#[trigger] a[k], b[k]) by {
        if k != i as int {
            if k < xs.len() {
                assert(pad(xs, i + 1)[k] == xs[k] && pad(ys, i + 1)[k] == ys[k]);
            } else {
                assert(pad(xs, i + 1)[k] == Val::Unit && pad(ys, i + 1)[k] == Val::Unit);
            }
        }
    }
}

pub proof fn lemma_put_shape(v1: Val, v2: Val, e: PE, w1: Val, w2: Val)
    requires shape_eq(v1, v2), shape_eq(w1, w2),
    ensures shape_eq(put(v1, e, w1), put(v2, e, w2)),
{
    match (v1, v2) {
        (Val::Tup(xs), Val::Tup(ys)) => if let PE::Field(i) = e { lemma_fields_put_shape(xs, ys, i, w1, w2); },
        (Val::Adt(_, xs), Val::Adt(_, ys)) => match e {
            PE::Field(i) => lemma_fields_put_shape(xs, ys, i, w1, w2),
            PE::Variant(_) => if let (Val::Adt(_, ws1), Val::Adt(_, ws2)) = (w1, w2) {
                assert forall|k: int| 0 <= k < ws1.len() implies shape_eq(#[trigger] ws1[k], ws2[k]) by {}
            },
            _ => {},
        },
        (Val::Arr(xs), Val::Arr(ys)) => if let PE::Index(i) = e {
            if i < xs.len() {
                let (a, b) = (xs.update(i as int, w1), ys.update(i as int, w2));
                assert forall|k: int| 0 <= k < a.len() implies shape_eq(#[trigger] a[k], b[k]) by {
                    if k != i as int { assert(shape_eq(xs[k], ys[k])); }
                }
            }
        },
        _ => {},
    }
}

pub proof fn lemma_write_at_shape(v1: Val, v2: Val, path: Seq<PE>, w1: Val, w2: Val)
    requires shape_eq(v1, v2), shape_eq(w1, w2),
    ensures shape_eq(write_at(v1, path, w1), write_at(v2, path, w2)),
    decreases path.len(),
{
    if path.len() > 0 {
        lemma_get_shape(v1, v2, path[0]);
        lemma_write_at_shape(get(v1, path[0]), get(v2, path[0]), path.drop_first(), w1, w2);
        lemma_put_shape(v1, v2, path[0], write_at(get(v1, path[0]), path.drop_first(), w1),
            write_at(get(v2, path[0]), path.drop_first(), w2));
    }
}

/// Writing values related at the root's label keeps `agree`.
pub proof fn lemma_write_loc_agree(p: Program, ls: Seq<FnLab>, f: nat, fr1: Frame, fr2: Frame, l: Loc, w1: Val, w2: Val)
    requires agree(p, ls, f, fr1, fr2), val_rel(root_lab(ls[f as int], l.root), w1, w2),
    ensures agree(p, ls, f, write_loc(fr1, l, w1), write_loc(fr2, l, w2)),
{
    let lb = ls[f as int];
    let (g1, g2) = (write_loc(fr1, l, w1), write_loc(fr2, l, w2));
    match l.root {
        Root::Local(i) => if i < fr1.locals.len() {
            let (o1, o2) = (fr1.locals[i as int], fr2.locals[i as int]);
            if lab(lb, i) { lemma_write_at_shape(o1, o2, l.path, w1, w2); }
            assert forall|x: int| 0 <= x < g1.locals.len() implies
                val_rel(lab(lb, x as nat), #[trigger] g1.locals[x], g2.locals[x]) by {
                if x != i as int { assert(val_rel(lab(lb, x as nat), fr1.locals[x], fr2.locals[x])); }
            }
            assert forall|j: int| 0 <= j < g1.slots.len() implies
                val_rel(slot_lab(lb, j as nat), #[trigger] g1.slots[j], g2.slots[j]) by {
                assert(val_rel(slot_lab(lb, j as nat), fr1.slots[j], fr2.slots[j]));
            }
        },
        Root::Slot(i) => if i < fr1.slots.len() {
            let (o1, o2) = (fr1.slots[i as int], fr2.slots[i as int]);
            if slot_lab(lb, i) { lemma_write_at_shape(o1, o2, l.path, w1, w2); }
            assert forall|j: int| 0 <= j < g1.slots.len() implies
                val_rel(slot_lab(lb, j as nat), #[trigger] g1.slots[j], g2.slots[j]) by {
                if j != i as int { assert(val_rel(slot_lab(lb, j as nat), fr1.slots[j], fr2.slots[j])); }
            }
            assert forall|x: int| 0 <= x < g1.locals.len() implies
                val_rel(lab(lb, x as nat), #[trigger] g1.locals[x], g2.locals[x]) by {
                assert(val_rel(lab(lb, x as nat), fr1.locals[x], fr2.locals[x]));
            }
        },
    }
}

/// Every frame agrees with itself.
pub proof fn lemma_agree_refl(p: Program, ls: Seq<FnLab>, f: nat, fr: Frame)
    requires fr.locals.len() == p.fns@[f as int].locals@.len(),
    ensures agree(p, ls, f, fr, fr),
{
    assert forall|x: int| 0 <= x < fr.locals.len() implies val_rel(lab(ls[f as int], x as nat), #[trigger] fr.locals[x], fr.locals[x]) by {
        lemma_shape_refl(fr.locals[x]);
    }
    assert forall|j: int| 0 <= j < fr.slots.len() implies val_rel(slot_lab(ls[f as int], j as nat), #[trigger] fr.slots[j], fr.slots[j]) by {
        lemma_shape_refl(fr.slots[j]);
    }
}

pub proof fn lemma_place_loc_agree(p: Program, ls: Seq<FnLab>, f: nat, fr1: Frame, fr2: Frame, pl: Place)
    requires
        agree(p, ls, f, fr1, fr2), plc(p, ls, f, fr1), plc(p, ls, f, fr2),
        ok_place(p.fns@[f as int], ls[f as int], pl),
    ensures
        (place_loc(fr1, pl) is None && place_loc(fr2, pl) is None)
            || (place_loc(fr1, pl) is Some && place_loc(fr1, pl) == place_loc(fr2, pl)),
        place_walk(fr1, pl).1 == place_walk(fr2, pl).1,
{
    let c0 = Cur::L(local_loc(pl.local as nat));
    lemma_walk_agree(p, ls, f, fr1, fr2, pl.proj@, 0, c0, c0, lab(ls[f as int], pl.local as nat));
}

// ------------------------------------------------------------------ operands and rvalues: agreement

pub proof fn lemma_eval_op_agree(p: Program, ls: Seq<FnLab>, f: nat, fr1: Frame, fr2: Frame, op: Operand)
    requires
        agree(p, ls, f, fr1, fr2), plc(p, ls, f, fr1), plc(p, ls, f, fr2),
        ok_op(p.fns@[f as int], ls[f as int], op),
    ensures
        eval_op(fr1, op).1 == eval_op(fr2, op).1,
        !sec_op(p.fns@[f as int], ls[f as int], op) ==> eval_op(fr1, op).0 == eval_op(fr2, op).0,
        shape_eq(eval_op(fr1, op).0, eval_op(fr2, op).0),
{
    match op {
        Operand::Copy(pl) => lemma_read_place_agree(p, ls, f, fr1, fr2, pl),
        Operand::Const(_, _) => {},
        Operand::Lit(c) => lemma_shape_refl(const_val(c)),
    }
}

pub proof fn lemma_ops_ev_agree(p: Program, ls: Seq<FnLab>, f: nat, fr1: Frame, fr2: Frame, ops: Seq<Operand>)
    requires
        agree(p, ls, f, fr1, fr2), plc(p, ls, f, fr1), plc(p, ls, f, fr2),
        forall|i: int| 0 <= i < ops.len() ==> ok_op(p.fns@[f as int], ls[f as int], #[trigger] ops[i]),
    ensures ops_ev(fr1, ops) == ops_ev(fr2, ops),
    decreases ops.len(),
{
    if ops.len() > 0 {
        assert(ok_op(p.fns@[f as int], ls[f as int], ops[ops.len() - 1]));
        lemma_eval_op_agree(p, ls, f, fr1, fr2, ops.last());
        let d = ops.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies ok_op(p.fns@[f as int], ls[f as int], #[trigger] d[i]) by {
            assert(d[i] == ops[i]);
        }
        lemma_ops_ev_agree(p, ls, f, fr1, fr2, d);
    }
}

/// `elems` of shape-equal values: equal lengths, pointwise `shape_eq`.
pub proof fn lemma_elems_shape(p: Program, ls: Seq<FnLab>, f: nat, fr1: Frame, fr2: Frame, v1: Val, v2: Val)
    requires agree(p, ls, f, fr1, fr2), shape_eq(v1, v2),
    ensures
        elems(fr1, v1).len() == elems(fr2, v2).len(),
        forall|i: int| 0 <= i < elems(fr1, v1).len() ==> shape_eq(#[trigger] elems(fr1, v1)[i], elems(fr2, v2)[i]),
{
    let t1 = match v1 { Val::Shr(b) => *b, Val::Mut(l) => read_loc(fr1, l), _ => v1 };
    let t2 = match v2 { Val::Shr(b) => *b, Val::Mut(l) => read_loc(fr2, l), _ => v2 };
    if let Val::Mut(l) = v1 { lemma_read_loc_agree(p, ls, f, fr1, fr2, l); }
    assert(shape_eq(t1, t2));
    if let (Val::Arr(xs), Val::Arr(ys)) = (t1, t2) {
        assert forall|i: int| 0 <= i < xs.len() implies shape_eq(#[trigger] xs[i], ys[i]) by {}
    }
}

pub proof fn lemma_eval_rv_agree(p: Program, ls: Seq<FnLab>, f: nat, fr1: Frame, fr2: Frame, rv: Rvalue)
    requires
        agree(p, ls, f, fr1, fr2), plc(p, ls, f, fr1), plc(p, ls, f, fr2),
        ok_rv(p.fns@[f as int], ls[f as int], rv),
    ensures
        eval_rv(fr1, rv).1 == eval_rv(fr2, rv).1,
        !sec_rv(p.fns@[f as int], ls[f as int], rv) ==> eval_rv(fr1, rv).0 == eval_rv(fr2, rv).0,
        shape_eq(eval_rv(fr1, rv).0, eval_rv(fr2, rv).0),
{
    let (b, l) = (p.fns@[f as int], ls[f as int]);
    match rv {
        Rvalue::Use(op) => lemma_eval_op_agree(p, ls, f, fr1, fr2, op),
        Rvalue::Bin(op, ty, x, y) => {
            lemma_eval_op_agree(p, ls, f, fr1, fr2, x);
            lemma_eval_op_agree(p, ls, f, fr1, fr2, y);
            let (a1, b1) = (as_int(eval_op(fr1, x).0), as_int(eval_op(fr1, y).0));
            let (a2, b2) = (as_int(eval_op(fr2, x).0), as_int(eval_op(fr2, y).0));
            assert(op_ev(op, a1, b1) == op_ev(op, a2, b2));
        },
        Rvalue::Un(_, _, x) => lemma_eval_op_agree(p, ls, f, fr1, fr2, x),
        Rvalue::Cast(_, _, x) => lemma_eval_op_agree(p, ls, f, fr1, fr2, x),
        Rvalue::Len(pl) => {
            lemma_read_place_agree(p, ls, f, fr1, fr2, pl);
            lemma_elems_shape(p, ls, f, fr1, fr2, read_place(fr1, pl).0, read_place(fr2, pl).0);
        },
        Rvalue::Discr(pl) => lemma_read_place_agree(p, ls, f, fr1, fr2, pl),
        Rvalue::Aggregate(kind, ops) => {
            let (vs1, vs2) = (op_vals(fr1, ops@), op_vals(fr2, ops@));
            assert forall|i: int| 0 <= i < ops@.len() implies
                shape_eq(#[trigger] vs1[i], vs2[i]) && (!sec_op(b, l, ops@[i]) ==> vs1[i] == vs2[i]) by {
                assert(ok_op(b, l, ops@[i]));
                lemma_eval_op_agree(p, ls, f, fr1, fr2, ops@[i]);
            }
            if !sec_rv(b, l, rv) {
                assert forall|i: int| 0 <= i < ops@.len() implies #[trigger] vs1[i] == vs2[i] by {
                    assert(!sec_op(b, l, ops@[i]));
                }
                assert(vs1 =~= vs2);
            }
            lemma_ops_ev_agree(p, ls, f, fr1, fr2, ops@);
        },
        Rvalue::Repeat(x, n) => {
            lemma_eval_op_agree(p, ls, f, fr1, fr2, x);
            let (v1, v2) = (eval_op(fr1, x).0, eval_op(fr2, x).0);
            let (r1, r2) = (Seq::new(n as nat, |j: int| v1), Seq::new(n as nat, |j: int| v2));
            assert forall|i: int| 0 <= i < r1.len() implies shape_eq(#[trigger] r1[i], r2[i]) by {}
            if !sec_op(b, l, x) { assert(r1 =~= r2); }
        },
        Rvalue::RefShr(pl) => lemma_read_place_agree(p, ls, f, fr1, fr2, pl),
        Rvalue::RefMut(pl) => lemma_place_loc_agree(p, ls, f, fr1, fr2, pl),
    }
}

// ------------------------------------------------------------------ plc: single-frame facts

pub proof fn lemma_put_no_mut(v: Val, e: PE, w: Val)
    requires no_mut(v), no_mut(w),
    ensures no_mut(put(v, e, w)),
{
    match (v, e) {
        (Val::Tup(vs), PE::Field(i)) => {
            let a = pad(vs, i + 1).update(i as int, w);
            assert forall|k: int| 0 <= k < a.len() implies no_mut(#[trigger] a[k]) by {
                if k != i as int { if k < vs.len() { assert(pad(vs, i + 1)[k] == vs[k]); } else { assert(pad(vs, i + 1)[k] == Val::Unit); } }
            }
        },
        (Val::Adt(_, vs), PE::Field(i)) => {
            let a = pad(vs, i + 1).update(i as int, w);
            assert forall|k: int| 0 <= k < a.len() implies no_mut(#[trigger] a[k]) by {
                if k != i as int { if k < vs.len() { assert(pad(vs, i + 1)[k] == vs[k]); } else { assert(pad(vs, i + 1)[k] == Val::Unit); } }
            }
        },
        (Val::Arr(vs), PE::Index(i)) => if i < vs.len() {
            let a = vs.update(i as int, w);
            assert forall|k: int| 0 <= k < a.len() implies no_mut(#[trigger] a[k]) by { if k != i as int { assert(no_mut(vs[k])); } }
        },
        (Val::Adt(_, _), PE::Variant(_)) => if let Val::Adt(_, ws) = w {
            assert forall|k: int| 0 <= k < ws.len() implies no_mut(#[trigger] ws[k]) by {}
        },
        _ => {},
    }
}

pub proof fn lemma_write_at_no_mut(v: Val, path: Seq<PE>, w: Val)
    requires no_mut(v), no_mut(w),
    ensures no_mut(write_at(v, path, w)),
    decreases path.len(),
{
    if path.len() > 0 {
        lemma_get_no_mut(v, path[0]);
        lemma_write_at_no_mut(get(v, path[0]), path.drop_first(), w);
        lemma_put_no_mut(v, path[0], write_at(get(v, path[0]), path.drop_first(), w));
    }
}

pub proof fn lemma_const_no_mut(c: ConstVal)
    ensures no_mut(const_val(c)),
    decreases c,
{
    match c {
        ConstVal::Arr(cs) => {
            let vs = Seq::new(cs@.len(), |i: int| if 0 <= i < cs@.len() { const_val(cs@[i]) } else { Val::Unit });
            assert forall|i: int| 0 <= i < vs.len() implies no_mut(#[trigger] vs[i]) by { lemma_const_no_mut(cs@[i]); }
            assert(const_val(c)->Arr_0 =~= vs);
        },
        ConstVal::Shr(b) => lemma_const_no_mut(*b),
        _ => {},
    }
}

/// The read-side walk invariant: a cursor at a location that reads no `Mut` (a non-empty path,
/// or a `root_ok` root), or a snapshot value with no `Mut`.
pub open spec fn wr_inv(b: Body, fr: Frame, c: Cur) -> bool {
    match c {
        Cur::L(a) => root_ok(b, fr, a.root) || (a.path.len() > 0 && (a.root matches Root::Local(x) && x < fr.locals.len())),
        Cur::V(v) => no_mut(v),
    }
}

/// The `RefMut` walk invariant: a cursor at a `root_ok` root, or a snapshot value.
pub open spec fn wt_inv(b: Body, fr: Frame, c: Cur) -> bool {
    match c { Cur::L(a) => root_ok(b, fr, a.root), Cur::V(_) => true }
}

pub proof fn lemma_step_plc(p: Program, ls: Seq<FnLab>, f: nat, fr: Frame, c: Cur, pr: Proj)
    requires plc(p, ls, f, fr), wr_inv(p.fns@[f as int], fr, c),
    ensures
        wr_inv(p.fns@[f as int], fr, step(fr, c, pr).0),
        wt_inv(p.fns@[f as int], fr, c) ==> wt_inv(p.fns@[f as int], fr, step(fr, c, pr).0),
{
    if let (Proj::Deref, Cur::L(a)) = (pr, c) {
        lemma_read_loc_mut(p, ls, f, fr, a);
        if let Root::Local(x) = a.root { if x < fr.locals.len() { assert(fr.locals[x as int] is Mut ==> p.fns@[f as int].locals@[x as int] is Mut); } }
        let v = read_loc(fr, a);
        if let Val::Shr(bx) = v { assert(no_mut(*bx)); }
    } else if let Cur::V(v) = c {
        match pr {
            Proj::Field(i) => lemma_get_no_mut(v, PE::Field(i as nat)),
            Proj::Index(x) => lemma_get_no_mut(v, PE::Index(as_int(read_loc(fr, local_loc(x as nat))) as nat)),
            Proj::ConstIndex(k) => lemma_get_no_mut(v, PE::Index(k as nat)),
            Proj::Downcast(k) => lemma_get_no_mut(v, PE::Variant(k as nat)),
            Proj::Deref => {},
        }
    }
}

pub proof fn lemma_walk_plc(p: Program, ls: Seq<FnLab>, f: nat, fr: Frame, ps: Seq<Proj>, k: nat, c: Cur)
    requires plc(p, ls, f, fr), k <= ps.len(), wr_inv(p.fns@[f as int], fr, c),
    ensures
        wr_inv(p.fns@[f as int], fr, walk(fr, ps, k, c).0),
        wt_inv(p.fns@[f as int], fr, c) ==> wt_inv(p.fns@[f as int], fr, walk(fr, ps, k, c).0),
    decreases ps.len() - k,
{
    if k < ps.len() {
        lemma_step_plc(p, ls, f, fr, c, ps[k as int]);
        lemma_walk_plc(p, ls, f, fr, ps, k + 1, step(fr, c, ps[k as int]).0);
    }
}

/// `wr_inv` cursors read no `Mut`.
pub proof fn lemma_wr_read(p: Program, ls: Seq<FnLab>, f: nat, fr: Frame, c: Cur)
    requires plc(p, ls, f, fr), wr_inv(p.fns@[f as int], fr, c),
    ensures no_mut(match c { Cur::L(a) => read_loc(fr, a), Cur::V(v) => v }),
{
    if let Cur::L(a) = c {
        lemma_read_loc_mut(p, ls, f, fr, a);
        if let Root::Local(x) = a.root { if x < fr.locals.len() { assert(fr.locals[x as int] is Mut ==> p.fns@[f as int].locals@[x as int] is Mut); } }
    }
}

/// Single-frame place facts under `plc`: what a place reads, and where it writes.
pub proof fn lemma_place_plc(p: Program, ls: Seq<FnLab>, f: nat, fr: Frame, pl: Place)
    requires plc(p, ls, f, fr), ok_place(p.fns@[f as int], ls[f as int], pl),
    ensures ({
        let (b, l) = (p.fns@[f as int], ls[f as int]);
        &&& !mut_pl(b, pl) ==> no_mut(read_place(fr, pl).0)
        &&& mut_pl(b, pl) ==> read_place(fr, pl).0 == fr.locals[pl.local as int]
            && place_loc(fr, pl) == Some((local_loc(pl.local as nat), Seq::<Event>::empty()))
        &&& place_loc(fr, pl) matches Some((loc, _)) ==> root_lab(l, loc.root) == lab(l, pl.local as nat)
        &&& refmut_ok(b, pl) ==> (place_loc(fr, pl) matches Some((loc, _)) ==> tgt_ok(b, l, fr, loc, lab(l, pl.local as nat)))
    }),
{
    let (b, l) = (p.fns@[f as int], ls[f as int]);
    let (ps, x) = (pl.proj@, pl.local as nat);
    let c0 = Cur::L(local_loc(x));
    // labels: the two-frame walk lemma on (fr, fr)
    lemma_agree_refl(p, ls, f, fr);
    lemma_walk_agree(p, ls, f, fr, fr, ps, 0, c0, c0, lab(l, x));
    if !(b.locals@[x as int] is Mut) {
        lemma_walk_plc(p, ls, f, fr, ps, 0, c0);
        lemma_wr_read(p, ls, f, fr, place_walk(fr, pl).0);
    } else if ps.len() > 0 {
        let c1 = step(fr, c0, ps[0]).0;
        assert(walk(fr, ps, 0, c0).0 == walk(fr, ps, 1, c1).0);
        assert(wr_inv(b, fr, c1) && (ps[0] is Deref ==> wt_inv(b, fr, c1))) by {
            if ps[0] is Deref {
                if let Val::Mut(l2) = fr.locals[x as int] { assert(tgt_ok(b, l, fr, l2, lab(l, x))); }
                if let Val::Shr(bx) = fr.locals[x as int] { assert(no_mut(fr.locals[x as int])); }
            }
            if let Cur::V(v) = c1 {
                if !(ps[0] is Deref) { lemma_get_no_mut(Val::Unit, PE::Field(0)); }
            }
        }
        lemma_walk_plc(p, ls, f, fr, ps, 1, c1);
        lemma_wr_read(p, ls, f, fr, walk(fr, ps, 1, c1).0);
    }
}

pub proof fn lemma_write_loc_plc(p: Program, ls: Seq<FnLab>, f: nat, fr: Frame, loc: Loc, w: Val)
    requires plc(p, ls, f, fr), no_mut(w),
    ensures plc(p, ls, f, write_loc(fr, loc, w)),
{
    let (b, l) = (p.fns@[f as int], ls[f as int]);
    let g = write_loc(fr, loc, w);
    match loc.root {
        Root::Local(i) => if i < fr.locals.len() {
            let o = fr.locals[i as int];
            if o is Mut && loc.path.len() > 0 {
                assert(write_at(o, loc.path, w) == o);
            } else if !(o is Mut) {
                lemma_write_at_no_mut(o, loc.path, w);
            }
        },
        Root::Slot(j) => if j < fr.slots.len() {
            lemma_write_at_no_mut(fr.slots[j as int], loc.path, w);
        },
    }
    assert forall|x: int| #![trigger g.locals[x]] 0 <= x < g.locals.len() implies (match g.locals[x] {
        Val::Mut(m) => b.locals@[x] is Mut && tgt_ok(b, l, g, m, lab(l, x as nat)),
        v => no_mut(v),
    }) by {
        assert(match fr.locals[x] {
            Val::Mut(m) => b.locals@[x] is Mut && tgt_ok(b, l, fr, m, lab(l, x as nat)),
            v => no_mut(v),
        });
    }
    assert forall|j: int| 0 <= j < g.slots.len() implies no_mut(#[trigger] g.slots[j]) by {
        assert(no_mut(fr.slots[j]));
    }
}

/// Writing a well-targeted `Mut` into an empty-path `Mut`-typed local keeps `plc`.
pub proof fn lemma_write_loc_plc_mut(p: Program, ls: Seq<FnLab>, f: nat, fr: Frame, x: nat, m: Loc)
    requires
        plc(p, ls, f, fr), x < fr.locals.len(), p.fns@[f as int].locals@[x as int] is Mut,
        tgt_ok(p.fns@[f as int], ls[f as int], fr, m, lab(ls[f as int], x)),
    ensures plc(p, ls, f, write_loc(fr, local_loc(x), Val::Mut(m))),
{
    let (b, l) = (p.fns@[f as int], ls[f as int]);
    let g = write_loc(fr, local_loc(x), Val::Mut(m));
    assert forall|y: int| #![trigger g.locals[y]] 0 <= y < g.locals.len() implies (match g.locals[y] {
        Val::Mut(m2) => b.locals@[y] is Mut && tgt_ok(b, l, g, m2, lab(l, y as nat)),
        v => no_mut(v),
    }) by {
        assert(match fr.locals[y] {
            Val::Mut(m2) => b.locals@[y] is Mut && tgt_ok(b, l, fr, m2, lab(l, y as nat)),
            v => no_mut(v),
        });
    }
    assert forall|j: int| 0 <= j < g.slots.len() implies no_mut(#[trigger] g.slots[j]) by {
        assert(no_mut(fr.slots[j]));
    }
}

/// A non-`Mut`-yielding rvalue gives a value with no `Mut`.
pub proof fn lemma_eval_rv_plc(p: Program, ls: Seq<FnLab>, f: nat, fr: Frame, rv: Rvalue)
    requires plc(p, ls, f, fr), ok_rv(p.fns@[f as int], ls[f as int], rv),
    ensures
        (rv matches Rvalue::Use(op) && mut_op(p.fns@[f as int], op)) || rv is RefMut
            || no_mut(eval_rv(fr, rv).0),
{
    let (b, l) = (p.fns@[f as int], ls[f as int]);
    match rv {
        Rvalue::Use(op) => match op {
            Operand::Copy(pl) => lemma_place_plc(p, ls, f, fr, pl),
            Operand::Lit(c) => lemma_const_no_mut(c),
            _ => {},
        },
        Rvalue::Aggregate(_, ops) => {
            let vs = op_vals(fr, ops@);
            assert forall|i: int| 0 <= i < vs.len() implies no_mut(#[trigger] vs[i]) by {
                assert(ok_op(b, l, ops@[i]) && !mut_op(b, ops@[i]));
                match ops@[i] {
                    Operand::Copy(pl) => lemma_place_plc(p, ls, f, fr, pl),
                    Operand::Lit(c) => lemma_const_no_mut(c),
                    _ => {},
                }
            }
        },
        Rvalue::Repeat(op, n) => {
            match op {
                Operand::Copy(pl) => lemma_place_plc(p, ls, f, fr, pl),
                Operand::Lit(c) => lemma_const_no_mut(c),
                _ => {},
            }
            let vs = Seq::new(n as nat, |j: int| eval_op(fr, op).0);
            assert forall|i: int| 0 <= i < vs.len() implies no_mut(#[trigger] vs[i]) by {}
        },
        Rvalue::RefShr(pl) => lemma_place_plc(p, ls, f, fr, pl),
        _ => {},
    }
}

/// `dst = &mut q` keeps `plc`: the new `Mut` targets `q`'s root, whose label is `lab(dst)`.
pub proof fn lemma_plc_refmut(p: Program, ls: Seq<FnLab>, f: nat, fr: Frame, pl: Place, q: Place)
    requires plc(p, ls, f, fr), ok_stmt(p.fns@[f as int], ls[f as int], Stmt::Assign(pl, Rvalue::RefMut(q))),
    ensures plc(p, ls, f, exec_stmt(fr, Stmt::Assign(pl, Rvalue::RefMut(q))).0),
{
    let (b, l) = (p.fns@[f as int], ls[f as int]);
    let x = pl.local as nat;
    lemma_place_plc(p, ls, f, fr, pl);
    lemma_place_plc(p, ls, f, fr, q);
    assert(place_loc(fr, pl) == Some((local_loc(x), Seq::<Event>::empty())));
    if let Some((m, _)) = place_loc(fr, q) {
        assert(tgt_ok(b, l, fr, m, lab(l, q.local as nat)));
        assert(lab(l, x) == lab(l, q.local as nat));
        lemma_write_loc_plc_mut(p, ls, f, fr, x, m);
    } else {
        lemma_write_loc_plc(p, ls, f, fr, local_loc(x), Val::Unit);
    }
}

/// `dst = move q` of a `Mut`-typed `q` into a `Mut`-typed `dst` of the same label keeps `plc`.
pub proof fn lemma_plc_move(p: Program, ls: Seq<FnLab>, f: nat, fr: Frame, pl: Place, q: Place)
    requires
        plc(p, ls, f, fr), mut_pl(p.fns@[f as int], q),
        ok_stmt(p.fns@[f as int], ls[f as int], Stmt::Assign(pl, Rvalue::Use(Operand::Copy(q)))),
    ensures plc(p, ls, f, exec_stmt(fr, Stmt::Assign(pl, Rvalue::Use(Operand::Copy(q)))).0),
{
    let (b, l) = (p.fns@[f as int], ls[f as int]);
    let x = pl.local as nat;
    lemma_place_plc(p, ls, f, fr, pl);
    lemma_place_plc(p, ls, f, fr, q);
    assert(place_loc(fr, pl) == Some((local_loc(x), Seq::<Event>::empty())));
    let o = fr.locals[q.local as int];
    assert(match o {
        Val::Mut(m) => b.locals@[q.local as int] is Mut && tgt_ok(b, l, fr, m, lab(l, q.local as nat)),
        v => no_mut(v),
    });
    if let Val::Mut(m) = o {
        assert(lab(l, x) == lab(l, q.local as nat));
        lemma_write_loc_plc_mut(p, ls, f, fr, x, m);
    } else {
        lemma_write_loc_plc(p, ls, f, fr, local_loc(x), o);
    }
}

/// Any other assignment writes a value with no `Mut`.
pub proof fn lemma_plc_assign_nm(p: Program, ls: Seq<FnLab>, f: nat, fr: Frame, pl: Place, rv: Rvalue)
    requires
        plc(p, ls, f, fr), ok_stmt(p.fns@[f as int], ls[f as int], Stmt::Assign(pl, rv)),
        !(rv is RefMut), !(rv matches Rvalue::Use(op) && mut_op(p.fns@[f as int], op)),
    ensures plc(p, ls, f, exec_stmt(fr, Stmt::Assign(pl, rv)).0),
{
    lemma_eval_rv_plc(p, ls, f, fr, rv);
    assert(no_mut(eval_rv(fr, rv).0));
    if let Some((loc, _)) = place_loc(fr, pl) { lemma_write_loc_plc(p, ls, f, fr, loc, eval_rv(fr, rv).0); }
}

/// `SetDiscr` re-tags a value with no `Mut`, or rewrites a `Mut` local unchanged.
pub proof fn lemma_plc_setdiscr(p: Program, ls: Seq<FnLab>, f: nat, fr: Frame, pl: Place, k: usize)
    requires plc(p, ls, f, fr),
    ensures plc(p, ls, f, exec_stmt(fr, Stmt::SetDiscr(pl, k)).0),
{
    if let Some((loc, _)) = place_loc(fr, pl) {
        let o = read_loc(fr, loc);
        let w = match o { Val::Adt(_, vs) => Val::Adt(k as nat, vs), v => v };
        lemma_read_loc_mut(p, ls, f, fr, loc);
        if no_mut(o) {
            if let Val::Adt(_, vs) = o { assert forall|i: int| 0 <= i < vs.len() implies no_mut(#[trigger] vs[i]) by {} }
            lemma_write_loc_plc(p, ls, f, fr, loc, w);
        } else if let Root::Local(x) = loc.root {
            assert(loc.path =~= Seq::<PE>::empty());
            assert(write_loc(fr, loc, w).locals =~= fr.locals);
        }
    }
}

/// `ok_stmt` keeps `plc`.
pub proof fn lemma_plc_stmt(p: Program, ls: Seq<FnLab>, f: nat, fr: Frame, s: Stmt)
    requires plc(p, ls, f, fr), ok_stmt(p.fns@[f as int], ls[f as int], s),
    ensures plc(p, ls, f, exec_stmt(fr, s).0),
{
    match s {
        Stmt::Assign(pl, rv) => match rv {
            Rvalue::RefMut(q) => lemma_plc_refmut(p, ls, f, fr, pl, q),
            Rvalue::Use(Operand::Copy(q)) => if mut_pl(p.fns@[f as int], q) {
                lemma_plc_move(p, ls, f, fr, pl, q)
            } else {
                lemma_plc_assign_nm(p, ls, f, fr, pl, rv)
            },
            _ => lemma_plc_assign_nm(p, ls, f, fr, pl, rv),
        },
        Stmt::SetDiscr(pl, k) => lemma_plc_setdiscr(p, ls, f, fr, pl, k),
    }
}

// ------------------------------------------------------------------ entry frames

/// The entry frames of `args_agree` arguments agree and satisfy `plc`.
pub proof fn lemma_entry_agree(p: Program, ls: Seq<FnLab>, f: nat, a1: Seq<Val>, a2: Seq<Val>, s1: Seq<Val>, s2: Seq<Val>)
    requires f < p.fns@.len(), args_agree(p, ls, f, a1, a2, s1, s2),
    ensures ({
        let (e1, e2) = (init_entry(p, f, a1, s1), init_entry(p, f, a2, s2));
        agree(p, ls, f, e1, e2) && plc(p, ls, f, e1) && plc(p, ls, f, e2)
    }),
{
    let (b, l) = (p.fns@[f as int], ls[f as int]);
    let (e1, e2) = (init_entry(p, f, a1, s1), init_entry(p, f, a2, s2));
    assert forall|x: int| 0 <= x < e1.locals.len() implies
        val_rel(lab(l, x as nat), #[trigger] e1.locals[x], e2.locals[x])
        && (match e1.locals[x] { Val::Mut(m) => b.locals@[x] is Mut && tgt_ok(b, l, e1, m, lab(l, x as nat)), v => no_mut(v) })
        && (match e2.locals[x] { Val::Mut(m) => b.locals@[x] is Mut && tgt_ok(b, l, e2, m, lab(l, x as nat)), v => no_mut(v) })
    by {
        if 1 <= x <= b.nargs {
            let j = x - 1;
            assert((1 + j) as nat == x as nat);
            if !(b.locals@[x] is Mut) {
                assert(val_rel(lab(l, (1 + j) as nat), a1[j], a2[j]) && no_mut(a1[j]) && no_mut(a2[j]));
            } else {
                assert(slot_lab(l, j as nat) == lab(l, x as nat));
            }
        }
    }
    assert forall|j: int| 0 <= j < e1.slots.len() implies val_rel(slot_lab(l, j as nat), #[trigger] e1.slots[j], e2.slots[j]) by {
        assert(val_rel(slot_lab(l, j as nat), s1[j], s2[j]));
    }
}

// ------------------------------------------------------------------ call entry frames

/// What an operand yields under `plc`: no `Mut` unless it is `mut_op`, which reads the local.
pub proof fn lemma_eval_op_plc(p: Program, ls: Seq<FnLab>, f: nat, fr: Frame, op: Operand)
    requires plc(p, ls, f, fr), ok_op(p.fns@[f as int], ls[f as int], op),
    ensures
        !mut_op(p.fns@[f as int], op) ==> no_mut(eval_op(fr, op).0),
        mut_op(p.fns@[f as int], op) ==> eval_op(fr, op).0 == fr.locals[op->Copy_0.local as int],
{
    match op {
        Operand::Copy(pl) => lemma_place_plc(p, ls, f, fr, pl),
        Operand::Lit(c) => lemma_const_no_mut(c),
        _ => {},
    }
}

/// What arg `j` of a call evaluates to in two agreeing frames.
pub open spec fn arg_facts(p: Program, ls: Seq<FnLab>, f: nat, g: nat, args: Seq<Operand>, fr1: Frame, fr2: Frame, j: int) -> bool {
    let (b, l, gb) = (p.fns@[f as int], ls[f as int], p.fns@[g as int]);
    let (v1, v2) = (op_vals(fr1, args)[j], op_vals(fr2, args)[j]);
    let s = sec_op(b, l, args[j]);
    &&& val_rel(s, v1, v2) && shape_eq(v1, v2)
    &&& !(v1 is Mut) ==> no_mut(v1) && no_mut(v2)
    &&& v1 matches Val::Mut(m) ==> v2 == v1 && gb.locals@[1 + j] is Mut
            && tgt_ok(b, l, fr1, m, s) && tgt_ok(b, l, fr2, m, s)
}

pub proof fn lemma_arg_facts(p: Program, ls: Seq<FnLab>, f: nat, g: nat, args: Seq<Operand>, fr1: Frame, fr2: Frame, j: int)
    requires
        0 <= j < args.len(), agree(p, ls, f, fr1, fr2), plc(p, ls, f, fr1), plc(p, ls, f, fr2),
        ok_arg(p.fns@[f as int], ls[f as int], p.fns@[g as int], ls[g as int], j, args[j]),
    ensures arg_facts(p, ls, f, g, args, fr1, fr2, j),
{
    let (b, l) = (p.fns@[f as int], ls[f as int]);
    lemma_eval_op_agree(p, ls, f, fr1, fr2, args[j]);
    lemma_eval_op_plc(p, ls, f, fr1, args[j]);
    lemma_eval_op_plc(p, ls, f, fr2, args[j]);
    if mut_op(b, args[j]) {
        let x = args[j]->Copy_0.local as int;
        assert(match fr1.locals[x] { Val::Mut(m) => b.locals@[x] is Mut && tgt_ok(b, l, fr1, m, lab(l, x as nat)), v => no_mut(v) });
        assert(match fr2.locals[x] { Val::Mut(m) => b.locals@[x] is Mut && tgt_ok(b, l, fr2, m, lab(l, x as nat)), v => no_mut(v) });
    }
}

/// Under the call-site rule, the two callee frames agree and satisfy `plc` under `ls[g]`, and
/// the write-back locs and the arg events are equal.
pub proof fn lemma_call_enter_frames(p: Program, ls: Seq<FnLab>, f: nat, g: nat, args: Seq<Operand>, fr1: Frame, fr2: Frame)
    requires
        g < p.fns@.len(), args.len() == p.fns@[g as int].nargs,
        p.fns@[g as int].nargs < p.fns@[g as int].locals@.len(),
        agree(p, ls, f, fr1, fr2), plc(p, ls, f, fr1), plc(p, ls, f, fr2),
        forall|j: int| 0 <= j < args.len() ==> ok_arg(p.fns@[f as int], ls[f as int], p.fns@[g as int], ls[g as int], j, #[trigger] args[j]),
    ensures ({
        let (c1, wb1, e1) = call_enter(p, g, fr1, args);
        let (c2, wb2, e2) = call_enter(p, g, fr2, args);
        agree(p, ls, g, c1, c2) && plc(p, ls, g, c1) && plc(p, ls, g, c2) && wb1 == wb2 && e1 == e2
    }),
{
    let (b, l, gb, gl) = (p.fns@[f as int], ls[f as int], p.fns@[g as int], ls[g as int]);
    let (c1, wb1, e1) = call_enter(p, g, fr1, args);
    let (c2, wb2, e2) = call_enter(p, g, fr2, args);
    let (vs1, vs2) = (op_vals(fr1, args), op_vals(fr2, args));
    assert forall|j: int| 0 <= j < args.len() implies #[trigger] arg_facts(p, ls, f, g, args, fr1, fr2, j) by {
        lemma_arg_facts(p, ls, f, g, args, fr1, fr2, j);
    }
    assert forall|i: int| 0 <= i < c1.locals.len() implies
        val_rel(lab(gl, i as nat), #[trigger] c1.locals[i], c2.locals[i])
        && (match c1.locals[i] { Val::Mut(m) => gb.locals@[i] is Mut && tgt_ok(gb, gl, c1, m, lab(gl, i as nat)), v => no_mut(v) })
        && (match c2.locals[i] { Val::Mut(m) => gb.locals@[i] is Mut && tgt_ok(gb, gl, c2, m, lab(gl, i as nat)), v => no_mut(v) })
    by {
        if 1 <= i <= vs1.len() {
            let j = i - 1;
            assert(arg_facts(p, ls, f, g, args, fr1, fr2, j) && ok_arg(b, l, gb, gl, j, args[j]));
            assert((1 + j) as nat == i as nat);
            if !(vs1[j] is Mut) { lemma_rel_shape(sec_op(b, l, args[j]), vs1[j], vs2[j]); }
        }
    }
    assert forall|j: int| 0 <= j < c1.slots.len() implies
        val_rel(slot_lab(gl, j as nat), #[trigger] c1.slots[j], c2.slots[j]) && no_mut(c1.slots[j]) && no_mut(c2.slots[j])
    by {
        assert(arg_facts(p, ls, f, g, args, fr1, fr2, j) && ok_arg(b, l, gb, gl, j, args[j]));
        if let Val::Mut(m) = vs1[j] {
            lemma_read_loc_agree(p, ls, f, fr1, fr2, m);
            lemma_wr_read(p, ls, f, fr1, Cur::L(m));
            lemma_wr_read(p, ls, f, fr2, Cur::L(m));
        }
    }
    assert forall|j: int| 0 <= j < wb1.len() implies #[trigger] wb1[j] == wb2[j] by { assert(arg_facts(p, ls, f, g, args, fr1, fr2, j)); }
    assert(wb1 =~= wb2);
    assert forall|i: int| 0 <= i < args.len() implies ok_op(b, l, #[trigger] args[i]) by { assert(ok_arg(b, l, gb, gl, i, args[i])); }
    lemma_ops_ev_agree(p, ls, f, fr1, fr2, args);
    assert(agree(p, ls, g, c1, c2));
    assert(plc(p, ls, g, c1));
    assert(plc(p, ls, g, c2));
    assert(wb1 == wb2);
}

} // verus!
