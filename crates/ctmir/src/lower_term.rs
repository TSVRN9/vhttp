//! The translator's terminators (verified against `rel::lowers_term`): jumps, switches, asserts,
//! drops through their glue and calls through `calls`. The fn order is fixed before bodies are
//! lowered (`lower_fn::closure_order`), so a callee's core fn is a lookup in it.
use crate::json::bytes_eq;
use crate::look::*;
use crate::lower::*;
use crate::lower_const::*;
use crate::mir::*;
use crate::policy::*;
#[cfg(verus_keep_ghost)]
use crate::rel::*;
#[cfg(verus_keep_ghost)]
use crate::sem::*;
use crate::sem::StdFn;
use ctcore::syntax as c;
use vstd::prelude::*;

verus! {

/// The keys bound so far: key, def, the instance for an internal fn or root (`None` for a leaf).
pub type Keys = Vec<(Vec<u8>, DefId, Option<usize>)>;

/// Binds `key` to `(def, inst)`; `false` when it names something else already (`ct_key` drops
/// generic args, so distinct fns can share one).
pub fn bind(keys: &mut Keys, key: &[u8], def: DefId, inst: Option<usize>) -> bool {
    let mut k: usize = 0;
    while k < keys.len()
        invariant k <= keys@.len(),
        decreases keys.len() - k,
    {
        if bytes_eq(keys[k].0.as_slice(), key) { return keys[k].1 == def && keys[k].2 == inst; }
        k += 1;
    }
    keys.push((msg(key), def, inst));
    true
}

/// The core fn of `insts[j]` in the fixed order.
pub fn fn_index(order: &Vec<usize>, j: usize) -> (r: Option<usize>)
    ensures r matches Some(h) ==> fn_of(order@, h, j as nat),
{
    let mut g: usize = 0;
    while g < order.len()
        invariant g <= order@.len(),
        decreases order.len() - g,
    {
        if order[g] == j { return Some(g); }
        g += 1;
    }
    None
}

pub proof fn lemma_ord_set(ord: Seq<usize>, h: usize, j: nat)
    requires fn_of(ord, h, j),
    ensures ord_set(ord).contains(j),
{
    let w = ord.map_values(|x: usize| x as nat);
    w.to_set_ensures();
    assert(w[h as int] == j);
}

/// A callee entered as a core fn: an `Item` with a body, in the dump's crate or a policy crate.
pub fn is_internal(m: &MirCrate, pol: &Policy, j: usize) -> (r: bool)
    ensures r == internal(*m, *pol, j as nat),
{
    if j >= m.insts.len() { return false; }
    let x = &m.insts[j];
    matches!(x.kind, InstanceKind::Item) && x.body.is_some()
        && (bytes_eq(x.krate.as_slice(), m.crate_name.as_slice()) || has_exec(&pol.internal_crates, x.krate.as_slice())
            || has_exec(&pol.translate_crates, x.krate.as_slice()))
}

pub fn x_intr_of(m: &MirCrate, pol: &Policy, key: &[u8], g: &GenericArgs) -> (r: Option<c::Intrinsic>)
    ensures r == intr_of(*m, cpol(*pol), key@, *g),
{
    proof { lemma_set_of(pol.declassify@, key@); lemma_set_of(pol.ghost_unit@, key@); }
    if has_exec(&pol.declassify, key) { return Some(c::Intrinsic::Declassify); }
    if has_exec(&pol.ghost_unit, key) { return Some(c::Intrinsic::GhostUnit); }
    match x_std_model(m, key, g) {
        Some(f) => Some(match f {
            StdFn::VecNew => c::Intrinsic::VecNew,
            StdFn::VecWithCapacity => c::Intrinsic::VecWithCapacity,
            StdFn::VecPush => c::Intrinsic::VecPush,
            StdFn::VecExtendFromSlice => c::Intrinsic::VecExtendFromSlice,
            StdFn::VecAsSlice => c::Intrinsic::VecAsSlice,
            StdFn::ArrayAsSlice => c::Intrinsic::ArrayAsSlice,
            StdFn::VecLen => c::Intrinsic::VecLen,
            StdFn::VecSet => c::Intrinsic::VecSet,
            StdFn::VecIndex => c::Intrinsic::VecIndex,
            StdFn::SliceSubrange => c::Intrinsic::SliceSubrange,
            StdFn::SliceToVec => c::Intrinsic::SliceToVec,
            StdFn::Wrapping(op, it) => c::Intrinsic::Wrapping(op, it),
            StdFn::GhostNew => c::Intrinsic::GhostUnit,
        }),
        None => None,
    }
}

/// `leaf_ok`: arity, and a ghost result's type.
pub fn x_leaf_ok(m: &MirCrate, pol: &Policy, key: &[u8], g: &GenericArgs, n: usize, dty: Option<Ty>) -> (r: bool)
    ensures r ==> leaf_ok(*m, cpol(*pol), key@, *g, n as nat, dty),
{
    proof { lemma_set_of(pol.declassify@, key@); lemma_set_of(pol.ghost_unit@, key@); }
    let ghost_dest = match dty { Some(t) => x_zst_dest(m, t), None => false };
    if has_exec(&pol.declassify, key) { return n == 1; }
    if has_exec(&pol.ghost_unit, key) { return ghost_dest; }
    match x_std_model(m, key, g) {
        Some(f) => match f {
            StdFn::VecNew => n == 0,
            StdFn::VecWithCapacity | StdFn::VecAsSlice | StdFn::ArrayAsSlice | StdFn::VecLen | StdFn::SliceToVec => n == 1,
            StdFn::VecPush | StdFn::VecExtendFromSlice | StdFn::VecIndex | StdFn::Wrapping(_, _) => n == 2,
            StdFn::VecSet | StdFn::SliceSubrange => n == 3,
            StdFn::GhostNew => ghost_dest,
        },
        None => false,
    }
}

/// A fresh temp of type `ty` with no assignment (a drop glue call's unit destination).
pub fn fresh_local(tmp: &mut Tmp, ty: c::Ty) -> (r: Result<usize, Vec<u8>>)
    ensures r matches Ok(y) ==> y as nat == tbase(*old(tmp)) && final(tmp).nloc == old(tmp).nloc && final(tmp).pre@ == old(tmp).pre@
        && final(tmp).tys@.len() == old(tmp).tys@.len() + 1,
{
    if tmp.tys.len() >= usize::MAX - tmp.nloc { return Err(msg(b"too many temps")); }
    let local = tmp.nloc + tmp.tys.len();
    tmp.tys.push(ty);
    Ok(local)
}

/// The postcondition every terminator lowering shares (its temps are all of `t1.pre`).
pub open spec fn term_post(m: MirCrate, pol: Policy, ord: Seq<usize>, b: Body, t: TerminatorKind, ct: c::Term, t0: Tmp, t1: Tmp) -> bool {
    &&& grew2(t0, t1) && term_ok(m, cpol(pol), b, t) && callees_in(m, cpol(pol), b, t, ord_set(ord))
    &&& lowers_term(m, pol, ord, b, b.locals@.len(), tbase(t1), t, t1.pre@, ct)
}

pub struct Site { pub path: Vec<u8>, pub site: Vec<u8> }

pub fn uns(s: &Site, what: Vec<u8>) -> Reject {
    Reject::Unsupported { path: copy_bytes(&s.path), what, site: copy_bytes(&s.site) }
}

/// A terminator, and whether it is a declassify call.
pub fn lower_term(m: &MirCrate, pol: &Policy, order: &Vec<usize>, keys: &mut Keys, b: &Body, tmp: &mut Tmp, s: &Site, t: &Terminator)
    -> (r: Result<(c::Term, bool), Reject>)
    requires old(tmp).nloc == b.locals@.len(), old(tmp).pre@.len() == 0,
    ensures r matches Ok((ct, _)) ==> term_post(*m, *pol, order@, *b, t.kind, ct, *old(tmp), *final(tmp)),
{
    proof { lemma_no_temps(*tmp); }
    let ghost t0 = *tmp;
    let ghost nloc = b.locals@.len();
    match &t.kind {
        TerminatorKind::Goto { target } => {
            let ct = c::Term::Goto(*target);
            proof { assert(lowers_term_at(*m, *pol, order@, *b, nloc, tbase(*tmp), t.kind, tmp.pre@, ct, tbase(t0))); }
            Ok((ct, false))
        },
        TerminatorKind::SwitchInt { discr, targets } => {
            let (op, _) = match lower_int_op(m, b, discr, tmp) { Ok(x) => x, Err(e) => return Err(uns(s, e)) };
            let mut brs: Vec<(u128, usize)> = Vec::new();
            let mut k: usize = 0;
            while k < targets.branches.len()
                invariant k <= targets.branches@.len(), brs@ == targets.branches@.subrange(0, k as int),
                decreases targets.branches.len() - k,
            {
                brs.push(targets.branches[k]);
                proof { assert(brs@ =~= targets.branches@.subrange(0, k + 1)); }
                k += 1;
            }
            let ct = c::Term::Switch(op, brs, targets.otherwise);
            proof {
                assert(brs@ =~= targets.branches@);
                assert(seg(*old(tmp), *tmp) =~= tmp.pre@);
                assert(lowers_term_at(*m, *pol, order@, *b, nloc, tbase(*tmp), t.kind, tmp.pre@, ct, tbase(t0)));
            }
            Ok((ct, false))
        },
        TerminatorKind::Assert { cond, expected, msg: _, target, unwind: _ } => {
            let (op, _) = match lower_int_op(m, b, cond, tmp) { Ok(x) => x, Err(e) => return Err(uns(s, e)) };
            let ct = c::Term::Assert(op, *expected, *target);
            proof {
                assert(seg(*old(tmp), *tmp) =~= tmp.pre@);
                assert(lowers_term_at(*m, *pol, order@, *b, nloc, tbase(*tmp), t.kind, tmp.pre@, ct, tbase(t0)));
            }
            Ok((ct, false))
        },
        TerminatorKind::Return => {
            let ct = c::Term::Return;
            proof { assert(lowers_term_at(*m, *pol, order@, *b, nloc, tbase(*tmp), t.kind, tmp.pre@, ct, tbase(t0))); }
            Ok((ct, false))
        },
        TerminatorKind::Unreachable => {
            let ct = c::Term::Abort;
            proof { assert(lowers_term_at(*m, *pol, order@, *b, nloc, tbase(*tmp), t.kind, tmp.pre@, ct, tbase(t0))); }
            Ok((ct, false))
        },
        TerminatorKind::Drop { place: _, target: _, unwind: _ } => lower_drop(m, pol, order, b, tmp, s, t),
        TerminatorKind::Call { func: _, args: _, destination: _, target, unwind: _ } => {
            if target.is_none() { return Err(uns(s, msg(b"a diverging call"))); }
            lower_call(m, pol, order, keys, b, tmp, s, t)
        },
        _ => Err(uns(s, msg(b"terminator outside the subset (Resume, Abort, InlineAsm, ..)"))),
    }
}

/// `Drop` through its `drops` row: an empty shim or the `Vec<int>` leaf is a `Goto`; any other
/// glue is a `Call` of the glue fn on a fresh `&mut place` temp, into a fresh `Unit` temp.
#[allow(unused_variables)] // `pol` is the relation's
pub fn lower_drop(m: &MirCrate, pol: &Policy, order: &Vec<usize>, b: &Body, tmp: &mut Tmp, s: &Site, t: &Terminator) -> (r: Result<(c::Term, bool), Reject>)
    requires old(tmp).nloc == b.locals@.len(), old(tmp).pre@.len() == 0, t.kind is Drop,
    ensures r matches Ok((ct, _)) ==> term_post(*m, *pol, order@, *b, t.kind, ct, *old(tmp), *final(tmp)),
{
    let (place, target) = match &t.kind { TerminatorKind::Drop { place, target, unwind: _ } => (place, *target), _ => return Err(uns(s, msg(b"?"))) };
    let ty = match x_place_ty(m, b, place) { Some(t) => t, None => return Err(uns(s, msg(b"drop place type"))) };
    let cp = match lower_place(m, b, place, true) { Ok(p) => p, Err(e) => return Err(uns(s, e)) };
    let mut k: usize = 0;
    while k < place.projection.len()
        invariant k <= place.projection@.len(), forall|i: int| 0 <= i < k ==> !(#[trigger] place.projection@[i] is Index),
        decreases place.projection.len() - k,
    {
        if matches!(place.projection[k], ProjectionElem::Index(_)) { return Err(uns(s, msg(b"a drop of an indexed place"))); }
        k += 1;
    }
    let d = match x_drop_row(m, ty) { Some(d) => d, None => return Err(uns(s, msg(b"a drop with no drops row"))) };
    if d.empty || x_vec_int(m, ty) {
        proof { lemma_no_temps(*tmp); lemma_drop_goto(*m, *pol, order@, *b, t.kind, cp, *tmp, ty, *d); }
        return Ok((c::Term::Goto(target), false));
    }
    let j = match x_inst_idx(m, d.glue) { Some(j) => j, None => return Err(uns(s, msg(b"drop glue with no insts row"))) };
    let gb = match x_inst_body(m, j) { Some(gb) => gb, None => return Err(uns(s, msg(b"drop glue without a body"))) };
    if !glue_ok(m, gb, ty) { return Err(uns(s, msg(b"drop glue without a body of one &mut parameter"))); }
    let h = match fn_index(order, j) { Some(h) => h, None => return Err(uns(s, msg(b"drop glue outside the closure"))) };
    let ct = match lower_ty(m, ty, TYF) { Ok(ct) => ct, Err(e) => return Err(uns(s, e)) };
    let ghost t0 = *tmp;
    let x = match fresh(tmp, c::Ty::Mut(Box::new(ct)), c::Rvalue::RefMut(cp)) { Ok(x) => x, Err(e) => return Err(uns(s, e)) };
    let y = match fresh_local(tmp, c::Ty::Unit) { Ok(y) => y, Err(e) => return Err(uns(s, e)) };
    let mut args: Vec<c::Operand> = Vec::new();
    args.push(c::Operand::Copy(pl(x)));
    let term = c::Term::Call(c::Callee::Fn(h), args, pl(y), target);
    proof {
        lemma_ord_set(order@, h, j as nat);
        assert(tmp.pre@.len() == 1 && tmp.pre@[0] == tmp.pre@.last());
        lemma_drop_glue(*m, *pol, order@, *b, t.kind, t0, *tmp, j as nat, term, ty, *d, *gb);
    }
    Ok((term, false))
}

proof fn lemma_drop_goto(m: MirCrate, pol: Policy, ord: Seq<usize>, b: Body, t: TerminatorKind, cp: c::Place, t1: Tmp, ty: Ty, d: DropRow)
    requires t is Drop, t1.pre@.len() == 0, t1.nloc == b.locals@.len(), grew2(t1, t1),
        place_ty(m, b, t->Drop_place) == Some(ty), drop_row(m, ty) == Some(d), d.empty || vec_int(m, ty),
        no_index(t->Drop_place), lowers_place(m, b, t->Drop_place, cp, true),
    ensures term_post(m, pol, ord, b, t, c::Term::Goto(t->Drop_target), t1, t1),
{
    assert(lowers_term_at(m, pol, ord, b, b.locals@.len(), tbase(t1), t, t1.pre@, c::Term::Goto(t->Drop_target), tbase(t1)));
}

proof fn lemma_drop_glue(m: MirCrate, pol: Policy, ord: Seq<usize>, b: Body, t: TerminatorKind, t0: Tmp, t2: Tmp, j: nat, ct: c::Term,
    ty: Ty, d: DropRow, gb: Body)
    requires
        t is Drop, t0.pre@.len() == 0, t0.nloc == b.locals@.len(),
        place_ty(m, b, t->Drop_place) == Some(ty), drop_row(m, ty) == Some(d), !(d.empty || vec_int(m, ty)),
        glue_of(m, d.glue) == Some((j, gb)), gb.arg_count == 1, sig_ok(m, gb), is_mut_ref(m, gb.locals@[1].ty), glue_param_is(m, gb, ty),
        no_index(t->Drop_place), ord_set(ord).contains(j),
        t2.nloc == t0.nloc, t2.pre@.len() == 1, t2.tys@.len() == t0.tys@.len() + 2,
        t2.pre@[0] is Assign && t2.pre@[0]->Assign_0.local == tbase(t0) && t2.pre@[0]->Assign_0.proj@.len() == 0,
        t2.pre@[0]->Assign_1 is RefMut && lowers_place(m, b, t->Drop_place, t2.pre@[0]->Assign_1->RefMut_0, true),
        ct is Call && ct->Call_0 is Fn && fn_of(ord, ct->Call_0->Fn_0, j) && ct->Call_3 == t->Drop_target,
        ct->Call_1@.len() == 1 && is_tmp(ct->Call_1@[0], tbase(t0)),
        ct->Call_2.proj@.len() == 0 && ct->Call_2.local == tbase(t0) + 1,
    ensures term_post(m, pol, ord, b, t, ct, t0, t2),
{
    assert(t2.pre@.subrange(0, 0) =~= t0.pre@);
    assert(lowers_drop(m, ord, b, b.locals@.len(), tbase(t2), t->Drop_place, t->Drop_target, t2.pre@, ct));
    assert(lowers_term_at(m, pol, ord, b, b.locals@.len(), tbase(t2), t, t2.pre@, ct, tbase(t0)));
}

pub fn lower_call(m: &MirCrate, pol: &Policy, order: &Vec<usize>, keys: &mut Keys, b: &Body, tmp: &mut Tmp, s: &Site, t: &Terminator)
    -> (r: Result<(c::Term, bool), Reject>)
    requires old(tmp).nloc == b.locals@.len(), old(tmp).pre@.len() == 0, t.kind is Call, t.kind->Call_target is Some,
    ensures r matches Ok((ct, _)) ==> term_post(*m, *pol, order@, *b, t.kind, ct, *old(tmp), *final(tmp)),
{
    let (func, args, dest, tb) = match &t.kind {
        TerminatorKind::Call { func, args, destination, target: Some(tb), unwind: _ } => (func, args, destination, *tb),
        _ => return Err(uns(s, msg(b"?"))),
    };
    let fty = match func {
        Operand::Constant(k) => k.const_.ty,
        _ => return Err(uns(s, msg(b"a call through a fn pointer or closure value"))),
    };
    let (j, k) = match x_callee_of(m, func) {
        Some(x) => x,
        None => {
            let callee = match x_call_row(m, fty) { Some(k) => copy_bytes(&m.calls[k].def_name), None => msg(b"?") };
            return Err(Reject::Unresolved { path: copy_bytes(&s.path), callee, site: copy_bytes(&s.site) });
        },
    };
    if j >= m.insts.len() { return Err(uns(s, msg(b"?"))); }
    let key = m.insts[j].key.as_slice();
    let ga = &m.calls[k].args;
    let leaf = x_is_leaf(m, pol, key, ga);
    let internal = !leaf && is_internal(m, pol, j);
    if !bind(keys, key, m.insts[j].def, if internal { Some(j) } else { None }) {
        let mut w = msg(b"ambiguous key ");
        let mut i: usize = 0;
        while i < key.len()
            invariant i <= key@.len(),
            decreases key.len() - i,
        {
            w.push(key[i]);
            i += 1;
        }
        return Err(uns(s, w));
    }
    let ghost t0 = *tmp;
    if leaf {
        if !x_leaf_ok(m, pol, key, ga, args.len(), x_place_ty(m, b, dest)) {
            return Err(uns(s, msg(b"a std or policy call at an unexpected arity or result type")));
        }
        let kk = match x_intr_of(m, pol, key, ga) { Some(kk) => kk, None => return Err(uns(s, msg(b"a leaf without an intrinsic"))) };
        let declass = matches!(kk, c::Intrinsic::Declassify);
        let ops = match lower_ops(m, b, args, tmp) { Ok(o) => o, Err(e) => return Err(uns(s, e)) };
        let dst = match lower_place(m, b, dest, true) { Ok(p) => p, Err(e) => return Err(uns(s, e)) };
        let ct = c::Term::Call(c::Callee::Intr(kk), ops, dst, tb);
        proof { lemma_call_post(*m, *pol, order@, *b, t.kind, ct, t0, *tmp, j as nat); }
        return Ok((ct, declass));
    }
    if internal {
        match callee_ok(m, b, args, j) {
            0 => {},
            1 => return Err(uns(s, msg(b"a call to a closure (rust-call body)"))),
            // a closure called through `Fn::call` takes its arguments tupled (rust-call)
            2 => return Err(uns(s, msg(b"a call whose argument types are not the callee's parameter types (a closure call)"))),
            _ => return Err(uns(s, msg(b"a call to a fn whose signature is outside the subset"))),
        }
        let h = match fn_index(order, j) { Some(h) => h, None => return Err(uns(s, msg(b"a callee outside the closure"))) };
        let ops = match lower_ops(m, b, args, tmp) { Ok(o) => o, Err(e) => return Err(uns(s, e)) };
        let dst = match lower_place(m, b, dest, true) { Ok(p) => p, Err(e) => return Err(uns(s, e)) };
        let ct = c::Term::Call(c::Callee::Fn(h), ops, dst, tb);
        proof { lemma_ord_set(order@, h, j as nat); lemma_call_post(*m, *pol, order@, *b, t.kind, ct, t0, *tmp, j as nat); }
        return Ok((ct, false));
    }
    if std_key(key) { return Err(uns(s, msg(b"a std fn at generic args the std model does not admit"))); }
    Err(Reject::Unresolved { path: copy_bytes(&s.path), callee: msg(key), site: copy_bytes(&s.site) })
}

proof fn lemma_call_post(m: MirCrate, pol: Policy, ord: Seq<usize>, b: Body, t: TerminatorKind, ct: c::Term, t0: Tmp, t2: Tmp, j: nat)
    requires
        t is Call, t->Call_target is Some, t0.pre@.len() == 0, t0.nloc == b.locals@.len(),
        callee_of(m, t->Call_func) matches Some((jj, g)) && jj == j && j < m.insts@.len() && {
            let key = m.insts@[j as int].key@;
            &&& ct is Call && ct->Call_3 == t->Call_target->Some_0
            &&& lowers_place(m, b, t->Call_destination, ct->Call_2, true)
            &&& grew(t0, t2) && lowers_ops(m, b, t->Call_args@, ct->Call_1@, seg(t0, t2), tbase(t0)) && ops_ok(m, b, t->Call_args@)
            &&& if is_leaf(m, cpol(pol), key, g) {
                ct->Call_0 is Intr && intr_of(m, cpol(pol), key, g) == Some(ct->Call_0->Intr_0)
                && leaf_ok(m, cpol(pol), key, g, t->Call_args@.len(), place_ty(m, b, t->Call_destination))
            } else {
                ct->Call_0 is Fn && fn_of(ord, ct->Call_0->Fn_0, j) && internal(m, pol, j) && ord_set(ord).contains(j)
                && inst_body(m, j) is Some && t->Call_args@.len() == inst_body(m, j)->Some_0.arg_count && sig_ok(m, inst_body(m, j)->Some_0)
                && args_typed(m, b, t->Call_args@, inst_body(m, j)->Some_0)
            }
        },
    ensures term_post(m, pol, ord, b, t, ct, t0, t2),
{
    hide(lowers_ops);
    hide(ops_ok);
    hide(leaf_ok);
    hide(sig_ok);
    assert(seg(t0, t2) =~= t2.pre@);
    assert(lowers_term_at(m, pol, ord, b, b.locals@.len(), tbase(t2), t, t2.pre@, ct, tbase(t0)));
}

/// Drop glue the translator calls: one `&mut T` parameter, `T` the dropped type.
pub fn glue_ok(m: &MirCrate, gb: &Body, ty: Ty) -> (r: bool)
    ensures r ==> gb.arg_count == 1 && gb.locals@.len() > 1 && sig_ok(*m, *gb) && is_mut_ref(*m, gb.locals@[1].ty) && glue_param_is(*m, *gb, ty),
{
    gb.arg_count == 1 && gb.locals.len() > 1 && x_sig_ok(m, gb) && x_is_mut_ref(m, gb.locals[1].ty)
        && matches!(x_rigid(m, gb.locals[1].ty), Some(RigidTy::Ref(_, pt, _)) if *pt == ty)
}

/// A body call the translator makes: 0 when the callee's body takes these arguments (1: a
/// rust-call body, 2: argument types differ from the parameters', 3: no body or signature).
pub fn callee_ok(m: &MirCrate, b: &Body, args: &Vec<Operand>, j: usize) -> (r: u8)
    ensures r == 0 ==> (inst_body(*m, j as nat) matches Some(cb) && args@.len() == cb.arg_count && sig_ok(*m, cb) && args_typed(*m, *b, args@, cb)),
{
    match x_inst_body(m, j) {
        Some(cb) => if cb.spread_arg.is_some() { 1 } else if !(args.len() == cb.arg_count && x_sig_ok(m, cb)) { 3 }
            else if !args_match(m, b, args, cb) { 2 } else { 0 },
        None => 3,
    }
}

/// Each argument's type is the callee's parameter type (ids are interned types).
pub fn args_match(m: &MirCrate, b: &Body, args: &Vec<Operand>, cb: &Body) -> (r: bool)
    ensures r ==> args_typed(*m, *b, args@, *cb),
{
    if args.len() >= cb.locals.len() { return false; }
    let mut k: usize = 0;
    while k < args.len()
        invariant k <= args@.len(), args@.len() < cb.locals@.len(),
            forall|i: int| 0 <= i < k ==> op_ty(*m, *b, #[trigger] args@[i]) == Some(cb.locals@[i + 1].ty),
        decreases args.len() - k,
    {
        match x_op_ty(m, b, &args[k]) { Some(t) => if t != cb.locals[k + 1].ty { return false; }, None => return false }
        k += 1;
    }
    true
}

} // verus!
