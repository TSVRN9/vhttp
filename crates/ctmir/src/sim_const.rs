//! The simulation, constants: a constant's core image (its temps `pre`, then the operand `y`)
//! computes a value agreeing with `const_val` (decision 5), with no events, changing only its
//! temps. By induction on the decoder's fuel, mirroring `lowers_cv`/`adt_img`/`zref_img`/`ul_img`.
#[allow(unused_imports)]
use crate::mir::*;
#[allow(unused_imports)]
use crate::rel::*;
#[allow(unused_imports)]
use crate::sem::*;
#[allow(unused_imports)]
use crate::sim::*;
#[allow(unused_imports)]
use crate::sim_exec::*;
#[allow(unused_imports)]
use ctcore::sem::{Event, Frame, Val};
#[allow(unused_imports)]
use ctcore::syntax as c;
use vstd::prelude::*;

verus! {

/// A type's unit-like value is unit-shaped.
pub proof fn lemma_ul_us(m: MirCrate, t: Ty, fuel: nat, clos: bool)
    ensures unit_like(m, t, fuel, clos) matches Some((v, _)) ==> us(v),
    decreases fuel, 0nat,
{
    if fuel > 0 {
        let f = (fuel - 1) as nat;
        match rigid(m, t) {
            Some(RigidTy::Tuple(ts)) => lemma_uls_us(m, ts@, f, ts@.len(), clos),
            Some(RigidTy::Adt(_, _)) => if let Some(a) = adt_row(m, t) {
                lemma_uls_us(m, a.variants@[0].fields@, f, a.variants@[0].fields@.len(), clos);
            },
            Some(RigidTy::Array(e, _)) => {
                lemma_ul_us(m, e, f, clos);
                if let Some((v, _)) = unit_like(m, t, fuel, clos) {
                    if let Val::Arr(vs) = v {
                        assert forall|i: int| 0 <= i < vs.len() implies us(#[trigger] vs[i]) by {}
                    }
                }
            },
            _ => {},
        }
    }
}

pub proof fn lemma_uls_us(m: MirCrate, ts: Seq<Ty>, fuel: nat, n: nat, clos: bool)
    ensures unit_likes(m, ts, fuel, n, clos) matches Some((vs, _)) ==> vs.len() == n && forall|i: int| 0 <= i < vs.len() ==> us(#[trigger] vs[i]),
    decreases fuel, n + 1,
{
    if n > 0 && n <= ts.len() {
        lemma_uls_us(m, ts, fuel, (n - 1) as nat, clos);
        lemma_ul_us(m, ts[n - 1], fuel, clos);
    }
}

/// `dec_fields`, field by field.
pub proof fn lemma_dec_fields_at(m: MirCrate, ts: Seq<Ty>, os: Seq<MachineSize>, a: Allocation, base: nat, fuel: nat, n: nat)
    requires dec_fields(m, ts, os, a, base, fuel, n) is Some,
    ensures
        dec_fields(m, ts, os, a, base, fuel, n)->Some_0.0.len() == n, n <= ts.len(), n <= os.len(),
        forall|i: nat| i < n ==> {
            &&& dec_fields(m, ts, os, a, base, fuel, i) is Some
            &&& #[trigger] dec(m, ts[i as int], a, (base + os[i as int].num_bits / 8) as nat, fuel) is Some
            &&& dec_fields(m, ts, os, a, base, fuel, n)->Some_0.0[i as int] == dec(m, ts[i as int], a, (base + os[i as int].num_bits / 8) as nat, fuel)->Some_0.0
            &&& fcount(m, ts, os, a, base, fuel, i + 1) == fcount(m, ts, os, a, base, fuel, i) + dec(m, ts[i as int], a, (base + os[i as int].num_bits / 8) as nat, fuel)->Some_0.1
        },
    decreases n,
{
    if n > 0 {
        let k = (n - 1) as nat;
        lemma_dec_fields_at(m, ts, os, a, base, fuel, k);
        let vs = dec_fields(m, ts, os, a, base, fuel, k)->Some_0.0;
        assert forall|i: nat| i < n implies {
            &&& dec_fields(m, ts, os, a, base, fuel, i) is Some
            &&& #[trigger] dec(m, ts[i as int], a, (base + os[i as int].num_bits / 8) as nat, fuel) is Some
            &&& dec_fields(m, ts, os, a, base, fuel, n)->Some_0.0[i as int] == dec(m, ts[i as int], a, (base + os[i as int].num_bits / 8) as nat, fuel)->Some_0.0
            &&& fcount(m, ts, os, a, base, fuel, i + 1) == fcount(m, ts, os, a, base, fuel, i) + dec(m, ts[i as int], a, (base + os[i as int].num_bits / 8) as nat, fuel)->Some_0.1
        } by {
            if i < k { assert(vs.push(dec(m, ts[k as int], a, (base + os[k as int].num_bits / 8) as nat, fuel)->Some_0.0)[i as int] == vs[i as int]); }
        }
    }
}

/// `unit_likes`, field by field.
pub proof fn lemma_uls_at(m: MirCrate, ts: Seq<Ty>, fuel: nat, n: nat)
    requires unit_likes(m, ts, fuel, n, true) is Some,
    ensures
        unit_likes(m, ts, fuel, n, true)->Some_0.0.len() == n, n <= ts.len(),
        forall|i: nat| i < n ==> {
            &&& #[trigger] unit_like(m, ts[i as int], fuel, true) is Some
            &&& unit_likes(m, ts, fuel, n, true)->Some_0.0[i as int] == unit_like(m, ts[i as int], fuel, true)->Some_0.0
            &&& ucount(m, ts, fuel, i + 1) == ucount(m, ts, fuel, i) + unit_like(m, ts[i as int], fuel, true)->Some_0.1
            &&& unit_likes(m, ts, fuel, i, true) is Some
        },
    decreases n,
{
    if n > 0 {
        let k = (n - 1) as nat;
        lemma_uls_at(m, ts, fuel, k);
        let vs = unit_likes(m, ts, fuel, k, true)->Some_0.0;
        assert forall|i: nat| i < n implies {
            &&& #[trigger] unit_like(m, ts[i as int], fuel, true) is Some
            &&& unit_likes(m, ts, fuel, n, true)->Some_0.0[i as int] == unit_like(m, ts[i as int], fuel, true)->Some_0.0
            &&& ucount(m, ts, fuel, i + 1) == ucount(m, ts, fuel, i) + unit_like(m, ts[i as int], fuel, true)->Some_0.1
            &&& unit_likes(m, ts, fuel, i, true) is Some
        } by {
            if i < k { assert(vs.push(unit_like(m, ts[k as int], fuel, true)->Some_0.0)[i as int] == vs[i as int]); }
        }
    }
}

/// An image with no temps: its operand's value.
proof fn lemma_no_pre(pre: Seq<c::Stmt>, base: nat, y: c::Operand, v: Val, fc0: Frame)
    requires pre.len() == 0, !(y is Copy), vr(v, ctcore::sem::eval_op(fc0, y).0), ctcore::sem::eval_op(fc0, y).1 == Seq::<Event>::empty(),
    ensures img_ok(pre, base, y, v, fc0),
{
}

/// A literal image (decoder fuel `fuel`).
pub proof fn lemma_lit(m: MirCrate, t: Ty, a: Allocation, off: nat, fuel: nat, y: c::Operand, pre: Seq<c::Stmt>, base: nat, fc0: Frame)
    requires lit_img(m, t, a, off, fuel, y), pre.len() == 0,
    ensures img_ok(pre, base, y, dec(m, t, a, off, fuel)->Some_0.0, fc0),
{
    let v = dec(m, t, a, off, fuel)->Some_0.0;
    if y is Lit && !(core_cv(y->Lit_0) == v) {
        assert(us(v));
    } else if y is Lit {
        lemma_vr_refl(v);
    }
}

/// One temp assigned at `base + c` after `pre[0..c]`: the image's result.
proof fn lemma_last_tmp(pre: Seq<c::Stmt>, base: nat, cnt: nat, y: c::Operand, fc0: Frame)
    requires pre.len() == cnt + 1, temps_at(pre, base), is_tmp(y, base + cnt), fc0.locals.len() >= base + pre.len(),
    ensures ({
        let (g, e) = xs(pre, 0, cnt as int, fc0);
        let (fc1, e2) = ctcore::sem::exec_stmts(pre, 0, fc0);
        let r = ctcore::sem::eval_rv(g, pre[cnt as int]->Assign_1);
        &&& fc1 == Frame { locals: g.locals.update((base + cnt) as int, r.0), slots: g.slots }
        &&& e2 == e + r.1
        &&& ctcore::sem::eval_op(fc1, y) == (r.0, Seq::<Event>::empty())
        &&& g.locals.len() == fc0.locals.len() && fc1.locals.len() == fc0.locals.len()
    }),
{
    lemma_xs_all(pre, fc0);
    lemma_xs_split(pre, 0, cnt as int, (cnt + 1) as int, fc0);
    let (g, e) = xs(pre, 0, cnt as int, fc0);
    lemma_xs_one(pre, cnt as int, g);
    lemma_xs_len(pre, 0, cnt as int, fc0);
    lemma_tmp_assign(g, pre[cnt as int], base + cnt);
    let (fc1, _) = ctcore::sem::exec_stmts(pre, 0, fc0);
    lemma_eval_tmp(fc1, y, base + cnt);
}

/// The ops of an aggregate temp at `base + cnt`, each reading earlier temps: its frame and value.
proof fn lemma_agg_tmp(pre: Seq<c::Stmt>, base: nat, cnt: nat, y: c::Operand, fc0: Frame, ops: Seq<c::Operand>, kv: nat,
    cntf: spec_fn(nat) -> nat, valf: spec_fn(nat) -> Val, n: nat, vs: Seq<Val>)
    requires
        pre.len() == cnt + 1, temps_at(pre, base), is_tmp(y, base + cnt), fc0.locals.len() >= base + pre.len(),
        tmp_rv(pre, cnt as int) == c::Rvalue::Aggregate(c::AggKind::Adt(kv as usize), tmp_rv(pre, cnt as int)->Aggregate_1),
        tmp_rv(pre, cnt as int)->Aggregate_1@ == ops, ops.len() == n, vs.len() == n, kv as usize as nat == kv,
        cntf(n) == cnt, forall|i: nat| i < n ==> #[trigger] cntf(i) <= cntf(i + 1),
        forall|i: nat| i < n ==> #[trigger] vs[i as int] == valf(i),
        ({
            let (g, e) = xs(pre, 0, cnt as int, fc0);
            &&& e == Seq::<Event>::empty()
            &&& same_out(fc0, g, base, base + cnt)
            &&& forall|i: nat| i < n ==> dep(ops[i as int], base + cntf(i), base + cntf(i + 1))
                && vr(valf(i), ctcore::sem::eval_op(g, #[trigger] ops[i as int]).0) && ctcore::sem::eval_op(g, ops[i as int]).1 == Seq::<Event>::empty()
        }),
    ensures img_ok(pre, base, y, Val::Adt(kv, vs), fc0),
{
    let (g, e) = xs(pre, 0, cnt as int, fc0);
    lemma_last_tmp(pre, base, cnt, y, fc0);
    assert forall|i: int| 0 <= i < ops.len() implies dep(#[trigger] ops[i], base, base + cnt) by {
        lemma_cnt_mono(cntf, (i + 1) as nat, n);
        assert(dep(ops[i as nat as int], base + cntf(i as nat), base + cntf((i + 1) as nat)));
    }
    lemma_ops_ev_dep(g, ops, base, base + cnt);
    let r = ctcore::sem::eval_rv(g, pre[cnt as int]->Assign_1);
    assert(r.1 == Seq::<Event>::empty());
    assert(e + r.1 == Seq::<Event>::empty());
    let cv = ctcore::sem::op_vals(g, ops);
    assert(r.0 == Val::Adt(kv, cv));
    assert forall|i: int| 0 <= i < vs.len() implies vr(#[trigger] vs[i], cv[i]) by {
        assert(vs[i as nat as int] == valf(i as nat));
        assert(vr(valf(i as nat), ctcore::sem::eval_op(g, ops[i as nat as int]).0));
    }
    let (fc1, _) = ctcore::sem::exec_stmts(pre, 0, fc0);
    assert forall|i: int| 0 <= i < fc0.locals.len() && !(base <= i < base + pre.len()) implies #[trigger] fc1.locals[i] == fc0.locals[i] by {
        assert(fc1.locals[i] == g.locals[i]);
    }
}

/// `lowers_cv`: the constant's image computes the decoded value.
pub proof fn lemma_cv(m: MirCrate, t: Ty, a: Allocation, off: nat, fuel: nat, y: c::Operand, pre: Seq<c::Stmt>, base: nat, fc0: Frame)
    requires lowers_cv(m, t, a, off, fuel, y, pre, base), fc0.locals.len() >= base + pre.len(),
    ensures img_ok(pre, base, y, dec(m, t, a, off, fuel)->Some_0.0, fc0),
    decreases fuel, 2nat,
{
    let (v, k) = dec(m, t, a, off, fuel)->Some_0;
    if k == 0 && lit_img(m, t, a, off, fuel, y) {
        lemma_lit(m, t, a, off, fuel, y, pre, base, fc0);
    } else if k == 1 && is_tmp(y, base) && tmp_rv(pre, 0) is Use && tmp_rv(pre, 0)->Use_0 is Lit && core_cv(tmp_rv(pre, 0)->Use_0->Lit_0) == v {
        lemma_last_tmp(pre, base, 0, y, fc0);
        lemma_xs_empty(pre, 0, fc0);
        lemma_vr_refl(v);
        let (fc1, _) = ctcore::sem::exec_stmts(pre, 0, fc0);
        assert(Seq::<Event>::empty() + Seq::<Event>::empty() == Seq::<Event>::empty());
        assert forall|i: int| 0 <= i < fc0.locals.len() && !(base <= i < base + pre.len()) implies #[trigger] fc1.locals[i] == fc0.locals[i] by {}
    } else if adt_img(m, t, a, off, (fuel - 1) as nat, y, pre, base) {
        lemma_adt(m, t, a, off, fuel, y, pre, base, fc0);
    } else {
        lemma_zref(m, t, a, off, fuel, y, pre, base, fc0);
    }
}

/// The parts of an ADT constant `adt_img` decodes: variant, field offsets and types.
pub open spec fn adt_kv(m: MirCrate, t: Ty, a: Allocation, off: nat) -> nat { adt_sel(adt_row(m, t)->Some_0, layout(m, t)->Some_0, a, off)->Some_0.0 }
pub open spec fn adt_os(m: MirCrate, t: Ty, a: Allocation, off: nat) -> Seq<MachineSize> { adt_sel(adt_row(m, t)->Some_0, layout(m, t)->Some_0, a, off)->Some_0.1 }
pub open spec fn adt_fs(m: MirCrate, t: Ty, a: Allocation, off: nat) -> Seq<Ty> { adt_row(m, t)->Some_0.variants@[adt_kv(m, t, a, off) as int].fields@ }

proof fn lemma_adt_unpack(m: MirCrate, t: Ty, a: Allocation, off: nat, fuel: nat, y: c::Operand, pre: Seq<c::Stmt>, base: nat)
    requires fuel > 0, adt_img(m, t, a, off, (fuel - 1) as nat, y, pre, base),
    ensures ({
        let (f, kv, o, fs) = ((fuel - 1) as nat, adt_kv(m, t, a, off), adt_os(m, t, a, off), adt_fs(m, t, a, off));
        let cnt = fcount(m, fs, o, a, off, f, fs.len());
        &&& dec_fields(m, fs, o, a, off, f, fs.len()) is Some && o.len() == fs.len()
        &&& dec(m, t, a, off, fuel) == Some((Val::Adt(kv, dec_fields(m, fs, o, a, off, f, fs.len())->Some_0.0), cnt + 1))
        &&& pre.len() == cnt + 1 && is_tmp(y, base + cnt) && kv as usize as nat == kv
        &&& tmp_rv(pre, cnt as int) == c::Rvalue::Aggregate(c::AggKind::Adt(kv as usize), tmp_rv(pre, cnt as int)->Aggregate_1)
        &&& tmp_rv(pre, cnt as int)->Aggregate_1@.len() == fs.len()
        &&& forall|i: int| 0 <= i < fs.len() ==> lowers_cv(m, #[trigger] fs[i], a, (off + o[i].num_bits / 8) as nat, f, tmp_rv(pre, cnt as int)->Aggregate_1@[i],
                pre.subrange(fcount(m, fs, o, a, off, f, i as nat) as int, fcount(m, fs, o, a, off, f, (i + 1) as nat) as int),
                base + fcount(m, fs, o, a, off, f, i as nat))
    }),
{
    hide(dec);
    let kv = adt_kv(m, t, a, off);
    let row = adt_row(m, t)->Some_0;
    assert(kv < row.variants@.len());
    assert(row.variants@.len() <= usize::MAX) by { assert(row.variants.len() == row.variants@.len()); }
    lemma_adt_dec(m, t, a, off, fuel);
    let (f, o, fs) = ((fuel - 1) as nat, adt_os(m, t, a, off), adt_fs(m, t, a, off));
    let cnt = fcount(m, fs, o, a, off, f, fs.len());
    assert(dec_fields(m, fs, o, a, off, f, fs.len()) is Some && o.len() == fs.len());
    assert(pre.len() == cnt + 1);
    assert(is_tmp(y, base + cnt));
    assert(tmp_rv(pre, cnt as int) == c::Rvalue::Aggregate(c::AggKind::Adt(kv as usize), tmp_rv(pre, cnt as int)->Aggregate_1));
    assert(tmp_rv(pre, cnt as int)->Aggregate_1@.len() == fs.len());
    assert(kv as usize as nat == kv);
    assert(dec(m, t, a, off, fuel) == Some((Val::Adt(kv, dec_fields(m, fs, o, a, off, f, fs.len())->Some_0.0), cnt + 1)));
    let (kv2, o2) = adt_sel(row, layout(m, t)->Some_0, a, off)->Some_0;
    assert(kv2 == kv && o2 == o);
    let fs2 = row.variants@[kv2 as int].fields@;
    assert(fs2 == fs);
    let ops = tmp_rv(pre, cnt as int)->Aggregate_1@;
    assert forall|i: int| 0 <= i < fs.len() implies lowers_cv(m, #[trigger] fs[i], a, (off + o[i].num_bits / 8) as nat, f, ops[i],
                pre.subrange(fcount(m, fs, o, a, off, f, i as nat) as int, fcount(m, fs, o, a, off, f, (i + 1) as nat) as int),
                base + fcount(m, fs, o, a, off, f, i as nat)) by {
        assert(lowers_cv(m, fs2[i], a, (off + o2[i].num_bits / 8) as nat, f, ops[i],
                pre.subrange(fcount(m, fs2, o2, a, off, f, i as nat) as int, fcount(m, fs2, o2, a, off, f, (i + 1) as nat) as int),
                base + fcount(m, fs2, o2, a, off, f, i as nat)));
    }
}

proof fn lemma_adt_dec(m: MirCrate, t: Ty, a: Allocation, off: nat, fuel: nat)
    requires fuel > 0, rigid(m, t) is Some && rigid(m, t)->Some_0 is Adt, adt_row(m, t) is Some, layout(m, t) is Some,
        !adt_row(m, t)->Some_0.is_box, !(adt_row(m, t)->Some_0.kind is Union),
        adt_sel(adt_row(m, t)->Some_0, layout(m, t)->Some_0, a, off) is Some,
        adt_kv(m, t, a, off) < adt_row(m, t)->Some_0.variants@.len(), adt_os(m, t, a, off).len() == adt_fs(m, t, a, off).len(),
        dec_fields(m, adt_fs(m, t, a, off), adt_os(m, t, a, off), a, off, (fuel - 1) as nat, adt_fs(m, t, a, off).len()) is Some,
    ensures ({
        let (f, kv, o, fs) = ((fuel - 1) as nat, adt_kv(m, t, a, off), adt_os(m, t, a, off), adt_fs(m, t, a, off));
        dec(m, t, a, off, fuel) == Some((Val::Adt(kv, dec_fields(m, fs, o, a, off, f, fs.len())->Some_0.0), fcount(m, fs, o, a, off, f, fs.len()) + 1))
    }),
{
    assert(int_of(rigid(m, t)->Some_0) is None);
    assert(dec(m, t, a, off, fuel) == dec_adt(m, t, a, off, (fuel - 1) as nat));
}

proof fn lemma_fcount_steps(m: MirCrate, fs: Seq<Ty>, o: Seq<MachineSize>, a: Allocation, off: nat, f: nat)
    requires dec_fields(m, fs, o, a, off, f, fs.len()) is Some,
    ensures fcount(m, fs, o, a, off, f, 0) == 0,
        forall|i: nat| i < fs.len() ==> #[trigger] fcount(m, fs, o, a, off, f, i) <= fcount(m, fs, o, a, off, f, i + 1),
{
    lemma_dec_fields_at(m, fs, o, a, off, f, fs.len());
    assert forall|i: nat| i < fs.len() implies #[trigger] fcount(m, fs, o, a, off, f, i) <= fcount(m, fs, o, a, off, f, i + 1) by {
        assert(dec(m, fs[i as int], a, (off + o[i as int].num_bits / 8) as nat, f) is Some);
    }
}

proof fn lemma_ucount_steps(m: MirCrate, fs: Seq<Ty>, f: nat)
    requires unit_likes(m, fs, f, fs.len(), true) is Some,
    ensures ucount(m, fs, f, 0) == 0,
        forall|i: nat| i < fs.len() ==> #[trigger] ucount(m, fs, f, i) <= ucount(m, fs, f, i + 1),
{
    lemma_uls_at(m, fs, f, fs.len());
    assert forall|i: nat| i < fs.len() implies #[trigger] ucount(m, fs, f, i) <= ucount(m, fs, f, i + 1) by {
        assert(unit_like(m, fs[i as int], f, true) is Some);
    }
}

proof fn lemma_adt(m: MirCrate, t: Ty, a: Allocation, off: nat, fuel: nat, y: c::Operand, pre: Seq<c::Stmt>, base: nat, fc0: Frame)
    requires fuel > 0, adt_img(m, t, a, off, (fuel - 1) as nat, y, pre, base), temps_at(pre, base), fc0.locals.len() >= base + pre.len(),
    ensures dec(m, t, a, off, fuel) is Some, img_ok(pre, base, y, dec(m, t, a, off, fuel)->Some_0.0, fc0),
    decreases fuel, 1nat,
{
    hide(adt_img);
    hide(dec);
    hide(lowers_cv);
    let (f, kv, o, fs) = ((fuel - 1) as nat, adt_kv(m, t, a, off), adt_os(m, t, a, off), adt_fs(m, t, a, off));
    lemma_adt_unpack(m, t, a, off, fuel, y, pre, base);
    let n = fs.len();
    let cnt = fcount(m, fs, o, a, off, f, n);
    let ops = tmp_rv(pre, cnt as int)->Aggregate_1@;
    lemma_dec_fields_at(m, fs, o, a, off, f, n);
    lemma_fcount_steps(m, fs, o, a, off, f);
    let vs = dec_fields(m, fs, o, a, off, f, n)->Some_0.0;
    let cntf = |i: nat| fcount(m, fs, o, a, off, f, i);
    let valf = |i: nat| dec(m, fs[i as int], a, (off + o[i as int].num_bits / 8) as nat, f)->Some_0.0;
    assert forall|i: nat| i < n implies #[trigger] cntf(i) <= cntf(i + 1) by {}
    assert forall|i: nat, g: Frame| i < n && g.locals.len() == fc0.locals.len()
        implies #[trigger] img_ok(pre.subrange(cntf(i) as int, cntf(i + 1) as int), base + cntf(i), ops[i as int], valf(i), g) by {
        lemma_cnt_mono(cntf, i + 1, n);
        assert(lowers_cv(m, fs[i as int], a, (off + o[i as int].num_bits / 8) as nat, f, ops[i as int],
            pre.subrange(fcount(m, fs, o, a, off, f, i) as int, fcount(m, fs, o, a, off, f, i + 1) as int), base + fcount(m, fs, o, a, off, f, i)));
        lemma_cv(m, fs[i as int], a, (off + o[i as int].num_bits / 8) as nat, f, ops[i as int],
            pre.subrange(cntf(i) as int, cntf(i + 1) as int), base + cntf(i), g);
    }
    lemma_imgs(pre, base, ops, cntf, valf, n, fc0);
    assert forall|i: nat| i < n implies #[trigger] vs[i as int] == valf(i) by {
        assert(dec(m, fs[i as int], a, (off + o[i as int].num_bits / 8) as nat, f) is Some);
    }
    lemma_agg_tmp(pre, base, cnt, y, fc0, ops, kv, cntf, valf, n, vs);
}

pub open spec fn ul_fs(m: MirCrate, t: Ty) -> Seq<Ty> { adt_row(m, t)->Some_0.variants@[0].fields@ }

proof fn lemma_ul_unpack(m: MirCrate, t: Ty, fuel: nat, y: c::Operand, pre: Seq<c::Stmt>, base: nat)
    requires ul_img(m, t, fuel, y, pre, base), !(unit_like(m, t, fuel, true)->Some_0.1 == 0 && y is Lit),
    ensures ({
        let (f, fs) = ((fuel - 1) as nat, ul_fs(m, t));
        let cnt = ucount(m, fs, f, fs.len());
        &&& fuel > 0 && unit_likes(m, fs, f, fs.len(), true) is Some
        &&& unit_like(m, t, fuel, true) == Some((Val::Adt(0, unit_likes(m, fs, f, fs.len(), true)->Some_0.0), cnt + 1))
        &&& pre.len() == cnt + 1 && is_tmp(y, base + cnt) && temps_at(pre, base)
        &&& tmp_rv(pre, cnt as int) == c::Rvalue::Aggregate(c::AggKind::Adt(0), tmp_rv(pre, cnt as int)->Aggregate_1)
        &&& tmp_rv(pre, cnt as int)->Aggregate_1@.len() == fs.len()
        &&& forall|i: int| 0 <= i < fs.len() ==> ul_img(m, #[trigger] fs[i], f, tmp_rv(pre, cnt as int)->Aggregate_1@[i],
                pre.subrange(ucount(m, fs, f, i as nat) as int, ucount(m, fs, f, (i + 1) as nat) as int), base + ucount(m, fs, f, i as nat))
    }),
{
}

/// `ul_img`: the image of a unit-like value (closures allowed).
pub proof fn lemma_ul(m: MirCrate, t: Ty, fuel: nat, y: c::Operand, pre: Seq<c::Stmt>, base: nat, fc0: Frame)
    requires ul_img(m, t, fuel, y, pre, base), fc0.locals.len() >= base + pre.len(),
    ensures img_ok(pre, base, y, unit_like(m, t, fuel, true)->Some_0.0, fc0),
    decreases fuel, 1nat,
{
    let (v, k) = unit_like(m, t, fuel, true)->Some_0;
    if k == 0 && y is Lit {
        if core_cv(y->Lit_0) == v { lemma_vr_refl(v); }
    } else {
        lemma_ul_adt(m, t, fuel, y, pre, base, fc0);
    }
}

proof fn lemma_ul_adt(m: MirCrate, t: Ty, fuel: nat, y: c::Operand, pre: Seq<c::Stmt>, base: nat, fc0: Frame)
    requires ul_img(m, t, fuel, y, pre, base), fc0.locals.len() >= base + pre.len(), !(unit_like(m, t, fuel, true)->Some_0.1 == 0 && y is Lit),
    ensures img_ok(pre, base, y, unit_like(m, t, fuel, true)->Some_0.0, fc0),
    decreases fuel, 0nat,
{
    hide(ul_img);
    hide(unit_like);
    {
        lemma_ul_unpack(m, t, fuel, y, pre, base);
        let (f, fs) = ((fuel - 1) as nat, ul_fs(m, t));
        let n = fs.len();
        let cnt = ucount(m, fs, f, n);
        let ops = tmp_rv(pre, cnt as int)->Aggregate_1@;
        lemma_uls_at(m, fs, f, n);
        lemma_ucount_steps(m, fs, f);
        let vs = unit_likes(m, fs, f, n, true)->Some_0.0;
        let cntf = |i: nat| ucount(m, fs, f, i);
        let valf = |i: nat| unit_like(m, fs[i as int], f, true)->Some_0.0;
        assert forall|i: nat| i < n implies #[trigger] cntf(i) <= cntf(i + 1) by {}
        assert forall|i: nat, g: Frame| i < n && g.locals.len() == fc0.locals.len()
            implies #[trigger] img_ok(pre.subrange(cntf(i) as int, cntf(i + 1) as int), base + cntf(i), ops[i as int], valf(i), g) by {
            lemma_cnt_mono(cntf, i + 1, n);
            assert(ul_img(m, fs[i as int], f, ops[i as int],
                pre.subrange(ucount(m, fs, f, i) as int, ucount(m, fs, f, i + 1) as int), base + ucount(m, fs, f, i)));
            lemma_ul(m, fs[i as int], f, ops[i as int], pre.subrange(cntf(i) as int, cntf(i + 1) as int), base + cntf(i), g);
        }
        lemma_imgs(pre, base, ops, cntf, valf, n, fc0);
        assert forall|i: nat| i < n implies #[trigger] vs[i as int] == valf(i) by {
            assert(unit_like(m, fs[i as int], f, true) is Some);
        }
        lemma_agg_tmp(pre, base, cnt, y, fc0, ops, 0, cntf, valf, n, vs);
    }
}

/// The value `dec` gives a `&` of a unit-like ADT (the `zref_img` case).
proof fn lemma_zref_val(m: MirCrate, t: Ty, a: Allocation, off: nat, fuel: nat, p: Ty)
    requires fuel > 0, rigid(m, t) == Some(RigidTy::Ref(rigid(m, t)->Some_0->Ref_0, p, Mutability::Not)), rigid(m, p) matches Some(RigidTy::Adt(_, _)),
        dec(m, t, a, off, fuel) is Some,
    ensures dec(m, t, a, off, fuel)->Some_0.0 == Val::Shr(Box::new(unit_like(m, p, tfuel(m), true)->Some_0.0)),
{
    assert(dec(m, t, a, off, fuel) == dec_ref(m, p, a, off, (fuel - 1) as nat));
}

proof fn lemma_zref_unpack(m: MirCrate, t: Ty, y: c::Operand, pre: Seq<c::Stmt>, base: nat)
    requires zref_img(m, t, y, pre, base),
    ensures ({
        let p = rigid(m, t)->Some_0->Ref_1;
        let cnt = (pre.len() - 1) as nat;
        let pl = tmp_rv(pre, cnt as int)->RefShr_0;
        &&& rigid(m, t) == Some(RigidTy::Ref(rigid(m, t)->Some_0->Ref_0, p, Mutability::Not))
        &&& pre.len() >= 1 && is_tmp(y, base + cnt) && tmp_rv(pre, cnt as int) is RefShr
        &&& ul_img(m, p, tfuel(m), c::Operand::Copy(pl), pre.subrange(0, cnt as int), base)
        &&& rigid(m, p) matches Some(RigidTy::Adt(_, _))
        &&& cnt >= 1 && pl.local == base + cnt - 1 && pl.proj@.len() == 0
    }),
{
    let p = rigid(m, t)->Some_0->Ref_1;
    let cnt = (pre.len() - 1) as nat;
    let pl = tmp_rv(pre, cnt as int)->RefShr_0;
    let ulp = pre.subrange(0, cnt as int);
    assert(ul_img(m, p, tfuel(m), c::Operand::Copy(pl), ulp, base));
    lemma_ul_unpack(m, p, tfuel(m), c::Operand::Copy(pl), ulp, base);
    assert(cnt == ucount(m, ul_fs(m, p), (tfuel(m) - 1) as nat, ul_fs(m, p).len()) + 1);
}

/// `zref_img`: `&` of a unit-like ADT.
proof fn lemma_zref(m: MirCrate, t: Ty, a: Allocation, off: nat, fuel: nat, y: c::Operand, pre: Seq<c::Stmt>, base: nat, fc0: Frame)
    requires zref_img(m, t, y, pre, base), temps_at(pre, base), fuel > 0, dec(m, t, a, off, fuel) is Some, fc0.locals.len() >= base + pre.len(),
    ensures img_ok(pre, base, y, dec(m, t, a, off, fuel)->Some_0.0, fc0),
{
    hide(zref_img);
    hide(dec);
    hide(ul_img);
    let p = rigid(m, t)->Some_0->Ref_1;
    let cnt = (pre.len() - 1) as nat;
    let pl = tmp_rv(pre, cnt as int)->RefShr_0;
    lemma_zref_unpack(m, t, y, pre, base);
    lemma_zref_val(m, t, a, off, fuel, p);
    let ulpre = pre.subrange(0, cnt as int);
    lemma_ul(m, p, tfuel(m), c::Operand::Copy(pl), ulpre, base, fc0);
    lemma_last_tmp(pre, base, cnt, y, fc0);
    let (g, e) = xs(pre, 0, cnt as int, fc0);
    lemma_eval_tmp(g, c::Operand::Copy(pl), (base + cnt - 1) as nat);
    let r = ctcore::sem::eval_rv(g, pre[cnt as int]->Assign_1);
    assert(r == (Val::Shr(Box::new(g.locals[base + cnt - 1])), Seq::<Event>::empty()));
    assert(e + r.1 == Seq::<Event>::empty());
    let (fc1, _) = ctcore::sem::exec_stmts(pre, 0, fc0);
    assert forall|i: int| 0 <= i < fc0.locals.len() && !(base <= i < base + pre.len()) implies #[trigger] fc1.locals[i] == fc0.locals[i] by {
        assert(fc1.locals[i] == g.locals[i]);
    }
}

/// `lowers_const`: a constant operand's image computes `const_val`'s value.
pub proof fn lemma_const(m: MirCrate, k: ConstOperand, y: c::Operand, pre: Seq<c::Stmt>, base: nat, fc0: Frame)
    requires lowers_const(m, k, y, pre, base), fc0.locals.len() >= base + pre.len(),
    ensures img_ok(pre, base, y, const_val(m, k)->Some_0.0, fc0),
{
    let t = k.const_.ty;
    match k.const_.kind {
        ConstantKind::ZeroSized => { lemma_ul_us(m, t, tfuel(m), true); },
        ConstantKind::Allocated(a) => {
            if charged(m, t) { lemma_cv(m, t, a, 0, dfuel(m), y, pre, base, fc0); }
            else { lemma_lit(m, t, a, 0, dfuel(m), y, pre, base, fc0); }
        },
        _ => {},
    }
}

} // verus!
