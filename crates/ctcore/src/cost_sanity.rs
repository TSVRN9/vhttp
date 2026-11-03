//! Non-vacuity of `theorem_cost` on counted loops: certificates with `Gap` potentials for a
//! 4-block `while i < n`, with `n` a parameter, an input's length, or the length behind `&&[u8]`
//! (the varint parser's input), and the theorem's premises discharged end to end. Spec code cannot
//! build a `Vec`, so each lemma takes the program through premises on its views.
#[allow(unused_imports)]
use crate::cost::*;
#[allow(unused_imports)]
use crate::ct::*;
#[allow(unused_imports)]
use crate::sem::*;
#[allow(unused_imports)]
use crate::syntax::*;
use vstd::prelude::*;

verus! {

pub open spec fn local(pl: Place, x: usize) -> bool { pl.local == x && pl.proj@.len() == 0 }
pub open spec fn vu(x: usize) -> Atom { Atom::Val(x, IntTy::Usize) }
pub open spec fn ga(m: usize) -> Atom { Atom::Gap(Box::new(vu(m)), Box::new(vu(2))) }

// ------- program shape: bb1 test, bb2 increment, bb3 return; bb0 varies
pub open spec fn b1_ok(blk: Block, m: usize) -> bool {
    &&& blk.stmts@.len() == 1
    &&& blk.stmts@[0] matches Stmt::Assign(d, Rvalue::Bin(BinOp::Lt, IntTy::Usize, Operand::Copy(a), Operand::Copy(b))) && local(d, 3) && local(a, 2) && local(b, m)
    &&& blk.term matches Term::Switch(Operand::Copy(cc), ts, o) && local(cc, 3) && ts@ == seq![(0u128, 3usize)] && o == 2
}
pub open spec fn b2_ok(blk: Block) -> bool {
    &&& blk.stmts@.len() == 1
    &&& blk.stmts@[0] matches Stmt::Assign(d, Rvalue::Bin(BinOp::Add, IntTy::Usize, Operand::Copy(a), Operand::Const(IntTy::Usize, n))) && local(d, 2) && local(a, 2) && n == 1
    &&& blk.term == Term::Goto(1usize)
}
pub open spec fn b3_ok(blk: Block) -> bool { blk.stmts@.len() == 0 && blk.term == Term::Return }
pub open spec fn set0(s: Stmt) -> bool { s matches Stmt::Assign(d, Rvalue::Use(Operand::Const(IntTy::Usize, n))) && local(d, 2) && n == 0 }

pub open spec fn p_lin(pl: Poly, a: Atom, k: u64, c: u64) -> bool {
    &&& pl.monos@.len() == 2
    &&& pl.monos@[0].coef == k && pl.monos@[0].atoms@ == seq![a]
    &&& pl.monos@[1].coef == c && pl.monos@[1].atoms@.len() == 0
}
pub open spec fn p_const(pl: Poly, c: u64) -> bool {
    pl.monos@.len() == 1 && pl.monos@[0].coef == c && pl.monos@[0].atoms@.len() == 0
}
/// bb1..bb3 of the certificate; bb0's pot is `4 * a0 + c0`.
pub open spec fn cert_shape(c: Cert, m: usize, a0: Atom, c0: u64) -> bool {
    &&& c.blocks@.len() == 4
    &&& c.blocks@[0].facts@.len() == 0 && p_lin(c.blocks@[0].pot, a0, 4, c0)
    &&& c.blocks@[1].facts@.len() == 0 && p_lin(c.blocks@[1].pot, ga(m), 4, 3)
    &&& c.blocks@[2].facts@ == seq![Fact::Lt(vu(2), vu(m))] && p_lin(c.blocks@[2].pot, ga(m), 4, 1)
    &&& c.blocks@[3].facts@.len() == 0 && p_const(c.blocks@[3].pot, 1)
}

// ------- generic evaluation
pub proof fn lemma_p_lin(fr: Frame, pl: Poly, a: Atom, k: u64, c: u64)
    requires p_lin(pl, a, k, c),
    ensures poly_val(fr, pl) == (k as nat) * atom_val(fr, a) + (c as nat),
{
    reveal_with_fuel(monos_val, 3);
    reveal_with_fuel(atoms_val, 2);
    let ms = pl.monos@;
    assert(ms.drop_first()[0] == ms[1]);
    assert(ms.drop_first().drop_first().len() == 0);
    let s = ms[0].atoms@;
    assert(s[0] == a);
    assert(s.drop_first().len() == 0);
    assert(atoms_val(fr, s) == atom_val(fr, a) * 1);
    assert(atoms_val(fr, ms[1].atoms@) == 1);
    assert(mono_val(fr, ms[1]) == (c as nat) * 1);
}
proof fn lemma_p_const(fr: Frame, pl: Poly, c: u64)
    requires p_const(pl, c),
    ensures poly_val(fr, pl) == c as nat,
{
    reveal_with_fuel(monos_val, 2);
    reveal_with_fuel(atoms_val, 1);
    assert(pl.monos@.drop_first().len() == 0);
    assert(mono_val(fr, pl.monos@[0]) == (c as nat) * 1);
}
pub proof fn lemma_read_local(fr: Frame, pl: Place, x: usize)
    requires local(pl, x), (x as nat) < fr.locals.len(),
    ensures read_place(fr, pl).0 == fr.locals[x as int],
        place_loc(fr, pl) == Some((local_loc(x as nat), Seq::<Event>::empty())),
{
    assert(pl.proj@.len() == 0);
    assert(walk(fr, pl.proj@, 0, Cur::L(local_loc(pl.local as nat))).0 == Cur::L(local_loc(x as nat)));
    assert(place_walk(fr, pl).1 =~= Seq::<Event>::empty());
    assert(nth(fr.locals, x as nat) == fr.locals[x as int]);
    assert(local_loc(x as nat).path.len() == 0);
}
/// `x := v` for an empty-projection place.
pub proof fn lemma_assign_local(fr: Frame, pl: Place, x: usize, v: Val)
    requires local(pl, x), (x as nat) < fr.locals.len(),
    ensures assign(fr, pl, v).0 == (Frame { locals: fr.locals.update(x as int, v), slots: fr.slots }),
{
    lemma_read_local(fr, pl, x);
    assert(local_loc(x as nat).path.len() == 0);
    let l = local_loc(x as nat);
    assert(write_at(fr.locals[x as int], l.path, v) == v);
}
proof fn lemma_stmts1(ss: Seq<Stmt>, fr: Frame)
    requires ss.len() == 1,
    ensures exec_stmts(ss, 0, fr).0 == exec_stmt(fr, ss[0]).0,
{
    reveal_with_fuel(exec_stmts, 2);
}
proof fn lemma_val_as(v: Val)
    ensures val_nat(IntTy::Usize, v) == uval(IntTy::Usize, as_int(v)), uval(IntTy::Usize, as_int(v)) < 0x1_0000_0000_0000_0000int, uval(IntTy::Usize, as_int(v)) >= 0,
{
    vstd::arithmetic::power2::lemma2_to64();
    assert(vstd::arithmetic::power2::pow2(bits(IntTy::Usize)) == 0x1_0000_0000_0000_0000int);
    assert(0int % 0x1_0000_0000_0000_0000int == 0);
    assert((as_int(v) as int) % 0x1_0000_0000_0000_0000int < 0x1_0000_0000_0000_0000int);
}

pub proof fn lemma_uval_small(x: u128)
    requires (x as int) < 0x1_0000_0000_0000_0000int,
    ensures uval(IntTy::Usize, x) == x as int,
{
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::div_mod::lemma_small_mod(x as nat, 0x1_0000_0000_0000_0000nat);
}

// ------- the three fixed blocks
proof fn lemma_b3(p: Program, c: Cert, sums: Seq<Option<Poly>>, fr: Frame, m: usize, a0: Atom, c0: u64)
    requires b3_ok(p.fns@[0].blocks@[3]), cert_shape(c, m, a0, c0),
    ensures block_step_ok(p, 0, 3, c, sums, fr),
{
    lemma_p_const(fr, c.blocks@[3].pot, 1);
}

proof fn lemma_b2(p: Program, c: Cert, sums: Seq<Option<Poly>>, fr: Frame, m: usize, a0: Atom, c0: u64)
    requires b2_ok(p.fns@[0].blocks@[2]), cert_shape(c, m, a0, c0), fr.locals.len() == 6, m < 6, m != 2, m != 3,
        facts_hold(fr, c.blocks@[2].facts@),
    ensures block_step_ok(p, 0, 2, c, sums, fr),
{
    let blk = p.fns@[0].blocks@[2];
    let s = blk.stmts@[0];
    lemma_stmts1(blk.stmts@, fr);
    if let Stmt::Assign(d, Rvalue::Bin(_, _, Operand::Copy(a), o)) = s {
        lemma_read_local(fr, a, 2);
        let old = fr.locals[2];
        assert(eval_op(fr, o).0 == Val::Int(1));
        let nv = Val::Int(binop(BinOp::Add, IntTy::Usize, as_int(old), 1));
        lemma_assign_local(fr, d, 2, nv);
        let fr1 = exec_stmts(blk.stmts@, 0, fr).0;
        assert(fr1.locals == fr.locals.update(2, nv));
        assert(fact_holds(fr, c.blocks@[2].facts@[0]));
        reveal_with_fuel(atom_val, 3);
        lemma_val_as(old); lemma_val_as(fr.locals[m as int]);
        lemma_val_as(Val::Int(1));
        let u = uval(IntTy::Usize, as_int(old));
        let n = val_nat(IntTy::Usize, fr.locals[m as int]);
        assert(u < n);
        assert(u + 1 < 0x1_0000_0000_0000_0000int);
        vstd::arithmetic::power2::lemma2_to64();
        assert(vstd::arithmetic::power2::pow2(bits(IntTy::Usize)) == 0x1_0000_0000_0000_0000int);
        assert(binop(BinOp::Add, IntTy::Usize, as_int(old), 1) == (u + 1) as u128) by {
            reveal(binop);
            lemma_uval_small(1);
            assert((u + 1) % 0x1_0000_0000_0000_0000int == u + 1) by (nonlinear_arith) requires 0 <= u + 1 < 0x1_0000_0000_0000_0000int;
        }
        assert(val_nat(IntTy::Usize, nv) == u + 1) by {
            assert((u + 1) % 0x1_0000_0000_0000_0000int == u + 1) by (nonlinear_arith) requires 0 <= u + 1 < 0x1_0000_0000_0000_0000int;
        }
        assert(fr1.locals[m as int] == fr.locals[m as int]);
        assert(fr1.locals[2] == nv);
        lemma_gap_dec(n, u as nat);
        lemma_p_lin(fr, c.blocks@[2].pot, ga(m), 4, 1);
        lemma_p_lin(fr1, c.blocks@[1].pot, ga(m), 4, 3);
        assert(atom_val(fr, ga(m)) == gap(n, u as nat));
        assert(atom_val(fr1, ga(m)) == gap(n, (u + 1) as nat));
    }
}

proof fn lemma_b1(p: Program, c: Cert, sums: Seq<Option<Poly>>, fr: Frame, m: usize, a0: Atom, c0: u64)
    requires b1_ok(p.fns@[0].blocks@[1], m), cert_shape(c, m, a0, c0), fr.locals.len() == 6, m < 6, m != 2, m != 3,
    ensures block_step_ok(p, 0, 1, c, sums, fr),
{
    let blk = p.fns@[0].blocks@[1];
    lemma_stmts1(blk.stmts@, fr);
    if let Stmt::Assign(d, Rvalue::Bin(_, _, Operand::Copy(a), Operand::Copy(b))) = blk.stmts@[0] {
        lemma_read_local(fr, a, 2);
        lemma_read_local(fr, b, m);
        let (vi, vn) = (fr.locals[2], fr.locals[m as int]);
        let nv = Val::Int(binop(BinOp::Lt, IntTy::Usize, as_int(vi), as_int(vn)));
        lemma_assign_local(fr, d, 3, nv);
        let fr1 = exec_stmts(blk.stmts@, 0, fr).0;
        assert(fr1.locals == fr.locals.update(3, nv));
        lemma_val_as(vi); lemma_val_as(vn);
        assert(binop(BinOp::Lt, IntTy::Usize, as_int(vi), as_int(vn))
            == b2i(uval(IntTy::Usize, as_int(vi)) < uval(IntTy::Usize, as_int(vn)))) by { reveal(binop); }
        reveal_with_fuel(atom_val, 3);
        assert(fr1.locals[2] == vi && fr1.locals[m as int] == vn);
        assert(atom_val(fr1, ga(m)) == atom_val(fr, ga(m)));
        lemma_p_lin(fr, c.blocks@[1].pot, ga(m), 4, 3);
        lemma_p_lin(fr1, c.blocks@[2].pot, ga(m), 4, 1);
        lemma_p_const(fr1, c.blocks@[3].pot, 1);
        if let Term::Switch(Operand::Copy(cc), ts, o) = blk.term {
            lemma_read_local(fr1, cc, 3);
            assert(fr1.locals[3] == nv);
            let v = as_int(nv);
            assert(switch_target(ts@, 0, v, o) == (if v == 0 { 3usize } else { 2usize })) by { reveal_with_fuel(switch_target, 2); }
            if v != 0 {
                assert(fact_holds(fr1, c.blocks@[2].facts@[0]));
            }
        }
    }
}

// ------- entry: the bound is the parameter `_1: usize`
pub open spec fn prog_param(p: Program) -> bool {
    &&& p.fns@.len() == 1
    &&& p.fns@[0].nargs == 1
    &&& p.fns@[0].locals@ == seq![Ty::Unit, Ty::Int(IntTy::Usize), Ty::Int(IntTy::Usize), Ty::Int(IntTy::Bool), Ty::Int(IntTy::Usize), Ty::Int(IntTy::Usize)]
    &&& p.fns@[0].blocks@.len() == 4
    &&& p.fns@[0].blocks@[0].stmts@.len() == 1 && set0(p.fns@[0].blocks@[0].stmts@[0])
    &&& p.fns@[0].blocks@[0].term == Term::Goto(1usize)
    &&& b1_ok(p.fns@[0].blocks@[1], 1) && b2_ok(p.fns@[0].blocks@[2]) && b3_ok(p.fns@[0].blocks@[3])
}
proof fn lemma_b0_param(p: Program, c: Cert, sums: Seq<Option<Poly>>, fr: Frame)
    requires prog_param(p), cert_shape(c, 1, vu(1), 5), fr.locals.len() == 6,
    ensures block_step_ok(p, 0, 0, c, sums, fr),
{
    let blk = p.fns@[0].blocks@[0];
    lemma_stmts1(blk.stmts@, fr);
    if let Stmt::Assign(d, _) = blk.stmts@[0] {
        lemma_assign_local(fr, d, 2, Val::Int(0));
        let fr1 = exec_stmts(blk.stmts@, 0, fr).0;
        assert(fr1.locals == fr.locals.update(2, Val::Int(0)));
        reveal_with_fuel(atom_val, 3);
        lemma_val_as(Val::Int(0));
        lemma_p_lin(fr, c.blocks@[0].pot, vu(1), 4, 5);
        lemma_p_lin(fr1, c.blocks@[1].pot, ga(1), 4, 3);
        assert(fr1.locals[1] == fr.locals[1]);
        lemma_uval_small(0);
        assert(val_nat(IntTy::Usize, Val::Int(0)) == 0);
        assert(atom_val(fr1, ga(1)) == atom_val(fr, vu(1)));
    }
}
pub proof fn sanity_cert_loop_param(p: Program, c: Cert, sums: Seq<Option<Poly>>)
    requires prog_param(p), cert_shape(c, 1, vu(1), 5), sums.len() == 1, sums[0] == Some(c.blocks@[0].pot),
    ensures cert_for(p, 0, c, sums),
{
    assert forall|ls: Seq<FnLab>, b: nat, fr: Frame| #![trigger plc(p, ls, 0, fr), block_step_ok(p, 0, b, c, sums, fr)]
        b < c.blocks@.len() && ok_prog(p, ls) && plc(p, ls, 0, fr)
        && facts_hold(fr, c.blocks@[b as int].facts@) && frame_len_ok(fr)
        implies block_step_ok(p, 0, b, c, sums, fr)
    by {
        if b == 0 { lemma_b0_param(p, c, sums, fr); }
        else if b == 1 { lemma_b1(p, c, sums, fr, 1, vu(1), 5); }
        else if b == 2 { lemma_b2(p, c, sums, fr, 1, vu(1), 5); }
        else { lemma_b3(p, c, sums, fr, 1, vu(1), 5); }
    }
}

// ------- premises: ok_prog with all-public labels
proof fn lemma_ok_param(p: Program, ls: Seq<FnLab>)
    requires prog_param(p), ls.len() == 1, ls[0].locals@ == seq![false, false, false, false, false, false],
    ensures ok_prog(p, ls),
{
    let b = p.fns@[0];
    assert(!ty_has_mut(Ty::Unit)); assert(!ty_has_mut(Ty::Int(IntTy::Usize))); assert(!ty_has_mut(Ty::Int(IntTy::Bool)));
    assert(wf_body(p, 0)) by {
        assert forall|i: int| 0 < i < b.locals@.len() implies wf_local_ty(#[trigger] b.locals@[i]) by {}
        assert forall|i: int| 0 <= i < b.blocks@.len() implies #[trigger] wf_block(p, 0, b.blocks@[i]) by {
            if i == 1 { if let Term::Switch(_, ts, o) = b.blocks@[1].term {
                assert forall|k: int| 0 <= k < ts@.len() implies (#[trigger] ts@[k]).1 < 4 by { assert(ts@[0].1 == 3); }
            } }
        }
    }
    assert forall|f: nat| f < p.fns@.len() implies #[trigger] wf_body(p, f) by { assert(f == 0); }
    let l = ls[0];
    assert forall|x: nat| x < 6 implies !lab(l, x) by {}
    assert(ok_body(p, ls, 0)) by {
        assert forall|i: int| 0 <= i < b.blocks@.len() implies #[trigger] ok_block(p, ls, 0, b.blocks@[i]) by {
            let blk = b.blocks@[i];
            assert forall|k: int| 0 <= k < blk.stmts@.len() implies ok_stmt(b, l, #[trigger] blk.stmts@[k]) by {
                assert(k == 0);
                if i == 0 || i == 1 || i == 2 {
                    assert(lab(l, 2) == false && lab(l, 1) == false && lab(l, 3) == false);
                }
            }
            if i == 1 { assert(lab(l, 3) == false); }
        }
    }
    assert forall|f: nat| #![trigger ok_body(p, ls, f)] f < p.fns@.len() implies
        ls[f as int].locals@.len() == p.fns@[f as int].locals@.len() && ok_body(p, ls, f) by { assert(f == 0); }
}

/// End to end: `theorem_cost`'s premises discharged on `while i < n`, all-public labels, a concrete `Int` argument.
pub proof fn sanity_theorem_loop(p: Program, ls: Seq<FnLab>, c: Cert, sums: Seq<Option<Poly>>, n: u128, fuel: nat)
    requires
        prog_param(p), cert_shape(c, 1, vu(1), 5), sums.len() == 1, sums[0] == Some(c.blocks@[0].pot),
        ls.len() == 1, ls[0].locals@ == seq![false, false, false, false, false, false],
        run_fn(p, 0, init_entry(p, 0, seq![Val::Int(n)], seq![Val::Unit]), fuel) is Some,
    ensures
        run_fn(p, 0, init_entry(p, 0, seq![Val::Int(n)], seq![Val::Unit]), fuel).unwrap().2
            <= 4 * val_nat(IntTy::Usize, Val::Int(n)) + 5,
{
    let (args, slots) = (seq![Val::Int(n)], seq![Val::Unit]);
    lemma_ok_param(p, ls);
    sanity_cert_loop_param(p, c, sums);
    let certs = seq![c];
    assert forall|g: int| 0 <= g < p.fns@.len() && sums[g] is Some implies cert_for(p, g as nat, certs[g], sums) by { assert(g == 0); }
    assert(entry_plc(p, 0, args, slots)) by {
        assert forall|j: int| 0 <= j < 1 && !(p.fns@[0].locals@[1 + j] is Mut) implies no_mut(#[trigger] args[j]) by { assert(args[0] == Val::Int(n)); }
        assert forall|j: int| 0 <= j < 1 implies no_mut(#[trigger] slots[j]) by { assert(slots[0] == Val::Unit); }
    }
    assert(vals_len_ok(args)) by { assert forall|i: int| 0 <= i < args.len() implies len_ok(#[trigger] args[i]) by { assert(args[0] == Val::Int(n)); } }
    assert(vals_len_ok(slots)) by { assert forall|i: int| 0 <= i < slots.len() implies len_ok(#[trigger] slots[i]) by { assert(slots[0] == Val::Unit); } }
    theorem_cost(p, ls, certs, sums, 0, args, slots, fuel, c.blocks@[0].pot);
    let e = init_entry(p, 0, args, slots);
    lemma_p_lin(e, c.blocks@[0].pot, vu(1), 4, 5);
    assert(e.locals[1] == Val::Int(n));
}

// ------- entries over a length
proof fn lemma_stmts2(ss: Seq<Stmt>, fr: Frame)
    requires ss.len() == 2,
    ensures exec_stmts(ss, 0, fr).0 == exec_stmt(exec_stmt(fr, ss[0]).0, ss[1]).0,
{ reveal_with_fuel(exec_stmts, 3); }
pub proof fn lemma_stmts3(ss: Seq<Stmt>, fr: Frame)
    requires ss.len() == 3,
    ensures exec_stmts(ss, 0, fr).0 == exec_stmt(exec_stmt(exec_stmt(fr, ss[0]).0, ss[1]).0, ss[2]).0,
{ reveal_with_fuel(exec_stmts, 4); }
pub open spec fn shape_tail(p: Program, m: usize) -> bool {
    &&& p.fns@.len() == 1 && p.fns@[0].nargs == 1
    &&& p.fns@[0].blocks@.len() == 4
    &&& p.fns@[0].blocks@[0].term == Term::Goto(1usize)
    &&& b1_ok(p.fns@[0].blocks@[1], m) && b2_ok(p.fns@[0].blocks@[2]) && b3_ok(p.fns@[0].blocks@[3])
}

// ------- entry: `_1: &[u8]`, `_4 = Len(_1); _2 = 0`, as `parse_prefix_int`'s `_3 = PtrMetadata(_2)`
pub open spec fn prog_len(p: Program) -> bool {
    &&& shape_tail(p, 4)
    &&& p.fns@[0].blocks@[0].stmts@.len() == 2
    &&& p.fns@[0].blocks@[0].stmts@[0] matches Stmt::Assign(d, Rvalue::Len(q)) && local(d, 4) && local(q, 1)
    &&& set0(p.fns@[0].blocks@[0].stmts@[1])
}
proof fn lemma_b0_len(p: Program, c: Cert, sums: Seq<Option<Poly>>, fr: Frame)
    requires prog_len(p), cert_shape(c, 4, Atom::Len(1), 6), fr.locals.len() == 6, frame_len_ok(fr),
    ensures block_step_ok(p, 0, 0, c, sums, fr),
{
    let blk = p.fns@[0].blocks@[0];
    lemma_stmts2(blk.stmts@, fr);
    if let Stmt::Assign(d, Rvalue::Len(q)) = blk.stmts@[0] { if let Stmt::Assign(d2, _) = blk.stmts@[1] {
        lemma_read_local(fr, q, 1);
        let v1 = fr.locals[1];
        assert(len_ok(v1));
        lemma_elems_len_ok(fr, v1);
        let n = elems(fr, v1).len();
        let f1 = Frame { locals: fr.locals.update(4, Val::Int(n as u128)), slots: fr.slots };
        lemma_assign_local(fr, d, 4, Val::Int(n as u128));
        lemma_assign_local(f1, d2, 2, Val::Int(0));
        let fr1 = exec_stmts(blk.stmts@, 0, fr).0;
        assert(fr1.locals == f1.locals.update(2, Val::Int(0)));
        reveal_with_fuel(atom_val, 3);
        lemma_uval_small(0); lemma_uval_small(n as u128);
        lemma_p_lin(fr, c.blocks@[0].pot, Atom::Len(1), 4, 6);
        lemma_p_lin(fr1, c.blocks@[1].pot, ga(4), 4, 3);
        assert(fr1.locals[4] == Val::Int(n as u128) && fr1.locals[2] == Val::Int(0));
        lemma_elems_le_len_nat(fr, v1);
        assert(n <= atom_val(fr, Atom::Len(1)));
        assert(atom_val(fr1, ga(4)) == n);
    } }
}
pub proof fn sanity_cert_loop_len(p: Program, c: Cert, sums: Seq<Option<Poly>>)
    requires prog_len(p), p.fns@[0].locals@.len() == 6, cert_shape(c, 4, Atom::Len(1), 6), sums.len() == 1, sums[0] == Some(c.blocks@[0].pot),
    ensures cert_for(p, 0, c, sums),
{
    assert forall|ls: Seq<FnLab>, b: nat, fr: Frame| #![trigger plc(p, ls, 0, fr), block_step_ok(p, 0, b, c, sums, fr)]
        b < c.blocks@.len() && ok_prog(p, ls) && plc(p, ls, 0, fr)
        && facts_hold(fr, c.blocks@[b as int].facts@) && frame_len_ok(fr)
        implies block_step_ok(p, 0, b, c, sums, fr)
    by {
        if b == 0 { lemma_b0_len(p, c, sums, fr); }
        else if b == 1 { lemma_b1(p, c, sums, fr, 4, Atom::Len(1), 6); }
        else if b == 2 { lemma_b2(p, c, sums, fr, 4, Atom::Len(1), 6); }
        else { lemma_b3(p, c, sums, fr, 4, Atom::Len(1), 6); }
    }
}

pub open spec fn prog_double_ref(p: Program) -> bool {
    &&& shape_tail(p, 4)
    &&& p.fns@[0].locals@.len() == 6
    &&& !(p.fns@[0].locals@[1] is Mut)
    &&& p.fns@[0].blocks@[0].stmts@.len() == 3
    &&& p.fns@[0].blocks@[0].stmts@[0] matches Stmt::Assign(d, Rvalue::Use(Operand::Copy(q)))
            && local(d, 5) && q.local == 1 && q.proj@ == seq![Proj::Deref]
    &&& p.fns@[0].blocks@[0].stmts@[1] matches Stmt::Assign(d, Rvalue::Len(q)) && local(d, 4) && local(q, 5)
    &&& set0(p.fns@[0].blocks@[0].stmts@[2])
}

pub open spec fn deref_of(v1: Val) -> Val { match v1 { Val::Shr(b) => *b, _ => Val::Unit } }

proof fn lemma_read_deref(fr: Frame, q: Place)
    requires q.local == 1, q.proj@ == seq![Proj::Deref], fr.locals.len() == 6, !(fr.locals[1] is Mut),
    ensures read_place(fr, q).0 == deref_of(fr.locals[1]),
{
    let v1 = fr.locals[1];
    assert(q.proj@[0] == Proj::Deref);
    assert(read_loc(fr, local_loc(1)) == v1) by { assert(nth(fr.locals, 1) == v1); assert(local_loc(1).path.len() == 0); }
    reveal_with_fuel(walk, 2);
}

/// The frame after bb0, and the length that lands in `_4`.
proof fn lemma_post_double_ref(p: Program, ls: Seq<FnLab>, fr: Frame) -> (n: nat)
    requires prog_double_ref(p), plc(p, ls, 0, fr), frame_len_ok(fr),
    ensures
        n <= USIZE_MAX, exec_stmts(p.fns@[0].blocks@[0].stmts@, 0, fr).0.locals.len() == 6,
        n == elems(fr, deref_of(fr.locals[1])).len(),
        exec_stmts(p.fns@[0].blocks@[0].stmts@, 0, fr).0.locals[4] == Val::Int(n as u128),
        exec_stmts(p.fns@[0].blocks@[0].stmts@, 0, fr).0.locals[2] == Val::Int(0),
{
    let blk = p.fns@[0].blocks@[0];
    lemma_stmts3(blk.stmts@, fr);
    let v1 = fr.locals[1];
    assert(!(v1 is Mut));
    assert(no_mut(v1));
    assert(len_ok(v1));
    let w = deref_of(v1);
    assert(no_mut(w)); assert(len_ok(w));
    lemma_elems_len_ok(fr, w);
    let n = elems(fr, w).len();
    if let Stmt::Assign(d5, Rvalue::Use(Operand::Copy(q))) = blk.stmts@[0] {
    if let Stmt::Assign(d4, Rvalue::Len(q5)) = blk.stmts@[1] {
    if let Stmt::Assign(d2, _) = blk.stmts@[2] {
        lemma_read_deref(fr, q);
        let f1 = Frame { locals: fr.locals.update(5, w), slots: fr.slots };
        lemma_assign_local(fr, d5, 5, w);
        lemma_read_local(f1, q5, 5);
        assert(elems(f1, w) == elems(fr, w));
        let f2 = Frame { locals: f1.locals.update(4, Val::Int(n as u128)), slots: f1.slots };
        lemma_assign_local(f1, d4, 4, Val::Int(n as u128));
        lemma_assign_local(f2, d2, 2, Val::Int(0));
    } } }
    n
}

/// `_1 = Shr(Shr(Arr))`: `4 * Len(1) + 7` pays for a loop over the inner length.
proof fn lemma_b0_double_ref(p: Program, c: Cert, sums: Seq<Option<Poly>>, ls: Seq<FnLab>, fr: Frame)
    requires prog_double_ref(p), cert_shape(c, 4, Atom::Len(1), 7), plc(p, ls, 0, fr), frame_len_ok(fr),
    ensures block_step_ok(p, 0, 0, c, sums, fr),
{
    let n = lemma_post_double_ref(p, ls, fr);
    let fr1 = exec_stmts(p.fns@[0].blocks@[0].stmts@, 0, fr).0;
    reveal_with_fuel(atom_val, 3);
    lemma_uval_small(0); lemma_uval_small(n as u128);
    lemma_p_lin(fr, c.blocks@[0].pot, Atom::Len(1), 4, 7);
    lemma_p_lin(fr1, c.blocks@[1].pot, ga(4), 4, 3);
    assert(atom_val(fr1, ga(4)) == n);
    let v1 = fr.locals[1];
    assert(!(v1 is Mut));
    assert(no_mut(v1));
    lemma_elems_le_len_nat(fr, deref_of(v1));
    assert(no_mut(deref_of(v1)));
    assert(!(deref_of(v1) is Mut));
    if let Val::Shr(b) = v1 { assert(shr_len(v1) == shr_len(*b)); assert(deref_of(v1) == *b); } else { assert(deref_of(v1) == Val::Unit); }
    assert(atom_val(fr, Atom::Len(1)) == shr_len(v1));
    assert(n <= atom_val(fr, Atom::Len(1)));
}

/// The `&&[u8]` shape as a whole certificate, `parse`'s entry over a counted loop.
pub proof fn sanity_cert_loop_double_ref(p: Program, c: Cert, sums: Seq<Option<Poly>>)
    requires prog_double_ref(p), cert_shape(c, 4, Atom::Len(1), 7), sums.len() == 1, sums[0] == Some(c.blocks@[0].pot),
    ensures cert_for(p, 0, c, sums),
{
    assert forall|ls: Seq<FnLab>, b: nat, fr: Frame| #![trigger plc(p, ls, 0, fr), block_step_ok(p, 0, b, c, sums, fr)]
        b < c.blocks@.len() && ok_prog(p, ls) && plc(p, ls, 0, fr)
        && facts_hold(fr, c.blocks@[b as int].facts@) && frame_len_ok(fr)
        implies block_step_ok(p, 0, b, c, sums, fr)
    by {
        if b == 0 { lemma_b0_double_ref(p, c, sums, ls, fr); }
        else if b == 1 { lemma_b1(p, c, sums, fr, 4, Atom::Len(1), 7); }
        else if b == 2 { lemma_b2(p, c, sums, fr, 4, Atom::Len(1), 7); }
        else { lemma_b3(p, c, sums, fr, 4, Atom::Len(1), 7); }
    }
}

/// `Len` reads through any number of `Shr`.
pub proof fn sanity_len_double_ref(fr: Frame, s: Seq<Val>)
    ensures len_nat(fr, Val::Shr(Box::new(Val::Shr(Box::new(Val::Arr(s)))))) == s.len(),
{
    reveal_with_fuel(shr_len, 3);
}

} // verus!
