//! Sanity facts about `sem`, proved over small crates built here (each builder's `ensures` is the
//! premise of its lemmas, so none is vacuous). Step and event counts are worked by hand from the
//! spec's tables in the comments.
#[allow(unused_imports)]
use crate::json::Json;
use crate::mir::*;
#[cfg(verus_keep_ghost)]
use crate::sem::*;
#[cfg(verus_keep_ghost)]
use ctcore::sem::{binop, read_at, write_at, Event, Frame, Loc, Root, Val, PE};
#[cfg(verus_keep_ghost)]
use ctcore::syntax::{BinOp as COp, IntTy as CTy};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ shapes the builders ensure

pub open spec fn local0(p: Place, l: nat) -> bool { p.local == l && p.projection@.len() == 0 }

pub open spec fn cint(op: Operand, ty: Ty, bs: Seq<Option<u8>>) -> bool {
    op matches Operand::Constant(c) && c.const_.ty == ty
        && (c.const_.kind matches ConstantKind::Allocated(a) && a.bytes@ == bs && a.provenance.ptrs@.len() == 0)
}

pub open spec fn copy_of(op: Operand, l: nat) -> bool { op matches Operand::Copy(p) && local0(p, l) }
pub open spec fn move_of(op: Operand, l: nat) -> bool { op matches Operand::Move(p) && local0(p, l) }

pub open spec fn b1(x: u8) -> Seq<Option<u8>> { seq![Some(x)] }
pub open spec fn b8(x: u8) -> Seq<Option<u8>> { seq![Some(x), Some(0u8), Some(0u8), Some(0u8), Some(0u8), Some(0u8), Some(0u8), Some(0u8)] }

pub open spec fn is_noop(s: Statement) -> bool { s.kind is StorageLive || s.kind is StorageDead }

pub open spec fn assign_bin(s: Statement, dst: nat, op: BinOp) -> bool {
    s.kind matches StatementKind::Assign(p, rv) && local0(p, dst) && (rv matches Rvalue::BinaryOp(o, _, _) && o == op)
}
pub open spec fn bin_x(s: Statement) -> Operand { s.kind->Assign_1->BinaryOp_1 }
pub open spec fn bin_y(s: Statement) -> Operand { s.kind->Assign_1->BinaryOp_2 }

// ------------------------------------------------------------------ exec builders

fn bytes1(x: u8) -> (v: Vec<Option<u8>>) ensures v@ == b1(x) {
    let mut v = Vec::new();
    v.push(Some(x));
    assert(v@ =~= b1(x));
    v
}

fn bytes8(x: u8) -> (v: Vec<Option<u8>>) ensures v@ == b8(x) {
    let mut v = Vec::new();
    v.push(Some(x));
    let mut k: usize = 0;
    while k < 7
        invariant k <= 7, v@.len() == 1 + k, v@[0] == Some(x), forall|j: int| 1 <= j < v@.len() ==> v@[j] == Some(0u8),
        decreases 7 - k,
    {
        v.push(Some(0u8));
        k += 1;
    }
    assert(v@ =~= b8(x));
    v
}

fn place0(l: usize) -> (p: Place) ensures local0(p, l as nat) { Place { local: l, projection: Vec::new() } }

fn place_deref(l: usize) -> (p: Place)
    ensures p.local == l, p.projection@.len() == 1, p.projection@[0] is Deref,
{
    let mut v = Vec::new();
    v.push(ProjectionElem::Deref);
    Place { local: l, projection: v }
}

fn cnst(ty: Ty, bytes: Vec<Option<u8>>) -> (op: Operand) ensures cint(op, ty, bytes@) {
    let a = Allocation { bytes, provenance: ProvenanceMap { ptrs: Vec::new() }, align: 1, mutability: Mutability::Mut };
    Operand::Constant(ConstOperand { span: 0, user_ty: Json::Null, const_: MirConst { kind: ConstantKind::Allocated(a), ty, id: 0 } })
}

fn stmt(kind: StatementKind) -> (s: Statement) ensures s.kind == kind { Statement { kind, span: 0 } }

fn term(kind: TerminatorKind) -> (t: Terminator) ensures t.kind == kind { Terminator { kind, span: 0 } }

fn ldecl(ty: Ty) -> (d: LocalDecl) ensures d.ty == ty { LocalDecl { ty, span: 0, mutability: Mutability::Mut } }

fn uint(id: Ty, u: UintTy) -> (r: TyRow) ensures r.id == id, r.kind == TyKind::RigidTy(RigidTy::Uint(u)) {
    TyRow { id, kind: TyKind::RigidTy(RigidTy::Uint(u)) }
}

fn ref_row(id: Ty, pointee: Ty, mu: Mutability) -> (r: TyRow)
    ensures r.id == id, r.kind matches TyKind::RigidTy(RigidTy::Ref(_, p, m)) && p == pointee && m == mu,
{
    TyRow { id, kind: TyKind::RigidTy(RigidTy::Ref(Json::Null, pointee, mu)) }
}

fn arr_row(id: Ty, elem: Ty) -> (r: TyRow)
    ensures r.id == id, r.kind matches TyKind::RigidTy(RigidTy::Array(e, c)) && e == elem && c.id == 0,
{
    TyRow { id, kind: TyKind::RigidTy(RigidTy::Array(elem, TyConst { kind: Json::Null, id: 0 })) }
}

fn body(blocks: Vec<BasicBlock>, locals: Vec<LocalDecl>, arg_count: usize) -> (b: Body)
    ensures b.blocks@ == blocks@, b.locals@ == locals@, b.arg_count == arg_count, b.spread_arg is None,
{
    Body { blocks, locals, arg_count, var_debug_info: Vec::new(), spread_arg: None, span: 0 }
}

fn inst(id: InstanceDef, b: Body) -> (x: Inst)
    ensures x.id == id, x.kind is Item, x.body matches Some(y) && y == b, x.key@.len() == 0,
{
    Inst { id, def: id, name: Vec::new(), key: Vec::new(), krate: Vec::new(), kind: InstanceKind::Item, body: Some(b), fn_sig: None }
}

fn krate(insts: Vec<Inst>, calls: Vec<Call>, drops: Vec<DropRow>, tys: Vec<TyRow>, adts: Vec<Adt>, layouts: Vec<LayoutRow>) -> (m: MirCrate)
    ensures m.insts@ == insts@, m.calls@ == calls@, m.drops@ == drops@, m.tys@ == tys@, m.adts@ == adts@,
        m.layouts@ == layouts@, m.consts@.len() == 0, m.allocs@.len() == 0,
{
    MirCrate { crate_name: Vec::new(), items: Vec::new(), insts, calls, drops, tys, adts, consts: Vec::new(), layouts, allocs: Vec::new(), spans: Vec::new() }
}

// ================================================================== 1. tiny
//
// tests/data/tiny.rs: `pub fn tiny(a: &[u8; 4], i: usize) -> u8 { let x = [1u8, 2, 3]; a[i & 3] ^ x[1] }`.
// Its dumped MIR (tiny.json, `tiny::tiny`), with the dump's type ids (1 usize, 2 u8, 3 &[u8; 4],
// 7 bool, 9 [u8; 3]); locals _0: u8, _1: &[u8; 4], _2: usize, _3: [u8; 3], _4: u8, _5: usize, _6: bool:
//   bb0: StorageLive(_3); _3 = [const 1u8, const 2u8, const 3u8]; StorageLive(_4); StorageLive(_5);
//        _5 = BitAnd(copy _2, const 3usize); _6 = Lt(copy _5, const 4usize);
//        assert(move _6, true) -> bb1
//   bb1: _4 = copy (*_1)[_5]; _0 = BitXor(move _4, const 2u8); StorageDead(_4); StorageDead(_3);
//        StorageDead(_5); return
// The tables keep the rows the run reads (tys 2, 1, 3).

pub open spec fn tiny_bb0(blk: BasicBlock) -> bool {
    let ss = blk.statements@;
    ss.len() == 6 && is_noop(ss[0]) && is_noop(ss[2]) && is_noop(ss[3])
    && (ss[1].kind matches StatementKind::Assign(p, rv) && local0(p, 3)
        && (rv matches Rvalue::Aggregate(ak, ops) && ak is Array && ops@.len() == 3
            && cint(ops@[0], 2, b1(1)) && cint(ops@[1], 2, b1(2)) && cint(ops@[2], 2, b1(3))))
    && assign_bin(ss[4], 5, BinOp::BitAnd) && copy_of(bin_x(ss[4]), 2) && cint(bin_y(ss[4]), 1, b8(3))
    && assign_bin(ss[5], 6, BinOp::Lt) && copy_of(bin_x(ss[5]), 5) && cint(bin_y(ss[5]), 1, b8(4))
    && (blk.terminator.kind matches TerminatorKind::Assert { cond, expected, target, .. } && move_of(cond, 6) && expected && target == 1)
}

pub open spec fn tiny_bb1(blk: BasicBlock) -> bool {
    let ss = blk.statements@;
    ss.len() == 5 && is_noop(ss[2]) && is_noop(ss[3]) && is_noop(ss[4])
    && (ss[0].kind matches StatementKind::Assign(p, rv) && local0(p, 4)
        && (rv matches Rvalue::Use(x, _) && (x matches Operand::Copy(q) && q.local == 1 && q.projection@.len() == 2
            && q.projection@[0] is Deref && (q.projection@[1] matches ProjectionElem::Index(ix) && ix == 5))))
    && assign_bin(ss[1], 0, BinOp::BitXor) && move_of(bin_x(ss[1]), 4) && cint(bin_y(ss[1]), 2, b1(2))
    && blk.terminator.kind is Return
}

pub open spec fn tiny_ok(m: MirCrate) -> bool {
    m.insts@.len() == 1 && m.insts@[0].kind is Item && m.insts@[0].body is Some && m.allocs@.len() == 0
    && m.consts@.len() == 0 && m.tys@.len() == 6
    && m.tys@[0].id == 2 && (m.tys@[0].kind matches TyKind::RigidTy(RigidTy::Uint(UintTy::U8)))
    && m.tys@[1].id == 1 && (m.tys@[1].kind matches TyKind::RigidTy(RigidTy::Uint(UintTy::Usize)))
    && m.tys@[2].id == 3 && (m.tys@[2].kind matches TyKind::RigidTy(RigidTy::Ref(_, p, mu)) && p == 11 && mu is Not)
    && m.tys@[3].id == 11 && (m.tys@[3].kind matches TyKind::RigidTy(RigidTy::Array(e, _)) && e == 2)
    && m.tys@[4].id == 7 && (m.tys@[4].kind matches TyKind::RigidTy(RigidTy::Bool))
    && m.tys@[5].id == 9 && (m.tys@[5].kind matches TyKind::RigidTy(RigidTy::Array(e, _)) && e == 2)
    && {
        let b = m.insts@[0].body->Some_0;
        b.arg_count == 2 && b.locals@.len() == 7 && b.blocks@.len() == 2
        && b.locals@[0].ty == 2 && b.locals@[1].ty == 3 && b.locals@[2].ty == 1 && b.locals@[3].ty == 9 && b.locals@[4].ty == 2
        && b.locals@[5].ty == 1 && b.locals@[6].ty == 7
        && tiny_bb0(b.blocks@[0]) && tiny_bb1(b.blocks@[1])
    }
}

fn arr3() -> (r: Rvalue)
    ensures r matches Rvalue::Aggregate(ak, ops) && ak is Array && ops@.len() == 3
        && cint(ops@[0], 2, b1(1)) && cint(ops@[1], 2, b1(2)) && cint(ops@[2], 2, b1(3)),
{
    let mut ops = Vec::new();
    ops.push(cnst(2, bytes1(1)));
    ops.push(cnst(2, bytes1(2)));
    ops.push(cnst(2, bytes1(3)));
    Rvalue::Aggregate(AggregateKind::Array(2), ops)
}

fn bin(dst: usize, op: BinOp, x: Operand, y: Operand) -> (s: Statement)
    ensures s.kind matches StatementKind::Assign(p, rv) && local0(p, dst as nat) && rv == Rvalue::BinaryOp(op, x, y),
{
    stmt(StatementKind::Assign(place0(dst), Rvalue::BinaryOp(op, x, y)))
}

pub fn tiny_crate() -> (m: MirCrate) ensures tiny_ok(m) {
    let mut s0 = Vec::new();
    s0.push(stmt(StatementKind::StorageLive(3)));
    s0.push(stmt(StatementKind::Assign(place0(3), arr3())));
    s0.push(stmt(StatementKind::StorageLive(4)));
    s0.push(stmt(StatementKind::StorageLive(5)));
    s0.push(bin(5, BinOp::BitAnd, Operand::Copy(place0(2)), cnst(1, bytes8(3))));
    s0.push(bin(6, BinOp::Lt, Operand::Copy(place0(5)), cnst(1, bytes8(4))));
    let t0 = term(TerminatorKind::Assert { cond: Operand::Move(place0(6)), expected: true, msg: Json::Null, target: 1, unwind: Json::Null });
    let mut proj = Vec::new();
    proj.push(ProjectionElem::Deref);
    proj.push(ProjectionElem::Index(5));
    let mut s1 = Vec::new();
    s1.push(stmt(StatementKind::Assign(place0(4), Rvalue::Use(Operand::Copy(Place { local: 1, projection: proj }), Json::Null))));
    s1.push(bin(0, BinOp::BitXor, Operand::Move(place0(4)), cnst(2, bytes1(2))));
    s1.push(stmt(StatementKind::StorageDead(4)));
    s1.push(stmt(StatementKind::StorageDead(3)));
    s1.push(stmt(StatementKind::StorageDead(5)));
    let mut blocks = Vec::new();
    blocks.push(BasicBlock { statements: s0, terminator: t0 });
    blocks.push(BasicBlock { statements: s1, terminator: term(TerminatorKind::Return) });
    let mut locals = Vec::new();
    locals.push(ldecl(2));
    locals.push(ldecl(3));
    locals.push(ldecl(1));
    locals.push(ldecl(9));
    locals.push(ldecl(2));
    locals.push(ldecl(1));
    locals.push(ldecl(7));
    let mut insts = Vec::new();
    insts.push(inst(0, body(blocks, locals, 2)));
    let mut tys = Vec::new();
    tys.push(uint(2, UintTy::U8));
    tys.push(uint(1, UintTy::Usize));
    tys.push(ref_row(3, 11, Mutability::Not));
    tys.push(arr_row(11, 2));
    tys.push(TyRow { id: 7, kind: TyKind::RigidTy(RigidTy::Bool) });
    tys.push(arr_row(9, 2));
    krate(insts, Vec::new(), Vec::new(), tys, Vec::new(), Vec::new())
}

pub open spec fn tb(m: MirCrate) -> Body { m.insts@[0].body->Some_0 }

proof fn tiny_tys(m: MirCrate)
    requires tiny_ok(m),
    ensures int_ty(m, 2) == Some(CTy::U8), int_ty(m, 1) == Some(CTy::Usize), !is_mut_ref(m, 1), !is_mut_ref(m, 3),
        !charged(m, 1), !charged(m, 2), dfuel(m) == 7, tfuel(m) == 7, int_ty(m, 7) == Some(CTy::Bool),
        rigid(m, 3) matches Some(RigidTy::Ref(_, p, mu)) && p == 11 && mu is Not,
        rigid(m, 11) matches Some(RigidTy::Array(e, _)) && e == 2,
        rigid(m, 9) matches Some(RigidTy::Array(e, _)) && e == 2,
        unit_like(m, 1, 7, false) is None, unit_like(m, 2, 7, false) is None, unit_like(m, 7, 7, false) is None,
        unit_like(m, 9, 7, false) is None,
{
    reveal_with_fuel(find_from, 7);
    assert(unit_like(m, 2, 6, false) is None);
}

/// bb0's `_3 = [1, 2, 3]` is in the subset.
proof fn tiny_s1_ok(m: MirCrate)
    requires tiny_ok(m),
    ensures stmt_ok(m, tb(m), tb(m).blocks@[0].statements@[1]),
{
    let fr = Frame { locals: seq![], slots: seq![] };
    let ops = tb(m).blocks@[0].statements@[1].kind->Assign_1->Aggregate_1@;
    tiny_const(m, fr, ops[0], 1, false);
    tiny_const(m, fr, ops[1], 2, false);
    tiny_const(m, fr, ops[2], 3, false);
    assert(ops_ok(m, tb(m), ops));
}

/// bb0's two `BinaryOp`s on usize, and its `Assert` on a bool, are in the subset.
proof fn tiny_s45_ok(m: MirCrate, pol: CallPolicy)
    requires tiny_ok(m),
    ensures stmt_ok(m, tb(m), tb(m).blocks@[0].statements@[4]), stmt_ok(m, tb(m), tb(m).blocks@[0].statements@[5]),
        term_ok(m, pol, tb(m), tb(m).blocks@[0].terminator.kind),
{
    let fr = Frame { locals: seq![], slots: seq![] };
    let ss0 = tb(m).blocks@[0].statements@;
    tiny_tys(m);
    tiny_const(m, fr, bin_y(ss0[4]), 3, true);
    tiny_const(m, fr, bin_y(ss0[5]), 4, true);
}

/// tiny's bb0 passes the static subset gate.
proof fn tiny_bb0_ok(m: MirCrate, pol: CallPolicy)
    requires tiny_ok(m),
    ensures block_ok(m, pol, tb(m), tb(m).blocks@[0]),
{
    reveal(block_ok);
    let b = tb(m);
    let ss0 = b.blocks@[0].statements@;
    tiny_s1_ok(m);
    tiny_s45_ok(m, pol);
    assert forall|k: int| 0 <= k < ss0.len() implies stmt_ok(m, b, #[trigger] ss0[k]) by {
        if k == 0 || k == 2 || k == 3 { assert(is_noop(ss0[k])); }
    };
}

/// tiny's bb1 passes the static subset gate.
proof fn tiny_bb1_ok(m: MirCrate, pol: CallPolicy)
    requires tiny_ok(m),
    ensures block_ok(m, pol, tb(m), tb(m).blocks@[1]),
{
    reveal(block_ok);
    let b = tb(m);
    let fr = Frame { locals: seq![], slots: seq![] };
    tiny_tys(m);
    let ss1 = b.blocks@[1].statements@;
    tiny_const(m, fr, bin_y(ss1[1]), 2, false);
    let q = ss1[0].kind->Assign_1->Use_0->Copy_0;
    assert(tys_along(m, 3, q.projection@, 0) == Some(3usize));
    assert(proj_ty(m, 3, q.projection@[0]) == Some(11usize));
    assert(tys_along(m, 3, q.projection@, 1) == Some(11usize));
    assert(proj_ok(m, b, 3, q.projection@[0], false));
    assert(proj_ok(m, b, 11, q.projection@[1], false));
    assert(path_ok(m, b, 3, q.projection@, 0, false));
    assert(path_ok(m, b, 3, q.projection@, 1, false));
    assert(path_ok(m, b, 3, q.projection@, 2, false));
    assert(stmt_ok(m, b, ss1[0]));
    assert(stmt_ok(m, b, ss1[1]));
    assert forall|k: int| 0 <= k < ss1.len() implies stmt_ok(m, b, #[trigger] ss1[k]) by {
        if k >= 2 { assert(is_noop(ss1[k])); }
    };
}

proof fn tiny_blocks_ok(m: MirCrate, pol: CallPolicy)
    requires tiny_ok(m),
    ensures block_ok(m, pol, tb(m), tb(m).blocks@[0]), block_ok(m, pol, tb(m), tb(m).blocks@[1]),
{
    tiny_bb0_ok(m, pol);
    tiny_bb1_ok(m, pol);
}

/// A u8 constant (1 byte) or usize constant (8 bytes) evaluates to its value, at no charge.
proof fn tiny_const(m: MirCrate, fr: Frame, op: Operand, x: u8, wide: bool)
    requires tiny_ok(m), if wide { cint(op, 1, b8(x)) } else { cint(op, 2, b1(x)) },
    ensures eval_op(m, fr, op) == Some((Val::Int(x as u128), seq![], 0nat)),
{
    tiny_tys(m);
    reveal_with_fuel(find_from, 7);
    reveal_with_fuel(le, 9);
    let c = op->Constant_0;
    let a = c.const_.kind->Allocated_0;
    if wide {
        assert(le(a, 7, 1) == Some(0nat));
        assert(le(a, 0, 8) == Some(x as nat));
    } else {
        assert(le(a, 0, 1) == Some(x as nat));
    }
}

proof fn tiny_read_local(m: MirCrate, fr: Frame, op: Operand, l: nat)
    requires copy_of(op, l) || move_of(op, l), l < fr.locals.len(),
    ensures eval_op(m, fr, op) == Some((fr.locals[l as int], Seq::<Event>::empty(), 0nat)),
{
}

pub open spec fn put_local(fr: Frame, l: nat, v: Val) -> Frame { Frame { locals: fr.locals.update(l as int, v), slots: fr.slots } }

proof fn tiny_store0(fr: Frame, p: Place, l: nat, v: Val)
    requires local0(p, l), l < fr.locals.len(),
    ensures eval_place(fr, p) == Some((PRes::At(Loc { root: Root::Local(l), path: seq![] }), Seq::<Event>::empty())),
        store(fr, Loc { root: Root::Local(l), path: seq![] }, v) == Some(put_local(fr, l, v)),
{
}

pub open spec fn arr123() -> Val { Val::Arr(seq![Val::Int(1), Val::Int(2), Val::Int(3)]) }

/// `_3 = [1, 2, 3]`: cost 1, no events.
proof fn tiny_s1(m: MirCrate, fr: Frame)
    requires tiny_ok(m), fr.locals.len() == 7,
    ensures exec_stmt(m, tb(m), fr, tb(m).blocks@[0].statements@[1]) == Some((put_local(fr, 3, arr123()), Seq::<Event>::empty(), 1nat)),
{
    reveal(exec_stmt);
    let s = tb(m).blocks@[0].statements@[1];
    let ops = s.kind->Assign_1->Aggregate_1@;
    tiny_const(m, fr, ops[0], 1, false);
    tiny_const(m, fr, ops[1], 2, false);
    tiny_const(m, fr, ops[2], 3, false);
    reveal_with_fuel(eval_ops, 4);
    assert(eval_ops(m, fr, ops, 3) == Some((seq![Val::Int(1), Val::Int(2), Val::Int(3)], Seq::<Event>::empty(), 0nat))) by {
        assert(seq![Val::Int(1)].push(Val::Int(2)).push(Val::Int(3)) =~= seq![Val::Int(1), Val::Int(2), Val::Int(3)]);
        assert(Seq::<Event>::empty() + Seq::<Event>::empty() =~= Seq::<Event>::empty());
    };
    tiny_store0(fr, s.kind->Assign_0, 3, arr123());
    assert(Seq::<Event>::empty() + Seq::<Event>::empty() =~= Seq::<Event>::empty());
}

proof fn tiny_bitand(i: u128)
    requires i < 0x1_0000_0000_0000_0000,
    ensures binop(COp::BitAnd, CTy::Usize, i, 3) == i & 3, i & 3 < 4,
        binop(COp::Lt, CTy::Usize, i & 3, 4) == 1,
{
    reveal(binop);
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
    assert(i & 3 < 4) by (bit_vector);
    assert((i & 3) as int % 0x1_0000_0000_0000_0000 == (i & 3) as int);
    assert(3u128 as int % 0x1_0000_0000_0000_0000 == 3);
    assert((i as int) % 0x1_0000_0000_0000_0000 == i as int);
}

proof fn tiny_xor(x: u128)
    requires x < 256,
    ensures binop(COp::BitXor, CTy::U8, x, 2) == x ^ 2,
{
    reveal(binop);
    vstd::arithmetic::power2::lemma2_to64();
    assert(x ^ 2 < 256) by (bit_vector) requires x < 256;
    assert((x ^ 2) as int % 256 == (x ^ 2) as int);
}

pub open spec fn fr_a(fr: Frame, i: u128) -> Frame {
    put_local(put_local(put_local(fr, 3, arr123()), 5, Val::Int(i & 3)), 6, Val::Int(1))
}

/// `_5 = BitAnd(_2, 3)` and `_6 = Lt(_5, 4)`: cost 1 each, no events.
proof fn tiny_s45(m: MirCrate, fr: Frame, i: u128)
    requires tiny_ok(m), fr.locals.len() == 7, fr.locals[2] == Val::Int(i), i < 0x1_0000_0000_0000_0000,
    ensures
        exec_stmt(m, tb(m), fr, tb(m).blocks@[0].statements@[4]) == Some((put_local(fr, 5, Val::Int(i & 3)), Seq::<Event>::empty(), 1nat)),
        exec_stmt(m, tb(m), put_local(fr, 5, Val::Int(i & 3)), tb(m).blocks@[0].statements@[5])
            == Some((put_local(put_local(fr, 5, Val::Int(i & 3)), 6, Val::Int(1)), Seq::<Event>::empty(), 1nat)),
{
    reveal(exec_stmt);
    tiny_tys(m);
    tiny_bitand(i);
    let b = tb(m);
    let s4 = b.blocks@[0].statements@[4];
    let s5 = b.blocks@[0].statements@[5];
    let f5 = put_local(fr, 5, Val::Int(i & 3));
    tiny_const(m, fr, bin_y(s4), 3, true);
    tiny_read_local(m, fr, bin_x(s4), 2);
    tiny_const(m, f5, bin_y(s5), 4, true);
    tiny_read_local(m, f5, bin_x(s5), 5);
    tiny_store0(fr, s4.kind->Assign_0, 5, Val::Int(i & 3));
    tiny_store0(f5, s5.kind->Assign_0, 6, Val::Int(1));
    assert(Seq::<Event>::empty() + Seq::<Event>::empty() =~= Seq::<Event>::empty());
    assert(place_ty(m, b, bin_x(s4)->Copy_0) == Some(1usize));
    assert(place_ty(m, b, bin_x(s5)->Copy_0) == Some(1usize));
}

/// The StorageLive/StorageDead statements cost 0.
proof fn tiny_noop(m: MirCrate, b: Body, fr: Frame, s: Statement)
    requires is_noop(s),
    ensures exec_stmt(m, b, fr, s) == Some((fr, Seq::<Event>::empty(), 0nat)),
{
    reveal(exec_stmt);
}

/// bb0's statements: 0 + 1 + 0 + 0 + 1 + 1 = 3 steps, no events.
proof fn tiny_bb0_stmts(m: MirCrate, fr: Frame, i: u128)
    requires tiny_ok(m), fr.locals.len() == 7, fr.locals[2] == Val::Int(i), i < 0x1_0000_0000_0000_0000,
    ensures exec_stmts(m, tb(m), fr, tb(m).blocks@[0].statements@, 6) == Some((fr_a(fr, i), Seq::<Event>::empty(), 3nat)),
{
    let b = tb(m);
    let ss = b.blocks@[0].statements@;
    let e = Seq::<Event>::empty();
    assert(e + e =~= e);
    tiny_noop(m, b, fr, ss[0]);
    tiny_s1(m, fr);
    let f1 = put_local(fr, 3, arr123());
    tiny_noop(m, b, f1, ss[2]);
    tiny_noop(m, b, f1, ss[3]);
    tiny_s45(m, f1, i);
    assert(exec_stmts(m, b, fr, ss, 0) == Some((fr, e, 0nat)));
    assert(exec_stmts(m, b, fr, ss, 1) == Some((fr, e, 0nat)));
    assert(exec_stmts(m, b, fr, ss, 2) == Some((f1, e, 1nat)));
    assert(exec_stmts(m, b, fr, ss, 3) == Some((f1, e, 1nat)));
    assert(exec_stmts(m, b, fr, ss, 4) == Some((f1, e, 1nat)));
    assert(exec_stmts(m, b, fr, ss, 5) == Some((put_local(f1, 5, Val::Int(i & 3)), e, 2nat)));
}

/// Reading `(*_1)[_5]` through a shared reference: `Deref` gives the snapshot, `Index` checks the
/// bound and emits `Idx(j)`.
proof fn index_read(fr: Frame, q: Place, a: Seq<Val>, j: u128)
    requires q.local == 1, q.projection@.len() == 2, q.projection@[0] is Deref,
        q.projection@[1] matches ProjectionElem::Index(ix) && ix == 5,
        fr.locals.len() == 7, fr.locals[1] == Val::Shr(Box::new(Val::Arr(a))), fr.locals[5] == Val::Int(j), j < a.len(),
    ensures read_place(fr, q) == Some((a[j as int], seq![Event::Idx(j)])),
{
    let base = PRes::At(Loc { root: Root::Local(1), path: seq![] });
    let ps = q.projection@;
    assert(places(fr, base, ps, 0) == Some((base, Seq::<Event>::empty())));
    assert(proj_step(fr, base, ps[0]) == Some((PRes::Snap(Val::Arr(a)), Seq::<Event>::empty())));
    assert(places(fr, base, ps, 1) == Some((PRes::Snap(Val::Arr(a)), Seq::<Event>::empty())));
    assert(proj_step(fr, PRes::Snap(Val::Arr(a)), ps[1]) == Some((PRes::Snap(a[j as int]), seq![Event::Idx(j)])));
    assert(Seq::<Event>::empty() + seq![Event::Idx(j)] =~= seq![Event::Idx(j)]);
}

/// bb1's `_4 = copy (*_1)[_5]`: reads `a[i & 3]` and emits `Idx(i & 3)`; cost 1.
proof fn tiny_s_index(m: MirCrate, fr: Frame, a: Seq<Val>, j: u128)
    requires tiny_ok(m), fr.locals.len() == 7, fr.locals[1] == Val::Shr(Box::new(Val::Arr(a))), fr.locals[5] == Val::Int(j),
        a.len() == 4, j < 4,
    ensures exec_stmt(m, tb(m), fr, tb(m).blocks@[1].statements@[0]) == Some((put_local(fr, 4, a[j as int]), seq![Event::Idx(j)], 1nat)),
{
    let s = tb(m).blocks@[1].statements@[0];
    let q = s.kind->Assign_1->Use_0->Copy_0;
    let ev = seq![Event::Idx(j)];
    index_read(fr, q, a, j);
    assert(eval_rv(m, tb(m), fr, s.kind->Assign_1) == Some((a[j as int], ev, 0nat)));
    tiny_store0(fr, s.kind->Assign_0, 4, a[j as int]);
    assert(ev + Seq::<Event>::empty() =~= ev);
    reveal(exec_stmt);
}

/// bb1's `_0 = BitXor(move _4, 2)`: cost 1, no events.
proof fn tiny_s_xor(m: MirCrate, fr: Frame, x: u128)
    requires tiny_ok(m), fr.locals.len() == 7, fr.locals[4] == Val::Int(x), x < 256,
    ensures exec_stmt(m, tb(m), fr, tb(m).blocks@[1].statements@[1]) == Some((put_local(fr, 0, Val::Int(x ^ 2)), Seq::<Event>::empty(), 1nat)),
{
    reveal(exec_stmt);
    tiny_tys(m);
    tiny_xor(x);
    let b = tb(m);
    let s = b.blocks@[1].statements@[1];
    tiny_const(m, fr, bin_y(s), 2, false);
    tiny_read_local(m, fr, bin_x(s), 4);
    tiny_store0(fr, s.kind->Assign_0, 0, Val::Int(x ^ 2));
    assert(Seq::<Event>::empty() + Seq::<Event>::empty() =~= Seq::<Event>::empty());
    assert(place_ty(m, b, bin_x(s)->Move_0) == Some(2usize));
}

pub open spec fn fr_b(fr: Frame, a: Seq<Val>, i: u128) -> Frame {
    put_local(put_local(fr, 4, a[(i & 3) as int]), 0, Val::Int(a[(i & 3) as int]->Int_0 ^ 2))
}

/// bb1's statements: 1 + 1 + 0 + 0 + 0 = 2 steps, events `[Idx(i & 3)]`.
proof fn tiny_bb1_stmts(m: MirCrate, fr: Frame, a: Seq<Val>, i: u128)
    requires tiny_ok(m), fr.locals.len() == 7, fr.locals[1] == Val::Shr(Box::new(Val::Arr(a))), fr.locals[5] == Val::Int(i & 3),
        a.len() == 4, i & 3 < 4, a[(i & 3) as int] is Int, a[(i & 3) as int]->Int_0 < 256,
    ensures exec_stmts(m, tb(m), fr, tb(m).blocks@[1].statements@, 5) == Some((fr_b(fr, a, i), seq![Event::Idx(i & 3)], 2nat)),
{
    let b = tb(m);
    let ss = b.blocks@[1].statements@;
    let j = i & 3;
    let e = Seq::<Event>::empty();
    let ev = seq![Event::Idx(j)];
    assert(e + ev =~= ev);
    assert(ev + e =~= ev);
    tiny_s_index(m, fr, a, j);
    let f1 = put_local(fr, 4, a[j as int]);
    tiny_s_xor(m, f1, a[j as int]->Int_0);
    let f2 = fr_b(fr, a, i);
    tiny_noop(m, b, f2, ss[2]);
    tiny_noop(m, b, f2, ss[3]);
    tiny_noop(m, b, f2, ss[4]);
    assert(exec_stmts(m, b, fr, ss, 0) == Some((fr, e, 0nat)));
    assert(exec_stmts(m, b, fr, ss, 1) == Some((f1, ev, 1nat)));
    assert(exec_stmts(m, b, fr, ss, 2) == Some((f2, ev, 2nat)));
    assert(exec_stmts(m, b, fr, ss, 3) == Some((f2, ev, 2nat)));
    assert(exec_stmts(m, b, fr, ss, 4) == Some((f2, ev, 2nat)));
}

pub open spec fn tiny_args(a: Seq<Val>, i: u128) -> Seq<Val> { seq![Val::Shr(Box::new(Val::Arr(a))), Val::Int(i)] }

pub open spec fn tiny_fr0(a: Seq<Val>, i: u128) -> Frame {
    Frame { locals: seq![Val::Unit, Val::Shr(Box::new(Val::Arr(a))), Val::Int(i), Val::Unit, Val::Unit, Val::Unit, Val::Unit], slots: seq![] }
}

proof fn tiny_entry(m: MirCrate, a: Seq<Val>, i: u128)
    requires tiny_ok(m),
    ensures mir_entry(m, 0, tiny_args(a, i), seq![]) == tiny_fr0(a, i),
{
    tiny_tys(m);
    assert(mir_entry(m, 0, tiny_args(a, i), seq![]).locals =~= tiny_fr0(a, i).locals);
}

/// bb1's Return from `fr_b`.
proof fn tiny_ret(m: MirCrate, pol: CallPolicy, fb: Frame, fuel: nat)
    requires tiny_ok(m),
    ensures step_term(m, pol, tb(m), tb(m).blocks@[1].terminator.kind, fb, fuel) == Step::Stop(Out::Done(fb, Seq::<Event>::empty(), 1nat)),
{
}

/// bb1 from `fr_a`: its statements (2 steps, `[Idx(i & 3)]`) then the Return (1 step).
proof fn tiny_run_bb1(m: MirCrate, pol: CallPolicy, a: Seq<Val>, i: u128, fuel: nat)
    requires tiny_ok(m), fuel >= 1, i < 0x1_0000_0000_0000_0000, a.len() == 4,
        forall|k: int| 0 <= k < 4 ==> (#[trigger] a[k]) is Int && a[k]->Int_0 < 256,
    ensures run_block(m, pol, tb(m), 1, fr_a(tiny_fr0(a, i), i), fuel)
        == Out::Done(fr_b(fr_a(tiny_fr0(a, i), i), a, i), seq![Event::Idx(i & 3)], 3nat),
{
    let b = tb(m);
    let fa = fr_a(tiny_fr0(a, i), i);
    let fb = fr_b(fa, a, i);
    let blk = b.blocks@[1];
    tiny_blocks_ok(m, pol);
    tiny_bitand(i);
    assert(a[(i & 3) as int] is Int);
    tiny_bb1_stmts(m, fa, a, i);
    tiny_ret(m, pol, fb, fuel);
    assert(seq![Event::Idx(i & 3)] + Seq::<Event>::empty() =~= seq![Event::Idx(i & 3)]);
    assert(exec_stmts(m, b, fa, blk.statements@, blk.statements@.len()) == Some((fb, seq![Event::Idx(i & 3)], 2nat)));
}

/// bb0's Assert(move _6, true): `_6 == 1`, so `Cond(1)` and on to bb1; cost 1.
proof fn tiny_term0(m: MirCrate, pol: CallPolicy, a: Seq<Val>, i: u128, fuel: nat)
    requires tiny_ok(m),
    ensures step_term(m, pol, tb(m), tb(m).blocks@[0].terminator.kind, fr_a(tiny_fr0(a, i), i), fuel)
        == Step::Jump(1, fr_a(tiny_fr0(a, i), i), seq![Event::Cond(1)], 1nat),
{
    let fa = fr_a(tiny_fr0(a, i), i);
    assert(eval_op(m, fa, tb(m).blocks@[0].terminator.kind->Assert_cond) == Some((Val::Int(1), Seq::<Event>::empty(), 0nat)));
    assert(Seq::<Event>::empty() + seq![Event::Cond(1)] =~= seq![Event::Cond(1)]);
}

/// bb0 then bb1 from tiny's entry frame: 7 steps, `[Cond(1), Idx(i & 3)]`.
proof fn tiny_run_bb0(m: MirCrate, pol: CallPolicy, a: Seq<Val>, i: u128, fuel: nat)
    requires tiny_ok(m), fuel >= 2, i < 0x1_0000_0000_0000_0000, a.len() == 4,
        forall|k: int| 0 <= k < 4 ==> (#[trigger] a[k]) is Int && a[k]->Int_0 < 256,
    ensures run_block(m, pol, tb(m), 0, tiny_fr0(a, i), fuel)
        == Out::Done(fr_b(fr_a(tiny_fr0(a, i), i), a, i), seq![Event::Cond(1), Event::Idx(i & 3)], 7nat),
{
    let b = tb(m);
    let fr0 = tiny_fr0(a, i);
    tiny_blocks_ok(m, pol);
    tiny_bb0_stmts(m, fr0, i);
    tiny_term0(m, pol, a, i, fuel);
    tiny_run_bb1(m, pol, a, i, (fuel - 1) as nat);
    assert(Seq::<Event>::empty() + seq![Event::Cond(1)] + seq![Event::Idx(i & 3)] =~= seq![Event::Cond(1), Event::Idx(i & 3)]);
}

/// **Fact 1.** `tiny(a, i)` returns `a[i & 3] ^ 2`, with events `[Cond(1), Idx(i & 3)]` and 7
/// steps: bb0's 3 assignments (3) + the Assert (1), bb1's 2 assignments (2) + the Return (1);
/// the 3 StorageLive and 3 StorageDead cost 0; the int constants have no charge. Fuel: 2 blocks.
pub proof fn fact_tiny(m: MirCrate, pol: CallPolicy, a: Seq<Val>, i: u128, fuel: nat)
    requires tiny_ok(m), fuel >= 2, i < 0x1_0000_0000_0000_0000, a.len() == 4,
        forall|k: int| 0 <= k < 4 ==> (#[trigger] a[k]) is Int && a[k]->Int_0 < 256,
    ensures mir_run_fn(m, pol, 0, mir_entry(m, 0, tiny_args(a, i), seq![]), fuel) matches Some((f, ev, st))
        && f.locals[0] == Val::Int(a[(i & 3) as int]->Int_0 ^ 2)
        && ev == seq![Event::Cond(1), Event::Idx(i & 3)] && st == 7,
{
    tiny_entry(m, a, i);
    tiny_run_bb0(m, pol, a, i, fuel);
    let fb = fr_b(fr_a(tiny_fr0(a, i), i), a, i);
    assert(mir_run(m, pol, 0, tiny_fr0(a, i), fuel) == Out::Done(fb, seq![Event::Cond(1), Event::Idx(i & 3)], 7nat));
    assert(fb.locals[0] == Val::Int(a[(i & 3) as int]->Int_0 ^ 2));
}

// ================================================================== 2. Drop of a Vec<u8>
//
// `fn f(v: Vec<u8>) { }`-shaped: _1: Vec<u8> (ty 5 = Adt(Vec, [u8, Global])); bb0: drop(_1) -> bb1;
// bb1: return. The `drops` row for ty 5 has a non-empty glue, but `Vec<int>`'s glue is the std-model
// leaf (decision 4): the Drop costs 1 and leaves the frame as it was. Steps: Drop 1 + Return 1 = 2.

pub open spec fn dropc_ok(m: MirCrate) -> bool {
    m.insts@.len() == 1 && m.insts@[0].kind is Item && m.insts@[0].body is Some
    && m.tys@.len() == 2 && m.tys@[0].id == 5
    && (m.tys@[0].kind matches TyKind::RigidTy(RigidTy::Adt(_, ga)) && ga.0@.len() == 2 && (ga.0@[0] matches GenericArgKind::Type(e) && e == 2))
    && m.tys@[1].id == 2 && (m.tys@[1].kind matches TyKind::RigidTy(RigidTy::Uint(UintTy::U8)))
    && m.adts@.len() == 1 && m.adts@[0].ty == 5 && m.adts@[0].name@ == b"std::vec::Vec"@
    && m.drops@.len() == 1 && m.drops@[0].ty == 5 && !m.drops@[0].empty
    && {
        let b = m.insts@[0].body->Some_0;
        b.locals@.len() == 2 && b.locals@[1].ty == 5 && b.blocks@.len() == 2
        && b.blocks@[0].statements@.len() == 0
        && (b.blocks@[0].terminator.kind matches TerminatorKind::Drop { place, target, .. } && local0(place, 1) && target == 1)
        && b.blocks@[1].statements@.len() == 0 && b.blocks@[1].terminator.kind is Return
    }
}

pub fn drop_crate() -> (m: MirCrate) ensures dropc_ok(m) {
    let mut blocks = Vec::new();
    blocks.push(BasicBlock { statements: Vec::new(), terminator: term(TerminatorKind::Drop { place: place0(1), target: 1, unwind: Json::Null }) });
    blocks.push(BasicBlock { statements: Vec::new(), terminator: term(TerminatorKind::Return) });
    let mut locals = Vec::new();
    locals.push(ldecl(10));
    locals.push(ldecl(5));
    let mut insts = Vec::new();
    insts.push(inst(0, body(blocks, locals, 1)));
    let mut ga = Vec::new();
    ga.push(GenericArgKind::Type(2));
    ga.push(GenericArgKind::Type(6));
    let mut tys = Vec::new();
    tys.push(TyRow { id: 5, kind: TyKind::RigidTy(RigidTy::Adt(0, GenericArgs(ga))) });
    tys.push(uint(2, UintTy::U8));
    let name: &[u8] = b"std::vec::Vec";
    let mut adts = Vec::new();
    adts.push(Adt { ty: 5, name: vstd::slice::slice_to_vec(name), kind: AdtKind::Struct, is_box: false, variants: Vec::new() });
    let mut drops = Vec::new();
    drops.push(DropRow { ty: 5, glue: 9, empty: false });
    krate(insts, Vec::new(), drops, tys, adts, Vec::new())
}

/// **Fact 2.** Dropping a `Vec<u8>` local is a no-op on the frame: 2 steps, no events.
pub proof fn fact_drop_vec(m: MirCrate, pol: CallPolicy, fr: Frame, fuel: nat)
    requires dropc_ok(m), fr.locals.len() == 2, fuel >= 2,
    ensures mir_run_fn(m, pol, 0, fr, fuel) == Some((fr, Seq::<Event>::empty(), 2nat)),
{
    let b = m.insts@[0].body->Some_0;
    let e = Seq::<Event>::empty();
    reveal_with_fuel(find_from, 3);
    assert(block_ok(m, pol, b, b.blocks@[0]) && block_ok(m, pol, b, b.blocks@[1])) by { reveal(block_ok); };
    assert(vec_elem(m, 5) == Some(2usize));
    assert(int_ty(m, 2) == Some(CTy::U8));
    assert(vec_int(m, 5));
    assert(place_ty(m, b, b.blocks@[0].terminator.kind->Drop_place) == Some(5usize));
    tiny_store0(fr, b.blocks@[0].terminator.kind->Drop_place, 1, Val::Unit);
    assert(exec_stmts(m, b, fr, b.blocks@[0].statements@, 0) == Some((fr, e, 0nat)));
    assert(step_term(m, pol, b, b.blocks@[0].terminator.kind, fr, fuel) == Step::Jump(1, fr, e, 1nat));
    assert(step_term(m, pol, b, b.blocks@[1].terminator.kind, fr, (fuel - 1) as nat) == Step::Stop(Out::Done(fr, e, 1nat)));
    assert(e + e =~= e);
    assert(run_block(m, pol, b, 1, fr, (fuel - 1) as nat) == Out::Done(fr, e, 1nat));
    assert(e + e + e =~= e);
}

// ================================================================== 3. a niche constant
//
// `Option<NonZeroU8>` (ty 6; NonZeroU8 is ty 7). Its layout, in rustc_public's shape (copied from
// the `Niche` layouts in the T3 dumps, e.g. quic's `Option<_>` with `niche_start: 2`), with the values
// rustc_abi gives this type: the u8 niche is the value 0, so `niche_start: 0`, `niche_variants: 0..=0`
// (None), `untagged_variant: 1` (Some), tag field 0 at byte 0. Byte 0: rel = (0 - 0) mod 2^8 = 0
// <= 0 - 0, so the variant is 0 + 0 = None, which has no fields: `Adt(0, [])`, 1 ADT node.

pub open spec fn niche_ok(m: MirCrate) -> bool {
    m.tys@.len() == 4 && m.allocs@.len() == 0 && m.tys@[0].id == 6 && (m.tys@[0].kind matches TyKind::RigidTy(RigidTy::Adt(_, _)))
    && m.tys@[1].id == 7 && (m.tys@[1].kind matches TyKind::RigidTy(RigidTy::Adt(_, _)))
    && m.tys@[2].id == 8 && (m.tys@[2].kind matches TyKind::RigidTy(RigidTy::Pat(base, _)) && base == 9)
    && m.tys@[3].id == 9 && (m.tys@[3].kind matches TyKind::RigidTy(RigidTy::Uint(UintTy::U8)))
    && m.adts@.len() == 2 && m.adts@[0].ty == 6 && !m.adts@[0].is_box && m.adts@[0].kind is Enum
    && m.adts@[0].variants@.len() == 2 && m.adts@[0].variants@[0].fields@.len() == 0
    && m.adts@[0].variants@[1].fields@.len() == 1 && m.adts@[0].variants@[1].fields@[0] == 7
    && m.adts@[1].ty == 7 && !m.adts@[1].is_box && m.adts@[1].kind is Struct && m.adts@[1].variants@.len() == 1
    && m.adts@[1].variants@[0].fields@.len() == 1 && m.adts@[1].variants@[0].fields@[0] == 8
    && m.layouts@.len() == 2 && m.layouts@[0].ty == 6 && m.layouts@[1].ty == 7
    && (m.layouts@[1].shape.fields matches FieldsShape::Arbitrary { offsets } && offsets@.len() == 1 && offsets@[0].num_bits == 0)
    && (m.layouts@[1].shape.variants matches VariantsShape::Single { index } && index == 0)
    && {
        let l = m.layouts@[0].shape;
        (l.fields matches FieldsShape::Arbitrary { offsets } && offsets@.len() == 1 && offsets@[0].num_bits == 0)
        && (l.variants matches VariantsShape::Multiple { tag, tag_encoding, tag_field, variants }
            && tag_field == 0 && variants@.len() == 2 && variants@[0].offsets@.len() == 0
            && variants@[1].offsets@.len() == 1 && variants@[1].offsets@[0].num_bits == 0
            && (tag matches Scalar::Initialized { value, .. } && (value matches Primitive::Int { length, .. } && length is I8))
            && (tag_encoding matches TagEncoding::Niche { untagged_variant, niche_variants, niche_start }
                && untagged_variant == 1 && niche_variants.start == 0 && niche_variants.end == 0 && niche_start == 0))
    }
}

pub fn niche_crate() -> (m: MirCrate) ensures niche_ok(m) {
    let mut ga = Vec::new();
    ga.push(GenericArgKind::Type(7));
    let mut tys = Vec::new();
    tys.push(TyRow { id: 6, kind: TyKind::RigidTy(RigidTy::Adt(0, GenericArgs(ga))) });
    tys.push(TyRow { id: 7, kind: TyKind::RigidTy(RigidTy::Adt(1, GenericArgs(Vec::new()))) });
    tys.push(TyRow { id: 8, kind: TyKind::RigidTy(RigidTy::Pat(9, Json::Null)) });
    tys.push(uint(9, UintTy::U8));
    let mut f1 = Vec::new();
    f1.push(7);
    let mut nzf = Vec::new();
    nzf.push(8);
    let mut nzv = Vec::new();
    nzv.push(AdtVariant { discr: None, fields: nzf });
    let mut vars = Vec::new();
    vars.push(AdtVariant { discr: Some(0), fields: Vec::new() });
    vars.push(AdtVariant { discr: Some(1), fields: f1 });
    let mut adts = Vec::new();
    adts.push(Adt { ty: 6, name: Vec::new(), kind: AdtKind::Enum, is_box: false, variants: vars });
    adts.push(Adt { ty: 7, name: Vec::new(), kind: AdtKind::Struct, is_box: false, variants: nzv });
    let mut offs = Vec::new();
    offs.push(MachineSize { num_bits: 0 });
    let mut o1 = Vec::new();
    o1.push(MachineSize { num_bits: 0 });
    let mut vf = Vec::new();
    vf.push(VariantFields { offsets: Vec::new() });
    vf.push(VariantFields { offsets: o1 });
    let tag = Scalar::Initialized {
        value: Primitive::Int { length: IntegerLength::I8, signed: false },
        valid_range: WrappingRange { start: 0, end: 255 },
    };
    let enc = TagEncoding::Niche { untagged_variant: 1, niche_variants: RangeInclusive { start: 0, end: 0 }, niche_start: 0 };
    let shape = LayoutShape {
        fields: FieldsShape::Arbitrary { offsets: offs },
        variants: VariantsShape::Multiple { tag, tag_encoding: enc, tag_field: 0, variants: vf },
        abi: Json::Null,
        abi_align: 1,
        size: MachineSize { num_bits: 8 },
    };
    let mut o7 = Vec::new();
    o7.push(MachineSize { num_bits: 0 });
    let nz = LayoutShape {
        fields: FieldsShape::Arbitrary { offsets: o7 },
        variants: VariantsShape::Single { index: 0 },
        abi: Json::Null,
        abi_align: 1,
        size: MachineSize { num_bits: 8 },
    };
    let mut layouts = Vec::new();
    layouts.push(LayoutRow { ty: 6, shape });
    layouts.push(LayoutRow { ty: 7, shape: nz });
    krate(Vec::new(), Vec::new(), Vec::new(), tys, adts, layouts)
}

/// **Fact 3.** The niche constant with byte 0 decodes to `Adt(0, [])` (None), and as an operand
/// costs 1 (one ADT node, decision 7).
pub proof fn fact_niche(m: MirCrate, a: Allocation)
    requires niche_ok(m), a.bytes@ == b1(0), a.provenance.ptrs@.len() == 0,
    ensures decode_const(m, 6, a, 0) == Some(Val::Adt(0, seq![])), dec(m, 6, a, 0, dfuel(m)) == Some((Val::Adt(0, seq![]), 1nat)),
        charged(m, 6),
{
    reveal_with_fuel(le, 2);
    vstd::arithmetic::power2::lemma2_to64();
    let l = m.layouts@[0].shape;
    assert(rigid(m, 6) matches Some(RigidTy::Adt(_, _)));
    assert(adt_row(m, 6) == Some(m.adts@[0]));
    assert(layout(m, 6) == Some(l));
    assert(le(a, 0, 1) == Some(0nat));
    assert(tag_variant(m.adts@[0], l.variants->Multiple_tag_encoding, 0, 8) == Some(0nat));
    assert(adt_sel(m.adts@[0], l, a, 0) == Some((0nat, Seq::<MachineSize>::empty())));
    assert(dfuel(m) == 5);
    assert(dec_adt(m, 6, a, 0, 4) == Some((Val::Adt(0, seq![]), 1nat)));
}

// ================================================================== 4. a call with a `&mut` argument
//
// caller (insts[0]): _0: (), _1: u8, _2: &mut u8 (ty 4)
//   bb0: _2 = &mut _1; _0 = f(move _2) -> bb1        bb1: return
// f (insts[1], key "", resolved through `calls` by fn_ty 8): _0: (), _1: &mut u8
//   bb0: (*_1) = const 7u8; return
// The callee's slot 0 holds the copied-in `_1`; `*_1 = 7` writes the slot; on return slot 0 is
// written back to the caller's `_1`. Steps: `_2 = &mut _1` 1 + the Call 1 + f's (assign 1 +
// return 1) + the caller's return 1 = 5. Events: none. Fuel: the callee runs on fuel - 1.

pub open spec fn callc_ok(m: MirCrate) -> bool {
    m.insts@.len() == 2 && m.insts@[0].id == 0 && m.insts@[1].id == 1 && m.insts@[0].kind is Item && m.insts@[1].kind is Item
    && m.insts@[0].body is Some && m.insts@[1].body is Some && m.insts@[1].key@.len() == 0
    && m.tys@.len() == 3 && m.tys@[0].id == 2 && (m.tys@[0].kind matches TyKind::RigidTy(RigidTy::Uint(UintTy::U8)))
    && m.tys@[1].id == 4 && (m.tys@[1].kind matches TyKind::RigidTy(RigidTy::Ref(_, p, mu)) && p == 2 && mu is Mut)
    && m.tys@[2].id == 10 && (m.tys@[2].kind matches TyKind::RigidTy(RigidTy::Tuple(ts)) && ts@.len() == 0)
    && m.calls@.len() == 1 && m.calls@[0].fn_ty == 8 && m.calls@[0].resolved == Some(1usize) && m.calls@[0].args.0@.len() == 0
    && {
        let c = m.insts@[0].body->Some_0;
        c.arg_count == 1 && c.locals@.len() == 3 && c.locals@[0].ty == 10 && c.locals@[1].ty == 2 && c.locals@[2].ty == 4 && c.blocks@.len() == 2
        && c.blocks@[0].statements@.len() == 1
        && (c.blocks@[0].statements@[0].kind matches StatementKind::Assign(p, rv) && local0(p, 2)
            && (rv matches Rvalue::Ref(_, bk, q) && bk is Mut && local0(q, 1)))
        && (c.blocks@[0].terminator.kind matches TerminatorKind::Call { func, args, destination, target, .. }
            && (func matches Operand::Constant(k) && k.const_.ty == 8) && args@.len() == 1 && move_of(args@[0], 2)
            && local0(destination, 0) && target == Some(1usize))
        && c.blocks@[1].statements@.len() == 0 && c.blocks@[1].terminator.kind is Return
    }
    && {
        let f = m.insts@[1].body->Some_0;
        f.arg_count == 1 && f.locals@.len() == 2 && f.locals@[0].ty == 10 && f.locals@[1].ty == 4 && f.blocks@.len() == 1 && f.spread_arg is None
        && f.blocks@[0].statements@.len() == 1
        && (f.blocks@[0].statements@[0].kind matches StatementKind::Assign(p, rv) && p.local == 1 && p.projection@.len() == 1
            && p.projection@[0] is Deref && (rv matches Rvalue::Use(x, _) && cint(x, 2, b1(7))))
        && f.blocks@[0].terminator.kind is Return
    }
}

fn zst_fn(ty: Ty) -> (op: Operand) ensures op matches Operand::Constant(k) && k.const_.ty == ty && k.const_.kind is ZeroSized {
    Operand::Constant(ConstOperand { span: 0, user_ty: Json::Null, const_: MirConst { kind: ConstantKind::ZeroSized, ty, id: 0 } })
}

pub fn call_crate() -> (m: MirCrate) ensures callc_ok(m) {
    let mut cs = Vec::new();
    cs.push(stmt(StatementKind::Assign(place0(2), Rvalue::Ref(Json::Null, BorrowKind::Mut { kind: Json::Null }, place0(1)))));
    let mut args = Vec::new();
    args.push(Operand::Move(place0(2)));
    let ct = term(TerminatorKind::Call { func: zst_fn(8), args, destination: place0(0), target: Some(1), unwind: Json::Null });
    let mut cb = Vec::new();
    cb.push(BasicBlock { statements: cs, terminator: ct });
    cb.push(BasicBlock { statements: Vec::new(), terminator: term(TerminatorKind::Return) });
    let mut cl = Vec::new();
    cl.push(ldecl(10));
    cl.push(ldecl(2));
    cl.push(ldecl(4));
    let mut fs = Vec::new();
    fs.push(stmt(StatementKind::Assign(place_deref(1), Rvalue::Use(cnst(2, bytes1(7)), Json::Null))));
    let mut fb = Vec::new();
    fb.push(BasicBlock { statements: fs, terminator: term(TerminatorKind::Return) });
    let mut fl = Vec::new();
    fl.push(ldecl(10));
    fl.push(ldecl(4));
    let mut insts = Vec::new();
    insts.push(inst(0, body(cb, cl, 1)));
    insts.push(inst(1, body(fb, fl, 1)));
    let mut calls = Vec::new();
    calls.push(Call { fn_ty: 8, def: 1, def_name: Vec::new(), args: GenericArgs(Vec::new()), resolved: Some(1) });
    let mut tys = Vec::new();
    tys.push(uint(2, UintTy::U8));
    tys.push(ref_row(4, 2, Mutability::Mut));
    tys.push(TyRow { id: 10, kind: TyKind::RigidTy(RigidTy::Tuple(Vec::new())) });
    krate(insts, calls, Vec::new(), tys, Vec::new(), Vec::new())
}

pub open spec fn l1() -> Loc { Loc { root: Root::Local(1), path: seq![] } }
pub open spec fn s0() -> Loc { Loc { root: Root::Slot(0), path: seq![] } }

pub open spec fn cfr_in(x: u128) -> Frame { Frame { locals: seq![unit_val(), Val::Mut(s0())], slots: seq![Val::Int(x)] } }
pub open spec fn cfr_out() -> Frame { Frame { locals: seq![unit_val(), Val::Mut(s0())], slots: seq![Val::Int(7)] } }

/// The callee's `(*_1) = 7`: `_1` holds `Mut(Slot(0))`, so the write lands in slot 0. Cost 1.
proof fn callee_stmt(m: MirCrate, x: u128)
    requires callc_ok(m),
    ensures exec_stmt(m, m.insts@[1].body->Some_0, cfr_in(x), (m.insts@[1].body->Some_0).blocks@[0].statements@[0])
        == Some((cfr_out(), Seq::<Event>::empty(), 1nat)),
{
    let f = m.insts@[1].body->Some_0;
    let fr = cfr_in(x);
    let e = Seq::<Event>::empty();
    let s = f.blocks@[0].statements@[0];
    let p = s.kind->Assign_0;
    assert(e + e =~= e);
    tiny_const_any(m, fr, s.kind->Assign_1->Use_0, 7);
    assert(places(fr, PRes::At(l1()), p.projection@, 0) == Some((PRes::At(l1()), e)));
    assert(eval_place(fr, p) == Some((PRes::At(s0()), e)));
    assert(store(fr, s0(), Val::Int(7)) == Some(cfr_out())) by { assert(fr.slots.update(0, Val::Int(7)) =~= cfr_out().slots); };
    reveal(exec_stmt);
}

/// The callee runs its one block: 1 + the Return's 1 = 2 steps.
proof fn call_callee(m: MirCrate, pol: CallPolicy, x: u128, fuel: nat)
    requires callc_ok(m), fuel >= 1,
    ensures mir_run(m, pol, 1, cfr_in(x), fuel) == Out::Done(cfr_out(), Seq::<Event>::empty(), 2nat),
{
    let f = m.insts@[1].body->Some_0;
    let e = Seq::<Event>::empty();
    assert(e + e =~= e);
    callee_block_ok(m, pol);
    callee_stmt(m, x);
    assert(exec_stmts(m, f, cfr_in(x), f.blocks@[0].statements@, 0) == Some((cfr_in(x), e, 0nat)));
    assert(exec_stmts(m, f, cfr_in(x), f.blocks@[0].statements@, 1) == Some((cfr_out(), e, 1nat)));
    assert(step_term(m, pol, f, f.blocks@[0].terminator.kind, cfr_out(), fuel) == Step::Stop(Out::Done(cfr_out(), e, 1nat)));
    assert(run_block(m, pol, f, 0, cfr_in(x), fuel) == Out::Done(cfr_out(), e, 2nat));
}

/// A u8 constant in a crate whose `tys` has `u8` (id 2) first.
proof fn tiny_const_any(m: MirCrate, fr: Frame, op: Operand, x: u8)
    requires cint(op, 2, b1(x)), m.tys@.len() >= 1, m.tys@[0].id == 2,
        m.tys@[0].kind matches TyKind::RigidTy(RigidTy::Uint(UintTy::U8)),
    ensures eval_op(m, fr, op) == Some((Val::Int(x as u128), Seq::<Event>::empty(), 0nat)),
{
    reveal_with_fuel(le, 2);
    let a = op->Constant_0.const_.kind->Allocated_0;
    assert(rigid(m, 2) matches Some(RigidTy::Uint(UintTy::U8)));
    assert(le(a, 0, 1) == Some(x as nat));
    assert(dfuel(m) > 0) by (nonlinear_arith) requires dfuel(m) == (m.tys@.len() + 1) * (m.allocs@.len() + 1);
}

pub open spec fn call_fr1(x: u128) -> Frame { Frame { locals: seq![unit_val(), Val::Int(x), Val::Mut(l1())], slots: seq![] } }
pub open spec fn call_fr2() -> Frame { Frame { locals: seq![unit_val(), Val::Int(7), Val::Mut(l1())], slots: seq![] } }

/// The empty key names no std-model row.
proof fn call_not_std(m: MirCrate, g: GenericArgs)
    ensures std_model(m, Seq::<u8>::empty(), g) is None,
{
    assert(b"std::vec::Vec::new"@.len() > 0);
    assert(b"std::vec::Vec::with_capacity"@.len() > 0);
    assert(b"std::vec::Vec::push"@.len() > 0);
    assert(b"std::vec::Vec::extend_from_slice"@.len() > 0);
    assert(b"std::vec::Vec::as_slice"@.len() > 0);
    assert(b"std::array::<impl [u8; 16]>::as_slice"@.len() > 0);
    assert(b"std::array::<impl [u8; 32]>::as_slice"@.len() > 0);
    assert(b"std::array::<impl [u8; 64]>::as_slice"@.len() > 0);
    assert(b"std::array::<impl [u8; 128]>::as_slice"@.len() > 0);
    assert(b"std::vec::Vec::len"@.len() > 0);
    assert(b"<std::vec::Vec<u8> as vstd::pervasive::VecAdditionalExecFns<u8>>::set"@.len() > 0);
    assert(b"<std::vec::Vec<(u64, u64)> as std::ops::Index<usize>>::index"@.len() > 0);
    assert(b"vstd::slice::slice_subrange"@.len() > 0);
    assert(b"vstd::slice::slice_to_vec"@.len() > 0);
    assert(b"core::num::<impl u32>::wrapping_add"@.len() > 0);
    assert(b"core::num::<impl u64>::wrapping_sub"@.len() > 0);
    assert(b"vstd::prelude::Ghost::assume_new_fallback"@.len() > 0);
}

/// `()` (ty 10) is unit-like, with the canonical value `Unit`; `u8` and `&mut u8` are not.
proof fn call_unit(m: MirCrate)
    requires callc_ok(m),
    ensures unit_like(m, 10, tfuel(m), false) == Some((unit_val(), 0nat)), unit_like(m, 2, tfuel(m), false) is None,
        unit_like(m, 4, tfuel(m), false) is None, tfuel(m) == 4,
{
    reveal_with_fuel(find_from, 4);
    let ts = (m.tys@[2].kind->RigidTy_0)->Tuple_0@;
    assert(unit_likes(m, ts, 3, 0, false) == Some((Seq::<Val>::empty(), 0nat)));
    assert(tup_val(Seq::<Val>::empty()) == Val::Unit);
}

/// f's signature: returns `()`, takes `&mut u8`.
proof fn callee_sig_ok(m: MirCrate)
    requires callc_ok(m),
    ensures sig_ok(m, m.insts@[1].body->Some_0),
{
    reveal_with_fuel(find_from, 4);
    assert(ty_free(m, 10, 4, false));
    assert(ty_free(m, 2, 3, false));
}

/// f's block passes the static subset gate.
proof fn callee_block_ok(m: MirCrate, pol: CallPolicy)
    requires callc_ok(m),
    ensures block_ok(m, pol, m.insts@[1].body->Some_0, (m.insts@[1].body->Some_0).blocks@[0]),
{
    reveal(block_ok);
    reveal_with_fuel(find_from, 4);
    let f = m.insts@[1].body->Some_0;
    let fs = f.blocks@[0].statements@[0];
    tiny_const_any(m, Frame { locals: seq![], slots: seq![] }, fs.kind->Assign_1->Use_0, 7);
    let ps = (fs.kind->Assign_0).projection@;
    assert(rigid(m, 4) matches Some(RigidTy::Ref(_, p, mu)) && p == 2 && mu is Mut);
    assert(!(rigid(m, 2) matches Some(RigidTy::Str)));
    assert(proj_ty(m, 4, ps[0]) == Some(2usize));
    assert(proj_ok(m, f, 4, ps[0], true));
    assert(path_ok(m, f, 4, ps, 0, true));
    assert(tys_along(m, 4, ps, 0) == Some(4usize));
    assert(path_ok(m, f, 4, ps, 1, true));
    assert(stmt_ok(m, f, fs));
}

/// The caller's two blocks pass the static subset gate.
proof fn caller_blocks_ok(m: MirCrate, pol: CallPolicy)
    requires callc_ok(m), !pol.declassify.contains(Seq::<u8>::empty()), !pol.ghost_unit.contains(Seq::<u8>::empty()),
    ensures block_ok(m, pol, m.insts@[0].body->Some_0, (m.insts@[0].body->Some_0).blocks@[0]),
        block_ok(m, pol, m.insts@[0].body->Some_0, (m.insts@[0].body->Some_0).blocks@[1]),
{
    reveal(block_ok);
    reveal_with_fuel(find_from, 4);
    let c = m.insts@[0].body->Some_0;
    call_not_std(m, m.calls@[0].args);
    callee_sig_ok(m);
    assert(m.insts@[1].key@ =~= Seq::<u8>::empty());
    assert(stmt_ok(m, c, c.blocks@[0].statements@[0]));
    assert(callee_of(m, c.blocks@[0].terminator.kind->Call_func) == Some((1nat, m.calls@[0].args)));
    let args = c.blocks@[0].terminator.kind->Call_args@;
    assert(op_ty(m, c, args[0]) == Some(4usize));
    assert(args_typed(m, c, args, m.insts@[1].body->Some_0));
    assert(term_ok(m, pol, c, c.blocks@[0].terminator.kind));
}

/// Entering f: `_2`'s location passes the `&mut` check, slot 0 gets `_1`'s value `x`.
proof fn call_enter(m: MirCrate, x: u128)
    requires callc_ok(m),
    ensures args_ok(m, m.insts@[1].body->Some_0, call_fr1(x), seq![Val::Mut(l1())]),
        call_slots(m, m.insts@[1].body->Some_0, call_fr1(x), seq![Val::Mut(l1())]) == seq![Val::Int(x)],
        mir_entry(m, 1, seq![Val::Mut(l1())], seq![Val::Int(x)]) == cfr_in(x),
{
    reveal_with_fuel(find_from, 3);
    let f = m.insts@[1].body->Some_0;
    let vs = seq![Val::Mut(l1())];
    assert(is_mut_ref(m, 4));
    assert(arg_ok(m, f, call_fr1(x), vs, 0));
    assert(call_slots(m, f, call_fr1(x), vs) =~= seq![Val::Int(x)]);
    call_unit(m);
    assert(mir_entry(m, 1, vs, seq![Val::Int(x)]).locals =~= cfr_in(x).locals);
}

pub open spec fn call_fw() -> Frame { Frame { locals: seq![unit_val(), Val::Int(7), Val::Mut(l1())], slots: seq![] } }

/// Leaving f: its return value is `Unit` (a `()` body never writes `_0`); slot 0 (7) is written
/// back to the caller's `_1`.
proof fn call_leave(m: MirCrate, x: u128)
    requires callc_ok(m),
    ensures return_to(m, m.insts@[1].body->Some_0, call_fr1(x), seq![Val::Mut(l1())], cfr_out()) == Some((unit_val(), call_fw())),
{
    reveal_with_fuel(find_from, 3);
    let f = m.insts@[1].body->Some_0;
    let fr = call_fr1(x);
    let vs = seq![Val::Mut(l1())];
    assert(is_mut_ref(m, 4));
    assert(write_back(m, f, fr, vs, cfr_out().slots, 0) == Some(fr));
    assert(store(fr, l1(), Val::Int(7)) == Some(call_fw())) by { assert(fr.locals.update(1, Val::Int(7)) =~= call_fw().locals); };
    assert(write_back(m, f, fr, vs, cfr_out().slots, 1) == Some(call_fw()));
}

/// The caller's Call terminator: 1 + the callee's 2 = 3 steps; `_1` is 7 afterwards.
proof fn call_term(m: MirCrate, pol: CallPolicy, x: u128, fuel: nat)
    requires callc_ok(m), fuel >= 2, !pol.declassify.contains(Seq::<u8>::empty()), !pol.ghost_unit.contains(Seq::<u8>::empty()),
    ensures step_term(m, pol, m.insts@[0].body->Some_0, (m.insts@[0].body->Some_0).blocks@[0].terminator.kind, call_fr1(x), fuel)
        == Step::Jump(1, call_fr2(), Seq::<Event>::empty(), 3nat),
{
    let c = m.insts@[0].body->Some_0;
    let t = c.blocks@[0].terminator.kind;
    let fr = call_fr1(x);
    let e = Seq::<Event>::empty();
    let vs = seq![Val::Mut(l1())];
    assert(e + e =~= e);
    assert(callee_of(m, t->Call_func) == Some((1nat, m.calls@[0].args))) by { reveal_with_fuel(find_from, 3); };
    assert(eval_ops(m, fr, t->Call_args@, 1) == Some((vs, e, 0nat))) by {
        reveal_with_fuel(eval_ops, 2);
        assert(seq![].push(Val::Mut(l1())) =~= vs);
    };
    tiny_store0(fr, t->Call_destination, 0, Val::Unit);
    assert(m.insts@[1].key@ =~= Seq::<u8>::empty());
    call_not_std(m, m.calls@[0].args);
    assert(!is_leaf(m, pol, m.insts@[1].key@, m.calls@[0].args));
    call_enter(m, x);
    call_callee(m, pol, x, (fuel - 1) as nat);
    call_leave(m, x);
    let f = m.insts@[1].body->Some_0;
    assert(body_call(m, pol, 1, f, vs, fr, fuel) == Ok::<(Val, Frame, Seq<Event>, nat), Out>((unit_val(), call_fw(), e, 2nat)));
    assert(store(call_fw(), Loc { root: Root::Local(0), path: seq![] }, unit_val()) == Some(call_fr2())) by {
        assert(call_fw().locals.update(0, unit_val()) =~= call_fr2().locals);
    };
}

pub open spec fn call_fr0(x: u128) -> Frame { Frame { locals: seq![unit_val(), Val::Int(x), Val::Unit], slots: seq![] } }

/// The caller's `_2 = &mut _1`: `Mut` of `_1`'s location. Cost 1.
proof fn caller_stmt(m: MirCrate, x: u128)
    requires callc_ok(m),
    ensures exec_stmt(m, m.insts@[0].body->Some_0, call_fr0(x), (m.insts@[0].body->Some_0).blocks@[0].statements@[0])
        == Some((call_fr1(x), Seq::<Event>::empty(), 1nat)),
{
    let c = m.insts@[0].body->Some_0;
    let fr0 = call_fr0(x);
    let s = c.blocks@[0].statements@[0];
    assert(Seq::<Event>::empty() + Seq::<Event>::empty() =~= Seq::<Event>::empty());
    tiny_store0(fr0, s.kind->Assign_1->Ref_2, 1, Val::Unit);
    tiny_store0(fr0, s.kind->Assign_0, 2, Val::Mut(l1()));
    assert(put_local(fr0, 2, Val::Mut(l1())) == call_fr1(x)) by { assert(fr0.locals.update(2, Val::Mut(l1())) =~= call_fr1(x).locals); };
    reveal(exec_stmt);
}

/// **Fact 4.** The `&mut` argument's pointee is copied into the callee's slot, written there, and
/// written back to the caller's `_1` on return: `_1 == 7`, 5 steps, no events.
pub proof fn fact_mut_call(m: MirCrate, pol: CallPolicy, x: u128, fuel: nat)
    requires callc_ok(m), fuel >= 2, !pol.declassify.contains(Seq::<u8>::empty()), !pol.ghost_unit.contains(Seq::<u8>::empty()),
    ensures mir_run_fn(m, pol, 0, mir_entry(m, 0, seq![Val::Int(x)], seq![]), fuel) == Some((call_fr2(), Seq::<Event>::empty(), 5nat)),
        call_fr2().locals[1] == Val::Int(7),
{
    reveal_with_fuel(find_from, 3);
    let c = m.insts@[0].body->Some_0;
    let e = Seq::<Event>::empty();
    assert(e + e =~= e);
    assert(e + e + e =~= e);
    assert(!is_mut_ref(m, 2));
    call_unit(m);
    caller_blocks_ok(m, pol);
    assert(mir_entry(m, 0, seq![Val::Int(x)], seq![]).locals =~= call_fr0(x).locals);
    caller_stmt(m, x);
    assert(exec_stmts(m, c, call_fr0(x), c.blocks@[0].statements@, 0) == Some((call_fr0(x), e, 0nat)));
    assert(exec_stmts(m, c, call_fr0(x), c.blocks@[0].statements@, 1) == Some((call_fr1(x), e, 1nat)));
    call_term(m, pol, x, fuel);
    assert(exec_stmts(m, c, call_fr2(), c.blocks@[1].statements@, 0) == Some((call_fr2(), e, 0nat)));
    assert(step_term(m, pol, c, c.blocks@[1].terminator.kind, call_fr2(), (fuel - 1) as nat) == Step::Stop(Out::Done(call_fr2(), e, 1nat)));
    assert(run_block(m, pol, c, 1, call_fr2(), (fuel - 1) as nat) == Out::Done(call_fr2(), e, 1nat));
    assert(run_block(m, pol, c, 0, call_fr0(x), fuel) == Out::Done(call_fr2(), e, 5nat));
}

// ================================================================== 5. the event order of a projection
//
// `_1[_2][_3]` on a 2-D array: the projections are walked left to right, so the trace is
// `[Idx(i), Idx(j)]` (decision 6), and the place is `_1` at path `[Index(i), Index(j)]`.

pub fn index2_place() -> (p: Place)
    ensures p.local == 1, p.projection@.len() == 2,
        p.projection@[0] matches ProjectionElem::Index(x) && x == 2,
        p.projection@[1] matches ProjectionElem::Index(y) && y == 3,
{
    let mut v = Vec::new();
    v.push(ProjectionElem::Index(2));
    v.push(ProjectionElem::Index(3));
    Place { local: 1, projection: v }
}

/// **Fact 5.**
pub proof fn fact_proj_order(fr: Frame, p: Place, vs: Seq<Val>, ws: Seq<Val>, i: u128, j: u128)
    requires p.local == 1, p.projection@.len() == 2,
        p.projection@[0] matches ProjectionElem::Index(x) && x == 2,
        p.projection@[1] matches ProjectionElem::Index(y) && y == 3,
        fr.locals.len() == 4, fr.locals[1] == Val::Arr(vs), fr.locals[2] == Val::Int(i), fr.locals[3] == Val::Int(j),
        (i as nat) < vs.len(), vs[i as int] == Val::Arr(ws), (j as nat) < ws.len(),
    ensures
        eval_place(fr, p) == Some((PRes::At(Loc { root: Root::Local(1), path: seq![PE::Index(i as nat), PE::Index(j as nat)] }),
            seq![Event::Idx(i), Event::Idx(j)])),
        read_place(fr, p) == Some((ws[j as int], seq![Event::Idx(i), Event::Idx(j)])),
{
    reveal_with_fuel(read_at, 3);
    let e = Seq::<Event>::empty();
    let base = PRes::At(l1());
    let ps = p.projection@;
    let p1 = PRes::At(Loc { root: Root::Local(1), path: seq![PE::Index(i as nat)] });
    let p2 = PRes::At(Loc { root: Root::Local(1), path: seq![PE::Index(i as nat), PE::Index(j as nat)] });
    assert(places(fr, base, ps, 0) == Some((base, e)));
    assert(seq![].push(PE::Index(i as nat)) =~= seq![PE::Index(i as nat)]);
    assert(proj_step(fr, base, ps[0]) == Some((p1, seq![Event::Idx(i)])));
    assert(e + seq![Event::Idx(i)] =~= seq![Event::Idx(i)]);
    assert(places(fr, base, ps, 1) == Some((p1, seq![Event::Idx(i)])));
    assert(read_at(Val::Arr(vs), seq![PE::Index(i as nat)]) == Val::Arr(ws)) by {
        assert(seq![PE::Index(i as nat)].drop_first() =~= Seq::<PE>::empty());
    };
    assert(seq![PE::Index(i as nat)].push(PE::Index(j as nat)) =~= seq![PE::Index(i as nat), PE::Index(j as nat)]);
    assert(proj_step(fr, p1, ps[1]) == Some((p2, seq![Event::Idx(j)])));
    assert(seq![Event::Idx(i)] + seq![Event::Idx(j)] =~= seq![Event::Idx(i), Event::Idx(j)]);
    assert(read_at(Val::Arr(vs), seq![PE::Index(i as nat), PE::Index(j as nat)]) == ws[j as int]) by {
        let q = seq![PE::Index(i as nat), PE::Index(j as nat)];
        assert(q.drop_first() =~= seq![PE::Index(j as nat)]);
        assert(q.drop_first().drop_first() =~= Seq::<PE>::empty());
    };
}

// ------------------------------------------------------------------ 3b. the untagged niche variant
//
// The same `Option<NonZeroU8>` with byte 5: t = 5, rel = (5 - 0) mod 2^8 = 5 > 0 - 0, so the untagged
// variant 1 (Some), whose one field (NonZeroU8, ty 7) sits at offset 0. NonZeroU8 is a struct
// (`Single { index: 0 }`) of one `u8 is 1..` field (ty 8, a pattern over u8, ty 9) at offset 0.
// Value: `Adt(1, [Adt(0, [Int(5)])])`, 2 ADT nodes. Fuel: dfuel = (4 + 1) * (0 + 1) = 5, one level
// per type: 6 (5), 7 (4 via dec_adt; dec at 4), 8 (3), 9 (2).

proof fn niche_inner(m: MirCrate, a: Allocation)
    requires niche_ok(m), a.bytes@ == b1(5), a.provenance.ptrs@.len() == 0,
    ensures dec(m, 7, a, 0, 4) == Some((Val::Adt(0, seq![Val::Int(5)]), 1nat)),
{
    reveal_with_fuel(find_from, 4);
    reveal_with_fuel(le, 2);
    assert(le(a, 0, 1) == Some(5nat));
    assert(dec(m, 9, a, 0, 2) == Some((Val::Int(5), 0nat)));
    assert(dec(m, 8, a, 0, 3) == Some((Val::Int(5), 0nat)));
    let fs = m.adts@[1].variants@[0].fields@;
    let os = (m.layouts@[1].shape.fields)->Arbitrary_offsets@;
    assert(adt_sel(m.adts@[1], m.layouts@[1].shape, a, 0) == Some((0nat, os)));
    assert(dec_fields(m, fs, os, a, 0, 3, 0) == Some((Seq::<Val>::empty(), 0nat)));
    assert(seq![].push(Val::Int(5)) =~= seq![Val::Int(5)]);
    assert(dec_fields(m, fs, os, a, 0, 3, 1) == Some((seq![Val::Int(5)], 0nat)));
    assert(dec_adt(m, 7, a, 0, 3) == Some((Val::Adt(0, seq![Val::Int(5)]), 1nat)));
}

/// **Fact 3b.** Byte 5 decodes to `Some(NonZeroU8(5))` = `Adt(1, [Adt(0, [Int(5)])])`, 2 nodes.
pub proof fn fact_niche_untagged(m: MirCrate, a: Allocation)
    requires niche_ok(m), a.bytes@ == b1(5), a.provenance.ptrs@.len() == 0,
    ensures dec(m, 6, a, 0, dfuel(m)) == Some((Val::Adt(1, seq![Val::Adt(0, seq![Val::Int(5)])]), 2nat)),
{
    reveal_with_fuel(find_from, 4);
    reveal_with_fuel(le, 2);
    vstd::arithmetic::power2::lemma2_to64();
    let l = m.layouts@[0].shape;
    assert(le(a, 0, 1) == Some(5nat));
    assert(tag_variant(m.adts@[0], l.variants->Multiple_tag_encoding, 5, 8) == Some(1nat));
    let os = (l.variants->Multiple_variants)@[1].offsets@;
    assert(adt_sel(m.adts@[0], l, a, 0) == Some((1nat, os)));
    niche_inner(m, a);
    let fs = m.adts@[0].variants@[1].fields@;
    let v = Val::Adt(0, seq![Val::Int(5)]);
    assert(dec_fields(m, fs, os, a, 0, 4, 0) == Some((Seq::<Val>::empty(), 0nat)));
    assert(seq![].push(v) =~= seq![v]);
    assert(dec_fields(m, fs, os, a, 0, 4, 1) == Some((seq![v], 1nat)));
    assert(dfuel(m) == 5);
    assert(dec_adt(m, 6, a, 0, 4) == Some((Val::Adt(1, seq![v]), 2nat)));
}

// ------------------------------------------------------------------ 3c. a `Direct` tag
//
// `enum Code { A(u64) = 3, B(u64) = 7 }`: the layout shape of the fixture `ct_fixtures::fx::Code`
// (T3 dump: tag I64 at offset 0, `Direct`, both variants' field at bit 64, size 128), with the
// discriminants set to 3 and 7 so the tag differs from the variant index. Bytes: tag 7 (LE), then
// 9. t = 7; variant 0 has discr 3 mod 2^64 = 3 != 7, variant 1 has 7 mod 2^64 = 7: variant 1. Its
// u64 field at byte 64 / 8 = 8 is 9. Value `Adt(1, [Int(9)])`, 1 ADT node. dfuel = (2 + 1) * 1 = 3.

pub open spec fn b16(t: u8, x: u8) -> Seq<Option<u8>> { b8(t) + b8(x) }

pub open spec fn direct_ok(m: MirCrate) -> bool {
    m.tys@.len() == 2 && m.allocs@.len() == 0
    && m.tys@[0].id == 12 && (m.tys@[0].kind matches TyKind::RigidTy(RigidTy::Adt(_, _)))
    && m.tys@[1].id == 13 && (m.tys@[1].kind matches TyKind::RigidTy(RigidTy::Uint(UintTy::U64)))
    && m.adts@.len() == 1 && m.adts@[0].ty == 12 && !m.adts@[0].is_box && m.adts@[0].kind is Enum
    && m.adts@[0].variants@.len() == 2 && m.adts@[0].variants@[0].discr == Some(3u128) && m.adts@[0].variants@[1].discr == Some(7u128)
    && m.adts@[0].variants@[1].fields@.len() == 1 && m.adts@[0].variants@[1].fields@[0] == 13
    && m.layouts@.len() == 1 && m.layouts@[0].ty == 12
    && {
        let l = m.layouts@[0].shape;
        (l.fields matches FieldsShape::Arbitrary { offsets } && offsets@.len() == 1 && offsets@[0].num_bits == 0)
        && (l.variants matches VariantsShape::Multiple { tag, tag_encoding, tag_field, variants }
            && tag_field == 0 && variants@.len() == 2 && variants@[1].offsets@.len() == 1 && variants@[1].offsets@[0].num_bits == 64
            && (tag matches Scalar::Initialized { value, .. } && (value matches Primitive::Int { length, .. } && length is I64))
            && tag_encoding is Direct)
    }
}

fn ms(bits: usize) -> (v: Vec<MachineSize>) ensures v@.len() == 1, v@[0].num_bits == bits {
    let mut v = Vec::new();
    v.push(MachineSize { num_bits: bits });
    v
}

pub fn direct_crate() -> (m: MirCrate) ensures direct_ok(m) {
    let mut tys = Vec::new();
    tys.push(TyRow { id: 12, kind: TyKind::RigidTy(RigidTy::Adt(2, GenericArgs(Vec::new()))) });
    tys.push(uint(13, UintTy::U64));
    let mut fa = Vec::new();
    fa.push(13);
    let mut fb = Vec::new();
    fb.push(13);
    let mut vars = Vec::new();
    vars.push(AdtVariant { discr: Some(3), fields: fa });
    vars.push(AdtVariant { discr: Some(7), fields: fb });
    let mut adts = Vec::new();
    adts.push(Adt { ty: 12, name: Vec::new(), kind: AdtKind::Enum, is_box: false, variants: vars });
    let mut vf = Vec::new();
    vf.push(VariantFields { offsets: ms(64) });
    vf.push(VariantFields { offsets: ms(64) });
    let tag = Scalar::Initialized {
        value: Primitive::Int { length: IntegerLength::I64, signed: false },
        valid_range: WrappingRange { start: 3, end: 7 },
    };
    let shape = LayoutShape {
        fields: FieldsShape::Arbitrary { offsets: ms(0) },
        variants: VariantsShape::Multiple { tag, tag_encoding: TagEncoding::Direct, tag_field: 0, variants: vf },
        abi: Json::Null,
        abi_align: 8,
        size: MachineSize { num_bits: 128 },
    };
    let mut layouts = Vec::new();
    layouts.push(LayoutRow { ty: 12, shape });
    krate(Vec::new(), Vec::new(), Vec::new(), tys, adts, layouts)
}

proof fn direct_le(a: Allocation)
    requires a.bytes@ == b16(7, 9), a.provenance.ptrs@.len() == 0,
    ensures le(a, 0, 8) == Some(7nat), le(a, 8, 8) == Some(9nat),
{
    reveal_with_fuel(le, 9);
    assert(le(a, 7, 1) == Some(0nat));
    assert(le(a, 15, 1) == Some(0nat));
}

/// **Fact 3c.** The `Direct`-tagged constant decodes to `Adt(1, [Int(9)])`, 1 node.
pub proof fn fact_direct(m: MirCrate, a: Allocation)
    requires direct_ok(m), a.bytes@ == b16(7, 9), a.provenance.ptrs@.len() == 0,
    ensures dec(m, 12, a, 0, dfuel(m)) == Some((Val::Adt(1, seq![Val::Int(9)]), 1nat)),
{
    reveal_with_fuel(find_from, 3);
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
    direct_le(a);
    let row = m.adts@[0];
    let l = m.layouts@[0].shape;
    let p = |v: AdtVariant| v.discr is Some && (v.discr->Some_0 as int) % (pow2(64) as int) == 7int;
    assert(!p(row.variants@[0]));
    assert(p(row.variants@[1]));
    assert(tag_variant(row, TagEncoding::Direct, 7, 64) == Some(1nat));
    let os = (l.variants->Multiple_variants)@[1].offsets@;
    assert(adt_sel(row, l, a, 0) == Some((1nat, os)));
    assert(rd_int(a, 8, CTy::U64) == Some(9u128));
    assert(dec(m, 13, a, 8, 2) == Some((Val::Int(9), 0nat)));
    let fs = row.variants@[1].fields@;
    assert(dec_fields(m, fs, os, a, 0, 2, 0) == Some((Seq::<Val>::empty(), 0nat)));
    assert(seq![].push(Val::Int(9)) =~= seq![Val::Int(9)]);
    assert(dec_fields(m, fs, os, a, 0, 2, 1) == Some((seq![Val::Int(9)], 0nat)));
    assert(dec_adt(m, 12, a, 0, 2) == Some((Val::Adt(1, seq![Val::Int(9)]), 1nat)));
    assert(dfuel(m) == 3);
}

// ------------------------------------------------------------------ 3d. a `&str` constant
//
// `&str` (ty 20 = `&'static str`, ty 21 = `str`) decodes to the opaque `Unit`, whatever its bytes,
// with no charge (`str` is unsized, so `&str` is not `&ZST`), and `Unit` is a well-typed `&str`.

pub open spec fn str_ok(m: MirCrate) -> bool {
    m.tys@.len() == 2 && m.allocs@.len() == 1 && m.allocs@[0].id == 12 && m.allocs@[0].alloc is Memory
    && m.tys@[0].id == 20 && (m.tys@[0].kind matches TyKind::RigidTy(RigidTy::Ref(_, p, mu)) && p == 21 && mu is Not)
    && m.tys@[1].id == 21 && (m.tys@[1].kind matches TyKind::RigidTy(RigidTy::Str))
}

pub fn str_crate() -> (m: MirCrate) ensures str_ok(m) {
    let mut tys = Vec::new();
    tys.push(ref_row(20, 21, Mutability::Not));
    tys.push(TyRow { id: 21, kind: TyKind::RigidTy(RigidTy::Str) });
    let target = Allocation { bytes: bytes1(101), provenance: ProvenanceMap { ptrs: Vec::new() }, align: 1, mutability: Mutability::Not };
    let mut allocs = Vec::new();
    allocs.push(AllocRow { id: 12, alloc: GlobalAlloc::Memory(target) });
    MirCrate {
        crate_name: Vec::new(), items: Vec::new(), insts: Vec::new(), calls: Vec::new(), drops: Vec::new(), tys,
        adts: Vec::new(), consts: Vec::new(), layouts: Vec::new(), allocs, spans: Vec::new(),
    }
}

/// An allocation of `bytes` with one pointer at offset 0 into alloc `id`.
fn alloc_ptr(bytes: Vec<Option<u8>>, id: AllocId) -> (a: Allocation)
    ensures a.bytes@ == bytes@, a.provenance.ptrs@ == seq![(0usize, id)],
{
    let mut ptrs = Vec::new();
    ptrs.push((0usize, id));
    assert(ptrs@ =~= seq![(0usize, id)]);
    Allocation { bytes, provenance: ProvenanceMap { ptrs }, align: 8, mutability: Mutability::Mut }
}

/// A `&str` constant as rustc writes it: 16 bytes, pointer at 0 with provenance into alloc 12.
pub fn str_const_alloc() -> (a: Allocation) ensures a.provenance.ptrs@ == seq![(0usize, 12usize)] {
    let mut b = bytes8(0);
    let mut l = bytes8(1);
    b.append(&mut l);
    alloc_ptr(b, 12)
}

proof fn prov_none(a: Allocation, off: nat)
    requires a.provenance.ptrs@.len() == 0,
    ensures prov_at(a, off) is None,
{
    assert(find_from(a.provenance.ptrs@, |e: (usize, AllocId)| e.0 as nat == off, 0) is None);
}

/// **Fact 3d.**
pub proof fn fact_str(m: MirCrate, a: Allocation)
    requires str_ok(m), a.provenance.ptrs@.len() == 0,
    ensures decode_const(m, 20, a, 0) == Some(Val::Unit), !charged(m, 20), wt_val(m, 20, Val::Unit),
{
    reveal_with_fuel(find_from, 3);
    prov_none(a, 0);
    assert(dfuel(m) == 6) by (nonlinear_arith) requires dfuel(m) == (m.tys@.len() + 1) * (m.allocs@.len() + 1), m.tys@.len() == 2, m.allocs@.len() == 1;
    assert(dec_ref(m, 21, a, 0, 5) == Some((Val::Unit, 0nat)));
    assert(dec(m, 20, a, 0, 6) == Some((Val::Unit, 0nat)));
    assert(!is_zst(m, 21));
    assert(m.tys@[0].id == 20 && m.tys@[1].id == 21);
    assert(ty_kind(m, 21) == Some(m.tys@[1].kind));
    assert(rigid(m, 21) matches Some(RigidTy::Str));
    assert(rigid(m, 20) matches Some(RigidTy::Ref(_, p, mu)) && p == 21 && mu is Not);
    assert(ty_free(m, 21, 2, false));
    assert(ty_free(m, 20, 3, true));
}

/// **Fact 3e.** A `&str` constant with provenance into a `GlobalAlloc::Memory` (alloc 12) is the
/// opaque `Unit` too.
pub proof fn fact_str_prov(m: MirCrate, a: Allocation)
    requires str_ok(m), a.provenance.ptrs@ == seq![(0usize, 12usize)],
    ensures decode_const(m, 20, a, 0) == Some(Val::Unit),
{
    reveal_with_fuel(find_from, 3);
    assert(prov_at(a, 0) == Some(12usize));
    assert(alloc_mem(m, 12) is Some);
    assert(dfuel(m) == 6) by (nonlinear_arith) requires dfuel(m) == (m.tys@.len() + 1) * (m.allocs@.len() + 1), m.tys@.len() == 2, m.allocs@.len() == 1;
    assert(m.tys@[0].id == 20 && m.tys@[1].id == 21);
    assert(rigid(m, 21) matches Some(RigidTy::Str));
    assert(dec_ref(m, 21, a, 0, 5) == Some((Val::Unit, 0nat)));
    assert(dec(m, 20, a, 0, 6) == Some((Val::Unit, 0nat)));
}

// ------------------------------------------------------------------ 3f. a pointer niche tag
//
// `None::<&str>` from `pos_str_unit` bb2 (fixtures dump, ty 240 = `Option<&str>`): the layout copied
// from the dump, tag `Initialized { Pointer(0) }` at offset 0, `Niche { untagged 1, 0..=0, start 0 }`.
// Bytes: 8 zero bytes, then 8 uninitialized (the absent length). Tag width 8 (a pointer), no
// provenance on it: t = 0, rel = (0 - 0) mod 2^64 = 0 <= 0, so variant 0 (None), no fields:
// `Adt(0, [])`, 1 node. dfuel = (3 + 1) * (0 + 1) = 4. With provenance on the tag (a real
// pointer, as in `neg_const_pointer_tag`), `no_prov` fails and the constant does not decode.

pub open spec fn b8u() -> Seq<Option<u8>> { seq![None, None, None, None, None, None, None, None] }

pub open spec fn optref_ok(m: MirCrate) -> bool {
    m.tys@.len() == 3 && m.allocs@.len() == 0
    && m.tys@[0].id == 240 && (m.tys@[0].kind matches TyKind::RigidTy(RigidTy::Adt(_, _)))
    && m.adts@.len() == 1 && m.adts@[0].ty == 240 && !m.adts@[0].is_box && m.adts@[0].kind is Enum
    && m.adts@[0].variants@.len() == 2 && m.adts@[0].variants@[0].fields@.len() == 0
    && m.layouts@.len() == 1 && m.layouts@[0].ty == 240
    && {
        let l = m.layouts@[0].shape;
        (l.fields matches FieldsShape::Arbitrary { offsets } && offsets@.len() == 1 && offsets@[0].num_bits == 0)
        && (l.variants matches VariantsShape::Multiple { tag, tag_encoding, tag_field, variants }
            && tag_field == 0 && variants@.len() == 2 && variants@[0].offsets@.len() == 0
            && (tag matches Scalar::Initialized { value, .. } && value is Pointer)
            && (tag_encoding matches TagEncoding::Niche { untagged_variant, niche_variants, niche_start }
                && untagged_variant == 1 && niche_variants.start == 0 && niche_variants.end == 0 && niche_start == 0))
    }
}

pub fn optref_crate() -> (m: MirCrate) ensures optref_ok(m) {
    let mut ga = Vec::new();
    ga.push(GenericArgKind::Type(130));
    let mut tys = Vec::new();
    tys.push(TyRow { id: 240, kind: TyKind::RigidTy(RigidTy::Adt(141, GenericArgs(ga))) });
    tys.push(ref_row(130, 394, Mutability::Not));
    tys.push(TyRow { id: 394, kind: TyKind::RigidTy(RigidTy::Str) });
    let mut f1 = Vec::new();
    f1.push(130);
    let mut vars = Vec::new();
    vars.push(AdtVariant { discr: Some(0), fields: Vec::new() });
    vars.push(AdtVariant { discr: Some(1), fields: f1 });
    let mut adts = Vec::new();
    adts.push(Adt { ty: 240, name: Vec::new(), kind: AdtKind::Enum, is_box: false, variants: vars });
    let mut vf = Vec::new();
    vf.push(VariantFields { offsets: Vec::new() });
    vf.push(VariantFields { offsets: ms(0) });
    let tag = Scalar::Initialized { value: Primitive::Pointer(0), valid_range: WrappingRange { start: 0, end: 18446744073709551615 } };
    let enc = TagEncoding::Niche { untagged_variant: 1, niche_variants: RangeInclusive { start: 0, end: 0 }, niche_start: 0 };
    let shape = LayoutShape {
        fields: FieldsShape::Arbitrary { offsets: ms(0) },
        variants: VariantsShape::Multiple { tag, tag_encoding: enc, tag_field: 0, variants: vf },
        abi: Json::Null,
        abi_align: 8,
        size: MachineSize { num_bits: 128 },
    };
    let mut layouts = Vec::new();
    layouts.push(LayoutRow { ty: 240, shape });
    krate(Vec::new(), Vec::new(), Vec::new(), tys, adts, layouts)
}

proof fn le_zero8(a: Allocation)
    requires a.bytes@.len() == 16, forall|k: int| 0 <= k < 8 ==> a.bytes@[k] == Some(0u8),
    ensures le(a, 0, 8) == Some(0nat),
{
    reveal_with_fuel(le, 9);
    assert(le(a, 8, 0) == Some(0nat));
    assert(le(a, 7, 1) == Some(0nat));
}

/// **Fact 3f.** `None::<&str>` (null pointer tag, no provenance) decodes to variant 0, 1 node; the
/// same bytes with provenance on the tag do not decode.
pub proof fn fact_none_ref(m: MirCrate, a: Allocation, p: Allocation)
    requires optref_ok(m), a.bytes@ == b8(0) + b8u(), a.provenance.ptrs@.len() == 0,
        p.bytes@ == b8(0) + b8u(), p.provenance.ptrs@ == seq![(0usize, 12usize)],
    ensures dec(m, 240, a, 0, dfuel(m)) == Some((Val::Adt(0, seq![]), 1nat)), dec(m, 240, p, 0, dfuel(m)) is None,
{
    reveal_with_fuel(find_from, 2);
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
    let l = m.layouts@[0].shape;
    le_zero8(a);
    assert(tag_bytes((l.variants->Multiple_tag)->Initialized_value) == Some(8nat));
    assert(tag_variant(m.adts@[0], l.variants->Multiple_tag_encoding, 0, 64) == Some(0nat));
    assert(adt_sel(m.adts@[0], l, a, 0) == Some((0nat, Seq::<MachineSize>::empty())));
    assert(dfuel(m) == 4);
    assert(dec_adt(m, 240, a, 0, 3) == Some((Val::Adt(0, seq![]), 1nat)));
    assert(!no_prov(p, 0, 8)) by { assert(p.provenance.ptrs@[0].0 == 0usize); };
    assert(adt_sel(m.adts@[0], l, p, 0) is None);
    assert(dec_adt(m, 240, p, 0, 3) is None);
}

// ------------------------------------------------------------------ 3g. an empty-array reference
//
// `&[u8; 0]` (crypto::sha256::sha256 has one): `[u8; 0]` (ty 41) is a ZST (layout size 0) whose one
// value is `Arr([])`, whatever the element type, so the constant is `Shr(Arr([]))`, and as an
// `&ZST` it costs 1 (one reference node, decision 7).

pub open spec fn empty_ok(m: MirCrate) -> bool {
    m.tys@.len() == 3 && m.allocs@.len() == 0
    && m.tys@[0].id == 40 && (m.tys@[0].kind matches TyKind::RigidTy(RigidTy::Ref(_, p, mu)) && p == 41 && mu is Not)
    && m.tys@[1].id == 41 && (m.tys@[1].kind matches TyKind::RigidTy(RigidTy::Array(e, c)) && e == 2 && c.id == 0)
    && m.tys@[2].id == 2 && (m.tys@[2].kind matches TyKind::RigidTy(RigidTy::Uint(UintTy::U8)))
    && m.consts@.len() == 1 && m.consts@[0].id == 0 && m.consts@[0].usize == Some(0u64)
    && m.layouts@.len() == 1 && m.layouts@[0].ty == 41 && m.layouts@[0].shape.size.num_bits == 0
}

pub fn empty_crate() -> (m: MirCrate) ensures empty_ok(m) {
    let mut tys = Vec::new();
    tys.push(ref_row(40, 41, Mutability::Not));
    tys.push(arr_row(41, 2));
    tys.push(uint(2, UintTy::U8));
    let mut consts = Vec::new();
    consts.push(ConstRow { id: 0, usize: Some(0) });
    let shape = LayoutShape {
        fields: FieldsShape::Array { stride: MachineSize { num_bits: 8 }, count: 0 },
        variants: VariantsShape::Single { index: 0 },
        abi: Json::Null,
        abi_align: 1,
        size: MachineSize { num_bits: 0 },
    };
    let mut layouts = Vec::new();
    layouts.push(LayoutRow { ty: 41, shape });
    MirCrate {
        crate_name: Vec::new(), items: Vec::new(), insts: Vec::new(), calls: Vec::new(), drops: Vec::new(), tys,
        adts: Vec::new(), consts, layouts, allocs: Vec::new(), spans: Vec::new(),
    }
}

/// **Fact 3g.**
pub proof fn fact_empty_array_ref(m: MirCrate, a: Allocation)
    requires empty_ok(m), a.bytes@ == b8(1), a.provenance.ptrs@.len() == 0,
    ensures dec(m, 40, a, 0, dfuel(m)) == Some((Val::Shr(Box::new(Val::Arr(seq![]))), 1nat)), charged(m, 40),
{
    reveal_with_fuel(find_from, 4);
    reveal_with_fuel(le, 9);
    prov_none(a, 0);
    assert(le(a, 7, 1) == Some(0nat));
    assert(le(a, 0, 8) is Some);
    assert(is_zst(m, 41));
    assert(const_usize(m, 0) == Some(0u64));
    assert(tfuel(m) == 4);
    assert(unit_like(m, 41, 4, true) == Some((Val::Arr(seq![]), 0nat)));
    assert(dfuel(m) == 4) by (nonlinear_arith) requires dfuel(m) == (m.tys@.len() + 1) * (m.allocs@.len() + 1), m.tys@.len() == 3, m.allocs@.len() == 0;
    assert(rigid(m, 41) matches Some(RigidTy::Array(_, _)));
    assert(rigid(m, 40) matches Some(RigidTy::Ref(_, p, mu)) && p == 41 && mu is Not);
    assert(dec_ref(m, 41, a, 0, 3) == Some((Val::Shr(Box::new(Val::Arr(seq![]))), 1nat)));
}

// ------------------------------------------------------------------ 4b. call event order, ghost results
//
// One body (insts[0]): _0: (), _1: [u8; 4] (ty 11), _2: usize, _3: u8, _4: G (ty 30).
//   bb0: _1[_2] = d(copy _3) -> bb1      (d = insts[1], key "": a `declassify` policy key)
//   bb1: _4 = g() -> bb2                 (g = insts[2], key "g": a `ghost` policy key)
//   bb2: return
// G is `struct G(PhantomData)` (tys 30, 31) with no layout row, like vstd's `Ghost<_>`.
// bb0's Call: the argument has no events, the row emits `Declass(x)`, then the destination's
// `Index` emits `Idx(i)`: `[Declass(x), Idx(i)]` (decision 6: destination last); cost 1; `_1[i] = x`.
// bb1's Call: `zst_dest(G)` holds (sized, unit-like without closures, no layout row), so `_4` gets
// G's one value `Adt(0, [Adt(0, [])])`; no events; cost 1.

pub open spec fn g_key() -> Seq<u8> { seq![103u8] }

pub open spec fn order_ok(m: MirCrate) -> bool {
    m.insts@.len() == 3 && m.insts@[0].kind is Item && m.insts@[0].body is Some
    && m.insts@[1].id == 1 && m.insts@[1].key@.len() == 0 && m.insts@[2].id == 2 && m.insts@[2].key@ == g_key()
    && m.insts@[0].id == 0
    && m.tys@.len() == 2 && m.tys@[0].id == 30 && (m.tys@[0].kind matches TyKind::RigidTy(RigidTy::Adt(_, _)))
    && m.tys@[1].id == 31 && (m.tys@[1].kind matches TyKind::RigidTy(RigidTy::Adt(_, _)))
    && m.adts@.len() == 2 && m.adts@[0].ty == 30 && m.adts@[1].ty == 31
    && !m.adts@[0].is_box && m.adts@[0].kind is Struct && m.adts@[0].variants@.len() == 1
    && m.adts@[0].variants@[0].fields@.len() == 1 && m.adts@[0].variants@[0].fields@[0] == 31
    && !m.adts@[1].is_box && m.adts@[1].kind is Struct && m.adts@[1].variants@.len() == 1 && m.adts@[1].variants@[0].fields@.len() == 0
    && m.layouts@.len() == 0
    && m.calls@.len() == 2 && m.calls@[0].fn_ty == 8 && m.calls@[0].resolved == Some(1usize)
    && m.calls@[1].fn_ty == 9 && m.calls@[1].resolved == Some(2usize)
    && {
        let b = m.insts@[0].body->Some_0;
        b.locals@.len() == 5 && b.locals@[4].ty == 30 && b.blocks@.len() == 3
        && (b.blocks@[0].terminator.kind matches TerminatorKind::Call { func, args, destination, target, .. }
            && (func matches Operand::Constant(k) && k.const_.ty == 8) && args@.len() == 1 && copy_of(args@[0], 3)
            && destination.local == 1 && destination.projection@.len() == 1
            && (destination.projection@[0] matches ProjectionElem::Index(x) && x == 2) && target == Some(1usize))
        && (b.blocks@[1].terminator.kind matches TerminatorKind::Call { func, args, destination, target, .. }
            && (func matches Operand::Constant(k) && k.const_.ty == 9) && args@.len() == 0 && local0(destination, 4)
            && target == Some(2usize))
    }
}

fn call_to(fn_ty: Ty, args: Vec<Operand>, dest: Place, target: usize) -> (t: TerminatorKind)
    ensures t matches TerminatorKind::Call { func, args: a, destination, target: tg, .. }
        && (func matches Operand::Constant(k) && k.const_.ty == fn_ty) && a@ == args@ && destination == dest && tg == Some(target),
{
    TerminatorKind::Call { func: zst_fn(fn_ty), args, destination: dest, target: Some(target), unwind: Json::Null }
}

fn bare_inst(id: InstanceDef, key: Vec<u8>) -> (x: Inst) ensures x.id == id, x.key@ == key@ {
    Inst { id, def: id, name: Vec::new(), key, krate: Vec::new(), kind: InstanceKind::Item, body: None, fn_sig: None }
}

pub fn order_crate() -> (m: MirCrate) ensures order_ok(m) {
    let mut a0 = Vec::new();
    a0.push(Operand::Copy(place0(3)));
    let mut proj = Vec::new();
    proj.push(ProjectionElem::Index(2));
    let mut blocks = Vec::new();
    blocks.push(BasicBlock { statements: Vec::new(), terminator: term(call_to(8, a0, Place { local: 1, projection: proj }, 1)) });
    blocks.push(BasicBlock { statements: Vec::new(), terminator: term(call_to(9, Vec::new(), place0(4), 2)) });
    blocks.push(BasicBlock { statements: Vec::new(), terminator: term(TerminatorKind::Return) });
    let mut locals = Vec::new();
    locals.push(ldecl(10));
    locals.push(ldecl(11));
    locals.push(ldecl(1));
    locals.push(ldecl(2));
    locals.push(ldecl(30));
    let mut insts = Vec::new();
    insts.push(inst(0, body(blocks, locals, 0)));
    insts.push(bare_inst(1, Vec::new()));
    let mut gk = Vec::new();
    gk.push(103u8);
    assert(gk@ =~= g_key());
    insts.push(bare_inst(2, gk));
    let mut calls = Vec::new();
    calls.push(Call { fn_ty: 8, def: 1, def_name: Vec::new(), args: GenericArgs(Vec::new()), resolved: Some(1) });
    calls.push(Call { fn_ty: 9, def: 2, def_name: Vec::new(), args: GenericArgs(Vec::new()), resolved: Some(2) });
    let mut gf = Vec::new();
    gf.push(31);
    let mut gv = Vec::new();
    gv.push(AdtVariant { discr: None, fields: gf });
    let mut pv = Vec::new();
    pv.push(AdtVariant { discr: None, fields: Vec::new() });
    let mut adts = Vec::new();
    adts.push(Adt { ty: 30, name: Vec::new(), kind: AdtKind::Struct, is_box: false, variants: gv });
    adts.push(Adt { ty: 31, name: Vec::new(), kind: AdtKind::Struct, is_box: false, variants: pv });
    let mut tys = Vec::new();
    tys.push(TyRow { id: 30, kind: TyKind::RigidTy(RigidTy::Adt(3, GenericArgs(Vec::new()))) });
    tys.push(TyRow { id: 31, kind: TyKind::RigidTy(RigidTy::Adt(4, GenericArgs(Vec::new()))) });
    krate(insts, calls, Vec::new(), tys, adts, Vec::new())
}

pub open spec fn order_fr(a: Seq<Val>, i: u128, x: u128, g: Val) -> Frame {
    Frame { locals: seq![unit_val(), Val::Arr(a), Val::Int(i), Val::Int(x), g], slots: seq![] }
}

/// **Fact 4b.** The declassify call with an `Index` destination: `[Declass(Int(x)), Idx(i)]`.
pub proof fn fact_call_order(m: MirCrate, pol: CallPolicy, a: Seq<Val>, i: u128, x: u128, g: Val, fuel: nat)
    requires order_ok(m), pol.declassify.contains(Seq::<u8>::empty()), (i as nat) < a.len(),
    ensures step_term(m, pol, m.insts@[0].body->Some_0, (m.insts@[0].body->Some_0).blocks@[0].terminator.kind, order_fr(a, i, x, g), fuel)
        == Step::Jump(1, order_fr(a.update(i as int, Val::Int(x)), i, x, g), seq![Event::Declass(Val::Int(x)), Event::Idx(i)], 1nat),
{
    reveal_with_fuel(find_from, 3);
    reveal_with_fuel(eval_ops, 2);
    reveal_with_fuel(write_at, 2);
    let b = m.insts@[0].body->Some_0;
    let t = b.blocks@[0].terminator.kind;
    let fr = order_fr(a, i, x, g);
    let e = Seq::<Event>::empty();
    let dest = t->Call_destination;
    assert(callee_of(m, t->Call_func) == Some((1nat, m.calls@[0].args)));
    assert(m.insts@[1].key@ =~= Seq::<u8>::empty());
    assert(eval_ops(m, fr, t->Call_args@, 1) == Some((seq![Val::Int(x)], e, 0nat))) by {
        assert(seq![].push(Val::Int(x)) =~= seq![Val::Int(x)]);
        assert(e + e =~= e);
    };
    let l = Loc { root: Root::Local(1), path: seq![PE::Index(i as nat)] };
    assert(places(fr, PRes::At(Loc { root: Root::Local(1), path: seq![] }), dest.projection@, 0)
        == Some((PRes::At(Loc { root: Root::Local(1), path: seq![] }), e)));
    assert(seq![].push(PE::Index(i as nat)) =~= seq![PE::Index(i as nat)]);
    assert(e + seq![Event::Idx(i)] =~= seq![Event::Idx(i)]);
    assert(eval_place(fr, dest) == Some((PRes::At(l), seq![Event::Idx(i)])));
    assert(write_at(Val::Arr(a), seq![PE::Index(i as nat)], Val::Int(x)) == Val::Arr(a.update(i as int, Val::Int(x)))) by {
        assert(seq![PE::Index(i as nat)].drop_first() =~= Seq::<PE>::empty());
    };
    let fr2 = order_fr(a.update(i as int, Val::Int(x)), i, x, g);
    assert(store(fr, l, Val::Int(x)) == Some(fr2)) by { assert(fr.locals.update(1, Val::Arr(a.update(i as int, Val::Int(x)))) =~= fr2.locals); };
    assert(e + seq![Event::Declass(Val::Int(x))] + seq![Event::Idx(i)] =~= seq![Event::Declass(Val::Int(x)), Event::Idx(i)]);
}

pub open spec fn g_val() -> Val { Val::Adt(0, seq![Val::Adt(0, seq![])]) }

/// G (ty 30) is a ghost-result type: `zst_dest` holds although it has no layout row, and its value
/// is `Adt(0, [Adt(0, [])])`.
proof fn order_g(m: MirCrate)
    requires order_ok(m),
    ensures zst_dest(m, 30), unit_like(m, 30, tfuel(m), false) == Some((g_val(), 2nat)), !is_zst(m, 30), !ul_arr(m, 30),
{
    reveal_with_fuel(find_from, 3);
    let fs = m.adts@[0].variants@[0].fields@;
    let es = m.adts@[1].variants@[0].fields@;
    assert(unit_likes(m, es, 1, 0, false) == Some((Seq::<Val>::empty(), 0nat)));
    assert(unit_like(m, 31, 2, false) == Some((Val::Adt(0, seq![]), 1nat)));
    assert(unit_likes(m, fs, 2, 0, false) == Some((Seq::<Val>::empty(), 0nat)));
    assert(seq![].push(Val::Adt(0, seq![])) =~= seq![Val::Adt(0, seq![])]);
    assert(unit_likes(m, fs, 2, 1, false) == Some((seq![Val::Adt(0, seq![])], 1nat)));
    assert(tfuel(m) == 3);
    assert(!has_arr(m, 31, 2));
    assert(!has_arr(m, 30, 3));
}

/// **Fact 4c.** The ghost call writes the canonical `Unit` for G, with no events, cost 1.
pub proof fn fact_ghost(m: MirCrate, pol: CallPolicy, a: Seq<Val>, i: u128, x: u128, g: Val, fuel: nat)
    requires order_ok(m), pol.ghost_unit.contains(g_key()), !pol.declassify.contains(g_key()),
    ensures step_term(m, pol, m.insts@[0].body->Some_0, (m.insts@[0].body->Some_0).blocks@[1].terminator.kind, order_fr(a, i, x, g), fuel)
        == Step::Jump(2, order_fr(a, i, x, Val::Unit), Seq::<Event>::empty(), 1nat),
{
    reveal_with_fuel(find_from, 3);
    let b = m.insts@[0].body->Some_0;
    let t = b.blocks@[1].terminator.kind;
    let fr = order_fr(a, i, x, g);
    let e = Seq::<Event>::empty();
    order_g(m);
    assert(callee_of(m, t->Call_func) == Some((2nat, m.calls@[1].args)));
    assert(eval_ops(m, fr, t->Call_args@, 0) == Some((Seq::<Val>::empty(), e, 0nat)));
    tiny_store0(fr, t->Call_destination, 4, Val::Unit);
    assert(place_ty(m, b, t->Call_destination) == Some(30usize));
    let fr2 = order_fr(a, i, x, Val::Unit);
    assert(put_local(fr, 4, Val::Unit) == fr2) by { assert(fr.locals.update(4, Val::Unit) =~= fr2.locals); };
    assert(e + e + e =~= e);
}

/// **Fact 4d.** A `&mut` met inside a `&` snapshot is not followed: the projection gives `None`
/// (core's walk would read `Unit` there).
pub proof fn fact_snap_mut(fr: Frame, l: Loc)
    ensures proj_step(fr, PRes::Snap(Val::Mut(l)), ProjectionElem::Deref) is None,
{
}

// ================================================================== 6. tiny is in the subset
//
// The witness: the closure `{0}` (tiny calls nothing) and its blocks `{0, 1}` (bb0's Assert goes to
// bb1; bb1 returns). Its signature (`&[u8; 4], usize -> u8`) and locals are free of `&mut`, `Box`
// and the rest; both blocks pass `block_ok`. So by `theorem_in_subset_no_unsup` no run of tiny is
// `Unsup`.

proof fn tiny_types_ok(m: MirCrate)
    requires tiny_ok(m),
    ensures sig_ok(m, tb(m)), locals_ok(m, tb(m)),
{
    tiny_tys(m);
    reveal_with_fuel(find_from, 7);
    let b = tb(m);
    assert(ty_free(m, 2, 5, false));
    assert(ty_free(m, 11, 6, false));
    assert(ty_free(m, 3, 7, false));
    assert(ty_free(m, 3, 7, true));
    assert(ty_free(m, 2, 7, true) && ty_free(m, 1, 7, true) && ty_free(m, 7, 7, true));
    assert(ty_free(m, 2, 6, true));
    assert(ty_free(m, 9, 7, true));
    assert(ty_free(m, 2, 7, false) && ty_free(m, 1, 7, false));
    assert forall|k: int| 0 <= k < b.locals@.len() implies ty_free(m, #[trigger] b.locals@[k].ty, tfuel(m), true) by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {} else if k == 5 {} else {}
    };
}

/// **Fact 6.**
pub proof fn fact_tiny_in_subset(m: MirCrate, pol: CallPolicy)
    requires tiny_ok(m),
    ensures in_subset(m, pol, 0),
{
    let s = set![0nat];
    let rs = |j: nat| set![0nat, 1nat];
    tiny_types_ok(m);
    tiny_blocks_ok(m, pol);
    let b = tb(m);
    assert(body_in(m, pol, s, rs, 0)) by {
        assert forall|bb: nat| #[trigger] rs(0).contains(bb) implies bb < b.blocks@.len() && block_ok(m, pol, b, b.blocks@[bb as int])
            && succs_in(b.blocks@[bb as int].terminator.kind, rs(0)) && callees_in(m, pol, b, b.blocks@[bb as int].terminator.kind, s) by {
            assert(bb == 0 || bb == 1);
        };
    };
    assert(closed(m, pol, s, rs));
}

// ------------------------------------------------------------------ the builders run

#[test]
fn sanity_builders() {
    let _ = (tiny_crate(), drop_crate(), niche_crate(), direct_crate(), str_crate(), str_const_alloc(), optref_crate(), order_crate(), empty_crate(),
        call_crate(), index2_place(), ext_crate());
}


// ================================================================== 7. the canonical `Unit` (Task 6 alignment)
//
// Each fact pins one producer of a unit-like value to `Val::Unit`, written literally, so a revert
// of the alignment edit in sem.rs fails it. (A unit-like type holding an array keeps its
// structural value: section 8.)

/// **Fact 7a.** An entry local that is not a parameter starts as `Unit`, unless its type is
/// unit-like and holds an array.
pub proof fn fact_entry_unit(m: MirCrate, i: nat, args: Seq<Val>, slots: Seq<Val>, k: int)
    requires inst_body(m, i) is Some, 0 <= k < inst_body(m, i)->Some_0.locals@.len(), !(1 <= k <= inst_body(m, i)->Some_0.arg_count),
        !ul_arr(m, inst_body(m, i)->Some_0.locals@[k].ty),
    ensures mir_entry(m, i, args, slots).locals[k] == Val::Unit,
{
}

/// **Fact 7b.** A `ZeroSized` constant of a unit-like type without an array is `Unit`, with no charge.
pub proof fn fact_zst_const_unit(m: MirCrate, c: ConstOperand)
    requires c.const_.kind is ZeroSized, unit_like(m, c.const_.ty, tfuel(m), true) is Some, !ul_arr(m, c.const_.ty),
    ensures const_val(m, c) == Some((Val::Unit, 0nat)),
{
}

/// **Fact 7c.** `Ghost::assume_new_fallback` (the std row) gives `Unit` at a type without an array.
pub proof fn fact_ghost_new_unit(m: MirCrate, t: Ty, vs: Seq<Val>, fr: Frame)
    requires zst_dest(m, t), !ul_arr(m, t),
    ensures std_apply(m, StdFn::GhostNew, Some(t), vs, fr) == Some((Val::Unit, fr, Seq::<Event>::empty(), 0nat)),
{
}

/// **Fact 7d.** A decoded `()` is `Unit`.
pub proof fn fact_dec_unit(m: MirCrate, t: Ty, a: Allocation, off: nat, fuel: nat)
    requires fuel > 0, rigid(m, t) matches Some(RigidTy::Tuple(ts)) && ts@.len() == 0,
        layout(m, t) matches Some(l) && offs_of(l.fields) matches Some(o) && o.len() == 0,
    ensures dec(m, t, a, off, fuel) == Some((Val::Unit, 0nat)),
{
    assert(dec(m, t, a, off, fuel) == dec_tuple(m, t, rigid(m, t)->Some_0->Tuple_0@, a, off, (fuel - 1) as nat));
}

/// **Fact 7e.** `slice_to_vec` of more than `usize::MAX` elements panics (core's `SliceToVec` is `None`).
pub proof fn fact_slice_to_vec_bound(m: MirCrate, xs: Seq<Val>, fr: Frame)
    requires xs.len() > USZ,
    ensures std_apply(m, StdFn::SliceToVec, None, seq![Val::Shr(Box::new(Val::Arr(xs)))], fr) is None,
{
}

/// **Fact 7f.** The canonical `Unit` of a unit-like one-variant enum has that variant's discriminant.
pub proof fn fact_discr_unit(m: MirCrate, b: Body, fr: Frame, p: Place)
    requires read_place(fr, p) matches Some((v, _)) && v is Unit,
        place_ty(m, b, p) matches Some(t) && adt_row(m, t) matches Some(a) && a.kind is Enum && a.variants@.len() == 1 && a.variants@[0].discr == Some(0u128)
            && unit_like(m, t, tfuel(m), true) is Some,
    ensures rv_discr(m, b, fr, p) == Some((Val::Int(0), read_place(fr, p)->Some_0.1, 0nat)),
{
}


// ================================================================== 8. unit-like types holding an array (Task 6 fix round 1)
//
// A unit-like type holding an array keeps its structural value from every producer, so the
// array reads that rustc's optimized MIR does on it complete. The crate (seat B's CE-A and CE-B):
//   tys: 2 u8, 10 (), 20 Vec<u8>, 21 &mut Vec<u8>, 22 [u8; 0], 23 &[u8], 24 &[u8; 0], 25 [u8]
//   insts[0] f(_1: &mut Vec<u8>) { let e: [u8; 0] = []; _1.extend_from_slice(&e) }  (CE-A: e is _2)
//   insts[1] `std::vec::Vec::extend_from_slice` (the std row), fn type 8, generic arg u8
//   insts[2] h(_1: [u8; 0], _2: &mut Vec<u8>) { _2.extend_from_slice(&_1) }           (CE-B's callee)
//   insts[3] root(_1: &mut Vec<u8>) { h(const ZeroSized: [u8; 0], move _1) }          (CE-B), fn type 9
// rustc's RemoveZsts deletes `e = []` (an assignment to a ZST place) and turns `h(e, v)`'s first
// argument into a `ZeroSized` constant. f's and h's bodies are one shape, `ext_body(b, a, v)`:
//   bb0: _4 = &_a; _3 = move _4 as &[u8] (PointerCoercion(Unsize));
//        _0 = extend_from_slice(move _v, move _3) -> bb1
//   bb1: return
// Steps: 2 assignments + the leaf call (1, plus `len(&[])` = 0) + the Return = 4; no events. The
// extend appends nothing, so the Vec is unchanged.

pub open spec fn ext_key() -> Seq<u8> { b"std::vec::Vec::extend_from_slice"@ }

pub open spec fn ext_body(b: Body, a: nat, v: nat) -> bool {
    b.locals@.len() == 5 && b.locals@[0].ty == 10 && b.locals@[3].ty == 23 && b.locals@[4].ty == 24
    && b.locals@[a as int].ty == 22 && b.locals@[v as int].ty == 21 && b.blocks@.len() == 2 && b.spread_arg is None
    && b.blocks@[0].statements@.len() == 2
    && (b.blocks@[0].statements@[0].kind matches StatementKind::Assign(p, rv) && local0(p, 4)
        && (rv matches Rvalue::Ref(_, bk, q) && bk is Shared && local0(q, a)))
    && (b.blocks@[0].statements@[1].kind matches StatementKind::Assign(p, rv) && local0(p, 3)
        && (rv matches Rvalue::Cast(ck, x, to) && (ck matches CastKind::PointerCoercion(PointerCoercion::Unsize)) && move_of(x, 4) && to == 23))
    && (b.blocks@[0].terminator.kind matches TerminatorKind::Call { func, args, destination, target, .. }
        && (func matches Operand::Constant(k) && k.const_.ty == 8) && args@.len() == 2 && move_of(args@[0], v) && move_of(args@[1], 3)
        && local0(destination, 0) && target == Some(1usize))
    && b.blocks@[1].statements@.len() == 0 && b.blocks@[1].terminator.kind is Return
}

pub open spec fn root_body(b: Body) -> bool {
    b.arg_count == 1 && b.locals@.len() == 2 && b.locals@[0].ty == 10 && b.locals@[1].ty == 21 && b.blocks@.len() == 2
    && b.blocks@[0].statements@.len() == 0
    && (b.blocks@[0].terminator.kind matches TerminatorKind::Call { func, args, destination, target, .. }
        && (func matches Operand::Constant(k) && k.const_.ty == 9) && args@.len() == 2
        && (args@[0] matches Operand::Constant(k) && k.const_.ty == 22 && k.const_.kind is ZeroSized) && move_of(args@[1], 1)
        && local0(destination, 0) && target == Some(1usize))
    && b.blocks@[1].statements@.len() == 0 && b.blocks@[1].terminator.kind is Return
}

pub open spec fn ext_ok(m: MirCrate) -> bool {
    m.insts@.len() == 4 && m.insts@[0].id == 0 && m.insts@[1].id == 1 && m.insts@[2].id == 2 && m.insts@[3].id == 3
    && m.insts@[0].kind is Item && m.insts@[2].kind is Item && m.insts@[3].kind is Item
    && m.insts@[1].key@ == ext_key() && m.insts@[2].key@.len() == 0
    && (m.insts@[0].body matches Some(b) && b.arg_count == 1 && ext_body(b, 2, 1))
    && (m.insts@[2].body matches Some(b) && b.arg_count == 2 && ext_body(b, 1, 2))
    && (m.insts@[3].body matches Some(b) && root_body(b))
    && m.tys@.len() == 8
    && m.tys@[0].id == 2 && (m.tys@[0].kind matches TyKind::RigidTy(RigidTy::Uint(UintTy::U8)))
    && m.tys@[1].id == 10 && (m.tys@[1].kind matches TyKind::RigidTy(RigidTy::Tuple(ts)) && ts@.len() == 0)
    && m.tys@[2].id == 20 && (m.tys@[2].kind matches TyKind::RigidTy(RigidTy::Adt(_, ga)) && ga.0@.len() == 1 && (ga.0@[0] matches GenericArgKind::Type(e) && e == 2))
    && m.tys@[3].id == 21 && (m.tys@[3].kind matches TyKind::RigidTy(RigidTy::Ref(_, p, mu)) && p == 20 && mu is Mut)
    && m.tys@[4].id == 22 && (m.tys@[4].kind matches TyKind::RigidTy(RigidTy::Array(e, c)) && e == 2 && c.id == 0)
    && m.tys@[5].id == 23 && (m.tys@[5].kind matches TyKind::RigidTy(RigidTy::Ref(_, p, mu)) && p == 25 && mu is Not)
    && m.tys@[6].id == 24 && (m.tys@[6].kind matches TyKind::RigidTy(RigidTy::Ref(_, p, mu)) && p == 22 && mu is Not)
    && m.tys@[7].id == 25 && (m.tys@[7].kind matches TyKind::RigidTy(RigidTy::Slice(e)) && e == 2)
    && m.adts@.len() == 1 && m.adts@[0].ty == 20 && m.adts@[0].name@ == b"std::vec::Vec"@
    && m.consts@.len() == 1 && m.consts@[0].id == 0 && m.consts@[0].usize == Some(0u64)
    && m.calls@.len() == 2 && m.calls@[0].fn_ty == 8 && m.calls@[0].resolved == Some(1usize)
    && m.calls@[0].args.0@.len() == 1 && (m.calls@[0].args.0@[0] matches GenericArgKind::Type(e) && e == 2)
    && m.calls@[1].fn_ty == 9 && m.calls@[1].resolved == Some(2usize)
    && m.layouts@.len() == 0 && m.allocs@.len() == 0
}

fn ext_blocks(a: usize, v: usize) -> (bs: Vec<BasicBlock>)
    ensures bs@.len() == 2, bs@[0].statements@.len() == 2,
        bs@[0].statements@[0].kind matches StatementKind::Assign(p, rv) && local0(p, 4)
            && (rv matches Rvalue::Ref(_, bk, q) && bk is Shared && local0(q, a as nat)),
        bs@[0].statements@[1].kind matches StatementKind::Assign(p, rv) && local0(p, 3)
            && (rv matches Rvalue::Cast(ck, x, to) && (ck matches CastKind::PointerCoercion(PointerCoercion::Unsize)) && move_of(x, 4) && to == 23),
        bs@[0].terminator.kind matches TerminatorKind::Call { func, args, destination, target, .. }
            && (func matches Operand::Constant(k) && k.const_.ty == 8) && args@.len() == 2 && move_of(args@[0], v as nat) && move_of(args@[1], 3)
            && local0(destination, 0) && target == Some(1usize),
        bs@[1].statements@.len() == 0, bs@[1].terminator.kind is Return,
{
    let mut s0 = Vec::new();
    s0.push(stmt(StatementKind::Assign(place0(4), Rvalue::Ref(Json::Null, BorrowKind::Shared, place0(a)))));
    s0.push(stmt(StatementKind::Assign(place0(3), Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize), Operand::Move(place0(4)), 23))));
    let mut args = Vec::new();
    args.push(Operand::Move(place0(v)));
    args.push(Operand::Move(place0(3)));
    let mut bs = Vec::new();
    bs.push(BasicBlock { statements: s0, terminator: term(call_to(8, args, place0(0), 1)) });
    bs.push(BasicBlock { statements: Vec::new(), terminator: term(TerminatorKind::Return) });
    bs
}

/// The locals of f (`a == 2`) or h (`a == 1`): the `&mut Vec` is the other of `_1`, `_2`.
fn ext_locals(a: usize) -> (ls: Vec<LocalDecl>)
    requires a == 1 || a == 2,
    ensures ls@.len() == 5, ls@[0].ty == 10, ls@[3].ty == 23, ls@[4].ty == 24, ls@[a as int].ty == 22, ls@[3 - a].ty == 21,
{
    let mut ls = Vec::new();
    ls.push(ldecl(10));
    if a == 1 { ls.push(ldecl(22)); ls.push(ldecl(21)); } else { ls.push(ldecl(21)); ls.push(ldecl(22)); }
    ls.push(ldecl(23));
    ls.push(ldecl(24));
    ls
}

pub fn ext_crate() -> (m: MirCrate) ensures ext_ok(m) {
    let mut ra = Vec::new();
    ra.push(zst_fn(22));
    ra.push(Operand::Move(place0(1)));
    let mut rb = Vec::new();
    rb.push(BasicBlock { statements: Vec::new(), terminator: term(call_to(9, ra, place0(0), 1)) });
    rb.push(BasicBlock { statements: Vec::new(), terminator: term(TerminatorKind::Return) });
    let mut rl = Vec::new();
    rl.push(ldecl(10));
    rl.push(ldecl(21));
    let key: &[u8] = b"std::vec::Vec::extend_from_slice";
    let mut insts = Vec::new();
    insts.push(inst(0, body(ext_blocks(2, 1), ext_locals(2), 1)));
    insts.push(bare_inst(1, vstd::slice::slice_to_vec(key)));
    insts.push(inst(2, body(ext_blocks(1, 2), ext_locals(1), 2)));
    insts.push(inst(3, body(rb, rl, 1)));
    let mut ga = Vec::new();
    ga.push(GenericArgKind::Type(2));
    let mut ga2 = Vec::new();
    ga2.push(GenericArgKind::Type(2));
    let mut calls = Vec::new();
    calls.push(Call { fn_ty: 8, def: 1, def_name: Vec::new(), args: GenericArgs(ga), resolved: Some(1) });
    calls.push(Call { fn_ty: 9, def: 2, def_name: Vec::new(), args: GenericArgs(Vec::new()), resolved: Some(2) });
    let mut tys = Vec::new();
    tys.push(uint(2, UintTy::U8));
    tys.push(TyRow { id: 10, kind: TyKind::RigidTy(RigidTy::Tuple(Vec::new())) });
    tys.push(TyRow { id: 20, kind: TyKind::RigidTy(RigidTy::Adt(0, GenericArgs(ga2))) });
    tys.push(ref_row(21, 20, Mutability::Mut));
    tys.push(arr_row(22, 2));
    tys.push(ref_row(23, 25, Mutability::Not));
    tys.push(ref_row(24, 22, Mutability::Not));
    tys.push(TyRow { id: 25, kind: TyKind::RigidTy(RigidTy::Slice(2)) });
    let name: &[u8] = b"std::vec::Vec";
    let mut adts = Vec::new();
    adts.push(Adt { ty: 20, name: vstd::slice::slice_to_vec(name), kind: AdtKind::Struct, is_box: false, variants: Vec::new() });
    let mut consts = Vec::new();
    consts.push(ConstRow { id: 0, usize: Some(0) });
    MirCrate {
        crate_name: Vec::new(), items: Vec::new(), insts, calls, drops: Vec::new(), tys, adts, consts, layouts: Vec::new(),
        allocs: Vec::new(), spans: Vec::new(),
    }
}

/// The crate's types: `[u8; 0]` is unit-like and holds an array, so its producers give `Arr([])`;
/// `()` is `Unit`; the references are not unit-like.
proof fn ext_tys(m: MirCrate)
    requires ext_ok(m),
    ensures tfuel(m) == 9, ul_val(m, 22) == Val::Arr(seq![]),
        unit_like(m, 22, 9, true) is Some, ul_val(m, 10) == Val::Unit, ul_val(m, 23) == Val::Unit,
        ul_val(m, 24) == Val::Unit, is_mut_ref(m, 21), !is_mut_ref(m, 22), !is_mut_ref(m, 10),
        !is_mut_ref(m, 23), !is_mut_ref(m, 24),
        rigid(m, 24) matches Some(RigidTy::Ref(_, p, mu)) && p == 22 && mu is Not,
        rigid(m, 23) matches Some(RigidTy::Ref(_, p, mu)) && p == 25 && mu is Not,
        rigid(m, 22) matches Some(RigidTy::Array(_, _)), rigid(m, 25) matches Some(RigidTy::Slice(_)),
        rigid(m, 21) matches Some(RigidTy::Ref(_, p, mu)) && p == 20 && mu is Mut,
        vec_elem(m, 20) == Some(2usize), int_ty(m, 2) == Some(CTy::U8),
        std_model(m, ext_key(), m.calls@[0].args) == Some(StdFn::VecExtendFromSlice),
{
    reveal_with_fuel(find_from, 9);
    assert(const_usize(m, 0) == Some(0u64));
    assert(unit_like(m, 22, 9, true) == Some((Val::Arr(seq![]), 0nat)));
    assert(unit_like(m, 22, 9, false) == Some((Val::Arr(seq![]), 0nat)));
    assert(has_arr(m, 22, 9));
    let ts = (m.tys@[1].kind->RigidTy_0)->Tuple_0@;
    assert(unit_likes(m, ts, 8, 0, true) == Some((Seq::<Val>::empty(), 0nat)));
    assert(!has_arr(m, 10, 9));
    assert(unit_like(m, 23, 9, true) is None);
    assert(unit_like(m, 24, 9, true) is None);
    assert(b"std::vec::Vec::new"@.len() == 18);
    assert(b"std::vec::Vec::with_capacity"@.len() == 28);
    assert(b"std::vec::Vec::push"@.len() == 19);
    assert(ext_key().len() == 32);
    assert(is_u8(garg0(m, m.calls@[0].args)));
}

/// f's and h's blocks pass the static subset gate.
proof fn ext_blocks_ok(m: MirCrate, pol: CallPolicy, b: Body, a: nat, v: nat)
    requires ext_ok(m), ext_body(b, a, v), (a == 1 && v == 2) || (a == 2 && v == 1),
        !pol.declassify.contains(ext_key()), !pol.ghost_unit.contains(ext_key()),
    ensures block_ok(m, pol, b, b.blocks@[0]), block_ok(m, pol, b, b.blocks@[1]),
{
    reveal(block_ok);
    reveal_with_fuel(find_from, 9);
    ext_tys(m);
    let ss = b.blocks@[0].statements@;
    assert(stmt_ok(m, b, ss[0]));
    assert(op_ty(m, b, ss[1].kind->Assign_1->Cast_1) == Some(24usize));
    assert(stmt_ok(m, b, ss[1]));
    let t = b.blocks@[0].terminator.kind;
    assert(callee_of(m, t->Call_func) == Some((1nat, m.calls@[0].args)));
    assert(is_leaf(m, pol, m.insts@[1].key@, m.calls@[0].args));
    assert(ops_ok(m, b, t->Call_args@));
    assert(term_ok(m, pol, b, t));
}

pub open spec fn ext_out(fr: Frame) -> Frame {
    Frame { locals: fr.locals.update(4, Val::Shr(Box::new(Val::Arr(seq![])))).update(3, Val::Shr(Box::new(Val::Arr(seq![])))).update(0, Val::Unit), slots: fr.slots }
}

/// bb0's statements: `_4 = &_a` and the Unsize cast, both `Shr(Arr([]))`; 2 steps.
proof fn ext_stmts(m: MirCrate, b: Body, a: nat, v: nat, fr: Frame)
    requires ext_ok(m), ext_body(b, a, v), (a == 1 && v == 2) || (a == 2 && v == 1), fr.locals.len() == 5,
        fr.locals[a as int] == Val::Arr(seq![]),
    ensures exec_stmts(m, b, fr, b.blocks@[0].statements@, 2)
        == Some((Frame { locals: fr.locals.update(4, Val::Shr(Box::new(Val::Arr(seq![])))).update(3, Val::Shr(Box::new(Val::Arr(seq![])))), slots: fr.slots },
            Seq::<Event>::empty(), 2nat)),
{
    reveal(exec_stmt);
    ext_tys(m);
    let ss = b.blocks@[0].statements@;
    let e = Seq::<Event>::empty();
    let r = Val::Shr(Box::new(Val::Arr(seq![])));
    assert(e + e =~= e);
    tiny_store0(fr, ss[0].kind->Assign_1->Ref_2, a, Val::Unit);
    tiny_store0(fr, ss[0].kind->Assign_0, 4, r);
    let f1 = put_local(fr, 4, r);
    assert(exec_stmt(m, b, fr, ss[0]) == Some((f1, e, 1nat)));
    tiny_store0(f1, ss[1].kind->Assign_1->Cast_1->Move_0, 4, Val::Unit);
    tiny_store0(f1, ss[1].kind->Assign_0, 3, r);
    assert(op_ty(m, b, ss[1].kind->Assign_1->Cast_1) == Some(24usize));
    let f2 = put_local(f1, 3, r);
    assert(exec_stmt(m, b, f1, ss[1]) == Some((f2, e, 1nat)));
    assert(exec_stmts(m, b, fr, ss, 0) == Some((fr, e, 0nat)));
    assert(exec_stmts(m, b, fr, ss, 1) == Some((f1, e, 1nat)));
}

/// f's or h's run: `&mut` Vec at a slot location holding `xs`; done in 4 steps, no events, the
/// Vec unchanged.
proof fn ext_run(m: MirCrate, pol: CallPolicy, b: Body, a: nat, v: nat, fr: Frame, n: nat, xs: Seq<Val>, fuel: nat)
    requires ext_ok(m), ext_body(b, a, v), (a == 1 && v == 2) || (a == 2 && v == 1), fr.locals.len() == 5,
        fr.locals[a as int] == Val::Arr(seq![]), fr.locals[v as int] == Val::Mut(Loc { root: Root::Slot(n), path: seq![] }),
        n < fr.slots.len(), fr.slots[n as int] == Val::Arr(xs), xs.len() <= USZ, fuel >= 2,
        !pol.declassify.contains(ext_key()), !pol.ghost_unit.contains(ext_key()),
    ensures run_block(m, pol, b, 0, fr, fuel) == Out::Done(ext_out(fr), Seq::<Event>::empty(), 4nat),
{
    ext_blocks_ok(m, pol, b, a, v);
    ext_stmts(m, b, a, v, fr);
    let e = Seq::<Event>::empty();
    let r = Val::Shr(Box::new(Val::Arr(seq![])));
    let f2 = Frame { locals: fr.locals.update(4, r).update(3, r), slots: fr.slots };
    ext_call(m, pol, b, a, v, f2, n, xs, fuel);
    assert(put_local(f2, 0, Val::Unit) == ext_out(fr));
    assert(e + e =~= e);
    assert(e + e + e =~= e);
    assert(exec_stmts(m, b, ext_out(fr), b.blocks@[1].statements@, 0) == Some((ext_out(fr), e, 0nat)));
    assert(step_term(m, pol, b, b.blocks@[1].terminator.kind, ext_out(fr), (fuel - 1) as nat) == Step::Stop(Out::Done(ext_out(fr), e, 1nat)));
    assert(run_block(m, pol, b, 1, ext_out(fr), (fuel - 1) as nat) == Out::Done(ext_out(fr), e, 1nat));
}

/// The extend row on `[Mut(slot n), Shr(Arr([]))]`: `()`, the Vec unchanged, no events, cost 0.
proof fn ext_leaf(m: MirCrate, pol: CallPolicy, dty: Option<Ty>, f2: Frame, n: nat, xs: Seq<Val>)
    requires ext_ok(m), n < f2.slots.len(), f2.slots[n as int] == Val::Arr(xs), xs.len() <= USZ,
        !pol.declassify.contains(ext_key()), !pol.ghost_unit.contains(ext_key()),
    ensures is_leaf(m, pol, m.insts@[1].key@, m.calls@[0].args),
        leaf_call(m, pol, m.insts@[1].key@, m.calls@[0].args, dty, seq![Val::Mut(s_at(n)), Val::Shr(Box::new(Val::Arr(seq![])))], f2)
            == Some((Val::Unit, f2, Seq::<Event>::empty(), 0nat)),
{
    ext_tys(m);
    let l = s_at(n);
    assert(xs + Seq::<Val>::empty() =~= xs);
    assert(store(f2, l, Val::Arr(xs + Seq::<Val>::empty())) == Some(f2)) by { assert(f2.slots.update(n as int, Val::Arr(xs)) =~= f2.slots); };
}

/// bb0's call (the extend row) from the frame after the statements: on to bb1, cost 1.
proof fn ext_call(m: MirCrate, pol: CallPolicy, b: Body, a: nat, v: nat, f2: Frame, n: nat, xs: Seq<Val>, fuel: nat)
    requires ext_ok(m), ext_body(b, a, v), (a == 1 && v == 2) || (a == 2 && v == 1), f2.locals.len() == 5,
        f2.locals[3] == Val::Shr(Box::new(Val::Arr(seq![]))), f2.locals[v as int] == Val::Mut(s_at(n)),
        n < f2.slots.len(), f2.slots[n as int] == Val::Arr(xs), xs.len() <= USZ,
        !pol.declassify.contains(ext_key()), !pol.ghost_unit.contains(ext_key()),
    ensures step_term(m, pol, b, b.blocks@[0].terminator.kind, f2, fuel) == Step::Jump(1, put_local(f2, 0, Val::Unit), Seq::<Event>::empty(), 1nat),
{
    hide(leaf_call);
    hide(is_leaf);
    hide(body_call);
    let e = Seq::<Event>::empty();
    let r = Val::Shr(Box::new(Val::Arr(seq![])));
    let t = b.blocks@[0].terminator.kind;
    let vs = seq![Val::Mut(s_at(n)), r];
    ext_leaf(m, pol, place_ty(m, b, t->Call_destination), f2, n, xs);
    assert(callee_of(m, t->Call_func) == Some((1nat, m.calls@[0].args))) by { reveal_with_fuel(find_from, 3); };
    assert(eval_ops(m, f2, t->Call_args@, 2) == Some((vs, e, 0nat))) by {
        reveal_with_fuel(eval_ops, 3);
        assert(seq![Val::Mut(s_at(n))] =~= seq![].push(Val::Mut(s_at(n))));
        assert(vs =~= seq![Val::Mut(s_at(n))].push(r));
        assert(e + e =~= e);
    };
    tiny_store0(f2, t->Call_destination, 0, Val::Unit);
    assert(e + e + e =~= e);
}

pub open spec fn s_at(n: nat) -> Loc { Loc { root: Root::Slot(n), path: seq![] } }

pub open spec fn cea_out(xs: Seq<Val>) -> Frame {
    Frame { locals: seq![Val::Unit, Val::Mut(s_at(0)), Val::Arr(seq![]), Val::Shr(Box::new(Val::Arr(seq![]))), Val::Shr(Box::new(Val::Arr(seq![])))],
        slots: seq![Val::Arr(xs)] }
}

/// **Fact 8a (CE-A).** f completes, with the Vec unchanged: its never-assigned `[u8; 0]` local
/// `_2` holds `Arr([])`, so `&_2` unsized is the empty slice. 4 steps, no events.
pub proof fn fact_ce_a(m: MirCrate, pol: CallPolicy, args: Seq<Val>, xs: Seq<Val>, fuel: nat)
    requires ext_ok(m), args.len() == 1, xs.len() <= USZ, fuel >= 2,
        !pol.declassify.contains(ext_key()), !pol.ghost_unit.contains(ext_key()),
    ensures mir_run(m, pol, 0, mir_entry(m, 0, args, seq![Val::Arr(xs)]), fuel) == Out::Done(cea_out(xs), Seq::<Event>::empty(), 4nat),
{
    hide(mir_entry);
    hide(mir_run);
    cea_entry(m, args, xs);
    cea_run(m, pol, xs, fuel);
    assert(ext_out(cea_in(xs)).locals =~= cea_out(xs).locals);
}

pub open spec fn cea_in(xs: Seq<Val>) -> Frame {
    Frame { locals: seq![Val::Unit, Val::Mut(s_at(0)), Val::Arr(seq![]), Val::Unit, Val::Unit], slots: seq![Val::Arr(xs)] }
}

/// f's entry frame: `_1` the slot location; the never-assigned `_2: [u8; 0]` is `Arr([])`.
proof fn cea_entry(m: MirCrate, args: Seq<Val>, xs: Seq<Val>)
    requires ext_ok(m), args.len() == 1,
    ensures mir_entry(m, 0, args, seq![Val::Arr(xs)]) == cea_in(xs),
{
    ext_tys(m);
    assert(mir_entry(m, 0, args, seq![Val::Arr(xs)]).locals =~= cea_in(xs).locals);
}

proof fn cea_run(m: MirCrate, pol: CallPolicy, xs: Seq<Val>, fuel: nat)
    requires ext_ok(m), xs.len() <= USZ, fuel >= 2, !pol.declassify.contains(ext_key()), !pol.ghost_unit.contains(ext_key()),
    ensures mir_run(m, pol, 0, cea_in(xs), fuel) == Out::Done(ext_out(cea_in(xs)), Seq::<Event>::empty(), 4nat),
{
    ext_run(m, pol, m.insts@[0].body->Some_0, 2, 1, cea_in(xs), 0, xs, fuel);
}

/// The root's call of h passes the static subset gate (a body call: `h`'s signature, and the
/// arguments have its parameters' types).
proof fn root_blocks_ok(m: MirCrate, pol: CallPolicy)
    requires ext_ok(m), !pol.declassify.contains(Seq::<u8>::empty()), !pol.ghost_unit.contains(Seq::<u8>::empty()),
    ensures block_ok(m, pol, m.insts@[3].body->Some_0, (m.insts@[3].body->Some_0).blocks@[0]),
        block_ok(m, pol, m.insts@[3].body->Some_0, (m.insts@[3].body->Some_0).blocks@[1]),
{
    reveal(block_ok);
    reveal_with_fuel(find_from, 9);
    ext_tys(m);
    let c = m.insts@[3].body->Some_0;
    let h = m.insts@[2].body->Some_0;
    let t = c.blocks@[0].terminator.kind;
    call_not_std(m, m.calls@[1].args);
    assert(m.insts@[2].key@ =~= Seq::<u8>::empty());
    assert(callee_of(m, t->Call_func) == Some((2nat, m.calls@[1].args)));
    assert(ty_free(m, 10, 9, false));
    assert(ty_free(m, 2, 8, false));
    assert(ty_free(m, 22, 9, false));
    assert(ty_free(m, 20, 9, false));
    assert(sig_ok(m, h));
    let args = t->Call_args@;
    assert(op_ty(m, c, args[0]) == Some(22usize));
    assert(op_ty(m, c, args[1]) == Some(21usize));
    assert(args_typed(m, c, args, h));
    assert(ops_ok(m, c, args));
    assert(term_ok(m, pol, c, t));
}

pub open spec fn ceb_root(xs: Seq<Val>) -> Frame { Frame { locals: seq![Val::Unit, Val::Mut(s_at(0))], slots: seq![Val::Arr(xs)] } }

pub open spec fn ceb_h0(xs: Seq<Val>) -> Frame {
    Frame { locals: seq![Val::Unit, Val::Arr(seq![]), Val::Mut(s_at(1)), Val::Unit, Val::Unit], slots: seq![Val::Unit, Val::Arr(xs)] }
}

/// The root's call: the `ZeroSized` argument is `Arr([])`; h runs (4 steps) and its slot is
/// written back unchanged. 1 + 4 steps.
proof fn ceb_call(m: MirCrate, pol: CallPolicy, xs: Seq<Val>, fuel: nat)
    requires ext_ok(m), xs.len() <= USZ, fuel >= 3, forall|i: int| 0 <= i < xs.len() ==> mut_free(#[trigger] xs[i]),
        !pol.declassify.contains(ext_key()), !pol.ghost_unit.contains(ext_key()),
        !pol.declassify.contains(Seq::<u8>::empty()), !pol.ghost_unit.contains(Seq::<u8>::empty()),
    ensures step_term(m, pol, m.insts@[3].body->Some_0, (m.insts@[3].body->Some_0).blocks@[0].terminator.kind, ceb_root(xs), fuel)
        == Step::Jump(1, ceb_root(xs), Seq::<Event>::empty(), 5nat),
{
    hide(leaf_call);
    hide(is_leaf);
    hide(eval_ops);
    hide(callee_of);
    let c = m.insts@[3].body->Some_0;
    let t = c.blocks@[0].terminator.kind;
    let fr = ceb_root(xs);
    let e = Seq::<Event>::empty();
    assert(e + e =~= e);
    assert(e + e + e =~= e);
    ceb_ops(m, pol, xs);
    tiny_store0(fr, t->Call_destination, 0, Val::Unit);
    ceb_body(m, pol, xs, fuel);
    assert(put_local(fr, 0, Val::Unit) == fr) by { assert(fr.locals.update(0, Val::Unit) =~= fr.locals); };
}

/// The root's call: the callee is h (a body), and the arguments are the `ZeroSized` constant's
/// `Arr([])` and `_1`'s location.
proof fn ceb_ops(m: MirCrate, pol: CallPolicy, xs: Seq<Val>)
    requires ext_ok(m), !pol.declassify.contains(Seq::<u8>::empty()), !pol.ghost_unit.contains(Seq::<u8>::empty()),
    ensures ({
        let t = (m.insts@[3].body->Some_0).blocks@[0].terminator.kind;
        &&& callee_of(m, t->Call_func) == Some((2nat, m.calls@[1].args))
        &&& eval_ops(m, ceb_root(xs), t->Call_args@, 2) == Some((seq![Val::Arr(seq![]), Val::Mut(s_at(0))], Seq::<Event>::empty(), 0nat))
        &&& !is_leaf(m, pol, m.insts@[2].key@, m.calls@[1].args)
    }),
{
    reveal_with_fuel(find_from, 9);
    ext_tys(m);
    let t = (m.insts@[3].body->Some_0).blocks@[0].terminator.kind;
    let e = Seq::<Event>::empty();
    let vs = seq![Val::Arr(seq![]), Val::Mut(s_at(0))];
    assert(e + e =~= e);
    assert(const_val(m, t->Call_args@[0]->Constant_0) == Some((Val::Arr(seq![]), 0nat)));
    assert(eval_ops(m, ceb_root(xs), t->Call_args@, 2) == Some((vs, e, 0nat))) by {
        reveal_with_fuel(eval_ops, 3);
        assert(seq![Val::Arr(seq![])] =~= seq![].push(Val::Arr(seq![])));
        assert(vs =~= seq![Val::Arr(seq![])].push(Val::Mut(s_at(0))));
    };
    call_not_std(m, m.calls@[1].args);
    assert(m.insts@[2].key@ =~= Seq::<u8>::empty());
}

pub open spec fn ceb_vs() -> Seq<Val> { seq![Val::Arr(seq![]), Val::Mut(s_at(0))] }
pub open spec fn ceb_cs(xs: Seq<Val>) -> Seq<Val> { seq![Val::Unit, Val::Arr(xs)] }

/// Entering h from the root: `_1` is the constant's `Arr([])`, `_2` the location of slot 1, which
/// holds the root's Vec.
proof fn ceb_enter(m: MirCrate, xs: Seq<Val>)
    requires ext_ok(m), forall|i: int| 0 <= i < xs.len() ==> mut_free(#[trigger] xs[i]),
    ensures args_ok(m, m.insts@[2].body->Some_0, ceb_root(xs), ceb_vs()),
        call_slots(m, m.insts@[2].body->Some_0, ceb_root(xs), ceb_vs()) == ceb_cs(xs),
        mir_entry(m, 2, ceb_vs(), ceb_cs(xs)) == ceb_h0(xs),
{
    ext_tys(m);
    let h = m.insts@[2].body->Some_0;
    let fr = ceb_root(xs);
    let vs = ceb_vs();
    assert(mut_free(Val::Arr(xs)));
    assert(arg_ok(m, h, fr, vs, 0));
    assert(arg_ok(m, h, fr, vs, 1));
    assert(call_slots(m, h, fr, vs) =~= ceb_cs(xs));
    assert(mir_entry(m, 2, vs, ceb_cs(xs)).locals =~= ceb_h0(xs).locals);
}

/// Leaving h: `_0` is `Unit`; slot 1 is written back to the root's slot 0, unchanged.
proof fn ceb_leave(m: MirCrate, xs: Seq<Val>)
    requires ext_ok(m), forall|i: int| 0 <= i < xs.len() ==> mut_free(#[trigger] xs[i]),
    ensures return_to(m, m.insts@[2].body->Some_0, ceb_root(xs), ceb_vs(), ext_out(ceb_h0(xs))) == Some((Val::Unit, ceb_root(xs))),
{
    ext_tys(m);
    let h = m.insts@[2].body->Some_0;
    let fr = ceb_root(xs);
    let vs = ceb_vs();
    let hf = ext_out(ceb_h0(xs));
    assert(mut_free(Val::Arr(xs)));
    assert(write_back(m, h, fr, vs, hf.slots, 0) == Some(fr));
    assert(write_back(m, h, fr, vs, hf.slots, 1) == Some(fr));
    assert(store(fr, s_at(0), Val::Arr(xs)) == Some(fr)) by { assert(fr.slots.update(0, Val::Arr(xs)) =~= fr.slots); };
    assert(write_back(m, h, fr, vs, hf.slots, 2) == Some(fr));
}

/// The body call of h from the root's frame: h runs its 4 steps and returns `Unit`.
proof fn ceb_body(m: MirCrate, pol: CallPolicy, xs: Seq<Val>, fuel: nat)
    requires ext_ok(m), xs.len() <= USZ, fuel >= 3, forall|i: int| 0 <= i < xs.len() ==> mut_free(#[trigger] xs[i]),
        !pol.declassify.contains(ext_key()), !pol.ghost_unit.contains(ext_key()),
    ensures body_call(m, pol, 2, m.insts@[2].body->Some_0, ceb_vs(), ceb_root(xs), fuel)
        == Ok::<(Val, Frame, Seq<Event>, nat), Out>((Val::Unit, ceb_root(xs), Seq::<Event>::empty(), 4nat)),
{
    hide(mir_entry);
    hide(args_ok);
    hide(call_slots);
    hide(return_to);
    ceb_enter(m, xs);
    ceb_leave(m, xs);
    ceb_hrun(m, pol, xs, (fuel - 1) as nat);
}

/// h's run from its entry frame.
proof fn ceb_hrun(m: MirCrate, pol: CallPolicy, xs: Seq<Val>, fuel: nat)
    requires ext_ok(m), xs.len() <= USZ, fuel >= 2, !pol.declassify.contains(ext_key()), !pol.ghost_unit.contains(ext_key()),
    ensures mir_run(m, pol, 2, ceb_h0(xs), fuel) == Out::Done(ext_out(ceb_h0(xs)), Seq::<Event>::empty(), 4nat),
{
    ext_run(m, pol, m.insts@[2].body->Some_0, 1, 2, ceb_h0(xs), 1, xs, fuel);
}

/// **Fact 8b (CE-B).** The root completes, with the Vec unchanged: the `ZeroSized` `[u8; 0]`
/// argument is `Arr([])`, so h's `&_1` unsized is the empty slice. 1 + 4 + 1 = 6 steps, no events.
pub proof fn fact_ce_b(m: MirCrate, pol: CallPolicy, args: Seq<Val>, xs: Seq<Val>, fuel: nat)
    requires ext_ok(m), args.len() == 1, xs.len() <= USZ, fuel >= 3, forall|i: int| 0 <= i < xs.len() ==> mut_free(#[trigger] xs[i]),
        !pol.declassify.contains(ext_key()), !pol.ghost_unit.contains(ext_key()),
        !pol.declassify.contains(Seq::<u8>::empty()), !pol.ghost_unit.contains(Seq::<u8>::empty()),
    ensures mir_run(m, pol, 3, mir_entry(m, 3, args, seq![Val::Arr(xs)]), fuel) == Out::Done(ceb_root(xs), Seq::<Event>::empty(), 6nat),
{
    hide(mir_entry);
    let c = m.insts@[3].body->Some_0;
    let e = Seq::<Event>::empty();
    assert(e + e =~= e);
    assert(e + e + e =~= e);
    ceb_entry(m, args, xs);
    root_blocks_ok(m, pol);
    ceb_call(m, pol, xs, fuel);
    assert(step_term(m, pol, c, c.blocks@[1].terminator.kind, ceb_root(xs), (fuel - 1) as nat) == Step::Stop(Out::Done(ceb_root(xs), e, 1nat)));
    assert(exec_stmts(m, c, ceb_root(xs), c.blocks@[0].statements@, 0) == Some((ceb_root(xs), e, 0nat)));
    assert(exec_stmts(m, c, ceb_root(xs), c.blocks@[1].statements@, 0) == Some((ceb_root(xs), e, 0nat)));
    assert(run_block(m, pol, c, 1, ceb_root(xs), (fuel - 1) as nat) == Out::Done(ceb_root(xs), e, 1nat));
}

proof fn ceb_entry(m: MirCrate, args: Seq<Val>, xs: Seq<Val>)
    requires ext_ok(m), args.len() == 1,
    ensures mir_entry(m, 3, args, seq![Val::Arr(xs)]) == ceb_root(xs),
{
    ext_tys(m);
    assert(mir_entry(m, 3, args, seq![Val::Arr(xs)]).locals =~= ceb_root(xs).locals);
}

/// `[T; 0]` at type `t`: unit-like, holding an array, value `Arr([])`.
proof fn arr0_ul(m: MirCrate, t: Ty)
    requires rigid(m, t) matches Some(RigidTy::Array(_, n)) && const_usize(m, n.id) == Some(0u64), m.tys@.len() >= 1,
    ensures ul_arr(m, t), ul_val(m, t) == Val::Arr(seq![]),
        unit_like(m, t, tfuel(m), true) is Some,
{
}

/// **Fact 8c.** `PtrMetadata` of `&` a `ZeroSized` `[u8; 0]` (held by `_1`, as a parameter it was
/// passed to), through `Unsize` to `&[u8]`, is 0: `_2 = &_1` is `Shr(Arr([]))`, the cast keeps it.
pub proof fn fact_ptrmeta_zst(m: MirCrate, b: Body, fr: Frame, c: ConstOperand, p1: Place, x: Operand, to: Ty, y: Operand)
    requires c.const_.kind is ZeroSized, m.tys@.len() >= 1,
        rigid(m, c.const_.ty) matches Some(RigidTy::Array(_, n)) && const_usize(m, n.id) == Some(0u64),
        local0(p1, 1), move_of(x, 2), copy_of(y, 3), fr.locals.len() == 4, b.locals@.len() == 4,
        fr.locals[1] == const_val(m, c)->Some_0.0,
        fr.locals[2] == Val::Shr(Box::new(fr.locals[1])),
        rigid(m, b.locals@[2].ty) matches Some(RigidTy::Ref(_, p, _)) && p == c.const_.ty,
        rigid(m, to) matches Some(RigidTy::Ref(_, q, _)) && rigid(m, q) matches Some(RigidTy::Slice(_)),
        b.locals@[3].ty == to, fr.locals[3] == rv_cast(m, b, fr, CastKind::PointerCoercion(PointerCoercion::Unsize), x, to)->Some_0.0,
    ensures rv_ref(fr, BorrowKind::Shared, p1) == Some((fr.locals[2], Seq::<Event>::empty(), 0nat)),
        rv_cast(m, b, fr, CastKind::PointerCoercion(PointerCoercion::Unsize), x, to) == Some((fr.locals[2], Seq::<Event>::empty(), 0nat)),
        rv_un(m, b, fr, UnOp::PtrMetadata, y) == Some((Val::Int(0), Seq::<Event>::empty(), 0nat)),
{
    arr0_ul(m, c.const_.ty);
}

/// **Fact 8d.** An in-bounds `Index` of a never-assigned `[(); 3]` local keeps its `Idx(i)` event:
/// the local holds `Arr([Unit; 3])`.
pub proof fn fact_unit_arr_index(m: MirCrate, i: nat, args: Seq<Val>, slots: Seq<Val>, q: Place, j: u128)
    requires inst_body(m, i) matches Some(b) && b.arg_count == 0 && b.locals@.len() == 3
            && (rigid(m, b.locals@[1].ty) matches Some(RigidTy::Array(e, n)) && const_usize(m, n.id) == Some(3u64)
            && (rigid(m, e) matches Some(RigidTy::Tuple(ts)) && ts@.len() == 0)),
        m.tys@.len() >= 2, q.local == 1, q.projection@.len() == 1, q.projection@[0] matches ProjectionElem::Index(x) && x == 2, j < 3,
    ensures read_place(put_local(mir_entry(m, i, args, slots), 2, Val::Int(j)), q) == Some((Val::Unit, seq![Event::Idx(j)])),
{
    let b = inst_body(m, i)->Some_0;
    let t = b.locals@[1].ty;
    let e = rigid(m, t)->Some_0->Array_0;
    let tf = tfuel(m);
    let ts = match rigid(m, e) { Some(RigidTy::Tuple(ts)) => ts@, _ => seq![] };
    assert(unit_likes(m, ts, (tf - 2) as nat, 0, false) == Some((Seq::<Val>::empty(), 0nat)));
    assert(unit_like(m, e, (tf - 1) as nat, false) == Some((Val::Unit, 0nat)));
    assert(unit_likes(m, ts, (tf - 2) as nat, 0, true) == Some((Seq::<Val>::empty(), 0nat)));
    assert(unit_like(m, e, (tf - 1) as nat, true) == Some((Val::Unit, 0nat)));
    let fr = put_local(mir_entry(m, i, args, slots), 2, Val::Int(j));
    let u = fr.locals[1];
    assert(u == unit_like(m, t, tf, true)->Some_0.0);
    assert(u is Arr && u->Arr_0.len() == 3 && u->Arr_0[j as int] == Val::Unit);
    let l0 = Loc { root: Root::Local(1), path: seq![] };
    assert(places(fr, PRes::At(l0), q.projection@, 0) == Some((PRes::At(l0), Seq::<Event>::empty())));
    assert(Seq::<Event>::empty() + seq![Event::Idx(j)] =~= seq![Event::Idx(j)]);
    let l1 = Loc { root: Root::Local(1), path: seq![PE::Index(j as nat)] };
    assert(seq![].push(PE::Index(j as nat)) =~= seq![PE::Index(j as nat)]);
    assert(eval_place(fr, q) == Some((PRes::At(l1), seq![Event::Idx(j)])));
    assert(seq![PE::Index(j as nat)].drop_first() =~= Seq::<PE>::empty());
    reveal_with_fuel(read_at, 2);
    assert(read_at(u, l1.path) == Val::Unit);
}

/// **Fact 8e.** A ghost result (the std row and a `ghost` policy key) at `[T; 0]` is `Arr([])`.
pub proof fn fact_ghost_arr(m: MirCrate, pol: CallPolicy, key: Seq<u8>, g: GenericArgs, t: Ty, vs: Seq<Val>, fr: Frame)
    requires m.tys@.len() >= 1, rigid(m, t) matches Some(RigidTy::Array(_, n)) && const_usize(m, n.id) == Some(0u64), zst_dest(m, t),
        pol.ghost_unit.contains(key), !pol.declassify.contains(key),
    ensures std_apply(m, StdFn::GhostNew, Some(t), vs, fr) == Some((Val::Arr(seq![]), fr, Seq::<Event>::empty(), 0nat)),
        leaf_call(m, pol, key, g, Some(t), vs, fr) == Some((Val::Arr(seq![]), fr, Seq::<Event>::empty(), 0nat)),
{
    arr0_ul(m, t);
}

/// **Fact 8f.** `Discriminant` of `Unit` at a one-variant enum that is not unit-like (`enum E {
/// A(u8) }`: a `Unit` there is uninitialized) is `None`.
pub proof fn fact_discr_unit_guard(m: MirCrate, b: Body, fr: Frame, p: Place)
    requires read_place(fr, p) matches Some((v, _)) && v is Unit,
        place_ty(m, b, p) matches Some(t) && rigid(m, t) matches Some(RigidTy::Adt(_, _)) && adt_row(m, t) matches Some(a)
            && a.kind is Enum && a.variants@.len() == 1 && a.variants@[0].discr == Some(0u128)
            && a.variants@[0].fields@.len() == 1 && rigid(m, a.variants@[0].fields@[0]) matches Some(RigidTy::Uint(UintTy::U8)),
    ensures rv_discr(m, b, fr, p) is None,
{
    let t = place_ty(m, b, p)->Some_0;
    let a = adt_row(m, t)->Some_0;
    let fs = a.variants@[0].fields@;
    let f = (tfuel(m) - 1) as nat;
    assert(unit_like(m, fs[0], f, true) is None);
    assert(unit_likes(m, fs, f, 1, true) is None);
    assert(unit_like(m, t, tfuel(m), true) is None);
}

/// **Fact 8g.** `wt_val`'s `wt_rec` takes both forms of `()` and only `Arr([])` for `[T; 0]`.
pub proof fn fact_wt_forms(m: MirCrate, u: Ty, t: Ty)
    requires m.tys@.len() >= 1, rigid(m, u) matches Some(RigidTy::Tuple(ts)) && ts@.len() == 0,
        rigid(m, t) matches Some(RigidTy::Array(_, n)) && const_usize(m, n.id) == Some(0u64),
    ensures wt_rec(m, u, Val::Unit), wt_rec(m, u, Val::Tup(seq![])), wt_rec(m, t, Val::Arr(seq![])), !wt_rec(m, t, Val::Unit),
{
    let ts = rigid(m, u)->Some_0->Tuple_0@;
    assert(unit_likes(m, ts, (tfuel(m) - 1) as nat, 0, true) == Some((Seq::<Val>::empty(), 0nat)));
    assert(!has_arr(m, u, tfuel(m)));
    arr0_ul(m, t);
}

// ------------------------------------------------------------------ 8h. consumers see both forms alike
//
// A one-variant enum `E { A = 5 }` (unit-like, no array) has two forms: the canonical `Unit` (a
// `ZeroSized` constant, an entry local, a ghost result) and `Adt(0, [])` (an aggregate, a decoded
// constant). `F { A(E) }` likewise: `Unit` or `Adt(0, [Adt(0, [])])`. Each fact runs one consumer
// on both forms and ends in the same observable. (A `Declass(v)` event carries the form; the
// translator admits only plain declassify arguments, `declass_arg_ok`.)

pub open spec fn e_ok(m: MirCrate, e: Ty) -> bool {
    m.tys@.len() >= 1 && (rigid(m, e) matches Some(RigidTy::Adt(_, _))) && (adt_row(m, e) matches Some(a) && !a.is_box && a.kind is Enum
        && a.variants@.len() == 1 && a.variants@[0].discr == Some(5u128) && a.variants@[0].fields@.len() == 0)
}

pub open spec fn f_ok(m: MirCrate, f: Ty, e: Ty) -> bool {
    e_ok(m, e) && m.tys@.len() >= 2 && (rigid(m, f) matches Some(RigidTy::Adt(_, _))) && (adt_row(m, f) matches Some(a) && !a.is_box && a.kind is Enum
        && a.variants@.len() == 1 && a.variants@[0].fields@.len() == 1 && a.variants@[0].fields@[0] == e)
}

proof fn e_ul(m: MirCrate, e: Ty)
    requires e_ok(m, e),
    ensures unit_like(m, e, tfuel(m), true) is Some,
{
    let a = adt_row(m, e)->Some_0;
    assert(unit_likes(m, a.variants@[0].fields@, (tfuel(m) - 1) as nat, 0, true) == Some((Seq::<Val>::empty(), 0nat)));
}

/// **Fact 8h-1 (Discriminant).** `Discriminant` of either form of E is 5.
pub proof fn fact_discr_forms(m: MirCrate, b: Body, f1: Frame, f2: Frame, p: Place, ev: Seq<Event>)
    requires read_place(f1, p) == Some((Val::Unit, ev)), read_place(f2, p) == Some((Val::Adt(0, seq![]), ev)),
        place_ty(m, b, p) matches Some(e) && e_ok(m, e),
    ensures rv_discr(m, b, f1, p) == Some((Val::Int(5), ev, 0nat)), rv_discr(m, b, f2, p) == Some((Val::Int(5), ev, 0nat)),
{
    e_ul(m, place_ty(m, b, p)->Some_0);
}

/// **Fact 8h-2 (Downcast and Field navigation).** `(_1 as A).0` of either form of F, then its
/// `Discriminant`: no events, and 5 on both.
pub proof fn fact_nav_forms(m: MirCrate, b: Body, fr: Frame, q: Place, f: Ty, e: Ty)
    requires f_ok(m, f, e), q.local == 1, q.projection@.len() == 2, q.projection@[0] matches ProjectionElem::Downcast(k) && k == 0,
        q.projection@[1] matches ProjectionElem::Field(i, ft) && i == 0 && ft == e, b.locals@.len() == 2, b.locals@[1].ty == f,
        fr.locals.len() == 2,
    ensures ({
        let s = put_local(fr, 1, Val::Adt(0, seq![Val::Adt(0, seq![])]));
        let u = put_local(fr, 1, Val::Unit);
        &&& read_place(s, q) == Some((Val::Adt(0, seq![]), Seq::<Event>::empty()))
        &&& read_place(u, q) == Some((Val::Unit, Seq::<Event>::empty()))
        &&& rv_discr(m, b, s, q) == Some((Val::Int(5), Seq::<Event>::empty(), 0nat))
        &&& rv_discr(m, b, u, q) == Some((Val::Int(5), Seq::<Event>::empty(), 0nat))
    }),
{
    let e0 = Seq::<Event>::empty();
    assert(e0 + e0 =~= e0);
    let ps = q.projection@;
    let pv = seq![PE::Variant(0)];
    let pf = seq![PE::Variant(0), PE::Field(0)];
    assert(seq![].push(PE::Variant(0)) =~= pv);
    assert(pv.push(PE::Field(0)) =~= pf);
    assert(pf.drop_first() =~= seq![PE::Field(0)]);
    assert(seq![PE::Field(0)].drop_first() =~= Seq::<PE>::empty());
    let l0 = Loc { root: Root::Local(1), path: seq![] };
    let lf = Loc { root: Root::Local(1), path: pf };
    let s = put_local(fr, 1, Val::Adt(0, seq![Val::Adt(0, seq![])]));
    let u = put_local(fr, 1, Val::Unit);
    assert(places(s, PRes::At(l0), ps, 0) == Some((PRes::At(l0), e0)));
    assert(places(u, PRes::At(l0), ps, 0) == Some((PRes::At(l0), e0)));
    let lv = Loc { root: Root::Local(1), path: pv };
    assert(places(s, PRes::At(l0), ps, 1) == Some((PRes::At(lv), e0)));
    assert(places(u, PRes::At(l0), ps, 1) == Some((PRes::At(lv), e0)));
    assert(places(s, PRes::At(l0), ps, 2) == Some((PRes::At(lf), e0)));
    assert(places(u, PRes::At(l0), ps, 2) == Some((PRes::At(lf), e0)));
    reveal_with_fuel(read_at, 3);
    assert(read_at(Val::Adt(0, seq![Val::Adt(0, seq![])]), pf) == Val::Adt(0, seq![]));
    assert(read_at(Val::Unit, pf) == Val::Unit);
    assert(tys_along(m, f, ps, 0) == Some(f));
    assert(tys_along(m, f, ps, 1) == Some(f));
    assert(place_ty(m, b, q) == Some(e));
    e_ul(m, e);
}

/// **Fact 8h-3 (Copy and Move).** Reading either form has no events and no charge: the operand
/// is the form, unchanged.
pub proof fn fact_copy_forms(m: MirCrate, fr: Frame, p: Place)
    requires local0(p, 1), fr.locals.len() == 2,
    ensures eval_op(m, put_local(fr, 1, Val::Unit), Operand::Copy(p)) == Some((Val::Unit, Seq::<Event>::empty(), 0nat)),
        eval_op(m, put_local(fr, 1, Val::Adt(0, seq![])), Operand::Copy(p)) == Some((Val::Adt(0, seq![]), Seq::<Event>::empty(), 0nat)),
        eval_op(m, put_local(fr, 1, Val::Unit), Operand::Move(p)) == Some((Val::Unit, Seq::<Event>::empty(), 0nat)),
        eval_op(m, put_local(fr, 1, Val::Adt(0, seq![])), Operand::Move(p)) == Some((Val::Adt(0, seq![]), Seq::<Event>::empty(), 0nat)),
{
}

/// **Fact 8h-4 (Ref and Deref).** `_2 = &_1` of either form of E, then `Discriminant(*_2)`: 5 on both.
pub proof fn fact_ref_forms(m: MirCrate, b: Body, fr: Frame, p1: Place, q: Place, e: Ty)
    requires e_ok(m, e), local0(p1, 1), q.local == 2, q.projection@.len() == 1, q.projection@[0] is Deref, fr.locals.len() == 3,
        b.locals@.len() == 3, rigid(m, b.locals@[2].ty) matches Some(RigidTy::Ref(_, pt, _)) && pt == e,
    ensures ({
        let su = put_local(fr, 1, Val::Unit);
        let ss = put_local(fr, 1, Val::Adt(0, seq![]));
        &&& rv_ref(su, BorrowKind::Shared, p1) == Some((Val::Shr(Box::new(Val::Unit)), Seq::<Event>::empty(), 0nat))
        &&& rv_ref(ss, BorrowKind::Shared, p1) == Some((Val::Shr(Box::new(Val::Adt(0, seq![]))), Seq::<Event>::empty(), 0nat))
        &&& rv_discr(m, b, put_local(su, 2, Val::Shr(Box::new(Val::Unit))), q) == Some((Val::Int(5), Seq::<Event>::empty(), 0nat))
        &&& rv_discr(m, b, put_local(ss, 2, Val::Shr(Box::new(Val::Adt(0, seq![])))), q) == Some((Val::Int(5), Seq::<Event>::empty(), 0nat))
    }),
{
    let e0 = Seq::<Event>::empty();
    assert(e0 + e0 =~= e0);
    let l2 = Loc { root: Root::Local(2), path: seq![] };
    let fu = put_local(put_local(fr, 1, Val::Unit), 2, Val::Shr(Box::new(Val::Unit)));
    let fs = put_local(put_local(fr, 1, Val::Adt(0, seq![])), 2, Val::Shr(Box::new(Val::Adt(0, seq![]))));
    assert(places(fu, PRes::At(l2), q.projection@, 0) == Some((PRes::At(l2), e0)));
    assert(places(fs, PRes::At(l2), q.projection@, 0) == Some((PRes::At(l2), e0)));
    assert(tys_along(m, b.locals@[2].ty, q.projection@, 0) == Some(b.locals@[2].ty));
    assert(place_ty(m, b, q) == Some(e));
    e_ul(m, e);
}

/// **Fact 8h-5 (call-argument passing).** Either form passes to a non-`&mut` parameter, with the
/// same (`Unit`) slot: the callee's entry differs only in the parameter holding the form.
pub proof fn fact_arg_forms(m: MirCrate, cb: Body, fr: Frame)
    requires cb.arg_count == 1, cb.locals@.len() >= 2, !is_mut_ref(m, cb.locals@[1].ty),
    ensures args_ok(m, cb, fr, seq![Val::Unit]), args_ok(m, cb, fr, seq![Val::Adt(0, seq![])]),
        call_slots(m, cb, fr, seq![Val::Unit]) == call_slots(m, cb, fr, seq![Val::Adt(0, seq![])]),
        call_slots(m, cb, fr, seq![Val::Unit]) == seq![Val::Unit],
{
    assert(arg_ok(m, cb, fr, seq![Val::Unit], 0));
    assert(arg_ok(m, cb, fr, seq![Val::Adt(0, seq![])], 0));
    assert(call_slots(m, cb, fr, seq![Val::Unit]) =~= seq![Val::Unit]);
    assert(call_slots(m, cb, fr, seq![Val::Adt(0, seq![])]) =~= seq![Val::Unit]);
}

/// **Fact 8h-6 (Drop).** Dropping a place of a type whose drop shim is empty: on either form a
/// jump with the place's events and cost 1, the frame unchanged.
pub proof fn fact_drop_forms(m: MirCrate, pol: CallPolicy, b: Body, fr: Frame, p: Place, tb: nat, fuel: nat)
    requires local0(p, 1), fr.locals.len() == 2, b.locals@.len() == 2, drop_row(m, b.locals@[1].ty) matches Some(d) && d.empty,
    ensures drop_step(m, pol, b, p, tb, put_local(fr, 1, Val::Unit), fuel) == Step::Jump(tb, put_local(fr, 1, Val::Unit), Seq::<Event>::empty(), 1),
        drop_step(m, pol, b, p, tb, put_local(fr, 1, Val::Adt(0, seq![])), fuel)
            == Step::Jump(tb, put_local(fr, 1, Val::Adt(0, seq![])), Seq::<Event>::empty(), 1),
{
}

/// **Fact 8h-7 (a std row given a unit-like value).** `Ghost::assume_new_fallback` given either
/// form gives the same result.
pub proof fn fact_std_forms(m: MirCrate, t: Ty, fr: Frame)
    requires zst_dest(m, t),
    ensures std_apply(m, StdFn::GhostNew, Some(t), seq![Val::Unit], fr) == std_apply(m, StdFn::GhostNew, Some(t), seq![Val::Adt(0, seq![])], fr),
{
}

} // verus!
