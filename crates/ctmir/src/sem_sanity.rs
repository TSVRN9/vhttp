//! Sanity facts about `sem`, proved over small crates built here (each builder's `ensures` is the
//! premise of its lemmas, so none is vacuous). Step and event counts are worked by hand from the
//! spec's tables in the comments.
#[allow(unused_imports)]
use crate::json::Json;
use crate::mir::*;
#[cfg(verus_keep_ghost)]
use crate::sem::*;
#[cfg(verus_keep_ghost)]
use ctcore::sem::{binop, read_at, Event, Frame, Loc, Root, Val, PE};
#[cfg(verus_keep_ghost)]
use ctcore::syntax::{BinOp as COp, IntTy as CTy};
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

fn body(blocks: Vec<BasicBlock>, locals: Vec<LocalDecl>, arg_count: usize) -> (b: Body)
    ensures b.blocks@ == blocks@, b.locals@ == locals@, b.arg_count == arg_count,
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
    && m.tys@.len() == 3
    && m.tys@[0].id == 2 && (m.tys@[0].kind matches TyKind::RigidTy(RigidTy::Uint(UintTy::U8)))
    && m.tys@[1].id == 1 && (m.tys@[1].kind matches TyKind::RigidTy(RigidTy::Uint(UintTy::Usize)))
    && m.tys@[2].id == 3 && (m.tys@[2].kind matches TyKind::RigidTy(RigidTy::Ref(_, _, mu)) && mu is Not)
    && {
        let b = m.insts@[0].body->Some_0;
        b.arg_count == 2 && b.locals@.len() == 7 && b.blocks@.len() == 2
        && b.locals@[0].ty == 2 && b.locals@[1].ty == 3 && b.locals@[2].ty == 1 && b.locals@[4].ty == 2 && b.locals@[5].ty == 1
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
    krate(insts, Vec::new(), Vec::new(), tys, Vec::new(), Vec::new())
}

pub open spec fn tb(m: MirCrate) -> Body { m.insts@[0].body->Some_0 }

proof fn tiny_tys(m: MirCrate)
    requires tiny_ok(m),
    ensures int_ty(m, 2) == Some(CTy::U8), int_ty(m, 1) == Some(CTy::Usize), !is_mut_ref(m, 1), !is_mut_ref(m, 3),
        !charged(m, 1), !charged(m, 2), dfuel(m) == 4,
{
    reveal_with_fuel(find_from, 4);
}

/// A u8 constant (1 byte) or usize constant (8 bytes) evaluates to its value, at no charge.
proof fn tiny_const(m: MirCrate, fr: Frame, op: Operand, x: u8, wide: bool)
    requires tiny_ok(m), if wide { cint(op, 1, b8(x)) } else { cint(op, 2, b1(x)) },
    ensures eval_op(m, fr, op) == Some((Val::Int(x as u128), seq![], 0nat)),
{
    tiny_tys(m);
    reveal_with_fuel(find_from, 3);
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

/// bb1 from `fr_a`: its statements (2 steps, `[Idx(i & 3)]`) then the Return (1 step).
proof fn tiny_run_bb1(m: MirCrate, pol: CallPolicy, a: Seq<Val>, i: u128, fuel: nat)
    requires tiny_ok(m), fuel >= 1, i < 0x1_0000_0000_0000_0000, a.len() == 4,
        forall|k: int| 0 <= k < 4 ==> (#[trigger] a[k]) is Int && a[k]->Int_0 < 256,
    ensures run_block(m, pol, tb(m), 1, fr_a(tiny_fr0(a, i), i), fuel)
        == Some((fr_b(fr_a(tiny_fr0(a, i), i), a, i), seq![Event::Idx(i & 3)], 3nat)),
{
    let b = tb(m);
    let fa = fr_a(tiny_fr0(a, i), i);
    tiny_bitand(i);
    assert(a[(i & 3) as int] is Int);
    tiny_bb1_stmts(m, fa, a, i);
    let fb = fr_b(fa, a, i);
    assert(step_term(m, pol, b, b.blocks@[1].terminator.kind, fb, fuel) == Some(Step::Done(fb, Seq::<Event>::empty(), 1nat)));
    assert(seq![Event::Idx(i & 3)] + Seq::<Event>::empty() =~= seq![Event::Idx(i & 3)]);
}

/// bb0's Assert(move _6, true): `_6 == 1`, so `Cond(1)` and on to bb1; cost 1.
proof fn tiny_term0(m: MirCrate, pol: CallPolicy, a: Seq<Val>, i: u128, fuel: nat)
    requires tiny_ok(m),
    ensures step_term(m, pol, tb(m), tb(m).blocks@[0].terminator.kind, fr_a(tiny_fr0(a, i), i), fuel)
        == Some(Step::Jump(1, fr_a(tiny_fr0(a, i), i), seq![Event::Cond(1)], 1nat)),
{
    let fa = fr_a(tiny_fr0(a, i), i);
    assert(eval_op(m, fa, tb(m).blocks@[0].terminator.kind->Assert_cond) == Some((Val::Int(1), Seq::<Event>::empty(), 0nat)));
    assert(Seq::<Event>::empty() + seq![Event::Cond(1)] =~= seq![Event::Cond(1)]);
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
    let b = tb(m);
    let fr0 = tiny_fr0(a, i);
    let fa = fr_a(fr0, i);
    let fb = fr_b(fa, a, i);
    tiny_entry(m, a, i);
    tiny_bb0_stmts(m, fr0, i);
    tiny_term0(m, pol, a, i, fuel);
    tiny_run_bb1(m, pol, a, i, (fuel - 1) as nat);
    assert(Seq::<Event>::empty() + seq![Event::Cond(1)] + seq![Event::Idx(i & 3)] =~= seq![Event::Cond(1), Event::Idx(i & 3)]);
    assert(run_block(m, pol, b, 0, fr0, fuel) == Some((fb, seq![Event::Cond(1), Event::Idx(i & 3)], 7nat)));
}

// ================================================================== 2. Drop of a Vec<u8>
//
// `fn f(v: Vec<u8>) { }`-shaped: _1: Vec<u8> (ty 5 = Adt(Vec, [u8, Global])); bb0: drop(_1) -> bb1;
// bb1: return. The `drops` row for ty 5 has a non-empty glue, but `Vec<int>`'s glue is the std-model
// leaf (decision 4): the Drop costs 1 and leaves the frame as it was. Steps: Drop 1 + Return 1 = 2.

pub open spec fn drop_ok(m: MirCrate) -> bool {
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

pub fn drop_crate() -> (m: MirCrate) ensures drop_ok(m) {
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
    requires drop_ok(m), fr.locals.len() == 2, fuel >= 2,
    ensures mir_run_fn(m, pol, 0, fr, fuel) == Some((fr, Seq::<Event>::empty(), 2nat)),
{
    let b = m.insts@[0].body->Some_0;
    let e = Seq::<Event>::empty();
    reveal_with_fuel(find_from, 3);
    assert(vec_elem(m, 5) == Some(2usize));
    assert(int_ty(m, 2) == Some(CTy::U8));
    assert(vec_int(m, 5));
    assert(place_ty(m, b, b.blocks@[0].terminator.kind->Drop_place) == Some(5usize));
    tiny_store0(fr, b.blocks@[0].terminator.kind->Drop_place, 1, Val::Unit);
    assert(exec_stmts(m, b, fr, b.blocks@[0].statements@, 0) == Some((fr, e, 0nat)));
    assert(step_term(m, pol, b, b.blocks@[0].terminator.kind, fr, fuel) == Some(Step::Jump(1, fr, e, 1nat)));
    assert(step_term(m, pol, b, b.blocks@[1].terminator.kind, fr, (fuel - 1) as nat) == Some(Step::Done(fr, e, 1nat)));
    assert(e + e =~= e);
    assert(run_block(m, pol, b, 1, fr, (fuel - 1) as nat) == Some((fr, e, 1nat)));
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
    m.tys@.len() == 1 && m.allocs@.len() == 0 && m.tys@[0].id == 6 && (m.tys@[0].kind matches TyKind::RigidTy(RigidTy::Adt(_, _)))
    && m.adts@.len() == 1 && m.adts@[0].ty == 6 && !m.adts@[0].is_box && m.adts@[0].kind is Enum
    && m.adts@[0].variants@.len() == 2 && m.adts@[0].variants@[0].fields@.len() == 0
    && m.layouts@.len() == 1 && m.layouts@[0].ty == 6
    && {
        let l = m.layouts@[0].shape;
        (l.fields matches FieldsShape::Arbitrary { offsets } && offsets@.len() == 1 && offsets@[0].num_bits == 0)
        && (l.variants matches VariantsShape::Multiple { tag, tag_encoding, tag_field, variants }
            && tag_field == 0 && variants@.len() == 2 && variants@[0].offsets@.len() == 0
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
    let mut f1 = Vec::new();
    f1.push(7);
    let mut vars = Vec::new();
    vars.push(AdtVariant { discr: Some(0), fields: Vec::new() });
    vars.push(AdtVariant { discr: Some(1), fields: f1 });
    let mut adts = Vec::new();
    adts.push(Adt { ty: 6, name: Vec::new(), kind: AdtKind::Enum, is_box: false, variants: vars });
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
    let mut layouts = Vec::new();
    layouts.push(LayoutRow { ty: 6, shape });
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
    assert(dfuel(m) == 2);
    assert(dec_adt(m, 6, a, 0, 1) == Some((Val::Adt(0, seq![]), 1nat)));
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

pub open spec fn call_ok(m: MirCrate) -> bool {
    m.insts@.len() == 2 && m.insts@[0].id == 0 && m.insts@[1].id == 1 && m.insts@[0].kind is Item && m.insts@[1].kind is Item
    && m.insts@[0].body is Some && m.insts@[1].body is Some && m.insts@[1].key@.len() == 0
    && m.tys@.len() == 2 && m.tys@[0].id == 2 && (m.tys@[0].kind matches TyKind::RigidTy(RigidTy::Uint(UintTy::U8)))
    && m.tys@[1].id == 4 && (m.tys@[1].kind matches TyKind::RigidTy(RigidTy::Ref(_, p, mu)) && p == 2 && mu is Mut)
    && m.calls@.len() == 1 && m.calls@[0].fn_ty == 8 && m.calls@[0].resolved == Some(1usize) && m.calls@[0].args.0@.len() == 0
    && {
        let c = m.insts@[0].body->Some_0;
        c.arg_count == 1 && c.locals@.len() == 3 && c.locals@[1].ty == 2 && c.locals@[2].ty == 4 && c.blocks@.len() == 2
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
        f.arg_count == 1 && f.locals@.len() == 2 && f.locals@[1].ty == 4 && f.blocks@.len() == 1
        && f.blocks@[0].statements@.len() == 1
        && (f.blocks@[0].statements@[0].kind matches StatementKind::Assign(p, rv) && p.local == 1 && p.projection@.len() == 1
            && p.projection@[0] is Deref && (rv matches Rvalue::Use(x, _) && cint(x, 2, b1(7))))
        && f.blocks@[0].terminator.kind is Return
    }
}

fn zst_fn(ty: Ty) -> (op: Operand) ensures op matches Operand::Constant(k) && k.const_.ty == ty {
    Operand::Constant(ConstOperand { span: 0, user_ty: Json::Null, const_: MirConst { kind: ConstantKind::ZeroSized, ty, id: 0 } })
}

pub fn call_crate() -> (m: MirCrate) ensures call_ok(m) {
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
    krate(insts, calls, Vec::new(), tys, Vec::new(), Vec::new())
}

pub open spec fn l1() -> Loc { Loc { root: Root::Local(1), path: seq![] } }
pub open spec fn s0() -> Loc { Loc { root: Root::Slot(0), path: seq![] } }

pub open spec fn cfr_in(x: u128) -> Frame { Frame { locals: seq![Val::Unit, Val::Mut(s0())], slots: seq![Val::Int(x)] } }
pub open spec fn cfr_out() -> Frame { Frame { locals: seq![Val::Unit, Val::Mut(s0())], slots: seq![Val::Int(7)] } }

/// The callee's `(*_1) = 7`: `_1` holds `Mut(Slot(0))`, so the write lands in slot 0. Cost 1.
proof fn callee_stmt(m: MirCrate, x: u128)
    requires call_ok(m),
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
    requires call_ok(m), fuel >= 1,
    ensures mir_run_fn(m, pol, 1, cfr_in(x), fuel) == Some((cfr_out(), Seq::<Event>::empty(), 2nat)),
{
    let f = m.insts@[1].body->Some_0;
    let e = Seq::<Event>::empty();
    assert(e + e =~= e);
    callee_stmt(m, x);
    assert(exec_stmts(m, f, cfr_in(x), f.blocks@[0].statements@, 0) == Some((cfr_in(x), e, 0nat)));
    assert(exec_stmts(m, f, cfr_in(x), f.blocks@[0].statements@, 1) == Some((cfr_out(), e, 1nat)));
    assert(step_term(m, pol, f, f.blocks@[0].terminator.kind, cfr_out(), fuel) == Some(Step::Done(cfr_out(), e, 1nat)));
    assert(run_block(m, pol, f, 0, cfr_in(x), fuel) == Some((cfr_out(), e, 2nat)));
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

pub open spec fn call_fr1(x: u128) -> Frame { Frame { locals: seq![Val::Unit, Val::Int(x), Val::Mut(l1())], slots: seq![] } }
pub open spec fn call_fr2() -> Frame { Frame { locals: seq![Val::Unit, Val::Int(7), Val::Mut(l1())], slots: seq![] } }

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

/// Entering f: `_2`'s location passes the `&mut` check, slot 0 gets `_1`'s value `x`.
proof fn call_enter(m: MirCrate, x: u128)
    requires call_ok(m),
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
    assert(mir_entry(m, 1, vs, seq![Val::Int(x)]).locals =~= cfr_in(x).locals);
}

pub open spec fn call_fw() -> Frame { Frame { locals: seq![Val::Unit, Val::Int(7), Val::Mut(l1())], slots: seq![] } }

/// Leaving f: its return value is `Unit` (a `()` body never writes `_0`); slot 0 (7) is written
/// back to the caller's `_1`.
proof fn call_leave(m: MirCrate, x: u128)
    requires call_ok(m),
    ensures return_to(m, m.insts@[1].body->Some_0, call_fr1(x), seq![Val::Mut(l1())], cfr_out()) == Some((Val::Unit, call_fw())),
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
    requires call_ok(m), fuel >= 2, !pol.declassify.contains(Seq::<u8>::empty()), !pol.ghost_unit.contains(Seq::<u8>::empty()),
    ensures step_term(m, pol, m.insts@[0].body->Some_0, (m.insts@[0].body->Some_0).blocks@[0].terminator.kind, call_fr1(x), fuel)
        == Some(Step::Jump(1, call_fr2(), Seq::<Event>::empty(), 3nat)),
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
    assert(store(call_fw(), Loc { root: Root::Local(0), path: seq![] }, Val::Unit) == Some(call_fr2())) by {
        assert(call_fw().locals.update(0, Val::Unit) =~= call_fr2().locals);
    };
}

pub open spec fn call_fr0(x: u128) -> Frame { Frame { locals: seq![Val::Unit, Val::Int(x), Val::Unit], slots: seq![] } }

/// The caller's `_2 = &mut _1`: `Mut` of `_1`'s location. Cost 1.
proof fn caller_stmt(m: MirCrate, x: u128)
    requires call_ok(m),
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
    requires call_ok(m), fuel >= 2, !pol.declassify.contains(Seq::<u8>::empty()), !pol.ghost_unit.contains(Seq::<u8>::empty()),
    ensures mir_run_fn(m, pol, 0, mir_entry(m, 0, seq![Val::Int(x)], seq![]), fuel) == Some((call_fr2(), Seq::<Event>::empty(), 5nat)),
        call_fr2().locals[1] == Val::Int(7),
{
    reveal_with_fuel(find_from, 2);
    let c = m.insts@[0].body->Some_0;
    let e = Seq::<Event>::empty();
    assert(e + e =~= e);
    assert(e + e + e =~= e);
    assert(!is_mut_ref(m, 2));
    assert(mir_entry(m, 0, seq![Val::Int(x)], seq![]).locals =~= call_fr0(x).locals);
    caller_stmt(m, x);
    assert(exec_stmts(m, c, call_fr0(x), c.blocks@[0].statements@, 0) == Some((call_fr0(x), e, 0nat)));
    assert(exec_stmts(m, c, call_fr0(x), c.blocks@[0].statements@, 1) == Some((call_fr1(x), e, 1nat)));
    call_term(m, pol, x, fuel);
    assert(exec_stmts(m, c, call_fr2(), c.blocks@[1].statements@, 0) == Some((call_fr2(), e, 0nat)));
    assert(step_term(m, pol, c, c.blocks@[1].terminator.kind, call_fr2(), (fuel - 1) as nat) == Some(Step::Done(call_fr2(), e, 1nat)));
    assert(run_block(m, pol, c, 1, call_fr2(), (fuel - 1) as nat) == Some((call_fr2(), e, 1nat)));
    assert(run_block(m, pol, c, 0, call_fr0(x), fuel) == Some((call_fr2(), e, 5nat)));
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

// ------------------------------------------------------------------ the builders run

#[test]
fn sanity_builders() {
    let _ = (tiny_crate(), drop_crate(), niche_crate(), call_crate(), index2_place());
}

} // verus!
