//! Spec semantics of the core language (trusted): values, places, statements, intrinsics, calls
//! and fuelled runs that return the final frame, the leakage event trace and the step count.
//! Totality: shape mismatches read `Unit` and make writes no-ops; out-of-bounds indices read
//! `Unit` and make writes no-ops. Only `Abort`, a failed `Assert`, fuel exhaustion, Vec length
//! overflow, and (excluded by `wf`) an out-of-range fn or block index give `None`.
#[allow(unused_imports)]
use crate::syntax::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ values

/// `Int(n)` holds a raw bit pattern: the low `bits(ty)` bits of the value, zero-extended to
/// u128. The width comes from the instruction, not the value.
pub enum Val { Int(u128), Unit, Tup(Seq<Val>), Adt(nat, Seq<Val>), Arr(Seq<Val>), Shr(Box<Val>), Mut(Loc) }

/// A local or slot of the current frame plus a resolved path.
pub struct Loc { pub root: Root, pub path: Seq<PE> }

pub enum Root { Local(nat), Slot(nat) }

pub enum PE { Field(nat), Index(nat), Variant(nat) }

/// Slot `j` holds the copied-in pointee of parameter `1 + j` when that parameter is `&mut`.
pub struct Frame { pub locals: Seq<Val>, pub slots: Seq<Val> }

pub enum Event { Cond(u128), Idx(u128), DivOps(u128, u128), Shamt(u128), Declass(Val), Alloc(u128), Range(u128, u128) }

pub type Res = Option<(Frame, Seq<Event>, nat)>;

pub spec const USIZE_MAX: nat = 0xffff_ffff_ffff_ffff;

// ------------------------------------------------------------------ arithmetic

pub open spec fn bits(ty: IntTy) -> nat {
    match ty {
        IntTy::U8 | IntTy::I8 => 8,
        IntTy::U16 | IntTy::I16 => 16,
        IntTy::U32 | IntTy::I32 => 32,
        IntTy::U64 | IntTy::I64 | IntTy::Usize | IntTy::Isize => 64,
        IntTy::U128 | IntTy::I128 => 128,
        IntTy::Bool => 1,
    }
}

pub open spec fn signed(ty: IntTy) -> bool {
    ty is I8 || ty is I16 || ty is I32 || ty is I64 || ty is I128 || ty is Isize
}

/// The low `bits(ty)` bits of `x` (two's complement for negative `x`).
pub open spec fn trunc(ty: IntTy, x: int) -> u128 {
    (x % (vstd::arithmetic::power2::pow2(bits(ty)) as int)) as u128
}

/// Unsigned reading of the low `bits(ty)` bits of `a`.
pub open spec fn uval(ty: IntTy, a: u128) -> int {
    (a as int) % (vstd::arithmetic::power2::pow2(bits(ty)) as int)
}

/// Reading of `a` at type `ty`: two's complement for signed types.
pub open spec fn ival(ty: IntTy, a: u128) -> int {
    let u = uval(ty, a);
    if signed(ty) && u >= vstd::arithmetic::power2::pow2((bits(ty) - 1) as nat) { u - vstd::arithmetic::power2::pow2(bits(ty)) } else { u }
}

pub open spec fn abs(x: int) -> int { if x < 0 { -x } else { x } }

/// Division truncating toward zero, as Rust's `/` on signed ints.
pub open spec fn tdiv(x: int, y: int) -> int {
    let q = abs(x) / abs(y);
    if (x < 0) != (y < 0) { -q } else { q }
}

/// Remainder with the sign of the dividend, as Rust's `%` on signed ints.
pub open spec fn trem(x: int, y: int) -> int {
    let r = abs(x) % abs(y);
    if x < 0 { -r } else { r }
}

pub open spec fn b2i(b: bool) -> u128 { if b { 1 } else { 0 } }

/// Rust's release-mode (wrapping) binary operators at type `ty`: shifts mask the amount to the
/// bit width, `/` and `%` by 0 give 0, comparisons give 0/1.
#[verifier::opaque]
pub open spec fn binop(op: BinOp, ty: IntTy, a: u128, b: u128) -> u128 {
    let (x, y) = (ival(ty, a), ival(ty, b));
    let sh = (uval(ty, b) % (bits(ty) as int)) as nat;
    match op {
        BinOp::Add => trunc(ty, x + y),
        BinOp::Sub => trunc(ty, x - y),
        BinOp::Mul => trunc(ty, x * y),
        BinOp::Div => if y == 0 { 0 } else { trunc(ty, tdiv(x, y)) },
        BinOp::Rem => if y == 0 { 0 } else { trunc(ty, trem(x, y)) },
        BinOp::BitXor => trunc(ty, (a ^ b) as int),
        BinOp::BitAnd => trunc(ty, (a & b) as int),
        BinOp::BitOr => trunc(ty, (a | b) as int),
        BinOp::Shl => trunc(ty, x * vstd::arithmetic::power2::pow2(sh)),
        BinOp::Shr => trunc(ty, x / (vstd::arithmetic::power2::pow2(sh) as int)),
        BinOp::Eq => b2i(x == y),
        BinOp::Ne => b2i(x != y),
        BinOp::Lt => b2i(x < y),
        BinOp::Le => b2i(x <= y),
        BinOp::Gt => b2i(x > y),
        BinOp::Ge => b2i(x >= y),
    }
}

/// `!` (bitwise; on Bool, logical) and wrapping negation at type `ty`.
#[verifier::opaque]
pub open spec fn unop(op: UnOp, ty: IntTy, a: u128) -> u128 {
    match op {
        UnOp::Not => trunc(ty, vstd::arithmetic::power2::pow2(bits(ty)) - 1 - uval(ty, a)),
        UnOp::Neg => trunc(ty, -ival(ty, a)),
    }
}

/// `as` between int types: sign-extends from a signed source, then truncates to `to`.
#[verifier::opaque]
pub open spec fn cast(from: IntTy, to: IntTy, a: u128) -> u128 {
    trunc(to, ival(from, a))
}

pub open spec fn as_int(v: Val) -> u128 {
    match v { Val::Int(n) => n, _ => 0 }
}

pub open spec fn op_ev(op: BinOp, a: u128, b: u128) -> Seq<Event> {
    match op {
        BinOp::Div | BinOp::Rem => seq![Event::DivOps(a, b)],
        BinOp::Shl | BinOp::Shr => seq![Event::Shamt(b)],
        _ => seq![],
    }
}

// ------------------------------------------------------------------ value navigation

pub open spec fn nth(vs: Seq<Val>, i: nat) -> Val {
    if i < vs.len() { vs[i as int] } else { Val::Unit }
}

/// `vs` extended with `Unit` to at least `n` elements.
pub open spec fn pad(vs: Seq<Val>, n: nat) -> Seq<Val> {
    if vs.len() < n { vs + Seq::new((n - vs.len()) as nat, |j: int| Val::Unit) } else { vs }
}

pub open spec fn get(v: Val, e: PE) -> Val {
    match (v, e) {
        (Val::Tup(vs), PE::Field(i)) => nth(vs, i),
        (Val::Adt(_, vs), PE::Field(i)) => nth(vs, i),
        (Val::Arr(vs), PE::Index(i)) => nth(vs, i),
        (Val::Adt(_, vs), PE::Variant(k)) => Val::Adt(k, vs),
        _ => Val::Unit,
    }
}

/// Writing through `Variant(k)` keeps the stored variant: only `SetDiscr` and aggregates change it.
pub open spec fn put(v: Val, e: PE, w: Val) -> Val {
    match (v, e) {
        (Val::Tup(vs), PE::Field(i)) => Val::Tup(pad(vs, i + 1).update(i as int, w)),
        (Val::Adt(k, vs), PE::Field(i)) => Val::Adt(k, pad(vs, i + 1).update(i as int, w)),
        (Val::Arr(vs), PE::Index(i)) => if i < vs.len() { Val::Arr(vs.update(i as int, w)) } else { v },
        (Val::Adt(k, _), PE::Variant(_)) => match w { Val::Adt(_, ws) => Val::Adt(k, ws), _ => v },
        _ => v,
    }
}

pub open spec fn read_at(v: Val, path: Seq<PE>) -> Val
    decreases path.len(),
{
    if path.len() == 0 { v } else { read_at(get(v, path[0]), path.drop_first()) }
}

pub open spec fn write_at(v: Val, path: Seq<PE>, w: Val) -> Val
    decreases path.len(),
{
    if path.len() == 0 { w } else { put(v, path[0], write_at(get(v, path[0]), path.drop_first(), w)) }
}

/// Every `Arr` inside `v` has length <= usize::MAX.
pub open spec fn len_ok(v: Val) -> bool
    decreases v,
{
    match v {
        Val::Tup(vs) => forall|i: int| 0 <= i < vs.len() ==> len_ok(#[trigger] vs[i]),
        Val::Adt(_, vs) => forall|i: int| 0 <= i < vs.len() ==> len_ok(#[trigger] vs[i]),
        Val::Arr(vs) => vs.len() <= USIZE_MAX && forall|i: int| 0 <= i < vs.len() ==> len_ok(#[trigger] vs[i]),
        Val::Shr(b) => len_ok(*b),
        _ => true,
    }
}

// ------------------------------------------------------------------ frames and places

pub open spec fn read_loc(fr: Frame, l: Loc) -> Val {
    match l.root {
        Root::Local(i) => read_at(nth(fr.locals, i), l.path),
        Root::Slot(j) => read_at(nth(fr.slots, j), l.path),
    }
}

pub open spec fn write_loc(fr: Frame, l: Loc, w: Val) -> Frame {
    match l.root {
        Root::Local(i) => if i < fr.locals.len() {
            Frame { locals: fr.locals.update(i as int, write_at(fr.locals[i as int], l.path, w)), ..fr }
        } else { fr },
        Root::Slot(j) => if j < fr.slots.len() {
            Frame { slots: fr.slots.update(j as int, write_at(fr.slots[j as int], l.path, w)), ..fr }
        } else { fr },
    }
}

pub open spec fn local_loc(x: nat) -> Loc { Loc { root: Root::Local(x), path: seq![] } }

/// Place-walk cursor: still at a location (`L`), or inside a `Shr` snapshot (`V`).
pub enum Cur { L(Loc), V(Val) }

pub open spec fn descend(c: Cur, e: PE) -> Cur {
    match c {
        Cur::L(l) => Cur::L(Loc { root: l.root, path: l.path.push(e) }),
        Cur::V(v) => Cur::V(get(v, e)),
    }
}

/// One projection. `Deref` follows a `Mut` (switching root and path) or enters a `Shr`
/// snapshot; `Index(x)` reads local `x` as an Int and emits `Idx`.
pub open spec fn step(fr: Frame, c: Cur, p: Proj) -> (Cur, Seq<Event>) {
    match p {
        Proj::Deref => {
            let v = match c { Cur::L(l) => read_loc(fr, l), Cur::V(v) => v };
            (match v {
                Val::Mut(l2) => match c { Cur::L(_) => Cur::L(l2), Cur::V(_) => Cur::V(Val::Unit) },
                Val::Shr(b) => Cur::V(*b),
                _ => Cur::V(Val::Unit),
            }, seq![])
        },
        Proj::Field(i) => (descend(c, PE::Field(i as nat)), seq![]),
        Proj::Index(x) => {
            let i = as_int(read_loc(fr, local_loc(x as nat)));
            (descend(c, PE::Index(i as nat)), seq![Event::Idx(i)])
        },
        Proj::ConstIndex(k) => (descend(c, PE::Index(k as nat)), seq![]),
        Proj::Downcast(k) => (descend(c, PE::Variant(k as nat)), seq![]),
    }
}

pub open spec fn walk(fr: Frame, ps: Seq<Proj>, k: nat, c: Cur) -> (Cur, Seq<Event>)
    decreases ps.len() - k when k <= ps.len()
{
    if k == ps.len() {
        (c, seq![])
    } else {
        let (c1, e1) = step(fr, c, ps[k as int]);
        let (c2, e2) = walk(fr, ps, k + 1, c1);
        (c2, e1 + e2)
    }
}

pub open spec fn place_walk(fr: Frame, pl: Place) -> (Cur, Seq<Event>) {
    walk(fr, pl.proj@, 0, Cur::L(local_loc(pl.local as nat)))
}

pub open spec fn read_place(fr: Frame, pl: Place) -> (Val, Seq<Event>) {
    let (c, e) = place_walk(fr, pl);
    (match c { Cur::L(l) => read_loc(fr, l), Cur::V(v) => v }, e)
}

/// `None` through a `Shr` snapshot.
pub open spec fn place_loc(fr: Frame, pl: Place) -> Option<(Loc, Seq<Event>)> {
    match place_walk(fr, pl) {
        (Cur::L(l), e) => Some((l, e)),
        _ => None,
    }
}

/// `pl := v`, with the place's events. A write to a `None` place is a no-op (`wf` excludes it).
pub open spec fn assign(fr: Frame, pl: Place, v: Val) -> (Frame, Seq<Event>) {
    match place_loc(fr, pl) {
        Some((l, e)) => (write_loc(fr, l, v), e),
        None => (fr, seq![]),
    }
}

// ------------------------------------------------------------------ operands and rvalues

pub open spec fn const_val(c: ConstVal) -> Val
    decreases c,
{
    match c {
        ConstVal::Int(n) => Val::Int(n),
        ConstVal::Unit => Val::Unit,
        ConstVal::Arr(cs) => Val::Arr(Seq::new(cs@.len(), |i: int| if 0 <= i < cs@.len() { const_val(cs@[i]) } else { Val::Unit })),
        ConstVal::Shr(b) => Val::Shr(Box::new(const_val(*b))),
    }
}

pub open spec fn eval_op(fr: Frame, op: Operand) -> (Val, Seq<Event>) {
    match op {
        Operand::Copy(pl) => read_place(fr, pl),
        Operand::Const(_, n) => (Val::Int(n), seq![]),
        Operand::Lit(c) => (const_val(c), seq![]),
    }
}

pub open spec fn op_vals(fr: Frame, ops: Seq<Operand>) -> Seq<Val> {
    Seq::new(ops.len(), |j: int| eval_op(fr, ops[j]).0)
}

/// The operands' events, left to right.
pub open spec fn ops_ev(fr: Frame, ops: Seq<Operand>) -> Seq<Event>
    decreases ops.len(),
{
    if ops.len() == 0 { seq![] } else { ops_ev(fr, ops.drop_last()) + eval_op(fr, ops.last()).1 }
}

/// The elements of an `Arr`, looking through one `Shr`/`Mut`; empty otherwise.
pub open spec fn elems(fr: Frame, v: Val) -> Seq<Val> {
    let t = match v { Val::Shr(b) => *b, Val::Mut(l) => read_loc(fr, l), _ => v };
    match t { Val::Arr(s) => s, _ => seq![] }
}

pub open spec fn eval_rv(fr: Frame, rv: Rvalue) -> (Val, Seq<Event>) {
    match rv {
        Rvalue::Use(op) => eval_op(fr, op),
        Rvalue::Bin(op, ty, a, b) => {
            let (va, ea) = eval_op(fr, a);
            let (vb, eb) = eval_op(fr, b);
            (Val::Int(binop(op, ty, as_int(va), as_int(vb))), ea + eb + op_ev(op, as_int(va), as_int(vb)))
        },
        Rvalue::Un(op, ty, a) => {
            let (va, ea) = eval_op(fr, a);
            (Val::Int(unop(op, ty, as_int(va))), ea)
        },
        Rvalue::Cast(from, to, a) => {
            let (va, ea) = eval_op(fr, a);
            (Val::Int(cast(from, to, as_int(va))), ea)
        },
        Rvalue::Len(pl) => {
            let (v, e) = read_place(fr, pl);
            (Val::Int(elems(fr, v).len() as u128), e)
        },
        Rvalue::Discr(pl) => {
            let (v, e) = read_place(fr, pl);
            (Val::Int(match v { Val::Adt(k, _) => k as u128, _ => 0 }), e)
        },
        Rvalue::Aggregate(kind, ops) => {
            let vs = op_vals(fr, ops@);
            (match kind {
                AggKind::Tuple => Val::Tup(vs),
                AggKind::Array => Val::Arr(vs),
                AggKind::Adt(k) => Val::Adt(k as nat, vs),
            }, ops_ev(fr, ops@))
        },
        Rvalue::Repeat(op, n) => {
            let (v, e) = eval_op(fr, op);
            (Val::Arr(Seq::new(n as nat, |j: int| v)), e)
        },
        Rvalue::RefShr(pl) => {
            let (v, e) = read_place(fr, pl);
            (Val::Shr(Box::new(v)), e)
        },
        Rvalue::RefMut(pl) => match place_loc(fr, pl) {
            Some((l, e)) => (Val::Mut(l), e),
            None => (Val::Unit, seq![]),
        },
    }
}

// ------------------------------------------------------------------ statements (1 step each)

/// Events: the rvalue's, then the place's; then the value is written.
pub open spec fn exec_stmt(fr: Frame, s: Stmt) -> (Frame, Seq<Event>) {
    match s {
        Stmt::Assign(pl, rv) => {
            let (v, e1) = eval_rv(fr, rv);
            let (f2, e2) = assign(fr, pl, v);
            (f2, e1 + e2)
        },
        Stmt::SetDiscr(pl, k) => match place_loc(fr, pl) {
            Some((l, e)) => (write_loc(fr, l, match read_loc(fr, l) {
                Val::Adt(_, vs) => Val::Adt(k as nat, vs),
                v => v,
            }), e),
            None => (fr, seq![]),
        },
    }
}

pub open spec fn exec_stmts(ss: Seq<Stmt>, k: nat, fr: Frame) -> (Frame, Seq<Event>)
    decreases ss.len() - k when k <= ss.len()
{
    if k == ss.len() {
        (fr, seq![])
    } else {
        let (f1, e1) = exec_stmt(fr, ss[k as int]);
        let (f2, e2) = exec_stmts(ss, k + 1, f1);
        (f2, e1 + e2)
    }
}

// ------------------------------------------------------------------ intrinsics

/// Appends `xs` to the `Arr` that `m` (a `Mut`) targets; `None` past usize::MAX elements.
pub open spec fn grow(fr: Frame, m: Val, xs: Seq<Val>) -> Option<Frame> {
    match m {
        Val::Mut(l) => match read_loc(fr, l) {
            Val::Arr(s) => if s.len() + xs.len() > USIZE_MAX { None } else { Some(write_loc(fr, l, Val::Arr(s + xs))) },
            _ => Some(fr),
        },
        _ => Some(fr),
    }
}

/// The intrinsic's effect on the frame, its result value and its own events.
pub open spec fn intr_eff(k: Intrinsic, fr: Frame, vs: Seq<Val>) -> Option<(Frame, Val, Seq<Event>)> {
    let (a0, a1, a2) = (nth(vs, 0), nth(vs, 1), nth(vs, 2));
    match k {
        Intrinsic::Declassify => Some((fr, a0, seq![Event::Declass(a0)])),
        Intrinsic::GhostUnit => Some((fr, Val::Unit, seq![])),
        Intrinsic::VecNew => Some((fr, Val::Arr(seq![]), seq![])),
        Intrinsic::VecWithCapacity => Some((fr, Val::Arr(seq![]), seq![Event::Alloc(as_int(a0))])),
        Intrinsic::VecPush => match grow(fr, a0, seq![a1]) {
            Some(f) => Some((f, Val::Unit, seq![])),
            None => None,
        },
        Intrinsic::VecExtendFromSlice => match grow(fr, a0, elems(fr, a1)) {
            Some(f) => Some((f, Val::Unit, seq![])),
            None => None,
        },
        Intrinsic::VecAsSlice | Intrinsic::ArrayAsSlice => Some((fr, a0, seq![])),
        Intrinsic::VecLen => Some((fr, Val::Int(elems(fr, a0).len() as u128), seq![])),
        Intrinsic::VecSet => {
            let i = as_int(a1);
            let f = match a0 {
                Val::Mut(l) => write_loc(fr, Loc { root: l.root, path: l.path.push(PE::Index(i as nat)) }, a2),
                _ => fr,
            };
            Some((f, Val::Unit, seq![Event::Idx(i)]))
        },
        Intrinsic::VecIndex => {
            let i = as_int(a1);
            Some((fr, Val::Shr(Box::new(nth(elems(fr, a0), i as nat))), seq![Event::Idx(i)]))
        },
        Intrinsic::SliceSubrange => {
            let s = elems(fr, a0);
            let (lo, hi) = (as_int(a1), as_int(a2));
            let h = if (hi as nat) < s.len() { hi as int } else { s.len() as int };
            let l = if (lo as int) < h { lo as int } else { h };
            Some((fr, Val::Shr(Box::new(Val::Arr(s.subrange(l, h)))), seq![Event::Range(lo, hi)]))
        },
        Intrinsic::SliceToVec => {
            let s = elems(fr, a0);
            if s.len() > USIZE_MAX { None } else { Some((fr, Val::Arr(s), seq![])) }
        },
        Intrinsic::Wrapping(op, ty) => {
            let (a, b) = (as_int(a0), as_int(a1));
            Some((fr, Val::Int(binop(op, ty, a, b)), op_ev(op, a, b)))
        },
    }
}

/// Steps beyond the terminator's 1.
pub open spec fn intr_cost(k: Intrinsic, fr: Frame, args: Seq<Operand>) -> nat {
    let vs = op_vals(fr, args);
    match k {
        Intrinsic::VecExtendFromSlice => elems(fr, nth(vs, 1)).len(),
        Intrinsic::SliceToVec => elems(fr, nth(vs, 0)).len(),
        _ => 0,
    }
}

/// Events: the args', then the intrinsic's, then the dst place's.
pub open spec fn exec_intr(k: Intrinsic, fr: Frame, args: Seq<Operand>, dst: Place) -> Option<(Frame, Seq<Event>, nat)> {
    match intr_eff(k, fr, op_vals(fr, args)) {
        Some((f1, r, ie)) => {
            let (f2, de) = assign(f1, dst, r);
            Some((f2, ops_ev(fr, args) + ie + de, intr_cost(k, fr, args)))
        },
        None => None,
    }
}

// ------------------------------------------------------------------ calls

/// The callee frame (`[Unit] + args + Unit...`, each top-level `Mut(loc)` arg `j` replaced by
/// `Mut(Slot(j), [])` with `slots[j] := read(loc)`), the write-back loc per parameter, and the
/// arg events.
pub open spec fn call_enter(p: Program, g: nat, fr: Frame, args: Seq<Operand>) -> (Frame, Seq<Option<Loc>>, Seq<Event>) {
    let vs = op_vals(fr, args);
    let n = if g < p.fns@.len() { p.fns@[g as int].locals@.len() } else { 0 };
    let locals = Seq::new(n, |i: int|
        if 1 <= i <= vs.len() {
            match vs[i - 1] { Val::Mut(_) => Val::Mut(Loc { root: Root::Slot((i - 1) as nat), path: seq![] }), v => v }
        } else { Val::Unit });
    let slots = Seq::new(vs.len(), |j: int| match vs[j] { Val::Mut(l) => read_loc(fr, l), _ => Val::Unit });
    let wb = Seq::new(vs.len(), |j: int| match vs[j] { Val::Mut(l) => Some(l), _ => None });
    (Frame { locals, slots }, wb, ops_ev(fr, args))
}

/// Writes back slots `0..wb.len()` to their locs, in caller order.
pub open spec fn write_back(fr: Frame, slots: Seq<Val>, wb: Seq<Option<Loc>>) -> Frame
    decreases wb.len(),
{
    if wb.len() == 0 {
        fr
    } else {
        let f1 = write_back(fr, slots, wb.drop_last());
        match wb.last() {
            Some(l) => write_loc(f1, l, nth(slots, (wb.len() - 1) as nat)),
            None => f1,
        }
    }
}

/// Write-back, then `dst := callee.locals[0]`.
pub open spec fn call_leave(fr: Frame, callee: Frame, wb: Seq<Option<Loc>>, dst: Place) -> (Frame, Seq<Event>) {
    assign(write_back(fr, callee.slots, wb), dst, nth(callee.locals, 0))
}

// ------------------------------------------------------------------ runs

/// First target whose value is `v`, else `otherwise`.
pub open spec fn switch_target(ts: Seq<(u128, usize)>, k: nat, v: u128, otherwise: usize) -> usize
    decreases ts.len() - k when k <= ts.len()
{
    if k == ts.len() { otherwise } else if ts[k as int].0 == v { ts[k as int].1 } else { switch_target(ts, k + 1, v, otherwise) }
}

/// Runs block `b` of fn `f`. Each block transition and each call consumes 1 fuel. Steps: one
/// per statement and terminator, plus callee steps and intrinsic costs.
pub open spec fn run_from(p: Program, f: nat, b: nat, fr: Frame, fuel: nat) -> Res
    decreases fuel,
{
    if fuel == 0 || f >= p.fns@.len() || b >= p.fns@[f as int].blocks@.len() {
        None
    } else {
        let blk = p.fns@[f as int].blocks@[b as int];
        let (f1, t1) = exec_stmts(blk.stmts@, 0, fr);
        let n1 = blk.stmts@.len() + 1;
        let fuel1 = (fuel - 1) as nat;
        match blk.term {
            Term::Goto(b2) => match run_from(p, f, b2 as nat, f1, fuel1) {
                Some((f2, t2, n2)) => Some((f2, t1 + t2, n1 + n2)),
                None => None,
            },
            Term::Switch(op, ts, otherwise) => {
                let (v, e) = eval_op(f1, op);
                let pre = t1 + e + seq![Event::Cond(as_int(v))];
                match run_from(p, f, switch_target(ts@, 0, as_int(v), otherwise) as nat, f1, fuel1) {
                    Some((f2, t2, n2)) => Some((f2, pre + t2, n1 + n2)),
                    None => None,
                }
            },
            Term::Assert(op, expected, b2) => {
                let (v, e) = eval_op(f1, op);
                let pre = t1 + e + seq![Event::Cond(as_int(v))];
                if (as_int(v) != 0) == expected {
                    match run_from(p, f, b2 as nat, f1, fuel1) {
                        Some((f2, t2, n2)) => Some((f2, pre + t2, n1 + n2)),
                        None => None,
                    }
                } else {
                    None
                }
            },
            Term::Return => Some((f1, t1, n1)),
            Term::Abort => None,
            Term::Call(Callee::Fn(g), args, dst, next) => {
                let (cf, wb, ae) = call_enter(p, g as nat, f1, args@);
                match run_from(p, g as nat, 0, cf, fuel1) {
                    Some((cf2, ct, cn)) => {
                        let (f2, de) = call_leave(f1, cf2, wb, dst);
                        let pre = t1 + ae + ct + de;
                        match run_from(p, f, next as nat, f2, fuel1) {
                            Some((f3, t3, n3)) => Some((f3, pre + t3, n1 + cn + n3)),
                            None => None,
                        }
                    },
                    None => None,
                }
            },
            Term::Call(Callee::Intr(k), args, dst, next) => match exec_intr(k, f1, args@, dst) {
                Some((f2, e, x)) => {
                    let pre = t1 + e;
                    match run_from(p, f, next as nat, f2, fuel1) {
                        Some((f3, t3, n3)) => Some((f3, pre + t3, n1 + x + n3)),
                        None => None,
                    }
                },
                None => None,
            },
        }
    }
}

pub open spec fn run_fn(p: Program, f: nat, fr: Frame, fuel: nat) -> Res {
    run_from(p, f, 0, fr, fuel)
}

/// The entry frame the theorems quantify over: `Mut(Slot(j), [])` in local `1 + j` for every
/// `Ty::Mut` parameter (ignoring `args[j]`), `args[j]` in the other parameter locals, `Unit`
/// elsewhere, and `slots` as the slots.
pub open spec fn init_entry(p: Program, f: nat, args: Seq<Val>, slots: Seq<Val>) -> Frame {
    let body = p.fns@[f as int];
    if f >= p.fns@.len() { Frame { locals: seq![], slots } } else { Frame {
        locals: Seq::new(body.locals@.len(), |i: int|
            if 1 <= i <= body.nargs {
                if body.locals@[i] is Mut { Val::Mut(Loc { root: Root::Slot((i - 1) as nat), path: seq![] }) }
                else { nth(args, (i - 1) as nat) }
            } else { Val::Unit }),
        slots,
    } }
}

} // verus!
