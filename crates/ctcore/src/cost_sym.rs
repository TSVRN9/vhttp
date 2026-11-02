//! The abstract effect of a block on a frame (Phase 8b): each local's value at the block's end in
//! terms of block-start atoms, the facts each out-edge establishes, and their soundness under
//! `plc`. The verified validator in `cost_check` consumes these.
#[allow(unused_imports)]
use crate::cost::*;
#[allow(unused_imports)]
use crate::cost_sanity::*;
#[allow(unused_imports)]
use crate::ct::*;
#[allow(unused_imports)]
use crate::ct_lemmas::*;
#[allow(unused_imports)]
use crate::sem::*;
#[allow(unused_imports)]
use crate::syntax::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ effects

/// One local's value at the block's end, in terms of block-start atoms.
pub enum Rel { Same, ValEq(Atom, u64), ValLe(Atom), LenEq(Atom), LenLe(Atom), Unknown }

/// The effect the validator builds: one `Rel` per local, and the post-state facts of each edge.
pub struct Eff { pub rel: Vec<Rel>, pub edge: Vec<(usize, Vec<Fact>)> }

/// `Eff` as spec code writes it: spec code cannot build a `Vec`.
pub struct SymEff { pub rel: Seq<Rel>, pub edge: Seq<(usize, Seq<Fact>)> }

pub open spec fn eff_view(e: Eff) -> SymEff {
    SymEff { rel: e.rel@, edge: e.edge@.map_values(|p: (usize, Vec<Fact>)| (p.0, p.1@)) }
}

pub open spec fn writer_place(b: Body, pl: Place) -> bool {
    pl.local < b.locals@.len() && b.locals@[pl.local as int] is Mut && pl.proj@.len() > 0 && pl.proj@[0] is Deref
}

/// `ValEq(Val(y, ty), k)` holds at `ty` only; `ValEq(Const(c), 0)` bounds every width.
pub open spec fn val_eq_sound(a: Atom, k: u64, w: Val, pre: Frame) -> bool {
    match a {
        Atom::Val(_, ty) => val_nat(ty, w) == atom_val(pre, a) + k,
        Atom::Const(c) => if k == 0 {
            forall|ty2: IntTy| #[trigger] val_nat(ty2, w) <= c
        } else {
            forall|ty2: IntTy| #[trigger] val_nat(ty2, w) == atom_val(pre, a) + k
        },
        _ => forall|ty2: IntTy| #[trigger] val_nat(ty2, w) == atom_val(pre, a) + k,
    }
}

pub open spec fn rel_sound(rel: Rel, x: nat, pre: Frame, post: Frame) -> bool {
    let v = nth(pre.locals, x);
    let w = nth(post.locals, x);
    match rel {
        Rel::Same => w == v && len_nat(post, w) == len_nat(pre, v),
        Rel::ValEq(a, k) => val_eq_sound(a, k, w, pre),
        Rel::ValLe(a) => forall|ty2: IntTy| #[trigger] val_nat(ty2, w) <= atom_val(pre, a),
        Rel::LenEq(a) => len_nat(post, w) == atom_val(pre, a),
        Rel::LenLe(a) => len_nat(post, w) <= atom_val(pre, a),
        Rel::Unknown => true,
    }
}

pub open spec fn rels_sound(rels: Seq<Rel>, pre: Frame, post: Frame) -> bool {
    forall|x: int| 0 <= x < rels.len() ==> rel_sound(#[trigger] rels[x], x as nat, pre, post)
}

/// Every `rel` is sound, and the edge facts for `succ` hold at `post`.
pub open spec fn eff_sound(e: SymEff, pre: Frame, post: Frame, succ: nat) -> bool {
    &&& rels_sound(e.rel, pre, post)
    &&& forall|i: int| 0 <= i < e.edge.len() && #[trigger] e.edge[i].0 as nat == succ ==> facts_hold(post, e.edge[i].1)
}

// ------------------------------------------------------------------ per-pattern rules

/// `y`'s rel so far; a rule over a local outside the body gives `Unknown`.
pub open spec fn rel_at(rels: Seq<Rel>, y: usize) -> Rel {
    if (y as nat) < rels.len() { rels[y as int] } else { Rel::Unknown }
}

pub open spec fn op_local(op: Operand) -> Option<usize> {
    match op {
        Operand::Copy(q) => if q.proj@.len() == 0 { Some(q.local) } else { None },
        _ => None,
    }
}

pub open spec fn op_one(op: Operand) -> bool {
    op matches Operand::Const(_, n) && n == 1
}

pub open spec fn arg_local(args: Seq<Operand>, i: int) -> Option<usize> {
    if 0 <= i < args.len() { op_local(args[i]) } else { None }
}

/// `x = Copy(y)`, through `y`'s rel so far.
pub open spec fn rel_copy(rels: Seq<Rel>, y: usize, ty: IntTy) -> Rel {
    match rel_at(rels, y) {
        Rel::Same => Rel::ValEq(Atom::Val(y, ty), 0),
        Rel::ValEq(Atom::Val(z, t), k) => if t == ty { Rel::ValEq(Atom::Val(z, t), k) } else { Rel::Unknown },
        Rel::ValEq(Atom::Const(c), k) => if k == 0 { Rel::ValEq(Atom::Const(c), 0) } else { Rel::Unknown },
        Rel::ValLe(a) => Rel::ValLe(a),
        _ => Rel::Unknown,
    }
}

/// `x = Copy(y)` for two locals of one `IntTy`.
pub open spec fn rel_copy_int(b: Body, rels: Seq<Rel>, x: usize, y: usize) -> Rel {
    if x < b.locals@.len() && y < b.locals@.len() {
        match b.locals@[y as int] {
            Ty::Int(ty) => if b.locals@[x as int] == Ty::Int(ty) { rel_copy(rels, y, ty) } else { Rel::Unknown },
            _ => Rel::Unknown,
        }
    } else {
        Rel::Unknown
    }
}

pub open spec fn rel_const(ty: IntTy, n: u128) -> Rel {
    if n as int == uval(ty, n) && uval(ty, n) <= u64::MAX {
        Rel::ValEq(Atom::Const(uval(ty, n) as u64), 0)
    } else {
        Rel::Unknown
    }
}

pub open spec fn inc_fact(fa: Fact, x: usize, ty: IntTy) -> bool {
    fa matches Fact::Lt(Atom::Val(y, t), a) && y == x && t == ty && inc_bound_ok(a, ty)
}

/// `x = x + 1`: no wrap by a pre-fact `Lt(Val(x, ty), A)`, so `x` must still hold its pre value.
pub open spec fn rel_inc(rels: Seq<Rel>, facts: Seq<Fact>, x: usize, ty: IntTy) -> Rel {
    if !signed(ty) && rel_at(rels, x) is Same && exists|i: int| 0 <= i < facts.len() && inc_fact(#[trigger] facts[i], x, ty) {
        Rel::ValEq(Atom::Val(x, ty), 1)
    } else {
        Rel::Unknown
    }
}

/// The pre atom bounding `len_nat` of `y` so far.
pub open spec fn len_atom(rels: Seq<Rel>, y: usize) -> Option<Atom> {
    match rel_at(rels, y) {
        Rel::Same => Some(Atom::Len(y)),
        Rel::LenEq(a) => Some(a),
        Rel::LenLe(a) => Some(a),
        _ => None,
    }
}

/// `x = Len(y)`, `VecLen(y)`: `eval_rv` reads one layer and the atom reads all.
pub open spec fn rel_len(rels: Seq<Rel>, y: usize) -> Rel {
    match len_atom(rels, y) { Some(a) => Rel::ValLe(a), None => Rel::Unknown }
}

/// `x = copy (*y)`, `SliceSubrange(y, ..)`, `SliceToVec(y)`.
pub open spec fn rel_le(rels: Seq<Rel>, y: usize) -> Rel {
    match len_atom(rels, y) { Some(a) => Rel::LenLe(a), None => Rel::Unknown }
}

/// `x = RefShr(y)`, `VecAsSlice(y)`.
pub open spec fn rel_shr(rels: Seq<Rel>, y: usize) -> Rel {
    match rel_at(rels, y) {
        Rel::Same => Rel::LenEq(Atom::Len(y)),
        Rel::LenEq(a) => Rel::LenEq(a),
        Rel::LenLe(a) => Rel::LenLe(a),
        _ => Rel::Unknown,
    }
}

pub open spec fn rule_stmt(b: Body, rels: Seq<Rel>, facts: Seq<Fact>, x: usize, rv: Rvalue) -> Rel {
    match rv {
        Rvalue::Use(Operand::Copy(q)) =>
            if q.proj@.len() == 0 {
                rel_copy_int(b, rels, x, q.local)
            } else if q.proj@.len() == 1 && q.proj@[0] is Deref {
                rel_le(rels, q.local)
            } else {
                Rel::Unknown
            },
        Rvalue::Use(Operand::Const(ty, n)) => rel_const(ty, n),
        Rvalue::Bin(op, ty, a, c) =>
            if op is Add && op_local(a) == Some(x) && op_one(c) { rel_inc(rels, facts, x, ty) } else { Rel::Unknown },
        Rvalue::Len(q) => if q.proj@.len() == 0 { rel_len(rels, q.local) } else { Rel::Unknown },
        Rvalue::RefShr(q) => if q.proj@.len() == 0 { rel_shr(rels, q.local) } else { Rel::Unknown },
        _ => Rel::Unknown,
    }
}

pub open spec fn rule_intr(rels: Seq<Rel>, facts: Seq<Fact>, x: usize, k: Intrinsic, args: Seq<Operand>) -> Rel {
    match (k, arg_local(args, 0)) {
        (Intrinsic::VecLen, Some(y)) => rel_len(rels, y),
        (Intrinsic::VecAsSlice, Some(y)) => rel_shr(rels, y),
        (Intrinsic::SliceSubrange, Some(y)) => rel_le(rels, y),
        (Intrinsic::SliceToVec, Some(y)) => rel_le(rels, y),
        (Intrinsic::Wrapping(BinOp::Add, ty), Some(y)) =>
            if y == x && args.len() > 1 && op_one(args[1]) { rel_inc(rels, facts, x, ty) } else { Rel::Unknown },
        _ => Rel::Unknown,
    }
}

// ------------------------------------------------------------------ writes

pub open spec fn mut_local(b: Body, x: int) -> bool {
    0 <= x < b.locals@.len() && b.locals@[x] is Mut
}

// ponytail: a writer loses every local, counters across any `&mut` call included; a frame invariant limiting targets to `RefMut` roots is the upgrade.
pub open spec fn all_unknown(n: nat) -> Seq<Rel> {
    Seq::new(n, |i: int| Rel::Unknown)
}

/// A non-writer write rooted at `r`: `r` gets `rnew`, and a `Mut`-typed local may target a
/// non-`Mut`-typed `r`, so it gets `Unknown`.
pub open spec fn write_root(b: Body, rels: Seq<Rel>, r: usize, rnew: Rel) -> Seq<Rel> {
    Seq::new(rels.len(), |i: int|
        if i == r as int { rnew } else if !mut_local(b, r as int) && mut_local(b, i) { Rel::Unknown } else { rels[i] })
}

// ------------------------------------------------------------------ the fold over statements

/// `c` holds `op` of `a` and `b`, atoms over the frame at hand.
pub struct Cmp { pub c: usize, pub op: BinOp, pub a: Atom, pub b: Atom }

// ponytail: remembers the last comparison only, enough for MIR's compare-then-switch; a per-local record is the upgrade.
pub struct SymSt { pub rels: Seq<Rel>, pub cmp: Option<Cmp> }

pub open spec fn is_cmp(op: BinOp) -> bool { op is Lt || op is Le || op is Gt || op is Ge }

pub open spec fn cmp_pred(op: BinOp, x: nat, y: nat) -> bool {
    match op {
        BinOp::Lt => x < y,
        BinOp::Le => x <= y,
        BinOp::Gt => x > y,
        _ => x >= y,
    }
}

/// The fact a comparison's outcome gives.
pub open spec fn cmp_fact(m: Cmp, outcome: bool) -> Fact {
    match m.op {
        BinOp::Lt => if outcome { Fact::Lt(m.a, m.b) } else { Fact::Le(m.b, m.a) },
        BinOp::Le => if outcome { Fact::Le(m.a, m.b) } else { Fact::Lt(m.b, m.a) },
        BinOp::Gt => if outcome { Fact::Lt(m.b, m.a) } else { Fact::Le(m.a, m.b) },
        _ => if outcome { Fact::Le(m.b, m.a) } else { Fact::Lt(m.a, m.b) },
    }
}

/// The operand's value at `ty`, as an atom over the frame at hand: through a copy, so
/// `_15 = copy _13; Lt(_15, _8)` compares `Val(13)`.
pub open spec fn cmp_atom(rels: Seq<Rel>, op: Operand, ty: IntTy) -> Option<Atom> {
    match op {
        Operand::Copy(q) => if q.proj@.len() == 0 {
            match rel_at(rels, q.local) {
                Rel::ValEq(Atom::Val(y, t), k) =>
                    if t == ty && k == 0 && rel_at(rels, y) is Same { Some(Atom::Val(y, ty)) } else { Some(Atom::Val(q.local, ty)) },
                _ => Some(Atom::Val(q.local, ty)),
            }
        } else {
            None
        },
        Operand::Const(_, n) => if uval(ty, n) <= u64::MAX { Some(Atom::Const(uval(ty, n) as u64)) } else { None },
        _ => None,
    }
}

pub open spec fn atom_reads(a: Atom, r: usize) -> bool {
    match a { Atom::Const(_) => false, Atom::Val(y, _) => y == r, _ => true }
}

pub open spec fn cmp_keeps(m: Cmp, r: usize) -> bool {
    m.c != r && !atom_reads(m.a, r) && !atom_reads(m.b, r)
}

/// `x = op(a, c)` at unsigned `ty`, when both operands have atoms that survive the write to `x`.
pub open spec fn new_cmp(rels: Seq<Rel>, x: usize, rv: Rvalue) -> Option<Cmp> {
    match rv {
        Rvalue::Bin(op, ty, a, c) => if is_cmp(op) && !signed(ty) {
            match (cmp_atom(rels, a, ty), cmp_atom(rels, c, ty)) {
                (Some(aa), Some(cc)) =>
                    if !atom_reads(aa, x) && !atom_reads(cc, x) { Some(Cmp { c: x, op, a: aa, b: cc }) } else { None },
                _ => None,
            }
        } else {
            None
        },
        _ => None,
    }
}

/// A write through `pl`, with `rnew` the rule's rel for an empty-projection `pl`.
pub open spec fn st_write(b: Body, st: SymSt, pl: Place, rnew: Rel) -> SymSt {
    if writer_place(b, pl) {
        SymSt { rels: all_unknown(st.rels.len()), cmp: None }
    } else {
        SymSt {
            rels: write_root(b, st.rels, pl.local, if pl.proj@.len() == 0 { rnew } else { Rel::Unknown }),
            cmp: match st.cmp {
                Some(m) => if cmp_keeps(m, pl.local) { Some(m) } else { None },
                None => None,
            },
        }
    }
}

pub open spec fn sym_stmt(b: Body, st: SymSt, s: Stmt, facts: Seq<Fact>) -> SymSt {
    match s {
        Stmt::Assign(pl, rv) => {
            let st1 = st_write(b, st, pl, rule_stmt(b, st.rels, facts, pl.local, rv));
            if pl.proj@.len() == 0 && new_cmp(st.rels, pl.local, rv) is Some {
                SymSt { rels: st1.rels, cmp: new_cmp(st.rels, pl.local, rv) }
            } else {
                st1
            }
        },
        Stmt::SetDiscr(pl, _) => st_write(b, st, pl, Rel::Unknown),
    }
}

pub open spec fn sym_from(b: Body, ss: Seq<Stmt>, k: nat, st: SymSt, facts: Seq<Fact>) -> SymSt
    decreases ss.len() - k when k <= ss.len()
{
    if k == ss.len() { st } else { sym_from(b, ss, k + 1, sym_stmt(b, st, ss[k as int], facts), facts) }
}

pub open spec fn sym_state(b: Body, ss: Seq<Stmt>, facts: Seq<Fact>) -> SymSt {
    sym_from(b, ss, 0, SymSt { rels: Seq::new(b.locals@.len(), |i: int| Rel::Same), cmp: None }, facts)
}

/// The rels from the block's start to `exec_stmts(..).0`.
pub open spec fn sym_stmts(b: Body, stmts: Seq<Stmt>, facts: Seq<Fact>) -> SymEff {
    SymEff { rel: sym_state(b, stmts, facts).rels, edge: seq![] }
}

// ------------------------------------------------------------------ the terminator

pub open spec fn intr_writer(b: Body, k: Intrinsic, args: Seq<Operand>) -> bool {
    (k is VecPush || k is VecSet || k is VecExtendFromSlice) && args.len() > 0 && mut_op(b, args[0])
}

pub open spec fn call_writer(b: Body, args: Seq<Operand>) -> bool {
    exists|i: int| 0 <= i < args.len() && mut_op(b, #[trigger] args[i])
}

pub open spec fn term_rels(b: Body, rels: Seq<Rel>, t: Term, facts: Seq<Fact>) -> Seq<Rel> {
    match t {
        Term::Call(Callee::Intr(k), args, dst, _) =>
            if intr_writer(b, k, args@) || writer_place(b, dst) {
                all_unknown(rels.len())
            } else {
                write_root(b, rels, dst.local, if dst.proj@.len() == 0 { rule_intr(rels, facts, dst.local, k, args@) } else { Rel::Unknown })
            },
        Term::Call(Callee::Fn(_), args, dst, _) =>
            if call_writer(b, args@) || writer_place(b, dst) {
                all_unknown(rels.len())
            } else {
                write_root(b, rels, dst.local, Rel::Unknown)
            },
        _ => rels,
    }
}

pub open spec fn atom_same(rels: Seq<Rel>, a: Atom) -> bool
    decreases a,
{
    match a {
        Atom::Const(_) => true,
        Atom::Val(x, _) => rel_at(rels, x) is Same,
        Atom::Len(x) => rel_at(rels, x) is Same,
        Atom::Gap(x, y) => atom_same(rels, *x) && atom_same(rels, *y),
    }
}

pub open spec fn fact_same(rels: Seq<Rel>, fa: Fact) -> bool {
    match fa {
        Fact::Le(x, y) => atom_same(rels, x) && atom_same(rels, y),
        Fact::Lt(x, y) => atom_same(rels, x) && atom_same(rels, y),
    }
}

/// `acc`, then the facts from `k` on whose atoms read only `Same` locals.
pub open spec fn carry_from(rels: Seq<Rel>, facts: Seq<Fact>, k: nat, acc: Seq<Fact>) -> Seq<Fact>
    decreases facts.len() - k when k <= facts.len()
{
    if k == facts.len() {
        acc
    } else {
        carry_from(rels, facts, k + 1, if fact_same(rels, facts[k as int]) { acc.push(facts[k as int]) } else { acc })
    }
}

pub open spec fn carry(rels: Seq<Rel>, facts: Seq<Fact>) -> Seq<Fact> {
    carry_from(rels, facts, 0, seq![])
}

/// The comparison a `Switch` or `Assert` tests.
pub open spec fn tested(st: SymSt, op: Operand) -> Option<Cmp> {
    match st.cmp {
        Some(m) => if op_local(op) == Some(m.c) { Some(m) } else { None },
        None => None,
    }
}

/// `Lt`/`Le` on target `t` of a `Switch` on a comparison, whose outcomes go to different blocks.
pub open spec fn switch_extra(st: SymSt, op: Operand, ts: Seq<(u128, usize)>, o: usize, t: usize) -> Seq<Fact> {
    let (z, n) = (switch_target(ts, 0, 0, o), switch_target(ts, 0, 1, o));
    match tested(st, op) {
        Some(m) =>
            if z == n { seq![] } else if t == z { seq![cmp_fact(m, false)] } else if t == n { seq![cmp_fact(m, true)] } else { seq![] },
        None => seq![],
    }
}

pub open spec fn switch_edges(st: SymSt, op: Operand, ts: Seq<(u128, usize)>, o: usize, cy: Seq<Fact>) -> Seq<(usize, Seq<Fact>)> {
    Seq::new((ts.len() + 1) as nat, |i: int| {
        let t = if i < ts.len() { ts[i].1 } else { o };
        (t, cy + switch_extra(st, op, ts, o, t))
    })
}

pub open spec fn term_edges(st: SymSt, rels: Seq<Rel>, t: Term, facts: Seq<Fact>) -> Seq<(usize, Seq<Fact>)> {
    let cy = carry(rels, facts);
    match t {
        Term::Goto(b2) => seq![(b2, cy)],
        Term::Switch(op, ts, o) => switch_edges(st, op, ts@, o, cy),
        Term::Assert(op, expected, b2) => seq![(b2, match tested(st, op) {
            Some(m) => if expected { cy + seq![cmp_fact(m, true)] } else { cy },
            None => cy,
        })],
        Term::Call(_, _, _, next) => seq![(next, cy)],
        _ => seq![],
    }
}

pub open spec fn sym_block(b: Body, blk: Block, facts: Seq<Fact>) -> SymEff {
    let st = sym_state(b, blk.stmts@, facts);
    let rels = term_rels(b, st.rels, blk.term, facts);
    SymEff { rel: rels, edge: term_edges(st, rels, blk.term, facts) }
}

/// `sym_block` is sound for the successor the terminator actually takes, at the successor frame.
pub open spec fn sym_block_sound(p: Program, blk: Block, facts: Seq<Fact>, fr: Frame, e: SymEff) -> bool {
    let fr1 = exec_stmts(blk.stmts@, 0, fr).0;
    match blk.term {
        Term::Goto(b2) => eff_sound(e, fr, fr1, b2 as nat),
        Term::Switch(op, ts, o) => eff_sound(e, fr, fr1, switch_target(ts@, 0, as_int(eval_op(fr1, op).0), o) as nat),
        Term::Assert(op, expected, b2) => (as_int(eval_op(fr1, op).0) != 0) == expected ==> eff_sound(e, fr, fr1, b2 as nat),
        Term::Call(Callee::Intr(k), args, dst, next) => exec_intr(k, fr1, args@, dst) matches Some((fr2, _, _)) ==> eff_sound(e, fr, fr2, next as nat),
        Term::Call(Callee::Fn(g), args, dst, next) => forall|out: Frame| frame_len_ok(out) ==>
            #[trigger] eff_sound(e, fr, call_leave(fr1, out, call_enter(p, g as nat, fr1, args@).1, dst).0, next as nat),
        _ => true,
    }
}

/// `c` is a value of unsigned `ty`.
pub open spec fn fits_ty(c: u64, ty: IntTy) -> bool {
    match ty {
        IntTy::U8 => c <= 0xff,
        IntTy::U16 => c <= 0xffff,
        IntTy::U32 => c <= 0xffff_ffff,
        IntTy::Bool => c <= 1,
        _ => true,
    }
}

/// What may bound a counter of type `ty` under `Lt`: at most `ty`'s maximum.
pub open spec fn inc_bound_ok(a: Atom, ty: IntTy) -> bool {
    match a {
        Atom::Const(c) => fits_ty(c, ty),
        Atom::Val(_, t) => t == ty,
        Atom::Len(_) => ty is Usize,
        Atom::Gap(_, _) => false,
    }
}

// ------------------------------------------------------------------ arithmetic

proof fn lemma_uval_bounds(ty: IntTy, a: u128)
    ensures 0 <= uval(ty, a) <= a, uval(ty, a) < pow2(bits(ty)), pow2(bits(ty)) > 0,
{
    lemma_pow2_pos(bits(ty));
    lemma_mod_pos_bound(a as int, pow2(bits(ty)) as int);
    lemma_mod_decreases(a as nat, pow2(bits(ty)));
}

/// The widths of the unsigned types.
proof fn lemma_unsigned_width(ty: IntTy)
    requires !signed(ty),
    ensures
        pow2(bits(ty)) >= 2,
        bits(ty) >= 64 ==> pow2(bits(ty)) >= 0x1_0000_0000_0000_0000,
        ty is Usize ==> pow2(bits(ty)) == 0x1_0000_0000_0000_0000,
        ty is U8 ==> pow2(bits(ty)) == 0x100,
        ty is U16 ==> pow2(bits(ty)) == 0x1_0000,
        ty is U32 ==> pow2(bits(ty)) == 0x1_0000_0000,
        ty is Bool ==> pow2(bits(ty)) == 2,
{
    lemma2_to64();
    if ty is U128 { lemma_pow2_strictly_increases(64, 128); }
}

/// `x + 1` at unsigned `ty`, no wrap.
proof fn lemma_binop_inc(ty: IntTy, a: u128)
    requires !signed(ty), uval(ty, a) + 1 < pow2(bits(ty)), uval(ty, a) + 1 <= u128::MAX,
    ensures binop(BinOp::Add, ty, a, 1) == (uval(ty, a) + 1) as u128,
{
    reveal(binop);
    let u = uval(ty, a);
    lemma_uval_bounds(ty, a);
    lemma_unsigned_width(ty);
    lemma_small_mod(1, pow2(bits(ty)));
    lemma_small_mod((u + 1) as nat, pow2(bits(ty)));
}

/// A bound `inc_bound_ok` admits is a value of `ty`.
proof fn lemma_inc_bound(fr: Frame, a: Atom, ty: IntTy)
    requires !signed(ty), inc_bound_ok(a, ty), frame_len_ok(fr),
    ensures atom_val(fr, a) < pow2(bits(ty)), atom_val(fr, a) <= u128::MAX,
{
    lemma_unsigned_width(ty);
    match a {
        Atom::Val(x, t) => if let Val::Int(n) = nth(fr.locals, x as nat) { lemma_uval_bounds(ty, n); },
        Atom::Len(x) => {
            let v = nth(fr.locals, x as nat);
            if (x as nat) < fr.locals.len() { assert(len_ok(fr.locals[x as int])); }
            if let Val::Mut(l) = v {
                lemma_read_loc_len_ok(fr, l);
                lemma_shr_len_ok(read_loc(fr, l));
            } else {
                lemma_shr_len_ok(v);
            }
        },
        _ => {},
    }
}

/// The no-wrap argument: under `x < a`, with `a` within `ty`'s width, `x + 1` does not wrap, and
/// the gap to `a` falls by one.
pub proof fn lemma_rel_inc(fr: Frame, old: Val, ty: IntTy, a: Atom)
    requires !signed(ty), inc_bound_ok(a, ty), frame_len_ok(fr), val_nat(ty, old) < atom_val(fr, a),
    ensures
        val_nat(ty, Val::Int(binop(BinOp::Add, ty, as_int(old), 1))) == val_nat(ty, old) + 1,
        gap(atom_val(fr, a), val_nat(ty, old)) == gap(atom_val(fr, a), val_nat(ty, old) + 1) + 1,
{
    let u = as_int(old);
    lemma_uval_bounds(ty, u);
    lemma_uval_bounds(ty, 0);
    lemma_small_mod(0, pow2(bits(ty)));
    assert(val_nat(ty, old) == uval(ty, u));
    lemma_inc_bound(fr, a, ty);
    lemma_binop_inc(ty, u);
    let w = (uval(ty, u) + 1) as u128;
    lemma_small_mod(w as nat, pow2(bits(ty)));
    assert(uval(ty, w) == w as int);
    lemma_gap_dec(atom_val(fr, a), val_nat(ty, old));
}


/// `val_nat` is the instruction's reading of a value.
proof fn lemma_val_as(ty: IntTy, v: Val)
    ensures val_nat(ty, v) == uval(ty, as_int(v)),
{
    lemma_uval_bounds(ty, as_int(v));
}

proof fn lemma_binop_cmp(op: BinOp, ty: IntTy, x: u128, y: u128)
    requires is_cmp(op), !signed(ty),
    ensures binop(op, ty, x, y) == b2i(cmp_pred(op, uval(ty, x) as nat, uval(ty, y) as nat)),
{
    reveal(binop);
    lemma_uval_bounds(ty, x);
    lemma_uval_bounds(ty, y);
}

// ------------------------------------------------------------------ places and frames

/// A cursor at a location that reads no `Mut` stays at its root.
proof fn lemma_step_root(p: Program, ls: Seq<FnLab>, f: nat, fr: Frame, c: Cur, pr: Proj, r: nat)
    requires plc(p, ls, f, fr), wr_inv(p.fns@[f as int], fr, c), c matches Cur::L(a) ==> a.root == Root::Local(r),
    ensures step(fr, c, pr).0 matches Cur::L(a) ==> a.root == Root::Local(r),
{
    lemma_wr_read(p, ls, f, fr, c);
}

proof fn lemma_walk_root(p: Program, ls: Seq<FnLab>, f: nat, fr: Frame, ps: Seq<Proj>, k: nat, c: Cur, r: nat)
    requires plc(p, ls, f, fr), k <= ps.len(), wr_inv(p.fns@[f as int], fr, c), c matches Cur::L(a) ==> a.root == Root::Local(r),
    ensures walk(fr, ps, k, c).0 matches Cur::L(a) ==> a.root == Root::Local(r),
    decreases ps.len() - k,
{
    if k < ps.len() {
        lemma_step_root(p, ls, f, fr, c, ps[k as int], r);
        lemma_step_plc(p, ls, f, fr, c, ps[k as int]);
        lemma_walk_root(p, ls, f, fr, ps, k + 1, step(fr, c, ps[k as int]).0, r);
    }
}

/// A non-writer place's location, if any, is rooted at its local.
pub proof fn lemma_nonwriter_root(p: Program, ls: Seq<FnLab>, f: nat, fr: Frame, pl: Place)
    requires plc(p, ls, f, fr), ok_place(p.fns@[f as int], ls[f as int], pl), !writer_place(p.fns@[f as int], pl),
    ensures place_loc(fr, pl) matches Some((l, _)) ==> l.root == Root::Local(pl.local as nat),
{
    let (b, ps, r) = (p.fns@[f as int], pl.proj@, pl.local as nat);
    let c0 = Cur::L(local_loc(r));
    if !(b.locals@[r as int] is Mut) {
        lemma_walk_root(p, ls, f, fr, ps, 0, c0, r);
    } else if ps.len() > 0 {
        let c1 = step(fr, c0, ps[0]).0;
        assert(walk(fr, ps, 0, c0).0 == walk(fr, ps, 1, c1).0);
        lemma_walk_root(p, ls, f, fr, ps, 1, c1, r);
    }
}

/// Only local `r` changes.
pub open spec fn only_root(cur: Frame, post: Frame, r: nat) -> bool {
    &&& post.slots == cur.slots
    &&& post.locals.len() == cur.locals.len()
    &&& forall|x: int| 0 <= x < cur.locals.len() && x != r ==> #[trigger] post.locals[x] == cur.locals[x]
}

proof fn lemma_assign_only_root(p: Program, ls: Seq<FnLab>, f: nat, fr: Frame, pl: Place, v: Val)
    requires plc(p, ls, f, fr), ok_place(p.fns@[f as int], ls[f as int], pl), !writer_place(p.fns@[f as int], pl),
    ensures only_root(fr, assign(fr, pl, v).0, pl.local as nat),
{
    lemma_nonwriter_root(p, ls, f, fr, pl);
}

proof fn lemma_setdiscr_only_root(p: Program, ls: Seq<FnLab>, f: nat, fr: Frame, pl: Place, k: usize)
    requires plc(p, ls, f, fr), ok_place(p.fns@[f as int], ls[f as int], pl), !writer_place(p.fns@[f as int], pl),
    ensures only_root(fr, exec_stmt(fr, Stmt::SetDiscr(pl, k)).0, pl.local as nat),
{
    lemma_nonwriter_root(p, ls, f, fr, pl);
}

/// A write rooted at `r` leaves `len_nat` of another local unless it may target `r`.
proof fn lemma_keep_len(p: Program, ls: Seq<FnLab>, f: nat, cur: Frame, post: Frame, r: nat, y: int)
    requires
        plc(p, ls, f, cur), only_root(cur, post, r), 0 <= y < cur.locals.len(), y != r,
        mut_local(p.fns@[f as int], r as int) || !mut_local(p.fns@[f as int], y),
    ensures len_nat(post, cur.locals[y]) == len_nat(cur, cur.locals[y]),
{
    let (b, l) = (p.fns@[f as int], ls[f as int]);
    if let Val::Mut(m) = cur.locals[y] {
        assert(b.locals@[y] is Mut && tgt_ok(b, l, cur, m, lab(l, y as nat)));
        match m.root {
            Root::Local(z) => {
                assert(post.locals[z as int] == cur.locals[z as int]);
                assert(nth(post.locals, z) == nth(cur.locals, z));
            },
            Root::Slot(_) => {},
        }
    }
}

proof fn lemma_rel_keep(rel: Rel, x: nat, pre: Frame, cur: Frame, post: Frame)
    requires
        rel_sound(rel, x, pre, cur), nth(post.locals, x) == nth(cur.locals, x),
        len_nat(post, nth(cur.locals, x)) == len_nat(cur, nth(cur.locals, x)),
    ensures rel_sound(rel, x, pre, post),
{
}

proof fn lemma_write_root_sound(p: Program, ls: Seq<FnLab>, f: nat, rels: Seq<Rel>, pre: Frame, cur: Frame, post: Frame, r: usize, rnew: Rel)
    requires
        plc(p, ls, f, cur), rels.len() == cur.locals.len(), rels_sound(rels, pre, cur),
        only_root(cur, post, r as nat), rel_sound(rnew, r as nat, pre, post),
    ensures rels_sound(write_root(p.fns@[f as int], rels, r, rnew), pre, post),
{
    let b = p.fns@[f as int];
    let w = write_root(b, rels, r, rnew);
    assert forall|x: int| 0 <= x < w.len() implies rel_sound(#[trigger] w[x], x as nat, pre, post) by {
        if x != r as int && !(!mut_local(b, r as int) && mut_local(b, x)) {
            assert(rel_sound(rels[x], x as nat, pre, cur));
            lemma_keep_len(p, ls, f, cur, post, r as nat, x);
            assert(post.locals[x] == cur.locals[x]);
            lemma_rel_keep(rels[x], x as nat, pre, cur, post);
        }
    }
}

// ------------------------------------------------------------------ per-pattern soundness

proof fn lemma_rel_at(rels: Seq<Rel>, y: usize, pre: Frame, cur: Frame)
    requires rels_sound(rels, pre, cur),
    ensures rel_sound(rel_at(rels, y), y as nat, pre, cur),
{
    if (y as nat) < rels.len() { assert(rel_sound(rels[y as int], (y as int) as nat, pre, cur)); }
}

pub proof fn lemma_rel_copy(rels: Seq<Rel>, y: usize, ty: IntTy, x: nat, pre: Frame, cur: Frame, post: Frame)
    requires rels_sound(rels, pre, cur), nth(post.locals, x) == nth(cur.locals, y as nat),
    ensures rel_sound(rel_copy(rels, y, ty), x, pre, post),
{
    lemma_rel_at(rels, y, pre, cur);
}

pub proof fn lemma_rel_const(ty: IntTy, n: u128, x: nat, pre: Frame, post: Frame)
    requires nth(post.locals, x) == Val::Int(n),
    ensures rel_sound(rel_const(ty, n), x, pre, post),
{
    assert forall|ty2: IntTy| n as int == uval(ty, n) && uval(ty, n) <= u64::MAX implies
        #[trigger] val_nat(ty2, Val::Int(n)) <= uval(ty, n) as u64 by {
        lemma_uval_bounds(ty2, n);
    }
}

/// `x = x + 1` under its `Lt` pre-fact.
proof fn lemma_rel_inc_at(rels: Seq<Rel>, facts: Seq<Fact>, x: usize, ty: IntTy, pre: Frame, cur: Frame, post: Frame)
    requires
        rels_sound(rels, pre, cur), facts_hold(pre, facts), frame_len_ok(pre),
        nth(post.locals, x as nat) == Val::Int(binop(BinOp::Add, ty, as_int(nth(cur.locals, x as nat)), 1)),
    ensures rel_sound(rel_inc(rels, facts, x, ty), x as nat, pre, post),
{
    if rel_inc(rels, facts, x, ty) is ValEq {
        lemma_rel_at(rels, x, pre, cur);
        let i = choose|i: int| 0 <= i < facts.len() && inc_fact(#[trigger] facts[i], x, ty);
        if let Fact::Lt(lhs, a) = facts[i] {
            assert(fact_holds(pre, facts[i]));
            lemma_rel_inc(pre, nth(pre.locals, x as nat), ty, a);
        }
    }
}

proof fn lemma_len_atom(rels: Seq<Rel>, y: usize, pre: Frame, cur: Frame)
    requires rels_sound(rels, pre, cur),
    ensures len_atom(rels, y) matches Some(a) ==> len_nat(cur, nth(cur.locals, y as nat)) <= atom_val(pre, a),
{
    lemma_rel_at(rels, y, pre, cur);
}

/// `n`, the length one layer down, is at most the atom that reads all layers.
pub proof fn lemma_rel_len(rels: Seq<Rel>, y: usize, x: nat, n: nat, pre: Frame, cur: Frame, post: Frame)
    requires
        rels_sound(rels, pre, cur), n <= USIZE_MAX, n <= len_nat(cur, nth(cur.locals, y as nat)),
        nth(post.locals, x) == Val::Int(n as u128),
    ensures rel_sound(rel_len(rels, y), x, pre, post),
{
    lemma_len_atom(rels, y, pre, cur);
    assert forall|ty2: IntTy| #[trigger] val_nat(ty2, Val::Int(n as u128)) <= n by {
        lemma_uval_bounds(ty2, n as u128);
    }
}

proof fn lemma_rel_le(rels: Seq<Rel>, y: usize, x: nat, pre: Frame, cur: Frame, post: Frame)
    requires
        rels_sound(rels, pre, cur), !(nth(post.locals, x) is Mut),
        shr_len(nth(post.locals, x)) <= len_nat(cur, nth(cur.locals, y as nat)),
    ensures rel_sound(rel_le(rels, y), x, pre, post),
{
    lemma_len_atom(rels, y, pre, cur);
}

pub proof fn lemma_rel_shr(rels: Seq<Rel>, y: usize, x: nat, pre: Frame, cur: Frame, post: Frame)
    requires
        rels_sound(rels, pre, cur), !(nth(cur.locals, y as nat) is Mut), !(nth(post.locals, x) is Mut),
        shr_len(nth(post.locals, x)) == shr_len(nth(cur.locals, y as nat)),
    ensures rel_sound(rel_shr(rels, y), x, pre, post),
{
    lemma_rel_at(rels, y, pre, cur);
}

/// `copy (*y)` reads no `Mut`, and at most `len_nat` of `y`.
proof fn lemma_deref_read(p: Program, ls: Seq<FnLab>, f: nat, fr: Frame, q: Place)
    requires
        plc(p, ls, f, fr), ok_place(p.fns@[f as int], ls[f as int], q), q.proj@.len() == 1, q.proj@[0] is Deref,
    ensures
        !(read_place(fr, q).0 is Mut),
        shr_len(read_place(fr, q).0) <= len_nat(fr, fr.locals[q.local as int]),
{
    lemma_place_plc(p, ls, f, fr, q);
    assert(read_loc(fr, local_loc(q.local as nat)) == fr.locals[q.local as int]) by {
        assert(nth(fr.locals, q.local as nat) == fr.locals[q.local as int]);
    }
    reveal_with_fuel(walk, 2);
}

pub proof fn lemma_rel_deref(p: Program, ls: Seq<FnLab>, f: nat, rels: Seq<Rel>, q: Place, x: nat, pre: Frame, cur: Frame, post: Frame)
    requires
        plc(p, ls, f, cur), ok_place(p.fns@[f as int], ls[f as int], q), q.proj@.len() == 1, q.proj@[0] is Deref,
        rels_sound(rels, pre, cur), nth(post.locals, x) == read_place(cur, q).0,
    ensures rel_sound(rel_le(rels, q.local), x, pre, post),
{
    lemma_deref_read(p, ls, f, cur, q);
    assert(nth(cur.locals, q.local as nat) == cur.locals[q.local as int]);
    lemma_rel_le(rels, q.local, x, pre, cur, post);
}

/// `SliceSubrange` shortens: `LenLe`, not `LenEq`.
pub proof fn lemma_rel_subrange(rels: Seq<Rel>, y: usize, x: nat, s: Seq<Val>, l: int, h: int, pre: Frame, cur: Frame, post: Frame)
    requires
        rels_sound(rels, pre, cur), 0 <= l <= h <= s.len(), s == elems(cur, nth(cur.locals, y as nat)),
        nth(post.locals, x) == Val::Shr(Box::new(Val::Arr(s.subrange(l, h)))),
    ensures rel_sound(rel_le(rels, y), x, pre, post),
{
    lemma_elems_le_len_nat(cur, nth(cur.locals, y as nat));
    let a = Val::Arr(s.subrange(l, h));
    assert(shr_len(Val::Shr(Box::new(a))) == shr_len(a));
    lemma_rel_le(rels, y, x, pre, cur, post);
}

proof fn lemma_rel_to_vec(rels: Seq<Rel>, y: usize, x: nat, pre: Frame, cur: Frame, post: Frame)
    requires rels_sound(rels, pre, cur), nth(post.locals, x) == Val::Arr(elems(cur, nth(cur.locals, y as nat))),
    ensures rel_sound(rel_le(rels, y), x, pre, post),
{
    lemma_elems_le_len_nat(cur, nth(cur.locals, y as nat));
    lemma_rel_le(rels, y, x, pre, cur, post);
}

// ------------------------------------------------------------------ comparisons

pub open spec fn cmp_holds(cur: Frame, m: Cmp) -> bool {
    &&& is_cmp(m.op)
    &&& (m.c as nat) < cur.locals.len()
    &&& cur.locals[m.c as int] == Val::Int(b2i(cmp_pred(m.op, atom_val(cur, m.a), atom_val(cur, m.b))))
}

/// The outcome of a comparison gives its fact.
pub proof fn lemma_edge_lt(cur: Frame, m: Cmp, outcome: bool)
    requires is_cmp(m.op), cmp_pred(m.op, atom_val(cur, m.a), atom_val(cur, m.b)) == outcome,
    ensures fact_holds(cur, cmp_fact(m, outcome)),
{
}

proof fn lemma_cmp_atom(rels: Seq<Rel>, op: Operand, ty: IntTy, pre: Frame, cur: Frame, a: Atom)
    requires
        rels_sound(rels, pre, cur), cmp_atom(rels, op, ty) == Some(a),
        op matches Operand::Copy(q) ==> (q.local as nat) < cur.locals.len(),
    ensures atom_val(cur, a) == uval(ty, as_int(eval_op(cur, op).0)),
{
    match op {
        Operand::Copy(q) => {
            lemma_read_local(cur, q, q.local);
            lemma_val_as(ty, cur.locals[q.local as int]);
            assert(nth(cur.locals, q.local as nat) == cur.locals[q.local as int]);
            lemma_rel_at(rels, q.local, pre, cur);
            if let Rel::ValEq(Atom::Val(y, t), k) = rel_at(rels, q.local) {
                lemma_rel_at(rels, y, pre, cur);
            }
        },
        Operand::Const(_, n) => lemma_uval_bounds(ty, n),
        _ => {},
    }
}

proof fn lemma_atom_keep(a: Atom, r: usize, cur: Frame, post: Frame)
    requires !atom_reads(a, r), only_root(cur, post, r as nat),
    ensures atom_val(post, a) == atom_val(cur, a),
{
    if let Atom::Val(y, _) = a {
        if (y as nat) < cur.locals.len() { assert(post.locals[y as int] == cur.locals[y as int]); }
    }
}

proof fn lemma_cmp_keep(m: Cmp, r: usize, cur: Frame, post: Frame)
    requires cmp_holds(cur, m), cmp_keeps(m, r), only_root(cur, post, r as nat),
    ensures cmp_holds(post, m),
{
    lemma_atom_keep(m.a, r, cur, post);
    lemma_atom_keep(m.b, r, cur, post);
    assert(post.locals[m.c as int] == cur.locals[m.c as int]);
}

/// A new record holds after the comparison's own write.
proof fn lemma_new_cmp(rels: Seq<Rel>, pl: Place, rv: Rvalue, pre: Frame, cur: Frame, post: Frame)
    requires
        rels_sound(rels, pre, cur), new_cmp(rels, pl.local, rv) is Some, only_root(cur, post, pl.local as nat),
        (pl.local as nat) < cur.locals.len(), post.locals[pl.local as int] == eval_rv(cur, rv).0,
        rv matches Rvalue::Bin(_, _, a, c) && (a matches Operand::Copy(q) ==> (q.local as nat) < cur.locals.len())
            && (c matches Operand::Copy(q) ==> (q.local as nat) < cur.locals.len()),
    ensures cmp_holds(post, new_cmp(rels, pl.local, rv).unwrap()),
{
    if let Rvalue::Bin(op, ty, a, c) = rv {
        let m = new_cmp(rels, pl.local, rv).unwrap();
        lemma_cmp_atom(rels, a, ty, pre, cur, m.a);
        lemma_cmp_atom(rels, c, ty, pre, cur, m.b);
        lemma_binop_cmp(op, ty, as_int(eval_op(cur, a).0), as_int(eval_op(cur, c).0));
        lemma_atom_keep(m.a, pl.local, cur, post);
        lemma_atom_keep(m.b, pl.local, cur, post);
    }
}

// ------------------------------------------------------------------ statements

pub open spec fn st_sound(b: Body, st: SymSt, pre: Frame, cur: Frame) -> bool {
    &&& st.rels.len() == b.locals@.len()
    &&& rels_sound(st.rels, pre, cur)
    &&& st.cmp matches Some(m) ==> cmp_holds(cur, m)
}

/// What every statement lemma assumes of the frame at hand.
pub open spec fn cur_ok(p: Program, ls: Seq<FnLab>, f: nat, facts: Seq<Fact>, pre: Frame, cur: Frame) -> bool {
    &&& plc(p, ls, f, cur)
    &&& frame_len_ok(cur)
    &&& facts_hold(pre, facts)
    &&& frame_len_ok(pre)
}

proof fn lemma_op_local(p: Program, ls: Seq<FnLab>, f: nat, fr: Frame, op: Operand)
    requires plc(p, ls, f, fr), ok_op(p.fns@[f as int], ls[f as int], op), op_local(op) is Some,
    ensures
        (op_local(op).unwrap() as nat) < fr.locals.len(),
        eval_op(fr, op).0 == fr.locals[op_local(op).unwrap() as int],
        eval_op(fr, op).0 == nth(fr.locals, op_local(op).unwrap() as nat),
{
    if let Operand::Copy(q) = op { lemma_read_local(fr, q, q.local); }
}

/// The value `Len` reads.
proof fn lemma_len_val(fr: Frame, v: Val)
    requires frame_len_ok(fr), len_ok(v),
    ensures
        elems(fr, v).len() <= USIZE_MAX, elems(fr, v).len() <= len_nat(fr, v),
{
    lemma_elems_len_ok(fr, v);
    lemma_elems_le_len_nat(fr, v);
}

proof fn lemma_rule_use(p: Program, ls: Seq<FnLab>, f: nat, rels: Seq<Rel>, x: usize, q: Place, pre: Frame, cur: Frame, post: Frame)
    requires
        plc(p, ls, f, cur), ok_place(p.fns@[f as int], ls[f as int], q), rels_sound(rels, pre, cur),
        nth(post.locals, x as nat) == read_place(cur, q).0,
    ensures rel_sound(rule_stmt(p.fns@[f as int], rels, seq![], x, Rvalue::Use(Operand::Copy(q))), x as nat, pre, post),
{
    let b = p.fns@[f as int];
    if q.proj@.len() == 0 {
        lemma_read_local(cur, q, q.local);
        if let Ty::Int(ty) = b.locals@[q.local as int] { lemma_rel_copy(rels, q.local, ty, x as nat, pre, cur, post); }
    } else if q.proj@.len() == 1 && q.proj@[0] is Deref {
        lemma_rel_deref(p, ls, f, rels, q, x as nat, pre, cur, post);
    }
}

proof fn lemma_rule_len(p: Program, ls: Seq<FnLab>, f: nat, rels: Seq<Rel>, x: nat, q: Place, pre: Frame, cur: Frame, post: Frame)
    requires
        plc(p, ls, f, cur), frame_len_ok(cur), ok_place(p.fns@[f as int], ls[f as int], q), q.proj@.len() == 0,
        rels_sound(rels, pre, cur),
        nth(post.locals, x) == Val::Int(elems(cur, read_place(cur, q).0).len() as u128),
    ensures rel_sound(rel_len(rels, q.local), x, pre, post),
{
    lemma_read_local(cur, q, q.local);
    let v = cur.locals[q.local as int];
    assert(len_ok(v));
    lemma_len_val(cur, v);
    assert(nth(cur.locals, q.local as nat) == v);
    lemma_rel_len(rels, q.local, x, elems(cur, v).len(), pre, cur, post);
}

proof fn lemma_rule_shr(p: Program, ls: Seq<FnLab>, f: nat, rels: Seq<Rel>, x: nat, q: Place, pre: Frame, cur: Frame, post: Frame)
    requires
        plc(p, ls, f, cur), ok_place(p.fns@[f as int], ls[f as int], q), !mut_pl(p.fns@[f as int], q), q.proj@.len() == 0,
        rels_sound(rels, pre, cur),
        nth(post.locals, x) == Val::Shr(Box::new(read_place(cur, q).0)),
    ensures rel_sound(rel_shr(rels, q.local), x, pre, post),
{
    lemma_place_plc(p, ls, f, cur, q);
    lemma_read_local(cur, q, q.local);
    assert(nth(cur.locals, q.local as nat) == cur.locals[q.local as int]);
    lemma_rel_shr(rels, q.local, x, pre, cur, post);
}

/// An `Assign`'s rule, at the rule's own write.
proof fn lemma_rule_stmt(p: Program, ls: Seq<FnLab>, f: nat, rels: Seq<Rel>, facts: Seq<Fact>, x: usize, rv: Rvalue, pre: Frame, cur: Frame, post: Frame)
    requires
        cur_ok(p, ls, f, facts, pre, cur), rels_sound(rels, pre, cur),
        ok_rv(p.fns@[f as int], ls[f as int], rv),
        nth(post.locals, x as nat) == eval_rv(cur, rv).0,
    ensures rel_sound(rule_stmt(p.fns@[f as int], rels, facts, x, rv), x as nat, pre, post),
{
    match rv {
        Rvalue::Use(Operand::Copy(q)) => {
            assert(rule_stmt(p.fns@[f as int], rels, facts, x, rv) == rule_stmt(p.fns@[f as int], rels, seq![], x, rv));
            lemma_rule_use(p, ls, f, rels, x, q, pre, cur, post);
        },
        Rvalue::Use(Operand::Const(ty, n)) => lemma_rel_const(ty, n, x as nat, pre, post),
        Rvalue::Bin(op, ty, a, c) => if op is Add && op_local(a) == Some(x) && op_one(c) {
            lemma_op_local(p, ls, f, cur, a);
            lemma_rel_inc_at(rels, facts, x, ty, pre, cur, post);
        },
        Rvalue::Len(q) => if q.proj@.len() == 0 { lemma_rule_len(p, ls, f, rels, x as nat, q, pre, cur, post); },
        Rvalue::RefShr(q) => if q.proj@.len() == 0 { lemma_rule_shr(p, ls, f, rels, x as nat, q, pre, cur, post); },
        _ => {},
    }
}

proof fn lemma_st_write(p: Program, ls: Seq<FnLab>, f: nat, st: SymSt, pl: Place, rnew: Rel, pre: Frame, cur: Frame, post: Frame)
    requires
        plc(p, ls, f, cur), st_sound(p.fns@[f as int], st, pre, cur),
        !writer_place(p.fns@[f as int], pl) ==> only_root(cur, post, pl.local as nat),
        pl.proj@.len() == 0 ==> rel_sound(rnew, pl.local as nat, pre, post),
    ensures st_sound(p.fns@[f as int], st_write(p.fns@[f as int], st, pl, rnew), pre, post),
{
    let b = p.fns@[f as int];
    if !writer_place(b, pl) {
        let r = if pl.proj@.len() == 0 { rnew } else { Rel::Unknown };
        lemma_write_root_sound(p, ls, f, st.rels, pre, cur, post, pl.local, r);
        if let Some(m) = st.cmp { if cmp_keeps(m, pl.local) { lemma_cmp_keep(m, pl.local, cur, post); } }
    }
}

proof fn lemma_sym_assign(p: Program, ls: Seq<FnLab>, f: nat, st: SymSt, facts: Seq<Fact>, pl: Place, rv: Rvalue, pre: Frame, cur: Frame)
    requires
        cur_ok(p, ls, f, facts, pre, cur), st_sound(p.fns@[f as int], st, pre, cur),
        ok_stmt(p.fns@[f as int], ls[f as int], Stmt::Assign(pl, rv)),
    ensures st_sound(p.fns@[f as int], sym_stmt(p.fns@[f as int], st, Stmt::Assign(pl, rv), facts), pre, exec_stmt(cur, Stmt::Assign(pl, rv)).0),
{
    let b = p.fns@[f as int];
    let s = Stmt::Assign(pl, rv);
    let v = eval_rv(cur, rv).0;
    let post = exec_stmt(cur, s).0;
    assert(post == assign(cur, pl, v).0);
    if !writer_place(b, pl) { lemma_assign_only_root(p, ls, f, cur, pl, v); }
    if pl.proj@.len() == 0 {
        lemma_assign_local(cur, pl, pl.local, v);
        assert(nth(post.locals, pl.local as nat) == v);
        lemma_rule_stmt(p, ls, f, st.rels, facts, pl.local, rv, pre, cur, post);
    }
    let rnew = rule_stmt(b, st.rels, facts, pl.local, rv);
    lemma_st_write(p, ls, f, st, pl, rnew, pre, cur, post);
    if pl.proj@.len() == 0 && new_cmp(st.rels, pl.local, rv) is Some {
        lemma_new_cmp(st.rels, pl, rv, pre, cur, post);
    }
}

proof fn lemma_sym_stmt(p: Program, ls: Seq<FnLab>, f: nat, st: SymSt, facts: Seq<Fact>, s: Stmt, pre: Frame, cur: Frame)
    requires
        cur_ok(p, ls, f, facts, pre, cur), st_sound(p.fns@[f as int], st, pre, cur),
        ok_stmt(p.fns@[f as int], ls[f as int], s),
    ensures st_sound(p.fns@[f as int], sym_stmt(p.fns@[f as int], st, s, facts), pre, exec_stmt(cur, s).0),
{
    match s {
        Stmt::Assign(pl, rv) => lemma_sym_assign(p, ls, f, st, facts, pl, rv, pre, cur),
        Stmt::SetDiscr(pl, k) => {
            if !writer_place(p.fns@[f as int], pl) { lemma_setdiscr_only_root(p, ls, f, cur, pl, k); }
            lemma_st_write(p, ls, f, st, pl, Rel::Unknown, pre, cur, exec_stmt(cur, s).0);
        },
    }
}

proof fn lemma_exec_stmt_len_ok(fr: Frame, s: Stmt)
    requires frame_len_ok(fr),
    ensures frame_len_ok(exec_stmt(fr, s).0),
{
    let ss = seq![s];
    lemma_exec_stmts_len_ok(ss, 0, fr);
    reveal_with_fuel(exec_stmts, 2);
    assert(ss[0] == s);
}

proof fn lemma_sym_from(p: Program, ls: Seq<FnLab>, f: nat, ss: Seq<Stmt>, k: nat, st: SymSt, facts: Seq<Fact>, pre: Frame, cur: Frame)
    requires
        cur_ok(p, ls, f, facts, pre, cur), st_sound(p.fns@[f as int], st, pre, cur), k <= ss.len(),
        forall|i: int| 0 <= i < ss.len() ==> ok_stmt(p.fns@[f as int], ls[f as int], #[trigger] ss[i]),
    ensures st_sound(p.fns@[f as int], sym_from(p.fns@[f as int], ss, k, st, facts), pre, exec_stmts(ss, k, cur).0),
    decreases ss.len() - k,
{
    if k < ss.len() {
        let s = ss[k as int];
        lemma_sym_stmt(p, ls, f, st, facts, s, pre, cur);
        lemma_plc_stmt(p, ls, f, cur, s);
        lemma_exec_stmt_len_ok(cur, s);
        lemma_sym_from(p, ls, f, ss, k + 1, sym_stmt(p.fns@[f as int], st, s, facts), facts, pre, exec_stmt(cur, s).0);
    }
}

/// The start of a block, and its typed statements and terminator.
proof fn lemma_block_start(p: Program, ls: Seq<FnLab>, f: nat, b: nat, blk: Block, facts: Seq<Fact>, fr: Frame)
    requires
        ok_prog(p, ls), f < p.fns@.len(), b < p.fns@[f as int].blocks@.len(), blk == p.fns@[f as int].blocks@[b as int],
        plc(p, ls, f, fr), facts_hold(fr, facts), frame_len_ok(fr),
    ensures ({
        let fr1 = exec_stmts(blk.stmts@, 0, fr).0;
        &&& ok_term(p, ls, f, blk.term)
        &&& cur_ok(p, ls, f, facts, fr, fr1)
        &&& st_sound(p.fns@[f as int], sym_state(p.fns@[f as int], blk.stmts@, facts), fr, fr1)
    }),
{
    let body = p.fns@[f as int];
    assert(ok_body(p, ls, f));
    assert(ok_block(p, ls, f, body.blocks@[b as int]));
    let st0 = SymSt { rels: Seq::new(body.locals@.len(), |i: int| Rel::Same), cmp: None };
    assert(st_sound(body, st0, fr, fr));
    lemma_sym_from(p, ls, f, blk.stmts@, 0, st0, facts, fr, fr);
    lemma_plc_stmts(p, ls, f, blk.stmts@, 0, fr);
    lemma_exec_stmts_len_ok(blk.stmts@, 0, fr);
}

/// The rels from the block's start to `exec_stmts(..).0`.
pub proof fn lemma_sym_stmts_sound(p: Program, ls: Seq<FnLab>, f: nat, b: nat, blk: Block, facts: Seq<Fact>, fr: Frame)
    requires
        ok_prog(p, ls), f < p.fns@.len(), b < p.fns@[f as int].blocks@.len(), blk == p.fns@[f as int].blocks@[b as int],
        plc(p, ls, f, fr), facts_hold(fr, facts), frame_len_ok(fr),
    ensures forall|s: nat| #[trigger] eff_sound(sym_stmts(p.fns@[f as int], blk.stmts@, facts), fr, exec_stmts(blk.stmts@, 0, fr).0, s),
{
    lemma_block_start(p, ls, f, b, blk, facts, fr);
}

// ------------------------------------------------------------------ edges

/// A pre-atom reading only `Same` locals has the same value at `post`.
proof fn lemma_atom_same(rels: Seq<Rel>, a: Atom, pre: Frame, post: Frame)
    requires rels_sound(rels, pre, post), atom_same(rels, a),
    ensures atom_val(post, a) == atom_val(pre, a),
    decreases a,
{
    match a {
        Atom::Val(x, _) => lemma_rel_at(rels, x, pre, post),
        Atom::Len(x) => lemma_rel_at(rels, x, pre, post),
        Atom::Gap(x, y) => {
            lemma_atom_same(rels, *x, pre, post);
            lemma_atom_same(rels, *y, pre, post);
        },
        _ => {},
    }
}

proof fn lemma_fact_same(rels: Seq<Rel>, fa: Fact, pre: Frame, post: Frame)
    requires rels_sound(rels, pre, post), fact_same(rels, fa), fact_holds(pre, fa),
    ensures fact_holds(post, fa),
{
    match fa {
        Fact::Le(x, y) => { lemma_atom_same(rels, x, pre, post); lemma_atom_same(rels, y, pre, post); },
        Fact::Lt(x, y) => { lemma_atom_same(rels, x, pre, post); lemma_atom_same(rels, y, pre, post); },
    }
}

proof fn lemma_carry_from(rels: Seq<Rel>, facts: Seq<Fact>, k: nat, acc: Seq<Fact>, pre: Frame, post: Frame)
    requires rels_sound(rels, pre, post), facts_hold(pre, facts), facts_hold(post, acc), k <= facts.len(),
    ensures facts_hold(post, carry_from(rels, facts, k, acc)),
    decreases facts.len() - k,
{
    if k < facts.len() {
        let fa = facts[k as int];
        if fact_same(rels, fa) {
            assert(fact_holds(pre, fa));
            lemma_fact_same(rels, fa, pre, post);
            let a2 = acc.push(fa);
            assert forall|i: int| 0 <= i < a2.len() implies fact_holds(post, #[trigger] a2[i]) by {
                if i < acc.len() { assert(a2[i] == acc[i]); assert(fact_holds(post, acc[i])); }
            }
            lemma_carry_from(rels, facts, k + 1, a2, pre, post);
        } else {
            lemma_carry_from(rels, facts, k + 1, acc, pre, post);
        }
    }
}

proof fn lemma_carry(rels: Seq<Rel>, facts: Seq<Fact>, pre: Frame, post: Frame)
    requires rels_sound(rels, pre, post), facts_hold(pre, facts),
    ensures facts_hold(post, carry(rels, facts)),
{
    lemma_carry_from(rels, facts, 0, seq![], pre, post);
}

/// The carried facts, and one more that holds.
proof fn lemma_facts_plus(fr: Frame, cy: Seq<Fact>, extra: Seq<Fact>)
    requires facts_hold(fr, cy), facts_hold(fr, extra),
    ensures facts_hold(fr, cy + extra),
{
    let a = cy + extra;
    assert forall|i: int| 0 <= i < a.len() implies fact_holds(fr, #[trigger] a[i]) by {
        if i < cy.len() {
            assert(a[i] == cy[i]);
            assert(fact_holds(fr, cy[i]));
        } else {
            assert(a[i] == extra[i - cy.len()]);
            assert(fact_holds(fr, extra[i - cy.len()]));
        }
    }
}

proof fn lemma_one_fact(fr: Frame, fa: Fact)
    requires fact_holds(fr, fa),
    ensures facts_hold(fr, seq![fa]),
{
    assert forall|i: int| 0 <= i < seq![fa].len() implies fact_holds(fr, #[trigger] seq![fa][i]) by { assert(seq![fa][i] == fa); }
}

/// The edge facts of the `Switch` target taken.
proof fn lemma_switch_extra(p: Program, ls: Seq<FnLab>, f: nat, st: SymSt, op: Operand, ts: Seq<(u128, usize)>, o: usize, fr1: Frame)
    requires
        plc(p, ls, f, fr1), ok_op(p.fns@[f as int], ls[f as int], op),
        st.cmp matches Some(m) ==> cmp_holds(fr1, m),
    ensures facts_hold(fr1, switch_extra(st, op, ts, o, switch_target(ts, 0, as_int(eval_op(fr1, op).0), o))),
{
    let t = switch_target(ts, 0, as_int(eval_op(fr1, op).0), o);
    if let Some(m) = tested(st, op) {
        lemma_op_local(p, ls, f, fr1, op);
        let outcome = cmp_pred(m.op, atom_val(fr1, m.a), atom_val(fr1, m.b));
        lemma_edge_lt(fr1, m, outcome);
        lemma_one_fact(fr1, cmp_fact(m, outcome));
    }
}

proof fn lemma_switch_sound(p: Program, ls: Seq<FnLab>, f: nat, st: SymSt, op: Operand, ts: Seq<(u128, usize)>, o: usize, facts: Seq<Fact>, pre: Frame, fr1: Frame)
    requires
        plc(p, ls, f, fr1), ok_op(p.fns@[f as int], ls[f as int], op), facts_hold(pre, facts), st_sound(p.fns@[f as int], st, pre, fr1),
    ensures ({
        let cy = carry(st.rels, facts);
        let e = SymEff { rel: st.rels, edge: switch_edges(st, op, ts, o, cy) };
        eff_sound(e, pre, fr1, switch_target(ts, 0, as_int(eval_op(fr1, op).0), o) as nat)
    }),
{
    let t = switch_target(ts, 0, as_int(eval_op(fr1, op).0), o);
    let cy = carry(st.rels, facts);
    lemma_carry(st.rels, facts, pre, fr1);
    lemma_switch_extra(p, ls, f, st, op, ts, o, fr1);
    lemma_facts_plus(fr1, cy, switch_extra(st, op, ts, o, t));
    let edges = switch_edges(st, op, ts, o, cy);
    assert forall|i: int| 0 <= i < edges.len() && #[trigger] edges[i].0 as nat == t as nat implies facts_hold(fr1, edges[i].1) by {
        assert(edges[i].0 == t);
    }
}

proof fn lemma_assert_sound(p: Program, ls: Seq<FnLab>, f: nat, st: SymSt, op: Operand, expected: bool, b2: usize, facts: Seq<Fact>, pre: Frame, fr1: Frame)
    requires
        plc(p, ls, f, fr1), ok_op(p.fns@[f as int], ls[f as int], op), facts_hold(pre, facts), st_sound(p.fns@[f as int], st, pre, fr1),
        (as_int(eval_op(fr1, op).0) != 0) == expected,
    ensures ({
        let e = SymEff { rel: st.rels, edge: term_edges(st, st.rels, Term::Assert(op, expected, b2), facts) };
        eff_sound(e, pre, fr1, b2 as nat)
    }),
{
    let cy = carry(st.rels, facts);
    lemma_carry(st.rels, facts, pre, fr1);
    let edges = term_edges(st, st.rels, Term::Assert(op, expected, b2), facts);
    if let Some(m) = tested(st, op) {
        if expected {
            lemma_op_local(p, ls, f, fr1, op);
            lemma_edge_lt(fr1, m, true);
            lemma_one_fact(fr1, cmp_fact(m, true));
            lemma_facts_plus(fr1, cy, seq![cmp_fact(m, true)]);
        }
    }
    assert(edges.len() == 1);
}

proof fn lemma_next_edge(rels: Seq<Rel>, facts: Seq<Fact>, next: usize, pre: Frame, post: Frame)
    requires rels_sound(rels, pre, post), facts_hold(pre, facts),
    ensures eff_sound(SymEff { rel: rels, edge: seq![(next, carry(rels, facts))] }, pre, post, next as nat),
{
    lemma_carry(rels, facts, pre, post);
    assert(seq![(next, carry(rels, facts))].len() == 1);
}

// ------------------------------------------------------------------ calls and intrinsics

proof fn lemma_write_back_none(fr: Frame, slots: Seq<Val>, wb: Seq<Option<Loc>>)
    requires forall|j: int| 0 <= j < wb.len() ==> #[trigger] wb[j] is None,
    ensures write_back(fr, slots, wb) == fr,
    decreases wb.len(),
{
    if wb.len() > 0 {
        let w0 = wb.drop_last();
        assert forall|j: int| 0 <= j < w0.len() implies #[trigger] w0[j] is None by { assert(w0[j] == wb[j]); }
        lemma_write_back_none(fr, slots, w0);
        assert(wb[wb.len() - 1] is None);
    }
}

/// With no `Mut` argument, a call only writes its dst.
proof fn lemma_call_only_dst(p: Program, ls: Seq<FnLab>, f: nat, g: nat, args: Seq<Operand>, dst: Place, out: Frame, fr1: Frame)
    requires
        plc(p, ls, f, fr1), ok_place(p.fns@[f as int], ls[f as int], dst), !writer_place(p.fns@[f as int], dst),
        !call_writer(p.fns@[f as int], args), forall|j: int| 0 <= j < args.len() ==> ok_op(p.fns@[f as int], ls[f as int], #[trigger] args[j]),
    ensures only_root(fr1, call_leave(fr1, out, call_enter(p, g, fr1, args).1, dst).0, dst.local as nat),
{
    let wb = call_enter(p, g, fr1, args).1;
    assert forall|j: int| 0 <= j < wb.len() implies #[trigger] wb[j] is None by {
        assert(ok_op(p.fns@[f as int], ls[f as int], args[j]));
        assert(!mut_op(p.fns@[f as int], args[j]));
        lemma_eval_op_plc(p, ls, f, fr1, args[j]);
    }
    lemma_write_back_none(fr1, out.slots, wb);
    lemma_assign_only_root(p, ls, f, fr1, dst, nth(out.locals, 0));
}

proof fn lemma_call_sound(p: Program, ls: Seq<FnLab>, f: nat, g: nat, args: Vec<Operand>, dst: Place, next: usize, rels: Seq<Rel>, facts: Seq<Fact>, out: Frame, pre: Frame, fr1: Frame)
    requires
        plc(p, ls, f, fr1), ok_place(p.fns@[f as int], ls[f as int], dst), rels.len() == fr1.locals.len(), rels_sound(rels, pre, fr1), facts_hold(pre, facts),
        forall|j: int| 0 <= j < args@.len() ==> ok_op(p.fns@[f as int], ls[f as int], #[trigger] args@[j]),
    ensures ({
        let r2 = term_rels(p.fns@[f as int], rels, Term::Call(Callee::Fn(g as usize), args, dst, next), facts);
        rels_sound(r2, pre, call_leave(fr1, out, call_enter(p, g, fr1, args@).1, dst).0)
    }),
{
    let b = p.fns@[f as int];
    if !call_writer(b, args@) && !writer_place(b, dst) {
        lemma_call_only_dst(p, ls, f, g, args@, dst, out, fr1);
        lemma_write_root_sound(p, ls, f, rels, pre, fr1, call_leave(fr1, out, call_enter(p, g, fr1, args@).1, dst).0, dst.local, Rel::Unknown);
    }
}

/// A non-writing intrinsic leaves the frame to its dst.
proof fn lemma_intr_keeps(p: Program, ls: Seq<FnLab>, f: nat, k: Intrinsic, args: Seq<Operand>, dst: Place, fr: Frame)
    requires plc(p, ls, f, fr), ok_intr(p.fns@[f as int], ls[f as int], k, args, dst), !intr_writer(p.fns@[f as int], k, args),
    ensures intr_eff(k, fr, op_vals(fr, args)) matches Some((g, _, _)) ==> g == fr,
{
    if args.len() > 0 && (k is VecPush || k is VecSet || k is VecExtendFromSlice) {
        lemma_arg_val(p, ls, f, fr, args, 0);
    }
}

/// What an intrinsic with result `r` writes.
proof fn lemma_rule_intr_read(p: Program, ls: Seq<FnLab>, f: nat, rels: Seq<Rel>, x: usize, k: Intrinsic, args: Seq<Operand>, dst: Place, r: Val, y: usize, pre: Frame, cur: Frame, post: Frame)
    requires
        plc(p, ls, f, cur), frame_len_ok(cur), rels_sound(rels, pre, cur), ok_intr(p.fns@[f as int], ls[f as int], k, args, dst),
        arg_local(args, 0) == Some(y), intr_eff(k, cur, op_vals(cur, args)) matches Some((_, r0, _)) && r0 == r,
        nth(post.locals, x as nat) == r,
        k is VecLen || k is VecAsSlice || k is SliceSubrange || k is SliceToVec,
    ensures rel_sound(rule_intr(rels, seq![], x, k, args), x as nat, pre, post),
{
    lemma_arg_val(p, ls, f, cur, args, 0);
    lemma_op_local(p, ls, f, cur, args[0]);
    let v = cur.locals[y as int];
    assert(nth(op_vals(cur, args), 0) == v);
    match k {
        Intrinsic::VecLen => {
            assert(len_ok(v));
            lemma_len_val(cur, v);
            lemma_rel_len(rels, y, x as nat, elems(cur, v).len(), pre, cur, post);
        },
        Intrinsic::VecAsSlice => lemma_rel_shr(rels, y, x as nat, pre, cur, post),
        Intrinsic::SliceSubrange => {
            let (s, lo, hi) = (elems(cur, v), as_int(nth(op_vals(cur, args), 1)), as_int(nth(op_vals(cur, args), 2)));
            let h = if (hi as nat) < s.len() { hi as int } else { s.len() as int };
            let l = if (lo as int) < h { lo as int } else { h };
            lemma_rel_subrange(rels, y, x as nat, s, l, h, pre, cur, post);
        },
        _ => lemma_rel_to_vec(rels, y, x as nat, pre, cur, post),
    }
}

proof fn lemma_rule_intr(p: Program, ls: Seq<FnLab>, f: nat, rels: Seq<Rel>, facts: Seq<Fact>, x: usize, k: Intrinsic, args: Seq<Operand>, dst: Place, r: Val, pre: Frame, cur: Frame, post: Frame)
    requires
        cur_ok(p, ls, f, facts, pre, cur), rels_sound(rels, pre, cur), ok_intr(p.fns@[f as int], ls[f as int], k, args, dst),
        intr_eff(k, cur, op_vals(cur, args)) matches Some((_, r0, _)) && r0 == r,
        nth(post.locals, x as nat) == r,
    ensures rel_sound(rule_intr(rels, facts, x, k, args), x as nat, pre, post),
{
    if let Some(y) = arg_local(args, 0) {
        match k {
            Intrinsic::VecLen | Intrinsic::VecAsSlice | Intrinsic::SliceSubrange | Intrinsic::SliceToVec => {
                assert(rule_intr(rels, facts, x, k, args) == rule_intr(rels, seq![], x, k, args));
                lemma_rule_intr_read(p, ls, f, rels, x, k, args, dst, r, y, pre, cur, post);
            },
            Intrinsic::Wrapping(BinOp::Add, ty) => if y == x && args.len() > 1 && op_one(args[1]) {
                lemma_arg_val(p, ls, f, cur, args, 0);
                lemma_arg_val(p, ls, f, cur, args, 1);
                lemma_op_local(p, ls, f, cur, args[0]);
                lemma_rel_inc_at(rels, facts, x, ty, pre, cur, post);
            },
            _ => {},
        }
    }
}

proof fn lemma_intr_sound(p: Program, ls: Seq<FnLab>, f: nat, k: Intrinsic, args: Vec<Operand>, dst: Place, next: usize, rels: Seq<Rel>, facts: Seq<Fact>, pre: Frame, fr1: Frame)
    requires
        cur_ok(p, ls, f, facts, pre, fr1), rels.len() == fr1.locals.len(), rels_sound(rels, pre, fr1),
        ok_intr(p.fns@[f as int], ls[f as int], k, args@, dst), exec_intr(k, fr1, args@, dst) is Some,
    ensures ({
        let r2 = term_rels(p.fns@[f as int], rels, Term::Call(Callee::Intr(k), args, dst, next), facts);
        rels_sound(r2, pre, exec_intr(k, fr1, args@, dst).unwrap().0)
    }),
{
    let b = p.fns@[f as int];
    if !intr_writer(b, k, args@) && !writer_place(b, dst) {
        lemma_intr_keeps(p, ls, f, k, args@, dst, fr1);
        let (g, r, _) = intr_eff(k, fr1, op_vals(fr1, args@)).unwrap();
        let post = exec_intr(k, fr1, args@, dst).unwrap().0;
        assert(post == assign(fr1, dst, r).0);
        lemma_assign_only_root(p, ls, f, fr1, dst, r);
        if dst.proj@.len() == 0 {
            lemma_assign_local(fr1, dst, dst.local, r);
            assert(nth(post.locals, dst.local as nat) == r);
            lemma_rule_intr(p, ls, f, rels, facts, dst.local, k, args@, dst, r, pre, fr1, post);
        }
        let rnew = if dst.proj@.len() == 0 { rule_intr(rels, facts, dst.local, k, args@) } else { Rel::Unknown };
        lemma_write_root_sound(p, ls, f, rels, pre, fr1, post, dst.local, rnew);
    }
}

// ------------------------------------------------------------------ the block

proof fn lemma_term_fn(p: Program, ls: Seq<FnLab>, f: nat, blk: Block, facts: Seq<Fact>, pre: Frame, fr1: Frame, st: SymSt)
    requires
        f < p.fns@.len(), blk.term is Call, blk.term->Call_0 is Fn, fr1 == exec_stmts(blk.stmts@, 0, pre).0,
        ok_term(p, ls, f, blk.term), cur_ok(p, ls, f, facts, pre, fr1), st_sound(p.fns@[f as int], st, pre, fr1),
        st == sym_state(p.fns@[f as int], blk.stmts@, facts),
    ensures sym_block_sound(p, blk, facts, pre, sym_block(p.fns@[f as int], blk, facts)),
{
    hide(exec_stmts);
    let e = sym_block(p.fns@[f as int], blk, facts);
    if let Term::Call(Callee::Fn(g), args, dst, next) = blk.term {
        assert forall|j: int| 0 <= j < args@.len() implies ok_op(p.fns@[f as int], ls[f as int], #[trigger] args@[j]) by {
            assert(ok_arg(p.fns@[f as int], ls[f as int], p.fns@[g as int], ls[g as int], j, args@[j]));
        }
        assert forall|out: Frame| frame_len_ok(out) implies
            #[trigger] eff_sound(e, pre, call_leave(fr1, out, call_enter(p, g as nat, fr1, args@).1, dst).0, next as nat) by {
            let post = call_leave(fr1, out, call_enter(p, g as nat, fr1, args@).1, dst).0;
            lemma_call_sound(p, ls, f, g as nat, args, dst, next, st.rels, facts, out, pre, fr1);
            lemma_next_edge(e.rel, facts, next, pre, post);
        }
    }
}

/// The successors of a block, at the frame the terminator actually leaves.
pub proof fn lemma_sym_block_sound(p: Program, ls: Seq<FnLab>, f: nat, b: nat, blk: Block, facts: Seq<Fact>, fr: Frame)
    requires
        ok_prog(p, ls), f < p.fns@.len(), b < p.fns@[f as int].blocks@.len(), blk == p.fns@[f as int].blocks@[b as int],
        plc(p, ls, f, fr), facts_hold(fr, facts), frame_len_ok(fr),
    ensures sym_block_sound(p, blk, facts, fr, sym_block(p.fns@[f as int], blk, facts)),
{
    hide(exec_stmts);
    hide(ok_prog);
    lemma_block_start(p, ls, f, b, blk, facts, fr);
    let body = p.fns@[f as int];
    let fr1 = exec_stmts(blk.stmts@, 0, fr).0;
    let st = sym_state(body, blk.stmts@, facts);
    let e = sym_block(body, blk, facts);
    match blk.term {
        Term::Goto(b2) => lemma_next_edge(st.rels, facts, b2, fr, fr1),
        Term::Switch(op, ts, o) => lemma_switch_sound(p, ls, f, st, op, ts@, o, facts, fr, fr1),
        Term::Assert(op, expected, b2) => if (as_int(eval_op(fr1, op).0) != 0) == expected {
            lemma_assert_sound(p, ls, f, st, op, expected, b2, facts, fr, fr1);
        },
        Term::Call(Callee::Intr(k), args, dst, next) => if exec_intr(k, fr1, args@, dst) is Some {
            lemma_intr_sound(p, ls, f, k, args, dst, next, st.rels, facts, fr, fr1);
            lemma_next_edge(e.rel, facts, next, fr, exec_intr(k, fr1, args@, dst).unwrap().0);
        },
        Term::Call(Callee::Fn(_), _, _, _) => lemma_term_fn(p, ls, f, blk, facts, fr, fr1, st),
        _ => {},
    }
}

// ------------------------------------------------------------------ the rules on MIR's shapes

pub open spec fn stmts2_state(b: Body, s0: Stmt, s1: Stmt, facts: Seq<Fact>) -> SymSt {
    sym_state(b, seq![s0, s1], facts)
}

proof fn lemma_state2(b: Body, s0: Stmt, s1: Stmt, facts: Seq<Fact>)
    ensures ({
        let st0 = SymSt { rels: Seq::new(b.locals@.len(), |i: int| Rel::Same), cmp: None };
        stmts2_state(b, s0, s1, facts) == sym_stmt(b, sym_stmt(b, st0, s0, facts), s1, facts)
    }),
{
    let ss = seq![s0, s1];
    assert(ss[0] == s0 && ss[1] == s1);
    reveal_with_fuel(sym_from, 3);
}

/// `_3 = copy (*_2); _4 = Len(_3)` gives `_4` `ValLe(Len(2))`.
pub proof fn sanity_double_ref(b: Body, d3: Place, q: Place, d4: Place, r: Place, facts: Seq<Fact>)
    requires
        b.locals@.len() == 5, !(b.locals@[3] is Mut), !(b.locals@[4] is Mut),
        d3.local == 3, d3.proj@.len() == 0, q.local == 2, q.proj@.len() == 1, q.proj@[0] is Deref,
        d4.local == 4, d4.proj@.len() == 0, r.local == 3, r.proj@.len() == 0,
    ensures ({
        let s0 = Stmt::Assign(d3, Rvalue::Use(Operand::Copy(q)));
        let s1 = Stmt::Assign(d4, Rvalue::Len(r));
        stmts2_state(b, s0, s1, facts).rels[4] == Rel::ValLe(Atom::Len(2))
    }),
{
    lemma_state2(b, Stmt::Assign(d3, Rvalue::Use(Operand::Copy(q))), Stmt::Assign(d4, Rvalue::Len(r)), facts);
}

/// `_5 = copy _3; _4 = Lt(_5, _2); switch(_4)` tests `Lt(Val(3), Val(2))`, through the temp copy.
pub proof fn sanity_temp_copy(b: Body, d5: Place, y3: Place, d4: Place, t5: Place, t2: Place, c: Place, facts: Seq<Fact>)
    requires
        b.locals@.len() == 6,
        b.locals@[5] == Ty::Int(IntTy::Usize), b.locals@[3] == Ty::Int(IntTy::Usize), !(b.locals@[4] is Mut),
        d5.local == 5, d5.proj@.len() == 0, y3.local == 3, y3.proj@.len() == 0,
        d4.local == 4, d4.proj@.len() == 0, t5.local == 5, t5.proj@.len() == 0, t2.local == 2, t2.proj@.len() == 0,
        c.local == 4, c.proj@.len() == 0,
    ensures ({
        let s0 = Stmt::Assign(d5, Rvalue::Use(Operand::Copy(y3)));
        let s1 = Stmt::Assign(d4, Rvalue::Bin(BinOp::Lt, IntTy::Usize, Operand::Copy(t5), Operand::Copy(t2)));
        let (va, vb) = (Atom::Val(3, IntTy::Usize), Atom::Val(2, IntTy::Usize));
        tested(stmts2_state(b, s0, s1, facts), Operand::Copy(c)) == Some(Cmp { c: 4, op: BinOp::Lt, a: va, b: vb })
    }),
{
    let s0 = Stmt::Assign(d5, Rvalue::Use(Operand::Copy(y3)));
    let s1 = Stmt::Assign(d4, Rvalue::Bin(BinOp::Lt, IntTy::Usize, Operand::Copy(t5), Operand::Copy(t2)));
    lemma_state2(b, s0, s1, facts);
    let st0 = SymSt { rels: Seq::new(b.locals@.len(), |i: int| Rel::Same), cmp: None };
    let st1 = sym_stmt(b, st0, s0, facts);
    assert(st1.rels[5] == Rel::ValEq(Atom::Val(3, IntTy::Usize), 0));
    assert(st1.rels[3] is Same);
}

} // verus!
