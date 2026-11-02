//! Step-bound certificates (Phase 8b; the spec part is frozen from the end of Task 2): bounds over
//! frame atoms, the per-block obligation `block_step_ok`, and `theorem_cost`: a terminating run
//! takes at most `summary(inputs)` steps. Validity of a certificate is semantic here; the verified
//! validator in `cost_check` establishes it.
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

// ------------------------------------------------------------------ bounds and certificates

/// `Val` reads a local at a width, as MIR's comparisons do.
pub enum Atom { Const(u64), Val(usize, IntTy), Len(usize), Gap(Box<Atom>, Box<Atom>) }

/// `coef` times the product of `atoms`.
// ponytail: at most 2 atoms, in canonical order (`check_cert` enforces it); higher degree needs a multiset-product lemma.
pub struct Mono { pub coef: u64, pub atoms: Vec<Atom> }

pub struct Poly { pub monos: Vec<Mono> }

pub enum Fact { Le(Atom, Atom), Lt(Atom, Atom) }

pub struct BlockCert { pub facts: Vec<Fact>, pub pot: Poly }

pub struct Cert { pub blocks: Vec<BlockCert> }

// ------------------------------------------------------------------ values of bounds

/// An `Int` at width `ty`; 0 for anything else.
pub open spec fn val_nat(ty: IntTy, v: Val) -> nat {
    match v { Val::Int(x) => uval(ty, x) as nat, _ => 0 }
}

/// The length of the `Arr` at the end of any number of `Shr`; 0 otherwise.
pub open spec fn shr_len(v: Val) -> nat
    decreases v,
{
    match v { Val::Shr(b) => shr_len(*b), Val::Arr(s) => s.len(), _ => 0 }
}

/// The length behind `v`: through a `Mut`'s target, then any number of `Shr`. `parse` takes `&&[u8]`.
pub open spec fn len_nat(fr: Frame, v: Val) -> nat {
    match v { Val::Mut(l) => shr_len(read_loc(fr, l)), _ => shr_len(v) }
}

pub open spec fn gap(a: nat, b: nat) -> nat {
    if a >= b { (a - b) as nat } else { 0 }
}

pub open spec fn atom_val(fr: Frame, a: Atom) -> nat
    decreases a,
{
    match a {
        Atom::Const(c) => c as nat,
        Atom::Val(x, ty) => val_nat(ty, nth(fr.locals, x as nat)),
        Atom::Len(x) => len_nat(fr, nth(fr.locals, x as nat)),
        Atom::Gap(x, y) => gap(atom_val(fr, *x), atom_val(fr, *y)),
    }
}

pub open spec fn atoms_val(fr: Frame, atoms: Seq<Atom>) -> nat
    decreases atoms.len(),
{
    if atoms.len() == 0 { 1 } else { atom_val(fr, atoms[0]) * atoms_val(fr, atoms.drop_first()) }
}

pub open spec fn mono_val(fr: Frame, m: Mono) -> nat {
    m.coef as nat * atoms_val(fr, m.atoms@)
}

pub open spec fn monos_val(fr: Frame, ms: Seq<Mono>) -> nat
    decreases ms.len(),
{
    if ms.len() == 0 { 0 } else { mono_val(fr, ms[0]) + monos_val(fr, ms.drop_first()) }
}

pub open spec fn poly_val(fr: Frame, p: Poly) -> nat {
    monos_val(fr, p.monos@)
}

pub open spec fn fact_holds(fr: Frame, f: Fact) -> bool {
    match f {
        Fact::Le(a, b) => atom_val(fr, a) <= atom_val(fr, b),
        Fact::Lt(a, b) => atom_val(fr, a) < atom_val(fr, b),
    }
}

pub open spec fn facts_hold(fr: Frame, fs: Seq<Fact>) -> bool {
    forall|i: int| 0 <= i < fs.len() ==> fact_holds(fr, #[trigger] fs[i])
}

pub open spec fn frame_len_ok(fr: Frame) -> bool {
    &&& forall|i: int| 0 <= i < fr.locals.len() ==> len_ok(#[trigger] fr.locals[i])
    &&& forall|j: int| 0 <= j < fr.slots.len() ==> len_ok(#[trigger] fr.slots[j])
}

pub open spec fn vals_len_ok(vs: Seq<Val>) -> bool {
    forall|i: int| 0 <= i < vs.len() ==> len_ok(#[trigger] vs[i])
}

/// `args_agree`'s facts for one run: one arg and one slot per parameter, holding no `Mut`.
pub open spec fn entry_plc(p: Program, f: nat, args: Seq<Val>, slots: Seq<Val>) -> bool {
    let b = p.fns@[f as int];
    &&& args.len() == b.nargs
    &&& slots.len() == b.nargs
    &&& forall|j: int| 0 <= j < b.nargs && !(b.locals@[1 + j] is Mut) ==> no_mut(#[trigger] args[j])
    &&& forall|j: int| 0 <= j < b.nargs ==> no_mut(#[trigger] slots[j])
}

// ------------------------------------------------------------------ certificates

/// Successor `succ`'s facts hold at `post`, and `pot` pays `cost` plus `succ`'s potential there.
pub open spec fn succ_ok(c: Cert, succ: nat, pot: nat, cost: nat, post: Frame) -> bool {
    &&& facts_hold(post, c.blocks@[succ as int].facts@)
    &&& pot >= cost + poly_val(post, c.blocks@[succ as int].pot)
}

/// `succ_ok` for a callee that left frame `out` after `n` steps.
pub open spec fn call_out_ok(c: Cert, next: nat, pot: nat, k: nat, fr1: Frame, wb: Seq<Option<Loc>>, dst: Place, out: Frame, n: nat) -> bool {
    succ_ok(c, next, pot, k + 1 + n, call_leave(fr1, out, wb, dst).0)
}

/// One block's obligation from a frame at its start.
pub open spec fn block_step_ok(p: Program, f: nat, b: nat, c: Cert, sums: Seq<Option<Poly>>, fr: Frame) -> bool {
    let blk = p.fns@[f as int].blocks@[b as int];
    let k = blk.stmts@.len();
    let fr1 = exec_stmts(blk.stmts@, 0, fr).0;
    let pot = poly_val(fr, c.blocks@[b as int].pot);
    match blk.term {
        Term::Goto(b2) => succ_ok(c, b2 as nat, pot, k + 1, fr1),
        Term::Switch(op, ts, o) =>
            succ_ok(c, switch_target(ts@, 0, as_int(eval_op(fr1, op).0), o) as nat, pot, k + 1, fr1),
        Term::Assert(op, expected, b2) =>
            (as_int(eval_op(fr1, op).0) != 0) == expected ==> succ_ok(c, b2 as nat, pot, k + 1, fr1),
        Term::Return => pot >= k + 1,
        Term::Abort => true,
        Term::Call(Callee::Intr(i), args, dst, next) => match exec_intr(i, fr1, args@, dst) {
            Some((fr2, _, extra)) => succ_ok(c, next as nat, pot, k + 1 + extra, fr2),
            None => true,
        },
        Term::Call(Callee::Fn(g), args, dst, next) => {
            let (cf, wb, _) = call_enter(p, g as nat, fr1, args@);
            &&& sums[g as int] is Some
            &&& forall|out: Frame, n: nat| frame_len_ok(out) && n <= poly_val(cf, sums[g as int].unwrap())
                    ==> #[trigger] call_out_ok(c, next as nat, pot, k, fr1, wb, dst, out, n)
        },
    }
}

/// `ls` stays inside the quantifier: `check_program` says nothing about its labels' values, and
/// no cost proof reads a label.
pub open spec fn cert_sem_ok(p: Program, f: nat, c: Cert, sums: Seq<Option<Poly>>) -> bool {
    &&& c.blocks@.len() == p.fns@[f as int].blocks@.len()
    &&& forall|ls: Seq<FnLab>, b: nat, fr: Frame| #![trigger plc(p, ls, f, fr), block_step_ok(p, f, b, c, sums, fr)]
            b < c.blocks@.len() && ok_prog(p, ls) && plc(p, ls, f, fr)
            && facts_hold(fr, c.blocks@[b as int].facts@) && frame_len_ok(fr)
            ==> block_step_ok(p, f, b, c, sums, fr)
}

pub open spec fn cert_for(p: Program, f: nat, c: Cert, sums: Seq<Option<Poly>>) -> bool {
    &&& cert_sem_ok(p, f, c, sums)
    &&& c.blocks@[0].facts@.len() == 0
    &&& sums[f as int] == Some(c.blocks@[0].pot)
}

// ------------------------------------------------------------------ gap

pub proof fn lemma_gap_dec(a: nat, x: nat)
    requires x < a,
    ensures gap(a, x) == gap(a, x + 1) + 1,
{
}

// ------------------------------------------------------------------ len_ok: values

proof fn lemma_get_len_ok(v: Val, e: PE)
    requires len_ok(v),
    ensures len_ok(get(v, e)),
{
    match (v, e) {
        (Val::Tup(vs), PE::Field(i)) => if i < vs.len() { assert(len_ok(vs[i as int])); },
        (Val::Adt(_, vs), PE::Field(i)) => if i < vs.len() { assert(len_ok(vs[i as int])); },
        (Val::Arr(vs), PE::Index(i)) => if i < vs.len() { assert(len_ok(vs[i as int])); },
        (Val::Adt(_, vs), PE::Variant(k)) => {
            assert forall|i: int| 0 <= i < vs.len() implies len_ok(#[trigger] vs[i]) by {}
        },
        _ => {},
    }
}

proof fn lemma_read_at_len_ok(v: Val, path: Seq<PE>)
    requires len_ok(v),
    ensures len_ok(read_at(v, path)),
    decreases path.len(),
{
    if path.len() > 0 {
        lemma_get_len_ok(v, path[0]);
        lemma_read_at_len_ok(get(v, path[0]), path.drop_first());
    }
}

/// A field update, padding with `Unit`.
proof fn lemma_fields_len_ok(vs: Seq<Val>, i: nat, w: Val)
    requires forall|k: int| 0 <= k < vs.len() ==> len_ok(#[trigger] vs[k]), len_ok(w),
    ensures forall|k: int| 0 <= k < pad(vs, i + 1).update(i as int, w).len() ==> len_ok(#[trigger] pad(vs, i + 1).update(i as int, w)[k]),
{
    let a = pad(vs, i + 1).update(i as int, w);
    assert forall|k: int| 0 <= k < a.len() implies len_ok(#[trigger] a[k]) by {
        if k != i as int {
            if k < vs.len() { assert(pad(vs, i + 1)[k] == vs[k]); } else { assert(pad(vs, i + 1)[k] == Val::Unit); }
        }
    }
}

proof fn lemma_put_len_ok(v: Val, e: PE, w: Val)
    requires len_ok(v), len_ok(w),
    ensures len_ok(put(v, e, w)),
{
    match (v, e) {
        (Val::Tup(vs), PE::Field(i)) => lemma_fields_len_ok(vs, i, w),
        (Val::Adt(_, vs), PE::Field(i)) => lemma_fields_len_ok(vs, i, w),
        (Val::Arr(vs), PE::Index(i)) => if i < vs.len() {
            let a = vs.update(i as int, w);
            assert forall|k: int| 0 <= k < a.len() implies len_ok(#[trigger] a[k]) by {
                if k != i as int { assert(len_ok(vs[k])); }
            }
        },
        (Val::Adt(_, _), PE::Variant(_)) => if let Val::Adt(_, ws) = w {
            assert forall|k: int| 0 <= k < ws.len() implies len_ok(#[trigger] ws[k]) by {}
        },
        _ => {},
    }
}

proof fn lemma_write_at_len_ok(v: Val, path: Seq<PE>, w: Val)
    requires len_ok(v), len_ok(w),
    ensures len_ok(write_at(v, path, w)),
    decreases path.len(),
{
    if path.len() > 0 {
        lemma_get_len_ok(v, path[0]);
        lemma_write_at_len_ok(get(v, path[0]), path.drop_first(), w);
        lemma_put_len_ok(v, path[0], write_at(get(v, path[0]), path.drop_first(), w));
    }
}

/// A `ConstVal` array comes from a `Vec`, so its length fits a usize.
proof fn lemma_const_len_ok(c: ConstVal)
    ensures len_ok(const_val(c)),
    decreases c,
{
    match c {
        ConstVal::Arr(cs) => {
            let vs = Seq::new(cs@.len(), |i: int| if 0 <= i < cs@.len() { const_val(cs@[i]) } else { Val::Unit });
            assert forall|i: int| 0 <= i < vs.len() implies len_ok(#[trigger] vs[i]) by { lemma_const_len_ok(cs@[i]); }
            assert(cs.len() == cs@.len());
            assert(const_val(c)->Arr_0 =~= vs);
        },
        ConstVal::Shr(b) => lemma_const_len_ok(*b),
        _ => {},
    }
}

// ------------------------------------------------------------------ len_ok: frames and places

proof fn lemma_nth_len_ok(vs: Seq<Val>, i: nat)
    requires vals_len_ok(vs),
    ensures len_ok(nth(vs, i)),
{
    if i < vs.len() { assert(len_ok(vs[i as int])); }
}

pub proof fn lemma_read_loc_len_ok(fr: Frame, l: Loc)
    requires frame_len_ok(fr),
    ensures len_ok(read_loc(fr, l)),
{
    match l.root {
        Root::Local(i) => {
            lemma_nth_len_ok(fr.locals, i);
            lemma_read_at_len_ok(nth(fr.locals, i), l.path);
        },
        Root::Slot(j) => {
            lemma_nth_len_ok(fr.slots, j);
            lemma_read_at_len_ok(nth(fr.slots, j), l.path);
        },
    }
}

proof fn lemma_write_loc_len_ok(fr: Frame, l: Loc, w: Val)
    requires frame_len_ok(fr), len_ok(w),
    ensures frame_len_ok(write_loc(fr, l, w)),
{
    let g = write_loc(fr, l, w);
    match l.root {
        Root::Local(i) => if i < fr.locals.len() {
            lemma_write_at_len_ok(fr.locals[i as int], l.path, w);
            assert forall|k: int| 0 <= k < g.locals.len() implies len_ok(#[trigger] g.locals[k]) by {
                if k != i as int { assert(len_ok(fr.locals[k])); }
            }
        },
        Root::Slot(j) => if j < fr.slots.len() {
            lemma_write_at_len_ok(fr.slots[j as int], l.path, w);
            assert forall|k: int| 0 <= k < g.slots.len() implies len_ok(#[trigger] g.slots[k]) by {
                if k != j as int { assert(len_ok(fr.slots[k])); }
            }
        },
    }
}

/// A place walk's snapshot cursor reads a `len_ok` value.
spec fn cur_len_ok(c: Cur) -> bool {
    match c { Cur::V(v) => len_ok(v), Cur::L(_) => true }
}

proof fn lemma_walk_len_ok(fr: Frame, ps: Seq<Proj>, k: nat, c: Cur)
    requires frame_len_ok(fr), k <= ps.len(), cur_len_ok(c),
    ensures cur_len_ok(walk(fr, ps, k, c).0),
    decreases ps.len() - k,
{
    if k < ps.len() {
        let c1 = step(fr, c, ps[k as int]).0;
        if let Cur::L(l) = c { lemma_read_loc_len_ok(fr, l); }
        if let Cur::V(v) = c {
            match ps[k as int] {
                Proj::Field(i) => lemma_get_len_ok(v, PE::Field(i as nat)),
                Proj::Index(x) => lemma_get_len_ok(v, PE::Index(as_int(read_loc(fr, local_loc(x as nat))) as nat)),
                Proj::ConstIndex(n) => lemma_get_len_ok(v, PE::Index(n as nat)),
                Proj::Downcast(n) => lemma_get_len_ok(v, PE::Variant(n as nat)),
                _ => {},
            }
        }
        assert(cur_len_ok(c1));
        lemma_walk_len_ok(fr, ps, k + 1, c1);
    }
}

proof fn lemma_read_place_len_ok(fr: Frame, pl: Place)
    requires frame_len_ok(fr),
    ensures len_ok(read_place(fr, pl).0),
{
    lemma_walk_len_ok(fr, pl.proj@, 0, Cur::L(local_loc(pl.local as nat)));
    if let Cur::L(l) = place_walk(fr, pl).0 { lemma_read_loc_len_ok(fr, l); }
}

proof fn lemma_assign_len_ok(fr: Frame, pl: Place, v: Val)
    requires frame_len_ok(fr), len_ok(v),
    ensures frame_len_ok(assign(fr, pl, v).0),
{
    if let Some((l, _)) = place_loc(fr, pl) { lemma_write_loc_len_ok(fr, l, v); }
}

proof fn lemma_eval_op_len_ok(fr: Frame, op: Operand)
    requires frame_len_ok(fr),
    ensures len_ok(eval_op(fr, op).0),
{
    match op {
        Operand::Copy(pl) => lemma_read_place_len_ok(fr, pl),
        Operand::Lit(c) => lemma_const_len_ok(c),
        _ => {},
    }
}

proof fn lemma_op_vals_len_ok(fr: Frame, ops: Seq<Operand>)
    requires frame_len_ok(fr),
    ensures vals_len_ok(op_vals(fr, ops)),
{
    let vs = op_vals(fr, ops);
    assert forall|i: int| 0 <= i < vs.len() implies len_ok(#[trigger] vs[i]) by { lemma_eval_op_len_ok(fr, ops[i]); }
}

pub proof fn lemma_elems_len_ok(fr: Frame, v: Val)
    requires frame_len_ok(fr), len_ok(v),
    ensures elems(fr, v).len() <= USIZE_MAX, vals_len_ok(elems(fr, v)),
{
    if let Val::Mut(l) = v { lemma_read_loc_len_ok(fr, l); }
    let t = match v { Val::Shr(b) => *b, Val::Mut(l) => read_loc(fr, l), _ => v };
    assert(len_ok(t));
    if let Val::Arr(s) = t {
        assert forall|i: int| 0 <= i < s.len() implies len_ok(#[trigger] s[i]) by {}
    }
}

pub proof fn lemma_shr_len_ok(v: Val)
    requires len_ok(v),
    ensures shr_len(v) <= USIZE_MAX,
    decreases v,
{
    if let Val::Shr(b) = v { lemma_shr_len_ok(*b); }
}

/// What `Rvalue::Len` and the len-cost intrinsics read is at most `len_nat`.
pub proof fn lemma_elems_le_len_nat(fr: Frame, v: Val)
    ensures elems(fr, v).len() <= len_nat(fr, v),
{
    if let Val::Shr(b) = v {
        assert(shr_len(v) == shr_len(*b));
        if let Val::Arr(s) = *b { assert(shr_len(*b) == s.len()); }
    } else if let Val::Arr(s) = v {
        assert(shr_len(v) == s.len());
    } else if let Val::Mut(l) = v {
        if let Val::Arr(s) = read_loc(fr, l) { assert(shr_len(read_loc(fr, l)) == s.len()); }
    }
}

// ------------------------------------------------------------------ len_ok: statements

proof fn lemma_eval_rv_len_ok(fr: Frame, rv: Rvalue)
    requires frame_len_ok(fr),
    ensures len_ok(eval_rv(fr, rv).0),
{
    match rv {
        Rvalue::Use(op) => lemma_eval_op_len_ok(fr, op),
        Rvalue::Aggregate(_, ops) => {
            lemma_op_vals_len_ok(fr, ops@);
            assert(op_vals(fr, ops@).len() == ops.len());
        },
        Rvalue::Repeat(op, n) => {
            lemma_eval_op_len_ok(fr, op);
            let v = eval_op(fr, op).0;
            let a = Seq::new(n as nat, |j: int| v);
            assert forall|i: int| 0 <= i < a.len() implies len_ok(#[trigger] a[i]) by {}
            assert(eval_rv(fr, rv).0 == Val::Arr(a));
        },
        Rvalue::RefShr(pl) => lemma_read_place_len_ok(fr, pl),
        _ => {},
    }
}

proof fn lemma_exec_stmt_len_ok(fr: Frame, s: Stmt)
    requires frame_len_ok(fr),
    ensures frame_len_ok(exec_stmt(fr, s).0),
{
    match s {
        Stmt::Assign(pl, rv) => {
            lemma_eval_rv_len_ok(fr, rv);
            lemma_assign_len_ok(fr, pl, eval_rv(fr, rv).0);
        },
        Stmt::SetDiscr(pl, k) => if let Some((l, _)) = place_loc(fr, pl) {
            lemma_read_loc_len_ok(fr, l);
            if let Val::Adt(_, vs) = read_loc(fr, l) {
                assert forall|i: int| 0 <= i < vs.len() implies len_ok(#[trigger] vs[i]) by {}
                assert(len_ok(Val::Adt(k as nat, vs)));
            }
            lemma_write_loc_len_ok(fr, l, match read_loc(fr, l) { Val::Adt(_, vs) => Val::Adt(k as nat, vs), v => v });
        },
    }
}

pub proof fn lemma_exec_stmts_len_ok(ss: Seq<Stmt>, k: nat, fr: Frame)
    requires frame_len_ok(fr), k <= ss.len(),
    ensures frame_len_ok(exec_stmts(ss, k, fr).0),
    decreases ss.len() - k,
{
    if k < ss.len() {
        lemma_exec_stmt_len_ok(fr, ss[k as int]);
        lemma_exec_stmts_len_ok(ss, k + 1, exec_stmt(fr, ss[k as int]).0);
    }
}

// ------------------------------------------------------------------ len_ok: intrinsics

/// 8a's overflow rule: `grow` gives `None` past usize::MAX elements.
proof fn lemma_grow_len_ok(fr: Frame, m: Val, xs: Seq<Val>)
    requires frame_len_ok(fr), vals_len_ok(xs),
    ensures grow(fr, m, xs) matches Some(g) ==> frame_len_ok(g),
{
    if let Val::Mut(l) = m {
        lemma_read_loc_len_ok(fr, l);
        if let Val::Arr(s) = read_loc(fr, l) {
            if s.len() + xs.len() <= USIZE_MAX {
                let a = s + xs;
                assert forall|i: int| 0 <= i < a.len() implies len_ok(#[trigger] a[i]) by {
                    if i < s.len() { assert(a[i] == s[i]); } else { assert(a[i] == xs[i - s.len()]); }
                }
                lemma_write_loc_len_ok(fr, l, Val::Arr(a));
            }
        }
    }
}

/// The elements a read-only slice intrinsic returns.
proof fn lemma_intr_read_len_ok(k: Intrinsic, fr: Frame, vs: Seq<Val>)
    requires frame_len_ok(fr), vals_len_ok(vs), k is VecIndex || k is SliceSubrange || k is SliceToVec,
    ensures intr_eff(k, fr, vs) matches Some((g, r, _)) ==> g == fr && len_ok(r),
{
    lemma_nth_len_ok(vs, 0);
    lemma_elems_len_ok(fr, nth(vs, 0));
    let s = elems(fr, nth(vs, 0));
    match k {
        Intrinsic::VecIndex => lemma_nth_len_ok(s, as_int(nth(vs, 1)) as nat),
        Intrinsic::SliceSubrange => {
            let (lo, hi) = (as_int(nth(vs, 1)), as_int(nth(vs, 2)));
            let h = if (hi as nat) < s.len() { hi as int } else { s.len() as int };
            let l = if (lo as int) < h { lo as int } else { h };
            let a = s.subrange(l, h);
            assert forall|i: int| 0 <= i < a.len() implies len_ok(#[trigger] a[i]) by { assert(a[i] == s[i + l]); }
            assert(a.len() <= USIZE_MAX);
            assert(len_ok(Val::Arr(a)));
            assert(len_ok(Val::Shr(Box::new(Val::Arr(a)))));
        },
        _ => {},
    }
}

proof fn lemma_intr_eff_len_ok(k: Intrinsic, fr: Frame, vs: Seq<Val>)
    requires frame_len_ok(fr), vals_len_ok(vs),
    ensures intr_eff(k, fr, vs) matches Some((g, r, _)) ==> frame_len_ok(g) && len_ok(r),
{
    lemma_nth_len_ok(vs, 0);
    lemma_nth_len_ok(vs, 1);
    lemma_nth_len_ok(vs, 2);
    let (a0, a1, a2) = (nth(vs, 0), nth(vs, 1), nth(vs, 2));
    match k {
        Intrinsic::VecNew | Intrinsic::VecWithCapacity => {
            let e = Seq::<Val>::empty();
            assert forall|i: int| 0 <= i < e.len() implies len_ok(#[trigger] e[i]) by {}
        },
        Intrinsic::VecPush => {
            let xs = seq![a1];
            assert forall|i: int| 0 <= i < xs.len() implies len_ok(#[trigger] xs[i]) by {}
            lemma_grow_len_ok(fr, a0, xs);
        },
        Intrinsic::VecExtendFromSlice => {
            lemma_elems_len_ok(fr, a1);
            lemma_grow_len_ok(fr, a0, elems(fr, a1));
        },
        Intrinsic::VecSet => if let Val::Mut(l) = a0 {
            lemma_write_loc_len_ok(fr, Loc { root: l.root, path: l.path.push(PE::Index(as_int(a1) as nat)) }, a2);
        },
        Intrinsic::VecIndex | Intrinsic::SliceSubrange | Intrinsic::SliceToVec => lemma_intr_read_len_ok(k, fr, vs),
        _ => {},
    }
}

pub proof fn lemma_intr_len_ok(k: Intrinsic, fr: Frame, args: Seq<Operand>, dst: Place)
    requires frame_len_ok(fr),
    ensures exec_intr(k, fr, args, dst) matches Some((g, _, _)) ==> frame_len_ok(g),
{
    let vs = op_vals(fr, args);
    lemma_op_vals_len_ok(fr, args);
    lemma_intr_eff_len_ok(k, fr, vs);
    if let Some((f1, r, _)) = intr_eff(k, fr, vs) { lemma_assign_len_ok(f1, dst, r); }
}

// ------------------------------------------------------------------ len_ok: calls and runs

proof fn lemma_call_enter_len_ok(p: Program, g: nat, fr: Frame, args: Seq<Operand>)
    requires frame_len_ok(fr),
    ensures frame_len_ok(call_enter(p, g, fr, args).0),
{
    let vs = op_vals(fr, args);
    lemma_op_vals_len_ok(fr, args);
    let cf = call_enter(p, g, fr, args).0;
    assert forall|i: int| 0 <= i < cf.locals.len() implies len_ok(#[trigger] cf.locals[i]) by {
        if 1 <= i <= vs.len() { assert(len_ok(vs[i - 1])); }
    }
    assert forall|j: int| 0 <= j < cf.slots.len() implies len_ok(#[trigger] cf.slots[j]) by {
        if let Val::Mut(l) = vs[j] { lemma_read_loc_len_ok(fr, l); }
    }
}

proof fn lemma_write_back_len_ok(fr: Frame, slots: Seq<Val>, wb: Seq<Option<Loc>>)
    requires frame_len_ok(fr), vals_len_ok(slots),
    ensures frame_len_ok(write_back(fr, slots, wb)),
    decreases wb.len(),
{
    if wb.len() > 0 {
        lemma_write_back_len_ok(fr, slots, wb.drop_last());
        let j = (wb.len() - 1) as nat;
        lemma_nth_len_ok(slots, j);
        if let Some(l) = wb.last() { lemma_write_loc_len_ok(write_back(fr, slots, wb.drop_last()), l, nth(slots, j)); }
    }
}

proof fn lemma_call_leave_len_ok(fr: Frame, out: Frame, wb: Seq<Option<Loc>>, dst: Place)
    requires frame_len_ok(fr), frame_len_ok(out),
    ensures frame_len_ok(call_leave(fr, out, wb, dst).0),
{
    assert(vals_len_ok(out.slots));
    assert(vals_len_ok(out.locals));
    lemma_write_back_len_ok(fr, out.slots, wb);
    lemma_nth_len_ok(out.locals, 0);
    lemma_assign_len_ok(write_back(fr, out.slots, wb), dst, nth(out.locals, 0));
}

/// A terminating run keeps every length within usize::MAX.
pub proof fn lemma_run_len_ok(p: Program, f: nat, b: nat, fr: Frame, fuel: nat)
    requires frame_len_ok(fr), run_from(p, f, b, fr, fuel) is Some,
    ensures frame_len_ok(run_from(p, f, b, fr, fuel).unwrap().0),
    decreases fuel,
{
    let blk = p.fns@[f as int].blocks@[b as int];
    let f1 = exec_stmts(blk.stmts@, 0, fr).0;
    let fuel1 = (fuel - 1) as nat;
    lemma_exec_stmts_len_ok(blk.stmts@, 0, fr);
    match blk.term {
        Term::Goto(b2) => lemma_run_len_ok(p, f, b2 as nat, f1, fuel1),
        Term::Switch(op, ts, o) =>
            lemma_run_len_ok(p, f, switch_target(ts@, 0, as_int(eval_op(f1, op).0), o) as nat, f1, fuel1),
        Term::Assert(_, _, b2) => lemma_run_len_ok(p, f, b2 as nat, f1, fuel1),
        Term::Call(Callee::Intr(k), args, dst, next) => {
            lemma_intr_len_ok(k, f1, args@, dst);
            lemma_run_len_ok(p, f, next as nat, exec_intr(k, f1, args@, dst).unwrap().0, fuel1);
        },
        Term::Call(Callee::Fn(g), args, dst, next) => {
            let (cf, wb, _) = call_enter(p, g as nat, f1, args@);
            lemma_call_enter_len_ok(p, g as nat, f1, args@);
            lemma_run_len_ok(p, g as nat, 0, cf, fuel1);
            let out = run_from(p, g as nat, 0, cf, fuel1).unwrap().0;
            lemma_call_leave_len_ok(f1, out, wb, dst);
            lemma_run_len_ok(p, f, next as nat, call_leave(f1, out, wb, dst).0, fuel1);
        },
        _ => {},
    }
}

pub proof fn lemma_init_entry_len_ok(p: Program, f: nat, args: Seq<Val>, slots: Seq<Val>)
    requires vals_len_ok(args), vals_len_ok(slots),
    ensures frame_len_ok(init_entry(p, f, args, slots)),
{
    let e = init_entry(p, f, args, slots);
    if f < p.fns@.len() {
        assert forall|i: int| 0 <= i < e.locals.len() implies len_ok(#[trigger] e.locals[i]) by {
            lemma_nth_len_ok(args, (i - 1) as nat);
        }
    }
}

// ------------------------------------------------------------------ plc: runs

pub proof fn lemma_entry_plc(p: Program, ls: Seq<FnLab>, f: nat, args: Seq<Val>, slots: Seq<Val>)
    requires f < p.fns@.len(), entry_plc(p, f, args, slots),
    ensures plc(p, ls, f, init_entry(p, f, args, slots)),
{
    let (b, l) = (p.fns@[f as int], ls[f as int]);
    assert forall|j: int| 0 <= j < b.nargs && !(b.locals@[1 + j] is Mut) implies
        val_rel(lab(l, (1 + j) as nat), #[trigger] args[j], args[j]) && no_mut(args[j])
    by { lemma_shape_refl(args[j]); }
    assert forall|j: int| 0 <= j < b.nargs implies
        val_rel(slot_lab(l, j as nat), #[trigger] slots[j], slots[j]) && no_mut(slots[j])
    by { lemma_shape_refl(slots[j]); }
    lemma_entry_agree(p, ls, f, args, args, slots, slots);
}

pub proof fn lemma_plc_stmts(p: Program, ls: Seq<FnLab>, f: nat, ss: Seq<Stmt>, k: nat, fr: Frame)
    requires
        plc(p, ls, f, fr), k <= ss.len(),
        forall|i: int| 0 <= i < ss.len() ==> ok_stmt(p.fns@[f as int], ls[f as int], #[trigger] ss[i]),
    ensures plc(p, ls, f, exec_stmts(ss, k, fr).0),
    decreases ss.len() - k,
{
    if k < ss.len() {
        lemma_plc_stmt(p, ls, f, fr, ss[k as int]);
        lemma_plc_stmts(p, ls, f, ss, k + 1, exec_stmt(fr, ss[k as int]).0);
    }
}

/// Block `b`'s statements keep `plc`; its terminator is typed.
proof fn lemma_plc_block(p: Program, ls: Seq<FnLab>, f: nat, b: nat, fr: Frame)
    requires ok_prog(p, ls), f < p.fns@.len(), b < p.fns@[f as int].blocks@.len(), plc(p, ls, f, fr),
    ensures
        plc(p, ls, f, exec_stmts(p.fns@[f as int].blocks@[b as int].stmts@, 0, fr).0),
        ok_term(p, ls, f, p.fns@[f as int].blocks@[b as int].term),
        wf_term(p, f, p.fns@[f as int].blocks@[b as int].term),
{
    let blk = p.fns@[f as int].blocks@[b as int];
    assert(ok_body(p, ls, f));
    assert(ok_block(p, ls, f, blk));
    assert(wf_body(p, f));
    assert(wf_block(p, f, blk));
    lemma_plc_stmts(p, ls, f, blk.stmts@, 0, fr);
}

/// The callee entry frame of a typed call satisfies `plc`.
proof fn lemma_plc_enter(p: Program, ls: Seq<FnLab>, f: nat, g: usize, args: Vec<Operand>, dst: Place, next: usize, fr: Frame)
    requires
        ok_prog(p, ls), f < p.fns@.len(), plc(p, ls, f, fr),
        ok_term(p, ls, f, Term::Call(Callee::Fn(g), args, dst, next)),
        wf_term(p, f, Term::Call(Callee::Fn(g), args, dst, next)),
    ensures g < p.fns@.len(), wf_body(p, g as nat), plc(p, ls, g as nat, call_enter(p, g as nat, fr, args@).0),
{
    assert(wf_body(p, g as nat));
    lemma_agree_refl(p, ls, f, fr);
    lemma_call_enter_frames(p, ls, f, g as nat, args@, fr, fr);
}

pub proof fn lemma_plc_reachable(p: Program, ls: Seq<FnLab>, f: nat, b: nat, fr: Frame, fuel: nat)
    requires ok_prog(p, ls), f < p.fns@.len(), plc(p, ls, f, fr), run_from(p, f, b, fr, fuel) is Some,
    ensures plc(p, ls, f, run_from(p, f, b, fr, fuel).unwrap().0),
    decreases fuel,
{
    let blk = p.fns@[f as int].blocks@[b as int];
    let f1 = exec_stmts(blk.stmts@, 0, fr).0;
    let fuel1 = (fuel - 1) as nat;
    lemma_plc_block(p, ls, f, b, fr);
    match blk.term {
        Term::Goto(b2) => lemma_plc_reachable(p, ls, f, b2 as nat, f1, fuel1),
        Term::Switch(op, ts, o) =>
            lemma_plc_reachable(p, ls, f, switch_target(ts@, 0, as_int(eval_op(f1, op).0), o) as nat, f1, fuel1),
        Term::Assert(_, _, b2) => lemma_plc_reachable(p, ls, f, b2 as nat, f1, fuel1),
        Term::Call(Callee::Intr(k), args, dst, next) => {
            lemma_plc_intr(p, ls, f, f1, k, args@, dst);
            lemma_plc_reachable(p, ls, f, next as nat, exec_intr(k, f1, args@, dst).unwrap().0, fuel1);
        },
        Term::Call(Callee::Fn(g), args, dst, next) => {
            let (cf, wb, _) = call_enter(p, g as nat, f1, args@);
            lemma_plc_enter(p, ls, f, g, args, dst, next, f1);
            lemma_plc_reachable(p, ls, g as nat, 0, cf, fuel1);
            let out = run_from(p, g as nat, 0, cf, fuel1).unwrap().0;
            lemma_plc_call_leave(p, ls, f, g as nat, f1, out, wb, dst);
            lemma_plc_reachable(p, ls, f, next as nat, call_leave(f1, out, wb, dst).0, fuel1);
        },
        _ => {},
    }
}

// ------------------------------------------------------------------ the bound

/// The theorem's certificate premise, kept out of the case lemmas' contexts.
#[verifier::opaque]
pub open spec fn all_cert_for(p: Program, certs: Seq<Cert>, sums: Seq<Option<Poly>>) -> bool {
    forall|g: int| 0 <= g < p.fns@.len() && sums[g] is Some ==> cert_for(p, g as nat, certs[g], sums)
}

/// A summary is the certificate's entry potential, and the entry has no facts to discharge.
proof fn lemma_entry_cert(p: Program, certs: Seq<Cert>, sums: Seq<Option<Poly>>, g: nat)
    requires all_cert_for(p, certs, sums), g < p.fns@.len(), sums[g as int] is Some,
    ensures
        certs[g as int].blocks@[0].facts@.len() == 0,
        sums[g as int] == Some(certs[g as int].blocks@[0].pot),
{
    reveal(all_cert_for);
    assert(cert_for(p, g, certs[g as int], sums));
}

/// `cert_sem_ok` at a live block.
proof fn lemma_block_step(p: Program, ls: Seq<FnLab>, certs: Seq<Cert>, sums: Seq<Option<Poly>>, f: nat, b: nat, fr: Frame)
    requires
        all_cert_for(p, certs, sums), ok_prog(p, ls), f < p.fns@.len(), sums[f as int] is Some,
        b < p.fns@[f as int].blocks@.len(),
        plc(p, ls, f, fr), facts_hold(fr, certs[f as int].blocks@[b as int].facts@), frame_len_ok(fr),
    ensures block_step_ok(p, f, b, certs[f as int], sums, fr),
{
    reveal(all_cert_for);
    assert(cert_for(p, f, certs[f as int], sums));
    assert(plc(p, ls, f, fr));
    assert(block_step_ok(p, f, b, certs[f as int], sums, fr));
}

/// What a `Return` block owes.
proof fn lemma_return_pays(p: Program, f: nat, b: nat, c: Cert, sums: Seq<Option<Poly>>, fr: Frame)
    requires
        block_step_ok(p, f, b, c, sums, fr),
        p.fns@[f as int].blocks@[b as int].term is Return,
    ensures poly_val(fr, c.blocks@[b as int].pot) >= p.fns@[f as int].blocks@[b as int].stmts@.len() + 1,
{
    hide(exec_stmts);
    hide(poly_val);
}

/// A `Return` block's steps are its statements and terminator.
proof fn cost_return(p: Program, f: nat, b: nat, c: Cert, sums: Seq<Option<Poly>>, fr: Frame, fuel: nat)
    requires
        block_step_ok(p, f, b, c, sums, fr),
        p.fns@[f as int].blocks@[b as int].term is Return,
        run_from(p, f, b, fr, fuel) is Some,
    ensures run_from(p, f, b, fr, fuel).unwrap().2 <= poly_val(fr, c.blocks@[b as int].pot),
{
    lemma_return_pays(p, f, b, c, sums, fr);
}

/// `Goto`, `Switch` and a passing `Assert`: pay `n1` and continue at `b2` in `f1`.
proof fn cost_jump(p: Program, ls: Seq<FnLab>, certs: Seq<Cert>, sums: Seq<Option<Poly>>, f: nat, b2: nat, f1: Frame, fuel: nat, pot: nat, n1: nat)
    requires
        ok_prog(p, ls), f < p.fns@.len(), certs.len() == p.fns@.len(), sums.len() == p.fns@.len(),
        all_cert_for(p, certs, sums),
        sums[f as int] is Some, plc(p, ls, f, f1), frame_len_ok(f1),
        succ_ok(certs[f as int], b2, pot, n1, f1),
        run_from(p, f, b2, f1, fuel) is Some,
    ensures n1 + run_from(p, f, b2, f1, fuel).unwrap().2 <= pot,
    decreases fuel, 3nat,
{
    cost_from(p, ls, certs, sums, f, b2, f1, fuel);
}

proof fn cost_intr(p: Program, ls: Seq<FnLab>, certs: Seq<Cert>, sums: Seq<Option<Poly>>, f: nat, b: nat, fr: Frame, fuel: nat)
    requires
        ok_prog(p, ls), f < p.fns@.len(), certs.len() == p.fns@.len(), sums.len() == p.fns@.len(),
        all_cert_for(p, certs, sums), sums[f as int] is Some,
        fuel > 0, b < p.fns@[f as int].blocks@.len(),
        block_step_ok(p, f, b, certs[f as int], sums, fr),
        plc(p, ls, f, exec_stmts(p.fns@[f as int].blocks@[b as int].stmts@, 0, fr).0),
        frame_len_ok(exec_stmts(p.fns@[f as int].blocks@[b as int].stmts@, 0, fr).0),
        ok_term(p, ls, f, p.fns@[f as int].blocks@[b as int].term),
        p.fns@[f as int].blocks@[b as int].term matches Term::Call(Callee::Intr(_), _, _, _),
        run_from(p, f, b, fr, fuel) is Some,
    ensures run_from(p, f, b, fr, fuel).unwrap().2 <= poly_val(fr, certs[f as int].blocks@[b as int].pot),
    decreases fuel, 0nat,
{
    let blk = p.fns@[f as int].blocks@[b as int];
    let f1 = exec_stmts(blk.stmts@, 0, fr).0;
    if let Term::Call(Callee::Intr(k), args, dst, next) = blk.term {
        lemma_plc_intr(p, ls, f, f1, k, args@, dst);
        lemma_intr_len_ok(k, f1, args@, dst);
        cost_jump(p, ls, certs, sums, f, next as nat, exec_intr(k, f1, args@, dst).unwrap().0, (fuel - 1) as nat,
            poly_val(fr, certs[f as int].blocks@[b as int].pot),
            blk.stmts@.len() + 1 + exec_intr(k, f1, args@, dst).unwrap().2);
    }
}

/// What a `Call(Fn)` block owes for a callee that left `out` after `n` steps within its summary.
proof fn lemma_call_pays(p: Program, f: nat, b: nat, c: Cert, sums: Seq<Option<Poly>>, fr: Frame, out: Frame, n: nat)
    requires
        block_step_ok(p, f, b, c, sums, fr),
        frame_len_ok(out),
        p.fns@[f as int].blocks@[b as int].term matches Term::Call(Callee::Fn(g), args, _, _) &&
            n <= poly_val(call_enter(p, g as nat, exec_stmts(p.fns@[f as int].blocks@[b as int].stmts@, 0, fr).0, args@).0, sums[g as int].unwrap()),
    ensures
        p.fns@[f as int].blocks@[b as int].term matches Term::Call(Callee::Fn(g), args, dst, next) && ({
            let blk = p.fns@[f as int].blocks@[b as int];
            let f1 = exec_stmts(blk.stmts@, 0, fr).0;
            let wb = call_enter(p, g as nat, f1, args@).1;
            succ_ok(c, next as nat, poly_val(fr, c.blocks@[b as int].pot), blk.stmts@.len() + 1 + n, call_leave(f1, out, wb, dst).0)
        }),
{
    let blk = p.fns@[f as int].blocks@[b as int];
    let f1 = exec_stmts(blk.stmts@, 0, fr).0;
    if let Term::Call(Callee::Fn(g), args, dst, next) = blk.term {
        let wb = call_enter(p, g as nat, f1, args@).1;
        assert(call_out_ok(c, next as nat, poly_val(fr, c.blocks@[b as int].pot), blk.stmts@.len(), f1, wb, dst, out, n));
    }
}

proof fn cost_call(p: Program, ls: Seq<FnLab>, certs: Seq<Cert>, sums: Seq<Option<Poly>>, f: nat, b: nat, fr: Frame, fuel: nat)
    requires
        ok_prog(p, ls), f < p.fns@.len(), certs.len() == p.fns@.len(), sums.len() == p.fns@.len(),
        all_cert_for(p, certs, sums), sums[f as int] is Some,
        fuel > 0, b < p.fns@[f as int].blocks@.len(),
        block_step_ok(p, f, b, certs[f as int], sums, fr),
        plc(p, ls, f, exec_stmts(p.fns@[f as int].blocks@[b as int].stmts@, 0, fr).0),
        frame_len_ok(exec_stmts(p.fns@[f as int].blocks@[b as int].stmts@, 0, fr).0),
        ok_term(p, ls, f, p.fns@[f as int].blocks@[b as int].term),
        wf_term(p, f, p.fns@[f as int].blocks@[b as int].term),
        p.fns@[f as int].blocks@[b as int].term matches Term::Call(Callee::Fn(_), _, _, _),
        run_from(p, f, b, fr, fuel) is Some,
    ensures run_from(p, f, b, fr, fuel).unwrap().2 <= poly_val(fr, certs[f as int].blocks@[b as int].pot),
    decreases fuel, 0nat,
{
    let blk = p.fns@[f as int].blocks@[b as int];
    let f1 = exec_stmts(blk.stmts@, 0, fr).0;
    let fuel1 = (fuel - 1) as nat;
    if let Term::Call(Callee::Fn(g), args, dst, next) = blk.term {
        let (cf, wb, _) = call_enter(p, g as nat, f1, args@);
        lemma_plc_enter(p, ls, f, g, args, dst, next, f1);
        lemma_call_enter_len_ok(p, g as nat, f1, args@);
        assert(sums[g as int] is Some);
        lemma_entry_cert(p, certs, sums, g as nat);
        let r = run_from(p, g as nat, 0, cf, fuel1).unwrap();
        cost_from(p, ls, certs, sums, g as nat, 0, cf, fuel1);
        lemma_plc_reachable(p, ls, g as nat, 0, cf, fuel1);
        lemma_run_len_ok(p, g as nat, 0, cf, fuel1);
        lemma_plc_call_leave(p, ls, f, g as nat, f1, r.0, wb, dst);
        lemma_call_leave_len_ok(f1, r.0, wb, dst);
        lemma_call_pays(p, f, b, certs[f as int], sums, fr, r.0, r.2);
        cost_jump(p, ls, certs, sums, f, next as nat, call_leave(f1, r.0, wb, dst).0, fuel1,
            poly_val(fr, certs[f as int].blocks@[b as int].pot), blk.stmts@.len() + 1 + r.2);
    }
}

/// One case lemma per terminator, from the facts `cost_from` establishes for the block.
proof fn cost_block(p: Program, ls: Seq<FnLab>, certs: Seq<Cert>, sums: Seq<Option<Poly>>, f: nat, b: nat, fr: Frame, fuel: nat)
    requires
        ok_prog(p, ls), f < p.fns@.len(), certs.len() == p.fns@.len(), sums.len() == p.fns@.len(),
        all_cert_for(p, certs, sums), sums[f as int] is Some,
        b < p.fns@[f as int].blocks@.len(),
        block_step_ok(p, f, b, certs[f as int], sums, fr),
        plc(p, ls, f, exec_stmts(p.fns@[f as int].blocks@[b as int].stmts@, 0, fr).0),
        frame_len_ok(exec_stmts(p.fns@[f as int].blocks@[b as int].stmts@, 0, fr).0),
        ok_term(p, ls, f, p.fns@[f as int].blocks@[b as int].term),
        wf_term(p, f, p.fns@[f as int].blocks@[b as int].term),
        run_from(p, f, b, fr, fuel) is Some,
    ensures run_from(p, f, b, fr, fuel).unwrap().2 <= poly_val(fr, certs[f as int].blocks@[b as int].pot),
    decreases fuel, 1nat,
{
    let blk = p.fns@[f as int].blocks@[b as int];
    let f1 = exec_stmts(blk.stmts@, 0, fr).0;
    let fuel1 = (fuel - 1) as nat;
    let pot = poly_val(fr, certs[f as int].blocks@[b as int].pot);
    let n1 = blk.stmts@.len() + 1;
    match blk.term {
        Term::Goto(b2) => cost_jump(p, ls, certs, sums, f, b2 as nat, f1, fuel1, pot, n1),
        Term::Switch(op, ts, o) =>
            cost_jump(p, ls, certs, sums, f, switch_target(ts@, 0, as_int(eval_op(f1, op).0), o) as nat, f1, fuel1, pot, n1),
        Term::Assert(_, _, b2) => cost_jump(p, ls, certs, sums, f, b2 as nat, f1, fuel1, pot, n1),
        Term::Call(Callee::Intr(_), _, _, _) => cost_intr(p, ls, certs, sums, f, b, fr, fuel),
        Term::Call(Callee::Fn(_), _, _, _) => cost_call(p, ls, certs, sums, f, b, fr, fuel),
        Term::Return => cost_return(p, f, b, certs[f as int], sums, fr, fuel),
        Term::Abort => {},
    }
}

/// A run from block `b` takes at most `b`'s potential.
pub proof fn cost_from(p: Program, ls: Seq<FnLab>, certs: Seq<Cert>, sums: Seq<Option<Poly>>, f: nat, b: nat, fr: Frame, fuel: nat)
    requires
        ok_prog(p, ls), f < p.fns@.len(), certs.len() == p.fns@.len(), sums.len() == p.fns@.len(),
        all_cert_for(p, certs, sums),
        sums[f as int] is Some,
        plc(p, ls, f, fr),
        facts_hold(fr, certs[f as int].blocks@[b as int].facts@),
        frame_len_ok(fr),
        run_from(p, f, b, fr, fuel) is Some,
    ensures run_from(p, f, b, fr, fuel).unwrap().2 <= poly_val(fr, certs[f as int].blocks@[b as int].pot),
    decreases fuel, 2nat,
{
    hide(run_from);
    hide(exec_stmts);
    hide(ok_prog);
    hide(block_step_ok);
    hide(poly_val);
    assert(b < p.fns@[f as int].blocks@.len()) by { reveal(run_from); }
    lemma_block_step(p, ls, certs, sums, f, b, fr);
    lemma_plc_block(p, ls, f, b, fr);
    lemma_exec_stmts_len_ok(p.fns@[f as int].blocks@[b as int].stmts@, 0, fr);
    cost_block(p, ls, certs, sums, f, b, fr, fuel);
}

/// A terminating run takes at most `summary(inputs)` steps.
pub proof fn theorem_cost(p: Program, ls: Seq<FnLab>, certs: Seq<Cert>, sums: Seq<Option<Poly>>, f: nat,
                          args: Seq<Val>, slots: Seq<Val>, fuel: nat, b: Poly)
    requires
        ok_prog(p, ls), f < p.fns@.len(), certs.len() == p.fns@.len(), sums.len() == p.fns@.len(),
        sums[f as int] == Some(b),
        forall|g: int| 0 <= g < p.fns@.len() && sums[g] is Some ==> cert_for(p, g as nat, certs[g], sums),
        entry_plc(p, f, args, slots), vals_len_ok(args), vals_len_ok(slots),
        run_fn(p, f, init_entry(p, f, args, slots), fuel) is Some,
    ensures
        run_fn(p, f, init_entry(p, f, args, slots), fuel).unwrap().2
            <= poly_val(init_entry(p, f, args, slots), b),
{
    let e = init_entry(p, f, args, slots);
    assert(all_cert_for(p, certs, sums)) by { reveal(all_cert_for); }
    lemma_entry_cert(p, certs, sums, f);
    lemma_entry_plc(p, ls, f, args, slots);
    lemma_init_entry_len_ok(p, f, args, slots);
    cost_from(p, ls, certs, sums, f, 0, e, fuel);
}

} // verus!
