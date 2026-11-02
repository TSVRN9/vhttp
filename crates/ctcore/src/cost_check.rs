//! The verified validator for step-bound certificates (Phase 8b): `check_cert`'s `true` is the
//! frozen `cert_for`. It runs the exec twins of `cost_sym`'s abstract effect, pulls each
//! successor's potential and each charge back to block-start atoms, and compares monomials.
#[allow(unused_imports)]
use crate::check::is_mut_op;
#[allow(unused_imports)]
use crate::cost::*;
#[allow(unused_imports)]
use crate::cost_sym::*;
#[allow(unused_imports)]
use crate::ct::*;
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

// ------------------------------------------------------------------ hand copies

pub fn int_ty_copy(t: &IntTy) -> (r: IntTy)
    ensures r == *t,
{
    match t {
        IntTy::U8 => IntTy::U8, IntTy::U16 => IntTy::U16, IntTy::U32 => IntTy::U32, IntTy::U64 => IntTy::U64,
        IntTy::U128 => IntTy::U128, IntTy::Usize => IntTy::Usize, IntTy::I8 => IntTy::I8, IntTy::I16 => IntTy::I16,
        IntTy::I32 => IntTy::I32, IntTy::I64 => IntTy::I64, IntTy::I128 => IntTy::I128, IntTy::Isize => IntTy::Isize,
        IntTy::Bool => IntTy::Bool,
    }
}

pub fn binop_clone(o: &BinOp) -> (s: BinOp)
    ensures s == *o,
{
    match o {
        BinOp::Add => BinOp::Add, BinOp::Sub => BinOp::Sub, BinOp::Mul => BinOp::Mul, BinOp::Div => BinOp::Div,
        BinOp::Rem => BinOp::Rem, BinOp::BitXor => BinOp::BitXor, BinOp::BitAnd => BinOp::BitAnd, BinOp::BitOr => BinOp::BitOr,
        BinOp::Shl => BinOp::Shl, BinOp::Shr => BinOp::Shr, BinOp::Eq => BinOp::Eq, BinOp::Ne => BinOp::Ne,
        BinOp::Lt => BinOp::Lt, BinOp::Le => BinOp::Le, BinOp::Gt => BinOp::Gt, BinOp::Ge => BinOp::Ge,
    }
}

pub fn atom_copy(a: &Atom) -> (r: Atom)
    ensures r == *a,
    decreases a,
{
    match a {
        Atom::Const(c) => Atom::Const(*c),
        Atom::Val(x, t) => Atom::Val(*x, int_ty_copy(t)),
        Atom::Len(x) => Atom::Len(*x),
        Atom::Gap(x, y) => Atom::Gap(Box::new(atom_copy(x)), Box::new(atom_copy(y))),
    }
}

pub fn fact_copy(f: &Fact) -> (r: Fact)
    ensures r == *f,
{
    match f {
        Fact::Le(a, b) => Fact::Le(atom_copy(a), atom_copy(b)),
        Fact::Lt(a, b) => Fact::Lt(atom_copy(a), atom_copy(b)),
    }
}

pub fn rel_clone(r: &Rel) -> (s: Rel)
    ensures s == *r,
{
    match r {
        Rel::Same => Rel::Same,
        Rel::ValEq(a, k) => Rel::ValEq(atom_copy(a), *k),
        Rel::ValLe(a) => Rel::ValLe(atom_copy(a)),
        Rel::LenEq(a) => Rel::LenEq(atom_copy(a)),
        Rel::LenLe(a) => Rel::LenLe(atom_copy(a)),
        Rel::Unknown => Rel::Unknown,
    }
}

fn atoms_copy(a: &Vec<Atom>) -> (r: Vec<Atom>)
    ensures r@ == a@,
{
    let mut r: Vec<Atom> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant i <= a@.len(), r@ =~= a@.take(i as int),
        decreases a.len() - i,
    {
        r.push(atom_copy(&a[i]));
        i += 1;
        assert(r@ =~= a@.take(i as int));
    }
    assert(a@.take(a@.len() as int) =~= a@);
    r
}

/// The views agree: `Vec` has no extensional `==` in this toolchain, and every reader goes through `@`.
pub open spec fn mono_same(a: Mono, b: Mono) -> bool { a.coef == b.coef && a.atoms@ == b.atoms@ }

pub open spec fn monos_same(a: Seq<Mono>, b: Seq<Mono>) -> bool {
    a.len() == b.len() && forall|i: int| 0 <= i < a.len() ==> #[trigger] mono_same(a[i], b[i])
}

/// `*m`, up to `Vec` identity (`mono_same`).
pub fn mono_copy(m: &Mono) -> (r: Mono)
    ensures mono_same(r, *m),
{
    Mono { coef: m.coef, atoms: atoms_copy(&m.atoms) }
}

/// `*p`, up to `Vec` identity (`monos_same`).
pub fn poly_copy(p: &Poly) -> (r: Poly)
    ensures monos_same(r.monos@, p.monos@),
{
    let mut out: Vec<Mono> = Vec::new();
    let mut i: usize = 0;
    while i < p.monos.len()
        invariant i <= p.monos@.len(), out@.len() == i, forall|j: int| 0 <= j < i ==> #[trigger] mono_same(out@[j], p.monos@[j]),
        decreases p.monos.len() - i,
    {
        out.push(mono_copy(&p.monos[i]));
        i += 1;
    }
    Poly { monos: out }
}

pub fn int_ty_eq(a: &IntTy, b: &IntTy) -> (r: bool)
    ensures r == (*a == *b),
{
    match (a, b) {
        (IntTy::U8, IntTy::U8) | (IntTy::U16, IntTy::U16) | (IntTy::U32, IntTy::U32) | (IntTy::U64, IntTy::U64)
        | (IntTy::U128, IntTy::U128) | (IntTy::Usize, IntTy::Usize) | (IntTy::I8, IntTy::I8) | (IntTy::I16, IntTy::I16)
        | (IntTy::I32, IntTy::I32) | (IntTy::I64, IntTy::I64) | (IntTy::I128, IntTy::I128) | (IntTy::Isize, IntTy::Isize)
        | (IntTy::Bool, IntTy::Bool) => true,
        _ => false,
    }
}

pub fn atom_eq(a: &Atom, b: &Atom) -> (r: bool)
    ensures r == (*a == *b),
    decreases a,
{
    match (a, b) {
        (Atom::Const(x), Atom::Const(y)) => *x == *y,
        (Atom::Val(x, s), Atom::Val(y, t)) => *x == *y && int_ty_eq(s, t),
        (Atom::Len(x), Atom::Len(y)) => *x == *y,
        (Atom::Gap(x1, y1), Atom::Gap(x2, y2)) => atom_eq(x1, x2) && atom_eq(y1, y2),
        _ => false,
    }
}

pub fn atoms_eq(a: &Vec<Atom>, b: &Vec<Atom>) -> (r: bool)
    ensures r == (a@ == b@),
{
    if a.len() != b.len() { return false; }
    let mut i: usize = 0;
    while i < a.len()
        invariant i <= a@.len(), a@.len() == b@.len(), forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a.len() - i,
    {
        if !atom_eq(&a[i], &b[i]) {
            assert(a@[i as int] != b@[i as int]);
            return false;
        }
        i += 1;
    }
    assert(a@ =~= b@);
    true
}

fn fact_eq(a: &Fact, b: &Fact) -> (r: bool)
    ensures r == (*a == *b),
{
    match (a, b) {
        (Fact::Le(x1, y1), Fact::Le(x2, y2)) => atom_eq(x1, x2) && atom_eq(y1, y2),
        (Fact::Lt(x1, y1), Fact::Lt(x2, y2)) => atom_eq(x1, x2) && atom_eq(y1, y2),
        _ => false,
    }
}

// ------------------------------------------------------------------ operands and per-pattern rules

fn ex_op_local(op: &Operand) -> (r: Option<usize>)
    ensures r == op_local(*op),
{
    match op {
        Operand::Copy(q) => if q.proj.len() == 0 { Some(q.local) } else { None },
        _ => None,
    }
}

fn ex_op_one(op: &Operand) -> (r: bool)
    ensures r == op_one(*op),
{
    match op { Operand::Const(_, n) => *n == 1, _ => false }
}

fn ex_arg_local(args: &Vec<Operand>, i: usize) -> (r: Option<usize>)
    ensures r == arg_local(args@, i as int),
{
    if i < args.len() { ex_op_local(&args[i]) } else { None }
}

fn ex_rel_at(rels: &Vec<Rel>, y: usize) -> (r: Rel)
    ensures r == rel_at(rels@, y),
{
    if y < rels.len() { rel_clone(&rels[y]) } else { Rel::Unknown }
}

fn ex_rel_copy(rels: &Vec<Rel>, y: usize, ty: &IntTy) -> (r: Rel)
    ensures r == rel_copy(rels@, y, *ty),
{
    match ex_rel_at(rels, y) {
        Rel::Same => Rel::ValEq(Atom::Val(y, int_ty_copy(ty)), 0),
        Rel::ValEq(Atom::Val(z, t), k) => if int_ty_eq(&t, ty) { Rel::ValEq(Atom::Val(z, t), k) } else { Rel::Unknown },
        Rel::ValEq(Atom::Const(c), k) => if k == 0 { Rel::ValEq(Atom::Const(c), 0) } else { Rel::Unknown },
        Rel::ValLe(a) => Rel::ValLe(a),
        _ => Rel::Unknown,
    }
}

fn ex_rel_copy_int(b: &Body, rels: &Vec<Rel>, x: usize, y: usize) -> (r: Rel)
    ensures r == rel_copy_int(*b, rels@, x, y),
{
    if x < b.locals.len() && y < b.locals.len() {
        match &b.locals[y] {
            Ty::Int(ty) => {
                let same = match &b.locals[x] { Ty::Int(t) => int_ty_eq(t, ty), _ => false };
                if same { ex_rel_copy(rels, y, ty) } else { Rel::Unknown }
            },
            _ => Rel::Unknown,
        }
    } else {
        Rel::Unknown
    }
}

proof fn lemma_pow2_widths()
    ensures
        pow2(1) == 2, pow2(8) == 0x100, pow2(16) == 0x1_0000, pow2(32) == 0x1_0000_0000,
        pow2(64) == 0x1_0000_0000_0000_0000,
        pow2(128) > u128::MAX,
{
    lemma2_to64();
    lemma2_to64_rest();
    lemma_pow2_adds(64, 64);
}

pub fn exec_uval(ty: &IntTy, n: u128) -> (r: u128)
    ensures r as int == uval(*ty, n),
{
    proof {
        lemma_pow2_widths();
        lemma_small_mod(n as nat, pow2(128));
    }
    match ty {
        IntTy::U8 | IntTy::I8 => n % 0x100,
        IntTy::U16 | IntTy::I16 => n % 0x1_0000,
        IntTy::U32 | IntTy::I32 => n % 0x1_0000_0000,
        IntTy::U64 | IntTy::I64 | IntTy::Usize | IntTy::Isize => n % 0x1_0000_0000_0000_0000,
        IntTy::U128 | IntTy::I128 => n,
        IntTy::Bool => n % 2,
    }
}

fn ex_rel_const(ty: &IntTy, n: u128) -> (r: Rel)
    ensures r == rel_const(*ty, n),
{
    let u = exec_uval(ty, n);
    if u == n && u <= u64::MAX as u128 { Rel::ValEq(Atom::Const(u as u64), 0) } else { Rel::Unknown }
}

fn ex_signed(ty: &IntTy) -> (r: bool)
    ensures r == signed(*ty),
{
    match ty {
        IntTy::I8 | IntTy::I16 | IntTy::I32 | IntTy::I64 | IntTy::I128 | IntTy::Isize => true,
        _ => false,
    }
}

fn ex_inc_bound_ok(a: &Atom, ty: &IntTy) -> (r: bool)
    ensures r == inc_bound_ok(*a, *ty),
{
    match a {
        Atom::Const(c) => match ty {
            IntTy::U8 => *c <= 0xff,
            IntTy::U16 => *c <= 0xffff,
            IntTy::U32 => *c <= 0xffff_ffff,
            IntTy::Bool => *c <= 1,
            _ => true,
        },
        Atom::Val(_, t) => int_ty_eq(t, ty),
        Atom::Len(_) => match ty { IntTy::Usize => true, _ => false },
        Atom::Gap(_, _) => false,
    }
}

fn ex_inc_fact(fa: &Fact, x: usize, ty: &IntTy) -> (r: bool)
    ensures r == inc_fact(*fa, x, *ty),
{
    match fa {
        Fact::Lt(Atom::Val(y, t), a) => *y == x && int_ty_eq(t, ty) && ex_inc_bound_ok(a, ty),
        _ => false,
    }
}

#[verifier::loop_isolation(false)]
fn ex_rel_inc(rels: &Vec<Rel>, facts: &Vec<Fact>, x: usize, ty: &IntTy) -> (r: Rel)
    ensures r == rel_inc(rels@, facts@, x, *ty),
{
    if ex_signed(ty) { return Rel::Unknown; }
    let same = match ex_rel_at(rels, x) { Rel::Same => true, _ => false };
    if !same { return Rel::Unknown; }
    let mut i: usize = 0;
    while i < facts.len()
        invariant i <= facts@.len(), forall|j: int| 0 <= j < i ==> !inc_fact(#[trigger] facts@[j], x, *ty),
        decreases facts.len() - i,
    {
        if ex_inc_fact(&facts[i], x, ty) {
            assert(inc_fact(facts@[i as int], x, *ty));
            assert(exists|i: int| 0 <= i < facts@.len() && inc_fact(#[trigger] facts@[i], x, *ty));
            return Rel::ValEq(Atom::Val(x, int_ty_copy(ty)), 1);
        }
        i += 1;
    }
    Rel::Unknown
}

fn ex_len_atom(rels: &Vec<Rel>, y: usize) -> (r: Option<Atom>)
    ensures r == len_atom(rels@, y),
{
    match ex_rel_at(rels, y) {
        Rel::Same => Some(Atom::Len(y)),
        Rel::LenEq(a) => Some(a),
        Rel::LenLe(a) => Some(a),
        _ => None,
    }
}

fn ex_rel_len(rels: &Vec<Rel>, y: usize) -> (r: Rel)
    ensures r == rel_len(rels@, y),
{
    match ex_len_atom(rels, y) { Some(a) => Rel::ValLe(a), None => Rel::Unknown }
}

fn ex_rel_le(rels: &Vec<Rel>, y: usize) -> (r: Rel)
    ensures r == rel_le(rels@, y),
{
    match ex_len_atom(rels, y) { Some(a) => Rel::LenLe(a), None => Rel::Unknown }
}

fn ex_rel_shr(rels: &Vec<Rel>, y: usize) -> (r: Rel)
    ensures r == rel_shr(rels@, y),
{
    match ex_rel_at(rels, y) {
        Rel::Same => Rel::LenEq(Atom::Len(y)),
        Rel::LenEq(a) => Rel::LenEq(a),
        Rel::LenLe(a) => Rel::LenLe(a),
        _ => Rel::Unknown,
    }
}

fn ex_rule_use_copy(b: &Body, rels: &Vec<Rel>, x: usize, q: &Place) -> (r: Rel)
    ensures r == rule_stmt(*b, rels@, seq![], x, Rvalue::Use(Operand::Copy(*q))),
{
    if q.proj.len() == 0 {
        ex_rel_copy_int(b, rels, x, q.local)
    } else if q.proj.len() == 1 {
        match &q.proj[0] { Proj::Deref => ex_rel_le(rels, q.local), _ => Rel::Unknown }
    } else {
        Rel::Unknown
    }
}

fn ex_rule_stmt(b: &Body, rels: &Vec<Rel>, facts: &Vec<Fact>, x: usize, rv: &Rvalue) -> (r: Rel)
    ensures r == rule_stmt(*b, rels@, facts@, x, *rv),
{
    match rv {
        Rvalue::Use(Operand::Copy(q)) => ex_rule_use_copy(b, rels, x, q),
        Rvalue::Use(Operand::Const(ty, n)) => ex_rel_const(ty, *n),
        Rvalue::Bin(op, ty, a, c) => {
            let add = match op { BinOp::Add => true, _ => false };
            if add && ex_op_one(c) && match ex_op_local(a) { Some(y) => y == x, None => false } {
                ex_rel_inc(rels, facts, x, ty)
            } else {
                Rel::Unknown
            }
        },
        Rvalue::Len(q) => if q.proj.len() == 0 { ex_rel_len(rels, q.local) } else { Rel::Unknown },
        Rvalue::RefShr(q) => if q.proj.len() == 0 { ex_rel_shr(rels, q.local) } else { Rel::Unknown },
        _ => Rel::Unknown,
    }
}

fn ex_rule_intr(rels: &Vec<Rel>, facts: &Vec<Fact>, x: usize, k: &Intrinsic, args: &Vec<Operand>) -> (r: Rel)
    ensures r == rule_intr(rels@, facts@, x, *k, args@),
{
    match ex_arg_local(args, 0) {
        None => Rel::Unknown,
        Some(y) => match k {
            Intrinsic::VecLen => ex_rel_len(rels, y),
            Intrinsic::VecAsSlice => ex_rel_shr(rels, y),
            Intrinsic::SliceSubrange | Intrinsic::SliceToVec => ex_rel_le(rels, y),
            Intrinsic::Wrapping(BinOp::Add, ty) =>
                if y == x && args.len() > 1 && ex_op_one(&args[1]) { ex_rel_inc(rels, facts, x, ty) } else { Rel::Unknown },
            _ => Rel::Unknown,
        },
    }
}

// ------------------------------------------------------------------ writes

fn ex_mut_local(b: &Body, x: usize) -> (r: bool)
    ensures r == mut_local(*b, x as int),
{
    x < b.locals.len() && match &b.locals[x] { Ty::Mut(_) => true, _ => false }
}

fn ex_writer_place(b: &Body, pl: &Place) -> (r: bool)
    ensures r == writer_place(*b, *pl),
{
    ex_mut_local(b, pl.local) && pl.proj.len() > 0 && match &pl.proj[0] { Proj::Deref => true, _ => false }
}

fn ex_filled(n: usize, same: bool) -> (r: Vec<Rel>)
    ensures r@ == Seq::new(n as nat, |i: int| if same { Rel::Same } else { Rel::Unknown }),
{
    let mut r: Vec<Rel> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n, r@ =~= Seq::new(i as nat, |j: int| if same { Rel::Same } else { Rel::Unknown }),
        decreases n - i,
    {
        r.push(if same { Rel::Same } else { Rel::Unknown });
        i += 1;
    }
    r
}

fn ex_all_unknown(n: usize) -> (r: Vec<Rel>)
    ensures r@ == all_unknown(n as nat),
{
    let r = ex_filled(n, false);
    assert(r@ =~= all_unknown(n as nat));
    r
}

fn ex_write_root(b: &Body, rels: &Vec<Rel>, r: usize, rnew: &Rel) -> (out: Vec<Rel>)
    ensures out@ == write_root(*b, rels@, r, *rnew),
{
    let rmut = ex_mut_local(b, r);
    let mut out: Vec<Rel> = Vec::new();
    let mut i: usize = 0;
    let ghost w = write_root(*b, rels@, r, *rnew);
    while i < rels.len()
        invariant
            i <= rels@.len(), rmut == mut_local(*b, r as int), w == write_root(*b, rels@, r, *rnew),
            w.len() == rels@.len(), out@.len() == i, forall|j: int| 0 <= j < i ==> out@[j] == #[trigger] w[j],
        decreases rels.len() - i,
    {
        let x = if i == r {
            rel_clone(rnew)
        } else if !rmut && ex_mut_local(b, i) {
            Rel::Unknown
        } else {
            rel_clone(&rels[i])
        };
        out.push(x);
        i += 1;
    }
    assert(out@ =~= w);
    out
}

// ------------------------------------------------------------------ comparisons

fn ex_is_cmp(op: &BinOp) -> (r: bool)
    ensures r == is_cmp(*op),
{
    match op { BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => true, _ => false }
}

fn ex_cmp_atom(rels: &Vec<Rel>, op: &Operand, ty: &IntTy) -> (r: Option<Atom>)
    ensures r == cmp_atom(rels@, *op, *ty),
{
    match op {
        Operand::Copy(q) => if q.proj.len() == 0 {
            match ex_rel_at(rels, q.local) {
                Rel::ValEq(Atom::Val(y, t), k) => {
                    let keep = int_ty_eq(&t, ty) && k == 0 && match ex_rel_at(rels, y) { Rel::Same => true, _ => false };
                    if keep { Some(Atom::Val(y, int_ty_copy(ty))) } else { Some(Atom::Val(q.local, int_ty_copy(ty))) }
                },
                _ => Some(Atom::Val(q.local, int_ty_copy(ty))),
            }
        } else {
            None
        },
        Operand::Const(_, n) => {
            let u = exec_uval(ty, *n);
            if u <= u64::MAX as u128 { Some(Atom::Const(u as u64)) } else { None }
        },
        _ => None,
    }
}

fn ex_atom_reads(a: &Atom, r: usize) -> (b: bool)
    ensures b == atom_reads(*a, r),
{
    match a { Atom::Const(_) => false, Atom::Val(y, _) => *y == r, _ => true }
}

fn ex_cmp_keeps(m: &Cmp, r: usize) -> (b: bool)
    ensures b == cmp_keeps(*m, r),
{
    m.c != r && !ex_atom_reads(&m.a, r) && !ex_atom_reads(&m.b, r)
}

fn ex_new_cmp(rels: &Vec<Rel>, x: usize, rv: &Rvalue) -> (r: Option<Cmp>)
    ensures r == new_cmp(rels@, x, *rv),
{
    match rv {
        Rvalue::Bin(op, ty, a, c) => if ex_is_cmp(op) && !ex_signed(ty) {
            match (ex_cmp_atom(rels, a, ty), ex_cmp_atom(rels, c, ty)) {
                (Some(aa), Some(cc)) =>
                    if !ex_atom_reads(&aa, x) && !ex_atom_reads(&cc, x) { Some(Cmp { c: x, op: binop_clone(op), a: aa, b: cc }) } else { None },
                _ => None,
            }
        } else {
            None
        },
        _ => None,
    }
}

fn cmp_copy(m: &Cmp) -> (r: Cmp)
    ensures r == *m,
{
    Cmp { c: m.c, op: binop_clone(&m.op), a: atom_copy(&m.a), b: atom_copy(&m.b) }
}

// ------------------------------------------------------------------ the fold over statements

pub open spec fn st_view(rels: Vec<Rel>, cmp: Option<Cmp>) -> SymSt { SymSt { rels: rels@, cmp } }

fn ex_st_write(b: &Body, rels: &Vec<Rel>, cmp: &Option<Cmp>, pl: &Place, rnew: &Rel) -> (r: (Vec<Rel>, Option<Cmp>))
    ensures st_view(r.0, r.1) == st_write(*b, st_view(*rels, *cmp), *pl, *rnew),
{
    if ex_writer_place(b, pl) {
        return (ex_all_unknown(rels.len()), None);
    }
    let r = if pl.proj.len() == 0 { rel_clone(rnew) } else { Rel::Unknown };
    let out = ex_write_root(b, rels, pl.local, &r);
    let c = match cmp {
        Some(m) => if ex_cmp_keeps(m, pl.local) { Some(cmp_copy(m)) } else { None },
        None => None,
    };
    (out, c)
}

fn ex_sym_stmt(b: &Body, rels: &Vec<Rel>, cmp: &Option<Cmp>, s: &Stmt, facts: &Vec<Fact>) -> (r: (Vec<Rel>, Option<Cmp>))
    ensures st_view(r.0, r.1) == sym_stmt(*b, st_view(*rels, *cmp), *s, facts@),
{
    match s {
        Stmt::Assign(pl, rv) => {
            let rnew = ex_rule_stmt(b, rels, facts, pl.local, rv);
            let st1 = ex_st_write(b, rels, cmp, pl, &rnew);
            if pl.proj.len() == 0 {
                match ex_new_cmp(rels, pl.local, rv) {
                    Some(m) => return (st1.0, Some(m)),
                    None => {},
                }
            }
            st1
        },
        Stmt::SetDiscr(pl, _) => ex_st_write(b, rels, cmp, pl, &Rel::Unknown),
    }
}

fn ex_sym_state(b: &Body, stmts: &Vec<Stmt>, facts: &Vec<Fact>) -> (r: (Vec<Rel>, Option<Cmp>))
    ensures st_view(r.0, r.1) == sym_state(*b, stmts@, facts@),
{
    let mut rels = ex_filled(b.locals.len(), true);
    let mut cmp: Option<Cmp> = None;
    let ghost st0 = SymSt { rels: Seq::new(b.locals@.len(), |i: int| Rel::Same), cmp: None };
    proof { assert(rels@ =~= st0.rels); }
    let mut k: usize = 0;
    while k < stmts.len()
        invariant
            k <= stmts@.len(),
            sym_from(*b, stmts@, k as nat, st_view(rels, cmp), facts@) == sym_from(*b, stmts@, 0, st0, facts@),
            st0 == (SymSt { rels: Seq::new(b.locals@.len(), |i: int| Rel::Same), cmp: None }),
        decreases stmts.len() - k,
    {
        let next = ex_sym_stmt(b, &rels, &cmp, &stmts[k], facts);
        proof {
            assert(sym_from(*b, stmts@, k as nat, st_view(rels, cmp), facts@)
                == sym_from(*b, stmts@, (k + 1) as nat, st_view(next.0, next.1), facts@));
        }
        rels = next.0;
        cmp = next.1;
        k += 1;
    }
    (rels, cmp)
}

/// The exec twin of `sym_stmts`: the rels from the block's start to the end of its statements.
pub fn exec_sym_stmts(b: &Body, stmts: &Vec<Stmt>, facts: &Vec<Fact>) -> (r: Eff)
    ensures eff_view(r) == sym_stmts(*b, stmts@, facts@),
{
    let st = ex_sym_state(b, stmts, facts);
    let r = Eff { rel: st.0, edge: Vec::new() };
    proof { assert(eff_view(r).edge =~= seq![]); }
    r
}

// ------------------------------------------------------------------ the terminator

fn ex_intr_writer(b: &Body, k: &Intrinsic, args: &Vec<Operand>) -> (r: bool)
    ensures r == intr_writer(*b, *k, args@),
{
    match k {
        Intrinsic::VecPush | Intrinsic::VecSet | Intrinsic::VecExtendFromSlice => args.len() > 0 && is_mut_op(b, &args[0]),
        _ => false,
    }
}

fn ex_call_writer(b: &Body, args: &Vec<Operand>) -> (r: bool)
    ensures r == call_writer(*b, args@),
{
    let mut i: usize = 0;
    while i < args.len()
        invariant i <= args@.len(), forall|j: int| 0 <= j < i ==> !mut_op(*b, #[trigger] args@[j]),
        decreases args.len() - i,
    {
        if is_mut_op(b, &args[i]) {
            assert(mut_op(*b, args@[i as int]));
            return true;
        }
        i += 1;
    }
    false
}

fn ex_term_rels(b: &Body, rels: &Vec<Rel>, t: &Term, facts: &Vec<Fact>) -> (r: Vec<Rel>)
    ensures r@ == term_rels(*b, rels@, *t, facts@),
{
    match t {
        Term::Call(Callee::Intr(k), args, dst, _) =>
            if ex_intr_writer(b, k, args) || ex_writer_place(b, dst) {
                ex_all_unknown(rels.len())
            } else {
                let rnew = if dst.proj.len() == 0 { ex_rule_intr(rels, facts, dst.local, k, args) } else { Rel::Unknown };
                ex_write_root(b, rels, dst.local, &rnew)
            },
        Term::Call(Callee::Fn(_), args, dst, _) =>
            if ex_call_writer(b, args) || ex_writer_place(b, dst) {
                ex_all_unknown(rels.len())
            } else {
                ex_write_root(b, rels, dst.local, &Rel::Unknown)
            },
        _ => ex_rels_copy(rels),
    }
}

fn ex_rels_copy(rels: &Vec<Rel>) -> (r: Vec<Rel>)
    ensures r@ == rels@,
{
    let mut r: Vec<Rel> = Vec::new();
    let mut i: usize = 0;
    while i < rels.len()
        invariant i <= rels@.len(), r@ =~= rels@.take(i as int),
        decreases rels.len() - i,
    {
        r.push(rel_clone(&rels[i]));
        i += 1;
        assert(r@ =~= rels@.take(i as int));
    }
    assert(rels@.take(rels@.len() as int) =~= rels@);
    r
}

fn ex_atom_same(rels: &Vec<Rel>, a: &Atom) -> (r: bool)
    ensures r == atom_same(rels@, *a),
    decreases a,
{
    match a {
        Atom::Const(_) => true,
        Atom::Val(x, _) => match ex_rel_at(rels, *x) { Rel::Same => true, _ => false },
        Atom::Len(x) => match ex_rel_at(rels, *x) { Rel::Same => true, _ => false },
        Atom::Gap(x, y) => ex_atom_same(rels, x) && ex_atom_same(rels, y),
    }
}

fn ex_fact_same(rels: &Vec<Rel>, fa: &Fact) -> (r: bool)
    ensures r == fact_same(rels@, *fa),
{
    match fa {
        Fact::Le(x, y) => ex_atom_same(rels, x) && ex_atom_same(rels, y),
        Fact::Lt(x, y) => ex_atom_same(rels, x) && ex_atom_same(rels, y),
    }
}

fn ex_carry(rels: &Vec<Rel>, facts: &Vec<Fact>) -> (r: Vec<Fact>)
    ensures r@ == carry(rels@, facts@),
{
    let mut acc: Vec<Fact> = Vec::new();
    let mut k: usize = 0;
    proof { assert(acc@ =~= seq![]); }
    while k < facts.len()
        invariant
            k <= facts@.len(),
            carry_from(rels@, facts@, k as nat, acc@) == carry_from(rels@, facts@, 0, seq![]),
        decreases facts.len() - k,
    {
        let ghost old_acc = acc@;
        let same = ex_fact_same(rels, &facts[k]);
        if same { acc.push(fact_copy(&facts[k])); }
        proof {
            assert(carry_from(rels@, facts@, k as nat, old_acc) == carry_from(rels@, facts@, (k + 1) as nat, acc@));
        }
        k += 1;
    }
    acc
}

fn ex_tested(cmp: &Option<Cmp>, op: &Operand) -> (r: Option<Cmp>)
    ensures forall|rels: Seq<Rel>| r == #[trigger] tested(SymSt { rels, cmp: *cmp }, *op),
{
    match cmp {
        Some(m) => match ex_op_local(op) {
            Some(y) => if y == m.c { Some(cmp_copy(m)) } else { None },
            None => None,
        },
        None => None,
    }
}

fn ex_cmp_fact(m: &Cmp, outcome: bool) -> (r: Fact)
    ensures r == cmp_fact(*m, outcome),
{
    let (a, b) = (atom_copy(&m.a), atom_copy(&m.b));
    match m.op {
        BinOp::Lt => if outcome { Fact::Lt(a, b) } else { Fact::Le(b, a) },
        BinOp::Le => if outcome { Fact::Le(a, b) } else { Fact::Lt(b, a) },
        BinOp::Gt => if outcome { Fact::Lt(b, a) } else { Fact::Le(a, b) },
        _ => if outcome { Fact::Le(b, a) } else { Fact::Lt(a, b) },
    }
}

fn ex_switch_target(ts: &Vec<(u128, usize)>, v: u128, o: usize) -> (r: usize)
    ensures r == switch_target(ts@, 0, v, o),
{
    let mut k: usize = 0;
    while k < ts.len()
        invariant k <= ts@.len(), switch_target(ts@, k as nat, v, o) == switch_target(ts@, 0, v, o),
        decreases ts.len() - k,
    {
        if ts[k].0 == v { return ts[k].1; }
        k += 1;
    }
    o
}

fn ex_facts_plus(cy: &Vec<Fact>, extra: Option<Fact>) -> (r: Vec<Fact>)
    ensures r@ == cy@ + (match extra { Some(x) => seq![x], None => seq![] }),
{
    let mut r: Vec<Fact> = Vec::new();
    let mut i: usize = 0;
    while i < cy.len()
        invariant i <= cy@.len(), r@ =~= cy@.take(i as int),
        decreases cy.len() - i,
    {
        r.push(fact_copy(&cy[i]));
        i += 1;
        assert(r@ =~= cy@.take(i as int));
    }
    assert(cy@.take(cy@.len() as int) =~= cy@);
    let ghost e0 = extra;
    match extra {
        Some(x) => {
            r.push(x);
            assert(r@ =~= cy@ + seq![e0.unwrap()]);
        },
        None => { assert(r@ =~= cy@ + Seq::<Fact>::empty()); },
    }
    r
}

/// `switch_extra`'s one fact, if any.
fn ex_switch_extra(cmp: &Option<Cmp>, op: &Operand, ts: &Vec<(u128, usize)>, o: usize, t: usize) -> (r: Option<Fact>)
    ensures forall|rels: Seq<Rel>| #[trigger] switch_extra(SymSt { rels, cmp: *cmp }, *op, ts@, o, t) ==
        (match r { Some(x) => seq![x], None => seq![] }),
{
    let (z, n) = (ex_switch_target(ts, 0, o), ex_switch_target(ts, 1, o));
    match ex_tested(cmp, op) {
        Some(m) =>
            if z == n { None } else if t == z { Some(ex_cmp_fact(&m, false)) } else if t == n { Some(ex_cmp_fact(&m, true)) } else { None },
        None => None,
    }
}

pub open spec fn edge_view(p: (usize, Vec<Fact>)) -> (usize, Seq<Fact>) { (p.0, p.1@) }

proof fn lemma_edges_view(out: Seq<(usize, Vec<Fact>)>, want: Seq<(usize, Seq<Fact>)>)
    requires out.len() == want.len(), forall|j: int| 0 <= j < out.len() ==> #[trigger] edge_view(out[j]) == want[j],
    ensures out.map_values(|p: (usize, Vec<Fact>)| (p.0, p.1@)) == want,
{
    assert forall|j: int| 0 <= j < want.len() implies out.map_values(|p: (usize, Vec<Fact>)| (p.0, p.1@))[j] == want[j] by {
        assert(edge_view(out[j]) == want[j]);
    }
    assert(out.map_values(|p: (usize, Vec<Fact>)| (p.0, p.1@)) =~= want);
}

fn ex_switch_edge(cmp: &Option<Cmp>, op: &Operand, ts: &Vec<(u128, usize)>, o: usize, cy: &Vec<Fact>, t: usize) -> (r: (usize, Vec<Fact>))
    ensures forall|rels: Seq<Rel>| edge_view(r) == (t, cy@ + #[trigger] switch_extra(SymSt { rels, cmp: *cmp }, *op, ts@, o, t)),
{
    let extra = ex_switch_extra(cmp, op, ts, o, t);
    let ghost e0 = extra;
    let fs = ex_facts_plus(cy, extra);
    proof {
        assert forall|rels: Seq<Rel>| edge_view((t, fs)) == (t, cy@ + #[trigger] switch_extra(SymSt { rels, cmp: *cmp }, *op, ts@, o, t)) by {
            assert(switch_extra(SymSt { rels, cmp: *cmp }, *op, ts@, o, t) == (match e0 { Some(x) => seq![x], None => seq![] }));
        }
    }
    (t, fs)
}

fn ex_switch_edges(cmp: &Option<Cmp>, ghost_rels: Ghost<Seq<Rel>>, op: &Operand, ts: &Vec<(u128, usize)>, o: usize, cy: &Vec<Fact>) -> (out: Vec<(usize, Vec<Fact>)>)
    ensures ({
        let want = switch_edges(SymSt { rels: ghost_rels@, cmp: *cmp }, *op, ts@, o, cy@);
        &&& out@.len() == want.len()
        &&& forall|j: int| 0 <= j < out@.len() ==> #[trigger] edge_view(out@[j]) == want[j]
    }),
{
    let ghost st = SymSt { rels: ghost_rels@, cmp: *cmp };
    let ghost want = switch_edges(st, *op, ts@, o, cy@);
    let mut out: Vec<(usize, Vec<Fact>)> = Vec::new();
    let mut i: usize = 0;
    while i < ts.len()
        invariant
            i <= ts@.len(), out@.len() == i, st == (SymSt { rels: ghost_rels@, cmp: *cmp }),
            want == switch_edges(st, *op, ts@, o, cy@), want.len() == ts@.len() + 1,
            forall|j: int| 0 <= j < i ==> #[trigger] edge_view(out@[j]) == want[j],
        decreases ts.len() - i,
    {
        let e = ex_switch_edge(cmp, op, ts, o, cy, ts[i].1);
        proof {
            assert(edge_view(e) == (ts@[i as int].1, cy@ + switch_extra(st, *op, ts@, o, ts@[i as int].1)));
            assert(want[i as int] == edge_view(e));
        }
        out.push(e);
        proof { assert(edge_view(out@[i as int]) == want[i as int]); }
        i += 1;
    }
    let e = ex_switch_edge(cmp, op, ts, o, cy, o);
    proof {
        assert(edge_view(e) == (o, cy@ + switch_extra(st, *op, ts@, o, o)));
        assert(want[i as int] == edge_view(e));
    }
    out.push(e);
    proof { assert(edge_view(out@[i as int]) == want[i as int]); }
    out
}

fn ex_term_edges(cmp: &Option<Cmp>, st_rels: Ghost<Seq<Rel>>, rels: &Vec<Rel>, t: &Term, facts: &Vec<Fact>) -> (out: Vec<(usize, Vec<Fact>)>)
    ensures ({
        let want = term_edges(SymSt { rels: st_rels@, cmp: *cmp }, rels@, *t, facts@);
        &&& out@.len() == want.len()
        &&& forall|j: int| 0 <= j < out@.len() ==> #[trigger] edge_view(out@[j]) == want[j]
    }),
{
    let cy = ex_carry(rels, facts);
    let mut out: Vec<(usize, Vec<Fact>)> = Vec::new();
    match t {
        Term::Goto(b2) => out.push((*b2, cy)),
        Term::Switch(op, ts, o) => return ex_switch_edges(cmp, st_rels, op, ts, *o, &cy),
        Term::Assert(op, expected, b2) => {
            let extra = match ex_tested(cmp, op) {
                Some(m) => if *expected { Some(ex_cmp_fact(&m, true)) } else { None },
                None => None,
            };
            let ghost e0 = extra;
            let fs = ex_facts_plus(&cy, extra);
            proof {
                if extra is None { assert(cy@ + seq![] =~= cy@); }
            }
            out.push((*b2, fs));
        },
        Term::Call(_, _, _, next) => out.push((*next, cy)),
        _ => {},
    }
    out
}

/// The exec twin of `sym_block`.
pub fn exec_sym_block(b: &Body, blk: &Block, facts: &Vec<Fact>) -> (r: Eff)
    ensures eff_view(r) == sym_block(*b, *blk, facts@),
{
    let st = ex_sym_state(b, &blk.stmts, facts);
    let rels = ex_term_rels(b, &st.0, &blk.term, facts);
    let edge = ex_term_edges(&st.1, Ghost(st.0@), &rels, &blk.term, facts);
    let r = Eff { rel: rels, edge };
    proof {
        lemma_edges_view(edge@, term_edges(SymSt { rels: st.0@, cmp: st.1 }, rels@, blk.term, facts@));
    }
    r
}

} // verus!
