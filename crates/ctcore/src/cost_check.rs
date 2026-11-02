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

/// `Vec` has no extensional `==` in this toolchain, and every reader goes through `@`.
pub open spec fn monos_same(a: Seq<Mono>, b: Seq<Mono>) -> bool {
    a.len() == b.len() && forall|i: int| 0 <= i < a.len() ==> #[trigger] mono_view_eq(a[i], b[i])
}

/// `*m`, up to `Vec` identity (`mono_view_eq`).
pub fn mono_copy(m: &Mono) -> (r: Mono)
    ensures mono_view_eq(r, *m),
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
        invariant i <= p.monos@.len(), out@.len() == i, forall|j: int| 0 <= j < i ==> #[trigger] mono_view_eq(out@[j], p.monos@[j]),
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

#[allow(unused_variables)]
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

// ------------------------------------------------------------------ atom order

pub open spec fn ty_rank(t: IntTy) -> nat {
    match t {
        IntTy::U8 => 0, IntTy::U16 => 1, IntTy::U32 => 2, IntTy::U64 => 3, IntTy::U128 => 4, IntTy::Usize => 5,
        IntTy::I8 => 6, IntTy::I16 => 7, IntTy::I32 => 8, IntTy::I64 => 9, IntTy::I128 => 10, IntTy::Isize => 11,
        IntTy::Bool => 12,
    }
}

fn ex_ty_rank(t: &IntTy) -> (r: u8)
    ensures r as nat == ty_rank(*t),
{
    match t {
        IntTy::U8 => 0, IntTy::U16 => 1, IntTy::U32 => 2, IntTy::U64 => 3, IntTy::U128 => 4, IntTy::Usize => 5,
        IntTy::I8 => 6, IntTy::I16 => 7, IntTy::I32 => 8, IntTy::I64 => 9, IntTy::I128 => 10, IntTy::Isize => 11,
        IntTy::Bool => 12,
    }
}

pub open spec fn spec_atom_lt(a: Atom, b: Atom) -> bool
    decreases a,
{
    match a {
        Atom::Const(x) => match b { Atom::Const(y) => x < y, _ => true },
        Atom::Val(x, s) => match b {
            Atom::Const(_) => false,
            Atom::Val(y, t) => x < y || (x == y && ty_rank(s) < ty_rank(t)),
            _ => true,
        },
        Atom::Len(x) => match b {
            Atom::Len(y) => x < y,
            Atom::Gap(_, _) => true,
            _ => false,
        },
        Atom::Gap(a1, b1) => match b {
            Atom::Gap(a2, b2) => spec_atom_lt(*a1, *a2) || (*a1 == *a2 && spec_atom_lt(*b1, *b2)),
            _ => false,
        },
    }
}

/// `spec_atom_lt` is total and irreflexive.
pub proof fn lemma_atom_lt_total(a: Atom, b: Atom)
    ensures a == b || spec_atom_lt(a, b) || spec_atom_lt(b, a), !spec_atom_lt(a, a),
    decreases a,
{
    match (a, b) {
        (Atom::Gap(a1, b1), Atom::Gap(a2, b2)) => {
            lemma_atom_lt_total(*a1, *a2);
            lemma_atom_lt_total(*b1, *b2);
        },
        (Atom::Gap(a1, b1), _) => {
            lemma_atom_lt_total(*a1, *a1);
            lemma_atom_lt_total(*b1, *b1);
        },
        _ => {},
    }
}

pub fn atom_lt(a: &Atom, b: &Atom) -> (r: bool)
    ensures r == spec_atom_lt(*a, *b),
    decreases a,
{
    match a {
        Atom::Const(x) => match b { Atom::Const(y) => *x < *y, _ => true },
        Atom::Val(x, s) => match b {
            Atom::Const(_) => false,
            Atom::Val(y, t) => *x < *y || (*x == *y && ex_ty_rank(s) < ex_ty_rank(t)),
            _ => true,
        },
        Atom::Len(x) => match b {
            Atom::Len(y) => *x < *y,
            Atom::Gap(_, _) => true,
            _ => false,
        },
        Atom::Gap(a1, b1) => match b {
            Atom::Gap(a2, b2) => atom_lt(a1, a2) || (atom_eq(a1, a2) && atom_lt(b1, b2)),
            _ => false,
        },
    }
}

/// Non-decreasing and of degree at most 2.
fn mono_canonical(m: &Mono) -> (r: bool) {
    m.atoms.len() < 2 || (m.atoms.len() == 2 && !atom_lt(&m.atoms[1], &m.atoms[0]))
}

fn poly_canonical(p: &Poly) -> (r: bool) {
    let mut i: usize = 0;
    while i < p.monos.len()
        invariant i <= p.monos@.len(),
        decreases p.monos.len() - i,
    {
        if !mono_canonical(&p.monos[i]) { return false; }
        i += 1;
    }
    true
}

// ------------------------------------------------------------------ values of monomials

proof fn lemma_atoms0(fr: Frame, s: Seq<Atom>)
    requires s.len() == 0,
    ensures atoms_val(fr, s) == 1,
{
}

proof fn lemma_atoms1(fr: Frame, s: Seq<Atom>)
    requires s.len() == 1,
    ensures atoms_val(fr, s) == atom_val(fr, s[0]),
{
    reveal_with_fuel(atoms_val, 2);
}

proof fn lemma_atoms2(fr: Frame, s: Seq<Atom>)
    requires s.len() == 2,
    ensures atoms_val(fr, s) == atom_val(fr, s[0]) * atom_val(fr, s[1]),
{
    reveal_with_fuel(atoms_val, 3);
    assert(s.drop_first()[0] == s[1]);
}

proof fn lemma_monos_empty(fr: Frame, ms: Seq<Mono>)
    requires ms.len() == 0,
    ensures monos_val(fr, ms) == 0,
{
}

proof fn lemma_monos_push(fr: Frame, ms: Seq<Mono>, m: Mono)
    ensures monos_val(fr, ms.push(m)) == monos_val(fr, ms) + mono_val(fr, m),
    decreases ms.len(),
{
    let u = ms.push(m);
    if ms.len() == 0 {
        lemma_monos_empty(fr, u.drop_first());
        lemma_monos_empty(fr, ms);
        assert(u[0] == m);
    } else {
        assert(u.drop_first() =~= ms.drop_first().push(m));
        lemma_monos_push(fr, ms.drop_first(), m);
        assert(u[0] == ms[0]);
    }
}

proof fn lemma_take_step(fr: Frame, ms: Seq<Mono>, i: int)
    requires 0 <= i < ms.len(),
    ensures monos_val(fr, ms.take(i + 1)) == monos_val(fr, ms.take(i)) + mono_val(fr, ms[i]),
{
    assert(ms.take(i + 1) =~= ms.take(i).push(ms[i]));
    lemma_monos_push(fr, ms.take(i), ms[i]);
}

proof fn lemma_take_ends(ms: Seq<Mono>)
    ensures ms.take(ms.len() as int) =~= ms, ms.take(0).len() == 0,
{
}

proof fn lemma_monos_update(fr: Frame, ms: Seq<Mono>, j: int, m2: Mono)
    requires 0 <= j < ms.len(),
    ensures monos_val(fr, ms.update(j, m2)) + mono_val(fr, ms[j]) == monos_val(fr, ms) + mono_val(fr, m2),
    decreases ms.len(),
{
    let u = ms.update(j, m2);
    if j == 0 {
        assert(u.drop_first() =~= ms.drop_first());
    } else {
        assert(u.drop_first() =~= ms.drop_first().update(j - 1, m2));
        lemma_monos_update(fr, ms.drop_first(), j - 1, m2);
        assert(u[0] == ms[0]);
        assert(ms.drop_first()[j - 1] == ms[j]);
    }
}

proof fn lemma_monos_same(fr: Frame, a: Seq<Mono>, b: Seq<Mono>)
    requires monos_same(a, b),
    ensures monos_val(fr, a) == monos_val(fr, b),
    decreases a.len(),
{
    if a.len() > 0 {
        assert(mono_view_eq(a[0], b[0]));
        assert forall|i: int| 0 <= i < a.drop_first().len() implies #[trigger] mono_view_eq(a.drop_first()[i], b.drop_first()[i]) by {
            assert(mono_view_eq(a[i + 1], b[i + 1]));
        }
        lemma_monos_same(fr, a.drop_first(), b.drop_first());
    }
}

// ------------------------------------------------------------------ products

proof fn lemma_scale(c: nat, x: nat, y: nat)
    requires x <= y,
    ensures c * x <= c * y,
{
    assert(c * x <= c * y) by (nonlinear_arith) requires x <= y, c >= 0;
}

proof fn lemma_scale_one(c: nat, x: nat)
    ensures c * (x + 1) == c * x + c,
{
    assert(c * (x + 1) == c * x + c) by (nonlinear_arith);
}

proof fn lemma_scale_add(c: nat, x: nat, y: nat)
    ensures c * (x + y) == c * x + c * y,
{
    vstd::arithmetic::mul::lemma_mul_is_distributive_add(c as int, x as int, y as int);
}

proof fn lemma_product_le(a: nat, a2: nat, b: nat, b2: nat)
    requires a <= a2, b <= b2,
    ensures a * b <= a2 * b2,
{
    assert(a * b <= a2 * b) by (nonlinear_arith) requires a <= a2, b >= 0;
    assert(a2 * b <= a2 * b2) by (nonlinear_arith) requires b <= b2, a2 >= 0;
}

/// `g'·u' + u <= g·u` when `g' + 1 <= g` and `u' <= u`.
proof fn lemma_mono_credit(g1: nat, g: nat, u1: nat, u: nat)
    requires g1 + 1 <= g, u1 <= u,
    ensures g1 * u1 + u <= g * u,
{
    assert(g1 * u1 <= g1 * u) by (nonlinear_arith) requires u1 <= u, g1 >= 0;
    assert((g1 + 1) * u <= g * u) by (nonlinear_arith) requires g1 + 1 <= g, u >= 0;
    assert((g1 + 1) * u == g1 * u + u) by (nonlinear_arith);
}

proof fn lemma_assoc(c: nat, k: nat, x: nat)
    ensures (c * k) * x == c * (k * x),
{
    vstd::arithmetic::mul::lemma_mul_is_associative(c as int, k as int, x as int);
}

proof fn lemma_comm(x: nat, y: nat)
    ensures x * y == y * x,
{
    assert(x * y == y * x) by (nonlinear_arith);
}

proof fn lemma_mul_nat(x: nat, y: nat)
    ensures x * y >= 0,
{
    assert(x * y >= 0) by (nonlinear_arith) requires x >= 0, y >= 0;
}

// ------------------------------------------------------------------ building monomials

fn const_atom(a: &Atom) -> (r: Option<u64>)
    ensures r matches Some(k) ==> *a == Atom::Const(k), r is None ==> !(*a is Const),
{
    match a { Atom::Const(k) => Some(*k), _ => None }
}

/// `c·a`, with a `Const` folded into the coefficient.
fn fold1(c: u64, a: Atom) -> (r: Option<Mono>)
    ensures r matches Some(m) ==> forall|fr: Frame| #[trigger] mono_val(fr, m) == c as nat * atom_val(fr, a),
{
    let ghost g = a;
    match const_atom(&a) {
        Some(k) => match c.checked_mul(k) {
            Some(v) => {
                let m = Mono { coef: v, atoms: Vec::new() };
                proof {
                    assert forall|fr: Frame| #[trigger] mono_val(fr, m) == c as nat * atom_val(fr, g) by {
                        lemma_atoms0(fr, m.atoms@);
                    }
                }
                Some(m)
            },
            None => None,
        },
        None => {
            let mut atoms: Vec<Atom> = Vec::new();
            atoms.push(a);
            let m = Mono { coef: c, atoms };
            proof {
                assert forall|fr: Frame| #[trigger] mono_val(fr, m) == c as nat * atom_val(fr, g) by {
                    lemma_atoms1(fr, m.atoms@);
                }
            }
            Some(m)
        },
    }
}

/// `c·a1·a2`, sorted non-decreasing, with `Const`s folded.
fn fold2(c: u64, a1: Atom, a2: Atom) -> (r: Option<Mono>)
    ensures r matches Some(m) ==> forall|fr: Frame| #[trigger] mono_val(fr, m) == c as nat * (atom_val(fr, a1) * atom_val(fr, a2)),
{
    let ghost (g1, g2) = (a1, a2);
    if let Some(k) = const_atom(&a1) {
        if let Some(v) = c.checked_mul(k) {
            let r = fold1(v, a2);
            proof {
                if r is Some {
                    let m = r.unwrap();
                    assert forall|fr: Frame| #[trigger] mono_val(fr, m) == c as nat * (atom_val(fr, g1) * atom_val(fr, g2)) by {
                        lemma_assoc(c as nat, k as nat, atom_val(fr, g2));
                    }
                }
            }
            return r;
        }
        return None;
    }
    if let Some(k) = const_atom(&a2) {
        if let Some(v) = c.checked_mul(k) {
            let r = fold1(v, a1);
            proof {
                if r is Some {
                    let m = r.unwrap();
                    assert forall|fr: Frame| #[trigger] mono_val(fr, m) == c as nat * (atom_val(fr, g1) * atom_val(fr, g2)) by {
                        lemma_assoc(c as nat, k as nat, atom_val(fr, g1));
                        lemma_comm(k as nat, atom_val(fr, g1));
                    }
                }
            }
            return r;
        }
        return None;
    }
    let swap = atom_lt(&a2, &a1);
    let mut atoms: Vec<Atom> = Vec::new();
    if swap { atoms.push(a2); atoms.push(a1); } else { atoms.push(a1); atoms.push(a2); }
    let m = Mono { coef: c, atoms };
    proof {
        assert forall|fr: Frame| #[trigger] mono_val(fr, m) == c as nat * (atom_val(fr, g1) * atom_val(fr, g2)) by {
            lemma_atoms2(fr, m.atoms@);
            lemma_comm(atom_val(fr, g1), atom_val(fr, g2));
        }
    }
    Some(m)
}

// ------------------------------------------------------------------ polynomial sums

/// Concatenation: coefficients are compared by `poly_dominates`, so no addition can overflow.
pub fn poly_add(a: &Poly, b: &Poly) -> (r: Option<Poly>)
    ensures r matches Some(q) ==> forall|fr: Frame| #[trigger] poly_val(fr, q) == poly_val(fr, *a) + poly_val(fr, *b),
{
    let copy = poly_copy(a);
    proof {
        assert forall|fr: Frame| #[trigger] monos_val(fr, copy.monos@) == poly_val(fr, *a) + monos_val(fr, b.monos@.take(0)) by {
            lemma_monos_same(fr, copy.monos@, a.monos@);
            lemma_monos_empty(fr, b.monos@.take(0));
        }
    }
    let mut out = copy.monos;
    let mut i: usize = 0;
    while i < b.monos.len()
        invariant
            i <= b.monos@.len(),
            forall|fr: Frame| #[trigger] monos_val(fr, out@) == poly_val(fr, *a) + monos_val(fr, b.monos@.take(i as int)),
        decreases b.monos.len() - i,
    {
        let ghost o0 = out@;
        let m = mono_copy(&b.monos[i]);
        out.push(m);
        proof {
            assert forall|fr: Frame| #[trigger] monos_val(fr, out@) == poly_val(fr, *a) + monos_val(fr, b.monos@.take(i + 1)) by {
                assert(monos_val(fr, o0) == poly_val(fr, *a) + monos_val(fr, b.monos@.take(i as int)));
                lemma_monos_push(fr, o0, m);
                lemma_take_step(fr, b.monos@, i as int);
                assert(out@ == o0.push(m));
            }
        }
        i += 1;
    }
    proof { lemma_take_ends(b.monos@); }
    Some(Poly { monos: out })
}

// ------------------------------------------------------------------ domination

/// Takes `c` of `atoms` out of the coefficients left in `rem`.
fn spend(rem: Vec<Mono>, atoms: &Vec<Atom>, c: u64) -> (r: (bool, Vec<Mono>))
    ensures r.0 ==> forall|fr: Frame| #[trigger] monos_val(fr, rem@) >= monos_val(fr, r.1@) + c as nat * atoms_val(fr, atoms@),
{
    let ghost orig = rem@;
    let mut rem = rem;
    let mut need = c;
    let mut j: usize = 0;
    proof {
        assert forall|fr: Frame| #[trigger] monos_val(fr, orig) == monos_val(fr, rem@) + (c - need) * atoms_val(fr, atoms@) by {
            assert((c - need) * atoms_val(fr, atoms@) == 0);
        }
    }
    while j < rem.len()
        invariant
            j <= rem@.len(), need <= c,
            forall|fr: Frame| #[trigger] monos_val(fr, orig) == monos_val(fr, rem@) + (c - need) * atoms_val(fr, atoms@),
        decreases rem@.len() - j,
    {
        if need > 0 && atoms_eq(&rem[j].atoms, atoms) {
            let have = rem[j].coef;
            let t = if have < need { have } else { need };
            let m2 = Mono { coef: have - t, atoms: atoms_copy(atoms) };
            let ghost r0 = rem@;
            let ghost n0 = need;
            rem.set(j, m2);
            need = need - t;
            proof {
                assert forall|fr: Frame| #[trigger] monos_val(fr, orig) == monos_val(fr, rem@) + (c - need) * atoms_val(fr, atoms@) by {
                    let av = atoms_val(fr, atoms@);
                    assert(monos_val(fr, orig) == monos_val(fr, r0) + (c - n0) * av);
                    lemma_monos_update(fr, r0, j as int, m2);
                    assert(mono_val(fr, m2) + t as nat * av == mono_val(fr, r0[j as int])) by {
                        lemma_scale_add(av, (have - t) as nat, t as nat);
                        lemma_comm(av, (have - t) as nat);
                        lemma_comm(av, t as nat);
                        lemma_comm(av, have as nat);
                    }
                    assert((c - n0) * av + t as nat * av == (c - need) * av) by {
                        lemma_scale_add(av, (c - n0) as nat, t as nat);
                        lemma_comm(av, (c - n0) as nat);
                        lemma_comm(av, t as nat);
                        lemma_comm(av, (c - need) as nat);
                    }
                }
            }
        }
        j += 1;
    }
    if need > 0 { return (false, rem); }
    (true, rem)
}

/// Syntactic matching on atom lists, `extra` from the constant monomials. Two lists that are the
/// same value in a different order do not match: canonical order is what makes this complete.
pub fn poly_dominates(lhs: &Poly, rhs: &Poly, extra: u64) -> (r: bool)
    ensures r ==> forall|fr: Frame| #[trigger] poly_val(fr, *lhs) >= poly_val(fr, *rhs) + extra,
{
    let copy = poly_copy(lhs);
    proof {
        assert forall|fr: Frame| #[trigger] monos_val(fr, copy.monos@) == poly_val(fr, *lhs) by {
            lemma_monos_same(fr, copy.monos@, lhs.monos@);
        }
    }
    let mut rem = copy.monos;
    let mut i: usize = 0;
    while i < rhs.monos.len()
        invariant
            i <= rhs.monos@.len(),
            forall|fr: Frame| #[trigger] poly_val(fr, *lhs) >= monos_val(fr, rem@) + monos_val(fr, rhs.monos@.take(i as int)),
        decreases rhs.monos.len() - i,
    {
        let ghost r0 = rem@;
        let s = spend(rem, &rhs.monos[i].atoms, rhs.monos[i].coef);
        if !s.0 { return false; }
        rem = s.1;
        proof {
            assert forall|fr: Frame| #[trigger] poly_val(fr, *lhs) >= monos_val(fr, rem@) + monos_val(fr, rhs.monos@.take(i + 1)) by {
                assert(poly_val(fr, *lhs) >= monos_val(fr, r0) + monos_val(fr, rhs.monos@.take(i as int)));
                assert(monos_val(fr, r0) >= monos_val(fr, rem@) + mono_val(fr, rhs.monos@[i as int]));
                lemma_take_step(fr, rhs.monos@, i as int);
            }
        }
        i += 1;
    }
    let no_atoms: Vec<Atom> = Vec::new();
    let ghost r0 = rem@;
    let s = spend(rem, &no_atoms, extra);
    if !s.0 { return false; }
    proof {
        lemma_take_ends(rhs.monos@);
        assert forall|fr: Frame| #[trigger] poly_val(fr, *lhs) >= poly_val(fr, *rhs) + extra by {
            lemma_atoms0(fr, no_atoms@);
            assert(poly_val(fr, *lhs) >= monos_val(fr, r0) + monos_val(fr, rhs.monos@.take(rhs.monos@.len() as int)));
            assert(monos_val(fr, r0) >= monos_val(fr, s.1@) + extra as nat * atoms_val(fr, no_atoms@));
        }
    }
    true
}

// ------------------------------------------------------------------ facts

fn fact_implied(have: &Vec<Fact>, f: &Fact) -> (r: bool)
    ensures r ==> forall|fr: Frame| #[trigger] facts_hold(fr, have@) ==> fact_holds(fr, *f),
{
    let mut i: usize = 0;
    while i < have.len()
        invariant i <= have@.len(),
        decreases have.len() - i,
    {
        let hit = fact_eq(&have[i], f) || match (&have[i], f) {
            (Fact::Lt(x1, y1), Fact::Le(x2, y2)) => atom_eq(x1, x2) && atom_eq(y1, y2),
            _ => false,
        };
        if hit {
            proof {
                assert forall|fr: Frame| #[trigger] facts_hold(fr, have@) implies fact_holds(fr, *f) by {
                    assert(fact_holds(fr, have@[i as int]));
                }
            }
            return true;
        }
        i += 1;
    }
    false
}

pub fn facts_imply(have: &Vec<Fact>, need: &Vec<Fact>) -> (r: bool)
    ensures r ==> forall|fr: Frame| #[trigger] facts_hold(fr, have@) ==> facts_hold(fr, need@),
{
    let mut i: usize = 0;
    while i < need.len()
        invariant
            i <= need@.len(),
            forall|j: int, fr: Frame| 0 <= j < i && #[trigger] facts_hold(fr, have@) ==> fact_holds(fr, #[trigger] need@[j]),
        decreases need.len() - i,
    {
        if !fact_implied(have, &need[i]) { return false; }
        i += 1;
    }
    proof {
        assert forall|fr: Frame| #[trigger] facts_hold(fr, have@) implies facts_hold(fr, need@) by {
            assert forall|j: int| 0 <= j < need@.len() implies fact_holds(fr, #[trigger] need@[j]) by {}
        }
    }
    true
}

// ------------------------------------------------------------------ pulling atoms back

pub open spec fn pull_ctx(rels: Seq<Rel>, facts: Seq<Fact>, pre: Frame, post: Frame) -> bool {
    facts_hold(pre, facts) && rels_sound(rels, pre, post)
}

pub open spec fn di(d: bool) -> nat { if d { 1 } else { 0 } }

/// `a` at `post` is at most `img` at `pre`, less one for a decrement.
pub open spec fn atom_up(rels: Seq<Rel>, facts: Seq<Fact>, a: Atom, img: Atom, d: bool) -> bool {
    forall|pre: Frame, post: Frame| #[trigger] pull_ctx(rels, facts, pre, post) ==> atom_val(post, a) + di(d) <= atom_val(pre, img)
}

pub open spec fn atom_exact(rels: Seq<Rel>, facts: Seq<Fact>, a: Atom, img: Atom) -> bool {
    forall|pre: Frame, post: Frame| #[trigger] pull_ctx(rels, facts, pre, post) ==> atom_val(post, a) == atom_val(pre, img)
}

proof fn lemma_rel_sound_at(rels: Seq<Rel>, x: usize, pre: Frame, post: Frame)
    requires rels_sound(rels, pre, post), (x as nat) < rels.len(),
    ensures rel_sound(rels[x as int], x as nat, pre, post),
{
    assert(rel_sound(rels[x as int], (x as int) as nat, pre, post));
}

#[allow(unused_variables)]
fn pull_val(rels: &Vec<Rel>, facts: &Vec<Fact>, x: usize, ty: &IntTy) -> (r: Option<Atom>)
    ensures r matches Some(img) ==> atom_up(rels@, facts@, Atom::Val(x, *ty), img, false),
{
    if x >= rels.len() { return None; }
    let r = match &rels[x] {
        Rel::Same => Some(Atom::Val(x, int_ty_copy(ty))),
        Rel::ValEq(Atom::Val(y, t), k) => if *k == 0 && int_ty_eq(t, ty) { Some(Atom::Val(*y, int_ty_copy(ty))) } else { None },
        Rel::ValEq(Atom::Const(c), k) => if *k == 0 { Some(Atom::Const(*c)) } else { None },
        Rel::ValLe(a) => Some(atom_copy(a)),
        _ => None,
    };
    proof {
        if r is Some {
            let img = r.unwrap();
            assert forall|pre: Frame, post: Frame| #[trigger] pull_ctx(rels@, facts@, pre, post)
                implies atom_val(post, Atom::Val(x, *ty)) + di(false) <= atom_val(pre, img) by {
                lemma_rel_sound_at(rels@, x, pre, post);
                assert(val_nat(*ty, nth(post.locals, x as nat)) == atom_val(post, Atom::Val(x, *ty)));
            }
        }
    }
    r
}

#[allow(unused_variables)]
fn pull_len(rels: &Vec<Rel>, facts: &Vec<Fact>, x: usize) -> (r: Option<Atom>)
    ensures r matches Some(img) ==> atom_up(rels@, facts@, Atom::Len(x), img, false),
{
    if x >= rels.len() { return None; }
    let r = match &rels[x] {
        Rel::Same => Some(Atom::Len(x)),
        Rel::LenEq(a) => Some(atom_copy(a)),
        Rel::LenLe(a) => Some(atom_copy(a)),
        _ => None,
    };
    proof {
        if r is Some {
            let img = r.unwrap();
            assert forall|pre: Frame, post: Frame| #[trigger] pull_ctx(rels@, facts@, pre, post)
                implies atom_val(post, Atom::Len(x)) + di(false) <= atom_val(pre, img) by {
                lemma_rel_sound_at(rels@, x, pre, post);
            }
        }
    }
    r
}

/// The image of a `Gap`'s subtrahend, where the two values are equal.
#[allow(unused_variables)]
fn pull_exact(rels: &Vec<Rel>, facts: &Vec<Fact>, b: &Atom) -> (r: Option<Atom>)
    ensures r matches Some(img) ==> atom_exact(rels@, facts@, *b, img),
{
    let r = match b {
        Atom::Val(x, ty) => if *x >= rels.len() { None } else {
            match &rels[*x] {
                Rel::Same => Some(Atom::Val(*x, int_ty_copy(ty))),
                Rel::ValEq(Atom::Val(y, t), k) => if *k == 0 && int_ty_eq(t, ty) { Some(Atom::Val(*y, int_ty_copy(ty))) } else { None },
                _ => None,
            }
        },
        Atom::Len(x) => if *x >= rels.len() { None } else {
            match &rels[*x] {
                Rel::Same => Some(Atom::Len(*x)),
                Rel::LenEq(a) => Some(atom_copy(a)),
                _ => None,
            }
        },
        _ => None,
    };
    proof {
        if r is Some {
            let img = r.unwrap();
            assert forall|pre: Frame, post: Frame| #[trigger] pull_ctx(rels@, facts@, pre, post)
                implies atom_val(post, *b) == atom_val(pre, img) by {
                match *b {
                    Atom::Val(x, _) => lemma_rel_sound_at(rels@, x, pre, post),
                    Atom::Len(x) => lemma_rel_sound_at(rels@, x, pre, post),
                    _ => {},
                }
            }
        }
    }
    r
}

/// `facts` has `Lt(lhs, rhs)`.
fn has_lt(facts: &Vec<Fact>, lhs: &Atom, rhs: &Atom) -> (r: bool)
    ensures r ==> forall|fr: Frame| #[trigger] facts_hold(fr, facts@) ==> atom_val(fr, *lhs) < atom_val(fr, *rhs),
{
    let mut i: usize = 0;
    while i < facts.len()
        invariant i <= facts@.len(),
        decreases facts.len() - i,
    {
        let hit = match &facts[i] {
            Fact::Lt(x, y) => atom_eq(x, lhs) && atom_eq(y, rhs),
            _ => false,
        };
        if hit {
            proof {
                assert forall|fr: Frame| #[trigger] facts_hold(fr, facts@) implies atom_val(fr, *lhs) < atom_val(fr, *rhs) by {
                    assert(fact_holds(fr, facts@[i as int]));
                }
            }
            return true;
        }
        i += 1;
    }
    false
}

/// `b` is a counter this block increments: `Val(i, ty)` with rel `ValEq(Val(i, ty), 1)`.
#[allow(unused_variables)]
fn inc_counter(rels: &Vec<Rel>, b: &Atom) -> (r: bool)
    ensures r ==> b is Val && (b->Val_0 as nat) < rels@.len()
        && rels@[b->Val_0 as int] == Rel::ValEq(*b, 1),
{
    match b {
        Atom::Val(i, ty) => *i < rels.len() && match &rels[*i] {
            Rel::ValEq(a, k) => *k == 1 && atom_eq(a, b),
            _ => false,
        },
        _ => false,
    }
}

#[allow(unused_variables)]
fn pull_gap(rels: &Vec<Rel>, facts: &Vec<Fact>, a: &Atom, a1: Atom, b: &Atom) -> (r: (Atom, bool))
    requires atom_up(rels@, facts@, *a, a1, false),
    ensures atom_up(rels@, facts@, Atom::Gap(Box::new(*a), Box::new(*b)), r.0, r.1),
{
    let ghost g = a1;
    let ghost whole = Atom::Gap(Box::new(*a), Box::new(*b));
    if let Some(img) = pull_exact(rels, facts, b) {
        let ghost gi = img;
        let r = Atom::Gap(Box::new(a1), Box::new(img));
        proof {
            assert forall|pre: Frame, post: Frame| #[trigger] pull_ctx(rels@, facts@, pre, post)
                implies atom_val(post, whole) + di(false) <= atom_val(pre, r) by {
                assert(atom_val(post, *a) + di(false) <= atom_val(pre, g));
                assert(atom_val(post, *b) == atom_val(pre, gi));
            }
        }
        return (r, false);
    }
    if inc_counter(rels, b) {
        let d = has_lt(facts, b, &a1);
        let r = Atom::Gap(Box::new(a1), Box::new(atom_copy(b)));
        proof {
            assert forall|pre: Frame, post: Frame| #[trigger] pull_ctx(rels@, facts@, pre, post)
                implies atom_val(post, whole) + di(d) <= atom_val(pre, r) by {
                assert(atom_val(post, *a) + di(false) <= atom_val(pre, g));
                lemma_rel_sound_at(rels@, b->Val_0, pre, post);
                assert(atom_val(post, *b) == atom_val(pre, *b) + 1);
                if d { assert(atom_val(pre, *b) < atom_val(pre, g)); }
            }
        }
        return (r, d);
    }
    proof {
        assert forall|pre: Frame, post: Frame| #[trigger] pull_ctx(rels@, facts@, pre, post)
            implies atom_val(post, whole) + di(false) <= atom_val(pre, g) by {
            assert(atom_val(post, *a) + di(false) <= atom_val(pre, g));
        }
    }
    (a1, false)
}

/// The image of a post-atom at the block's start, and whether it is a decrement.
#[allow(unused_variables)]
fn pull_atom(rels: &Vec<Rel>, facts: &Vec<Fact>, a: &Atom) -> (r: Option<(Atom, bool)>)
    ensures r matches Some((img, d)) ==> atom_up(rels@, facts@, *a, img, d),
    decreases a,
{
    match a {
        Atom::Const(c) => {
            let r = Atom::Const(*c);
            proof {
                assert forall|pre: Frame, post: Frame| #[trigger] pull_ctx(rels@, facts@, pre, post)
                    implies atom_val(post, *a) + di(false) <= atom_val(pre, r) by {}
            }
            Some((r, false))
        },
        Atom::Val(x, ty) => match pull_val(rels, facts, *x, ty) { Some(i) => Some((i, false)), None => None },
        Atom::Len(x) => match pull_len(rels, facts, *x) { Some(i) => Some((i, false)), None => None },
        Atom::Gap(x, y) => match pull_atom(rels, facts, x) {
            Some((a1, d)) => {
                let ghost g = a1;
                proof {
                    assert forall|pre: Frame, post: Frame| #[trigger] pull_ctx(rels@, facts@, pre, post)
                        implies atom_val(post, **x) + di(false) <= atom_val(pre, g) by {
                        assert(atom_val(post, **x) + di(d) <= atom_val(pre, g));
                    }
                }
                Some(pull_gap(rels, facts, x, a1, y))
            },
            None => None,
        },
    }
}

// ------------------------------------------------------------------ pulling monomials back

pub open spec fn cr_val(fr: Frame, cr: Option<Mono>) -> nat {
    match cr { Some(m) => mono_val(fr, m), None => 0 }
}

pub open spec fn mono_up(rels: Seq<Rel>, facts: Seq<Fact>, m: Mono, up: Mono, cr: Option<Mono>) -> bool {
    forall|pre: Frame, post: Frame| #[trigger] pull_ctx(rels, facts, pre, post) ==> mono_val(post, m) + cr_val(pre, cr) <= mono_val(pre, up)
}

fn pull_mono1(rels: &Vec<Rel>, facts: &Vec<Fact>, m: &Mono) -> (r: Option<(Mono, Option<Mono>)>)
    requires m.atoms@.len() == 1,
    ensures r matches Some((up, cr)) ==> mono_up(rels@, facts@, *m, up, cr),
{
    let c = m.coef;
    match pull_atom(rels, facts, &m.atoms[0]) {
        Some((img, d)) => {
            let ghost gi = img;
            match fold1(c, img) {
                Some(up) => {
                    let cr = if d { Some(Mono { coef: c, atoms: Vec::new() }) } else { None };
                    proof {
                        assert forall|pre: Frame, post: Frame| #[trigger] pull_ctx(rels@, facts@, pre, post)
                            implies mono_val(post, *m) + cr_val(pre, cr) <= mono_val(pre, up) by {
                            let p = atom_val(post, m.atoms@[0]);
                            let i = atom_val(pre, gi);
                            lemma_atoms1(post, m.atoms@);
                            assert(p + di(d) <= i);
                            lemma_scale(c as nat, p + di(d), i);
                            if d {
                                lemma_atoms0(pre, cr.unwrap().atoms@);
                                lemma_scale_one(c as nat, p);
                            }
                        }
                    }
                    Some((up, cr))
                },
                None => None,
            }
        },
        None => None,
    }
}

/// What a decrement in a degree-2 monomial owes, scaled by the coefficient.
proof fn lemma_mono2_credit(c: nat, p1: nat, p2: nat, i1: nat, i2: nat)
    requires p1 + 1 <= i1, p2 <= i2,
    ensures c * (p1 * p2) + c * i2 <= c * (i1 * i2),
{
    lemma_mono_credit(p1, i1, p2, i2);
    lemma_scale(c, p1 * p2 + i2, i1 * i2);
    lemma_mul_nat(p1, p2);
    lemma_scale_add(c, p1 * p2, i2);
}

proof fn lemma_mono2_up(rels: Seq<Rel>, facts: Seq<Fact>, m: Mono, up: Mono, cr: Option<Mono>, i1: Atom, d1: bool, i2: Atom, d2: bool, pre: Frame, post: Frame)
    requires
        m.atoms@.len() == 2, pull_ctx(rels, facts, pre, post),
        atom_up(rels, facts, m.atoms@[0], i1, d1), atom_up(rels, facts, m.atoms@[1], i2, d2),
        mono_val(pre, up) == m.coef as nat * (atom_val(pre, i1) * atom_val(pre, i2)),
        d1 ==> (cr matches Some(x) && mono_val(pre, x) == m.coef as nat * atom_val(pre, i2)),
        !d1 && d2 ==> (cr matches Some(x) && mono_val(pre, x) == m.coef as nat * atom_val(pre, i1)),
        !d1 && !d2 ==> cr is None,
    ensures mono_val(post, m) + cr_val(pre, cr) <= mono_val(pre, up),
{
    let (c, p1, p2, v1, v2) = (m.coef as nat, atom_val(post, m.atoms@[0]), atom_val(post, m.atoms@[1]), atom_val(pre, i1), atom_val(pre, i2));
    lemma_atoms2(post, m.atoms@);
    assert(p1 + di(d1) <= v1 && p2 + di(d2) <= v2);
    if d1 {
        lemma_mono2_credit(c, p1, p2, v1, v2);
    } else if d2 {
        lemma_mono2_credit(c, p2, p1, v2, v1);
        lemma_comm(p2, p1);
        lemma_comm(v2, v1);
    } else {
        lemma_product_le(p1, v1, p2, v2);
        lemma_scale(c, p1 * p2, v1 * v2);
    }
}

fn pull_mono2(rels: &Vec<Rel>, facts: &Vec<Fact>, m: &Mono) -> (r: Option<(Mono, Option<Mono>)>)
    requires m.atoms@.len() == 2,
    ensures r matches Some((up, cr)) ==> mono_up(rels@, facts@, *m, up, cr),
{
    let c = m.coef;
    let p1 = pull_atom(rels, facts, &m.atoms[0]);
    let p2 = pull_atom(rels, facts, &m.atoms[1]);
    if p1.is_none() || p2.is_none() { return None; }
    let (i1, d1) = p1.unwrap();
    let (i2, d2) = p2.unwrap();
    // the `d1` arm: canonical order puts `Gap` last, so only `Gap·Gap` reaches it; no test does, and Task 5 emits none.
    let cr = if d1 {
        match fold1(c, atom_copy(&i2)) { Some(x) => Some(x), None => return None }
    } else if d2 {
        match fold1(c, atom_copy(&i1)) { Some(x) => Some(x), None => return None }
    } else {
        None
    };
    let ghost (g1, g2) = (i1, i2);
    match fold2(c, i1, i2) {
        Some(up) => {
            proof {
                assert forall|pre: Frame, post: Frame| #[trigger] pull_ctx(rels@, facts@, pre, post)
                    implies mono_val(post, *m) + cr_val(pre, cr) <= mono_val(pre, up) by {
                    assert(mono_val(pre, up) == c as nat * (atom_val(pre, g1) * atom_val(pre, g2)));
                    lemma_mono2_up(rels@, facts@, *m, up, cr, g1, d1, g2, d2, pre, post);
                }
            }
            Some((up, cr))
        },
        None => None,
    }
}

// ponytail: degree at most 2; higher degree needs a multiset-product lemma.
fn pull_mono(rels: &Vec<Rel>, facts: &Vec<Fact>, m: &Mono) -> (r: Option<(Mono, Option<Mono>)>)
    ensures r matches Some((up, cr)) ==> mono_up(rels@, facts@, *m, up, cr),
{
    if m.atoms.len() == 0 {
        let up = mono_copy(m);
        let ghost none = Option::<Mono>::None;
        proof {
            assert forall|pre: Frame, post: Frame| #[trigger] pull_ctx(rels@, facts@, pre, post)
                implies mono_val(post, *m) + cr_val(pre, none) <= mono_val(pre, up) by {
                lemma_atoms0(post, m.atoms@);
                lemma_atoms0(pre, up.atoms@);
            }
        }
        Some((up, None))
    } else if m.atoms.len() == 1 {
        pull_mono1(rels, facts, m)
    } else if m.atoms.len() == 2 {
        pull_mono2(rels, facts, m)
    } else {
        None
    }
}

pub open spec fn monos_up(rels: Seq<Rel>, facts: Seq<Fact>, q: Seq<Mono>, up: Seq<Mono>, cr: Seq<Mono>) -> bool {
    forall|pre: Frame, post: Frame| #[trigger] pull_ctx(rels, facts, pre, post) ==> monos_val(post, q) + monos_val(pre, cr) <= monos_val(pre, up)
}

proof fn lemma_monos_up_step(rels: Seq<Rel>, facts: Seq<Fact>, q: Seq<Mono>, i: int, up: Seq<Mono>, cr: Seq<Mono>, u: Mono, c: Option<Mono>, up2: Seq<Mono>, cr2: Seq<Mono>)
    requires
        0 <= i < q.len(), monos_up(rels, facts, q.take(i), up, cr), mono_up(rels, facts, q[i], u, c),
        up2 == up.push(u), cr2 == (match c { Some(x) => cr.push(x), None => cr }),
    ensures monos_up(rels, facts, q.take(i + 1), up2, cr2),
{
    assert forall|pre: Frame, post: Frame| #[trigger] pull_ctx(rels, facts, pre, post)
        implies monos_val(post, q.take(i + 1)) + monos_val(pre, cr2) <= monos_val(pre, up2) by {
        assert(monos_val(post, q.take(i)) + monos_val(pre, cr) <= monos_val(pre, up));
        assert(mono_val(post, q[i]) + cr_val(pre, c) <= mono_val(pre, u));
        lemma_take_step(post, q, i);
        lemma_monos_push(pre, up, u);
        if let Some(x) = c { lemma_monos_push(pre, cr, x); }
    }
}

/// `q` at `post`, plus a credit at `pre`, is at most `up` at `pre`.
pub fn pull_post(q: &Poly, e: &Eff, facts: &Vec<Fact>) -> (r: Option<(Poly, Poly)>)
    ensures r matches Some((up, credit)) ==> forall|pre: Frame, post: Frame, s: nat|
        facts_hold(pre, facts@) && #[trigger] eff_sound(eff_view(*e), pre, post, s)
            ==> poly_val(post, *q) + poly_val(pre, credit) <= poly_val(pre, up),
{
    let mut up: Vec<Mono> = Vec::new();
    let mut cr: Vec<Mono> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert forall|pre: Frame, post: Frame| #[trigger] pull_ctx(e.rel@, facts@, pre, post)
            implies monos_val(post, q.monos@.take(0)) + monos_val(pre, cr@) <= monos_val(pre, up@) by {
            lemma_monos_empty(post, q.monos@.take(0));
        }
    }
    while i < q.monos.len()
        invariant i <= q.monos@.len(), monos_up(e.rel@, facts@, q.monos@.take(i as int), up@, cr@),
        decreases q.monos.len() - i,
    {
        match pull_mono(&e.rel, facts, &q.monos[i]) {
            Some((u, c)) => {
                let ghost (up0, cr0, g_u, g_c) = (up@, cr@, u, c);
                up.push(u);
                if let Some(x) = c { cr.push(x); }
                proof { lemma_monos_up_step(e.rel@, facts@, q.monos@, i as int, up0, cr0, g_u, g_c, up@, cr@); }
            },
            None => return None,
        }
        i += 1;
    }
    let r = (Poly { monos: up }, Poly { monos: cr });
    proof {
        lemma_take_ends(q.monos@);
        assert forall|pre: Frame, post: Frame, s: nat|
            facts_hold(pre, facts@) && #[trigger] eff_sound(eff_view(*e), pre, post, s)
                implies poly_val(post, *q) + poly_val(pre, r.1) <= poly_val(pre, r.0) by {
            assert(pull_ctx(e.rel@, facts@, pre, post));
        }
    }
    Some(r)
}

// ------------------------------------------------------------------ bounds under the edge's facts

/// `a`, raised by the first `Le(a, u)` or `Lt(a, u)`; a `Gap` keeps its subtrahend.
fn raise_atom(facts: &Vec<Fact>, a: &Atom) -> (r: Atom)
    ensures forall|fr: Frame| #[trigger] facts_hold(fr, facts@) ==> atom_val(fr, *a) <= atom_val(fr, r),
    decreases a,
{
    let mut i: usize = 0;
    while i < facts.len()
        invariant i <= facts@.len(),
        decreases facts.len() - i,
    {
        let u = match &facts[i] {
            Fact::Le(t, u) => if atom_eq(t, a) { Some(atom_copy(u)) } else { None },
            Fact::Lt(t, u) => if atom_eq(t, a) { Some(atom_copy(u)) } else { None },
        };
        if let Some(u) = u {
            proof {
                let gu = u;
                assert forall|fr: Frame| #[trigger] facts_hold(fr, facts@) implies atom_val(fr, *a) <= atom_val(fr, gu) by {
                    assert(fact_holds(fr, facts@[i as int]));
                }
            }
            return u;
        }
        i += 1;
    }
    match a {
        Atom::Gap(x, y) => {
            let x2 = raise_atom(facts, x);
            let r = Atom::Gap(Box::new(x2), Box::new(atom_copy(y)));
            proof {
                assert forall|fr: Frame| #[trigger] facts_hold(fr, facts@) implies atom_val(fr, *a) <= atom_val(fr, r) by {
                    assert(atom_val(fr, **x) <= atom_val(fr, x2));
                }
            }
            r
        },
        _ => {
            let r = atom_copy(a);
            proof {
                assert forall|fr: Frame| #[trigger] facts_hold(fr, facts@) implies atom_val(fr, *a) <= atom_val(fr, r) by {}
            }
            r
        },
    }
}

/// `m` with each atom raised. The coefficient stays, so nothing overflows.
fn raise_mono(facts: &Vec<Fact>, m: &Mono) -> (r: Option<Mono>)
    ensures r matches Some(u) ==> forall|fr: Frame| #[trigger] facts_hold(fr, facts@) ==> mono_val(fr, *m) <= mono_val(fr, u),
{
    if m.atoms.len() == 0 {
        let u = mono_copy(m);
        proof {
            assert forall|fr: Frame| #[trigger] facts_hold(fr, facts@) implies mono_val(fr, *m) <= mono_val(fr, u) by {
                lemma_atoms0(fr, m.atoms@);
                lemma_atoms0(fr, u.atoms@);
            }
        }
        Some(u)
    } else if m.atoms.len() == 1 {
        let a = raise_atom(facts, &m.atoms[0]);
        let mut atoms: Vec<Atom> = Vec::new();
        atoms.push(a);
        let u = Mono { coef: m.coef, atoms };
        proof {
            assert forall|fr: Frame| #[trigger] facts_hold(fr, facts@) implies mono_val(fr, *m) <= mono_val(fr, u) by {
                lemma_atoms1(fr, m.atoms@);
                lemma_atoms1(fr, u.atoms@);
                lemma_scale(m.coef as nat, atom_val(fr, m.atoms@[0]), atom_val(fr, u.atoms@[0]));
            }
        }
        Some(u)
    } else if m.atoms.len() == 2 {
        let a0 = raise_atom(facts, &m.atoms[0]);
        let a1 = raise_atom(facts, &m.atoms[1]);
        let mut atoms: Vec<Atom> = Vec::new();
        atoms.push(a0);
        atoms.push(a1);
        let u = Mono { coef: m.coef, atoms };
        proof {
            assert forall|fr: Frame| #[trigger] facts_hold(fr, facts@) implies mono_val(fr, *m) <= mono_val(fr, u) by {
                lemma_atoms2(fr, m.atoms@);
                lemma_atoms2(fr, u.atoms@);
                let (x0, x1, y0, y1) = (atom_val(fr, m.atoms@[0]), atom_val(fr, m.atoms@[1]), atom_val(fr, u.atoms@[0]), atom_val(fr, u.atoms@[1]));
                lemma_product_le(x0, y0, x1, y1);
                lemma_scale(m.coef as nat, x0 * x1, y0 * y1);
            }
        }
        Some(u)
    } else {
        None
    }
}

fn budget_has(budget: &Vec<Mono>, atoms: &Vec<Atom>) -> (r: bool) {
    let mut i: usize = 0;
    while i < budget.len()
        invariant i <= budget@.len(),
        decreases budget.len() - i,
    {
        if atoms_eq(&budget[i].atoms, atoms) { return true; }
        i += 1;
    }
    false
}

/// `pot` and the credits of the monomials of `p` that pull back.
fn make_budget(p: &Poly, pot: &Poly, e: &Eff, pre_facts: &Vec<Fact>) -> (r: Vec<Mono>) {
    let mut budget = poly_copy(pot).monos;
    let mut i: usize = 0;
    while i < p.monos.len()
        invariant i <= p.monos@.len(),
        decreases p.monos.len() - i,
    {
        if let Some((_, Some(c))) = pull_mono(&e.rel, pre_facts, &p.monos[i]) { budget.push(c); }
        i += 1;
    }
    budget
}

/// `p`, with what the block cannot pay as written raised under `post_facts`.
pub fn bound_post(p: &Poly, pot: &Poly, e: &Eff, pre_facts: &Vec<Fact>, post_facts: &Vec<Fact>) -> (r: Option<Poly>)
    ensures r matches Some(q) ==> forall|fr: Frame| #[trigger] facts_hold(fr, post_facts@) ==> poly_val(fr, q) >= poly_val(fr, *p),
{
    let budget = make_budget(p, pot, e, pre_facts);
    let mut out: Vec<Mono> = Vec::new();
    let mut i: usize = 0;
    while i < p.monos.len()
        invariant
            i <= p.monos@.len(),
            forall|fr: Frame| #[trigger] facts_hold(fr, post_facts@) ==> monos_val(fr, out@) >= monos_val(fr, p.monos@.take(i as int)),
        decreases p.monos.len() - i,
    {
        let m = &p.monos[i];
        let keep = match pull_mono(&e.rel, pre_facts, m) {
            Some((up, _)) => budget_has(&budget, &up.atoms),
            None => false,
        };
        let next = if keep {
            mono_copy(m)
        } else {
            match raise_mono(post_facts, m) { Some(u) => u, None => return None }
        };
        let ghost o0 = out@;
        proof {
            assert forall|fr: Frame| #[trigger] facts_hold(fr, post_facts@) implies mono_val(fr, *m) <= mono_val(fr, next) by {}
        }
        out.push(next);
        proof {
            assert forall|fr: Frame| #[trigger] facts_hold(fr, post_facts@) implies monos_val(fr, out@) >= monos_val(fr, p.monos@.take(i + 1)) by {
                assert(monos_val(fr, o0) >= monos_val(fr, p.monos@.take(i as int)));
                assert(mono_val(fr, *m) <= mono_val(fr, next));
                lemma_take_step(fr, p.monos@, i as int);
                lemma_monos_push(fr, o0, next);
            }
        }
        i += 1;
    }
    proof { lemma_take_ends(p.monos@); }
    Some(Poly { monos: out })
}

// ------------------------------------------------------------------ instantiating a summary

proof fn lemma_read_empty(fr: Frame, q: Place)
    requires q.proj@.len() == 0,
    ensures read_place(fr, q).0 == nth(fr.locals, q.local as nat),
{
    assert(walk(fr, q.proj@, 0, Cur::L(local_loc(q.local as nat))).0 == Cur::L(local_loc(q.local as nat)));
    assert(local_loc(q.local as nat).path.len() == 0);
}

pub open spec fn enter_frame(p: Program, g: nat, fr: Frame, args: Seq<Operand>) -> Frame { call_enter(p, g, fr, args).0 }

/// A callee local that is no parameter is `Unit` at entry.
proof fn lemma_enter_unit(p: Program, g: nat, fr: Frame, args: Seq<Operand>, j: usize)
    requires g < p.fns@.len(), !(1 <= j <= args.len() && (j as nat) < p.fns@[g as int].locals@.len()),
    ensures nth(enter_frame(p, g, fr, args).locals, j as nat) == Val::Unit,
{
}

/// A parameter copied from a local: the atoms read the same, through a `Mut`'s slot too.
proof fn lemma_enter_copy(p: Program, g: nat, fr: Frame, args: Seq<Operand>, j: usize, q: Place, ty: IntTy)
    requires
        g < p.fns@.len(), 1 <= j <= args.len(), (j as nat) < p.fns@[g as int].locals@.len(),
        args[j - 1] == Operand::Copy(q), q.proj@.len() == 0,
    ensures
        atom_val(enter_frame(p, g, fr, args), Atom::Val(j, ty)) == atom_val(fr, Atom::Val(q.local, ty)),
        atom_val(enter_frame(p, g, fr, args), Atom::Len(j)) == atom_val(fr, Atom::Len(q.local)),
{
    lemma_read_empty(fr, q);
    let cf = enter_frame(p, g, fr, args);
    let vs = op_vals(fr, args);
    assert(vs[j - 1] == nth(fr.locals, q.local as nat));
    assert(nth(cf.locals, j as nat) == cf.locals[j as int]);
    if let Val::Mut(l) = vs[j - 1] {
        let s = Loc { root: Root::Slot((j - 1) as nat), path: seq![] };
        assert(cf.locals[j as int] == Val::Mut(s));
        assert(cf.slots[j - 1] == read_loc(fr, l));
        assert(nth(cf.slots, (j - 1) as nat) == cf.slots[j - 1]);
        assert(read_loc(cf, s) == cf.slots[j - 1]);
    }
}

proof fn lemma_enter_const(p: Program, g: nat, fr: Frame, args: Seq<Operand>, j: usize, t: IntTy, n: u128)
    requires
        g < p.fns@.len(), 1 <= j <= args.len(), (j as nat) < p.fns@[g as int].locals@.len(),
        args[j - 1] == Operand::Const(t, n),
    ensures atom_val(enter_frame(p, g, fr, args), Atom::Val(j, t)) == uval(t, n) as nat,
{
    let cf = enter_frame(p, g, fr, args);
    assert(op_vals(fr, args)[j - 1] == Val::Int(n));
    assert(nth(cf.locals, j as nat) == cf.locals[j as int]);
}

fn is_param(p: &Program, g: usize, args: &Vec<Operand>, j: usize) -> (r: bool)
    requires g < p.fns@.len(),
    ensures r == (1 <= j <= args@.len() && (j as nat) < p.fns@[g as int].locals@.len()),
{
    1 <= j && j <= args.len() && j < p.fns[g].locals.len()
}

pub open spec fn inst_eq(p: Program, g: nat, args: Seq<Operand>, a: Atom, img: Atom) -> bool {
    forall|fr: Frame| #[trigger] atom_val(fr, img) == atom_val(enter_frame(p, g, fr, args), a)
}

#[allow(unused_variables)]
fn inst_val(p: &Program, g: usize, args: &Vec<Operand>, j: usize, ty: &IntTy) -> (r: Option<Atom>)
    requires g < p.fns@.len(),
    ensures r matches Some(img) ==> inst_eq(*p, g as nat, args@, Atom::Val(j, *ty), img),
{
    let a = Atom::Val(j, int_ty_copy(ty));
    if !is_param(p, g, args, j) {
        let r = Atom::Const(0);
        proof {
            assert forall|fr: Frame| #[trigger] atom_val(fr, r) == atom_val(enter_frame(*p, g as nat, fr, args@), a) by {
                lemma_enter_unit(*p, g as nat, fr, args@, j);
            }
        }
        return Some(r);
    }
    match &args[j - 1] {
        Operand::Copy(q) => if q.proj.len() == 0 {
            let r = Atom::Val(q.local, int_ty_copy(ty));
            proof {
                assert forall|fr: Frame| #[trigger] atom_val(fr, r) == atom_val(enter_frame(*p, g as nat, fr, args@), a) by {
                    lemma_enter_copy(*p, g as nat, fr, args@, j, *q, *ty);
                }
            }
            Some(r)
        } else {
            None
        },
        Operand::Const(t, n) => {
            let u = exec_uval(t, *n);
            if int_ty_eq(t, ty) && u <= u64::MAX as u128 {
                let r = Atom::Const(u as u64);
                proof {
                    assert forall|fr: Frame| #[trigger] atom_val(fr, r) == atom_val(enter_frame(*p, g as nat, fr, args@), a) by {
                        lemma_enter_const(*p, g as nat, fr, args@, j, *t, *n);
                    }
                }
                Some(r)
            } else {
                None
            }
        },
        _ => None,
    }
}

#[allow(unused_variables)]
fn inst_len(p: &Program, g: usize, args: &Vec<Operand>, j: usize) -> (r: Option<Atom>)
    requires g < p.fns@.len(),
    ensures r matches Some(img) ==> inst_eq(*p, g as nat, args@, Atom::Len(j), img),
{
    let a = Atom::Len(j);
    if !is_param(p, g, args, j) {
        let r = Atom::Const(0);
        proof {
            assert forall|fr: Frame| #[trigger] atom_val(fr, r) == atom_val(enter_frame(*p, g as nat, fr, args@), a) by {
                lemma_enter_unit(*p, g as nat, fr, args@, j);
            }
        }
        return Some(r);
    }
    match &args[j - 1] {
        Operand::Copy(q) => if q.proj.len() == 0 {
            let r = Atom::Len(q.local);
            proof {
                assert forall|fr: Frame| #[trigger] atom_val(fr, r) == atom_val(enter_frame(*p, g as nat, fr, args@), a) by {
                    lemma_enter_copy(*p, g as nat, fr, args@, j, *q, IntTy::Usize);
                }
            }
            Some(r)
        } else {
            None
        },
        _ => None,
    }
}

fn inst_atom(p: &Program, g: usize, args: &Vec<Operand>, a: &Atom) -> (r: Option<Atom>)
    requires g < p.fns@.len(),
    ensures r matches Some(img) ==> inst_eq(*p, g as nat, args@, *a, img),
    decreases a,
{
    match a {
        Atom::Const(c) => {
            let r = Atom::Const(*c);
            proof {
                assert forall|fr: Frame| #[trigger] atom_val(fr, r) == atom_val(enter_frame(*p, g as nat, fr, args@), *a) by {}
            }
            Some(r)
        },
        Atom::Val(j, ty) => inst_val(p, g, args, *j, ty),
        Atom::Len(j) => inst_len(p, g, args, *j),
        Atom::Gap(x, y) => match (inst_atom(p, g, args, x), inst_atom(p, g, args, y)) {
            (Some(x2), Some(y2)) => {
                let ghost (gx, gy) = (x2, y2);
                let r = Atom::Gap(Box::new(x2), Box::new(y2));
                proof {
                    assert forall|fr: Frame| #[trigger] atom_val(fr, r) == atom_val(enter_frame(*p, g as nat, fr, args@), *a) by {
                        assert(atom_val(fr, gx) == atom_val(enter_frame(*p, g as nat, fr, args@), **x));
                        assert(atom_val(fr, gy) == atom_val(enter_frame(*p, g as nat, fr, args@), **y));
                    }
                }
                Some(r)
            },
            _ => None,
        },
    }
}

pub open spec fn mono_inst(p: Program, g: nat, args: Seq<Operand>, m: Mono, q: Mono) -> bool {
    forall|fr: Frame| #[trigger] mono_val(fr, q) == mono_val(enter_frame(p, g, fr, args), m)
}

fn inst_mono(p: &Program, g: usize, args: &Vec<Operand>, m: &Mono) -> (r: Option<Mono>)
    requires g < p.fns@.len(),
    ensures r matches Some(q) ==> mono_inst(*p, g as nat, args@, *m, q),
{
    if m.atoms.len() == 0 {
        let q = mono_copy(m);
        proof {
            assert forall|fr: Frame| #[trigger] mono_val(fr, q) == mono_val(enter_frame(*p, g as nat, fr, args@), *m) by {
                lemma_atoms0(fr, q.atoms@);
                lemma_atoms0(enter_frame(*p, g as nat, fr, args@), m.atoms@);
            }
        }
        Some(q)
    } else if m.atoms.len() == 1 {
        match inst_atom(p, g, args, &m.atoms[0]) {
            Some(a) => {
                let ghost ga = a;
                let r = fold1(m.coef, a);
                proof {
                    if r is Some {
                        let q = r.unwrap();
                        assert forall|fr: Frame| #[trigger] mono_val(fr, q) == mono_val(enter_frame(*p, g as nat, fr, args@), *m) by {
                            lemma_atoms1(enter_frame(*p, g as nat, fr, args@), m.atoms@);
                            assert(atom_val(fr, ga) == atom_val(enter_frame(*p, g as nat, fr, args@), m.atoms@[0]));
                        }
                    }
                }
                r
            },
            None => None,
        }
    } else if m.atoms.len() == 2 {
        match (inst_atom(p, g, args, &m.atoms[0]), inst_atom(p, g, args, &m.atoms[1])) {
            (Some(a0), Some(a1)) => {
                let ghost (g0, g1) = (a0, a1);
                let r = fold2(m.coef, a0, a1);
                proof {
                    if r is Some {
                        let q = r.unwrap();
                        assert forall|fr: Frame| #[trigger] mono_val(fr, q) == mono_val(enter_frame(*p, g as nat, fr, args@), *m) by {
                            lemma_atoms2(enter_frame(*p, g as nat, fr, args@), m.atoms@);
                            assert(atom_val(fr, g0) == atom_val(enter_frame(*p, g as nat, fr, args@), m.atoms@[0]));
                            assert(atom_val(fr, g1) == atom_val(enter_frame(*p, g as nat, fr, args@), m.atoms@[1]));
                        }
                    }
                }
                r
            },
            _ => None,
        }
    } else {
        None
    }
}

/// A callee's summary, over the caller's frame at the call.
pub fn instantiate(sum: &Poly, p: &Program, g: usize, args: &Vec<Operand>) -> (r: Option<Poly>)
    ensures r matches Some(q) ==> forall|fr: Frame| #[trigger] poly_val(fr, q) >= poly_val(call_enter(*p, g as nat, fr, args@).0, *sum),
{
    if g >= p.fns.len() { return None; }
    let mut out: Vec<Mono> = Vec::new();
    let mut i: usize = 0;
    while i < sum.monos.len()
        invariant
            i <= sum.monos@.len(), g < p.fns@.len(),
            forall|fr: Frame| #[trigger] monos_val(fr, out@) == monos_val(enter_frame(*p, g as nat, fr, args@), sum.monos@.take(i as int)),
        decreases sum.monos.len() - i,
    {
        match inst_mono(p, g, args, &sum.monos[i]) {
            Some(q) => {
                let ghost (o0, gq) = (out@, q);
                out.push(q);
                proof {
                    assert forall|fr: Frame| #[trigger] monos_val(fr, out@) == monos_val(enter_frame(*p, g as nat, fr, args@), sum.monos@.take(i + 1)) by {
                        let cf = enter_frame(*p, g as nat, fr, args@);
                        assert(monos_val(fr, o0) == monos_val(cf, sum.monos@.take(i as int)));
                        assert(mono_val(fr, gq) == mono_val(cf, sum.monos@[i as int]));
                        lemma_monos_push(fr, o0, gq);
                        lemma_take_step(cf, sum.monos@, i as int);
                    }
                }
            },
            None => return None,
        }
        i += 1;
    }
    let q = Poly { monos: out };
    proof {
        lemma_take_ends(sum.monos@);
        assert forall|fr: Frame| #[trigger] poly_val(fr, q) >= poly_val(call_enter(*p, g as nat, fr, args@).0, *sum) by {
            assert(monos_val(fr, out@) == monos_val(enter_frame(*p, g as nat, fr, args@), sum.monos@.take(sum.monos@.len() as int)));
        }
    }
    Some(q)
}

// ------------------------------------------------------------------ charges

/// What the terminator owes beyond its own step, at the frame after the statements.
pub open spec fn charge_covers(p: Program, t: Term, sums: Seq<Option<Poly>>, charge: Poly, fr1: Frame) -> bool {
    match t {
        Term::Call(Callee::Intr(i), args, _, _) => intr_cost(i, fr1, args@) <= poly_val(fr1, charge),
        Term::Call(Callee::Fn(g), args, _, _) =>
            sums[g as int] is Some && poly_val(call_enter(p, g as nat, fr1, args@).0, sums[g as int].unwrap()) <= poly_val(fr1, charge),
        _ => true,
    }
}

fn empty_poly() -> (r: Poly)
    ensures forall|fr: Frame| #[trigger] poly_val(fr, r) == 0,
{
    let r = Poly { monos: Vec::new() };
    proof {
        assert forall|fr: Frame| #[trigger] poly_val(fr, r) == 0 by {
            lemma_monos_empty(fr, r.monos@);
        }
    }
    r
}

/// `Len(y)` for an operand reading local `y`: a len-cost intrinsic's cost.
fn len_charge(args: &Vec<Operand>, i: usize) -> (r: Option<Poly>)
    ensures r matches Some(ch) ==> forall|fr: Frame| #[trigger] poly_val(fr, ch) >= elems(fr, nth(op_vals(fr, args@), i as nat)).len(),
{
    if i >= args.len() { return None; }
    match &args[i] {
        Operand::Copy(q) => if q.proj.len() == 0 {
            let y = q.local;
            let mut atoms: Vec<Atom> = Vec::new();
            atoms.push(Atom::Len(y));
            let m = Mono { coef: 1, atoms };
            let mut monos: Vec<Mono> = Vec::new();
            monos.push(m);
            let ch = Poly { monos };
            proof {
                assert forall|fr: Frame| #[trigger] poly_val(fr, ch) >= elems(fr, nth(op_vals(fr, args@), i as nat)).len() by {
                    lemma_read_empty(fr, *q);
                    let v = nth(fr.locals, y as nat);
                    assert(nth(op_vals(fr, args@), i as nat) == v);
                    lemma_elems_le_len_nat(fr, v);
                    lemma_atoms1(fr, m.atoms@);
                    assert(ch.monos@ =~= Seq::<Mono>::empty().push(m));
                    lemma_monos_empty(fr, Seq::<Mono>::empty());
                    lemma_monos_push(fr, Seq::<Mono>::empty(), m);
                    assert(atom_val(fr, m.atoms@[0]) == len_nat(fr, v));
                }
            }
            Some(ch)
        } else {
            None
        },
        _ => None,
    }
}

pub fn term_charge(p: &Program, t: &Term, sums: &Vec<Option<Poly>>) -> (r: Option<Poly>)
    ensures r matches Some(ch) ==> forall|fr: Frame| #[trigger] charge_covers(*p, *t, sums@, ch, fr),
{
    match t {
        Term::Call(Callee::Fn(g), args, _, _) => {
            if *g >= sums.len() { return None; }
            match &sums[*g] {
                Some(sum) => {
                    let r = instantiate(sum, p, *g, args);
                    proof {
                        if r is Some {
                            let ch = r.unwrap();
                            assert forall|fr: Frame| #[trigger] charge_covers(*p, *t, sums@, ch, fr) by {
                                assert(poly_val(fr, ch) >= poly_val(call_enter(*p, *g as nat, fr, args@).0, *sum));
                            }
                        }
                    }
                    r
                },
                None => None,
            }
        },
        Term::Call(Callee::Intr(k), args, _, _) => match k {
            Intrinsic::SliceToVec => {
                let r = len_charge(args, 0);
                proof {
                    if r is Some {
                        let ch = r.unwrap();
                        assert forall|fr: Frame| #[trigger] charge_covers(*p, *t, sums@, ch, fr) by {
                            assert(poly_val(fr, ch) >= elems(fr, nth(op_vals(fr, args@), 0)).len());
                        }
                    }
                }
                r
            },
            Intrinsic::VecExtendFromSlice => {
                let r = len_charge(args, 1);
                proof {
                    if r is Some {
                        let ch = r.unwrap();
                        assert forall|fr: Frame| #[trigger] charge_covers(*p, *t, sums@, ch, fr) by {
                            assert(poly_val(fr, ch) >= elems(fr, nth(op_vals(fr, args@), 1)).len());
                        }
                    }
                }
                r
            },
            _ => {
                let ch = empty_poly();
                proof {
                    assert forall|fr: Frame| #[trigger] charge_covers(*p, *t, sums@, ch, fr) by {
                        assert(poly_val(fr, ch) == 0);
                    }
                }
                Some(ch)
            },
        },
        _ => {
            let ch = empty_poly();
            proof {
                assert forall|fr: Frame| #[trigger] charge_covers(*p, *t, sums@, ch, fr) by {}
            }
            Some(ch)
        },
    }
}

// ------------------------------------------------------------------ edges

/// Edge `j`'s successor exists, its facts follow, and `pot` pays `k1`, the charge and its potential.
pub open spec fn edge_ok(c: Cert, e: SymEff, facts: Seq<Fact>, pot: Poly, upc: Poly, crc: Poly, k1: nat, j: int) -> bool {
    let t = e.edge[j].0;
    &&& (t as nat) < c.blocks@.len()
    &&& forall|pre: Frame, post: Frame, s: nat| facts_hold(pre, facts) && #[trigger] eff_sound(e, pre, post, s) && facts_hold(post, e.edge[j].1)
        ==> facts_hold(post, c.blocks@[t as int].facts@)
            && poly_val(pre, pot) + poly_val(pre, crc) >= k1 + poly_val(post, c.blocks@[t as int].pot) + poly_val(pre, upc)
}

fn check_edge(c: &Cert, e: &Eff, facts: &Vec<Fact>, pot: &Poly, upc: &Poly, crc: &Poly, k1: u64, i: usize) -> (r: bool)
    requires i < e.edge@.len(),
    ensures r ==> edge_ok(*c, eff_view(*e), facts@, *pot, *upc, *crc, k1 as nat, i as int),
{
    let t = e.edge[i].0;
    let post_facts = &e.edge[i].1;
    if t >= c.blocks.len() { return false; }
    let s = &c.blocks[t];
    if !facts_imply(post_facts, &s.facts) { return false; }
    let need = match bound_post(&s.pot, pot, e, facts, post_facts) { Some(n) => n, None => return false };
    let (up, cr) = match pull_post(&need, e, facts) { Some(x) => x, None => return false };
    let l1 = match poly_add(pot, &cr) { Some(x) => x, None => return false };
    let lhs = match poly_add(&l1, crc) { Some(x) => x, None => return false };
    let rhs = match poly_add(&up, upc) { Some(x) => x, None => return false };
    if !poly_dominates(&lhs, &rhs, k1) { return false; }
    proof {
        let ev = eff_view(*e);
        assert(ev.edge[i as int] == (t, post_facts@));
        assert forall|pre: Frame, post: Frame, n: nat| facts_hold(pre, facts@) && #[trigger] eff_sound(ev, pre, post, n) && facts_hold(post, ev.edge[i as int].1)
            implies facts_hold(post, c.blocks@[t as int].facts@)
                && poly_val(pre, *pot) + poly_val(pre, *crc) >= k1 as nat + poly_val(post, c.blocks@[t as int].pot) + poly_val(pre, *upc) by {
            assert(facts_hold(post, post_facts@));
            assert(poly_val(post, need) >= poly_val(post, s.pot));
            assert(poly_val(post, need) + poly_val(pre, cr) <= poly_val(pre, up));
            assert(poly_val(pre, lhs) >= poly_val(pre, rhs) + k1);
            assert(poly_val(pre, lhs) == poly_val(pre, l1) + poly_val(pre, *crc));
            assert(poly_val(pre, l1) == poly_val(pre, *pot) + poly_val(pre, cr));
            assert(poly_val(pre, rhs) == poly_val(pre, up) + poly_val(pre, *upc));
        }
    }
    true
}

pub open spec fn edges_ok(c: Cert, e: SymEff, facts: Seq<Fact>, pot: Poly, upc: Poly, crc: Poly, k1: nat) -> bool {
    forall|j: int| 0 <= j < e.edge.len() ==> #[trigger] edge_ok(c, e, facts, pot, upc, crc, k1, j)
}

fn check_edges(c: &Cert, e: &Eff, facts: &Vec<Fact>, pot: &Poly, upc: &Poly, crc: &Poly, k1: u64) -> (r: bool)
    ensures r ==> edges_ok(*c, eff_view(*e), facts@, *pot, *upc, *crc, k1 as nat),
{
    let mut i: usize = 0;
    while i < e.edge.len()
        invariant i <= e.edge@.len(), forall|j: int| 0 <= j < i ==> #[trigger] edge_ok(*c, eff_view(*e), facts@, *pot, *upc, *crc, k1 as nat, j),
        decreases e.edge.len() - i,
    {
        if !check_edge(c, e, facts, pot, upc, crc, k1, i) { return false; }
        i += 1;
    }
    true
}

/// The edge taken pays. The charge is any value `crc` and `upc` cover.
proof fn lemma_edge_taken(c: Cert, e: SymEff, facts: Seq<Fact>, pot: Poly, upc: Poly, crc: Poly, k1: nat, pre: Frame, post: Frame, t: usize, i: int, chg: nat)
    requires
        edges_ok(c, e, facts, pot, upc, crc, k1), facts_hold(pre, facts), eff_sound(e, pre, post, t as nat),
        0 <= i < e.edge.len(), e.edge[i].0 == t, chg + poly_val(pre, crc) <= poly_val(pre, upc),
    ensures
        facts_hold(post, c.blocks@[t as int].facts@),
        poly_val(pre, pot) >= k1 + chg + poly_val(post, c.blocks@[t as int].pot),
{
    assert(edge_ok(c, e, facts, pot, upc, crc, k1, i));
    assert(e.edge[i].0 as nat == t as nat);
    assert(facts_hold(post, e.edge[i].1));
}

proof fn lemma_switch_index(ts: Seq<(u128, usize)>, k: nat, v: u128, o: usize) -> (i: int)
    requires k <= ts.len(),
    ensures k <= i <= ts.len(), switch_target(ts, k, v, o) == (if i < ts.len() { ts[i].1 } else { o }),
    decreases ts.len() - k,
{
    if k == ts.len() { k as int } else if ts[k as int].0 == v { k as int } else { lemma_switch_index(ts, k + 1, v, o) }
}

// ------------------------------------------------------------------ one block, by terminator

/// What `check_cost_block` establishes, at one frame.
pub open spec fn block_premises(p: Program, f: nat, b: nat, c: Cert, sums: Seq<Option<Poly>>, fr: Frame, upc: Poly, crc: Poly, charge: Poly) -> bool {
    let blk = p.fns@[f as int].blocks@[b as int];
    let facts = c.blocks@[b as int].facts@;
    let fr1 = exec_stmts(blk.stmts@, 0, fr).0;
    &&& edges_ok(c, sym_block(p.fns@[f as int], blk, facts), facts, c.blocks@[b as int].pot, upc, crc, blk.stmts@.len() + 1)
    &&& poly_val(fr1, charge) + poly_val(fr, crc) <= poly_val(fr, upc)
    &&& charge_covers(p, blk.term, sums, charge, fr1)
    &&& blk.term is Return ==> poly_val(fr, c.blocks@[b as int].pot) >= blk.stmts@.len() + 1
}

proof fn lemma_block_call(p: Program, ls: Seq<FnLab>, f: nat, b: nat, c: Cert, sums: Seq<Option<Poly>>, fr: Frame, upc: Poly, crc: Poly, charge: Poly)
    requires
        ok_prog(p, ls), f < p.fns@.len(), b < p.fns@[f as int].blocks@.len(), plc(p, ls, f, fr),
        facts_hold(fr, c.blocks@[b as int].facts@), frame_len_ok(fr),
        block_premises(p, f, b, c, sums, fr, upc, crc, charge),
        p.fns@[f as int].blocks@[b as int].term matches Term::Call(Callee::Fn(_), _, _, _),
    ensures block_step_ok(p, f, b, c, sums, fr),
{
    let blk = p.fns@[f as int].blocks@[b as int];
    let facts = c.blocks@[b as int].facts@;
    let k = blk.stmts@.len();
    let fr1 = exec_stmts(blk.stmts@, 0, fr).0;
    let e = sym_block(p.fns@[f as int], blk, facts);
    let pot = poly_val(fr, c.blocks@[b as int].pot);
    if let Term::Call(Callee::Fn(g), args, dst, next) = blk.term {
        let (cf, wb, _) = call_enter(p, g as nat, fr1, args@);
        lemma_sym_block_sound(p, ls, f, b, blk, facts, fr);
        assert forall|out: Frame, n: nat| frame_len_ok(out) && n <= poly_val(cf, sums[g as int].unwrap())
            implies #[trigger] call_out_ok(c, next as nat, pot, k, fr1, wb, dst, out, n) by {
            let post = call_leave(fr1, out, wb, dst).0;
            assert(eff_sound(e, fr, post, next as nat));
            assert(e.edge[0] == (next, carry(e.rel, facts)));
            lemma_edge_taken(c, e, facts, c.blocks@[b as int].pot, upc, crc, k + 1, fr, post, next, 0, poly_val(fr1, charge));
        }
    }
}

proof fn lemma_block_intr(p: Program, ls: Seq<FnLab>, f: nat, b: nat, c: Cert, sums: Seq<Option<Poly>>, fr: Frame, upc: Poly, crc: Poly, charge: Poly)
    requires
        ok_prog(p, ls), f < p.fns@.len(), b < p.fns@[f as int].blocks@.len(), plc(p, ls, f, fr),
        facts_hold(fr, c.blocks@[b as int].facts@), frame_len_ok(fr),
        block_premises(p, f, b, c, sums, fr, upc, crc, charge),
        p.fns@[f as int].blocks@[b as int].term matches Term::Call(Callee::Intr(_), _, _, _),
    ensures block_step_ok(p, f, b, c, sums, fr),
{
    let blk = p.fns@[f as int].blocks@[b as int];
    let facts = c.blocks@[b as int].facts@;
    let fr1 = exec_stmts(blk.stmts@, 0, fr).0;
    let e = sym_block(p.fns@[f as int], blk, facts);
    if let Term::Call(Callee::Intr(i), args, dst, next) = blk.term {
        if let Some((fr2, _, extra)) = exec_intr(i, fr1, args@, dst) {
            lemma_sym_block_sound(p, ls, f, b, blk, facts, fr);
            assert(eff_sound(e, fr, fr2, next as nat));
            assert(e.edge[0] == (next, carry(e.rel, facts)));
            lemma_edge_taken(c, e, facts, c.blocks@[b as int].pot, upc, crc, blk.stmts@.len() + 1, fr, fr2, next, 0, poly_val(fr1, charge));
        }
    }
}

proof fn lemma_block_jump(p: Program, ls: Seq<FnLab>, f: nat, b: nat, c: Cert, sums: Seq<Option<Poly>>, fr: Frame, upc: Poly, crc: Poly, charge: Poly)
    requires
        ok_prog(p, ls), f < p.fns@.len(), b < p.fns@[f as int].blocks@.len(), plc(p, ls, f, fr),
        facts_hold(fr, c.blocks@[b as int].facts@), frame_len_ok(fr),
        block_premises(p, f, b, c, sums, fr, upc, crc, charge),
        !(p.fns@[f as int].blocks@[b as int].term is Call),
    ensures block_step_ok(p, f, b, c, sums, fr),
{
    let blk = p.fns@[f as int].blocks@[b as int];
    let facts = c.blocks@[b as int].facts@;
    let k1 = blk.stmts@.len() + 1;
    let fr1 = exec_stmts(blk.stmts@, 0, fr).0;
    let e = sym_block(p.fns@[f as int], blk, facts);
    let chg = poly_val(fr1, charge);
    let pot = c.blocks@[b as int].pot;
    lemma_sym_block_sound(p, ls, f, b, blk, facts, fr);
    match blk.term {
        Term::Goto(b2) => {
            assert(e.edge[0] == (b2, carry(e.rel, facts)));
            lemma_edge_taken(c, e, facts, pot, upc, crc, k1, fr, fr1, b2, 0, chg);
        },
        Term::Switch(op, ts, o) => {
            let t = switch_target(ts@, 0, as_int(eval_op(fr1, op).0), o);
            let i = lemma_switch_index(ts@, 0, as_int(eval_op(fr1, op).0), o);
            assert(e.edge[i].0 == t);
            lemma_edge_taken(c, e, facts, pot, upc, crc, k1, fr, fr1, t, i, chg);
        },
        Term::Assert(op, expected, b2) => if (as_int(eval_op(fr1, op).0) != 0) == expected {
            assert(e.edge[0].0 == b2);
            lemma_edge_taken(c, e, facts, pot, upc, crc, k1, fr, fr1, b2, 0, chg);
        },
        _ => {},
    }
}

/// The per-frame premises give the obligation, one case lemma per kind of terminator.
proof fn lemma_block_ok(p: Program, ls: Seq<FnLab>, f: nat, b: nat, c: Cert, sums: Seq<Option<Poly>>, fr: Frame, upc: Poly, crc: Poly, charge: Poly)
    requires
        ok_prog(p, ls), f < p.fns@.len(), b < p.fns@[f as int].blocks@.len(), plc(p, ls, f, fr),
        facts_hold(fr, c.blocks@[b as int].facts@), frame_len_ok(fr),
        block_premises(p, f, b, c, sums, fr, upc, crc, charge),
    ensures block_step_ok(p, f, b, c, sums, fr),
{
    match p.fns@[f as int].blocks@[b as int].term {
        Term::Call(Callee::Fn(_), _, _, _) => lemma_block_call(p, ls, f, b, c, sums, fr, upc, crc, charge),
        Term::Call(Callee::Intr(_), _, _, _) => lemma_block_intr(p, ls, f, b, c, sums, fr, upc, crc, charge),
        _ => lemma_block_jump(p, ls, f, b, c, sums, fr, upc, crc, charge),
    }
}

pub open spec fn block_checked(p: Program, f: nat, b: nat, c: Cert, sums: Seq<Option<Poly>>) -> bool {
    forall|ls: Seq<FnLab>, fr: Frame| #![trigger plc(p, ls, f, fr), block_step_ok(p, f, b, c, sums, fr)]
        ok_prog(p, ls) && plc(p, ls, f, fr) && facts_hold(fr, c.blocks@[b as int].facts@) && frame_len_ok(fr)
            ==> block_step_ok(p, f, b, c, sums, fr)
}

/// `Return`'s and `Abort`'s obligation, and every other terminator's through its edges.
pub fn check_cost_block(p: &Program, f: usize, b: usize, c: &Cert, sums: &Vec<Option<Poly>>) -> (r: bool)
    ensures r ==> block_checked(*p, f as nat, b as nat, *c, sums@),
{
    if f >= p.fns.len() { return false; }
    let body = &p.fns[f];
    if b >= body.blocks.len() || c.blocks.len() != body.blocks.len() { return false; }
    let blk = &body.blocks[b];
    let facts = &c.blocks[b].facts;
    let pot = &c.blocks[b].pot;
    let k = blk.stmts.len() as u64;
    if k == u64::MAX { return false; }
    let k1 = k + 1;
    if let Term::Abort = &blk.term {
        return check_abort(p, f, b, c, sums);
    }
    let none = empty_poly();
    if let Term::Return = &blk.term {
        if !poly_dominates(pot, &none, k1) { return false; }
    }
    let e = exec_sym_block(body, blk, facts);
    let es = exec_sym_stmts(body, &blk.stmts, facts);
    let charge = match term_charge(p, &blk.term, sums) { Some(x) => x, None => return false };
    let (upc, crc) = match pull_post(&charge, &es, facts) { Some(x) => x, None => return false };
    if !check_edges(c, &e, facts, pot, &upc, &crc, k1) { return false; }
    proof {
        assert forall|ls: Seq<FnLab>, fr: Frame| #![trigger plc(*p, ls, f as nat, fr), block_step_ok(*p, f as nat, b as nat, *c, sums@, fr)]
            ok_prog(*p, ls) && plc(*p, ls, f as nat, fr) && facts_hold(fr, c.blocks@[b as int].facts@) && frame_len_ok(fr)
                implies block_step_ok(*p, f as nat, b as nat, *c, sums@, fr) by {
            lemma_sym_stmts_sound(*p, ls, f as nat, b as nat, *blk, facts@, fr);
            let fr1 = exec_stmts(blk.stmts@, 0, fr).0;
            assert(eff_sound(eff_view(es), fr, fr1, 0));
            assert(poly_val(fr1, charge) + poly_val(fr, crc) <= poly_val(fr, upc));
            assert(charge_covers(*p, blk.term, sums@, charge, fr1));
            if blk.term is Return { assert(poly_val(fr, *pot) >= poly_val(fr, none) + k1); }
            lemma_block_ok(*p, ls, f as nat, b as nat, *c, sums@, fr, upc, crc, charge);
        }
    }
    true
}

#[allow(unused_variables)]
fn check_abort(p: &Program, f: usize, b: usize, c: &Cert, sums: &Vec<Option<Poly>>) -> (r: bool)
    requires f < p.fns@.len(), b < p.fns@[f as int].blocks@.len(), p.fns@[f as int].blocks@[b as int].term is Abort,
    ensures r, block_checked(*p, f as nat, b as nat, *c, sums@),
{
    true
}

// ------------------------------------------------------------------ certificates

/// Equal coefficients and atom lists, monomial by monomial.
pub fn poly_eq(a: &Poly, b: &Poly) -> (r: bool)
    ensures r ==> poly_same(*a, *b),
{
    if a.monos.len() != b.monos.len() { return false; }
    let mut i: usize = 0;
    while i < a.monos.len()
        invariant
            i <= a.monos@.len(), a.monos@.len() == b.monos@.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] mono_view_eq(a.monos@[j], b.monos@[j]),
        decreases a.monos.len() - i,
    {
        if a.monos[i].coef != b.monos[i].coef || !atoms_eq(&a.monos[i].atoms, &b.monos[i].atoms) { return false; }
        i += 1;
    }
    true
}

/// A certificate's `true` is `cert_for`: every block's obligation, empty entry facts, and the
/// entry's potential as `f`'s summary. Only with `check_program` `Ok`: `cert_sem_ok` has `ok_prog` as a hypothesis.
pub fn check_cert(p: &Program, f: usize, c: &Cert, sums: &Vec<Option<Poly>>) -> (r: bool)
    ensures r ==> cert_for(*p, f as nat, *c, sums@),
{
    if f >= p.fns.len() || f >= sums.len() || c.blocks.len() != p.fns[f].blocks.len() || c.blocks.len() == 0 { return false; }
    if c.blocks[0].facts.len() != 0 { return false; }
    match &sums[f] {
        Some(s) => if !poly_eq(s, &c.blocks[0].pot) { return false; },
        None => return false,
    }
    let mut b: usize = 0;
    while b < c.blocks.len()
        invariant
            b <= c.blocks@.len(), c.blocks@.len() == p.fns@[f as int].blocks@.len(), f < p.fns@.len(), f < sums@.len(),
            c.blocks@.len() > 0, c.blocks@[0].facts@.len() == 0, sums@[f as int] is Some,
            poly_same(sums@[f as int].unwrap(), c.blocks@[0].pot),
            forall|i: nat| i < b ==> #[trigger] block_checked(*p, f as nat, i, *c, sums@),
        decreases c.blocks.len() - b,
    {
        if !poly_canonical(&c.blocks[b].pot) || !check_cost_block(p, f, b, c, sums) { return false; }
        b += 1;
    }
    proof {
        let (pp, ff, cc, ss) = (*p, f as nat, *c, sums@);
        assert forall|ls: Seq<FnLab>, i: nat, fr: Frame| #![trigger plc(pp, ls, ff, fr), block_step_ok(pp, ff, i, cc, ss, fr)]
            i < cc.blocks@.len() && ok_prog(pp, ls) && plc(pp, ls, ff, fr)
                && facts_hold(fr, cc.blocks@[i as int].facts@) && frame_len_ok(fr)
                implies block_step_ok(pp, ff, i, cc, ss, fr) by {
            assert(block_checked(pp, ff, i, cc, ss));
        }
    }
    true
}

} // verus!
