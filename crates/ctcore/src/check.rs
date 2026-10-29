//! The verified exec checker: each fn computes its `ct.rs` spec exactly, so `check_prog(p, ls)`
//! returns `ok_prog(p, ls)`, the premise of `theorem_ct`.
//!
//! The specs read labels and bodies without bounds checks, so the fns below `check_prog` take as
//! premises the facts `check_prog` establishes first: `wf`, and one label per local (`labs_ok`).
#[allow(unused_imports)]
use crate::ct::*;
#[allow(unused_imports)]
use crate::syntax::*;
use vstd::prelude::*;

verus! {

/// One label vector per fn, with one label per local.
pub open spec fn labs_ok(p: Program, ls: Seq<FnLab>) -> bool {
    &&& ls.len() == p.fns@.len()
    &&& forall|g: int| 0 <= g < ls.len() ==> (#[trigger] ls[g]).locals@.len() == p.fns@[g].locals@.len()
}

/// The body-level premise: `l` has one label per local of `b`.
pub open spec fn lab_len(b: Body, l: FnLab) -> bool { l.locals@.len() == b.locals@.len() }

// ------------------------------------------------------------------ wf

#[verifier::loop_isolation(false)]
pub fn check_ty_has_mut(t: &Ty) -> (r: bool)
    ensures r == ty_has_mut(*t),
    decreases t,
{
    match t {
        Ty::Int(_) => false,
        Ty::Unit => false,
        Ty::Tuple(ts) => {
            let mut i: usize = 0;
            while i < ts.len()
                invariant i <= ts@.len(), forall|k: int| 0 <= k < i ==> !ty_has_mut(#[trigger] ts@[k]),
                decreases ts.len() - i,
            {
                if check_ty_has_mut(&ts[i]) { return true; }
                i += 1;
            }
            false
        },
        Ty::Adt(vs) => {
            let mut i: usize = 0;
            while i < vs.len()
                invariant
                    i <= vs@.len(),
                    forall|a: int, k: int| 0 <= a < i && 0 <= k < vs@[a]@.len() ==> !ty_has_mut(#[trigger] vs@[a]@[k]),
                decreases vs.len() - i,
            {
                let ts = &vs[i];
                let mut k: usize = 0;
                while k < ts.len()
                    invariant
                        i < vs@.len(), *ts == vs@[i as int], k <= ts@.len(),
                        forall|a: int, kk: int| 0 <= a < i && 0 <= kk < vs@[a]@.len() ==> !ty_has_mut(#[trigger] vs@[a]@[kk]),
                        forall|kk: int| 0 <= kk < k ==> !ty_has_mut(#[trigger] ts@[kk]),
                    decreases ts.len() - k,
                {
                    if check_ty_has_mut(&ts[k]) {
                        assert(ty_has_mut(vs@[i as int]@[k as int]));
                        return true;
                    }
                    k += 1;
                }
                i += 1;
            }
            false
        },
        Ty::Array(e, _) => check_ty_has_mut(e),
        Ty::Slice(e) => check_ty_has_mut(e),
        Ty::Vec(e) => check_ty_has_mut(e),
        Ty::Shr(e) => check_ty_has_mut(e),
        Ty::Mut(_) => true,
    }
}

pub fn check_wf_local_ty(t: &Ty) -> (r: bool)
    ensures r == wf_local_ty(*t),
{
    match t {
        Ty::Mut(inner) => !check_ty_has_mut(inner),
        _ => !check_ty_has_mut(t),
    }
}

#[verifier::loop_isolation(false)]
pub fn check_wf_term(p: &Program, f: usize, t: &Term) -> (r: bool)
    requires f < p.fns@.len(),
    ensures r == wf_term(*p, f as nat, *t),
{
    let n = p.fns[f].blocks.len();
    match t {
        Term::Goto(b) => *b < n,
        Term::Switch(_, ts, o) => {
            if *o >= n { return false; }
            let mut k: usize = 0;
            while k < ts.len()
                invariant k <= ts@.len(), forall|j: int| 0 <= j < k ==> (#[trigger] ts@[j]).1 < n,
                decreases ts.len() - k,
            {
                if ts[k].1 >= n {
                    assert(ts@[k as int].1 >= n);
                    return false;
                }
                k += 1;
            }
            true
        },
        Term::Assert(_, _, b) => *b < n,
        Term::Call(Callee::Fn(g), args, _, next) => *g < p.fns.len() && args.len() == p.fns[*g].nargs && *next < n,
        Term::Call(Callee::Intr(_), _, _, next) => *next < n,
        Term::Return => true,
        Term::Abort => true,
    }
}

#[verifier::loop_isolation(false)]
pub fn check_wf_body(p: &Program, f: usize) -> (r: bool)
    requires f < p.fns@.len(),
    ensures r == wf_body(*p, f as nat),
{
    let b = &p.fns[f];
    if b.blocks.len() < 1 || b.nargs >= b.locals.len() || check_ty_has_mut(&b.locals[0]) { return false; }
    let mut i: usize = 1;
    while i < b.locals.len()
        invariant 1 <= i <= b.locals@.len(), forall|k: int| 0 < k < i ==> wf_local_ty(#[trigger] b.locals@[k]),
        decreases b.locals.len() - i,
    {
        if !check_wf_local_ty(&b.locals[i]) { return false; }
        i += 1;
    }
    let mut i: usize = 0;
    while i < b.blocks.len()
        invariant
            i <= b.blocks@.len(),
            forall|k: int| 0 < k < b.locals@.len() ==> wf_local_ty(#[trigger] b.locals@[k]),
            forall|k: int| 0 <= k < i ==> #[trigger] wf_block(*p, f as nat, b.blocks@[k]),
        decreases b.blocks.len() - i,
    {
        if !check_wf_term(p, f, &b.blocks[i].term) {
            assert(!wf_block(*p, f as nat, b.blocks@[i as int]));
            return false;
        }
        i += 1;
    }
    true
}

pub fn check_wf(p: &Program) -> (r: bool)
    ensures r == wf(*p),
{
    let mut f: usize = 0;
    while f < p.fns.len()
        invariant f <= p.fns@.len(), forall|g: nat| g < f ==> #[trigger] wf_body(*p, g),
        decreases p.fns.len() - f,
    {
        if !check_wf_body(p, f) { return false; }
        f += 1;
    }
    true
}

/// `r == labs_ok(p, ls)`.
pub fn check_labs(p: &Program, ls: &Vec<FnLab>) -> (r: bool)
    ensures r == labs_ok(*p, ls@),
{
    if ls.len() != p.fns.len() { return false; }
    let mut g: usize = 0;
    while g < ls.len()
        invariant
            g <= ls@.len(), ls@.len() == p.fns@.len(),
            forall|k: int| 0 <= k < g ==> (#[trigger] ls@[k]).locals@.len() == p.fns@[k].locals@.len(),
        decreases ls.len() - g,
    {
        if ls[g].locals.len() != p.fns[g].locals.len() {
            assert(ls@[g as int].locals@.len() != p.fns@[g as int].locals@.len());
            return false;
        }
        g += 1;
    }
    true
}

// ------------------------------------------------------------------ places and operands

pub fn is_mut_pl(b: &Body, pl: &Place) -> (r: bool)
    ensures r == mut_pl(*b, *pl),
{
    pl.proj.len() == 0 && pl.local < b.locals.len() && match &b.locals[pl.local] { Ty::Mut(_) => true, _ => false }
}

pub fn is_mut_op(b: &Body, op: &Operand) -> (r: bool)
    ensures r == mut_op(*b, *op),
{
    match op { Operand::Copy(pl) => is_mut_pl(b, pl), _ => false }
}

pub fn check_place(b: &Body, l: &FnLab, pl: &Place) -> (r: bool)
    requires lab_len(*b, *l),
    ensures r == ok_place(*b, *l, *pl),
{
    if pl.local >= b.locals.len() { return false; }
    let mut k: usize = 0;
    while k < pl.proj.len()
        invariant
            lab_len(*b, *l), pl.local < b.locals@.len(), k <= pl.proj@.len(),
            forall|j: int| 0 <= j < k && (#[trigger] pl.proj@[j]) is Index ==>
                pl.proj@[j]->Index_0 < b.locals@.len() && !lab(*l, pl.proj@[j]->Index_0 as nat),
        decreases pl.proj.len() - k,
    {
        match &pl.proj[k] {
            Proj::Index(x) => {
                if *x >= b.locals.len() || l.locals[*x] {
                    assert(pl.proj@[k as int] is Index);
                    return false;
                }
            },
            _ => {},
        }
        k += 1;
    }
    true
}

pub fn check_op(b: &Body, l: &FnLab, op: &Operand) -> (r: bool)
    requires lab_len(*b, *l),
    ensures r == ok_op(*b, *l, *op),
{
    match op { Operand::Copy(pl) => check_place(b, l, pl), _ => true }
}

#[allow(unused_variables)]
pub fn sec_operand(b: &Body, l: &FnLab, op: &Operand) -> (r: bool)
    requires lab_len(*b, *l), ok_op(*b, *l, *op),
    ensures r == sec_op(*b, *l, *op),
{
    match op { Operand::Copy(pl) => l.locals[pl.local], _ => false }
}

// ------------------------------------------------------------------ rvalues and statements

/// (ok, secret); the secret bit is meaningful when ok.
#[verifier::loop_isolation(false)]
pub fn check_rv(b: &Body, l: &FnLab, rv: &Rvalue) -> (r: (bool, bool))
    requires lab_len(*b, *l),
    ensures r.0 == ok_rv(*b, *l, *rv), r.0 ==> r.1 == sec_rv(*b, *l, *rv),
{
    match rv {
        Rvalue::Use(x) => if check_op(b, l, x) { (true, sec_operand(b, l, x)) } else { (false, false) },
        Rvalue::Bin(op, _, x, y) => {
            if !check_op(b, l, x) || !check_op(b, l, y) { return (false, false); }
            let (sx, sy) = (sec_operand(b, l, x), sec_operand(b, l, y));
            let dl = match op { BinOp::Div | BinOp::Rem => true, _ => false };
            let sl = match op { BinOp::Shl | BinOp::Shr => true, _ => false };
            (!(dl && (sx || sy)) && !(sl && sy), sx || sy)
        },
        Rvalue::Un(_, _, x) => if check_op(b, l, x) { (true, sec_operand(b, l, x)) } else { (false, false) },
        Rvalue::Cast(_, _, x) => if check_op(b, l, x) { (true, sec_operand(b, l, x)) } else { (false, false) },
        Rvalue::Len(pl) => (check_place(b, l, pl), false),
        Rvalue::Discr(pl) => (check_place(b, l, pl), false),
        Rvalue::Aggregate(_, ops) => {
            let mut s = false;
            let mut i: usize = 0;
            while i < ops.len()
                invariant
                    i <= ops@.len(),
                    forall|k: int| 0 <= k < i ==> ok_op(*b, *l, #[trigger] ops@[k]) && !mut_op(*b, ops@[k]),
                    s == exists|k: int| 0 <= k < i && sec_op(*b, *l, #[trigger] ops@[k]),
                decreases ops.len() - i,
            {
                if !check_op(b, l, &ops[i]) || is_mut_op(b, &ops[i]) {
                    assert(!(ok_op(*b, *l, ops@[i as int]) && !mut_op(*b, ops@[i as int])));
                    return (false, false);
                }
                if sec_operand(b, l, &ops[i]) {
                    assert(sec_op(*b, *l, ops@[i as int]));
                    s = true;
                }
                i += 1;
            }
            (true, s)
        },
        Rvalue::Repeat(x, _) => if check_op(b, l, x) && !is_mut_op(b, x) { (true, sec_operand(b, l, x)) } else { (false, false) },
        Rvalue::RefShr(pl) => if check_place(b, l, pl) && !is_mut_pl(b, pl) { (true, l.locals[pl.local]) } else { (false, false) },
        Rvalue::RefMut(pl) => {
            if !check_place(b, l, pl) { return (false, false); }
            let rm = match &b.locals[pl.local] {
                Ty::Mut(_) => pl.proj.len() > 0 && match &pl.proj[0] { Proj::Deref => true, _ => false },
                _ => true,
            };
            (rm, l.locals[pl.local])
        },
    }
}

pub fn check_stmt(b: &Body, l: &FnLab, s: &Stmt) -> (r: bool)
    requires lab_len(*b, *l),
    ensures r == ok_stmt(*b, *l, *s),
{
    match s {
        Stmt::Assign(pl, rv) => {
            if !check_place(b, l, pl) { return false; }
            let (ok, sr) = check_rv(b, l, rv);
            if !ok { return false; }
            let ld = l.locals[pl.local];
            match rv {
                Rvalue::RefMut(q) => is_mut_pl(b, pl) && ld == l.locals[q.local],
                Rvalue::Use(op) => if is_mut_op(b, op) {
                    is_mut_pl(b, pl) && sec_operand(b, l, op) == ld
                } else {
                    !sr || ld
                },
                _ => !sr || ld,
            }
        },
        Stmt::SetDiscr(pl, _) => check_place(b, l, pl),
    }
}

// ------------------------------------------------------------------ terminators

#[verifier::loop_isolation(false)]
pub fn check_intr(b: &Body, l: &FnLab, k: &Intrinsic, args: &Vec<Operand>, dst: &Place) -> (r: bool)
    requires lab_len(*b, *l),
    ensures r == ok_intr(*b, *l, *k, args@, *dst),
{
    if !check_place(b, l, dst) { return false; }
    let mut i: usize = 0;
    while i < args.len()
        invariant i <= args@.len(), forall|j: int| 0 <= j < i ==> ok_op(*b, *l, #[trigger] args@[j]),
        decreases args.len() - i,
    {
        if !check_op(b, l, &args[i]) { return false; }
        i += 1;
    }
    let ld = l.locals[dst.local];
    let n = args.len();
    match k {
        Intrinsic::Declassify => n == 1 && !is_mut_op(b, &args[0]),
        Intrinsic::GhostUnit => true,
        Intrinsic::VecNew => n == 0,
        Intrinsic::VecWithCapacity => n == 1 && !sec_operand(b, l, &args[0]),
        Intrinsic::VecPush => n == 2 && !is_mut_op(b, &args[1])
            && (!sec_operand(b, l, &args[1]) || sec_operand(b, l, &args[0])),
        Intrinsic::VecExtendFromSlice => n == 2 && (!sec_operand(b, l, &args[1]) || sec_operand(b, l, &args[0])),
        Intrinsic::VecAsSlice => n == 1 && !is_mut_op(b, &args[0]) && (!sec_operand(b, l, &args[0]) || ld),
        Intrinsic::ArrayAsSlice => n == 1 && !is_mut_op(b, &args[0]) && (!sec_operand(b, l, &args[0]) || ld),
        Intrinsic::VecLen => n == 1,
        Intrinsic::VecSet => n == 3 && !sec_operand(b, l, &args[1]) && !is_mut_op(b, &args[2])
            && (!sec_operand(b, l, &args[2]) || sec_operand(b, l, &args[0])),
        Intrinsic::VecIndex => n == 2 && !sec_operand(b, l, &args[1]) && (!sec_operand(b, l, &args[0]) || ld),
        Intrinsic::SliceSubrange => n == 3 && !sec_operand(b, l, &args[1]) && !sec_operand(b, l, &args[2])
            && (!sec_operand(b, l, &args[0]) || ld),
        Intrinsic::SliceToVec => n == 1 && (!sec_operand(b, l, &args[0]) || ld),
        Intrinsic::Wrapping(op, _) => {
            if n != 2 { return false; }
            let (s0, s1) = (sec_operand(b, l, &args[0]), sec_operand(b, l, &args[1]));
            let dl = match op { BinOp::Div | BinOp::Rem => true, _ => false };
            let sl = match op { BinOp::Shl | BinOp::Shr => true, _ => false };
            !(dl && (s0 || s1)) && !(sl && s1) && (!(s0 || s1) || ld)
        },
    }
}

/// `r == ok_arg(..)` for arg `j` of a call to a fn with body `gb` and labels `gl`.
pub fn check_arg(b: &Body, l: &FnLab, gb: &Body, gl: &FnLab, j: usize, a: &Operand) -> (r: bool)
    requires lab_len(*b, *l), lab_len(*gb, *gl), 1 + j < gb.locals@.len(),
    ensures r == ok_arg(*b, *l, *gb, *gl, j as int, *a),
{
    if !check_op(b, l, a) { return false; }
    let s = sec_operand(b, l, a);
    let _len = gb.locals.len(); // its usize bound rules out overflow in `1 + j`
    let pl = gl.locals[1 + j];
    let pm = match &gb.locals[1 + j] { Ty::Mut(_) => true, _ => false };
    (!s || pl) && (!pm || s == pl) && (!is_mut_op(b, a) || pm)
}

#[verifier::loop_isolation(false)]
pub fn check_term(p: &Program, ls: &Vec<FnLab>, f: usize, t: &Term) -> (r: bool)
    requires wf(*p), labs_ok(*p, ls@), f < p.fns@.len(), wf_term(*p, f as nat, *t),
    ensures r == ok_term(*p, ls@, f as nat, *t),
{
    let b = &p.fns[f];
    let l = &ls[f];
    match t {
        Term::Goto(_) => true,
        Term::Switch(op, _, _) => check_op(b, l, op) && !sec_operand(b, l, op),
        Term::Assert(op, _, _) => check_op(b, l, op) && !sec_operand(b, l, op),
        Term::Call(Callee::Fn(g), args, dst, _) => {
            let gb = &p.fns[*g];
            let gl = &ls[*g];
            assert(wf_body(*p, *g as nat));
            let mut j: usize = 0;
            while j < args.len()
                invariant j <= args@.len(), forall|i: int| 0 <= i < j ==> ok_arg(*b, *l, *gb, *gl, i, #[trigger] args@[i]),
                decreases args.len() - j,
            {
                if !check_arg(b, l, gb, gl, j, &args[j]) {
                    assert(!ok_arg(*b, *l, *gb, *gl, j as int, args@[j as int]));
                    return false;
                }
                j += 1;
            }
            check_place(b, l, dst) && (!gl.locals[0] || l.locals[dst.local])
        },
        Term::Call(Callee::Intr(k), args, dst, _) => check_intr(b, l, k, args, dst),
        Term::Return => true,
        Term::Abort => true,
    }
}

// ------------------------------------------------------------------ blocks, bodies, programs

pub fn check_block(p: &Program, ls: &Vec<FnLab>, f: usize, blk: &Block) -> (r: bool)
    requires wf(*p), labs_ok(*p, ls@), f < p.fns@.len(), wf_block(*p, f as nat, *blk),
    ensures r == ok_block(*p, ls@, f as nat, *blk),
{
    let b = &p.fns[f];
    let l = &ls[f];
    let mut i: usize = 0;
    while i < blk.stmts.len()
        invariant
            lab_len(*b, *l), *b == p.fns@[f as int], *l == ls@[f as int], i <= blk.stmts@.len(),
            forall|k: int| 0 <= k < i ==> ok_stmt(*b, *l, #[trigger] blk.stmts@[k]),
        decreases blk.stmts.len() - i,
    {
        if !check_stmt(b, l, &blk.stmts[i]) {
            assert(!ok_stmt(*b, *l, blk.stmts@[i as int]));
            return false;
        }
        i += 1;
    }
    check_term(p, ls, f, &blk.term)
}

pub fn check_body(p: &Program, ls: &Vec<FnLab>, f: usize) -> (r: bool)
    requires wf(*p), labs_ok(*p, ls@), f < p.fns@.len(),
    ensures r == ok_body(*p, ls@, f as nat),
{
    let b = &p.fns[f];
    assert(wf_body(*p, f as nat));
    let mut i: usize = 0;
    while i < b.blocks.len()
        invariant
            wf(*p), labs_ok(*p, ls@), f < p.fns@.len(), *b == p.fns@[f as int], wf_body(*p, f as nat),
            i <= b.blocks@.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] ok_block(*p, ls@, f as nat, b.blocks@[k]),
        decreases b.blocks.len() - i,
    {
        assert(wf_block(*p, f as nat, b.blocks@[i as int]));
        if !check_block(p, ls, f, &b.blocks[i]) { return false; }
        i += 1;
    }
    true
}

pub proof fn lemma_ok_prog_labs(p: Program, ls: Seq<FnLab>)
    requires ok_prog(p, ls),
    ensures labs_ok(p, ls),
{
    assert forall|g: int| 0 <= g < ls.len() implies (#[trigger] ls[g]).locals@.len() == p.fns@[g].locals@.len() by {
        assert(ok_body(p, ls, g as nat));
    }
}

/// The checker: `r == ok_prog(p, ls)`.
pub fn check_prog(p: &Program, ls: &Vec<FnLab>) -> (r: bool)
    ensures r == ok_prog(*p, ls@),
{
    if !check_wf(p) { return false; }
    if !check_labs(p, ls) {
        proof { if ok_prog(*p, ls@) { lemma_ok_prog_labs(*p, ls@); } }
        return false;
    }
    let mut f: usize = 0;
    while f < p.fns.len()
        invariant
            wf(*p), labs_ok(*p, ls@), f <= p.fns@.len(),
            forall|g: nat| g < f ==> #[trigger] ok_body(*p, ls@, g),
        decreases p.fns.len() - f,
    {
        if !check_body(p, ls, f) { return false; }
        f += 1;
    }
    assert forall|g: nat| #![trigger ok_body(*p, ls@, g)] g < p.fns@.len() implies
        ls@[g as int].locals@.len() == p.fns@[g as int].locals@.len() && ok_body(*p, ls@, g) by {
        assert(ls@[g as int].locals@.len() == p.fns@[g as int].locals@.len());
    }
    true
}

} // verus!
