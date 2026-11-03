//! Core language of the constant-time checker (Phase 8a): syntax, and its trusted spec semantics
//! with leakage events and step counts; the CT typing and its value/place lemmas; the verified
//! exec checker, label inference and the `check_program` API.
pub mod check;
pub mod cost;
pub mod cost_check;
pub mod cost_sanity;
pub mod cost_sym;
pub mod ct;
pub mod ct_lemmas;
pub mod infer;
pub mod loops;
pub mod ni;
pub mod sem;
pub mod sem_sanity;
pub mod syntax;

pub use cost_check::check_cert;
pub use syntax::*;

use check::*;
use cost::{Cert, Poly};
#[allow(unused_imports)]
use ct::*;
use infer::*;
use loops::{build_cert, CostWhy};
use vstd::prelude::*;

verus! {

pub enum RejectKind {
    SecretSwitch, SecretAssert, SecretIndex, SecretDivOperand, SecretShift, SecretAlloc, SecretRange,
    ArgLabel(usize), RetLabel, MutLabel, NotWf, Recursion, InferFailed,
}

/// A rejection site: fn `f`, block `block`, statement `stmt` (`None` = the terminator).
pub struct Reject { pub f: usize, pub block: usize, pub stmt: Option<usize>, pub kind: RejectKind }

fn rj(f: usize, block: usize, stmt: Option<usize>, kind: RejectKind) -> Reject { Reject { f, block, stmt, kind } }

fn is_div(op: &BinOp) -> bool { match op { BinOp::Div | BinOp::Rem => true, _ => false } }

fn is_shift(op: &BinOp) -> bool { match op { BinOp::Shl | BinOp::Shr => true, _ => false } }

fn mut_ty(b: &Body, x: usize) -> bool { x < b.locals.len() && match &b.locals[x] { Ty::Mut(_) => true, _ => false } }

fn place_kinds(b: &Body, l: &Vec<bool>, pl: &Place, out: &mut Vec<RejectKind>) {
    if pl.local >= b.locals.len() {
        out.push(RejectKind::NotWf);
        return;
    }
    let mut k: usize = 0;
    while k < pl.proj.len()
        decreases pl.proj.len() - k,
    {
        if let Proj::Index(x) = &pl.proj[k] {
            if *x >= b.locals.len() || get(l, *x) {
                out.push(RejectKind::SecretIndex);
                return;
            }
        }
        k += 1;
    }
}

fn op_kinds(b: &Body, l: &Vec<bool>, op: &Operand, out: &mut Vec<RejectKind>) {
    if let Operand::Copy(pl) = op { place_kinds(b, l, pl, out); }
}

fn stmt_kinds(b: &Body, l: &Vec<bool>, s: &Stmt, out: &mut Vec<RejectKind>) {
    match s {
        Stmt::Assign(pl, rv) => {
            place_kinds(b, l, pl, out);
            let ld = get(l, pl.local);
            match rv {
                Rvalue::Use(x) => {
                    op_kinds(b, l, x, out);
                    if is_mut_op(b, x) {
                        if !is_mut_pl(b, pl) { out.push(RejectKind::NotWf); }
                        if op_sec(l, x) != ld { out.push(RejectKind::MutLabel); }
                    }
                },
                Rvalue::Bin(op, _, x, y) => {
                    op_kinds(b, l, x, out);
                    op_kinds(b, l, y, out);
                    if is_div(op) && (op_sec(l, x) || op_sec(l, y)) { out.push(RejectKind::SecretDivOperand); }
                    if is_shift(op) && op_sec(l, y) { out.push(RejectKind::SecretShift); }
                },
                Rvalue::Un(_, _, x) => op_kinds(b, l, x, out),
                Rvalue::Cast(_, _, x) => op_kinds(b, l, x, out),
                Rvalue::Len(q) => place_kinds(b, l, q, out),
                Rvalue::Discr(q) => place_kinds(b, l, q, out),
                Rvalue::Aggregate(_, ops) => {
                    let mut i: usize = 0;
                    while i < ops.len()
                        decreases ops.len() - i,
                    {
                        op_kinds(b, l, &ops[i], out);
                        if is_mut_op(b, &ops[i]) { out.push(RejectKind::NotWf); }
                        i += 1;
                    }
                },
                Rvalue::Repeat(x, _) => {
                    op_kinds(b, l, x, out);
                    if is_mut_op(b, x) { out.push(RejectKind::NotWf); }
                },
                Rvalue::RefShr(q) => {
                    place_kinds(b, l, q, out);
                    if is_mut_pl(b, q) { out.push(RejectKind::NotWf); }
                },
                Rvalue::RefMut(q) => {
                    place_kinds(b, l, q, out);
                    let reborrow = q.proj.len() > 0 && match &q.proj[0] { Proj::Deref => true, _ => false };
                    if (mut_ty(b, q.local) && !reborrow) || !is_mut_pl(b, pl) { out.push(RejectKind::NotWf); }
                    if get(l, q.local) != ld { out.push(RejectKind::MutLabel); }
                },
            }
        },
        Stmt::SetDiscr(pl, _) => place_kinds(b, l, pl, out),
    }
}

#[verifier::loop_isolation(false)]
fn term_kinds(p: &Program, ls: &Vec<FnLab>, b: &Body, l: &Vec<bool>, t: &Term, out: &mut Vec<RejectKind>) {
    match t {
        Term::Switch(op, _, _) => {
            op_kinds(b, l, op, out);
            if op_sec(l, op) { out.push(RejectKind::SecretSwitch); }
        },
        Term::Assert(op, _, _) => {
            op_kinds(b, l, op, out);
            if op_sec(l, op) { out.push(RejectKind::SecretAssert); }
        },
        Term::Call(Callee::Fn(g), args, dst, _) => {
            if *g >= p.fns.len() || *g >= ls.len() {
                out.push(RejectKind::NotWf);
                return;
            }
            let (gb, gl) = (&p.fns[*g], &ls[*g].locals);
            let mut j: usize = 0;
            while j < args.len() && j < gb.locals.len()
                decreases args.len() - j,
            {
                let a = &args[j];
                op_kinds(b, l, a, out);
                let (s, pm) = (op_sec(l, a), mut_ty(gb, j + 1));
                let ps = get(gl, j + 1);
                // the param is named; a Mut param's label must equal the caller buffer's
                if (s && !ps) || (pm && s != ps) || (is_mut_op(b, a) && !pm) { out.push(RejectKind::ArgLabel(j)); }
                if pm && s != ps { out.push(RejectKind::MutLabel); }
                j += 1;
            }
            place_kinds(b, l, dst, out);
            if get(gl, 0) && !get(l, dst.local) { out.push(RejectKind::RetLabel); }
        },
        Term::Call(Callee::Intr(k), args, dst, _) => {
            place_kinds(b, l, dst, out);
            let n = args.len();
            let mut i: usize = 0;
            while i < n
                decreases n - i,
            {
                op_kinds(b, l, &args[i], out);
                i += 1;
            }
            let want = match k {
                Intrinsic::VecNew => 0,
                Intrinsic::Declassify | Intrinsic::VecWithCapacity | Intrinsic::VecAsSlice | Intrinsic::ArrayAsSlice
                | Intrinsic::VecLen | Intrinsic::SliceToVec => 1,
                Intrinsic::VecPush | Intrinsic::VecExtendFromSlice | Intrinsic::VecIndex | Intrinsic::Wrapping(_, _) => 2,
                Intrinsic::VecSet | Intrinsic::SliceSubrange => 3,
                Intrinsic::GhostUnit => n,
            };
            if n != want {
                out.push(RejectKind::NotWf);
                return;
            }
            match k {
                Intrinsic::VecWithCapacity => if op_sec(l, &args[0]) { out.push(RejectKind::SecretAlloc); },
                Intrinsic::VecSet | Intrinsic::VecIndex => if op_sec(l, &args[1]) { out.push(RejectKind::SecretIndex); },
                Intrinsic::SliceSubrange => if op_sec(l, &args[1]) || op_sec(l, &args[2]) { out.push(RejectKind::SecretRange); },
                Intrinsic::Wrapping(op, _) => {
                    if is_div(op) && (op_sec(l, &args[0]) || op_sec(l, &args[1])) { out.push(RejectKind::SecretDivOperand); }
                    if is_shift(op) && op_sec(l, &args[1]) { out.push(RejectKind::SecretShift); }
                },
                _ => {},
            }
        },
        _ => {},
    }
}

/// Moves `ks` into `out` at one site; a failing site with no kind found gets `InferFailed`
/// (a flow the labels violate, which inference should have satisfied).
fn push_site(out: &mut Vec<Reject>, ks: &mut Vec<RejectKind>, f: usize, block: usize, stmt: Option<usize>) {
    if ks.len() == 0 { ks.push(RejectKind::InferFailed); }
    loop
        decreases ks.len(),
    {
        match ks.pop() {
            Some(k) => out.push(rj(f, block, stmt, k)),
            None => break,
        }
    }
}

/// The rejection sites of `p` under `ls` (exec, unverified): every site whose check fails.
#[verifier::loop_isolation(false)]
pub fn explain(p: &Program, ls: &Vec<FnLab>) -> Vec<Reject> {
    let mut out: Vec<Reject> = Vec::new();
    if !check_wf(p) {
        let mut f: usize = 0;
        while f < p.fns.len()
            decreases p.fns.len() - f,
        {
            if !check_wf_body(p, f) { out.push(rj(f, 0, None, RejectKind::NotWf)); }
            f += 1;
        }
        return out;
    }
    if !check_labs(p, ls) {
        out.push(rj(0, 0, None, RejectKind::InferFailed));
        return out;
    }
    let mut f: usize = 0;
    while f < p.fns.len()
        decreases p.fns.len() - f,
    {
        let (b, l) = (&p.fns[f], &ls[f]);
        assert(wf_body(*p, f as nat));
        let mut bi: usize = 0;
        while bi < b.blocks.len()
            decreases b.blocks.len() - bi,
        {
            let blk = &b.blocks[bi];
            assert(wf_block(*p, f as nat, b.blocks@[bi as int]));
            let mut si: usize = 0;
            while si < blk.stmts.len()
                decreases blk.stmts.len() - si,
            {
                if !check_stmt(b, l, &blk.stmts[si]) {
                    let mut ks: Vec<RejectKind> = Vec::new();
                    stmt_kinds(b, &l.locals, &blk.stmts[si], &mut ks);
                    push_site(&mut out, &mut ks, f, bi, Some(si));
                }
                si += 1;
            }
            if !check_term(p, ls, f, &blk.term) {
                let mut ks: Vec<RejectKind> = Vec::new();
                term_kinds(p, ls, b, &l.locals, &blk.term, &mut ks);
                push_site(&mut out, &mut ks, f, bi, None);
            }
            bi += 1;
        }
        f += 1;
    }
    out
}

fn one(f: usize, kind: RejectKind) -> Vec<Reject> {
    let mut v = Vec::new();
    v.push(rj(f, 0, None, kind));
    v
}

/// Infer labels, check them with the verified checker, and check them against the declared
/// secrets: `Ok(ls)` only if `ok_prog(p, ls)` and `decl_ok(decl, ls)`, the premises
/// `theorem_ct` (`ctcore::ni::theorem_ct`) needs, with every declared-secret param secret.
#[verifier::loop_isolation(false)]
pub fn check_program(p: &Program, decl: &Vec<Option<Vec<bool>>>) -> (r: Result<Vec<FnLab>, Vec<Reject>>)
    ensures r is Ok ==> ok_prog(*p, r->Ok_0@) && decl_ok(decl@, r->Ok_0@),
{
    if !check_wf(p) { return Err(explain(p, &Vec::new())); }
    let ls = match infer_labels(p, decl) {
        Ok(ls) => ls,
        Err(f) => return Err(one(f, match callee_order(p) { Err(_) => RejectKind::Recursion, Ok(_) => RejectKind::InferFailed })),
    };
    if !check_prog(p, &ls) {
        let mut rs = explain(p, &ls);
        if rs.len() == 0 { rs.push(rj(0, 0, None, RejectKind::InferFailed)); }
        return Err(rs);
    }
    // decl_ok, by a verified loop
    let mut f: usize = 0;
    while f < decl.len()
        invariant
            f <= decl@.len(),
            forall|g: int, j: int| 0 <= g < f && decl@[g] is Some && 0 <= j < decl@[g]->Some_0@.len()
                && #[trigger] decl@[g]->Some_0@[j] ==> g < ls@.len() && 1 + j < ls@[g].locals@.len() && ls@[g].locals@[1 + j],
        decreases decl.len() - f,
    {
        if let Some(d) = &decl[f] {
            let mut j: usize = 0;
            while j < d.len()
                invariant
                    j <= d@.len(), f < decl@.len(), decl@[f as int] == Some(*d),
                    forall|g: int, k: int| 0 <= g < f && decl@[g] is Some && 0 <= k < decl@[g]->Some_0@.len()
                        && #[trigger] decl@[g]->Some_0@[k] ==> g < ls@.len() && 1 + k < ls@[g].locals@.len() && ls@[g].locals@[1 + k],
                    forall|k: int| 0 <= k < j && #[trigger] d@[k] ==> f < ls@.len() && 1 + k < ls@[f as int].locals@.len() && ls@[f as int].locals@[1 + k],
                decreases d.len() - j,
            {
                if d[j] && !(f < ls.len() && j < ls[f].locals.len() && j + 1 < ls[f].locals.len() && ls[f].locals[j + 1]) {
                    return Err(one(f, RejectKind::InferFailed));
                }
                j += 1;
            }
        }
        f += 1;
    }
    Ok(ls)
}

// ------------------------------------------------------------------ step bounds

/// Drops every summary whose certificate no longer checks against the rest, until none does. The
/// result is `cert_for` on itself: nothing here trusts `build_cert`.
#[verifier::loop_isolation(false)]
pub fn revalidate(p: &Program, certs: &Vec<Cert>, sums: Vec<Option<Poly>>) -> (r: Vec<Option<Poly>>)
    requires certs@.len() == p.fns@.len(), sums@.len() == p.fns@.len(),
    ensures
        r@.len() == p.fns@.len(),
        forall|g: int| 0 <= g < r@.len() && r@[g] is Some ==> cost::cert_for(*p, g as nat, certs@[g], r@),
{
    let n = p.fns.len();
    let mut sums = sums;
    let mut pass = n;
    while pass > 0
        invariant sums@.len() == n,
        decreases pass,
    {
        let mut changed = false;
        let mut g: usize = 0;
        while g < n
            invariant
                g <= n, sums@.len() == n,
                !changed ==> forall|j: int| 0 <= j < g && sums@[j] is Some ==> cost::cert_for(*p, j as nat, certs@[j], sums@),
            decreases n - g,
        {
            let some = match &sums[g] { Some(_) => true, None => false };
            if some && !check_cert(p, g, &certs[g], &sums) {
                sums.set(g, None);
                changed = true;
            }
            g += 1;
        }
        if !changed { return sums; }
        pass -= 1;
    }
    no_summaries(n)
}

fn no_summaries(n: usize) -> (r: Vec<Option<Poly>>)
    ensures r@.len() == n, forall|g: int| 0 <= g < r@.len() ==> r@[g] is None,
{
    let mut r: Vec<Option<Poly>> = Vec::new();
    while r.len() < n
        invariant r@.len() <= n, forall|g: int| 0 <= g < r@.len() ==> r@[g] is None,
        decreases n - r.len(),
    {
        r.push(None);
    }
    r
}

fn no_certs(n: usize) -> (r: Vec<Cert>)
    ensures r@.len() == n,
{
    let mut r: Vec<Cert> = Vec::new();
    while r.len() < n
        invariant r@.len() <= n,
        decreases n - r.len(),
    {
        r.push(Cert { blocks: Vec::new() });
    }
    r
}

fn whys_of(n: usize, rec: bool, wf: bool) -> (r: Vec<CostWhy>)
    ensures r@.len() == n,
{
    let mut r: Vec<CostWhy> = Vec::new();
    while r.len() < n
        invariant r@.len() <= n,
        decreases n - r.len(),
    {
        r.push(if !wf { CostWhy::NotWf } else if rec { CostWhy::Recursion } else { CostWhy::Bounded });
    }
    r
}

/// The block `check_cost_block` refuses, or 0.
#[verifier::loop_isolation(false)]
fn first_bad(p: &Program, g: usize, c: &Cert, sums: &Vec<Option<Poly>>) -> usize {
    if g >= p.fns.len() { return 0; }
    let mut b: usize = 0;
    while b < p.fns[g].blocks.len()
        decreases p.fns@[g as int].blocks@.len() - b,
    {
        if !cost_check::check_cost_block(p, g, b, c, sums) { return b; }
        b += 1;
    }
    0
}

/// Step bounds, callees first. A `Some` means `cert_for`, and says nothing without `check_program`
/// `Ok`: the driver supplies that. `theorem_cost` stays at `ctcore::cost::theorem_cost`.
#[verifier::loop_isolation(false)]
pub fn analyze(p: &Program) -> (r: (Vec<Option<Poly>>, Vec<Cert>, Vec<CostWhy>))
    ensures
        r.0@.len() == p.fns@.len(), r.1@.len() == p.fns@.len(),
        forall|g: int| 0 <= g < r.0@.len() && r.0@[g] is Some ==> cost::cert_for(*p, g as nat, r.1@[g], r.0@),
{
    let n = p.fns.len();
    if !check_wf(p) { return (no_summaries(n), no_certs(n), whys_of(n, false, false)); }
    let order = match callee_order(p) {
        Ok(o) => o,
        Err(_) => return (no_summaries(n), no_certs(n), whys_of(n, true, true)),
    };
    let mut sums = no_summaries(n);
    let mut certs = no_certs(n);
    let mut whys = whys_of(n, false, true);
    let mut i: usize = 0;
    while i < order.len()
        invariant sums@.len() == n, certs@.len() == n, whys@.len() == n,
        decreases order.len() - i,
    {
        let f = order[i];
        match build_cert(p, f, &sums) {
            Ok(c) => {
                if c.blocks.len() > 0 {
                    sums.set(f, Some(cost_check::poly_copy(&c.blocks[0].pot)));
                }
                if check_cert(p, f, &c, &sums) {
                    certs.set(f, c);
                } else {
                    whys.set(f, CostWhy::Validator(first_bad(p, f, &c, &sums)));
                    sums.set(f, None);
                }
            },
            Err(w) => whys.set(f, w),
        }
        i += 1;
    }
    let sums = revalidate(p, &certs, sums);
    let mut g: usize = 0;
    while g < n
        invariant
            whys@.len() == n, sums@.len() == n, certs@.len() == n,
            forall|j: int| 0 <= j < n && sums@[j] is Some ==> cost::cert_for(*p, j as nat, certs@[j], sums@),
        decreases n - g,
    {
        let none = match &sums[g] { None => true, Some(_) => false };
        if none {
            let dropped = match &whys[g] { CostWhy::Bounded => true, _ => false };
            if dropped { whys.set(g, CostWhy::Validator(first_bad(p, g, &certs[g], &sums))); }
            certs.set(g, Cert { blocks: Vec::new() });
        }
        g += 1;
    }
    (sums, certs, whys)
}

} // verus!
