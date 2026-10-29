//! Label inference (exec, functionally unverified, D10). Its labels reach a verdict only through
//! `check_prog` and the verified `decl_ok` loop in `check_program`, so a wrong inference can only
//! cause a rejection. Verus still proves it memory-safe and terminating.
//!
//! Callees are labelled before callers (a fn's labels are its call summary). Per fn, labels start
//! from the declared params and rise to the least fixpoint of the flows of `ct.rs`: `lab(rv)`
//! into the destination, joins both ways for the `==` rules (`RefMut`, a `Mut` copy, a `Mut`
//! arg against its param), and the per-intrinsic flows.
#[allow(unused_imports)]
use crate::ct::*;
#[allow(unused_imports)]
use crate::syntax::*;
use vstd::prelude::*;

verus! {

/// Label of local `x`; out of range is public.
pub fn get(lv: &Vec<bool>, x: usize) -> bool { x < lv.len() && lv[x] }

pub fn op_sec(lv: &Vec<bool>, op: &Operand) -> bool {
    match op { Operand::Copy(pl) => get(lv, pl.local), _ => false }
}

fn raise(lv: &mut Vec<bool>, x: usize, ch: &mut bool)
    ensures final(lv)@.len() == old(lv)@.len(),
{
    if x < lv.len() && !lv[x] {
        lv.set(x, true);
        *ch = true;
    }
}

fn raise_op(lv: &mut Vec<bool>, op: &Operand, ch: &mut bool)
    ensures final(lv)@.len() == old(lv)@.len(),
{
    if let Operand::Copy(pl) = op { raise(lv, pl.local, ch); }
}

/// An `==` rule: if either side is secret, both are.
fn join(lv: &mut Vec<bool>, x: usize, y: usize, ch: &mut bool)
    ensures final(lv)@.len() == old(lv)@.len(),
{
    if get(lv, x) || get(lv, y) {
        raise(lv, x, ch);
        raise(lv, y, ch);
    }
}

fn is_mut_ty(b: &Body, x: usize) -> bool {
    x < b.locals.len() && match &b.locals[x] { Ty::Mut(_) => true, _ => false }
}

/// Over-approximates `sec_rv`.
fn rv_sec(lv: &Vec<bool>, rv: &Rvalue) -> bool {
    match rv {
        Rvalue::Use(x) => op_sec(lv, x),
        Rvalue::Bin(_, _, x, y) => op_sec(lv, x) || op_sec(lv, y),
        Rvalue::Un(_, _, x) => op_sec(lv, x),
        Rvalue::Cast(_, _, x) => op_sec(lv, x),
        Rvalue::Len(_) => false,
        Rvalue::Discr(_) => false,
        Rvalue::Aggregate(_, ops) => {
            let mut i: usize = 0;
            while i < ops.len()
                decreases ops.len() - i,
            {
                if op_sec(lv, &ops[i]) { return true; }
                i += 1;
            }
            false
        },
        Rvalue::Repeat(x, _) => op_sec(lv, x),
        Rvalue::RefShr(pl) => get(lv, pl.local),
        Rvalue::RefMut(pl) => get(lv, pl.local),
    }
}

fn flow_stmt(b: &Body, lv: &mut Vec<bool>, s: &Stmt, ch: &mut bool)
    ensures final(lv)@.len() == old(lv)@.len(),
{
    if let Stmt::Assign(pl, rv) = s {
        match rv {
            Rvalue::RefMut(q) => join(lv, pl.local, q.local, ch),
            Rvalue::Use(Operand::Copy(q)) if q.proj.len() == 0 && is_mut_ty(b, q.local) => join(lv, pl.local, q.local, ch),
            _ => if rv_sec(lv, rv) { raise(lv, pl.local, ch); },
        }
    }
}

#[verifier::loop_isolation(false)]
fn flow_term(p: &Program, ls: &Vec<FnLab>, lv: &mut Vec<bool>, t: &Term, ch: &mut bool)
    ensures final(lv)@.len() == old(lv)@.len(),
{
    match t {
        Term::Call(Callee::Fn(g), args, dst, _) => {
            if *g < ls.len() && *g < p.fns.len() {
                let gl = &ls[*g].locals;
                let gb = &p.fns[*g];
                if get(gl, 0) { raise(lv, dst.local, ch); }
                let mut j: usize = 0;
                while j < args.len() && j < gb.locals.len()
                    invariant lv@.len() == old(lv)@.len(),
                    decreases args.len() - j,
                {
                    // the Mut-param `==`: a secret param makes the caller's `&mut` (and, by the
                    // RefMut join, the borrowed buffer) secret
                    if j + 1 < gb.locals.len() && is_mut_ty(gb, j + 1) && get(gl, j + 1) {
                        raise_op(lv, &args[j], ch);
                    }
                    j += 1;
                }
            }
        },
        Term::Call(Callee::Intr(k), args, dst, _) => {
            let n = args.len();
            match k {
                Intrinsic::VecPush | Intrinsic::VecExtendFromSlice =>
                    if n >= 2 && op_sec(lv, &args[1]) { raise_op(lv, &args[0], ch); },
                Intrinsic::VecSet => if n >= 3 && op_sec(lv, &args[2]) { raise_op(lv, &args[0], ch); },
                Intrinsic::VecAsSlice | Intrinsic::ArrayAsSlice | Intrinsic::VecIndex | Intrinsic::SliceSubrange
                | Intrinsic::SliceToVec => if n >= 1 && op_sec(lv, &args[0]) { raise(lv, dst.local, ch); },
                Intrinsic::Wrapping(_, _) =>
                    if n >= 2 && (op_sec(lv, &args[0]) || op_sec(lv, &args[1])) { raise(lv, dst.local, ch); },
                _ => {},
            }
        },
        _ => {},
    }
}

/// One pass over every flow of `b`; `ch` is set if a label rose.
#[verifier::loop_isolation(false)]
fn pass(p: &Program, ls: &Vec<FnLab>, b: &Body, lv: &mut Vec<bool>, ch: &mut bool)
    ensures final(lv)@.len() == old(lv)@.len(),
{
    let mut i: usize = 0;
    while i < b.blocks.len()
        invariant lv@.len() == old(lv)@.len(),
        decreases b.blocks.len() - i,
    {
        let blk = &b.blocks[i];
        let mut k: usize = 0;
        while k < blk.stmts.len()
            invariant lv@.len() == old(lv)@.len(),
            decreases blk.stmts.len() - k,
        {
            flow_stmt(b, lv, &blk.stmts[k], ch);
            k += 1;
        }
        flow_term(p, ls, lv, &blk.term, ch);
        i += 1;
    }
}

/// Fn `f`'s least fixpoint, given its callees' labels in `ls`; `None` if `nlocals + 1` passes
/// do not reach it.
#[verifier::loop_isolation(false)]
fn infer_fn(p: &Program, ls: &Vec<FnLab>, decl: &Vec<Option<Vec<bool>>>, f: usize) -> Option<Vec<bool>>
    requires f < p.fns@.len(),
{
    let b = &p.fns[f];
    let n = b.locals.len();
    let mut lv: Vec<bool> = Vec::new();
    while lv.len() < n
        invariant lv@.len() <= n,
        decreases n - lv.len(),
    {
        lv.push(false);
    }
    if f < decl.len() {
        if let Some(d) = &decl[f] {
            let mut j: usize = 0;
            while j < d.len()
                invariant lv@.len() == n,
                decreases d.len() - j,
            {
                // params only: an entry past `nargs` stays unset, so `decl_ok` rejects it
                if d[j] && j < b.nargs && j + 1 < n { lv.set(j + 1, true); }
                j += 1;
            }
        }
    }
    let mut left = n;
    loop
        invariant lv@.len() == n,
        decreases left,
    {
        let mut ch = false;
        pass(p, ls, b, &mut lv, &mut ch);
        if !ch { return Some(lv); }
        if left == 0 { return None; }
        left -= 1;
    }
}

/// Fn `f` calls no fn left undone.
#[verifier::loop_isolation(false)]
fn callees_done(p: &Program, f: usize, done: &Vec<bool>) -> bool
    requires f < p.fns@.len(),
{
    let b = &p.fns[f];
    let mut i: usize = 0;
    while i < b.blocks.len()
        decreases b.blocks.len() - i,
    {
        if let Term::Call(Callee::Fn(g), _, _, _) = &b.blocks[i].term {
            if *g < done.len() && !done[*g] { return false; }
        }
        i += 1;
    }
    true
}

/// The fns in callee-first order, or `Err(f)` for a fn `f` left on or above a call cycle.
#[verifier::loop_isolation(false)]
pub fn callee_order(p: &Program) -> (r: Result<Vec<usize>, usize>)
    ensures r is Ok ==> forall|i: int| 0 <= i < r->Ok_0@.len() ==> r->Ok_0@[i] < p.fns@.len(),
{
    let n = p.fns.len();
    let mut done: Vec<bool> = Vec::new();
    while done.len() < n
        invariant done@.len() <= n,
        decreases n - done.len(),
    {
        done.push(false);
    }
    let mut order: Vec<usize> = Vec::new();
    let mut round: usize = 0;
    // each round completes at least one fn, so `n` rounds complete all of them
    // ponytail: O(n^2) rounds over the call graph; a DFS topological sort if closures grow large
    while round < n
        invariant done@.len() == n, forall|i: int| 0 <= i < order@.len() ==> order@[i] < n,
        decreases n - round,
    {
        let mut progress = false;
        let mut f: usize = 0;
        while f < n
            invariant done@.len() == n, forall|i: int| 0 <= i < order@.len() ==> order@[i] < n,
            decreases n - f,
        {
            if !done[f] && callees_done(p, f, &done) {
                done.set(f, true);
                order.push(f);
                progress = true;
            }
            f += 1;
        }
        if !progress { break; }
        round += 1;
    }
    let mut f: usize = 0;
    while f < n
        invariant done@.len() == n,
        decreases n - f,
    {
        if !done[f] { return Err(f); }
        f += 1;
    }
    Ok(order)
}

#[verifier::loop_isolation(false)]
pub fn infer_labels(p: &Program, decl: &Vec<Option<Vec<bool>>>) -> (r: Result<Vec<FnLab>, usize>)
    ensures r is Ok ==> r->Ok_0@.len() == p.fns@.len(),
{
    let order = match callee_order(p) { Ok(o) => o, Err(f) => return Err(f) };
    let mut ls: Vec<FnLab> = Vec::new();
    while ls.len() < p.fns.len()
        invariant ls@.len() <= p.fns@.len(),
        decreases p.fns.len() - ls.len(),
    {
        ls.push(FnLab { locals: Vec::new() });
    }
    let mut i: usize = 0;
    while i < order.len()
        invariant ls@.len() == p.fns@.len(), forall|k: int| 0 <= k < order@.len() ==> order@[k] < p.fns@.len(),
        decreases order.len() - i,
    {
        let f = order[i];
        match infer_fn(p, &ls, decl, f) {
            Some(lv) => ls.set(f, FnLab { locals: lv }),
            None => return Err(f),
        }
        i += 1;
    }
    Ok(ls)
}

} // verus!
