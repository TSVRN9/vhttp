//! Untrusted inference of step-bound certificates (Phase 8b): dominators, natural loops, counted
//! loops, then facts forward and potentials backward, in the forms `check_cert` reads. Nothing here
//! is proved beyond memory safety and termination: `check_cert` re-validates every result, so a bug
//! costs coverage, never soundness.
use crate::check::is_mut_op;
use crate::cost::*;
use crate::cost_check::{
    atom_copy, atom_eq, atoms_eq, exec_sym_block, exec_sym_stmts, fact_copy, int_ty_copy, int_ty_eq, mono_copy, poly_copy,
    pull_post, term_charge,
};
use crate::cost_sym::Eff;
use crate::infer::get;
use crate::syntax::*;
use vstd::prelude::*;

verus! {

/// A loop `check_cert` can pay for: one test `counter < bound`, one `counter += 1`.
pub struct Counted {
    pub header: usize,
    pub body: Vec<bool>,
    pub counter: usize,
    pub ty: IntTy,
    pub bound: Atom,
    pub test_block: usize,
    pub inc_block: usize,
}

pub enum CostWhy {
    Bounded,
    NotCounted(usize /* a header, or the block where the region got stuck */),
    Unresolved,
    Recursion,
    CalleeNone(usize),
    DegreeCap,
    Overflow,
    Validator(usize /* block */),
    NotWf,
    NotTyped,
}

// ------------------------------------------------------------------ small vectors

fn filled(n: usize, x: bool) -> (r: Vec<bool>)
    ensures r@.len() == n,
{
    let mut r: Vec<bool> = Vec::new();
    while r.len() < n
        invariant r@.len() <= n,
        decreases n - r.len(),
    {
        r.push(x);
    }
    r
}

fn put(v: &mut Vec<bool>, i: usize, x: bool) {
    if i < v.len() { v.set(i, x); }
}

/// Passes for a dataflow over `n` blocks whose results only shrink. Running out leaves an
/// over-approximation, which at worst fails `check_cert`.
fn pass_bound(n: usize) -> usize {
    if n < 0x1000_0000 { n + 8 } else { n }
}

fn succs(t: &Term) -> Vec<usize> {
    let mut out: Vec<usize> = Vec::new();
    match t {
        Term::Goto(b) => out.push(*b),
        Term::Switch(_, ts, o) => {
            let mut i: usize = 0;
            while i < ts.len()
                decreases ts.len() - i,
            {
                out.push(ts[i].1);
                i += 1;
            }
            out.push(*o);
        },
        Term::Assert(_, _, b) => out.push(*b),
        Term::Call(_, _, _, next) => out.push(*next),
        _ => {},
    }
    out
}

// ------------------------------------------------------------------ graph structure

/// One pass of `seen` along the edges from what is already seen; `true` if it grew.
fn reach_pass(b: &Body, seen: &mut Vec<bool>) -> bool {
    let mut grew = false;
    let mut x: usize = 0;
    while x < b.blocks.len()
        decreases b.blocks.len() - x,
    {
        if get(seen, x) {
            let ss = succs(&b.blocks[x].term);
            let mut j: usize = 0;
            while j < ss.len()
                decreases ss.len() - j,
            {
                if !get(seen, ss[j]) && ss[j] < seen.len() {
                    seen.set(ss[j], true);
                    grew = true;
                }
                j += 1;
            }
        }
        x += 1;
    }
    grew
}

fn reachable(b: &Body) -> Vec<bool> {
    let n = b.blocks.len();
    let mut seen = filled(n, false);
    put(&mut seen, 0, true);
    let mut left = pass_bound(n);
    loop
        decreases left,
    {
        if !reach_pass(b, &mut seen) || left == 0 { break; }
        left -= 1;
    }
    seen
}

/// `dom[n][d]`: `d` dominates `n`. An unreachable block's row is all `false`.
pub fn dominators(b: &Body) -> Vec<Vec<bool>> {
    let n = b.blocks.len();
    let mut dom: Vec<Vec<bool>> = Vec::new();
    while dom.len() < n
        invariant dom@.len() <= n,
        decreases n - dom.len(),
    {
        let row = filled(n, dom.len() != 0);
        dom.push(row);
    }
    if n > 0 {
        let mut row = filled(n, false);
        put(&mut row, 0, true);
        dom.set(0, row);
    }
    let mut left = pass_bound(n);
    loop
        invariant dom@.len() == n, n == b.blocks@.len(),
        decreases left,
    {
        let mut changed = false;
        let mut p: usize = 0;
        while p < n
            invariant dom@.len() == n, n == b.blocks@.len(),
            decreases n - p,
        {
            let ss = succs(&b.blocks[p].term);
            let mut j: usize = 0;
            while j < ss.len()
                invariant dom@.len() == n,
                decreases ss.len() - j,
            {
                if ss[j] != 0 && dom_row_meet(&mut dom, ss[j], p) { changed = true; }
                j += 1;
            }
            p += 1;
        }
        if !changed || left == 0 { break; }
        left -= 1;
    }
    let seen = reachable(b);
    let mut x: usize = 0;
    while x < n
        invariant dom@.len() == n,
        decreases n - x,
    {
        if !get(&seen, x) { dom.set(x, filled(n, false)); }
        x += 1;
    }
    dom
}

/// `dom[s] := dom[s] & (dom[p] | {s})`; `true` if it shrank.
#[verifier::loop_isolation(false)]
fn dom_row_meet(dom: &mut Vec<Vec<bool>>, s: usize, p: usize) -> (r: bool)
    ensures final(dom)@.len() == old(dom)@.len(),
{
    if s >= dom.len() || p >= dom.len() { return false; }
    let mut row: Vec<bool> = Vec::new();
    let mut shrank = false;
    let n = dom[s].len();
    let mut d: usize = 0;
    while d < n
        decreases n - d,
    {
        let had = get(&dom[s], d);
        let keep = had && (d == s || get(&dom[p], d));
        if had && !keep { shrank = true; }
        row.push(keep);
        d += 1;
    }
    dom.set(s, row);
    shrank
}

#[verifier::loop_isolation(false)]
pub fn back_edges(b: &Body, dom: &Vec<Vec<bool>>) -> Vec<(usize, usize)> {
    let mut out: Vec<(usize, usize)> = Vec::new();
    let mut x: usize = 0;
    while x < b.blocks.len() && x < dom.len()
        decreases b.blocks.len() - x,
    {
        let ss = succs(&b.blocks[x].term);
        let mut j: usize = 0;
        while j < ss.len()
            decreases ss.len() - j,
        {
            if get(&dom[x], ss[j]) { out.push((x, ss[j])); }
            j += 1;
        }
        x += 1;
    }
    out
}

/// One pass of the blocks reaching `lp` without passing `header`; `true` if it grew.
fn loop_pass(b: &Body, lp: &mut Vec<bool>, header: usize) -> bool {
    let mut grew = false;
    let mut x = b.blocks.len();
    while x > 0
        decreases x,
    {
        x -= 1;
        if x < b.blocks.len() && x != header && !get(lp, x) {
            let ss = succs(&b.blocks[x].term);
            let mut j: usize = 0;
            while j < ss.len()
                decreases ss.len() - j,
            {
                if ss[j] != header && get(lp, ss[j]) && !get(lp, x) {
                    put(lp, x, true);
                    grew = true;
                }
                j += 1;
            }
        }
    }
    grew
}

pub fn natural_loop(b: &Body, latch: usize, header: usize) -> Vec<bool> {
    let n = b.blocks.len();
    let mut lp = filled(n, false);
    put(&mut lp, latch, true);
    put(&mut lp, header, true);
    let mut left = pass_bound(n);
    loop
        decreases left,
    {
        if !loop_pass(b, &mut lp, header) || left == 0 { break; }
        left -= 1;
    }
    lp
}

// ------------------------------------------------------------------ what a block writes

fn mut_local(b: &Body, x: usize) -> bool {
    x < b.locals.len() && match &b.locals[x] { Ty::Mut(_) => true, _ => false }
}

fn writer_place(b: &Body, q: &Place) -> bool {
    mut_local(b, q.local) && q.proj.len() > 0 && match &q.proj[0] { Proj::Deref => true, _ => false }
}

fn any_mut_arg(b: &Body, args: &Vec<Operand>) -> bool {
    let mut i: usize = 0;
    while i < args.len()
        decreases args.len() - i,
    {
        if is_mut_op(b, &args[i]) { return true; }
        i += 1;
    }
    false
}

fn stmt_place(s: &Stmt) -> &Place {
    match s { Stmt::Assign(q, _) => q, Stmt::SetDiscr(q, _) => q }
}

/// A block whose write may land in any local: `cost_sym`'s writer rule.
fn block_writer(b: &Body, blk: &Block) -> bool {
    let mut i: usize = 0;
    while i < blk.stmts.len()
        decreases blk.stmts.len() - i,
    {
        if writer_place(b, stmt_place(&blk.stmts[i])) { return true; }
        i += 1;
    }
    match &blk.term {
        Term::Call(Callee::Fn(_), args, dst, _) => any_mut_arg(b, args) || writer_place(b, dst),
        Term::Call(Callee::Intr(k), args, dst, _) => writer_place(b, dst) || match k {
            Intrinsic::VecPush | Intrinsic::VecSet | Intrinsic::VecExtendFromSlice => args.len() > 0 && is_mut_op(b, &args[0]),
            _ => false,
        },
        _ => false,
    }
}

/// `from` plus the block's writes to local `x`, saturating at 2.
fn count_writes(blk: &Block, x: usize, from: u8) -> (r: u8)
    requires from <= 2,
    ensures r <= 2,
{
    let mut c = from;
    let mut i: usize = 0;
    while i < blk.stmts.len()
        invariant c <= 2,
        decreases blk.stmts.len() - i,
    {
        if stmt_place(&blk.stmts[i]).local == x && c < 2 { c += 1; }
        i += 1;
    }
    if let Term::Call(_, _, dst, _) = &blk.term {
        if dst.local == x && c < 2 { c += 1; }
    }
    c
}

fn plain_local(op: &Operand, x: usize) -> bool {
    match op { Operand::Copy(q) => q.local == x && q.proj.len() == 0, _ => false }
}

fn is_one(op: &Operand) -> bool {
    match op { Operand::Const(_, n) => *n == 1, _ => false }
}

fn stmt_is_inc(s: &Stmt, x: usize, ty: &IntTy) -> bool {
    match s {
        Stmt::Assign(q, Rvalue::Bin(BinOp::Add, t, a, c)) => q.local == x && q.proj.len() == 0 && int_ty_eq(t, ty) && plain_local(a, x) && is_one(c),
        _ => false,
    }
}

fn term_is_inc(t: &Term, x: usize, ty: &IntTy) -> bool {
    match t {
        Term::Call(Callee::Intr(Intrinsic::Wrapping(BinOp::Add, w)), args, dst, _) =>
            dst.local == x && dst.proj.len() == 0 && int_ty_eq(w, ty) && args.len() == 2 && plain_local(&args[0], x) && is_one(&args[1]),
        _ => false,
    }
}

fn block_has_inc(blk: &Block, x: usize, ty: &IntTy) -> bool {
    let mut i: usize = 0;
    while i < blk.stmts.len()
        decreases blk.stmts.len() - i,
    {
        if stmt_is_inc(&blk.stmts[i], x, ty) { return true; }
        i += 1;
    }
    term_is_inc(&blk.term, x, ty)
}

/// The one block of `lp` writing `x`, if that one write is the increment.
fn find_inc(b: &Body, lp: &Vec<bool>, x: usize, ty: &IntTy) -> Option<usize> {
    let mut writes: u8 = 0;
    let mut inc: Option<usize> = None;
    let mut i: usize = 0;
    while i < b.blocks.len()
        invariant writes <= 2,
        decreases b.blocks.len() - i,
    {
        if get(lp, i) {
            writes = count_writes(&b.blocks[i], x, writes);
            if block_has_inc(&b.blocks[i], x, ty) { inc = Some(i); }
        }
        i += 1;
    }
    if writes == 1 { inc } else { None }
}

fn unwritten(b: &Body, lp: &Vec<bool>, x: usize) -> bool {
    let mut i: usize = 0;
    while i < b.blocks.len()
        decreases b.blocks.len() - i,
    {
        if get(lp, i) && count_writes(&b.blocks[i], x, 0) != 0 { return false; }
        i += 1;
    }
    true
}

fn stable(b: &Body, lp: &Vec<bool>, bound: &Atom) -> bool {
    match bound {
        Atom::Const(_) => true,
        Atom::Val(y, _) => unwritten(b, lp, *y),
        Atom::Len(y) => unwritten(b, lp, *y),
        Atom::Gap(_, _) => false,
    }
}

fn unsigned(ty: &IntTy) -> bool {
    match ty {
        IntTy::I8 | IntTy::I16 | IntTy::I32 | IntTy::I64 | IntTy::I128 | IntTy::Isize => false,
        _ => true,
    }
}

/// One pass from `seen` round `lp` without entering `inc`; `true` if it grew or reached a latch.
fn avoid_pass(b: &Body, lp: &Vec<bool>, header: usize, inc: usize, seen: &mut Vec<bool>, latch: &mut bool) -> bool {
    let mut grew = false;
    let mut x: usize = 0;
    while x < b.blocks.len()
        decreases b.blocks.len() - x,
    {
        if get(seen, x) {
            let ss = succs(&b.blocks[x].term);
            let mut j: usize = 0;
            while j < ss.len()
                decreases ss.len() - j,
            {
                let s = ss[j];
                if s == header {
                    *latch = true;
                } else if get(lp, s) && s != inc && !get(seen, s) {
                    put(seen, s, true);
                    grew = true;
                }
                j += 1;
            }
        }
        x += 1;
    }
    grew
}

/// Some way round the loop misses the increment.
fn path_avoids(b: &Body, lp: &Vec<bool>, header: usize, inc: usize) -> bool {
    let n = b.blocks.len();
    let mut seen = filled(n, false);
    put(&mut seen, header, true);
    let mut latch = false;
    let mut left = pass_bound(n);
    loop
        decreases left,
    {
        if !avoid_pass(b, lp, header, inc, &mut seen, &mut latch) || left == 0 { break; }
        left -= 1;
    }
    latch
}

/// The edge `test -> s` has `Lt(Val(c, ty), bound)`.
fn counted_at(b: &Body, lp: &Vec<bool>, header: usize, dom: &Vec<Vec<bool>>, test: usize, s: usize, c: usize, ty: &IntTy, bound: &Atom) -> Option<Counted> {
    if !unsigned(ty) || s == header || !get(lp, s) || !stable(b, lp, bound) { return None; }
    let inc = match find_inc(b, lp, c, ty) { Some(i) => i, None => return None };
    if inc == header || inc >= dom.len() || !get(&dom[inc], s) || path_avoids(b, lp, header, inc) { return None; }
    let mut body: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < lp.len()
        decreases lp.len() - i,
    {
        body.push(lp[i]);
        i += 1;
    }
    Some(Counted { header, body, counter: c, ty: int_ty_copy(ty), bound: atom_copy(bound), test_block: test, inc_block: inc })
}

/// The test edges of block `t`, read off `exec_sym_block`, so the bound and the temp copy are as
/// `cmp_atom` normalises them.
#[verifier::loop_isolation(false)]
fn counted_from(b: &Body, lp: &Vec<bool>, header: usize, dom: &Vec<Vec<bool>>, t: usize, e: &Eff) -> Option<Counted> {
    let mut i: usize = 0;
    while i < e.edge.len()
        decreases e.edge.len() - i,
    {
        let fs = &e.edge[i].1;
        let mut j: usize = 0;
        while j < fs.len()
            decreases fs.len() - j,
        {
            if let Fact::Lt(Atom::Val(c, ty), bound) = &fs[j] {
                if let Some(ct) = counted_at(b, lp, header, dom, t, e.edge[i].0, *c, ty, bound) { return Some(ct); }
            }
            j += 1;
        }
        i += 1;
    }
    None
}

/// By the spec's definition, unsigned counters only. `lp` is the union of the header's natural loops.
// ponytail: one increment per loop, so `if c { i += 1; continue; } i += 1;` isn't counted; one per latch path is the upgrade.
pub fn recognize(b: &Body, lp: &Vec<bool>, header: usize) -> Option<Counted> {
    let n = b.blocks.len();
    let mut x: usize = 0;
    while x < n
        invariant n == b.blocks@.len(),
        decreases n - x,
    {
        if get(lp, x) && block_writer(b, &b.blocks[x]) { return None; }
        x += 1;
    }
    let dom = dominators(b);
    let none: Vec<Fact> = Vec::new();
    let mut t: usize = 0;
    while t < n
        invariant n == b.blocks@.len(),
        decreases n - t,
    {
        if get(lp, t) {
            let e = exec_sym_block(b, &b.blocks[t], &none);
            if let Some(ct) = counted_from(b, lp, header, &dom, t, &e) { return Some(ct); }
        }
        t += 1;
    }
    None
}

// ------------------------------------------------------------------ facts, forward

fn facts_copy(a: &Vec<Fact>) -> Vec<Fact> {
    let mut r: Vec<Fact> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        decreases a.len() - i,
    {
        r.push(fact_copy(&a[i]));
        i += 1;
    }
    r
}

/// What of `f` the edge's facts give, `Lt ==> Le` being the one inference `check_cert` allows.
fn fact_meet(f: &Fact, edge: &Vec<Fact>) -> Option<Fact> {
    let (a, b, strict) = match f { Fact::Le(a, b) => (a, b, false), Fact::Lt(a, b) => (a, b, true) };
    let mut found = false;
    let mut lt = false;
    let mut i: usize = 0;
    while i < edge.len()
        decreases edge.len() - i,
    {
        match &edge[i] {
            Fact::Le(x, y) => if atom_eq(x, a) && atom_eq(y, b) { found = true; },
            Fact::Lt(x, y) => if atom_eq(x, a) && atom_eq(y, b) { found = true; lt = true; },
        }
        i += 1;
    }
    if !found {
        None
    } else if strict && lt {
        Some(Fact::Lt(atom_copy(a), atom_copy(b)))
    } else {
        Some(Fact::Le(atom_copy(a), atom_copy(b)))
    }
}

fn facts_meet(cur: &Vec<Fact>, edge: &Vec<Fact>) -> (Vec<Fact>, bool) {
    let mut out: Vec<Fact> = Vec::new();
    let mut changed = false;
    let mut i: usize = 0;
    while i < cur.len()
        decreases cur.len() - i,
    {
        match fact_meet(&cur[i], edge) {
            Some(g) => {
                if let (Fact::Lt(_, _), Fact::Le(_, _)) = (&cur[i], &g) { changed = true; }
                out.push(g);
            },
            None => changed = true,
        }
        i += 1;
    }
    (out, changed)
}

/// Meets one block's outgoing edges into `state`; `true` if anything changed. An edge's facts only
/// shrink as its source's do, so meeting in place reaches the greatest fixed point.
fn facts_edges(e: &Eff, state: &mut Vec<Option<Vec<Fact>>>) -> bool {
    let mut changed = false;
    let mut i: usize = 0;
    while i < e.edge.len()
        decreases e.edge.len() - i,
    {
        let t = e.edge[i].0;
        if t < state.len() {
            let next = match &state[t] {
                None => Some(facts_copy(&e.edge[i].1)),
                Some(cur) => {
                    let (m, ch) = facts_meet(cur, &e.edge[i].1);
                    if ch { Some(m) } else { None }
                },
            };
            if let Some(m) = next {
                state.set(t, Some(m));
                changed = true;
            }
        }
        i += 1;
    }
    changed
}

fn facts_pass(body: &Body, state: &mut Vec<Option<Vec<Fact>>>) -> bool {
    let mut changed = false;
    let mut b: usize = 0;
    while b < body.blocks.len() && b < state.len()
        decreases body.blocks.len() - b,
    {
        let e = match &state[b] {
            Some(fs) => Some(exec_sym_block(body, &body.blocks[b], fs)),
            None => None,
        };
        if let Some(e) = e {
            if facts_edges(&e, state) { changed = true; }
        }
        b += 1;
    }
    changed
}

/// Blocks unreached from the entry start from no facts, and so do their successors in the end.
fn facts_seed_unreached(state: &mut Vec<Option<Vec<Fact>>>) -> bool {
    let mut seeded = false;
    let mut b: usize = 0;
    while b < state.len()
        decreases state.len() - b,
    {
        let none = match &state[b] { None => true, Some(_) => false };
        if none {
            state.set(b, Some(Vec::new()));
            seeded = true;
        }
        b += 1;
    }
    seeded
}

/// Every block's facts: what every incoming edge gives, as `exec_sym_block` gives it. Entry: none.
fn block_facts(body: &Body) -> Vec<Vec<Fact>> {
    let n = body.blocks.len();
    let mut state: Vec<Option<Vec<Fact>>> = Vec::new();
    while state.len() < n
        invariant state@.len() <= n,
        decreases n - state.len(),
    {
        let first = state.len() == 0;
        state.push(if first { Some(Vec::new()) } else { None });
    }
    let mut left = pass_bound(n);
    loop
        decreases left,
    {
        let changed = facts_pass(body, &mut state);
        if !changed && !facts_seed_unreached(&mut state) { break; }
        if left == 0 { break; }
        left -= 1;
    }
    let mut out: Vec<Vec<Fact>> = Vec::new();
    let mut b: usize = 0;
    while b < state.len() && b < body.blocks.len()
        decreases body.blocks.len() - b,
    {
        out.push(match &state[b] {
            Some(fs) => match &body.blocks[b].term { Term::Abort => Vec::new(), _ => facts_copy(fs) },
            None => Vec::new(),
        });
        b += 1;
    }
    out
}

// ------------------------------------------------------------------ monomial-wise polynomials

fn mono_at(m: &Mono, coef: u64) -> Mono {
    Mono { coef, atoms: mono_copy(m).atoms }
}

fn find_mono(ms: &Vec<Mono>, atoms: &Vec<Atom>) -> (r: Option<usize>)
    ensures r matches Some(i) ==> i < ms@.len(),
{
    let mut i: usize = 0;
    while i < ms.len()
        decreases ms.len() - i,
    {
        if atoms_eq(&ms[i].atoms, atoms) { return Some(i); }
        i += 1;
    }
    None
}

fn add_mono(ms: &mut Vec<Mono>, m: &Mono) -> Result<(), CostWhy> {
    match find_mono(ms, &m.atoms) {
        Some(i) => match ms[i].coef.checked_add(m.coef) {
            Some(c) => {
                let u = mono_at(&ms[i], c);
                ms.set(i, u);
                Ok(())
            },
            None => Err(CostWhy::Overflow),
        },
        None => {
            ms.push(mono_copy(m));
            Ok(())
        },
    }
}

fn add_poly(ms: &mut Vec<Mono>, q: &Poly) -> Result<(), CostWhy> {
    let mut i: usize = 0;
    while i < q.monos.len()
        decreases q.monos.len() - i,
    {
        match add_mono(ms, &q.monos[i]) {
            Ok(_) => {},
            Err(w) => return Err(w),
        }
        i += 1;
    }
    Ok(())
}

/// Each coefficient less `q`'s, floored at 0.
fn sub_poly(ms: &mut Vec<Mono>, q: &Poly) {
    let mut i: usize = 0;
    while i < q.monos.len()
        decreases q.monos.len() - i,
    {
        if let Some(j) = find_mono(ms, &q.monos[i].atoms) {
            let have = ms[j].coef;
            let less = q.monos[i].coef;
            let u = mono_at(&ms[j], if have > less { have - less } else { 0 });
            ms.set(j, u);
        }
        i += 1;
    }
}

fn max_poly(ms: &mut Vec<Mono>, q: &Poly) {
    let mut i: usize = 0;
    while i < q.monos.len()
        decreases q.monos.len() - i,
    {
        match find_mono(ms, &q.monos[i].atoms) {
            Some(j) => if ms[j].coef < q.monos[i].coef {
                let u = mono_copy(&q.monos[i]);
                ms.set(j, u);
            },
            None => ms.push(mono_copy(&q.monos[i])),
        }
        i += 1;
    }
}

fn strip(ms: &Vec<Mono>) -> Poly {
    let mut out: Vec<Mono> = Vec::new();
    let mut i: usize = 0;
    while i < ms.len()
        decreases ms.len() - i,
    {
        if ms[i].coef != 0 { out.push(mono_copy(&ms[i])); }
        i += 1;
    }
    Poly { monos: out }
}

/// `a <= b`, monomial by monomial.
fn poly_le(a: &Poly, b: &Poly) -> bool {
    let mut i: usize = 0;
    while i < a.monos.len()
        decreases a.monos.len() - i,
    {
        if a.monos[i].coef != 0 {
            match find_mono(&b.monos, &a.monos[i].atoms) {
                Some(j) => if b.monos[j].coef < a.monos[i].coef { return false; },
                None => return false,
            }
        }
        i += 1;
    }
    true
}

fn constant(k: u64) -> Mono {
    Mono { coef: k, atoms: Vec::new() }
}

// ------------------------------------------------------------------ raising

/// The atom a `Gap` is bounded by, all the way down.
fn minuend(a: &Atom) -> Atom
    decreases a,
{
    match a {
        Atom::Gap(x, _) => minuend(x),
        _ => atom_copy(a),
    }
}

/// The first `Le(a, u)` or `Lt(a, u)`.
fn upper(facts: &Vec<Fact>, a: &Atom) -> Option<Atom> {
    let mut i: usize = 0;
    while i < facts.len()
        decreases facts.len() - i,
    {
        match &facts[i] {
            Fact::Le(t, u) => if atom_eq(t, a) { return Some(atom_copy(u)); },
            Fact::Lt(t, u) => if atom_eq(t, a) { return Some(atom_copy(u)); },
        }
        i += 1;
    }
    None
}

/// `bound_post`'s raise of one atom.
fn raise_like(facts: &Vec<Fact>, a: &Atom) -> Atom
    decreases a,
{
    if let Some(u) = upper(facts, a) { return u; }
    match a {
        Atom::Gap(x, y) => Atom::Gap(Box::new(raise_like(facts, x)), Box::new(atom_copy(y))),
        _ => atom_copy(a),
    }
}

fn atom_in(v: &Vec<Atom>, a: &Atom) -> bool {
    let mut i: usize = 0;
    while i < v.len()
        decreases v.len() - i,
    {
        if atom_eq(&v[i], a) { return true; }
        i += 1;
    }
    false
}

/// `m` reads a marked atom whose bound is new on this edge: where the fact starts, not where it is
/// carried, because a loop inside the fact's reach needs its `Gap` as written.
fn raises_here(m: &Mono, pre: &Vec<Fact>, post: &Vec<Fact>, marks: &Vec<Atom>) -> bool {
    let mut i: usize = 0;
    while i < m.atoms.len()
        decreases m.atoms.len() - i,
    {
        let t = minuend(&m.atoms[i]);
        if atom_in(marks, &t) && upper(post, &t).is_some() && upper(pre, &t).is_none() { return true; }
        i += 1;
    }
    false
}

fn raise_marked(q: &Poly, pre: &Vec<Fact>, post: &Vec<Fact>, marks: &Vec<Atom>) -> Poly {
    let mut out: Vec<Mono> = Vec::new();
    let mut i: usize = 0;
    while i < q.monos.len()
        decreases q.monos.len() - i,
    {
        let m = &q.monos[i];
        if raises_here(m, pre, post, marks) {
            let mut atoms: Vec<Atom> = Vec::new();
            let mut j: usize = 0;
            while j < m.atoms.len()
                decreases m.atoms.len() - j,
            {
                atoms.push(raise_like(post, &m.atoms[j]));
                j += 1;
            }
            out.push(Mono { coef: m.coef, atoms });
        } else {
            out.push(mono_copy(m));
        }
        i += 1;
    }
    Poly { monos: out }
}

/// `pull_post` said no to `q`: marks each atom of `q` that doesn't pull.
fn mark_failed(q: &Poly, e: &Eff, facts: &Vec<Fact>, marks: &mut Vec<Atom>) {
    let mut i: usize = 0;
    while i < q.monos.len()
        decreases q.monos.len() - i,
    {
        let m = &q.monos[i];
        let mut j: usize = 0;
        while j < m.atoms.len()
            decreases m.atoms.len() - j,
        {
            let t = minuend(&m.atoms[j]);
            let mut atoms: Vec<Atom> = Vec::new();
            atoms.push(atom_copy(&t));
            let mut monos: Vec<Mono> = Vec::new();
            monos.push(Mono { coef: 1, atoms });
            if pull_post(&Poly { monos }, e, facts).is_none() && !atom_in(marks, &t) { marks.push(t); }
            j += 1;
        }
        i += 1;
    }
}

// ------------------------------------------------------------------ potentials, backward

struct Cx<'a> {
    p: &'a Program,
    body: &'a Body,
    sums: &'a Vec<Option<Poly>>,
    facts: &'a Vec<Vec<Fact>>,
    loops: &'a Vec<Counted>,
    sizes: &'a Vec<usize>,
}

fn charge_why(t: &Term, sums: &Vec<Option<Poly>>) -> CostWhy {
    if let Term::Call(Callee::Fn(g), _, _, _) = t {
        if *g < sums.len() {
            let none = match &sums[*g] { None => true, Some(_) => false };
            if none { return CostWhy::CalleeNone(*g); }
        }
    }
    CostWhy::Unresolved
}

/// One edge's demand: `up + upc + k1 - cr - crc`, floored at 0.
fn edge_pot(next: &Poly, e: &Eff, i: usize, facts: &Vec<Fact>, marks: &mut Vec<Atom>, upc: &Poly, crc: &Poly, k1: u64, b: usize) -> Result<Poly, CostWhy>
    requires i < e.edge@.len(),
{
    let need = raise_marked(next, facts, &e.edge[i].1, marks);
    match pull_post(&need, e, facts) {
        Some((up, cr)) => {
            let mut out: Vec<Mono> = Vec::new();
            match add_poly(&mut out, &up) { Ok(_) => {}, Err(w) => return Err(w) }
            match add_poly(&mut out, upc) { Ok(_) => {}, Err(w) => return Err(w) }
            match add_mono(&mut out, &constant(k1)) { Ok(_) => {}, Err(w) => return Err(w) }
            sub_poly(&mut out, &cr);
            sub_poly(&mut out, crc);
            Ok(Poly { monos: out })
        },
        None => {
            mark_failed(&need, e, facts, marks);
            Err(CostWhy::Validator(b))
        },
    }
}

/// `b`'s potential, from its successors': the monomial-wise maximum over its edges.
fn block_pot(cx: &Cx, pots: &Vec<Poly>, marks: &mut Vec<Atom>, b: usize) -> Result<Poly, CostWhy> {
    if b >= cx.body.blocks.len() || b >= cx.facts.len() { return Err(CostWhy::Validator(b)); }
    let blk = &cx.body.blocks[b];
    let facts = &cx.facts[b];
    if let Term::Abort = &blk.term { return Ok(Poly { monos: Vec::new() }); }
    let k = blk.stmts.len() as u64;
    if k == u64::MAX { return Err(CostWhy::Overflow); }
    let k1 = k + 1;
    let mut best: Vec<Mono> = Vec::new();
    if let Term::Return = &blk.term { best.push(constant(k1)); }
    let charge = match term_charge(cx.p, &blk.term, cx.sums) { Some(c) => c, None => return Err(charge_why(&blk.term, cx.sums)) };
    let es = exec_sym_stmts(cx.body, &blk.stmts, facts);
    let (upc, crc) = match pull_post(&charge, &es, facts) { Some(x) => x, None => return Err(CostWhy::Validator(b)) };
    let e = exec_sym_block(cx.body, blk, facts);
    let mut i: usize = 0;
    while i < e.edge.len()
        decreases e.edge.len() - i,
    {
        let t = e.edge[i].0;
        if t >= pots.len() { return Err(CostWhy::Validator(b)); }
        match edge_pot(&pots[t], &e, i, facts, marks, &upc, &crc, k1, b) {
            Ok(q) => max_poly(&mut best, &q),
            Err(w) => return Err(w),
        }
        i += 1;
    }
    Ok(strip(&best))
}

/// The largest loop holding `x`, within loop `r` and short of it.
#[verifier::loop_isolation(false)]
fn child_loop(cx: &Cx, x: usize, r: Option<usize>) -> Option<usize> {
    let mut best: Option<usize> = None;
    let mut best_size: usize = 0;
    let mut i: usize = 0;
    while i < cx.loops.len() && i < cx.sizes.len()
        decreases cx.loops.len() - i,
    {
        let lp = &cx.loops[i];
        let inside = match r {
            None => true,
            Some(o) => o != i && o < cx.loops.len() && o < cx.sizes.len() && cx.sizes[i] < cx.sizes[o] && get(&cx.loops[o].body, lp.header),
        };
        if inside && get(&lp.body, x) && cx.sizes[i] > best_size {
            best = Some(i);
            best_size = cx.sizes[i];
        }
        i += 1;
    }
    best
}

fn succs_done(t: &Term, done: &Vec<bool>) -> bool {
    let ss = succs(t);
    let mut j: usize = 0;
    while j < ss.len()
        decreases ss.len() - j,
    {
        if !get(done, ss[j]) { return false; }
        j += 1;
    }
    true
}

/// Every edge out of loop `c` lands on a finished block.
fn exits_done(cx: &Cx, c: usize, done: &Vec<bool>) -> bool {
    if c >= cx.loops.len() { return false; }
    let lp = &cx.loops[c].body;
    let mut x: usize = 0;
    while x < cx.body.blocks.len()
        decreases cx.body.blocks.len() - x,
    {
        if get(lp, x) {
            let ss = succs(&cx.body.blocks[x].term);
            let mut j: usize = 0;
            while j < ss.len()
                decreases ss.len() - j,
            {
                if !get(lp, ss[j]) && !get(done, ss[j]) { return false; }
                j += 1;
            }
        }
        x += 1;
    }
    true
}

/// The monomial-wise maximum of the pots loop `c` exits to, from anywhere and from its header.
fn exit_pots(cx: &Cx, pots: &Vec<Poly>, c: usize) -> (Poly, Poly) {
    let mut all: Vec<Mono> = Vec::new();
    let mut head: Vec<Mono> = Vec::new();
    if c < cx.loops.len() {
        let lp = &cx.loops[c];
        let mut x: usize = 0;
        while x < cx.body.blocks.len()
            decreases cx.body.blocks.len() - x,
        {
            if get(&lp.body, x) {
                let ss = succs(&cx.body.blocks[x].term);
                let mut j: usize = 0;
                while j < ss.len()
                    decreases ss.len() - j,
                {
                    let s = ss[j];
                    if !get(&lp.body, s) && s < pots.len() {
                        max_poly(&mut all, &pots[s]);
                        if x == lp.header { max_poly(&mut head, &pots[s]); }
                    }
                    j += 1;
                }
            }
            x += 1;
        }
    }
    (strip(&all), strip(&head))
}

/// `P·Gap(bound, counter)`.
// ponytail: degree at most 2, so `P` holds no product and no `Gap`; a third nesting level is `DegreeCap`, and higher degree needs a multiset-product lemma.
fn times_gap(q: &Poly, lp: &Counted) -> Result<Poly, CostWhy> {
    let mut out: Vec<Mono> = Vec::new();
    let mut i: usize = 0;
    while i < q.monos.len()
        decreases q.monos.len() - i,
    {
        let m = &q.monos[i];
        let mut atoms: Vec<Atom> = Vec::new();
        if m.atoms.len() > 1 { return Err(CostWhy::DegreeCap); }
        if m.atoms.len() == 1 {
            if let Atom::Gap(_, _) = &m.atoms[0] { return Err(CostWhy::DegreeCap); }
            atoms.push(atom_copy(&m.atoms[0]));
        }
        atoms.push(Atom::Gap(Box::new(atom_copy(&lp.bound)), Box::new(Atom::Val(lp.counter, int_ty_copy(&lp.ty)))));
        out.push(Mono { coef: m.coef, atoms });
        i += 1;
    }
    Ok(Poly { monos: out })
}

/// `gap + p + rest`.
fn header_pot(gap: &Poly, p: &Poly, rest: &Poly) -> Result<Poly, CostWhy> {
    let mut out: Vec<Mono> = Vec::new();
    match add_poly(&mut out, gap) { Ok(_) => {}, Err(w) => return Err(w) }
    match add_poly(&mut out, p) { Ok(_) => {}, Err(w) => return Err(w) }
    match add_poly(&mut out, rest) { Ok(_) => {}, Err(w) => return Err(w) }
    Ok(strip(&out))
}

/// Runs the body with `pot` at the header: does it pay for itself?
fn try_header(cx: &Cx, pots: &mut Vec<Poly>, marks: &mut Vec<Atom>, c: usize, h: usize, pot: Poly, fuel: usize) -> (r: Result<bool, CostWhy>)
    decreases fuel, 2nat,
{
    if h >= pots.len() { return Err(CostWhy::Validator(h)); }
    pots.set(h, poly_copy(&pot));
    match pass(cx, pots, marks, Some(c), fuel) { Ok(_) => {}, Err(w) => return Err(w) }
    match block_pot(cx, pots, marks, h) {
        Ok(q) => Ok(poly_le(&q, &pot)),
        Err(w) => Err(w),
    }
}

/// Loop `c`, its exits' pots known: `P` from a pass with no `Gap` in the header (so no credit), then
/// the header `P·Gap + P + rest`. Exits read past the header's own are usually paid for by the
/// path's constant, so the header's exits come first and all of them only if that doesn't pay.
fn solve_loop(cx: &Cx, pots: &mut Vec<Poly>, marks: &mut Vec<Atom>, c: usize, fuel: usize) -> (r: Result<(), CostWhy>)
    decreases fuel, 3nat,
{
    if c >= cx.loops.len() { return Err(CostWhy::Validator(0)); }
    let lp = &cx.loops[c];
    let h = lp.header;
    if h >= pots.len() { return Err(CostWhy::Validator(h)); }
    let (rest, rest_head) = exit_pots(cx, pots, c);
    pots.set(h, poly_copy(&rest));
    match pass(cx, pots, marks, Some(c), fuel) { Ok(_) => {}, Err(w) => return Err(w) }
    let first = match block_pot(cx, pots, marks, h) { Ok(q) => q, Err(w) => return Err(w) };
    let mut left = mono_list(&first);
    sub_poly(&mut left, &rest);
    let per = strip(&left);
    let gap = match times_gap(&per, lp) { Ok(g) => g, Err(w) => return Err(w) };
    let cheap = match header_pot(&gap, &per, &rest_head) { Ok(q) => q, Err(w) => return Err(w) };
    match try_header(cx, pots, marks, c, h, cheap, fuel) {
        Ok(true) => return Ok(()),
        Ok(false) => {},
        Err(w) => return Err(w),
    }
    let full = match header_pot(&gap, &per, &rest) { Ok(q) => q, Err(w) => return Err(w) };
    match try_header(cx, pots, marks, c, h, full, fuel) {
        Ok(true) => Ok(()),
        Ok(false) => Err(CostWhy::Validator(h)),
        Err(w) => Err(w),
    }
}

fn mono_list(q: &Poly) -> Vec<Mono> {
    poly_copy(q).monos
}

fn mark_body(cx: &Cx, c: usize, done: &mut Vec<bool>) {
    if c < cx.loops.len() {
        let lp = &cx.loops[c].body;
        let mut x: usize = 0;
        while x < lp.len()
            decreases lp.len() - x,
        {
            if lp[x] { put(done, x, true); }
            x += 1;
        }
    }
}

/// One step of `pass` at block `x`: a block, or the whole child loop it's in. `true` if it finished one.
fn pass_step(cx: &Cx, pots: &mut Vec<Poly>, marks: &mut Vec<Atom>, r: Option<usize>, x: usize, done: &mut Vec<bool>, fuel: usize) -> (out: Result<bool, CostWhy>)
    decreases fuel, 0nat,
{
    if x >= cx.body.blocks.len() { return Ok(false); }
    match child_loop(cx, x, r) {
        Some(c) => {
            if !exits_done(cx, c, done) { return Ok(false); }
            if fuel == 0 { return Err(CostWhy::NotCounted(x)); }
            match solve_loop(cx, pots, marks, c, fuel - 1) { Ok(_) => {}, Err(w) => return Err(w) }
            mark_body(cx, c, done);
            Ok(true)
        },
        None => {
            if !succs_done(&cx.body.blocks[x].term, done) { return Ok(false); }
            let q = match block_pot(cx, pots, marks, x) { Ok(q) => q, Err(w) => return Err(w) };
            if x < pots.len() { pots.set(x, q); }
            put(done, x, true);
            Ok(true)
        },
    }
}

/// Everything in region `r` (a loop, or the whole fn) but its header, successors before predecessors
/// with back edges cut, and a child loop as one node. Stuck means a cycle no counted loop explains.
// ponytail: each level re-solves its children, two or three times per pass: exponential in nesting depth, which `DegreeCap` keeps at 2 unless the bounds are constants. Memoising a child on its exits' pots is the upgrade.
fn pass(cx: &Cx, pots: &mut Vec<Poly>, marks: &mut Vec<Atom>, r: Option<usize>, fuel: usize) -> (out: Result<(), CostWhy>)
    decreases fuel, 1nat,
{
    let n = cx.body.blocks.len();
    let mut done = filled(n, false);
    if let Some(l) = r {
        if l < cx.loops.len() {
            let lp = &cx.loops[l];
            let mut x: usize = 0;
            while x < n
                decreases n - x,
            {
                if !get(&lp.body, x) || x == lp.header { put(&mut done, x, true); }
                x += 1;
            }
        }
    }
    let mut left = pass_bound(n);
    loop
        decreases left,
    {
        let mut progress = false;
        let mut x = n;
        while x > 0
            decreases x,
        {
            x -= 1;
            if !get(&done, x) {
                match pass_step(cx, pots, marks, r, x, &mut done, fuel) {
                    Ok(true) => progress = true,
                    Ok(false) => {},
                    Err(w) => return Err(w),
                }
            }
        }
        if !progress || left == 0 { break; }
        left -= 1;
    }
    let mut x: usize = 0;
    while x < n
        decreases n - x,
    {
        if !get(&done, x) { return Err(CostWhy::NotCounted(x)); }
        x += 1;
    }
    Ok(())
}

// ------------------------------------------------------------------ the certificate

/// The union of the natural loops of `h`, from its back edges.
fn loop_of(b: &Body, be: &Vec<(usize, usize)>, h: usize) -> Vec<bool> {
    let mut lp = filled(b.blocks.len(), false);
    let mut i: usize = 0;
    while i < be.len()
        decreases be.len() - i,
    {
        if be[i].1 == h {
            let one = natural_loop(b, be[i].0, h);
            let mut x: usize = 0;
            while x < one.len()
                decreases one.len() - x,
            {
                if one[x] { put(&mut lp, x, true); }
                x += 1;
            }
        }
        i += 1;
    }
    lp
}

fn count_true(v: &Vec<bool>) -> usize {
    let mut c: usize = 0;
    let mut i: usize = 0;
    while i < v.len()
        invariant c <= i,
        decreases v.len() - i,
    {
        if v[i] { c += 1; }
        i += 1;
    }
    c
}

/// Every loop of `b`, each counted, or the first that isn't.
fn counted_loops(b: &Body) -> Result<(Vec<Counted>, Vec<usize>), CostWhy> {
    let dom = dominators(b);
    let be = back_edges(b, &dom);
    let mut loops: Vec<Counted> = Vec::new();
    let mut sizes: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < be.len()
        decreases be.len() - i,
    {
        let h = be[i].1;
        let mut seen = false;
        let mut j: usize = 0;
        while j < loops.len()
            decreases loops.len() - j,
        {
            if loops[j].header == h { seen = true; }
            j += 1;
        }
        if !seen {
            let lp = loop_of(b, &be, h);
            match recognize(b, &lp, h) {
                Some(ct) => {
                    sizes.push(count_true(&lp));
                    loops.push(ct);
                },
                None => return Err(CostWhy::NotCounted(h)),
            }
        }
        i += 1;
    }
    Ok((loops, sizes))
}

/// A certificate for fn `f` under the callee summaries `sums`: facts forward, then potentials
/// backward, restarting whenever a predecessor can't read an atom a fact can bound.
pub fn build_cert(p: &Program, f: usize, sums: &Vec<Option<Poly>>) -> Result<Cert, CostWhy> {
    if f >= p.fns.len() { return Err(CostWhy::NotWf); }
    let body = &p.fns[f];
    let n = body.blocks.len();
    if n == 0 { return Err(CostWhy::Validator(0)); }
    let (loops, sizes) = match counted_loops(body) { Ok(x) => x, Err(w) => return Err(w) };
    let facts = block_facts(body);
    let cx = Cx { p, body, sums, facts: &facts, loops: &loops, sizes: &sizes };
    let mut pots: Vec<Poly> = Vec::new();
    while pots.len() < n
        invariant pots@.len() <= n,
        decreases n - pots.len(),
    {
        pots.push(Poly { monos: Vec::new() });
    }
    let mut marks: Vec<Atom> = Vec::new();
    let mut tries: u8 = 16;
    loop
        decreases tries,
    {
        let before = marks.len();
        match pass(&cx, &mut pots, &mut marks, None, loops.len()) {
            Ok(_) => break,
            Err(CostWhy::Validator(b)) => if marks.len() == before || tries == 0 { return Err(CostWhy::Validator(b)); },
            Err(w) => return Err(w),
        }
        tries -= 1;
    }
    let mut blocks: Vec<BlockCert> = Vec::new();
    let mut b: usize = 0;
    while b < n && b < facts.len() && b < pots.len()
        decreases n - b,
    {
        blocks.push(BlockCert { facts: facts_copy(&facts[b]), pot: poly_copy(&pots[b]) });
        b += 1;
    }
    Ok(Cert { blocks })
}

} // verus!
