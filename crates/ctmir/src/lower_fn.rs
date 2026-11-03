//! The translator's bodies and closure (verified: `lower` ensures `rel::lowers`). The fn order is
//! fixed first (`closure_order`, the old translator's discovery order); then each body's
//! normal-edge reachable blocks are lowered, the others become empty `Abort` blocks.
use crate::json::bytes_eq;
use crate::look::*;
use crate::lower::*;
use crate::lower_const::*;
use crate::lower_term::*;
use crate::mir::*;
use crate::policy::*;
#[cfg(verus_keep_ghost)]
use crate::rel::*;
#[cfg(verus_keep_ghost)]
use crate::sem::*;
use ctcore::syntax as c;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ sites (report metadata)

fn push_dec(v: &mut Vec<u8>, n: usize)
    decreases n,
{
    if n >= 10 { push_dec(v, n / 10); }
    v.push((n % 10) as u8 + 48);
}

/// `<file>:<line>` of a span, or `?`.
pub fn site(m: &MirCrate, sp: Span) -> Vec<u8> {
    match x_span(m, sp) {
        Some(r) => {
            let mut v = copy_bytes(&r.file);
            v.push(b':');
            push_dec(&mut v, r.line);
            v
        },
        None => msg(b"?"),
    }
}

// ------------------------------------------------------------------ reachable blocks

/// A terminator's normal successors, in the order the walk visits them.
pub open spec fn succ_seq(t: TerminatorKind) -> Seq<usize> {
    match t {
        TerminatorKind::Goto { target } => seq![target],
        TerminatorKind::Drop { target, .. } => seq![target],
        TerminatorKind::Assert { target, .. } => seq![target],
        TerminatorKind::Call { target, .. } => match target { Some(x) => seq![x], None => seq![] },
        TerminatorKind::SwitchInt { discr: _, targets } => targets.branches@.map_values(|br: (u128, usize)| br.1).push(targets.otherwise),
        _ => seq![],
    }
}

fn succs(t: &TerminatorKind) -> (v: Vec<usize>)
    ensures v@ == succ_seq(*t),
{
    let mut v: Vec<usize> = Vec::new();
    match t {
        TerminatorKind::Goto { target } | TerminatorKind::Drop { target, .. } | TerminatorKind::Assert { target, .. } => v.push(*target),
        TerminatorKind::Call { target, .. } => if let Some(x) = target { v.push(*x); },
        TerminatorKind::SwitchInt { targets, .. } => {
            let mut k: usize = 0;
            while k < targets.branches.len()
                invariant k <= targets.branches@.len(), v@ == targets.branches@.subrange(0, k as int).map_values(|br: (u128, usize)| br.1),
                decreases targets.branches.len() - k,
            {
                v.push(targets.branches[k].1);
                proof { assert(v@ =~= targets.branches@.subrange(0, k + 1).map_values(|br: (u128, usize)| br.1)); }
                k += 1;
            }
            proof { assert(targets.branches@.subrange(0, k as int) =~= targets.branches@); }
            v.push(targets.otherwise);
        },
        _ => {},
    }
    proof { assert(v@ =~= succ_seq(*t)); }
    v
}

pub proof fn lemma_marks(r: Seq<bool>, i: nat)
    ensures marks(r).contains(i) == (i < r.len() && r[i as int]),
{
    let w = Seq::new(r.len(), |k: int| k as nat);
    let pred = |k: nat| k < r.len() && r[k as int];
    let f = w.filter(pred);
    f.to_set_ensures();
    if i < r.len() && r[i as int] {
        assert(w[i as int] == i);
        w.lemma_filter_contains(pred, i as int);
    }
    if f.contains(i) {
        let k = choose|k: int| 0 <= k < f.len() && f[k] == i;
        w.lemma_filter_pred(pred, k);
    }
}

/// Every successor of a terminator is a reached block.
pub open spec fn closed_at(t: TerminatorKind, s: Seq<bool>) -> bool {
    forall|i: int| 0 <= i < succ_seq(t).len() ==> (#[trigger] succ_seq(t)[i]) < s.len() && s[succ_seq(t)[i] as int]
}

proof fn lemma_succs_in(t: TerminatorKind, r: Seq<bool>)
    requires closed_at(t, r),
    ensures succs_in(t, marks(r)),
{
    assert forall|i: int| 0 <= i < succ_seq(t).len() implies marks(r).contains(#[trigger] succ_seq(t)[i] as nat) by {
        lemma_marks(r, succ_seq(t)[i] as nat);
    };
    match t {
        TerminatorKind::SwitchInt { discr: _, targets } => {
            assert(succ_seq(t)[targets.branches@.len() as int] == targets.otherwise);
            assert(marks(r).contains(succ_seq(t)[targets.branches@.len() as int] as nat));
            assert forall|k: int| 0 <= k < targets.branches@.len() implies marks(r).contains((#[trigger] targets.branches@[k]).1 as nat) by {
                assert(succ_seq(t)[k] == targets.branches@[k].1);
                assert(marks(r).contains(succ_seq(t)[k] as nat));
            };
        },
        TerminatorKind::Goto { target } => { assert(marks(r).contains(succ_seq(t)[0] as nat)); },
        TerminatorKind::Drop { target, .. } => { assert(marks(r).contains(succ_seq(t)[0] as nat)); },
        TerminatorKind::Assert { target, .. } => { assert(marks(r).contains(succ_seq(t)[0] as nat)); },
        TerminatorKind::Call { target, .. } => if target is Some { assert(marks(r).contains(succ_seq(t)[0] as nat)); },
        _ => {},
    }
}

proof fn lemma_closed_mono(t: TerminatorKind, s1: Seq<bool>, s2: Seq<bool>)
    requires s1.len() == s2.len(), forall|i: int| 0 <= i < s1.len() && #[trigger] s1[i] ==> s2[i], closed_at(t, s1),
    ensures closed_at(t, s2),
{
    assert forall|i: int| 0 <= i < succ_seq(t).len() implies (#[trigger] succ_seq(t)[i]) < s2.len() && s2[succ_seq(t)[i] as int] by {
        assert(s1[succ_seq(t)[i] as int]);
    };
}

pub open spec fn count_true(s: Seq<bool>) -> nat
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { count_true(s.drop_last()) + if s.last() { 1nat } else { 0nat } }
}

proof fn lemma_count(s: Seq<bool>, i: int)
    requires 0 <= i < s.len(), !s[i],
    ensures count_true(s.update(i, true)) == count_true(s) + 1, count_true(s) < s.len(),
    decreases s.len(),
{
    let u = s.update(i, true);
    if i == s.len() - 1 {
        assert(u.drop_last() =~= s.drop_last());
        lemma_count_le(s.drop_last());
    } else {
        assert(u.drop_last() =~= s.drop_last().update(i, true));
        lemma_count(s.drop_last(), i);
    }
}

proof fn lemma_count_le(s: Seq<bool>)
    ensures count_true(s) <= s.len(),
    decreases s.len(),
{
    if s.len() > 0 { lemma_count_le(s.drop_last()); }
}

/// Blocks reachable from block 0 along normal edges; `None` if a target is out of range.
pub fn reach(b: &Body) -> (r: Option<Vec<bool>>)
    ensures r matches Some(s) ==> s@.len() == b.blocks@.len() && s@.len() > 0 && s@[0]
        && forall|bb: int| 0 <= bb < s@.len() && #[trigger] s@[bb] ==> succs_in(b.blocks@[bb].terminator.kind, marks(s@)),
{
    let n = b.blocks.len();
    if n == 0 { return None; }
    let mut seen: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n, seen@.len() == i, forall|k: int| 0 <= k < i ==> !seen@[k],
        decreases n - i,
    {
        seen.push(false);
        i += 1;
    }
    proof { lemma_count(seen@, 0); }
    seen.set(0, true);
    let mut work: Vec<usize> = Vec::new();
    work.push(0);
    proof {
        assert(work@[0] == 0usize);
        assert forall|x: int| 0 <= x < n && #[trigger] seen@[x] && !work@.contains(x as usize) implies closed_at(b.blocks@[x].terminator.kind, seen@) by {
            if x != 0 { assert(!seen@[x]); } else { assert(work@.contains(0usize)); }
        };
    }
    while work.len() > 0
        invariant
            n == b.blocks@.len(), seen@.len() == n, seen@[0],
            forall|k: int| 0 <= k < work@.len() ==> (#[trigger] work@[k]) < n && seen@[work@[k] as int],
            forall|k1: int, k2: int| 0 <= k1 < k2 < work@.len() ==> work@[k1] != work@[k2],
            forall|x: int| 0 <= x < n && #[trigger] seen@[x] && !work@.contains(x as usize) ==> closed_at(b.blocks@[x].terminator.kind, seen@),
        decreases n - count_true(seen@), work@.len(),
    {
        let ghost c0 = count_true(seen@);
        let ghost w0 = work@.len();
        let ghost wold = work@;
        let bb = work.pop().unwrap();
        proof {
            assert(wold == work@.push(bb));
            assert forall|k: int| 0 <= k < work@.len() implies work@[k] != bb by { assert(wold[k] == work@[k]); assert(wold[wold.len() - 1] == bb); };
            assert(!work@.contains(bb));
        }
        let succ = succs(&b.blocks[bb].terminator.kind);
        proof { lemma_count_le(seen@); }
        let mut k: usize = 0;
        while k < succ.len()
            invariant
                n == b.blocks@.len(), seen@.len() == n, seen@[0], bb < n, seen@[bb as int], !work@.contains(bb),
                succ@ == succ_seq(b.blocks@[bb as int].terminator.kind), k <= succ@.len(),
                forall|i: int| 0 <= i < k ==> (#[trigger] succ@[i]) < n && seen@[succ@[i] as int],
                forall|kk: int| 0 <= kk < work@.len() ==> (#[trigger] work@[kk]) < n && seen@[work@[kk] as int],
                forall|k1: int, k2: int| 0 <= k1 < k2 < work@.len() ==> work@[k1] != work@[k2],
                forall|x: int| 0 <= x < n && #[trigger] seen@[x] && !work@.contains(x as usize) && x != bb ==> closed_at(b.blocks@[x].terminator.kind, seen@),
                count_true(seen@) >= c0, count_true(seen@) <= n, work@.len() + c0 == w0 - 1 + count_true(seen@),
            decreases succ@.len() - k,
        {
            let s = succ[k];
            if s >= n { return None; }
            if !seen[s] {
                let ghost s0 = seen@;
                let ghost wk = work@;
                proof { lemma_count(seen@, s as int); }
                seen.set(s, true);
                proof { assert(!work@.contains(s)); }
                work.push(s);
                proof {
                    assert forall|x: int| 0 <= x < n && #[trigger] seen@[x] && !work@.contains(x as usize) && x != bb
                        implies closed_at(b.blocks@[x].terminator.kind, seen@) by {
                        assert(work@[wk.len() as int] == s);
                        assert(x != s);
                        assert(!wk.contains(x as usize)) by { if wk.contains(x as usize) { let i = choose|i: int| 0 <= i < wk.len() && wk[i] == x as usize; assert(work@[i] == x as usize); } };
                        assert(s0[x]);
                        lemma_closed_mono(b.blocks@[x].terminator.kind, s0, seen@);
                    };
                    assert(!work@.contains(bb)) by { if work@.contains(bb) { let i = choose|i: int| 0 <= i < work@.len() && work@[i] == bb; if i < wk.len() { assert(wk[i] == bb); } } };
                }
            }
            k += 1;
        }
        proof { lemma_count_le(seen@); }
    }
    proof {
        assert forall|x: int| 0 <= x < n && #[trigger] seen@[x] implies succs_in(b.blocks@[x].terminator.kind, marks(seen@)) by {
            lemma_succs_in(b.blocks@[x].terminator.kind, seen@);
        };
    }
    Some(seen)
}

// ------------------------------------------------------------------ shapes and monotonicity

/// An rvalue image's temps are its charge.
pub proof fn lemma_rv_len(m: MirCrate, b: Body, rv: Rvalue, cr: c::Rvalue, pre: Seq<c::Stmt>, base: nat)
    requires lowers_rv(m, b, rv, cr, pre, base),
    ensures pre.len() == rv_charge(m, rv),
{
    match rv {
        Rvalue::Use(x, _) => lemma_op_shape(m, b, x, cr->Use_0, pre, base),
        Rvalue::UnaryOp(op, x) => match op {
            UnOp::Not | UnOp::Neg => lemma_op_shape(m, b, x, cr->Un_2, pre, base),
            _ => {},
        },
        Rvalue::Cast(ck, x, _) => match ck {
            CastKind::IntToInt => lemma_op_shape(m, b, x, cr->Cast_2, pre, base),
            _ => lemma_op_shape(m, b, x, cr->Use_0, pre, base),
        },
        Rvalue::Repeat(x, _) => lemma_op_shape(m, b, x, cr->Repeat_0, pre, base),
        _ => {},
    }
}

/// A statement image's length is `slen`, and the statement is `stmt_ok`.
pub proof fn lemma_stmt_len(m: MirCrate, b: Body, nloc: nat, ncore: nat, s: Statement, cs: Seq<c::Stmt>)
    requires lowers_stmt(m, b, nloc, ncore, s, cs),
    ensures cs.len() == slen(m, s), stmt_ok(m, b, s),
{
    if let StatementKind::Assign(p, rv) = s.kind {
        let base = choose|base: nat| tmps_in(base, (cs.len() - 1) as nat, nloc, ncore) && #[trigger] lowers_rv(m, b, rv, cs.last()->Assign_1, cs.drop_last(), base);
        lemma_rv_len(m, b, rv, cs.last()->Assign_1, cs.drop_last(), base);
    }
}

pub proof fn lemma_stmt_mono(m: MirCrate, b: Body, nloc: nat, n1: nat, n2: nat, s: Statement, cs: Seq<c::Stmt>)
    requires n1 <= n2, lowers_stmt(m, b, nloc, n1, s, cs),
    ensures lowers_stmt(m, b, nloc, n2, s, cs),
{
    if let StatementKind::Assign(p, rv) = s.kind {
        let base = choose|base: nat| tmps_in(base, (cs.len() - 1) as nat, nloc, n1) && #[trigger] lowers_rv(m, b, rv, cs.last()->Assign_1, cs.drop_last(), base);
        assert(tmps_in(base, (cs.len() - 1) as nat, nloc, n2));
    }
}

pub proof fn lemma_term_mono(m: MirCrate, pol: Policy, ord: Seq<usize>, b: Body, nloc: nat, n1: nat, n2: nat, t: TerminatorKind, pre: Seq<c::Stmt>, ct: c::Term)
    requires n1 <= n2, lowers_term(m, pol, ord, b, nloc, n1, t, pre, ct),
    ensures lowers_term(m, pol, ord, b, nloc, n2, t, pre, ct),
{
    let base = choose|base: nat| tmps_in(base, pre.len(), nloc, n1) && #[trigger] lowers_term_at(m, pol, ord, b, nloc, n1, t, pre, ct, base);
    assert(lowers_term_at(m, pol, ord, b, nloc, n2, t, pre, ct, base));
}

pub proof fn lemma_block_mono(m: MirCrate, pol: Policy, ord: Seq<usize>, b: Body, nloc: nat, n1: nat, n2: nat, blk: BasicBlock, cb: c::Block)
    requires n1 <= n2, lowers_block(m, pol, ord, b, nloc, n1, blk, cb),
    ensures lowers_block(m, pol, ord, b, nloc, n2, blk, cb),
{
    let ss = blk.statements@;
    let cs = cb.stmts@;
    assert forall|i: int| 0 <= i < ss.len() implies lowers_stmt(m, b, nloc, n2, #[trigger] ss[i],
        cs.subrange(soff(m, ss, i as nat) as int, soff(m, ss, (i + 1) as nat) as int)) by {
        lemma_stmt_mono(m, b, nloc, n1, n2, ss[i], cs.subrange(soff(m, ss, i as nat) as int, soff(m, ss, (i + 1) as nat) as int));
    };
    lemma_term_mono(m, pol, ord, b, nloc, n1, n2, blk.terminator.kind, cs.subrange(soff(m, ss, ss.len()) as int, cs.len() as int), cb.term);
}

pub proof fn lemma_block_rel_mono(m: MirCrate, pol: Policy, ord: Seq<usize>, b: Body, nloc: nat, n1: nat, n2: nat, r: Seq<bool>,
    blk: BasicBlock, cb: c::Block, reached: bool)
    requires n1 <= n2, block_rel(m, pol, ord, b, nloc, n1, r, blk, cb, reached),
    ensures block_rel(m, pol, ord, b, nloc, n2, r, blk, cb, reached),
{
    if reached { lemma_block_mono(m, pol, ord, b, nloc, n1, n2, blk, cb); }
}

proof fn lemma_soff_mono(m: MirCrate, ss: Seq<Statement>, i: nat, n: nat)
    requires i <= n <= ss.len(),
    ensures soff(m, ss, i) <= soff(m, ss, n),
    decreases n - i,
{
    if i < n { lemma_soff_mono(m, ss, i, (n - 1) as nat); }
}

// ------------------------------------------------------------------ blocks and bodies

/// The images of the first `i` statements of a block, one after another.
#[verifier::opaque]
pub open spec fn stmts_rel(m: MirCrate, b: Body, nloc: nat, ncore: nat, ss: Seq<Statement>, i: nat, cs: Seq<c::Stmt>) -> bool {
    cs.len() == soff(m, ss, i) && forall|k: int| 0 <= k < i ==> lowers_stmt(m, b, nloc, ncore, #[trigger] ss[k],
        cs.subrange(soff(m, ss, k as nat) as int, soff(m, ss, (k + 1) as nat) as int))
}

proof fn lemma_stmts_init(m: MirCrate, b: Body, nloc: nat, ncore: nat, ss: Seq<Statement>)
    ensures stmts_rel(m, b, nloc, ncore, ss, 0, Seq::<c::Stmt>::empty()),
{
    reveal(stmts_rel);
}

proof fn lemma_stmt_prev(m: MirCrate, b: Body, nloc: nat, n1: nat, n2: nat, ss: Seq<Statement>, i: nat, st0: Seq<c::Stmt>, img: Seq<c::Stmt>, k: int)
    requires 0 <= k < i, i <= ss.len(), n1 <= n2, st0.len() == soff(m, ss, i),
        lowers_stmt(m, b, nloc, n1, ss[k], st0.subrange(soff(m, ss, k as nat) as int, soff(m, ss, (k + 1) as nat) as int)),
    ensures lowers_stmt(m, b, nloc, n2, ss[k], (st0 + img).subrange(soff(m, ss, k as nat) as int, soff(m, ss, (k + 1) as nat) as int)),
{
    lemma_soff_mono(m, ss, (k + 1) as nat, i);
    lemma_soff_mono(m, ss, k as nat, (k + 1) as nat);
    assert((st0 + img).subrange(soff(m, ss, k as nat) as int, soff(m, ss, (k + 1) as nat) as int)
        =~= st0.subrange(soff(m, ss, k as nat) as int, soff(m, ss, (k + 1) as nat) as int));
    lemma_stmt_mono(m, b, nloc, n1, n2, ss[k], st0.subrange(soff(m, ss, k as nat) as int, soff(m, ss, (k + 1) as nat) as int));
}

/// One step of `lower_block`'s statement loop: the new image after the old ones.
proof fn lemma_stmt_step(m: MirCrate, b: Body, nloc: nat, n1: nat, n2: nat, ss: Seq<Statement>, i: nat, st0: Seq<c::Stmt>, img: Seq<c::Stmt>)
    requires i < ss.len(), n1 <= n2, stmts_rel(m, b, nloc, n1, ss, i, st0), lowers_stmt(m, b, nloc, n2, ss[i as int], img),
    ensures stmts_rel(m, b, nloc, n2, ss, i + 1, st0 + img),
{
    hide(lowers_stmt);
    lemma_stmt_len(m, b, nloc, n2, ss[i as int], img);
    reveal(stmts_rel);
    assert forall|k: int| 0 <= k < i + 1 implies lowers_stmt(m, b, nloc, n2, #[trigger] ss[k], (st0 + img).subrange(soff(m, ss, k as nat) as int, soff(m, ss, (k + 1) as nat) as int)) by {
        lemma_stmt_k(m, b, nloc, n1, n2, ss, i, st0, img, k);
    };
}

proof fn lemma_stmt_k(m: MirCrate, b: Body, nloc: nat, n1: nat, n2: nat, ss: Seq<Statement>, i: nat, st0: Seq<c::Stmt>, img: Seq<c::Stmt>, k: int)
    requires 0 <= k <= i, i < ss.len(), n1 <= n2, st0.len() == soff(m, ss, i), img.len() == slen(m, ss[i as int]),
        k < i ==> lowers_stmt(m, b, nloc, n1, ss[k], st0.subrange(soff(m, ss, k as nat) as int, soff(m, ss, (k + 1) as nat) as int)),
        k == i ==> lowers_stmt(m, b, nloc, n2, ss[i as int], img),
    ensures lowers_stmt(m, b, nloc, n2, ss[k], (st0 + img).subrange(soff(m, ss, k as nat) as int, soff(m, ss, (k + 1) as nat) as int)),
{
    if k < i { lemma_stmt_prev(m, b, nloc, n1, n2, ss, i, st0, img, k); } else { lemma_stmt_last(m, ss, i, st0, img); }
}

proof fn lemma_stmt_last(m: MirCrate, ss: Seq<Statement>, i: nat, st0: Seq<c::Stmt>, img: Seq<c::Stmt>)
    requires i < ss.len(), st0.len() == soff(m, ss, i), img.len() == slen(m, ss[i as int]),
    ensures (st0 + img).subrange(soff(m, ss, i) as int, soff(m, ss, i + 1) as int) == img,
{
    assert((st0 + img).subrange(soff(m, ss, i) as int, soff(m, ss, i + 1) as int) =~= img);
}

/// The terminator closes `lower_block`.
proof fn lemma_block_close(m: MirCrate, pol: Policy, ord: Seq<usize>, b: Body, nloc: nat, n1: nat, n2: nat, blk: BasicBlock,
    st0: Seq<c::Stmt>, pre: Seq<c::Stmt>, ct: c::Term, cb: c::Block)
    requires
        n1 <= n2, stmts_rel(m, b, nloc, n1, blk.statements@, blk.statements@.len(), st0),
        term_ok(m, cpol(pol), b, blk.terminator.kind), lowers_term(m, pol, ord, b, nloc, n2, blk.terminator.kind, pre, ct),
        cb.stmts@ == st0 + pre, cb.term == ct,
    ensures block_ok(m, cpol(pol), b, blk), lowers_block(m, pol, ord, b, nloc, n2, blk, cb),
{
    hide(lowers_stmt);
    hide(lowers_term);
    hide(term_ok);
    let ss = blk.statements@;
    let cs = cb.stmts@;
    assert forall|k: int| 0 <= k < ss.len() implies lowers_stmt(m, b, nloc, n2, #[trigger] ss[k],
        cs.subrange(soff(m, ss, k as nat) as int, soff(m, ss, (k + 1) as nat) as int)) by {
        lemma_stmts_at(m, b, nloc, n1, ss, ss.len(), st0, k);
        lemma_stmt_prev(m, b, nloc, n1, n2, ss, ss.len(), st0, pre, k);
    };
    lemma_stmts_len(m, b, nloc, n1, ss, ss.len(), st0);
    assert(cs.subrange(soff(m, ss, ss.len()) as int, cs.len() as int) =~= pre);
    lemma_block_ok(m, pol, b, nloc, n1, blk, st0);
}

proof fn lemma_stmts_len(m: MirCrate, b: Body, nloc: nat, ncore: nat, ss: Seq<Statement>, i: nat, cs: Seq<c::Stmt>)
    requires stmts_rel(m, b, nloc, ncore, ss, i, cs),
    ensures cs.len() == soff(m, ss, i),
{
    reveal(stmts_rel);
}

/// An instance of `stmts_rel`.
proof fn lemma_stmts_at(m: MirCrate, b: Body, nloc: nat, ncore: nat, ss: Seq<Statement>, i: nat, cs: Seq<c::Stmt>, k: int)
    requires stmts_rel(m, b, nloc, ncore, ss, i, cs), 0 <= k < i,
    ensures cs.len() == soff(m, ss, i), lowers_stmt(m, b, nloc, ncore, ss[k], cs.subrange(soff(m, ss, k as nat) as int, soff(m, ss, (k + 1) as nat) as int)),
{
    reveal(stmts_rel);
}

proof fn lemma_block_ok(m: MirCrate, pol: Policy, b: Body, nloc: nat, n1: nat, blk: BasicBlock, st0: Seq<c::Stmt>)
    requires stmts_rel(m, b, nloc, n1, blk.statements@, blk.statements@.len(), st0), term_ok(m, cpol(pol), b, blk.terminator.kind),
    ensures block_ok(m, cpol(pol), b, blk),
{
    hide(lowers_stmt);
    let ss = blk.statements@;
    assert forall|k: int| 0 <= k < ss.len() implies stmt_ok(m, b, #[trigger] ss[k]) by {
        lemma_stmts_at(m, b, nloc, n1, ss, ss.len(), st0, k);
        lemma_stmt_len(m, b, nloc, n1, ss[k], st0.subrange(soff(m, ss, k as nat) as int, soff(m, ss, (k + 1) as nat) as int));
    };
    reveal(block_ok);
}

fn sites_n(v: &mut Vec<Vec<u8>>, s: &Vec<u8>, n: usize) {
    let mut i: usize = 0;
    while i < n
        invariant i <= n,
        decreases n - i,
    {
        v.push(copy_bytes(s));
        i += 1;
    }
}

/// A block's statements: their images one after another (`bad` when one is rejected).
pub fn lower_stmts(m: &MirCrate, b: &Body, tmp: &mut Tmp, path: &Vec<u8>, bb: usize, errs: &mut Vec<Reject>)
    -> (r: (Vec<c::Stmt>, Vec<Vec<u8>>, bool))
    requires bb < b.blocks@.len(), old(tmp).nloc == b.locals@.len(), old(tmp).pre@.len() == 0,
    ensures final(tmp).nloc == b.locals@.len(), final(tmp).pre@.len() == 0,
        !r.2 ==> tbase(*final(tmp)) >= tbase(*old(tmp))
            && stmts_rel(*m, *b, b.locals@.len(), tbase(*final(tmp)), b.blocks@[bb as int].statements@, b.blocks@[bb as int].statements@.len(), r.0@),
{
    let ghost nloc = b.locals@.len();
    let ghost t00 = *tmp;
    let blk = &b.blocks[bb];
    let ghost ss = blk.statements@;
    let mut stmts: Vec<c::Stmt> = Vec::new();
    let mut sites: Vec<Vec<u8>> = Vec::new();
    let mut bad = false;
    let mut i: usize = 0;
    proof { lemma_stmts_init(*m, *b, nloc, tbase(*tmp), ss); }
    while i < blk.statements.len()
        invariant
            i <= ss.len(), ss == blk.statements@, *blk == b.blocks@[bb as int], tmp.nloc == nloc, tmp.pre@.len() == 0, nloc == b.locals@.len(),
            !bad ==> tbase(*tmp) >= tbase(t00) && stmts_rel(*m, *b, nloc, tbase(*tmp), ss, i as nat, stmts@),
        decreases blk.statements.len() - i,
    {
        let s = &blk.statements[i];
        let st_site = site(m, s.span);
        let ghost t1 = *tmp;
        let ghost st0 = stmts@;
        match lower_stmt(m, b, s, tmp) {
            Ok(Some(st)) => {
                let ghost img = tmp.pre@.push(st);
                let n0 = tmp.pre.len();
                stmts.append(&mut tmp.pre);
                stmts.push(st);
                sites_n(&mut sites, &st_site, n0);
                sites.push(st_site);
                proof {
                    assert(stmts@ =~= st0 + img);
                    if !bad { lemma_stmt_step(*m, *b, nloc, tbase(t1), tbase(*tmp), ss, i as nat, st0, img); }
                }
            },
            Ok(None) => {
                proof {
                    assert(st0 + Seq::<c::Stmt>::empty() =~= st0);
                    if !bad { lemma_stmt_step(*m, *b, nloc, tbase(t1), tbase(*tmp), ss, i as nat, st0, Seq::<c::Stmt>::empty()); }
                }
            },
            Err(e) => {
                errs.push(Reject::Unsupported { path: copy_bytes(path), what: e, site: st_site });
                bad = true;
                tmp.pre.clear();
                tmp.nloc = b.locals.len();
            },
        }
        i += 1;
    }
    (stmts, sites, bad)
}

/// One reachable block: its statements' images, then the terminator's temps and image. The
/// declassify site is the terminator's, when it is a declassify call.
pub fn lower_block(m: &MirCrate, pol: &Policy, order: &Vec<usize>, keys: &mut Keys, b: &Body, tmp: &mut Tmp, path: &Vec<u8>, bb: usize,
    errs: &mut Vec<Reject>) -> (r: Option<(c::Block, Vec<Vec<u8>>, Option<Vec<u8>>)>)
    requires bb < b.blocks@.len(), old(tmp).nloc == b.locals@.len(), old(tmp).pre@.len() == 0,
    ensures final(tmp).nloc == b.locals@.len(), final(tmp).pre@.len() == 0,
        r matches Some((cb, _, _)) ==> {
            let blk = b.blocks@[bb as int];
            &&& tbase(*final(tmp)) >= tbase(*old(tmp))
            &&& block_ok(*m, cpol(*pol), *b, blk) && callees_in(*m, cpol(*pol), *b, blk.terminator.kind, ord_set(order@))
            &&& lowers_block(*m, *pol, order@, *b, b.locals@.len(), tbase(*final(tmp)), blk, cb)
        },
{
    let ghost nloc = b.locals@.len();
    let ghost t00 = *tmp;
    let (mut stmts, mut sites, bad) = lower_stmts(m, b, tmp, path, bb, errs);
    let blk = &b.blocks[bb];
    let s = Site { path: copy_bytes(path), site: site(m, blk.terminator.span) };
    let ghost t2 = *tmp;
    let ghost st0 = stmts@;
    match lower_term(m, pol, order, keys, b, tmp, &s, &blk.terminator) {
        Ok((ct, declass)) => {
            let ghost pre = tmp.pre@;
            let n0 = tmp.pre.len();
            stmts.append(&mut tmp.pre);
            sites_n(&mut sites, &s.site, n0);
            if bad { return None; }
            let cb = c::Block { stmts, term: ct };
            proof { lemma_block_close(*m, *pol, order@, *b, nloc, tbase(t2), tbase(*tmp), *blk, st0, pre, ct, cb); }
            Some((cb, sites, if declass { Some(copy_bytes(&s.site)) } else { None }))
        },
        Err(e) => {
            errs.push(e);
            tmp.pre.clear();
            tmp.nloc = b.locals.len();
            None
        },
    }
}

/// The first `n` blocks of a body, related.
#[verifier::opaque]
pub open spec fn blocks_rel(m: MirCrate, pol: Policy, ord: Seq<usize>, b: Body, nloc: nat, ncore: nat, r: Seq<bool>, cbs: Seq<c::Block>, n: nat) -> bool {
    cbs.len() == n && forall|k: int| 0 <= k < n ==> #[trigger] block_rel(m, pol, ord, b, nloc, ncore, r, b.blocks@[k], cbs[k], r[k])
}

proof fn lemma_blocks_init(m: MirCrate, pol: Policy, ord: Seq<usize>, b: Body, nloc: nat, ncore: nat, r: Seq<bool>)
    ensures blocks_rel(m, pol, ord, b, nloc, ncore, r, Seq::<c::Block>::empty(), 0),
{
    reveal(blocks_rel);
}

proof fn lemma_blocks_step(m: MirCrate, pol: Policy, ord: Seq<usize>, b: Body, nloc: nat, n1: nat, n2: nat, r: Seq<bool>,
    cbs: Seq<c::Block>, n: nat, cb: c::Block)
    requires n1 <= n2, n < b.blocks@.len(), blocks_rel(m, pol, ord, b, nloc, n1, r, cbs, n),
        block_rel(m, pol, ord, b, nloc, n2, r, b.blocks@[n as int], cb, r[n as int]),
    ensures blocks_rel(m, pol, ord, b, nloc, n2, r, cbs.push(cb), n + 1),
{
    reveal(blocks_rel);
    assert forall|k: int| 0 <= k < n + 1 implies #[trigger] block_rel(m, pol, ord, b, nloc, n2, r, b.blocks@[k], cbs.push(cb)[k], r[k]) by {
        if k < n {
            assert(cbs.push(cb)[k] == cbs[k]);
            lemma_block_rel_mono(m, pol, ord, b, nloc, n1, n2, r, b.blocks@[k], cbs[k], r[k]);
        }
    };
}

proof fn lemma_body_close(m: MirCrate, pol: Policy, ord: Seq<usize>, j: nat, b: Body, cb: c::Body, r: Seq<bool>, locals: Seq<c::Ty>)
    requires
        inst_body(m, j) == Some(b), b.spread_arg is None, sig_ok(m, b), locals_ok(m, b),
        cb.nargs == b.arg_count, locals.len() == b.locals@.len(), cb.locals@.len() >= b.locals@.len(),
        cb.locals@.subrange(0, locals.len() as int) == locals,
        forall|i: int| 0 <= i < b.locals@.len() ==> lowers_ty(m, #[trigger] b.locals@[i].ty, locals[i], tyf()),
        r.len() == b.blocks@.len(), r.len() > 0, r[0], cb.blocks@.len() == b.blocks@.len(),
        blocks_rel(m, pol, ord, b, b.locals@.len(), cb.locals@.len(), r, cb.blocks@, b.blocks@.len()),
    ensures lowers_body(m, pol, ord, j, cb, r),
{
    reveal(blocks_rel);
    assert forall|k: int| 0 <= k < b.locals@.len() implies lowers_ty(m, #[trigger] b.locals@[k].ty, cb.locals@[k], tyf()) by {
        assert(cb.locals@[k] == cb.locals@.subrange(0, locals.len() as int)[k]);
    };
}

fn is_ws(c: u8) -> (r: bool)
    ensures r == ws(c),
{
    c == b' ' || c == b'\n' || c == b'\t' || c == b'\r'
}

proof fn lemma_trim_lo(s: Seq<u8>, i: nat)
    requires i <= s.len(), forall|k: int| 0 <= k < i ==> ws(#[trigger] s[k]),
    ensures trim_lo(s, 0) == trim_lo(s, i),
    decreases i,
{
    if i > 0 {
        lemma_trim_lo_step(s, 0, i);
    }
}

proof fn lemma_trim_lo_step(s: Seq<u8>, k: nat, i: nat)
    requires k <= i <= s.len(), forall|q: int| k <= q < i ==> ws(#[trigger] s[q]),
    ensures trim_lo(s, k) == trim_lo(s, i),
    decreases i - k,
{
    if k < i { lemma_trim_lo_step(s, k + 1, i); }
}

proof fn lemma_trim_hi(s: Seq<u8>, lo: nat, j: nat, n: nat)
    requires lo <= j <= n, forall|q: int| j <= q < n ==> ws(#[trigger] s[q]),
    ensures trim_hi(s, lo, n) == trim_hi(s, lo, j),
    decreases n - j,
{
    if j < n { lemma_trim_hi(s, lo, (j + 1) as nat, n); }
}

fn trim(s: &Vec<u8>) -> (r: Vec<u8>)
    ensures r@ == trim_spec(s@),
{
    let mut lo: usize = 0;
    while lo < s.len() && is_ws(s[lo])
        invariant lo <= s@.len(), forall|k: int| 0 <= k < lo ==> ws(#[trigger] s@[k]),
        decreases s.len() - lo,
    { lo += 1; }
    proof { lemma_trim_lo(s@, lo as nat); }
    let mut hi: usize = s.len();
    while hi > lo && is_ws(s[hi - 1])
        invariant lo <= hi <= s@.len(), forall|k: int| hi <= k < s@.len() ==> ws(#[trigger] s@[k]),
        decreases hi - lo,
    { hi -= 1; }
    proof { lemma_trim_hi(s@, lo as nat, hi as nat, s@.len()); }
    let mut v = Vec::new();
    let mut i = lo;
    while i < hi
        invariant lo <= i <= hi <= s@.len(), v@ == s@.subrange(lo as int, i as int),
        decreases hi - i,
    {
        v.push(s[i]);
        proof { assert(v@ =~= s@.subrange(lo as int, i + 1)); }
        i += 1;
    }
    v
}

fn is_ct_attr(t: &Vec<u8>) -> (r: bool)
    ensures r == ct_attr(t@),
{
    t.len() >= 6 && t[0] == b'#' && t[1] == b'[' && t[2] == b'c' && t[3] == b't' && t[4] == b':' && t[5] == b':'
}

/// The `#[ct::..]` attributes of the item of `def`, trimmed.
fn attrs_of(m: &MirCrate, def: DefId) -> (r: Vec<Vec<u8>>)
    ensures views(r@) == item_attrs(*m, def),
{
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut k: usize = 0;
    while k < m.items.len()
        invariant k <= m.items@.len(), out@.len() == 0, forall|i: int| 0 <= i < k ==> (#[trigger] m.items@[i]).def != def,
        decreases m.items.len() - k,
    {
        if m.items[k].def == def {
            let a = &m.items[k].attrs;
            let mut i: usize = 0;
            while i < a.len()
                invariant i <= a@.len(), *a == m.items@[k as int].attrs, views(out@) == attrs_from(a@, i as nat),
                decreases a.len() - i,
            {
                let t = trim(&a[i]);
                let ghost o0 = out@;
                if is_ct_attr(&t) { out.push(t); }
                proof { assert(views(out@) =~= attrs_from(a@, (i + 1) as nat)) by { assert(views(o0) == attrs_from(a@, i as nat)); }; }
                i += 1;
            }
            proof { crate::look::lemma_find(m.items@, |it: Item| it.def == def, k as nat); }
            return out;
        }
        k += 1;
    }
    proof {
        crate::look::lemma_find(m.items@, |it: Item| it.def == def, k as nat);
        assert(views(out@) =~= Seq::<Seq<u8>>::empty());
    }
    out
}

/// Parameter `j`'s name from the argument locals' debug info (`argument_index` is 1-based).
fn param_name(b: &Body, j: usize) -> (r: Vec<u8>)
    ensures r@ == pname(*b, j as nat),
{
    let mut k: usize = 0;
    while k < b.var_debug_info.len()
        invariant k <= b.var_debug_info@.len(), forall|i: int| 0 <= i < k ==> !vdi_is(#[trigger] b.var_debug_info@[i], j as nat),
        decreases b.var_debug_info.len() - k,
    {
        let v = &b.var_debug_info[k];
        let here = match &v.value {
            VarDebugInfoContents::Place(p) => p.local == j && p.projection.len() == 0,
            _ => false,
        };
        let idx = match v.argument_index { Some(x) => x as usize == j, None => false };
        if idx && here {
            proof { crate::look::lemma_find_spec(b.var_debug_info@, |v: VarDebugInfo| vdi_is(v, j as nat)); }
            return copy_bytes(&v.name);
        }
        k += 1;
    }
    proof { crate::look::lemma_find_spec(b.var_debug_info@, |v: VarDebugInfo| vdi_is(v, j as nat)); }
    Vec::new()
}

fn param_names(b: &Body) -> (r: Vec<Vec<u8>>)
    ensures views(r@) == pnames(*b),
{
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut j: usize = 0;
    while j < b.arg_count
        invariant j <= b.arg_count, views(out@) == Seq::new(j as nat, |k: int| pname(*b, (k + 1) as nat)),
        decreases b.arg_count - j,
    {
        let nm = param_name(b, j + 1);
        let ghost o0 = out@;
        let ghost nmv = nm;
        out.push(nm);
        proof {
            let want = Seq::new((j + 1) as nat, |k: int| pname(*b, (k + 1) as nat));
            assert(views(o0).len() == o0.len());
            assert(out@ == o0.push(nmv));
            assert(views(out@)[j as int] == nmv@);
            assert forall|k: int| 0 <= k < j + 1 implies views(out@)[k] == want[k] by {
                if k < j { assert(out@[k] == o0[k]); assert(views(o0)[k] == pname(*b, (k + 1) as nat)); }
            };
            assert(views(out@) =~= want);
        }
        j += 1;
    }
    out
}

fn err_at(path: &Vec<u8>, what: &[u8], site: Vec<u8>) -> Reject {
    Reject::Unsupported { path: copy_bytes(path), what: msg(what), site }
}

/// One fn of the closure: `insts[j]`'s body, with its reachable-block marks.
pub fn lower_body(m: &MirCrate, pol: &Policy, order: &Vec<usize>, keys: &mut Keys, j: usize, is_root: bool, errs: &mut Vec<Reject>)
    -> (r: Option<(c::Body, FnInfo, Ghost<Seq<bool>>)>)
    requires j < m.insts@.len(),
    ensures r matches Some((cb, info, rr)) ==> lowers_body(*m, *pol, order@, j as nat, cb, rr@) && info.inst == j && info.is_root == is_root
        && info.path@ == fn_path(*m, j as nat) && views(info.attrs@) == item_attrs(*m, m.insts@[j as int].def)
        && inst_body(*m, j as nat) is Some && views(info.param_names@) == pnames(inst_body(*m, j as nat)->Some_0),
{
    let x = &m.insts[j];
    let is_shim = matches!(x.kind, InstanceKind::Shim);
    let path = if is_shim { copy_bytes(&x.name) } else { copy_bytes(&x.key) };
    proof { assert(path@ == fn_path(*m, j as nat)); }
    let b = match x_inst_body(m, j) {
        Some(b) => b,
        None => { errs.push(err_at(&path, b"no MIR body", msg(b"?"))); return None; },
    };
    let ghost nloc = b.locals@.len();
    let bsite = site(m, b.span);
    let mut bad = false;
    if b.spread_arg.is_some() { errs.push(err_at(&path, b"a rust-call (closure) body", copy_bytes(&bsite))); bad = true; }
    if !x_sig_ok(m, b) || !x_locals_ok(m, b) { errs.push(err_at(&path, b"a local type outside the subset", copy_bytes(&bsite))); bad = true; }
    let mut locals: Vec<c::Ty> = Vec::new();
    let mut k: usize = 0;
    while k < b.locals.len()
        invariant k <= b.locals@.len(), !bad ==> locals@.len() == k && forall|i: int| 0 <= i < k ==> lowers_ty(*m, #[trigger] b.locals@[i].ty, locals@[i], tyf()),
            !bad ==> b.spread_arg is None && sig_ok(*m, *b) && locals_ok(*m, *b),
        decreases b.locals.len() - k,
    {
        match lower_ty(m, b.locals[k].ty, TYF) {
            Ok(t) => locals.push(t),
            Err(e) => { errs.push(Reject::Unsupported { path: copy_bytes(&path), what: e, site: site(m, b.locals[k].span) }); bad = true; },
        }
        k += 1;
    }
    let seen = match reach(b) {
        Some(s) => s,
        None => { errs.push(err_at(&path, b"a block target out of range", copy_bytes(&bsite))); return None; },
    };
    let mut tmp = Tmp { nloc: b.locals.len(), tys: Vec::new(), pre: Vec::new() };
    let mut blocks: Vec<c::Block> = Vec::new();
    let mut block_sites: Vec<Vec<u8>> = Vec::new();
    let mut stmt_sites: Vec<Vec<Vec<u8>>> = Vec::new();
    let mut declassify_sites: Vec<Vec<u8>> = Vec::new();
    let mut bb: usize = 0;
    proof { lemma_blocks_init(*m, *pol, order@, *b, nloc, tbase(tmp), seen@); }
    while bb < b.blocks.len()
        invariant
            bb <= b.blocks@.len(), seen@.len() == b.blocks@.len(), tmp.nloc == nloc, tmp.pre@.len() == 0, nloc == b.locals@.len(),
            seen@.len() > 0, seen@[0], forall|k: int| 0 <= k < seen@.len() && #[trigger] seen@[k] ==> succs_in(b.blocks@[k].terminator.kind, marks(seen@)),
            !bad ==> blocks_rel(*m, *pol, order@, *b, nloc, tbase(tmp), seen@, blocks@, bb as nat) && blocks@.len() == bb,
            !bad ==> locals@.len() == nloc && forall|i: int| 0 <= i < nloc ==> lowers_ty(*m, #[trigger] b.locals@[i].ty, locals@[i], tyf()),
            !bad ==> b.spread_arg is None && sig_ok(*m, *b) && locals_ok(*m, *b),
        decreases b.blocks.len() - bb,
    {
        block_sites.push(site(m, b.blocks[bb].terminator.span));
        let ghost t1 = tmp;
        let ghost bs0 = blocks@;
        if !seen[bb] {
            let cb = c::Block { stmts: Vec::new(), term: c::Term::Abort };
            proof { if !bad { lemma_blocks_step(*m, *pol, order@, *b, nloc, tbase(t1), tbase(tmp), seen@, bs0, bb as nat, cb); } }
            blocks.push(cb);
            stmt_sites.push(Vec::new());
        } else {
            match lower_block(m, pol, order, keys, b, &mut tmp, &path, bb, errs) {
                Some((cb, sites, ds)) => {
                    proof { if !bad { lemma_blocks_step(*m, *pol, order@, *b, nloc, tbase(t1), tbase(tmp), seen@, bs0, bb as nat, cb); } }
                    blocks.push(cb);
                    stmt_sites.push(sites);
                    if let Some(d) = ds { declassify_sites.push(d); }
                },
                None => { bad = true; },
            }
        }
        bb += 1;
    }
    if bad { return None; }
    let ghost ncore = tbase(tmp);
    let ghost locals0 = locals@;
    locals.append(&mut tmp.tys);
    let info = FnInfo {
        path, is_root, attrs: attrs_of(m, x.def), param_names: param_names(b), block_sites, declassify_sites, stmt_sites, inst: j,
    };
    let cb = c::Body { nargs: b.arg_count, locals, blocks };
    proof {
        assert(cb.locals@.len() == ncore);
        assert(cb.locals@.subrange(0, locals0.len() as int) =~= locals0);
        lemma_body_close(*m, *pol, order@, j as nat, *b, cb, seen@, locals0);
    }
    Some((cb, info, Ghost(seen@)))
}

// ------------------------------------------------------------------ the closure

#[verifier::loop_isolation(false)]
fn add(order: &mut Vec<usize>, j: usize)
    requires forall|k1: int, k2: int| 0 <= k1 < k2 < old(order)@.len() ==> old(order)@[k1] != old(order)@[k2],
    ensures forall|k1: int, k2: int| 0 <= k1 < k2 < final(order)@.len() ==> final(order)@[k1] != final(order)@[k2],
        final(order)@.len() >= old(order)@.len(), final(order)@.subrange(0, old(order)@.len() as int) == old(order)@,
        forall|k: int| 0 <= k < final(order)@.len() ==> final(order)@[k] == j || (k < old(order)@.len()),
{
    let mut g: usize = 0;
    while g < order.len()
        invariant g <= order@.len(), order@ == old(order)@, forall|k: int| 0 <= k < g ==> order@[k] != j,
        decreases order.len() - g,
    {
        if order[g] == j {
            proof { assert(order@.subrange(0, order@.len() as int) =~= order@); }
            return;
        }
        g += 1;
    }
    order.push(j);
    proof { assert(order@.subrange(0, old(order)@.len() as int) =~= old(order)@); }
}

/// The fns of the root's closure in discovery order (bodies in order, reachable blocks in order):
/// internal callees and non-trivial drop glue. `lower_body` checks every callee it meets is here.
pub fn closure_order(m: &MirCrate, pol: &Policy, j0: usize) -> (r: Vec<usize>)
    requires j0 < m.insts@.len(),
    ensures r@.len() >= 1, r@[0] == j0, forall|g: int| 0 <= g < r@.len() ==> (#[trigger] r@[g]) < m.insts@.len(),
        forall|k1: int, k2: int| 0 <= k1 < k2 < r@.len() ==> r@[k1] != r@[k2],
{
    let mut order: Vec<usize> = Vec::new();
    order.push(j0);
    let mut i: usize = 0;
    while i < order.len() && i <= m.insts.len()
        invariant
            order@.len() >= 1, order@[0] == j0, forall|g: int| 0 <= g < order@.len() ==> (#[trigger] order@[g]) < m.insts@.len(),
            forall|k1: int, k2: int| 0 <= k1 < k2 < order@.len() ==> order@[k1] != order@[k2],
        decreases m.insts@.len() + 1 - i,
    {
        let j = order[i];
        if let Some(b) = x_inst_body(m, j) {
            if let Some(seen) = reach(b) {
                let mut bb: usize = 0;
                while bb < b.blocks.len()
                    invariant
                        bb <= b.blocks@.len(), seen@.len() == b.blocks@.len(),
                        order@.len() >= 1, order@[0] == j0, forall|g: int| 0 <= g < order@.len() ==> (#[trigger] order@[g]) < m.insts@.len(),
                        forall|k1: int, k2: int| 0 <= k1 < k2 < order@.len() ==> order@[k1] != order@[k2],
                    decreases b.blocks.len() - bb,
                {
                    if seen[bb] {
                        match &b.blocks[bb].terminator.kind {
                            TerminatorKind::Call { func, args, target: Some(_), .. } => {
                                if let Some((jj, k)) = x_callee_of(m, func) {
                                    if jj < m.insts.len() && !x_is_leaf(m, pol, m.insts[jj].key.as_slice(), &m.calls[k].args) && is_internal(m, pol, jj)
                                        && callee_ok(m, b, args, jj) == 0 {
                                        add(&mut order, jj);
                                        proof { assert(order@[0] == j0); }
                                    }
                                }
                            },
                            TerminatorKind::Drop { place, .. } => {
                                if let Some(t) = x_place_ty(m, b, place) {
                                    if let Some(d) = x_drop_row(m, t) {
                                        if !(d.empty || x_vec_int(m, t)) {
                                            if let Some(jj) = x_inst_idx(m, d.glue) {
                                                if let Some(gb) = x_inst_body(m, jj) {
                                                    if glue_ok(m, gb, t) {
                                                        add(&mut order, jj);
                                                        proof { assert(order@[0] == j0); }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            },
                            _ => {},
                        }
                    }
                    bb += 1;
                }
            }
        }
        i += 1;
    }
    order
}

fn x_has_lt(s: &Vec<u8>) -> (r: bool)
    ensures r == has_lt(s@),
{
    if s.len() < 3 { return false; }
    let mut i: usize = 0;
    while i + 2 < s.len()
        invariant i + 2 <= s@.len(), forall|k: int| 0 <= k < i ==> !(#[trigger] s@[k] == 58u8 && s@[k + 1] == 58u8 && s@[k + 2] == 60u8),
        decreases s.len() - i,
    {
        if s[i] == b':' && s[i + 1] == b':' && s[i + 2] == b'<' { return true; }
        i += 1;
    }
    false
}

/// Item `k` may be `root`, and its instance's index.
fn may_be(m: &MirCrate, k: usize, root: &[u8]) -> (r: (bool, Option<usize>))
    requires k < m.items@.len(),
    ensures r.0 == item_may_be(*m, k as int, root@), r.1 matches Some(j) ==> item_inst(*m, k as int) == Some(j as nat) && j < m.insts@.len(),
{
    let it = &m.items[k];
    match it.inst {
        Some(id) => match x_inst_idx(m, id) {
            Some(j) => {
                proof { crate::look::lemma_find_spec(m.insts@, |x: Inst| x.id == id); }
                (bytes_eq(m.insts[j].key.as_slice(), root), Some(j))
            },
            None => (false, None),
        },
        None => (bytes_eq(it.name.as_slice(), root) || x_has_lt(&it.name), None),
    }
}

/// The root: exactly one local fn item that may be `root`, and it is monomorphic.
pub fn root_inst(m: &MirCrate, root: &[u8]) -> (r: Result<usize, Vec<u8>>)
    ensures r matches Ok(j) ==> root_of(*m, root@, j as nat) && j < m.insts@.len(),
{
    let mut hit: Option<(usize, Option<usize>)> = None;
    let mut n: usize = 0;
    let mut k: usize = 0;
    while k < m.items.len()
        invariant
            k <= m.items@.len(), n <= k,
            n == 0 ==> hit is None && forall|i: int| 0 <= i < k ==> !#[trigger] item_may_be(*m, i, root@),
            n == 1 ==> (hit matches Some((h, o)) && h < k && item_may_be(*m, h as int, root@)
                && (o is Some ==> item_inst(*m, h as int) == Some(o->Some_0 as nat) && o->Some_0 < m.insts@.len())
                && forall|i: int| 0 <= i < k && i != h ==> !#[trigger] item_may_be(*m, i, root@)),
        decreases m.items.len() - k,
    {
        let (here, o) = may_be(m, k, root);
        if here {
            hit = Some((k, o));
            n += 1;
        }
        k += 1;
    }
    if n > 1 { return Err(msg(b"root is ambiguous: several fns of the crate share its key")); }
    match hit {
        Some((_h, Some(j))) => {
            proof { assert(item_may_be(*m, _h as int, root@) && item_inst(*m, _h as int) == Some(j as nat)); }
            Ok(j)
        },
        _ => Err(msg(b"root matches no monomorphic fn of the crate")),
    }
}

/// Lowers the closure of manifest root `root` (a `ct_key`) to a core program, fn 0 the root.
/// `keys` is the crate's key map across its roots, in manifest order (as the old `by_key`): the
/// root and each callee bind their key in it, and a key that names something else is a reject.
pub fn lower(m: &MirCrate, pol: &Policy, root: &[u8], keys: &mut Keys) -> (r: Result<(c::Program, Vec<FnInfo>), Vec<Reject>>)
    ensures r matches Ok((p, infos)) ==> lowers(*m, *pol, root@, p, infos@) && ctcore::ct::wf(p),
{
    let j0 = match root_inst(m, root) {
        Ok(j) => j,
        Err(e) => { let mut es = Vec::new(); es.push(Reject::Root { path: msg(root), msg: e }); return Err(es); },
    };
    if !bind(keys, root, m.insts[j0].def, Some(j0)) {
        let mut es = Vec::new();
        es.push(Reject::Root { path: msg(root), msg: msg(b"ambiguous key: another root's closure reached a different fn under it") });
        return Err(es);
    }
    let order = closure_order(m, pol, j0);
    let mut errs: Vec<Reject> = Vec::new();
    let mut fns: Vec<c::Body> = Vec::new();
    let mut infos: Vec<FnInfo> = Vec::new();
    let ghost mut rs: Seq<Seq<bool>> = Seq::empty();
    let mut bad = false;
    let mut g: usize = 0;
    while g < order.len()
        invariant
            g <= order@.len(), forall|h: int| 0 <= h < order@.len() ==> (#[trigger] order@[h]) < m.insts@.len(),
            !bad ==> fns@.len() == g && infos@.len() == g && rs.len() == g
                && forall|h: int| 0 <= h < g ==> (#[trigger] infos@[h]).inst == order@[h] && info_ok(*m, infos@[h], h)
                    && lowers_body(*m, *pol, order@, order@[h] as nat, fns@[h], rs[h]),
        decreases order.len() - g,
    {
        match lower_body(m, pol, &order, keys, order[g], g == 0, &mut errs) {
            Some((cb, info, _r)) => {
                fns.push(cb);
                infos.push(info);
                proof { rs = rs.push(_r@); }
            },
            None => { bad = true; },
        }
        g += 1;
    }
    if bad || errs.len() > 0 { return Err(errs); }
    let p = c::Program { fns };
    if !ctcore::check::check_wf(&p) {
        let mut es = Vec::new();
        es.push(Reject::Unsupported { path: msg(root), what: msg(b"the core program is not well-formed (a &mut inside a type, ..)"), site: msg(b"?") });
        return Err(es);
    }
    proof {
        assert(ords(infos@) =~= order@);
        assert(lowers_rs(*m, *pol, root@, p, infos@, rs));
    }
    Ok((p, infos))
}

// ------------------------------------------------------------------ what `lowers` gives the semantics

/// Some fn of the program is the image of `insts[j]`.
pub open spec fn idx_of(infos: Seq<FnInfo>, j: nat) -> int { choose|h: int| 0 <= h < infos.len() && infos[h].inst as nat == j }

proof fn lemma_body_in(m: MirCrate, pol: Policy, ord: Seq<usize>, j: nat, cb: c::Body, r: Seq<bool>, rf: spec_fn(nat) -> Set<nat>)
    requires lowers_body(m, pol, ord, j, cb, r), rf(j) == marks(r),
    ensures body_in(m, cpol(pol), ord_set(ord), rf, j),
{
    let b = inst_body(m, j)->Some_0;
    lemma_marks(r, 0);
    assert forall|bb: nat| #[trigger] rf(j).contains(bb) implies bb < b.blocks@.len() && block_ok(m, cpol(pol), b, b.blocks@[bb as int])
        && succs_in(b.blocks@[bb as int].terminator.kind, rf(j)) && callees_in(m, cpol(pol), b, b.blocks@[bb as int].terminator.kind, ord_set(ord)) by {
        lemma_marks(r, bb);
        assert(block_rel(m, pol, ord, b, b.locals@.len(), cb.locals@.len(), r, b.blocks@[bb as int], cb.blocks@[bb as int], r[bb as int]));
    };
}

/// **`lowers` puts every translated fn in the subset**: the fns' instances and their reachable
/// blocks are a closed set (`sem::closed`), so `theorem_in_subset_no_unsup` applies to each, and a
/// `None` from `mir_run_fn` there is a panic or fuel.
pub proof fn theorem_lowers_in_subset(m: MirCrate, pol: Policy, root: Seq<u8>, p: c::Program, infos: Seq<FnInfo>, g: int)
    requires lowers(m, pol, root, p, infos), 0 <= g < infos.len(),
    ensures in_subset(m, cpol(pol), infos[g].inst as nat),
{
    let rs = choose|rs: Seq<Seq<bool>>| lowers_rs(m, pol, root, p, infos, rs);
    let ord = ords(infos);
    let s = ord_set(ord);
    let rf = |j: nat| marks(rs[idx_of(infos, j)]);
    let w = ord.map_values(|x: usize| x as nat);
    w.to_set_ensures();
    assert forall|j: nat| #[trigger] s.contains(j) implies body_in(m, cpol(pol), s, rf, j) by {
        let k = choose|k: int| 0 <= k < w.len() && w[k] == j;
        assert(infos[k].inst as nat == j);
        let h = idx_of(infos, j);
        assert(lowers_body(m, pol, ord, infos[h].inst as nat, p.fns@[h], rs[h]));
        lemma_body_in(m, pol, ord, j, p.fns@[h], rs[h], rf);
    };
    assert(closed(m, cpol(pol), s, rf));
    assert(w[g] == infos[g].inst as nat);
    assert(s.contains(infos[g].inst as nat));
}

} // verus!
