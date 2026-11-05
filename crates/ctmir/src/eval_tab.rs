//! Id-index tables for the MIR evaluator (`eval`): for each dump table, the index of the first row
//! of each key, proved equal to `sem`'s first-match `find` (`tabs_ok`). Built once per dump, they
//! make the evaluator's lookups constant-time. An id at or past `ID_CAP` makes `tabs` give `None`
//! rather than allocate.
use crate::look::*;
use crate::mir::*;
#[cfg(verus_keep_ghost)]
use crate::sem::*;
use vstd::prelude::*;

verus! {

pub struct Tabs {
    pub tys: Vec<Option<usize>>,
    pub adts: Vec<Option<usize>>,
    pub layouts: Vec<Option<usize>>,
    pub consts: Vec<Option<usize>>,
    pub allocs: Vec<Option<usize>>,
    pub insts: Vec<Option<usize>>,
    pub drops: Vec<Option<usize>>,
    pub calls: Vec<Option<usize>>,
}

pub const ID_CAP: usize = 1 << 24;

pub open spec fn onat(o: Option<usize>) -> Option<nat> { match o { Some(i) => Some(i as nat), None => None } }

// ------------------------------------------------------------------ the tables' contract

#[verifier::opaque]
pub open spec fn tab_tys(m: MirCrate, t: Seq<Option<usize>>) -> bool {
    &&& forall|k: usize| (k as int) < t.len() ==> onat(#[trigger] t[k as int]) == find(m.tys@, |r: TyRow| r.id == k)
    &&& forall|i: int| 0 <= i < m.tys@.len() ==> (#[trigger] m.tys@[i]).id < t.len()
}

#[verifier::opaque]
pub open spec fn tab_adts(m: MirCrate, t: Seq<Option<usize>>) -> bool {
    &&& forall|k: usize| (k as int) < t.len() ==> onat(#[trigger] t[k as int]) == find(m.adts@, |r: Adt| r.ty == k)
    &&& forall|i: int| 0 <= i < m.adts@.len() ==> (#[trigger] m.adts@[i]).ty < t.len()
}

#[verifier::opaque]
pub open spec fn tab_layouts(m: MirCrate, t: Seq<Option<usize>>) -> bool {
    &&& forall|k: usize| (k as int) < t.len() ==> onat(#[trigger] t[k as int]) == find(m.layouts@, |r: LayoutRow| r.ty == k)
    &&& forall|i: int| 0 <= i < m.layouts@.len() ==> (#[trigger] m.layouts@[i]).ty < t.len()
}

#[verifier::opaque]
pub open spec fn tab_consts(m: MirCrate, t: Seq<Option<usize>>) -> bool {
    &&& forall|k: usize| (k as int) < t.len() ==> onat(#[trigger] t[k as int]) == find(m.consts@, |r: ConstRow| r.id == k)
    &&& forall|i: int| 0 <= i < m.consts@.len() ==> (#[trigger] m.consts@[i]).id < t.len()
}

#[verifier::opaque]
pub open spec fn tab_allocs(m: MirCrate, t: Seq<Option<usize>>) -> bool {
    &&& forall|k: usize| (k as int) < t.len() ==> onat(#[trigger] t[k as int]) == find(m.allocs@, |r: AllocRow| r.id == k)
    &&& forall|i: int| 0 <= i < m.allocs@.len() ==> (#[trigger] m.allocs@[i]).id < t.len()
}

#[verifier::opaque]
pub open spec fn tab_insts(m: MirCrate, t: Seq<Option<usize>>) -> bool {
    &&& forall|k: usize| (k as int) < t.len() ==> onat(#[trigger] t[k as int]) == find(m.insts@, |x: Inst| x.id == k)
    &&& forall|i: int| 0 <= i < m.insts@.len() ==> (#[trigger] m.insts@[i]).id < t.len()
}

#[verifier::opaque]
pub open spec fn tab_drops(m: MirCrate, t: Seq<Option<usize>>) -> bool {
    &&& forall|k: usize| (k as int) < t.len() ==> onat(#[trigger] t[k as int]) == find(m.drops@, |d: DropRow| d.ty == k)
    &&& forall|i: int| 0 <= i < m.drops@.len() ==> (#[trigger] m.drops@[i]).ty < t.len()
}

#[verifier::opaque]
pub open spec fn tab_calls(m: MirCrate, t: Seq<Option<usize>>) -> bool {
    &&& forall|k: usize| (k as int) < t.len() ==> onat(#[trigger] t[k as int]) == find(m.calls@, |r: Call| r.fn_ty == k)
    &&& forall|i: int| 0 <= i < m.calls@.len() ==> (#[trigger] m.calls@[i]).fn_ty < t.len()
}

/// Each table maps a key `k` below its length to the first row with that key (`find`), and no
/// row's key is past its length.
pub open spec fn tabs_ok(m: MirCrate, t: Tabs) -> bool {
    &&& tab_tys(m, t.tys@) && tab_adts(m, t.adts@) && tab_layouts(m, t.layouts@) && tab_consts(m, t.consts@)
    &&& tab_allocs(m, t.allocs@) && tab_insts(m, t.insts@) && tab_drops(m, t.drops@) && tab_calls(m, t.calls@)
}

// ------------------------------------------------------------------ building

/// `t` indexes `ks` by first match.
pub open spec fn first(ks: Seq<usize>, t: Seq<Option<usize>>) -> bool {
    &&& forall|i: int| 0 <= i < ks.len() ==> (#[trigger] ks[i]) < t.len()
    &&& forall|k: int| 0 <= k < t.len() ==> match #[trigger] t[k] {
            Some(j) => j < ks.len() && ks[j as int] == k && forall|l: int| 0 <= l < j ==> ks[l] != k,
            None => forall|l: int| 0 <= l < ks.len() ==> ks[l] != k,
        }
}

/// The first-match index of `ks`; `None` when a key is at or past `ID_CAP`.
fn index(ks: &Vec<usize>) -> (r: Option<Vec<Option<usize>>>)
    ensures r matches Some(t) ==> first(ks@, t@),
{
    let mut n: usize = 0;
    let mut i: usize = 0;
    while i < ks.len()
        invariant i <= ks@.len(), n <= ID_CAP, forall|l: int| 0 <= l < i ==> (#[trigger] ks@[l]) < n,
        decreases ks.len() - i,
    {
        if ks[i] >= ID_CAP { return None; }
        if ks[i] >= n { n = ks[i] + 1; }
        i += 1;
    }
    let mut t: Vec<Option<usize>> = Vec::new();
    while t.len() < n
        invariant t@.len() <= n, forall|k: int| 0 <= k < t@.len() ==> (#[trigger] t@[k]) is None,
        decreases n - t@.len(),
    {
        t.push(None);
    }
    let mut i: usize = 0;
    while i < ks.len()
        invariant
            i <= ks@.len(), t@.len() == n, forall|l: int| 0 <= l < ks@.len() ==> (#[trigger] ks@[l]) < n,
            forall|k: int| 0 <= k < n ==> match #[trigger] t@[k] {
                Some(j) => j < i && ks@[j as int] == k && forall|l: int| 0 <= l < j ==> ks@[l] != k,
                None => forall|l: int| 0 <= l < i ==> ks@[l] != k,
            },
        decreases ks.len() - i,
    {
        let k = ks[i];
        if t[k].is_none() {
            t.set(k, Some(i));
        }
        i += 1;
    }
    Some(t)
}

/// `first` over the keys of `s` under `p` is `find`.
proof fn lemma_first_find<T>(s: Seq<T>, p: spec_fn(T) -> bool, ks: Seq<usize>, t: Seq<Option<usize>>, k: usize)
    requires first(ks, t), (k as int) < t.len(), ks.len() == s.len(), forall|i: int| #![trigger s[i]] #![trigger ks[i]] 0 <= i < s.len() ==> p(s[i]) == (ks[i] == k),
    ensures onat(t[k as int]) == find(s, p),
{
    match t[k as int] {
        Some(j) => lemma_find(s, p, j as nat),
        None => lemma_find(s, p, s.len()),
    }
}

proof fn lemma_tab_tys(m: MirCrate, ks: Seq<usize>, t: Seq<Option<usize>>)
    requires first(ks, t), ks.len() == m.tys@.len(), forall|i: int| 0 <= i < ks.len() ==> ks[i] == (#[trigger] m.tys@[i]).id,
    ensures tab_tys(m, t),
{
    reveal(tab_tys);
    assert forall|k: usize| (k as int) < t.len() implies onat(#[trigger] t[k as int]) == find(m.tys@, |r: TyRow| r.id == k) by {
        lemma_first_find(m.tys@, |r: TyRow| r.id == k, ks, t, k);
    };
    assert forall|i: int| 0 <= i < m.tys@.len() implies (#[trigger] m.tys@[i]).id < t.len() by { assert(ks[i] < t.len()); };
}

proof fn lemma_tab_adts(m: MirCrate, ks: Seq<usize>, t: Seq<Option<usize>>)
    requires first(ks, t), ks.len() == m.adts@.len(), forall|i: int| 0 <= i < ks.len() ==> ks[i] == (#[trigger] m.adts@[i]).ty,
    ensures tab_adts(m, t),
{
    reveal(tab_adts);
    assert forall|k: usize| (k as int) < t.len() implies onat(#[trigger] t[k as int]) == find(m.adts@, |r: Adt| r.ty == k) by {
        lemma_first_find(m.adts@, |r: Adt| r.ty == k, ks, t, k);
    };
    assert forall|i: int| 0 <= i < m.adts@.len() implies (#[trigger] m.adts@[i]).ty < t.len() by { assert(ks[i] < t.len()); };
}

proof fn lemma_tab_layouts(m: MirCrate, ks: Seq<usize>, t: Seq<Option<usize>>)
    requires first(ks, t), ks.len() == m.layouts@.len(), forall|i: int| 0 <= i < ks.len() ==> ks[i] == (#[trigger] m.layouts@[i]).ty,
    ensures tab_layouts(m, t),
{
    reveal(tab_layouts);
    assert forall|k: usize| (k as int) < t.len() implies onat(#[trigger] t[k as int]) == find(m.layouts@, |r: LayoutRow| r.ty == k) by {
        lemma_first_find(m.layouts@, |r: LayoutRow| r.ty == k, ks, t, k);
    };
    assert forall|i: int| 0 <= i < m.layouts@.len() implies (#[trigger] m.layouts@[i]).ty < t.len() by { assert(ks[i] < t.len()); };
}

proof fn lemma_tab_consts(m: MirCrate, ks: Seq<usize>, t: Seq<Option<usize>>)
    requires first(ks, t), ks.len() == m.consts@.len(), forall|i: int| 0 <= i < ks.len() ==> ks[i] == (#[trigger] m.consts@[i]).id,
    ensures tab_consts(m, t),
{
    reveal(tab_consts);
    assert forall|k: usize| (k as int) < t.len() implies onat(#[trigger] t[k as int]) == find(m.consts@, |r: ConstRow| r.id == k) by {
        lemma_first_find(m.consts@, |r: ConstRow| r.id == k, ks, t, k);
    };
    assert forall|i: int| 0 <= i < m.consts@.len() implies (#[trigger] m.consts@[i]).id < t.len() by { assert(ks[i] < t.len()); };
}

proof fn lemma_tab_allocs(m: MirCrate, ks: Seq<usize>, t: Seq<Option<usize>>)
    requires first(ks, t), ks.len() == m.allocs@.len(), forall|i: int| 0 <= i < ks.len() ==> ks[i] == (#[trigger] m.allocs@[i]).id,
    ensures tab_allocs(m, t),
{
    reveal(tab_allocs);
    assert forall|k: usize| (k as int) < t.len() implies onat(#[trigger] t[k as int]) == find(m.allocs@, |r: AllocRow| r.id == k) by {
        lemma_first_find(m.allocs@, |r: AllocRow| r.id == k, ks, t, k);
    };
    assert forall|i: int| 0 <= i < m.allocs@.len() implies (#[trigger] m.allocs@[i]).id < t.len() by { assert(ks[i] < t.len()); };
}

proof fn lemma_tab_insts(m: MirCrate, ks: Seq<usize>, t: Seq<Option<usize>>)
    requires first(ks, t), ks.len() == m.insts@.len(), forall|i: int| 0 <= i < ks.len() ==> ks[i] == (#[trigger] m.insts@[i]).id,
    ensures tab_insts(m, t),
{
    reveal(tab_insts);
    assert forall|k: usize| (k as int) < t.len() implies onat(#[trigger] t[k as int]) == find(m.insts@, |x: Inst| x.id == k) by {
        lemma_first_find(m.insts@, |x: Inst| x.id == k, ks, t, k);
    };
    assert forall|i: int| 0 <= i < m.insts@.len() implies (#[trigger] m.insts@[i]).id < t.len() by { assert(ks[i] < t.len()); };
}

proof fn lemma_tab_drops(m: MirCrate, ks: Seq<usize>, t: Seq<Option<usize>>)
    requires first(ks, t), ks.len() == m.drops@.len(), forall|i: int| 0 <= i < ks.len() ==> ks[i] == (#[trigger] m.drops@[i]).ty,
    ensures tab_drops(m, t),
{
    reveal(tab_drops);
    assert forall|k: usize| (k as int) < t.len() implies onat(#[trigger] t[k as int]) == find(m.drops@, |d: DropRow| d.ty == k) by {
        lemma_first_find(m.drops@, |d: DropRow| d.ty == k, ks, t, k);
    };
    assert forall|i: int| 0 <= i < m.drops@.len() implies (#[trigger] m.drops@[i]).ty < t.len() by { assert(ks[i] < t.len()); };
}

proof fn lemma_tab_calls(m: MirCrate, ks: Seq<usize>, t: Seq<Option<usize>>)
    requires first(ks, t), ks.len() == m.calls@.len(), forall|i: int| 0 <= i < ks.len() ==> ks[i] == (#[trigger] m.calls@[i]).fn_ty,
    ensures tab_calls(m, t),
{
    reveal(tab_calls);
    assert forall|k: usize| (k as int) < t.len() implies onat(#[trigger] t[k as int]) == find(m.calls@, |r: Call| r.fn_ty == k) by {
        lemma_first_find(m.calls@, |r: Call| r.fn_ty == k, ks, t, k);
    };
    assert forall|i: int| 0 <= i < m.calls@.len() implies (#[trigger] m.calls@[i]).fn_ty < t.len() by { assert(ks[i] < t.len()); };
}

// the key columns (the dump's row types share no trait)

fn keys_tys(m: &MirCrate) -> (ks: Vec<usize>)
    ensures ks@.len() == m.tys@.len(), forall|i: int| 0 <= i < ks@.len() ==> ks@[i] == (#[trigger] m.tys@[i]).id,
{
    let mut ks = Vec::new();
    for i in 0..m.tys.len()
        invariant ks@.len() == i, forall|l: int| 0 <= l < i ==> ks@[l] == (#[trigger] m.tys@[l]).id,
    {
        ks.push(m.tys[i].id);
    }
    ks
}

fn keys_adts(m: &MirCrate) -> (ks: Vec<usize>)
    ensures ks@.len() == m.adts@.len(), forall|i: int| 0 <= i < ks@.len() ==> ks@[i] == (#[trigger] m.adts@[i]).ty,
{
    let mut ks = Vec::new();
    for i in 0..m.adts.len()
        invariant ks@.len() == i, forall|l: int| 0 <= l < i ==> ks@[l] == (#[trigger] m.adts@[l]).ty,
    {
        ks.push(m.adts[i].ty);
    }
    ks
}

fn keys_layouts(m: &MirCrate) -> (ks: Vec<usize>)
    ensures ks@.len() == m.layouts@.len(), forall|i: int| 0 <= i < ks@.len() ==> ks@[i] == (#[trigger] m.layouts@[i]).ty,
{
    let mut ks = Vec::new();
    for i in 0..m.layouts.len()
        invariant ks@.len() == i, forall|l: int| 0 <= l < i ==> ks@[l] == (#[trigger] m.layouts@[l]).ty,
    {
        ks.push(m.layouts[i].ty);
    }
    ks
}

fn keys_consts(m: &MirCrate) -> (ks: Vec<usize>)
    ensures ks@.len() == m.consts@.len(), forall|i: int| 0 <= i < ks@.len() ==> ks@[i] == (#[trigger] m.consts@[i]).id,
{
    let mut ks = Vec::new();
    for i in 0..m.consts.len()
        invariant ks@.len() == i, forall|l: int| 0 <= l < i ==> ks@[l] == (#[trigger] m.consts@[l]).id,
    {
        ks.push(m.consts[i].id);
    }
    ks
}

fn keys_allocs(m: &MirCrate) -> (ks: Vec<usize>)
    ensures ks@.len() == m.allocs@.len(), forall|i: int| 0 <= i < ks@.len() ==> ks@[i] == (#[trigger] m.allocs@[i]).id,
{
    let mut ks = Vec::new();
    for i in 0..m.allocs.len()
        invariant ks@.len() == i, forall|l: int| 0 <= l < i ==> ks@[l] == (#[trigger] m.allocs@[l]).id,
    {
        ks.push(m.allocs[i].id);
    }
    ks
}

fn keys_insts(m: &MirCrate) -> (ks: Vec<usize>)
    ensures ks@.len() == m.insts@.len(), forall|i: int| 0 <= i < ks@.len() ==> ks@[i] == (#[trigger] m.insts@[i]).id,
{
    let mut ks = Vec::new();
    for i in 0..m.insts.len()
        invariant ks@.len() == i, forall|l: int| 0 <= l < i ==> ks@[l] == (#[trigger] m.insts@[l]).id,
    {
        ks.push(m.insts[i].id);
    }
    ks
}

fn keys_drops(m: &MirCrate) -> (ks: Vec<usize>)
    ensures ks@.len() == m.drops@.len(), forall|i: int| 0 <= i < ks@.len() ==> ks@[i] == (#[trigger] m.drops@[i]).ty,
{
    let mut ks = Vec::new();
    for i in 0..m.drops.len()
        invariant ks@.len() == i, forall|l: int| 0 <= l < i ==> ks@[l] == (#[trigger] m.drops@[l]).ty,
    {
        ks.push(m.drops[i].ty);
    }
    ks
}

fn keys_calls(m: &MirCrate) -> (ks: Vec<usize>)
    ensures ks@.len() == m.calls@.len(), forall|i: int| 0 <= i < ks@.len() ==> ks@[i] == (#[trigger] m.calls@[i]).fn_ty,
{
    let mut ks = Vec::new();
    for i in 0..m.calls.len()
        invariant ks@.len() == i, forall|l: int| 0 <= l < i ==> ks@[l] == (#[trigger] m.calls@[l]).fn_ty,
    {
        ks.push(m.calls[i].fn_ty);
    }
    ks
}

/// The tables of a dump; `None` when some key is at or past `ID_CAP`.
pub fn tabs(m: &MirCrate) -> (r: Option<Tabs>)
    ensures r matches Some(t) ==> tabs_ok(*m, t),
{
    let ks = keys_tys(m);
    let tys = index(&ks)?;
    proof { lemma_tab_tys(*m, ks@, tys@); }
    let ks = keys_adts(m);
    let adts = index(&ks)?;
    proof { lemma_tab_adts(*m, ks@, adts@); }
    let ks = keys_layouts(m);
    let layouts = index(&ks)?;
    proof { lemma_tab_layouts(*m, ks@, layouts@); }
    let ks = keys_consts(m);
    let consts = index(&ks)?;
    proof { lemma_tab_consts(*m, ks@, consts@); }
    let ks = keys_allocs(m);
    let allocs = index(&ks)?;
    proof { lemma_tab_allocs(*m, ks@, allocs@); }
    let ks = keys_insts(m);
    let insts = index(&ks)?;
    proof { lemma_tab_insts(*m, ks@, insts@); }
    let ks = keys_drops(m);
    let drops = index(&ks)?;
    proof { lemma_tab_drops(*m, ks@, drops@); }
    let ks = keys_calls(m);
    let calls = index(&ks)?;
    proof { lemma_tab_calls(*m, ks@, calls@); }
    Some(Tabs { tys, adts, layouts, consts, allocs, insts, drops, calls })
}

// ------------------------------------------------------------------ row lookups

fn slot(t: &Vec<Option<usize>>, k: usize) -> (r: Option<usize>)
    ensures r == if (k as int) < t@.len() { t@[k as int] } else { None },
{
    if k < t.len() { t[k] } else { None }
}

#[allow(unused_variables)] // used in the specs
fn ix_tys(m: &MirCrate, tb: &Tabs, k: usize) -> (r: Option<usize>)
    requires tabs_ok(*m, *tb),
    ensures onat(r) == find(m.tys@, |r: TyRow| r.id == k), r matches Some(i) ==> i < m.tys@.len(),
{
    broadcast use lemma_find_spec;
    reveal(tab_tys);
    let r = slot(&tb.tys, k);
    proof { if (k as int) >= tb.tys@.len() { lemma_find(m.tys@, |r: TyRow| r.id == k, m.tys@.len()); } }
    r
}

#[allow(unused_variables)] // used in the specs
fn ix_adts(m: &MirCrate, tb: &Tabs, k: usize) -> (r: Option<usize>)
    requires tabs_ok(*m, *tb),
    ensures onat(r) == find(m.adts@, |r: Adt| r.ty == k), r matches Some(i) ==> i < m.adts@.len(),
{
    broadcast use lemma_find_spec;
    reveal(tab_adts);
    let r = slot(&tb.adts, k);
    proof { if (k as int) >= tb.adts@.len() { lemma_find(m.adts@, |r: Adt| r.ty == k, m.adts@.len()); } }
    r
}

#[allow(unused_variables)] // used in the specs
fn ix_layouts(m: &MirCrate, tb: &Tabs, k: usize) -> (r: Option<usize>)
    requires tabs_ok(*m, *tb),
    ensures onat(r) == find(m.layouts@, |r: LayoutRow| r.ty == k), r matches Some(i) ==> i < m.layouts@.len(),
{
    broadcast use lemma_find_spec;
    reveal(tab_layouts);
    let r = slot(&tb.layouts, k);
    proof { if (k as int) >= tb.layouts@.len() { lemma_find(m.layouts@, |r: LayoutRow| r.ty == k, m.layouts@.len()); } }
    r
}

#[allow(unused_variables)] // used in the specs
fn ix_consts(m: &MirCrate, tb: &Tabs, k: usize) -> (r: Option<usize>)
    requires tabs_ok(*m, *tb),
    ensures onat(r) == find(m.consts@, |r: ConstRow| r.id == k), r matches Some(i) ==> i < m.consts@.len(),
{
    broadcast use lemma_find_spec;
    reveal(tab_consts);
    let r = slot(&tb.consts, k);
    proof { if (k as int) >= tb.consts@.len() { lemma_find(m.consts@, |r: ConstRow| r.id == k, m.consts@.len()); } }
    r
}

#[allow(unused_variables)] // used in the specs
fn ix_allocs(m: &MirCrate, tb: &Tabs, k: usize) -> (r: Option<usize>)
    requires tabs_ok(*m, *tb),
    ensures onat(r) == find(m.allocs@, |r: AllocRow| r.id == k), r matches Some(i) ==> i < m.allocs@.len(),
{
    broadcast use lemma_find_spec;
    reveal(tab_allocs);
    let r = slot(&tb.allocs, k);
    proof { if (k as int) >= tb.allocs@.len() { lemma_find(m.allocs@, |r: AllocRow| r.id == k, m.allocs@.len()); } }
    r
}

#[allow(unused_variables)] // used in the specs
fn ix_drops(m: &MirCrate, tb: &Tabs, k: usize) -> (r: Option<usize>)
    requires tabs_ok(*m, *tb),
    ensures onat(r) == find(m.drops@, |d: DropRow| d.ty == k), r matches Some(i) ==> i < m.drops@.len(),
{
    broadcast use lemma_find_spec;
    reveal(tab_drops);
    let r = slot(&tb.drops, k);
    proof { if (k as int) >= tb.drops@.len() { lemma_find(m.drops@, |d: DropRow| d.ty == k, m.drops@.len()); } }
    r
}

#[allow(unused_variables)] // used in the specs
fn ix_calls(m: &MirCrate, tb: &Tabs, k: usize) -> (r: Option<usize>)
    requires tabs_ok(*m, *tb),
    ensures onat(r) == find(m.calls@, |r: Call| r.fn_ty == k), r matches Some(i) ==> i < m.calls@.len(),
{
    broadcast use lemma_find_spec;
    reveal(tab_calls);
    let r = slot(&tb.calls, k);
    proof { if (k as int) >= tb.calls@.len() { lemma_find(m.calls@, |r: Call| r.fn_ty == k, m.calls@.len()); } }
    r
}

// ------------------------------------------------------------------ `sem`'s lookups

pub fn t_rigid<'a>(m: &'a MirCrate, tb: &Tabs, t: Ty) -> (r: Option<&'a RigidTy>)
    requires tabs_ok(*m, *tb),
    ensures match r { Some(x) => rigid(*m, t) == Some(*x), None => rigid(*m, t) is None },
{
    match ix_tys(m, tb, t) {
        Some(i) => match &m.tys[i].kind { TyKind::RigidTy(r) => Some(r), _ => None },
        None => None,
    }
}

pub fn t_adt_row<'a>(m: &'a MirCrate, tb: &Tabs, t: Ty) -> (r: Option<&'a Adt>)
    requires tabs_ok(*m, *tb),
    ensures match r { Some(x) => adt_row(*m, t) == Some(*x), None => adt_row(*m, t) is None },
{
    match ix_adts(m, tb, t) { Some(i) => Some(&m.adts[i]), None => None }
}

pub fn t_layout<'a>(m: &'a MirCrate, tb: &Tabs, t: Ty) -> (r: Option<&'a LayoutShape>)
    requires tabs_ok(*m, *tb),
    ensures match r { Some(x) => layout(*m, t) == Some(*x), None => layout(*m, t) is None },
{
    match ix_layouts(m, tb, t) { Some(i) => Some(&m.layouts[i].shape), None => None }
}

pub fn t_const_usize(m: &MirCrate, tb: &Tabs, id: TyConstId) -> (r: Option<u64>)
    requires tabs_ok(*m, *tb),
    ensures r == const_usize(*m, id),
{
    match ix_consts(m, tb, id) { Some(i) => m.consts[i].usize, None => None }
}

pub fn t_alloc_mem<'a>(m: &'a MirCrate, tb: &Tabs, id: AllocId) -> (r: Option<&'a Allocation>)
    requires tabs_ok(*m, *tb),
    ensures match r { Some(x) => alloc_mem(*m, id) == Some(*x), None => alloc_mem(*m, id) is None },
{
    match ix_allocs(m, tb, id) {
        Some(i) => match &m.allocs[i].alloc { GlobalAlloc::Memory(a) => Some(a), _ => None },
        None => None,
    }
}

#[allow(unused_variables)] // used in the specs
pub fn t_inst_idx(m: &MirCrate, tb: &Tabs, id: InstanceDef) -> (r: Option<usize>)
    requires tabs_ok(*m, *tb),
    ensures match r { Some(j) => inst_idx(*m, id) == Some(j as nat) && j < m.insts@.len(), None => inst_idx(*m, id) is None },
{
    broadcast use lemma_find_spec;
    reveal(tab_insts);
    let r = slot(&tb.insts, id);
    proof { if (id as int) >= tb.insts@.len() { lemma_find(m.insts@, |x: Inst| x.id == id, m.insts@.len()); } }
    r
}

pub fn t_drop_row<'a>(m: &'a MirCrate, tb: &Tabs, t: Ty) -> (r: Option<&'a DropRow>)
    requires tabs_ok(*m, *tb),
    ensures match r { Some(x) => drop_row(*m, t) == Some(*x), None => drop_row(*m, t) is None },
{
    match ix_drops(m, tb, t) { Some(i) => Some(&m.drops[i]), None => None }
}

pub fn t_int_ty(m: &MirCrate, tb: &Tabs, t: Ty) -> (o: Option<ctcore::syntax::IntTy>)
    requires tabs_ok(*m, *tb),
    ensures o == int_ty(*m, t),
{
    match t_rigid(m, tb, t) { Some(r) => x_int_of(r), None => None }
}

/// `callee_of`: the `insts` index and generic args of a constant `FnDef` callee.
pub fn t_callee_of<'a>(m: &'a MirCrate, tb: &Tabs, func: &Operand) -> (r: Option<(usize, &'a GenericArgs)>)
    requires tabs_ok(*m, *tb),
    ensures match r {
        Some((j, g)) => callee_of(*m, *func) == Some((j as nat, *g)) && j < m.insts@.len(),
        None => callee_of(*m, *func) is None,
    },
{
    match func {
        Operand::Constant(c) => match ix_calls(m, tb, c.const_.ty) {
            Some(k) => match m.calls[k].resolved {
                Some(id) => match t_inst_idx(m, tb, id) { Some(j) => Some((j, &m.calls[k].args)), None => None },
                None => None,
            },
            None => None,
        },
        _ => None,
    }
}

#[allow(unused_variables)] // used in the specs
pub fn t_inst_body<'a>(m: &'a MirCrate, tb: &Tabs, i: usize) -> (r: Option<&'a Body>)
    requires tabs_ok(*m, *tb),
    ensures match r { Some(b) => inst_body(*m, i as nat) == Some(*b), None => inst_body(*m, i as nat) is None },
{
    x_inst_body(m, i)
}

pub fn t_is_mut_ref(m: &MirCrate, tb: &Tabs, t: Ty) -> (r: bool)
    requires tabs_ok(*m, *tb),
    ensures r == is_mut_ref(*m, t),
{
    matches!(t_rigid(m, tb, t), Some(RigidTy::Ref(_, _, Mutability::Mut)))
}

pub fn t_is_zst(m: &MirCrate, tb: &Tabs, t: Ty) -> (r: bool)
    requires tabs_ok(*m, *tb),
    ensures r == is_zst(*m, t),
{
    let sized = match t_rigid(m, tb, t) {
        Some(r) => !(matches!(r, RigidTy::Str) || matches!(r, RigidTy::Slice(_)) || matches!(r, RigidTy::Dynamic(_, _))),
        None => false,
    };
    sized && match t_layout(m, tb, t) { Some(l) => l.size.num_bits == 0, None => false }
}

pub fn t_vec_elem(m: &MirCrate, tb: &Tabs, t: Ty) -> (r: Option<Ty>)
    requires tabs_ok(*m, *tb),
    ensures r == vec_elem(*m, t),
{
    match (t_adt_row(m, tb, t), t_rigid(m, tb, t)) {
        (Some(a), Some(RigidTy::Adt(_, ga))) => {
            if crate::json::bytes_eq(a.name.as_slice(), b"std::vec::Vec") && ga.0.len() >= 1 {
                match &ga.0[0] { GenericArgKind::Type(e) => Some(*e), _ => None }
            } else { None }
        },
        _ => None,
    }
}

pub fn t_proj_ty(m: &MirCrate, tb: &Tabs, t: Ty, e: &ProjectionElem) -> (r: Option<Ty>)
    requires tabs_ok(*m, *tb),
    ensures r == proj_ty(*m, t, *e),
{
    match e {
        ProjectionElem::Deref => match t_rigid(m, tb, t) { Some(RigidTy::Ref(_, p, _)) => Some(*p), _ => None },
        ProjectionElem::Field(_, ft) => Some(*ft),
        ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => match t_rigid(m, tb, t) {
            Some(RigidTy::Array(el, _)) => Some(*el),
            Some(RigidTy::Slice(el)) => Some(*el),
            _ => None,
        },
        ProjectionElem::Downcast(_) => Some(t),
        _ => None,
    }
}

proof fn lemma_tys_none(m: MirCrate, t: Ty, ps: Seq<ProjectionElem>, k: nat, n: nat)
    requires k <= n, tys_along(m, t, ps, k) is None,
    ensures tys_along(m, t, ps, n) is None,
    decreases n - k,
{
    if k < n { lemma_tys_none(m, t, ps, k, (n - 1) as nat); }
}

pub fn t_place_ty(m: &MirCrate, tb: &Tabs, b: &Body, p: &Place) -> (r: Option<Ty>)
    requires tabs_ok(*m, *tb),
    ensures r == place_ty(*m, *b, *p),
{
    if p.local >= b.locals.len() { return None; }
    let mut u = b.locals[p.local].ty;
    let mut k: usize = 0;
    while k < p.projection.len()
        invariant k <= p.projection@.len(), p.local < b.locals@.len(), tabs_ok(*m, *tb),
            tys_along(*m, b.locals@[p.local as int].ty, p.projection@, k as nat) == Some(u),
        decreases p.projection.len() - k,
    {
        u = match t_proj_ty(m, tb, u, &p.projection[k]) {
            Some(v) => v,
            None => {
                proof { lemma_tys_none(*m, b.locals@[p.local as int].ty, p.projection@, (k + 1) as nat, p.projection@.len()); }
                return None;
            },
        };
        k += 1;
    }
    Some(u)
}

pub fn t_op_ty(m: &MirCrate, tb: &Tabs, b: &Body, x: &Operand) -> (r: Option<Ty>)
    requires tabs_ok(*m, *tb),
    ensures r == op_ty(*m, *b, *x),
{
    match x {
        Operand::Copy(p) | Operand::Move(p) => t_place_ty(m, tb, b, p),
        Operand::Constant(k) => Some(k.const_.ty),
        _ => None,
    }
}

} // verus!
