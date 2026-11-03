//! The manifest's policy, as the translator takes it (Task 7 adds the parser). Keys and crate
//! names are bytes. `declassify` and `ghost` are the manifest's `declassify <path>` and
//! `ghost <path>` lines (`ghost_unit`: `ghost` is a Verus keyword), the semantics' `CallPolicy`.
use crate::json::bytes_eq;
use crate::sem::CallPolicy;
use vstd::prelude::*;

verus! {

pub struct Policy {
    pub roots: Vec<Vec<u8>>,
    pub cost_roots: Vec<Vec<u8>>,
    /// `label <path> secret(..) public(..)`: the path, the secret names, the public names.
    pub labels: Vec<(Vec<u8>, Vec<Vec<u8>>, Vec<Vec<u8>>)>,
    pub internal_crates: Vec<Vec<u8>>,
    pub translate_crates: Vec<Vec<u8>>,
    pub declassify: Vec<Vec<u8>>,
    pub ghost_unit: Vec<Vec<u8>>,
}

/// `k` is one of `v`'s byte strings.
pub open spec fn has(v: Seq<Vec<u8>>, k: Seq<u8>) -> bool { exists|i: int| 0 <= i < v.len() && (#[trigger] v[i])@ == k }

pub open spec fn set_of(v: Seq<Vec<u8>>) -> Set<Seq<u8>> { v.map_values(|x: Vec<u8>| x@).to_set() }

pub proof fn lemma_set_of(v: Seq<Vec<u8>>, k: Seq<u8>)
    ensures set_of(v).contains(k) == has(v, k),
{
    let w = v.map_values(|x: Vec<u8>| x@);
    w.to_set_ensures();
    if has(v, k) {
        let i = choose|i: int| 0 <= i < v.len() && (#[trigger] v[i])@ == k;
        assert(w[i] == k);
    }
    if w.contains(k) {
        let i = choose|i: int| 0 <= i < w.len() && w[i] == k;
        assert(v[i]@ == k);
    }
}

/// The semantics' view of the policy calls.
pub open spec fn cpol(pol: Policy) -> CallPolicy {
    CallPolicy { declassify: set_of(pol.declassify@), ghost_unit: set_of(pol.ghost_unit@) }
}

pub fn has_exec(v: &Vec<Vec<u8>>, k: &[u8]) -> (r: bool)
    ensures r == has(v@, k@),
{
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v@.len(), forall|j: int| 0 <= j < i ==> (#[trigger] v@[j])@ != k@,
        decreases v.len() - i,
    {
        if bytes_eq(v[i].as_slice(), k) { return true; }
        i += 1;
    }
    false
}

} // verus!
