use vstd::prelude::*;

verus! {

pub fn double(n: u32) -> (r: u64)
    ensures
        r == 2 * n,
{
    (n as u64) * 2
}

} // verus!
