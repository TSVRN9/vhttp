use vstd::prelude::*;

verus! {

pub fn quad(n: u32) -> (r: u64)
    ensures
        r == 4 * n,
{
    let d = dep::m::double(n);
    d * 2
}

pub fn count(n: u32) -> (r: u64)
    ensures
        r == n,
{
    let mut i: u64 = 0;
    while i < n as u64
        invariant
            i <= n,
        decreases n - i,
    {
        i += 1;
    }
    i
}

} // verus!
