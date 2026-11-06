use vstd::prelude::*;

verus! {

pub open spec fn allowed_demo_err(n: u64, c: u64) -> bool {
    n > 10 && c == 7
}

pub fn demo(n: u64) -> (r: Result<(), u64>)
    ensures
        r is Err ==> allowed_demo_err(n, r->Err_0),
{
    if n > 10 { Err(7) } else { Ok(()) }
}

} // verus!
