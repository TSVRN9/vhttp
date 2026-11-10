use vstd::prelude::*;

verus! {

fn good_fn(x: u8) -> (r: u8)
    ensures
        r == x,
{
    x
}

fn no_ens(x: u8) -> u8 {
    x
}

} // verus!

#[test]
fn good_test() {}
