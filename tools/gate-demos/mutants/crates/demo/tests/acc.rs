// Tests for the mutants demos (scripts/gate-demos.sh): D-kill (Err(8)) fails the first; the second passes mutated or
// not; the third fails unmutated too.
use demo::acc::demo;

#[test]
fn demo_eleven_is_err7() {
    assert_eq!(demo(11), Err(7));
}

#[test]
fn demo_three_is_ok() {
    assert_eq!(demo(3), Ok(()));
}

#[test]
fn demo_three_is_err() {
    assert_eq!(demo(3), Err(7));
}
