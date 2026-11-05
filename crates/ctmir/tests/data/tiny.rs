// The source of tiny.json: the lib.rs of a scratch crate `tiny` (edition 2021, own [workspace]),
// dumped by running tools/ct-driver by hand the way scripts/ct-check.sh does: RUSTC_WORKSPACE_WRAPPER=
// <ct-driver> RUSTC_BOOTSTRAP=1 CT_CRATES=tiny CT_OUT=<dir> cargo build --release (it was dumped
// while the driver still read a manifest and CT_MODE=dump; the dump does not depend on either).
pub fn tiny(a: &[u8; 4], i: usize) -> u8 { let x = [1u8, 2, 3]; a[i & 3] ^ x[1] }
pub fn opt(b: bool) -> Option<u8> { if b { Some(3) } else { None } }
pub fn call(a: &[u8; 4]) -> u8 { tiny(a, 2) }
