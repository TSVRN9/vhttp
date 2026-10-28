#![allow(unused_braces)]
use vstd::prelude::*;

verus! {

global size_of usize == 8;

} // verus!

pub mod bytes;
pub mod sha256;
mod shim;
