use vstd::prelude::*;

verus! {
/// Constant-time checker marker: the result is treated as public. Every call site has a
/// `ct-declassify:` row in TRUSTED.md.
#[inline(always)]
pub(crate) fn declassify<T>(x: T) -> (r: T)
    ensures r == x,
{ x }
}
