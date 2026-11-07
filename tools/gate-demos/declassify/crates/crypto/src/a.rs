fn f(x: bool) -> bool {
    if crate::ct::declassify(x) { true } else { false }
}
