use vstd::prelude::*;

verus! {

//= https://www.rfc-editor.org/rfc/rfc9000#section-7.4
//# An endpoint MUST treat receipt of a transport parameter with an invalid value as a connection error of type
//# TRANSPORT_PARAMETER_ERROR.
/// A parameter the RFC rejects.
pub open spec fn allowed_demo_err(n: u64, c: u64) -> bool {
    n > 10 && c == TRANSPORT_PARAMETER_ERROR
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-7.4
//# An endpoint MUST treat receipt of a transport parameter with an invalid value as a connection error of type
//# TRANSPORT_PARAMETER_ERROR.
spec fn demo_code(n: u64) -> u64 {
    TRANSPORT_PARAMETER_ERROR
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-7.4
//# An endpoint MUST treat receipt of a transport parameter with an invalid value as a connection error of type
//# TRANSPORT_PARAMETER_ERROR.
/// Closes with the mapped code.
#[verifier::spinoff_prover]
pub fn demo_close(c: &mut Conn, n: u64)
    ensures
        final(c).close_spec() == Some((false, TRANSPORT_PARAMETER_ERROR, Seq::<u8>::empty())),
{
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-7.4
//# An endpoint MUST treat receipt of a transport parameter with an invalid value as a connection error of type
//# TRANSPORT_PARAMETER_ERROR.
pub fn demo_map(c: &mut Conn, n: u64)
    ensures
        final(c).close_spec() == Some(
            (false, demo_code(n), Seq::<u8>::empty()),
        ),
{
}

} // verus!
