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
pub open spec fn allowed_demo_err_from(n: u64, c: u64) -> bool {
    allowed_demo_err(n, c)
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

pub fn demo_info(c: &Conn) -> (r: Option<(bool, u64, Vec<u8>)>)
    ensures
        r matches Some((a, k, v)) ==> c.close_spec() == Some((*a, *k, v@)),
        r is None ==> c.close_spec() is None,
        r matches Some((_, k, v)) ==> *k <= VARINT_MAX,
{
}

} // verus!
