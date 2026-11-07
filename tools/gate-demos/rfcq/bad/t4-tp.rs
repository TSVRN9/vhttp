// rfc-quantity gate demo: allowed_tp_err and allowed_tp_err_from verbatim from 6594f10 (9a T4 review I1), the duplicate rule
// reading the code's `seen` mask instead of the IDs earlier in the bytes.
use vstd::prelude::*;

verus! {

pub const TP_ORIGINAL_DESTINATION_CONNECTION_ID: u64 = 0x00;

pub const TP_STATELESS_RESET_TOKEN: u64 = 0x02;

pub const TP_PREFERRED_ADDRESS: u64 = 0x0d;

pub const TP_RETRY_SOURCE_CONNECTION_ID: u64 = 0x10;

pub struct SpecTp {
    pub max_idle_timeout: u64,
}

pub open spec fn spec_default_tp() -> SpecTp {
    SpecTp { max_idle_timeout: 0 }
}

pub open spec fn tp_bit(id: u64) -> u32 {
    1u32 << (id as u32)
}

pub open spec fn rfc_varint_decode(b: Seq<u8>) -> Option<(nat, u64)> {
    if b.len() == 0 { None } else { Some((1, b[0] as u64)) }
}

pub open spec fn rfc_vint(b: Seq<u8>, p: int) -> Option<(u64, int)> {
    match rfc_varint_decode(b.skip(p)) {
        None => None,
        Some((n, v)) => Some((v, p + n)),
    }
}

pub open spec fn rfc_bytes(b: Seq<u8>, p: int, len: int) -> Option<(Seq<u8>, int)> {
    if len > b.len() - p {
        None
    } else {
        Some((b.subrange(p, p + len), p + len))
    }
}

pub open spec fn rfc_tp_apply(id: u64, v: Seq<u8>, from_client: bool, t: SpecTp, seen: u32) -> Option<
    (SpecTp, u32),
> {
    if id > TP_RETRY_SOURCE_CONNECTION_ID {
        Some((t, seen))
    } else if seen & tp_bit(id) != 0 {
        None
    } else {
        Some((t, seen | tp_bit(id)))
    }
}

pub open spec fn tp_value_invalid(id: u64, v: Seq<u8>) -> bool {
    match rfc_varint_decode(v) {
        None => true,
        Some((n, x)) => n != v.len() || id == 0x03 && x < 1200,
    }
}

pub open spec fn tp_server_only(id: u64) -> bool {
    id == TP_ORIGINAL_DESTINATION_CONNECTION_ID || id == TP_PREFERRED_ADDRESS || id
        == TP_RETRY_SOURCE_CONNECTION_ID || id == TP_STATELESS_RESET_TOKEN
}

pub open spec fn allowed_tp_err_from(b: Seq<u8>, p: int, t: SpecTp, seen: u32) -> bool
    decreases (if p < b.len() {
        b.len() - p
    } else {
        0
    }),
    via allowed_tp_err_decreases
{
    if p >= b.len() {
        false
    } else {
        match rfc_vint(b, p) {
            None => true,
            Some((id, q)) => match rfc_vint(b, q) {
                None => true,
                Some((len, r)) => match rfc_bytes(b, r, len as int) {
                    None => true,
                    Some((v, s)) => {
                        ||| id <= TP_RETRY_SOURCE_CONNECTION_ID && seen & tp_bit(id) != 0
                        ||| tp_server_only(id)
                        ||| id <= TP_RETRY_SOURCE_CONNECTION_ID && tp_value_invalid(id, v)
                        ||| match rfc_tp_apply(id, v, true, t, seen) {
                            Some((t2, seen2)) => allowed_tp_err_from(b, s, t2, seen2),
                            None => false,
                        }
                    },
                },
            },
        }
    }
}

proof fn allowed_tp_err_decreases(b: Seq<u8>, p: int, t: SpecTp, seen: u32) {
    lemma_decode_len_bounds(b.skip(p));
    if let Some((n, _)) = rfc_varint_decode(b.skip(p)) {
        lemma_decode_len_bounds(b.skip(p + n));
    }
}

pub open spec fn allowed_tp_err(b: Seq<u8>) -> bool {
    allowed_tp_err_from(b, 0, spec_default_tp(), 0)
}

} // verus!
