// rfc-quantity gate demo: recv_allowed_err and its helpers verbatim from 8f6b48e (9a T6 review I1), reading rfc_recv's
// running `high` (and `counted`, over `high`) instead of the RFC's largest received offset.
use vstd::prelude::*;

verus! {

pub const FINAL_SIZE_ERROR: u64 = 0x06;

pub const FLOW_CONTROL_ERROR: u64 = 0x03;

pub struct SpecRecv {
    pub ins: Seq<(nat, Seq<u8>)>,
    pub high: nat,
    pub final_size: Option<nat>,
    pub limit: nat,
}

pub open spec fn counted(s: SpecRecv) -> nat {
    match s.final_size {
        Some(f) => f,
        None => s.high,
    }
}

pub closed spec fn credit_after(s: SpecRecv, end: nat, fin: bool) -> nat {
    if fin {
        end
    } else if s.final_size is Some {
        s.final_size->0
    } else if end > s.high {
        end
    } else {
        s.high
    }
}

pub closed spec fn final_size_trigger(s: SpecRecv, end: nat, fin: bool) -> bool {
    ||| s.final_size is Some && end > s.final_size->0
    ||| fin && end < s.high
    ||| fin && s.final_size is Some && end != s.final_size->0
}

pub closed spec fn flow_trigger(s: SpecRecv, end: nat, fin: bool, conn_room: nat) -> bool {
    ||| end > s.limit
    ||| credit_after(s, end, fin) > counted(s) + conn_room
}

pub closed spec fn recv_allowed_err(
    s: SpecRecv,
    off: nat,
    len: nat,
    fin: bool,
    conn_room: nat,
    c: u64,
) -> bool {
    ||| c == FINAL_SIZE_ERROR && final_size_trigger(s, off + len, fin)
    ||| c == FLOW_CONTROL_ERROR && flow_trigger(s, off + len, fin, conn_room)
}

} // verus!
