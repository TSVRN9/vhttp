// rfc-quantity gate fixture: recv_allowed_err and its helpers as on main ed35647 (9a 0a8c534), comments dropped.
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

pub open spec fn largest_received_offset(ins: Seq<(nat, Seq<u8>)>) -> nat
    decreases ins.len(),
{
    if ins.len() == 0 {
        0
    } else {
        let p = largest_received_offset(ins.drop_last());
        let e = ins.last().0 + ins.last().1.len();
        if e > p {
            e
        } else {
            p
        }
    }
}

pub open spec fn recv_data(s: SpecRecv, off: nat, data: Seq<u8>, fin: bool) -> SpecRecv {
    let end = off + data.len();
    if end > s.limit {
        s
    } else {
        let ins = s.ins.push((off, data));
        SpecRecv { ins, high: if end > s.high { end } else { s.high }, final_size: if fin { Some(end) } else { s.final_size }, ..s }
    }
}

pub open spec fn recv_reset(s: SpecRecv, fs: nat) -> SpecRecv {
    SpecRecv { final_size: Some(fs), high: fs, ..s }
}

pub open spec fn recv_inv(s: SpecRecv) -> bool {
    &&& largest_received_offset(s.ins) <= s.high
    &&& s.final_size is None ==> s.high == largest_received_offset(s.ins)
}

pub struct RecvStream {
    ins: Ghost<Seq<(nat, Seq<u8>)>>,
}

impl RecvStream {
    pub closed spec fn wf(&self, s: SpecRecv) -> bool {
        self.ins@ == s.ins
    }
}

#[verifier::opaque]
pub open spec fn credit_before(s: SpecRecv) -> nat {
    match s.final_size {
        Some(f) => f,
        None => largest_received_offset(s.ins),
    }
}

#[verifier::opaque]
pub open spec fn credit_after(s: SpecRecv, end: nat, fin: bool) -> nat {
    if fin {
        end
    } else if s.final_size is Some {
        s.final_size->0
    } else if end > largest_received_offset(s.ins) {
        end
    } else {
        largest_received_offset(s.ins)
    }
}

#[verifier::opaque]
pub open spec fn final_size_trigger(s: SpecRecv, end: nat, fin: bool) -> bool {
    ||| s.final_size is Some && end > s.final_size->0
    ||| fin && end < largest_received_offset(s.ins)
    ||| fin && s.final_size is Some && end != s.final_size->0
}

#[verifier::opaque]
pub open spec fn flow_trigger(s: SpecRecv, end: nat, fin: bool, conn_room: nat) -> bool {
    ||| end > s.limit
    ||| credit_after(s, end, fin) > credit_before(s) + conn_room
}

#[verifier::opaque]
pub open spec fn recv_allowed_err(
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
