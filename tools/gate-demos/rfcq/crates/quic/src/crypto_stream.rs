// rfc-quantity gate fixture: crypto_allowed_err as fixed in 9a (fcf9ff0), with stub bookkeeping.
use vstd::prelude::*;

verus! {

pub const MAX_CRYPTO_BUFFER: u64 = 16384;

pub const CRYPTO_BUFFER_EXCEEDED: u64 = 0x0d;

pub struct Reassembly {
    base: u64,
    ins: Ghost<Seq<(nat, Seq<u8>)>>,
}

impl Reassembly {
    pub closed spec fn inserted(&self) -> Seq<(nat, Seq<u8>)> {
        self.ins@
    }

    pub closed spec fn base(&self) -> nat {
        self.base as nat
    }
}

pub struct CryptoStream {
    re: Reassembly,
}

impl CryptoStream {
    pub closed spec fn reassembly(&self) -> Reassembly {
        self.re
    }
}

pub open spec fn rfc_contiguous(ins: Seq<(nat, Seq<u8>)>) -> nat {
    ins.len()
}

pub open spec fn crypto_contiguous(s: CryptoStream) -> nat {
    rfc_contiguous(s.reassembly().inserted())
}

pub open spec fn crypto_window_exceeded(contiguous: nat, offset: u64, len: nat) -> bool {
    len > 0 && offset + len > contiguous + MAX_CRYPTO_BUFFER
}

pub open spec fn crypto_allowed_err(s: CryptoStream, offset: u64, len: nat, c: u64) -> bool {
    c == CRYPTO_BUFFER_EXCEEDED && crypto_window_exceeded(crypto_contiguous(s), offset, len)
}

} // verus!
