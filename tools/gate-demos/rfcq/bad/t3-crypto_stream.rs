// rfc-quantity gate demo: crypto_allowed_err and crypto_window_exceeded verbatim from fcf9ff0^ (9a T3 review I2), the
// window anchored at the read offset `s.reassembly().base()`, the code's bookkeeping.
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

/// Our own limit: a frame with data ending past `base + MAX_CRYPTO_BUFFER` overflows the window.
/// An empty frame buffers nothing, so it never does.
pub open spec fn crypto_window_exceeded(base: nat, offset: u64, len: nat) -> bool {
    len > 0 && offset + len > base + MAX_CRYPTO_BUFFER
}

pub open spec fn crypto_allowed_err(s: CryptoStream, offset: u64, len: nat, c: u64) -> bool {
    c == CRYPTO_BUFFER_EXCEEDED && crypto_window_exceeded(s.reassembly().base(), offset, len)
}

} // verus!
