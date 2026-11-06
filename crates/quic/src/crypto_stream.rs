//! CRYPTO streams (RFC 9000 §7.5, §19.6): one reassembly buffer per encryption level, with
//! a fixed window past the read offset. CRYPTO data has no flow control (§4).
use vstd::prelude::*;
use crate::codes::*;
use crate::reassembly::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use wire::varint::*;

verus! {

//= https://www.rfc-editor.org/rfc/rfc9000#section-7.5
//# Implementations MUST support buffering at least 4096 bytes of data
//# received in out-of-order CRYPTO frames.
// ponytail: fixed 16 KiB window past the read offset (§7.5 floor is 4096); grow during the handshake only if real ClientHellos need it.
/// Data ending within `read offset + MAX_CRYPTO_BUFFER` is always accepted.
pub const MAX_CRYPTO_BUFFER: u64 = 16384;

/// Our own limit: a frame with data ending past `base + MAX_CRYPTO_BUFFER` overflows the window.
/// An empty frame buffers nothing, so it never does.
pub open spec fn crypto_window_exceeded(base: nat, offset: u64, len: nat) -> bool {
    len > 0 && offset + len > base + MAX_CRYPTO_BUFFER
}

/// The errors `on_crypto` may return: CRYPTO_BUFFER_EXCEEDED on the window overflow. During the
/// handshake the close is required; after it, closing is the chosen one of two MAYs.
//= https://www.rfc-editor.org/rfc/rfc9000#section-7.5
//# If an endpoint does not expand its buffer, it MUST close
//# the connection with a CRYPTO_BUFFER_EXCEEDED error code.
//= https://www.rfc-editor.org/rfc/rfc9000#section-7.5
//# Once the handshake completes, if an endpoint is unable to buffer all
//# data in a CRYPTO frame, it MAY discard that CRYPTO frame and all
//# CRYPTO frames received in the future, or it MAY close the connection
//# with a CRYPTO_BUFFER_EXCEEDED error code.
pub open spec fn crypto_allowed_err(s: CryptoStream, offset: u64, len: nat, c: u64) -> bool {
    c == CRYPTO_BUFFER_EXCEEDED && crypto_window_exceeded(s.reassembly().base(), offset, len)
}

/// `crypto_allowed_err` is not vacuous: an empty frame is never a window error, and no other
/// code is allowed.
proof fn lemma_crypto_allowed_err_rejects(s: CryptoStream, offset: u64)
    ensures
        !crypto_allowed_err(s, offset, 0, CRYPTO_BUFFER_EXCEEDED),
        !crypto_allowed_err(s, offset, 1, PROTOCOL_VIOLATION),
{
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-7.5
//# Implementations MUST support buffering at least 4096 bytes of data
//# received in out-of-order CRYPTO frames.
/// The floor: data ending within 4096 bytes of the read offset never overflows the window.
pub proof fn lemma_crypto_floor(base: nat, offset: u64, len: nat)
    requires
        offset + len <= base + 4096,
    ensures
        !crypto_window_exceeded(base, offset, len),
{
}

/// The CRYPTO stream of one encryption level.
pub struct CryptoStream {
    re: Reassembly,
}

impl CryptoStream {
    pub closed spec fn reassembly(&self) -> Reassembly {
        self.re
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.reassembly().wf()
        &&& self.reassembly().buf_len() <= MAX_CRYPTO_BUFFER
        &&& self.reassembly().tight()
    }

    /// The byte before `end()` has been received.
    pub proof fn lemma_end_received(&self)
        requires
            self.wf(),
        ensures
            self.reassembly().base() + self.reassembly().buf_len() > 0 ==> rfc_received(
                self.reassembly().inserted(),
            ).contains_key((self.reassembly().base() + self.reassembly().buf_len() - 1) as nat),
    {
        self.re.lemma_end_received();
    }

    pub fn new() -> (r: CryptoStream)
        ensures
            r.wf(),
            r.reassembly().inserted() == Seq::<(nat, Seq<u8>)>::empty(),
            r.reassembly().base() == 0,
    {
        let r = CryptoStream { re: Reassembly::new() };
        proof {
            r.re.lemma_new_tight();
        }
        r
    }

    /// Nothing buffered, and everything below `base` read.
    pub fn new_at(base: u64) -> (r: CryptoStream)
        requires
            base <= VARINT_MAX,
        ensures
            r.wf(),
            r.reassembly().base() == base,
            r.reassembly().buf_len() == 0,
    {
        let r = CryptoStream { re: Reassembly::new_at(base) };
        proof {
            r.re.lemma_new_tight();
        }
        r
    }

    /// A CRYPTO frame's `offset` and `data`.
    pub fn on_crypto(&mut self, offset: u64, data: &[u8]) -> (r: Result<(), u64>)
        requires
            old(self).wf(),
            offset + data@.len() <= VARINT_MAX,
        ensures
            final(self).wf(),
            r is Err <==> crypto_window_exceeded(old(self).reassembly().base(), offset, data@.len()),
            r is Err ==> r == Err::<(), u64>(CRYPTO_BUFFER_EXCEEDED),
            r matches Err(c) ==> crypto_allowed_err(*old(self), offset, data@.len(), c),
            (r is Err || offset + data@.len() <= old(self).reassembly().base() || data@.len() == 0)
                ==> *final(self) == *old(self),
            (r is Ok && offset + data@.len() > old(self).reassembly().base() && data@.len() > 0) ==> {
                &&& final(self).reassembly().inserted() == old(self).reassembly().inserted().push(
                    (offset as nat, data@),
                )
                &&& final(self).reassembly().base() == old(self).reassembly().base()
            },
    {
        proof {
            self.re.lemma_wf();
        }
        let base = self.re.base_exec();
        let end = offset + data.len() as u64;
        if end <= base {
            //= https://www.rfc-editor.org/rfc/rfc9000#section-7.5
            //# Packets containing
            //# discarded CRYPTO frames MUST be acknowledged because the packet has
            //# been received and processed by the transport even though the CRYPTO
            //# frame was discarded.
            // Already read: not an error, so the packet is processed and acknowledged. The
            // post-handshake option to discard frames that don't fit (a MAY) is declined: a
            // frame past the window always closes the connection, below.
            return Ok(());
        }
        if data.len() == 0 {
            // No bytes: nothing is buffered, so the buffer is not exceeded at any offset
            // (RFC 9000 §7.5), and the window is not extended past what was received (RFC 9001
            // §4.1.3). Checked before the window.
            return Ok(());
        }
        if end > base + MAX_CRYPTO_BUFFER {
            //= https://www.rfc-editor.org/rfc/rfc9000#section-7.5
            //# If an endpoint does not expand its buffer, it MUST close
            //# the connection with a CRYPTO_BUFFER_EXCEEDED error code.
            return Err(CRYPTO_BUFFER_EXCEEDED);
        }
        self.re.insert(offset, data);
        proof {
            Reassembly::lemma_insert_tight(old(self).re, self.re, offset, data@);
        }
        Ok(())
    }

    /// Appends the newly contiguous CRYPTO bytes to `out`.
    pub fn read(&mut self, out: &mut Vec<u8>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).reassembly().inserted() == old(self).reassembly().inserted(),
            final(self).reassembly().base() == rfc_contiguous(
                rfc_received(old(self).reassembly().inserted()),
            ),
            final(self).reassembly().base() + final(self).reassembly().buf_len() == old(
                self,
            ).reassembly().base() + old(self).reassembly().buf_len(),
            final(out)@ == old(out)@ + rfc_prefix(
                rfc_received(old(self).reassembly().inserted()),
                final(self).reassembly().base(),
            ).subrange(
                old(self).reassembly().base() as int,
                final(self).reassembly().base() as int,
            ),
    {
        proof {
            self.re.lemma_wf();
        }
        self.re.pop(out);
        proof {
            Reassembly::lemma_pop_tight(old(self).re, self.re);
        }
    }

    /// The read offset.
    pub fn start(&self) -> (r: u64)
        ensures
            r == self.reassembly().base(),
    {
        self.re.base_exec()
    }

    /// The end of the received data: the read offset plus the buffered window.
    pub fn end(&self) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self.reassembly().base() + self.reassembly().buf_len(),
    {
        proof {
            self.re.lemma_wf();
        }
        self.re.base_exec() + self.re.buf_len() as u64
    }
}

} // verus!

impl CryptoStream {
    /// Test support: the allocated capacities of the reassembly buffers. Verus models `Vec`
    /// length, not capacity (TRUSTED.md).
    #[doc(hidden)]
    pub fn capacities(&self) -> (usize, usize) {
        self.re.capacities()
    }
}

const _: () = assert!(MAX_CRYPTO_BUFFER >= 4096);
