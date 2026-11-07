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
// ponytail: fixed 16 KiB out-of-order window past the contiguous end (§7.5 floor is 4096); grow during the handshake only if real ClientHellos need it.
/// Data ending within `crypto_contiguous + MAX_CRYPTO_BUFFER` is always accepted.
pub const MAX_CRYPTO_BUFFER: u64 = 16384;

/// The end of the in-order CRYPTO data received: every byte below it has been received, and the
/// byte at it has not. Bytes received past it are the out-of-order data of RFC 9000 §7.5.
pub open spec fn crypto_contiguous(s: CryptoStream) -> nat {
    rfc_contiguous(rfc_received(s.reassembly().inserted()))
}

/// Our own limit: a frame with data ending past `contiguous + MAX_CRYPTO_BUFFER` overflows the
/// out-of-order window. An empty frame buffers nothing, so it never does.
pub open spec fn crypto_window_exceeded(contiguous: nat, offset: u64, len: nat) -> bool {
    len > 0 && offset + len > contiguous + MAX_CRYPTO_BUFFER
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
    c == CRYPTO_BUFFER_EXCEEDED && crypto_window_exceeded(crypto_contiguous(s), offset, len)
}

/// `crypto_allowed_err` is not vacuous: an empty frame is never a window error, a 1-byte frame
/// at offset 0 is in the window, and no other code is allowed.
proof fn lemma_crypto_allowed_err_rejects(s: CryptoStream, offset: u64)
    ensures
        !crypto_allowed_err(s, offset, 0, CRYPTO_BUFFER_EXCEEDED),
        !crypto_allowed_err(s, 0, 1, CRYPTO_BUFFER_EXCEEDED),
        !crypto_allowed_err(s, offset, 1, PROTOCOL_VIOLATION),
{
    lemma_crypto_floor(s, 0, 1);
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-7.5
//# Implementations MUST support buffering at least 4096 bytes of data
//# received in out-of-order CRYPTO frames.
/// The floor: a frame whose out-of-order part (its bytes past `crypto_contiguous`) ends within
/// 4096 bytes of the contiguous end is never refused, however much in-order data is unread.
pub proof fn lemma_crypto_floor(s: CryptoStream, offset: u64, len: nat)
    requires
        offset + len <= crypto_contiguous(s) + 4096,
    ensures
        !crypto_window_exceeded(crypto_contiguous(s), offset, len),
        forall|c: u64| !#[trigger] crypto_allowed_err(s, offset, len, c),
{
}

/// The CRYPTO stream of one encryption level.
pub struct CryptoStream {
    re: Reassembly,
    /// `crypto_contiguous`, kept so a frame costs O(1) plus the bytes it makes contiguous.
    contig: u64,
}

impl CryptoStream {
    pub closed spec fn reassembly(&self) -> Reassembly {
        self.re
    }

    pub closed spec fn contig_spec(&self) -> nat {
        self.contig as nat
    }

    /// The buffer holds the unread in-order bytes, `[base, crypto_contiguous)`, plus at most
    /// `MAX_CRYPTO_BUFFER` bytes of window past them.
    pub open spec fn wf(&self) -> bool {
        &&& self.reassembly().wf()
        &&& self.reassembly().tight()
        &&& self.contig_spec() == crypto_contiguous(*self)
        &&& self.reassembly().base() + self.reassembly().buf_len() <= crypto_contiguous(*self)
            + MAX_CRYPTO_BUFFER
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
        let re = Reassembly::new();
        proof {
            re.lemma_wf();
        }
        let contig = re.contiguous_from(0);
        let r = CryptoStream { re, contig };
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
        let re = Reassembly::new_at(base);
        proof {
            re.lemma_wf();
        }
        let contig = re.contiguous_from(base);
        let r = CryptoStream { re, contig };
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
            r is Err <==> crypto_window_exceeded(crypto_contiguous(*old(self)), offset, data@.len()),
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
            // non-empty frame past the window always closes the connection, below.
            return Ok(());
        }
        if data.len() == 0 {
            // No bytes: nothing is buffered, so the buffer is not exceeded at any offset
            // (RFC 9000 §7.5), and the window is not extended past what was received (RFC 9001
            // §4.1.3). Checked before the window.
            return Ok(());
        }
        proof {
            self.re.lemma_contiguous_le_end();
        }
        if end > self.contig + MAX_CRYPTO_BUFFER {
            //= https://www.rfc-editor.org/rfc/rfc9000#section-7.5
            //# If an endpoint does not expand its buffer, it MUST close
            //# the connection with a CRYPTO_BUFFER_EXCEEDED error code.
            return Err(CRYPTO_BUFFER_EXCEEDED);
        }
        self.re.insert(offset, data);
        proof {
            Reassembly::lemma_insert_tight(old(self).re, self.re, offset, data@);
            lemma_received_push(old(self).re.inserted(), offset as nat, data@);
            lemma_contiguous_mono(
                rfc_received(old(self).re.inserted()),
                rfc_received(self.re.inserted()),
            );
        }
        self.contig = self.re.contiguous_from(self.contig);
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
