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
    }

    pub fn new() -> (r: CryptoStream)
        ensures
            r.wf(),
            r.reassembly().inserted() == Seq::<(nat, Seq<u8>)>::empty(),
            r.reassembly().base() == 0,
    {
        CryptoStream { re: Reassembly::new() }
    }

    /// A CRYPTO frame's `offset` and `data`.
    pub fn on_crypto(&mut self, offset: u64, data: &[u8]) -> (r: Result<(), u64>)
        requires
            old(self).wf(),
            offset + data@.len() <= VARINT_MAX,
        ensures
            final(self).wf(),
            r is Err <==> offset + data@.len() > old(self).reassembly().base() + MAX_CRYPTO_BUFFER,
            r is Err ==> r == Err::<(), u64>(CRYPTO_BUFFER_EXCEEDED),
            (r is Err || offset + data@.len() <= old(self).reassembly().base()) ==> *final(self)
                == *old(self),
            (r is Ok && offset + data@.len() > old(self).reassembly().base()) ==> {
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
        if end > base + MAX_CRYPTO_BUFFER {
            //= https://www.rfc-editor.org/rfc/rfc9000#section-7.5
            //# If an endpoint does not expand its buffer, it MUST close
            //# the connection with a CRYPTO_BUFFER_EXCEEDED error code.
            return Err(CRYPTO_BUFFER_EXCEEDED);
        }
        self.re.insert(offset, data);
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
