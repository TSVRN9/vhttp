//! RFC 8446 §4 handshake message framing over a byte stream (QUIC CRYPTO data): a
//! transcribed spec of "the first complete message", a reassembling reader proven equal to
//! it, and proofs that framing is canonical and independent of how the stream is chunked.
//!
//= https://www.rfc-editor.org/rfc/rfc8446#appendix-D
//# The value of
//# TLSPlaintext.legacy_record_version MUST be ignored by all
//# implementations.
// by construction: QUIC CRYPTO frames carry bare handshake messages; there is no record layer.
use vstd::prelude::*;
use crate::codes::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use crate::pl::*;

verus! {

// RFC 8446 §4: `struct { HandshakeType msg_type; uint24 length; ... } Handshake;`
/// A handshake message: `msg_type`, `uint24 length`, then the body.
pub open spec fn spec_hs_bytes(ty: u8, body: Seq<u8>) -> Seq<u8> {
    seq![ty] + spec_vec_bytes(0xff_ffff, body)
}

/// The length (header included) of the first complete message in `buf`; `Ok(None)` while
/// more bytes are needed. The type is checked at the first byte, so nothing is buffered for
/// a message that will be refused.
pub open spec fn rfc_next_message(buf: Seq<u8>, expect: u8) -> Result<Option<nat>, u64> {
    if buf.len() == 0 {
        Ok(None)
    } else if buf[0] != expect {
        //= https://www.rfc-editor.org/rfc/rfc8446#appendix-D.5
        //# Implementations MUST NOT negotiate TLS 1.3 or later
        //# using an SSL version 2.0 compatible CLIENT-HELLO.
        // by construction: an SSL 2.0 CLIENT-HELLO starts with a length byte with 0x80 set,
        // never HT_CLIENT_HELLO (1), so it is unexpected_message here.
        Err(ALERT_UNEXPECTED_MESSAGE)
    } else if buf.len() < 4 {
        Ok(None)
    } else {
        let len = be(buf.subrange(1, 4), 3);
        if len > MAX_HS_BODY as nat {
            Err(CRYPTO_BUFFER_EXCEEDED)
        } else if buf.len() < 4 + len {
            Ok(None)
        } else {
            Ok(Some(4 + len))
        }
    }
}

//= https://www.rfc-editor.org/rfc/rfc8446#section-5.1
//# Handshake messages MAY be coalesced into a single TLSPlaintext record
//# or fragmented across several records, provided that:
/// A decided result (a message or an error) is unchanged by bytes arriving later; applied
/// repeatedly, the message sequence does not depend on how the stream is chunked (QUIC
/// CRYPTO chunks in place of records).
pub proof fn theorem_next_message_extend(buf: Seq<u8>, rest: Seq<u8>, e: u8)
    requires
        (rfc_next_message(buf, e) matches Ok(Some(_))) || rfc_next_message(buf, e) is Err,
    ensures
        rfc_next_message(buf + rest, e) == rfc_next_message(buf, e),
{
    let b = buf + rest;
    assert(b[0] == buf[0]);
    if buf[0] == e {
        assert(b.subrange(1, 4) =~= buf.subrange(1, 4));
    }
}

/// The framed bytes are exactly the canonical encoding of their type and body.
pub proof fn theorem_hs_canonical(buf: Seq<u8>, e: u8)
    ensures
        rfc_next_message(buf, e) matches Ok(Some(n)) ==> buf.take(n as int) == spec_hs_bytes(
            e,
            buf.subrange(4, n as int),
        ),
{
    if let Ok(Some(n)) = rfc_next_message(buf, e) {
        let h = buf.subrange(1, 4);
        lemma_be_canonical(h, 3);
        assert(h.take(3) =~= h);
        assert(buf.take(n as int) =~= seq![e] + h + buf.subrange(4, n as int));
    }
}

/// A serialized message frames back to itself, whatever follows it.
pub proof fn theorem_hs_roundtrip(body: Seq<u8>, rest: Seq<u8>, e: u8)
    requires
        body.len() <= MAX_HS_BODY as nat,
    ensures
        rfc_next_message(spec_hs_bytes(e, body) + rest, e) == Ok::<Option<nat>, u64>(
            Some(4 + body.len()),
        ),
{
    let b = spec_hs_bytes(e, body) + rest;
    let h = spec_be_bytes(body.len(), 3);
    assert(MAX_HS_BODY == 0x1_0000) by (compute);
    lemma_be_roundtrip(body.len(), 3, seq![]);
    assert(b =~= seq![e] + h + body + rest);
    assert(b.subrange(1, 4) =~= h + seq![]);
}

/// Reassembles handshake messages from CRYPTO data; the view is the buffered bytes.
pub struct HsReader {
    buf: Vec<u8>,
}

impl View for HsReader {
    type V = Seq<u8>;

    closed spec fn view(&self) -> Seq<u8> {
        self.buf@
    }
}

impl HsReader {
    pub fn new() -> (r: HsReader)
        ensures
            r@ == Seq::<u8>::empty(),
    {
        HsReader { buf: Vec::new() }
    }

    pub fn push(&mut self, data: &[u8])
        ensures
            final(self)@ == old(self)@ + data@,
    {
        let n = data.len();
        let mut i: usize = 0;
        while i < n
            invariant
                n == data@.len(),
                i <= n,
                self@ == old(self)@ + data@.take(i as int),
            decreases n - i,
        {
            self.buf.push(data[i]);
            assert(data@.take(i as int + 1) =~= data@.take(i as int).push(data@[i as int]));
            assert((old(self)@ + data@.take(i as int)).push(data@[i as int]) =~= old(self)@
                + data@.take(i as int + 1));
            i += 1;
        }
        assert(data@.take(n as int) =~= data@);
    }

    pub fn is_empty(&self) -> (r: bool)
        ensures
            r == (self@.len() == 0),
    {
        self.buf.len() == 0
    }

    /// Removes and returns the first complete message, header included (what the transcript
    /// hashes, RFC 8446 §4.4.1). On `Ok(None)` or `Err` nothing is consumed.
    pub fn next_message(&mut self, expect: u8) -> (r: Result<Option<Vec<u8>>, u64>)
        ensures
            match rfc_next_message(old(self)@, expect) {
                Ok(Some(n)) => r matches Ok(Some(m)) && m@ == old(self)@.take(n as int)
                    && final(self)@ == old(self)@.skip(n as int),
                Ok(None) => r matches Ok(None) && final(self)@ == old(self)@,
                Err(e) => r matches Err(x) && x == e && final(self)@ == old(self)@,
            },
    {
        let have = self.buf.len();
        if have == 0 {
            return Ok(None);
        }
        //= https://www.rfc-editor.org/rfc/rfc8446#section-4
        //# A peer which receives a
        //# handshake message in an unexpected order MUST abort the handshake
        //# with an "unexpected_message" alert.
        if self.buf[0] != expect {
            return Err(ALERT_UNEXPECTED_MESSAGE);
        }
        if have < 4 {
            return Ok(None);
        }
        let len = self.buf[1] as usize * 65536 + self.buf[2] as usize * 256 + self.buf[3] as usize;
        assert(len == be(self@.subrange(1, 4), 3));
        if len > MAX_HS_BODY {
            return Err(CRYPTO_BUFFER_EXCEEDED);
        }
        if have - 4 < len {
            return Ok(None);
        }
        // ponytail: drains from the front of a Vec (O(n) per message); a ring buffer if handshakes grow.
        let mut msg = self.buf.split_off(4 + len);
        core::mem::swap(&mut msg, &mut self.buf);
        Ok(Some(msg))
    }
}

} // verus!
