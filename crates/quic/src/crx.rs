//! `Connection`'s CRYPTO-stream invariant (`crx_ok`), kept apart so its leave-Open lemma can be a broadcast in `conn`
//! (a module may not broadcast its own lemma over an opaque fn it reveals).
use vstd::prelude::*;
#[allow(unused_imports)]
use crate::crypto_stream::*;

verus! {

/// The three CRYPTO streams' `wf`, and a stream whose space is not live is drained. Opaque, so a
/// fn that changes neither a CRYPTO stream nor `live_i`, `live_h`, `complete` carries it by field
/// congruence; the fns that do (`on_crypto_frame`, `crypto_read`, `crypto_drop`, `discard`,
/// `on_handshake_complete`, `crypto_end`'s proof, the constructor) reveal it. D6's slot rule: a level
/// that still takes CRYPTO frames (`open`, the connection Open, and the level live) has an empty slot, and a
/// non-empty slot means an empty store, so a store retires onto a full slot only empty. Leaving Open keeps it
/// (`lemma_crx_ok_closed`, a broadcast in `conn`).
#[verifier::opaque]
pub(crate) open spec fn crx_ok(i: CryptoStream, h: CryptoStream, o: CryptoStream, live_i: bool, live_h: bool, complete: bool, open: bool) -> bool {
    &&& i.wf() && h.wf() && o.wf()
    &&& !live_i ==> i.drained() && i.buf_len_spec() == 0
    &&& !live_h ==> h.drained()
    &&& !complete ==> o.drained()
    &&& open ==> (live_i ==> i.td_nodes() == 0) && (live_h ==> h.td_nodes() == 0) && o.td_nodes() == 0
    &&& i.td_nodes() > 0 ==> i.held_spec() == 0
    &&& h.td_nodes() > 0 ==> h.held_spec() == 0
    &&& o.td_nodes() > 0 ==> o.held_spec() == 0
}

/// `crx_ok` survives leaving Open: its `open` clause only weakens.
pub(crate) broadcast proof fn lemma_crx_ok_closed(
    i: CryptoStream,
    h: CryptoStream,
    o: CryptoStream,
    live_i: bool,
    live_h: bool,
    complete: bool,
)
    ensures
        crx_ok(i, h, o, live_i, live_h, complete, true) ==> #[trigger] crx_ok(i, h, o, live_i, live_h, complete, false),
{
    reveal(crx_ok);
}

} // verus!
