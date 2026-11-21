//! A fixed-capacity FIFO of stream ids (9b2 D13): the receiving parts with STREAM bytes or a FIN
//! left to deliver and the sending parts with a non-empty teardown slot (D10 (e)), so `backlog_step`
//! pops one without scanning the streams. `IDQ_CAP` slots in
//! one exact `CapVec`, filled on first use and then reused in a ring; push and pop are O(1).
use byteq::capvec::CapVec;
use vstd::prelude::*;

verus! {

/// The slots: one per stream that can have an entry, 100 peer bidirectional, 100 peer unidirectional and our 3
/// unidirectional (`max_entries()`, `2 * MAX_LOCAL_STREAMS + MAX_OWN_UNI`, streams.rs): every queued id is a live
/// entry's (`Streams::wf`'s `qinv`).
pub const IDQ_CAP: usize = 203;

pub struct IdQueue {
    q: CapVec<u64>,
    head: usize,
    len: usize,
}

impl IdQueue {
    /// The ids queued, oldest first.
    pub closed spec fn view(&self) -> Seq<u64> {
        Seq::new(
            self.len as nat,
            |k: int|
                self.q@[if self.head + k >= IDQ_CAP {
                    self.head + k - IDQ_CAP
                } else {
                    self.head + k
                }],
        )
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.q.wf()
        &&& self.q.cap() == IDQ_CAP
        &&& self.q@.len() <= IDQ_CAP
        &&& self.len <= IDQ_CAP
        &&& self.head < IDQ_CAP
        // Until every slot was used once, the queue sits in `[head, head + len)` with nothing past it.
        &&& self.q@.len() < IDQ_CAP ==> self.head + self.len == self.q@.len()
    }

    pub proof fn lemma_len(&self)
        requires
            self.wf(),
        ensures
            self@.len() <= IDQ_CAP,
    {
    }

    /// An empty queue; its slots are allocated here, once per connection.
    pub fn new() -> (r: IdQueue)
        ensures
            r.wf(),
            r@ == Seq::<u64>::empty(),
    {
        let r = IdQueue { q: CapVec::new(IDQ_CAP), head: 0, len: 0 };
        proof {
            assert(r@ =~= Seq::<u64>::empty());
        }
        r
    }

    pub fn len(&self) -> (r: usize)
        requires
            self.wf(),
        ensures
            r == self@.len(),
            r <= IDQ_CAP,
    {
        self.len
    }

    /// Appends `id`. O(1).
    pub fn push(&mut self, id: u64)
        requires
            old(self).wf(),
            old(self)@.len() < IDQ_CAP,
        ensures
            final(self).wf(),
            final(self)@ == old(self)@.push(id),
    {
        let t = if self.head + self.len >= IDQ_CAP {
            self.head + self.len - IDQ_CAP
        } else {
            self.head + self.len
        };
        if t < self.q.len() {
            self.q.set(t, id);
        } else {
            self.q.push(id);
        }
        self.len = self.len + 1;
        proof {
            assert(self@ =~= old(self)@.push(id));
        }
    }

    /// The oldest id, if any. O(1).
    pub fn front(&self) -> (r: Option<u64>)
        requires
            self.wf(),
        ensures
            self@.len() == 0 ==> r is None,
            self@.len() > 0 ==> r == Some(self@[0]),
    {
        if self.len == 0 {
            None
        } else {
            Some(*self.q.index(self.head))
        }
    }

    /// Removes and returns the oldest id, if any. O(1).
    pub fn pop(&mut self) -> (r: Option<u64>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            old(self)@.len() == 0 ==> r is None && final(self)@ == old(self)@,
            old(self)@.len() > 0 ==> r == Some(old(self)@[0]) && final(self)@ == old(self)@.drop_first(),
    {
        if self.len == 0 {
            return None;
        }
        let id = *self.q.index(self.head);
        self.head = if self.head + 1 >= IDQ_CAP {
            0
        } else {
            self.head + 1
        };
        self.len = self.len - 1;
        proof {
            assert(self@ =~= old(self)@.drop_first());
        }
        Some(id)
    }
}

} // verus!
