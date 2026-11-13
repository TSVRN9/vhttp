//! `CapVec<T>`: a `Vec` with a ghost capacity, the exact `Vec::with_capacity` argument, and every push proved below
//! it. std guarantees a push below the capacity never reallocates (TRUSTED.md's Vec row); this module is the one
//! place that guarantee is used. The ghost field takes no space: a `CapVec<T>` is a `Vec<T>` in memory.
use vstd::prelude::*;

verus! {

pub struct CapVec<T> {
    v: Vec<T>,
    /// Only spec fns read it, which a plain `cargo build` erases.
    #[allow(dead_code)]
    cap: Ghost<nat>,
}

impl<T> View for CapVec<T> {
    type V = Seq<T>;

    closed spec fn view(&self) -> Seq<T> {
        self.v@
    }
}

impl<T> CapVec<T> {
    /// The capacity `new` was given.
    pub closed spec fn cap(&self) -> nat {
        self.cap@
    }

    pub closed spec fn wf(&self) -> bool {
        self.v@.len() <= self.cap@
    }

    pub proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            self@.len() <= self.cap(),
    {
    }

    /// `Vec::with_capacity(c)`.
    pub fn new(c: usize) -> (r: CapVec<T>)
        ensures
            r.wf(),
            r@ == Seq::<T>::empty(),
            r.cap() == c,
    {
        CapVec { v: Vec::with_capacity(c), cap: Ghost(c as nat) }
    }

    /// The only push into `v`: below the capacity, so it never reallocates.
    pub fn push(&mut self, x: T)
        requires
            old(self).wf(),
            old(self)@.len() < old(self).cap(),
        ensures
            final(self).wf(),
            final(self)@ == old(self)@.push(x),
            final(self).cap() == old(self).cap(),
    {
        self.v.push(x);
    }

    /// An in-place write.
    pub fn set(&mut self, i: usize, x: T)
        requires
            old(self).wf(),
            i < old(self)@.len(),
        ensures
            final(self).wf(),
            final(self)@ == old(self)@.update(i as int, x),
            final(self).cap() == old(self).cap(),
    {
        self.v.set(i, x);
    }

    pub fn index(&self, i: usize) -> (r: &T)
        requires
            i < self@.len(),
        ensures
            *r == self@[i as int],
    {
        &self.v[i]
    }

    pub fn len(&self) -> (r: usize)
        ensures
            r == self@.len(),
    {
        self.v.len()
    }

    pub fn as_slice(&self) -> (r: &[T])
        ensures
            r@ == self@,
    {
        self.v.as_slice()
    }

    /// The guarantee ends here: the `Vec` is only read or moved afterwards.
    pub fn into_vec(self) -> (r: Vec<T>)
        ensures
            r@ == self@,
    {
        self.v
    }
}

impl CapVec<u8> {
    /// `s.len()` counted pushes; costs one unit per byte.
    pub fn push_slice(&mut self, s: &[u8]) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            old(self)@.len() + s@.len() <= old(self).cap(),
        ensures
            final(self).wf(),
            final(self)@ == old(self)@ + s@,
            final(self).cap() == old(self).cap(),
            r@ == s@.len(),
    {
        let ghost mut work: nat = 0;
        let mut i: usize = 0;
        while i < s.len()
            invariant
                self.wf(),
                self.cap() == old(self).cap(),
                old(self)@.len() + s@.len() <= self.cap(),
                i <= s@.len(),
                self@ == old(self)@ + s@.subrange(0, i as int),
                work == i,
            decreases s@.len() - i,
        {
            self.push(s[i]);
            proof {
                assert(s@.subrange(0, i + 1) == s@.subrange(0, i as int).push(s@[i as int]));
                assert(old(self)@ + s@.subrange(0, i + 1) =~= (old(self)@ + s@.subrange(0, i as int)).push(
                    s@[i as int],
                ));
            }
            i = i + 1;
            proof {
                work = work + 1;
            }
        }
        assert(s@.subrange(0, s@.len() as int) =~= s@);
        Ghost(work)
    }
}

} // verus!

impl<T> CapVec<T> {
    /// Test support: the allocated capacity. Verus models `Vec` length, not capacity (TRUSTED.md).
    #[doc(hidden)]
    pub fn capacity(&self) -> usize {
        self.v.capacity()
    }
}
