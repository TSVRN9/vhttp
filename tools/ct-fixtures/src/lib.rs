//! Constant-time checker fixtures, built only by `scripts/ct-check.sh` under ct-driver. Every
//! `fx::` fn below except the `helper_*` ones is a root in `manifest.txt`. Positive controls
//! must get `ok`; each negative control must be rejected with its stated kind (the comment
//! after it) among the reported kinds. `expected.txt` holds the verdicts.

/// The shims at the paths the manifest loader accepts: `<crate>::ct::declassify` and `ct_fixtures::ct::ghost_fallback`.
pub mod ct {
    /// Mapped to `Declassify`.
    pub fn declassify<T>(x: T) -> T {
        x
    }

    /// Mapped to `GhostUnit`: the erased `Ghost(..)` argument shape of vstd's
    /// `Ghost::assume_new_fallback(|| unreachable!())`.
    pub fn ghost_fallback<T>(_f: fn() -> T) {}
}

/// The fixtures. They are not at the crate root, where `ct::secret` would resolve to the `ct`
/// module (E0433 under `--cfg ct_check`).
pub mod fx {
    // ------------------------------------------------------------------ helpers (not roots)

    #[cfg_attr(ct_check, ct::secret(x))]
    pub fn helper_secret(x: u8) -> u8 {
        x ^ 0x5a
    }

    #[cfg_attr(ct_check, ct::secret(x))]
    pub fn helper_chain(x: u8) -> u8 {
        helper_secret(x) ^ 1
    }

    pub fn helper_unlabeled(x: u8) -> u8 {
        x ^ 1
    }

    pub fn helper_mut_unlabeled(buf: &mut [u8; 16]) {
        buf[0] = 1;
    }

    #[cfg_attr(ct_check, ct::secret(buf, k))]
    pub fn helper_update(buf: &mut [u8; 16], k: u8) {
        buf[0] ^= k;
    }

    // ------------------------------------------------------------------ positive controls

    #[cfg_attr(ct_check, ct::secret(bit, a, b))]
    pub fn pos_masked_select(bit: u8, a: u8, b: u8) -> u8 {
        let m = (bit & 1) * 0xff;
        (a & m) | (b & !m)
    }

    #[cfg_attr(ct_check, ct::secret(k))]
    pub fn pos_public_loop_over_secret_array(k: &[u8; 16]) -> u8 {
        let mut acc = 0u8;
        let mut i = 0usize;
        while i < 16 {
            acc ^= k[i];
            i += 1;
        }
        acc
    }

    #[cfg_attr(ct_check, ct::secret(k))]
    pub fn pos_len_of_secret_slice(k: &[u8]) -> usize {
        k.len()
    }

    #[cfg_attr(ct_check, ct::secret(k))]
    pub fn pos_declassified_branch(k: &[u8; 16]) -> u8 {
        if crate::ct::declassify(k[0]) == 7 {
            k[1] ^ 3
        } else {
            k[2] | 5
        }
    }

    #[cfg_attr(ct_check, ct::secret(k))]
    pub fn pos_call_chain(k: &[u8; 16]) -> u8 {
        helper_chain(k[3])
    }

    #[cfg_attr(ct_check, ct::secret(k))]
    pub fn pos_mut_param_update(k: &[u8; 16]) -> u8 {
        let mut buf = [0u8; 16];
        helper_update(&mut buf, k[1]);
        buf[0]
    }

    #[cfg_attr(ct_check, ct::secret(bit, a, b))]
    pub fn pos_u128_mul_mask(bit: u128, a: u128, b: u128) -> u128 {
        let m = (bit & 1) * u128::MAX;
        (a & m) | (b & !m)
    }

    #[cfg_attr(ct_check, ct::secret(k))]
    pub fn pos_ghost_arg(k: &[u8; 16]) -> u8 {
        crate::ct::ghost_fallback(|| 0u8);
        k[0] ^ 1
    }

    /// Labelled by a manifest `label` line instead of an attribute.
    pub fn pos_label_line(k: u8, n: u8) -> u8 {
        k ^ n
    }

    #[cfg_attr(ct_check, ct::public)]
    pub fn pos_bare_public(x: u32) -> u32 {
        if x > 3 {
            x ^ 5
        } else {
            x | 9
        }
    }

    // ------------------------------------------------------------------ negative controls

    #[cfg_attr(ct_check, ct::secret(k))]
    pub fn neg_secret_if(k: &[u8; 16]) -> u8 {
        // SecretSwitch
        if k[0] == 7 {
            k[1] ^ 3
        } else {
            k[2] | 5
        }
    }

    #[cfg_attr(ct_check, ct::secret(s))]
    pub fn neg_secret_match(s: u8) -> u8 {
        // SecretSwitch
        match s {
            0 => 11,
            1 => 22,
            5 => 33,
            _ => 44,
        }
    }

    #[cfg_attr(ct_check, ct::secret(k), ct::public(p))]
    pub fn neg_secret_and_and(k: &[u8; 16], p: u8) -> u8 {
        // SecretSwitch (on the rhs of the short circuit)
        if p == 1 && k[0] == 2 {
            p ^ 3
        } else {
            p | 5
        }
    }

    #[cfg_attr(ct_check, ct::secret(k), ct::public(p))]
    pub fn neg_secret_early_return(p: u8, k: u8) -> u8 {
        // SecretSwitch. The secret is the second param but listed first.
        if k == 0 {
            return p ^ 1;
        }
        p | 6
    }

    #[cfg_attr(ct_check, ct::secret(k))]
    pub fn neg_secret_while(k: u8) -> u8 {
        // SecretSwitch
        let mut x = k;
        let mut n = 0u8;
        while x > 0 {
            x >>= 1;
            n += 1;
        }
        n
    }

    #[cfg_attr(ct_check, ct::secret(i), ct::public(t))]
    pub fn neg_secret_index(t: &[u8; 16], i: usize) -> u8 {
        // SecretIndex, and SecretAssert from the bounds check on the same index
        t[i]
    }

    #[cfg_attr(ct_check, ct::secret(d), ct::public(n))]
    pub fn neg_secret_div(n: u32, d: u32) -> u32 {
        // SecretDivOperand, and SecretAssert from the divide-by-zero check
        n / d
    }

    #[cfg_attr(ct_check, ct::secret(x))]
    pub fn neg_secret_rem_u128(x: u128) -> u128 {
        // SecretDivOperand (secret dividend, constant divisor)
        x % 1_000_003
    }

    #[cfg_attr(ct_check, ct::secret(s), ct::public(x))]
    pub fn neg_secret_shift(x: u32, s: u32) -> u32 {
        // SecretShift
        x << s
    }

    #[cfg_attr(ct_check, ct::secret(k))]
    pub fn neg_secret_to_unlabeled_helper(k: &[u8; 16]) -> u8 {
        // ArgLabel
        helper_unlabeled(k[0])
    }

    #[cfg_attr(ct_check, ct::public(x))]
    pub fn neg_unresolved_callee(x: u64) -> u32 {
        // Unresolved: no manifest line maps u64::count_ones
        x.count_ones()
    }

    #[cfg_attr(ct_check, ct::secret(z))]
    pub fn neg_unknown_param_name(k: u8) -> u8 {
        // Attr
        k
    }

    #[cfg_attr(ct_check, ct::secret(a))]
    pub fn neg_missing_param_name(a: u8, b: u8) -> u8 {
        // Attr
        a ^ b
    }

    #[cfg_attr(ct_check, ct::secret(a), ct::public(a))]
    pub fn neg_duplicate_param_name(a: u8) -> u8 {
        // Attr
        a
    }

    #[cfg_attr(ct_check, ct::secrett(k))]
    pub fn neg_unknown_attr(k: u8) -> u8 {
        // Attr
        k
    }

    pub fn neg_root_without_label(k: u8) -> u8 {
        // Root
        k
    }

    /// Labelled by a manifest `label` line that does not name `b`.
    pub fn neg_label_line_missing_param(a: u8, b: u8) -> u8 {
        // Attr
        a ^ b
    }

    #[cfg_attr(ct_check, ct::secret(x))]
    pub fn neg_float(x: f32) -> f32 {
        // Unsupported
        x * 2.0
    }

    #[cfg_attr(ct_check, ct::public(p))]
    pub fn neg_raw_pointer(p: *const u8) -> usize {
        // Unsupported
        p as usize
    }

    #[cfg_attr(ct_check, ct::public(v, x))]
    pub fn neg_intr_type_args(v: &mut Vec<u64>, x: u64) {
        // Unsupported: `Vec::push` is keyed without its type args, and its `intr` line is
        // declared at u8 (the census); this call reaches it at u64
        v.push(x)
    }

    #[cfg_attr(ct_check, ct::secret(k))]
    pub fn neg_mut_param_label(k: &[u8; 16]) -> u8 {
        // ArgLabel and MutLabel: a secret buffer passed as an unlabeled (public) `&mut` param
        let mut b = *k;
        helper_mut_unlabeled(&mut b);
        b[0]
    }

    #[cfg_attr(ct_check, ct::public(c))]
    pub fn neg_char(c: char) -> u32 {
        // Unsupported
        c as u32
    }

    #[cfg_attr(ct_check, ct::public(b))]
    pub fn neg_box(b: Box<u8>) -> u8 {
        // Unsupported
        *b
    }

    #[cfg_attr(ct_check, ct::public(d))]
    pub fn neg_dyn(d: &dyn core::fmt::Debug) -> u8 {
        // Unsupported
        let _ = d;
        1
    }

    #[cfg_attr(ct_check, ct::public(f, x))]
    pub fn neg_fn_pointer_call(f: fn(u8) -> u8, x: u8) -> u8 {
        // Unsupported
        f(x)
    }

    #[cfg_attr(ct_check, ct::public(x))]
    pub fn neg_closure_call(x: u8) -> u8 {
        // Unsupported
        let f = |y: u8| y ^ 1;
        f(x)
    }

    #[cfg_attr(ct_check, ct::public(v))]
    pub fn neg_drop_non_vec(v: Vec<Vec<u8>>) -> u8 {
        // Unsupported: the drop glue of Vec<Vec<u8>> frees more than one Vec<int> buffer
        let _ = &v;
        1
    }

    #[cfg_attr(ct_check, ct::public(c))]
    pub fn neg_interior_mut(c: &core::cell::Cell<u8>) -> u8 {
        // Unsupported
        let _ = c;
        1
    }

    // ------------------------------------------------------------------ ambiguous keys
    // `ct_key` strips generic args, so `W::<u32>::f` and `W::<u64>::f` (two defs) and
    // `id::<u32>`/`id::<u64>` (one def, two instances) each share one key.

    pub struct W<T>(pub T);

    impl W<u32> {
        pub fn f(x: u32) -> u32 {
            x ^ 1
        }

        #[cfg_attr(ct_check, ct::public(x))]
        pub fn g(x: u32) -> u32 {
            x
        }

        pub fn h(x: u32) -> u32 {
            x ^ 3
        }
    }

    impl W<u64> {
        pub fn f(x: u64) -> u64 {
            x ^ 2
        }

        #[cfg_attr(ct_check, ct::public(x))]
        pub fn g(x: u64) -> u64 {
            x
        }

        pub fn h(x: u64) -> u64 {
            x ^ 4
        }
    }

    pub fn id<T>(x: T) -> T {
        x
    }

    #[cfg_attr(ct_check, ct::public(x))]
    pub fn neg_ambiguous_callee(x: u32) -> u64 {
        // Unsupported: two defs reached under the key ct_fixtures::fx::W::f
        W::<u32>::f(x) as u64 ^ W::<u64>::f(x as u64)
    }

    #[cfg_attr(ct_check, ct::public(a, b))]
    pub fn neg_ambiguous_generic(a: u32, b: u64) -> u64 {
        // Unsupported: two instances of `id` reached under one key
        id(a) as u64 ^ id(b)
    }

    #[cfg_attr(ct_check, ct::public(x))]
    pub fn pos_key_first_root(x: u32) -> u32 {
        // binds ct_fixtures::fx::W::h to W::<u32>::h for this crate
        W::<u32>::h(x)
    }

    #[cfg_attr(ct_check, ct::public(x))]
    pub fn neg_key_second_root(x: u64) -> u64 {
        // Unsupported: a later root reaches W::<u64>::h under the key the first root bound
        W::<u64>::h(x)
    }

    #[derive(Clone, Copy)]
    pub enum Discr {
        A = 3,
        B = 7,
    }

    #[cfg_attr(ct_check, ct::public(d))]
    pub fn neg_enum_discriminant(d: Discr) -> u8 {
        // Unsupported: core `Discr` reads variant indices, not discriminant values
        match d {
            Discr::A => 1,
            Discr::B => 2,
        }
    }

    // ------------------------------------------------------------------ 8b translator coverage

    #[cfg_attr(ct_check, ct::public(x))]
    pub fn pos_str_unit(x: u8) -> Option<&'static str> {
        // `&'static str` is an opaque `Unit`
        if x == 0 {
            Some("e")
        } else {
            None
        }
    }

    #[cfg_attr(ct_check, ct::public)]
    pub fn neg_str_len(s: &str) -> usize {
        // Unresolved: `str::len` has no intr line, so no read of a `str` translates
        s.len()
    }

    #[cfg_attr(ct_check, ct::public(v, i))]
    pub fn pos_vec_elem_pair(v: &Vec<(u64, u64)>, i: usize) -> u64 {
        // VecLen and VecIndex at element (u64, u64)
        if i < v.len() {
            v[i].0
        } else {
            0
        }
    }

    pub struct TwoVecs {
        pub a: Vec<u8>,
        pub b: Vec<u8>,
    }

    #[cfg_attr(ct_check, ct::public(o, t))]
    pub fn pos_drop_bounded(o: Option<Vec<u8>>, t: TwoVecs) -> u8 {
        // drop glue that frees at most three Vec<u8> buffers
        let _ = (&o, &t);
        1
    }

    pub struct WithDrop {
        pub v: Vec<u8>,
    }

    impl Drop for WithDrop {
        fn drop(&mut self) {}
    }

    #[cfg_attr(ct_check, ct::public(w))]
    pub fn neg_drop_user_impl(w: WithDrop) -> u8 {
        // Unsupported: the drop glue runs `<WithDrop as Drop>::drop`
        let _ = &w;
        1
    }

    #[cfg_attr(ct_check, ct::public(x))]
    pub fn pos_const_direct_tag(x: u8) -> Option<u64> {
        // allocated constants of a Direct-tag enum
        if x == 0 {
            Some(5)
        } else {
            None
        }
    }

    pub enum Code {
        Conn(u64),
        Stream(u64),
    }

    #[cfg_attr(ct_check, ct::public(x))]
    pub fn pos_const_niche(x: u8) -> Option<Code> {
        // allocated constants of an enum niche-encoded in `Code`'s tag
        if x == 0 {
            Some(Code::Stream(7))
        } else {
            None
        }
    }

    pub struct Zst;

    impl Zst {
        pub fn get(&self, x: u8) -> u8 {
            x ^ 1
        }
    }

    #[cfg_attr(ct_check, ct::public(x))]
    pub fn pos_const_ref_zst(x: u8) -> u8 {
        // a constant `&Zst` method receiver
        Zst.get(x)
    }

    pub struct Pair {
        pub a: u8,
        pub b: u64,
    }

    pub fn helper_pair(p: &Pair) -> u64 {
        p.b ^ p.a as u64
    }

    #[cfg_attr(ct_check, ct::public)]
    pub fn neg_const_ref_non_zst() -> u64 {
        // Unsupported: a constant `&Pair` (a pointer to non-zero-sized data)
        helper_pair(&Pair { a: 1, b: 2 })
    }
}
