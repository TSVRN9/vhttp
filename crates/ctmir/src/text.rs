//! The report's lines: their byte forms as specs, and the exec renderers proved equal to them.
//! A line is one text without `\n`, then `\n`. The `root .. ok` and `bounded ..` lines carry the
//! end-to-end theorems (`pipeline::report_sound`); `checked` names the labels the CT theorem is
//! stated with; `reject`, `none` and `declassify` lines are informational, with any `\n` in a
//! dump string turned into a space (`clean`), so no dump string can start a line of its own.
#[cfg(verus_keep_ghost)]
use crate::json::digits;
#[cfg(verus_keep_ghost)]
use crate::rel::views;
use ctcore::cost::{Atom, Mono, Poly};
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ bytes

/// `parts` joined by `sep`.
pub open spec fn join(parts: Seq<Seq<u8>>, sep: Seq<u8>) -> Seq<u8>
    decreases parts.len(),
{
    if parts.len() == 0 { seq![] }
    else if parts.len() == 1 { parts[0] }
    else { join(parts.drop_last(), sep) + sep + parts.last() }
}

pub open spec fn no_nl(s: Seq<u8>) -> bool { forall|i: int| 0 <= i < s.len() ==> s[i] != 10u8 }

/// `s` with every `\n` a space.
pub open spec fn clean(s: Seq<u8>) -> Seq<u8> { s.map_values(|c: u8| if c == 10u8 { 32u8 } else { c }) }

/// `out` += `s`.
pub fn put(out: &mut Vec<u8>, s: &[u8])
    ensures final(out)@ == old(out)@ + s@,
{
    let ghost o = out@;
    let mut i: usize = 0;
    while i < s.len()
        invariant i <= s@.len(), out@ == o + s@.subrange(0, i as int),
        decreases s.len() - i,
    {
        out.push(s[i]);
        i += 1;
        proof { assert(out@ =~= o + s@.subrange(0, i as int)); }
    }
    proof { assert(s@.subrange(0, s@.len() as int) =~= s@); }
}

/// `out` += `clean(s)`.
pub fn put_clean(out: &mut Vec<u8>, s: &[u8])
    ensures final(out)@ == old(out)@ + clean(s@),
{
    let ghost o = out@;
    let mut i: usize = 0;
    while i < s.len()
        invariant i <= s@.len(), out@ == o + clean(s@.subrange(0, i as int)),
        decreases s.len() - i,
    {
        out.push(if s[i] == 10u8 { 32u8 } else { s[i] });
        i += 1;
        proof { assert(out@ =~= o + clean(s@.subrange(0, i as int))); }
    }
    proof { assert(s@.subrange(0, s@.len() as int) =~= s@); }
}

/// Whether `s` holds a `\n`.
pub fn has_nl(s: &[u8]) -> (r: bool)
    ensures r == !no_nl(s@),
{
    let mut i: usize = 0;
    while i < s.len()
        invariant i <= s@.len(), forall|k: int| 0 <= k < i ==> s@[k] != 10u8,
        decreases s.len() - i,
    {
        if s[i] == 10u8 { return true; }
        i += 1;
    }
    false
}

pub proof fn lemma_clean_no_nl(s: Seq<u8>)
    ensures no_nl(clean(s)),
{}

/// `n` in decimal.
pub fn dec(n: u64) -> (r: Vec<u8>)
    ensures r@ == digits(n as nat),
    decreases n,
{
    if n < 10 {
        let mut v = Vec::new();
        v.push(48u8 + n as u8);
        proof { assert(v@ =~= digits(n as nat)); }
        v
    } else {
        let mut v = dec(n / 10);
        v.push(48u8 + (n % 10) as u8);
        proof { assert(v@ =~= digits(n as nat)); }
        v
    }
}

/// `parts` joined by `sep`.
pub fn join_exec(parts: &Vec<Vec<u8>>, sep: &[u8]) -> (r: Vec<u8>)
    ensures r@ == join(views(parts@), sep@),
{
    let ghost ps = views(parts@);
    let mut out: Vec<u8> = Vec::new();
    let mut k: usize = 0;
    while k < parts.len()
        invariant k <= parts@.len(), ps == views(parts@), out@ == join(ps.subrange(0, k as int), sep@),
        decreases parts.len() - k,
    {
        proof { assert(ps.subrange(0, k + 1).drop_last() =~= ps.subrange(0, k as int)); }
        if k > 0 { put(&mut out, sep); }
        put(&mut out, parts[k].as_slice());
        k += 1;
        proof { if k == 1 { assert(join(ps.subrange(0, 1), sep@) == ps[0]); } }
    }
    proof { assert(ps.subrange(0, parts@.len() as int) =~= ps); }
    out
}

// ------------------------------------------------------------------ step bounds

/// Local `x` in the root's parameter names: parameter `x - 1`'s name, `#x` if it has none, `_x`
/// if `x` is not a parameter.
pub open spec fn local_text(names: Seq<Seq<u8>>, x: nat) -> Seq<u8> {
    if 1 <= x && x - 1 < names.len() {
        if names[x - 1].len() > 0 { names[x - 1] } else { b"#"@ + digits(x) }
    } else { b"_"@ + digits(x) }
}

/// `Val` is the parameter's name, `Len` is `len(name)`, `Gap` is `sat(a - b)`, the saturating
/// difference.
pub open spec fn atom_text_spec(a: Atom, names: Seq<Seq<u8>>) -> Seq<u8>
    decreases a,
{
    match a {
        Atom::Const(c) => digits(c as nat),
        Atom::Val(x, _) => local_text(names, x as nat),
        Atom::Len(x) => b"len("@ + local_text(names, x as nat) + b")"@,
        Atom::Gap(x, y) => b"sat("@ + atom_text_spec(*x, names) + b" - "@ + atom_text_spec(*y, names) + b")"@,
    }
}

pub open spec fn atom_parts(atoms: Seq<Atom>, names: Seq<Seq<u8>>) -> Seq<Seq<u8>> {
    atoms.map_values(|a: Atom| atom_text_spec(a, names))
}

/// A monomial: `c*a*b`, with the coefficient left out when it is 1 and there are atoms.
pub open spec fn mono_text(mo: Mono, names: Seq<Seq<u8>>) -> Seq<u8> {
    let at = join(atom_parts(mo.atoms@, names), b"*"@);
    if mo.atoms@.len() == 0 { digits(mo.coef as nat) }
    else if mo.coef == 1 { at }
    else { digits(mo.coef as nat) + b"*"@ + at }
}

/// The nonzero monomials' texts, in order.
pub open spec fn mono_parts(ms: Seq<Mono>, names: Seq<Seq<u8>>) -> Seq<Seq<u8>>
    decreases ms.len(),
{
    if ms.len() == 0 { seq![] } else {
        mono_parts(ms.drop_last(), names) + if ms.last().coef != 0 { seq![mono_text(ms.last(), names)] } else { Seq::<Seq<u8>>::empty() }
    }
}

/// A summary in the root's parameter names: `13*len(s)*len(s) + 40*len(s) + 33`, or `0`.
pub open spec fn poly_text_spec(p: Poly, names: Seq<Seq<u8>>) -> Seq<u8> {
    let parts = mono_parts(p.monos@, names);
    if parts.len() == 0 { b"0"@ } else { join(parts, b" + "@) }
}

/// The most atoms of a nonzero monomial (0 if there is none).
pub open spec fn deg_of(ms: Seq<Mono>) -> nat
    decreases ms.len(),
{
    if ms.len() == 0 { 0 } else {
        let d = deg_of(ms.drop_last());
        if ms.last().coef != 0 && ms.last().atoms@.len() > d { ms.last().atoms@.len() } else { d }
    }
}

pub open spec fn deg_spec(p: Poly) -> nat { deg_of(p.monos@) }

pub fn local_text_exec(names: &Vec<Vec<u8>>, x: usize) -> (r: Vec<u8>)
    ensures r@ == local_text(views(names@), x as nat),
{
    let ghost ns = views(names@);
    let mut out: Vec<u8> = Vec::new();
    if 1 <= x && x - 1 < names.len() {
        if names[x - 1].len() > 0 { put(&mut out, names[x - 1].as_slice()); return out; }
        put(&mut out, b"#");
    } else {
        put(&mut out, b"_");
    }
    let d = dec(x as u64);
    put(&mut out, d.as_slice());
    proof { assert(out@ =~= local_text(ns, x as nat)); }
    out
}

pub fn atom_text(a: &Atom, names: &Vec<Vec<u8>>) -> (r: Vec<u8>)
    ensures r@ == atom_text_spec(*a, views(names@)),
    decreases a,
{
    match a {
        Atom::Const(c) => dec(*c),
        Atom::Val(x, _) => local_text_exec(names, *x),
        Atom::Len(x) => {
            let mut out = Vec::new();
            put(&mut out, b"len(");
            let t = local_text_exec(names, *x);
            put(&mut out, t.as_slice());
            put(&mut out, b")");
            out
        },
        Atom::Gap(x, y) => {
            let mut out = Vec::new();
            put(&mut out, b"sat(");
            let t = atom_text(x, names);
            put(&mut out, t.as_slice());
            put(&mut out, b" - ");
            let u = atom_text(y, names);
            put(&mut out, u.as_slice());
            put(&mut out, b")");
            out
        },
    }
}

pub fn mono_text_exec(mo: &Mono, names: &Vec<Vec<u8>>) -> (r: Vec<u8>)
    ensures r@ == mono_text(*mo, views(names@)),
{
    let ghost ns = views(names@);
    let mut parts: Vec<Vec<u8>> = Vec::new();
    let mut k: usize = 0;
    while k < mo.atoms.len()
        invariant k <= mo.atoms@.len(), ns == views(names@),
            views(parts@) =~= atom_parts(mo.atoms@.subrange(0, k as int), ns),
        decreases mo.atoms.len() - k,
    {
        let t = atom_text(&mo.atoms[k], names);
        let ghost p0 = parts@;
        parts.push(t);
        proof {
            assert(views(parts@) =~= views(p0).push(t@));
            assert(atom_parts(mo.atoms@.subrange(0, k + 1), ns) =~= atom_parts(mo.atoms@.subrange(0, k as int), ns).push(atom_text_spec(mo.atoms@[k as int], ns)));
        }
        k += 1;
    }
    proof { assert(mo.atoms@.subrange(0, mo.atoms@.len() as int) =~= mo.atoms@); }
    let at = join_exec(&parts, b"*");
    if mo.atoms.len() == 0 { dec(mo.coef) }
    else if mo.coef == 1 { at }
    else {
        let mut out = dec(mo.coef);
        put(&mut out, b"*");
        put(&mut out, at.as_slice());
        out
    }
}

/// The text of a `bounded` line's bound.
pub fn poly_text(p: &Poly, names: &Vec<Vec<u8>>) -> (r: Vec<u8>)
    ensures r@ == poly_text_spec(*p, views(names@)),
{
    let ghost ns = views(names@);
    let mut parts: Vec<Vec<u8>> = Vec::new();
    let mut k: usize = 0;
    while k < p.monos.len()
        invariant k <= p.monos@.len(), ns == views(names@),
            views(parts@) =~= mono_parts(p.monos@.subrange(0, k as int), ns),
        decreases p.monos.len() - k,
    {
        proof { assert(p.monos@.subrange(0, k + 1).drop_last() =~= p.monos@.subrange(0, k as int)); }
        if p.monos[k].coef != 0 {
            let t = mono_text_exec(&p.monos[k], names);
            parts.push(t);
        }
        k += 1;
        proof { assert(views(parts@) =~= mono_parts(p.monos@.subrange(0, k as int), ns)); }
    }
    proof { assert(p.monos@.subrange(0, p.monos@.len() as int) =~= p.monos@); }
    if parts.len() == 0 {
        let mut out = Vec::new();
        put(&mut out, b"0");
        proof { assert(out@ =~= b"0"@); }
        out
    } else { join_exec(&parts, b" + ") }
}

pub fn deg(p: &Poly) -> (r: u64)
    ensures r as nat == deg_spec(*p),
{
    let mut d: usize = 0;
    let mut k: usize = 0;
    while k < p.monos.len()
        invariant k <= p.monos@.len(), d as nat == deg_of(p.monos@.subrange(0, k as int)),
        decreases p.monos.len() - k,
    {
        proof { assert(p.monos@.subrange(0, k + 1).drop_last() =~= p.monos@.subrange(0, k as int)); }
        if p.monos[k].coef != 0 && p.monos[k].atoms.len() > d { d = p.monos[k].atoms.len(); }
        k += 1;
    }
    proof { assert(p.monos@.subrange(0, p.monos@.len() as int) =~= p.monos@); }
    d as u64
}

// ------------------------------------------------------------------ lines

pub open spec fn root_line(path: Seq<u8>) -> Seq<u8> { b"root "@ + path + b" ok"@ + seq![10u8] }

pub open spec fn bounded_line(path: Seq<u8>, d: nat, text: Seq<u8>) -> Seq<u8> {
    b"bounded "@ + path + b" deg="@ + digits(d) + b" steps <= "@ + text + seq![10u8]
}

/// Parameter `j`'s name (0-based), `#<j+1>` if it has none.
pub open spec fn param_text(names: Seq<Seq<u8>>, j: nat) -> Seq<u8> {
    if names[j as int].len() > 0 { names[j as int] } else { b"#"@ + digits(j + 1) }
}

/// The names of the first `n` parameters whose label is secret (`lab[1 + j]`).
pub open spec fn sec_parts(names: Seq<Seq<u8>>, lab: Seq<bool>, n: nat) -> Seq<Seq<u8>>
    decreases n,
{
    if n == 0 { seq![] } else {
        let j = (n - 1) as nat;
        sec_parts(names, lab, j) + if j + 1 < lab.len() && lab[(j + 1) as int] { seq![param_text(names, j)] } else { Seq::<Seq<u8>>::empty() }
    }
}

/// `checked <path> secret=<names> ret=<s|p>`: fn `path`'s labels, `lab` one per local.
pub open spec fn checked_line(path: Seq<u8>, names: Seq<Seq<u8>>, lab: Seq<bool>) -> Seq<u8> {
    b"checked "@ + path + b" secret="@ + join(sec_parts(names, lab, names.len()), b","@) + b" ret="@
        + (if lab.len() > 0 && lab[0] { b"s"@ } else { b"p"@ }) + seq![10u8]
}

pub fn checked_text(path: &Vec<u8>, names: &Vec<Vec<u8>>, lab: &Vec<bool>) -> (r: Vec<u8>)
    ensures r@ == checked_line(path@, views(names@), lab@),
{
    let ghost ns = views(names@);
    let mut parts: Vec<Vec<u8>> = Vec::new();
    let mut j: usize = 0;
    while j < names.len()
        invariant j <= names@.len(), ns == views(names@),
            views(parts@) =~= sec_parts(ns, lab@, j as nat),
        decreases names.len() - j,
    {
        let ghost p0 = parts@;
        if j + 1 < lab.len() && lab[j + 1] {
            let t = if names[j].len() > 0 { copy(&names[j]) } else {
                let mut t = Vec::new();
                put(&mut t, b"#");
                let d = dec(j as u64 + 1);
                put(&mut t, d.as_slice());
                t
            };
            proof { assert(t@ =~= param_text(ns, j as nat)); }
            parts.push(t);
            proof { assert(views(parts@) =~= views(p0).push(t@)); }
        }
        j += 1;
        proof { assert(views(parts@) =~= sec_parts(ns, lab@, j as nat)); }
    }
    let mut out = Vec::new();
    put(&mut out, b"checked ");
    put(&mut out, path.as_slice());
    put(&mut out, b" secret=");
    let s = join_exec(&parts, b",");
    put(&mut out, s.as_slice());
    put(&mut out, b" ret=");
    put(&mut out, if lab.len() > 0 && lab[0] { b"s" } else { b"p" });
    out.push(10u8);
    proof { assert(out@ =~= checked_line(path@, ns, lab@)); }
    out
}

pub fn copy(s: &Vec<u8>) -> (r: Vec<u8>)
    ensures r@ == s@,
{
    let mut out = Vec::new();
    put(&mut out, s.as_slice());
    proof { assert(out@ =~= s@); }
    out
}

} // verus!
