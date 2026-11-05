//! The pipeline: the dump's bytes and the manifests in, the report's bytes out, with the
//! end-to-end theorems in its ensures (`report_sound`). The theorems are stated over the MIR
//! semantics (`ctmir::sem` under the manifests' call policy) with premises in MIR terms only:
//! - **CT** (`ct_mir`): a `root <path> ok` line means two completed runs of the root, on
//!   well-typed arguments that agree on the parameters the root's `checked` line does not list as
//!   secret, have the same trace and steps and agree on the outputs the line does not mark secret,
//!   unless the traces first differ at two declassify events (`theorem_ct` carried by
//!   `theorem_sim`).
//! - **Cost** (`cost_mir`): a `bounded <path> deg=<d> steps <= <text>` line means every completed
//!   run of the root on well-typed arguments takes at most `p` steps at its entry frame, `<text>`
//!   being `poly_text_spec(p)` (`theorem_cost` carried by `theorem_sim` and
//!   `lemma_entry_premises`).
use crate::json::{bytes_eq, parse};
#[cfg(verus_keep_ghost)]
use crate::json_inj::jeq;
#[allow(unused_imports)]
use crate::json::*;
use crate::lower::{FnInfo, Reject};
use crate::lower_fn::lower;
use crate::lower_term::Keys;
#[allow(unused_imports)]
use crate::mir::*;
use crate::policy::{decl_exec, has_bytes, parse_manifests};
#[cfg(verus_keep_ghost)]
use crate::policy::{decl_spec, label_view};
#[allow(unused_imports)]
use crate::policy::*;
#[allow(unused_imports)]
use crate::rel::*;
use crate::schema::decode;
#[allow(unused_imports)]
use crate::schema::*;
#[allow(unused_imports)]
use crate::sem::*;
#[allow(unused_imports)]
use crate::sim::*;
#[allow(unused_imports)]
use crate::sim_entry::*;
use crate::text::{checked_text, copy, dec, deg, has_nl, join_exec, poly_text, put, put_clean};
#[allow(unused_imports)]
use crate::text::*;
#[cfg(verus_keep_ghost)]
use ctcore::cost::{atom_val, atoms_val, cert_for, monos_val, poly_val, Atom, Cert, Mono, Poly};
#[cfg(verus_keep_ghost)]
use ctcore::ct::{diverge, ok_prog, val_rel, FnLab};
#[cfg(verus_keep_ghost)]
use ctcore::sem::{nth, Frame, Res, Val};
#[allow(unused_imports)]
use ctcore::syntax as c;
use vstd::prelude::*;

verus! {

pub enum Mode { Check, Cost, Selftest(Vec<u8> /* vectors file */) }

// ------------------------------------------------------------------ the end-to-end statements

/// The arguments and slots of two runs of `insts[i]` agree on what `lab` (one label per local:
/// the return, then the parameters) calls public: equal there, the same shape elsewhere. A
/// `&mut` parameter's argument is its slot.
pub open spec fn pub_agree(m: MirCrate, i: nat, lab: Seq<bool>, a1: Seq<Val>, a2: Seq<Val>, s1: Seq<Val>, s2: Seq<Val>) -> bool {
    let b = inst_body(m, i)->Some_0;
    forall|j: int| #![trigger a1[j], a2[j]] #![trigger s1[j], s2[j]] 0 <= j < b.arg_count ==>
        (!is_mut_ref(m, b.locals@[j + 1].ty) ==> val_rel(lab[1 + j], a1[j], a2[j])) && val_rel(lab[1 + j], s1[j], s2[j])
}

/// The outputs of two runs, the return local and the slots, agree on what `lab` calls public.
pub open spec fn out_agree_mir(lab: Seq<bool>, f1: Frame, f2: Frame) -> bool {
    &&& val_rel(lab[0], f1.locals[0], f2.locals[0])
    &&& f1.slots.len() == f2.slots.len()
    &&& forall|j: int| #![trigger f1.slots[j], f2.slots[j]] 0 <= j < f1.slots.len() ==> val_rel(lab[1 + j], f1.slots[j], f2.slots[j])
}

/// Two completed runs `x`, `y` (final frame, trace, steps): the same trace and steps and outputs
/// agreeing on `lab`'s public ones, or traces that first differ at two declassify events.
pub open spec fn ct_out(lab: Seq<bool>, x: (Frame, Seq<ctcore::sem::Event>, nat), y: (Frame, Seq<ctcore::sem::Event>, nat)) -> bool {
    (x.1 == y.1 && x.2 == y.2 && out_agree_mir(lab, x.0, y.0)) || diverge(x.1, y.1)
}

pub open spec fn ct_runs(lab: Seq<bool>, r1: Res, r2: Res) -> bool {
    r1 is Some && r2 is Some ==> ct_out(lab, r1->Some_0, r2->Some_0)
}

/// **CT over MIR**: two completed runs of `insts[i]` from the same fuel, on well-typed arguments
/// that agree on `lab`'s public parameters, leak the same trace, take the same steps and agree on
/// `lab`'s public outputs, or their traces first differ at two different declassify events.
pub open spec fn ct_mir(m: MirCrate, cp: CallPolicy, i: nat, lab: Seq<bool>) -> bool {
    forall|a1: Seq<Val>, a2: Seq<Val>, s1: Seq<Val>, s2: Seq<Val>, fuel: nat|
        #![trigger mir_run_fn(m, cp, i, mir_entry(m, i, a1, s1), fuel), mir_run_fn(m, cp, i, mir_entry(m, i, a2, s2), fuel)]
        wt_args(m, i, a1, s1) && wt_args(m, i, a2, s2) && pub_agree(m, i, lab, a1, a2, s1, s2) ==>
            ct_runs(lab, mir_run_fn(m, cp, i, mir_entry(m, i, a1, s1), fuel), mir_run_fn(m, cp, i, mir_entry(m, i, a2, s2), fuel))
}

/// **Cost over MIR**: every completed run of `insts[i]` on well-typed arguments takes at most
/// `b`'s value at its entry frame in steps.
pub open spec fn cost_mir(m: MirCrate, cp: CallPolicy, i: nat, b: Poly) -> bool {
    forall|args: Seq<Val>, slots: Seq<Val>, fuel: nat| #![trigger mir_run_fn(m, cp, i, mir_entry(m, i, args, slots), fuel)]
        wt_args(m, i, args, slots) ==>
            (mir_run_fn(m, cp, i, mir_entry(m, i, args, slots), fuel) matches Some((f, t, n)) ==> n <= poly_val(mir_entry(m, i, args, slots), b))
}

/// A MIR type whose core image is `Unit` (`lowers_ty`): `()`, `str` and `&str`, fn items,
/// closures and fn pointers, `vstd`'s `Ghost`/`Tracked`. Such a parameter takes no label.
pub open spec fn unit_ty(m: MirCrate, t: Ty) -> bool {
    match rigid(m, t) {
        Some(RigidTy::Tuple(ts)) => ts@.len() == 0,
        Some(RigidTy::Str) => true,
        Some(RigidTy::Ref(_, q, _)) => rigid(m, q) matches Some(RigidTy::Str),
        Some(RigidTy::FnDef(_, _)) | Some(RigidTy::Closure(_, _)) | Some(RigidTy::FnPtr(_)) => true,
        Some(RigidTy::Adt(_, _)) => adt_row(m, t) matches Some(a) && (a.name@ == b"vstd::prelude::Ghost"@ || a.name@ == b"vstd::prelude::Tracked"@),
        _ => false,
    }
}

/// Per parameter of `b`, whether it takes no label (`unit_ty`).
pub open spec fn ghost_params(m: MirCrate, b: Body) -> Seq<bool> { Seq::new(b.arg_count as nat, |j: int| unit_ty(m, b.locals@[j + 1].ty)) }

/// The first `label` line (as `policy_of` gives them) for `path`, from `k` on.
pub open spec fn label_at(ls: Seq<(Seq<u8>, Seq<Seq<u8>>, Seq<Seq<u8>>)>, path: Seq<u8>, k: nat) -> Option<(Seq<u8>, Seq<Seq<u8>>, Seq<Seq<u8>>)>
    decreases ls.len() - k,
{
    if k >= ls.len() { None } else if ls[k as int].0 == path { Some(ls[k as int]) } else { label_at(ls, path, k + 1) }
}

/// A `label` line as `ct::` attributes: `#[ct::secret(<secret,..>)]`, `#[ct::public(<public,..>)]`.
pub open spec fn label_attrs(sec: Seq<Seq<u8>>, pb: Seq<Seq<u8>>) -> Seq<Seq<u8>> {
    seq![b"#[ct::secret("@ + join(sec, b","@) + b")]"@, b"#[ct::public("@ + join(pb, b","@) + b")]"@]
}

/// The labels source of fn `path` with attributes `attrs`: its `label` line rendered as attributes,
/// or its attributes; `None` when it has both.
pub open spec fn attrs_src(ls: Seq<(Seq<u8>, Seq<Seq<u8>>, Seq<Seq<u8>>)>, path: Seq<u8>, attrs: Seq<Seq<u8>>) -> Option<Seq<Seq<u8>>> {
    match label_at(ls, path, 0) {
        Some(l) => if attrs.len() > 0 { None } else { Some(label_attrs(l.1, l.2)) },
        None => Some(attrs),
    }
}

/// The labels `insts[i]` declares (`decl_spec` of its attributes or `label` line).
pub open spec fn declared(m: MirCrate, pol: Policy, i: nat) -> Option<Option<Seq<bool>>> {
    let b = inst_body(m, i)->Some_0;
    match attrs_src(pol.labels@.map_values(|l: (Vec<u8>, Vec<Vec<u8>>, Vec<Vec<u8>>)| label_view(l)), fn_path(m, i), item_attrs(m, m.insts@[i as int].def)) {
        Some(src) => decl_spec(src, pnames(b), ghost_params(m, b)),
        None => None,
    }
}

/// What a `root <path> ok` line claims: `path` is `insts[i]`; some labels `lab` make the CT
/// theorem hold; every parameter the root's `ct::` attributes (or `label` line) declare secret is
/// secret in `lab`; and the report prints `lab` in `i`'s `checked` line (which fixes the return's
/// and the other parameters' labels, conclusions of label inference).
pub open spec fn root_ok(m: MirCrate, pol: Policy, path: Seq<u8>, lines: Seq<Seq<u8>>) -> bool {
    exists|i: nat, lab: Seq<bool>| #![trigger root_of(m, path, i), ct_mir(m, cpol(pol), i, lab)]
        root_of(m, path, i) && inst_body(m, i) is Some && lab.len() > inst_body(m, i)->Some_0.arg_count
        && ct_mir(m, cpol(pol), i, lab) && lines.contains(checked_line(fn_path(m, i), pnames(inst_body(m, i)->Some_0), lab))
        && secrets_in(declared(m, pol, i), lab)
}

/// The labels were declared (`Some(Some(d))`), and each declared-secret parameter is secret in `lab`.
pub open spec fn secrets_in(dec: Option<Option<Seq<bool>>>, lab: Seq<bool>) -> bool {
    dec matches Some(Some(d)) && forall|j: int| 0 <= j < d.len() && #[trigger] d[j] ==> lab[1 + j]
}

/// What a `bounded ..` line claims: it is `bounded <path> deg=<d> steps <= <text>` for a root
/// `insts[i]` and a bound `b` with `<text> == poly_text_spec(b)` in the root's parameter names,
/// `<d> == deg_spec(b)`, and the cost theorem holds.
pub open spec fn bounded_ok(m: MirCrate, pol: Policy, l: Seq<u8>) -> bool {
    exists|path: Seq<u8>, i: nat, b: Poly| #![trigger root_of(m, path, i), cost_mir(m, cpol(pol), i, b)]
        root_of(m, path, i) && inst_body(m, i) is Some && cost_mir(m, cpol(pol), i, b)
        && l == bounded_line(path, deg_spec(b), poly_text_spec(b, pnames(inst_body(m, i)->Some_0)))
}

/// A line's first word is one of the report's: `root`, `bounded`, `reject`, `checked`,
/// `declassify`, `none`.
pub open spec fn line_kind(l: Seq<u8>) -> bool {
    starts(l, b"root "@) || starts(l, b"bounded "@) || starts(l, b"reject "@) || starts(l, b"checked "@)
        || starts(l, b"declassify "@) || starts(l, b"none "@)
}

/// One report line (`lines` is the whole report): a text without `\n`, then `\n`; a line starting `root ` is a `root <path> ok`
/// line whose claim holds, and one starting `bounded ` is a `bounded` line whose claim holds.
/// Every other line (`reject`, `checked`, `declassify`, `none`, `pass`, `fail`) is
/// informational.
pub open spec fn line_ok(m: MirCrate, pol: Policy, l: Seq<u8>, lines: Seq<Seq<u8>>) -> bool {
    &&& l.len() > 0 && l.last() == 10u8 && no_nl(l.drop_last()) && line_kind(l)
    &&& starts(l, b"root "@) ==> exists|path: Seq<u8>| l == root_line(path) && #[trigger] root_ok(m, pol, path, lines)
    &&& starts(l, b"bounded "@) ==> bounded_ok(m, pol, l)
}

/// **The report is sound.**
/// - The dump is `print(j)` of a JSON value `j`, and `j` is the only one: any `j2` that prints
///   the dump is `j` up to views (`jeq`; `print` is injective, `json_inj::theorem_print_injective`).
/// - `j` decodes (by the schema spec `decode_crate`) to crate `m`. `decode_crate` is *not* proved
///   functional: the claims are about the crate the pipeline decoded, which a TRUSTED row (Task 9)
///   takes to be the one the schema mirror spec gives.
/// - The manifests say policy `pol` (`policy_of`, determined by the bytes).
/// - The report is a sequence of lines, each `line_ok`. A line holds no `\n` before its last byte,
///   so the lines are the report's `\n`-terminated pieces.
///
/// (`mode` names the run; the claims do not depend on it.)
pub open spec fn report_sound(dump: Seq<u8>, manifests: Seq<Vec<u8>>, mode: Mode, out: Seq<u8>) -> bool {
    exists|j: Json, m: MirCrate, pol: Policy, lines: Seq<Seq<u8>>|
        print(j) == dump && (forall|j2: Json| #[trigger] print(j2) == dump ==> jeq(j2, j))
        && decode_crate(j, m) && policy_of(views(manifests), pol) && out == lines.flatten()
        && forall|k: int| 0 <= k < lines.len() ==> line_ok(m, pol, #[trigger] lines[k], lines)
}

// ------------------------------------------------------------------ the end-to-end theorems

/// The root's image has the root's parameters, and its `Mut` locals are the root's `&mut` ones.
proof fn lemma_root_shape(m: MirCrate, pol: Policy, root: Seq<u8>, p: c::Program, infos: Seq<FnInfo>)
    requires lowers(m, pol, root, p, infos),
    ensures ({
        let i = infos[0].inst as nat;
        let b = inst_body(m, i)->Some_0;
        let cb = p.fns@[0];
        &&& p.fns@.len() >= 1 && inst_body(m, i) is Some && root_of(m, root, i)
        &&& cb.nargs == b.arg_count && b.arg_count < b.locals@.len() && b.locals@.len() <= cb.locals@.len()
        &&& forall|k: int| 0 <= k < b.locals@.len() ==> (#[trigger] cb.locals@[k] is Mut) == is_mut_ref(m, b.locals@[k].ty)
        &&& info_ok(m, infos[0], 0)
    }),
{
    let rs = choose|rs: Seq<Seq<bool>>| lowers_rs(m, pol, root, p, infos, rs);
    let i = infos[0].inst as nat;
    assert(lowers_body(m, pol, ords(infos), i, p.fns@[0], rs[0]));
    assert(info_ok(m, infos[0], 0));
    let b = inst_body(m, i)->Some_0;
    let cb = p.fns@[0];
    assert(sig_ok(m, b));
    assert forall|k: int| 0 <= k < b.locals@.len() implies (#[trigger] cb.locals@[k] is Mut) == is_mut_ref(m, b.locals@[k].ty) by {
        assert(lowers_ty(m, b.locals@[k].ty, cb.locals@[k], tyf()));
        lemma_lowers_ty_mut(m, b.locals@[k].ty, cb.locals@[k], tyf());
    }
}

/// The core image of a type is `Unit` exactly when the type is `unit_ty`.
pub proof fn lemma_unit_ty(m: MirCrate, t: Ty, ct: c::Ty, fuel: nat)
    requires lowers_ty(m, t, ct, fuel),
    ensures (ct is Unit) == unit_ty(m, t),
{
    if rigid(m, t) matches Some(RigidTy::Adt(_, _)) {
        assert(lowers_adt_ty(m, t, ct, (fuel - 1) as nat));
    }
}

/// The root's image's parameter locals are `Unit` exactly at `ghost_params`.
proof fn lemma_root_ghost(m: MirCrate, pol: Policy, root: Seq<u8>, p: c::Program, infos: Seq<FnInfo>)
    requires lowers(m, pol, root, p, infos),
    ensures ({
        let b = inst_body(m, infos[0].inst as nat)->Some_0;
        forall|j: int| 0 <= j < b.arg_count ==> (#[trigger] p.fns@[0].locals@[j + 1] is Unit) == ghost_params(m, b)[j]
    }),
{
    let rs = choose|rs: Seq<Seq<bool>>| lowers_rs(m, pol, root, p, infos, rs);
    let i = infos[0].inst as nat;
    assert(lowers_body(m, pol, ords(infos), i, p.fns@[0], rs[0]));
    let b = inst_body(m, i)->Some_0;
    let cb = p.fns@[0];
    assert(sig_ok(m, b));
    assert forall|j: int| 0 <= j < b.arg_count implies (#[trigger] cb.locals@[j + 1] is Unit) == ghost_params(m, b)[j] by {
        assert(lowers_ty(m, b.locals@[j + 1].ty, cb.locals@[j + 1], tyf()));
        lemma_unit_ty(m, b.locals@[j + 1].ty, cb.locals@[j + 1], tyf());
    }
}

/// **The CT theorem over MIR** for a translated root whose image `check_program` accepted with
/// labels `ls`: `ct_mir` with the root's labels.
pub proof fn theorem_ct_mir(m: MirCrate, pol: Policy, root: Seq<u8>, p: c::Program, infos: Seq<FnInfo>, ls: Seq<FnLab>)
    requires lowers(m, pol, root, p, infos), ok_prog(p, ls),
    ensures ct_mir(m, cpol(pol), infos[0].inst as nat, ls[0].locals@),
{
    let i = infos[0].inst as nat;
    let lab = ls[0].locals@;
    lemma_root_shape(m, pol, root, p, infos);
    assert forall|a1: Seq<Val>, a2: Seq<Val>, s1: Seq<Val>, s2: Seq<Val>, fuel: nat|
        wt_args(m, i, a1, s1) && wt_args(m, i, a2, s2) && pub_agree(m, i, lab, a1, a2, s1, s2) implies
            #[trigger] ct_runs(lab, mir_run_fn(m, cpol(pol), i, mir_entry(m, i, a1, s1), fuel), mir_run_fn(m, cpol(pol), i, mir_entry(m, i, a2, s2), fuel)) by {
        lemma_ct_pair(m, pol, root, p, infos, ls, a1, a2, s1, s2, fuel);
    }
}

/// Core's run `c` matches the completed MIR run `x`: the same trace and steps, the same return
/// local and slots.
pub open spec fn core_rel(x: (Frame, Seq<ctcore::sem::Event>, nat), c: Res) -> bool {
    c is Some && c->Some_0.1 == x.1 && c->Some_0.2 == x.2 && x.0.locals[0] == nth(c->Some_0.0.locals, 0) && x.0.slots == c->Some_0.0.slots
}

/// A completed MIR run of the root is core's run of its image (`core_rel`); and the arguments meet
/// core's entry premises.
proof fn lemma_run_rel(m: MirCrate, pol: Policy, root: Seq<u8>, p: c::Program, infos: Seq<FnInfo>, args: Seq<Val>, slots: Seq<Val>, fuel: nat)
    requires lowers(m, pol, root, p, infos), wt_args(m, infos[0].inst as nat, args, slots),
    ensures
        ctcore::cost::entry_plc(p, 0, args, slots),
        ({ let r = mir_run_fn(m, cpol(pol), infos[0].inst as nat, mir_entry(m, infos[0].inst as nat, args, slots), fuel);
           r is Some ==> core_rel(r->Some_0, ctcore::sem::run_fn(p, 0, ctcore::sem::init_entry(p, 0, args, slots), fuel)) }),
{
    lemma_root_shape(m, pol, root, p, infos);
    theorem_sim(m, pol, root, p, infos, 0, args, slots, fuel);
    lemma_entry_premises(m, pol, root, p, infos, 0, args, slots);
}

/// `pub_agree` is core's `args_agree` for the root's image.
proof fn lemma_args_agree(m: MirCrate, pol: Policy, root: Seq<u8>, p: c::Program, infos: Seq<FnInfo>, ls: Seq<FnLab>,
    a1: Seq<Val>, a2: Seq<Val>, s1: Seq<Val>, s2: Seq<Val>)
    requires lowers(m, pol, root, p, infos), ls.len() >= 1, ls[0].locals@.len() == p.fns@[0].locals@.len(),
        wt_args(m, infos[0].inst as nat, a1, s1), wt_args(m, infos[0].inst as nat, a2, s2),
        ctcore::cost::entry_plc(p, 0, a1, s1), ctcore::cost::entry_plc(p, 0, a2, s2),
        pub_agree(m, infos[0].inst as nat, ls[0].locals@, a1, a2, s1, s2),
    ensures ctcore::ct::args_agree(p, ls, 0, a1, a2, s1, s2),
{
    lemma_root_shape(m, pol, root, p, infos);
    let cb = p.fns@[0];
    assert forall|j: int| 0 <= j < cb.nargs && !(cb.locals@[1 + j] is Mut) implies
        val_rel(ctcore::ct::lab(ls[0], (1 + j) as nat), #[trigger] a1[j], a2[j]) && ctcore::ct::no_mut(a1[j]) && ctcore::ct::no_mut(a2[j]) by {
        assert(cb.locals@[1 + j] == cb.locals@[j + 1]);
    }
}

proof fn lemma_ls0(m: MirCrate, pol: Policy, root: Seq<u8>, p: c::Program, infos: Seq<FnInfo>, ls: Seq<FnLab>)
    requires lowers(m, pol, root, p, infos), ok_prog(p, ls),
    ensures ls.len() >= 1 && p.fns@.len() >= 1 && ls[0].locals@.len() == p.fns@[0].locals@.len(),
{
    lemma_root_shape(m, pol, root, p, infos);
    assert(ctcore::ct::ok_body(p, ls, 0nat));
}

/// `theorem_ct` for the root's image, its conclusion read on the MIR runs `x`, `y` (`core_rel`).
proof fn lemma_core_ct(p: c::Program, ls: Seq<FnLab>, a1: Seq<Val>, a2: Seq<Val>, s1: Seq<Val>, s2: Seq<Val>, fuel: nat,
    x: (Frame, Seq<ctcore::sem::Event>, nat), y: (Frame, Seq<ctcore::sem::Event>, nat))
    requires ok_prog(p, ls), p.fns@.len() >= 1, ctcore::ct::args_agree(p, ls, 0, a1, a2, s1, s2),
        core_rel(x, ctcore::sem::run_fn(p, 0, ctcore::sem::init_entry(p, 0, a1, s1), fuel)),
        core_rel(y, ctcore::sem::run_fn(p, 0, ctcore::sem::init_entry(p, 0, a2, s2), fuel)),
    ensures ct_out(ls[0].locals@, x, y),
{
    ctcore::ni::theorem_ct(p, ls, 0, a1, a2, s1, s2, fuel);
}

proof fn lemma_ct_pair(m: MirCrate, pol: Policy, root: Seq<u8>, p: c::Program, infos: Seq<FnInfo>, ls: Seq<FnLab>,
    a1: Seq<Val>, a2: Seq<Val>, s1: Seq<Val>, s2: Seq<Val>, fuel: nat)
    requires lowers(m, pol, root, p, infos), ok_prog(p, ls),
        wt_args(m, infos[0].inst as nat, a1, s1), wt_args(m, infos[0].inst as nat, a2, s2),
        pub_agree(m, infos[0].inst as nat, ls[0].locals@, a1, a2, s1, s2),
    ensures ({
        let i = infos[0].inst as nat;
        ct_runs(ls[0].locals@, mir_run_fn(m, cpol(pol), i, mir_entry(m, i, a1, s1), fuel), mir_run_fn(m, cpol(pol), i, mir_entry(m, i, a2, s2), fuel))
    }),
{
    hide(lowers);
    hide(wt_args);
    hide(pub_agree);
    hide(mir_run_fn);
    hide(mir_entry);
    hide(ok_prog);
    hide(ctcore::sem::run_fn);
    hide(ctcore::sem::init_entry);
    hide(ctcore::ct::args_agree);
    hide(ctcore::cost::entry_plc);
    hide(ct_out);
    hide(core_rel);
    let i = infos[0].inst as nat;
    let r1 = mir_run_fn(m, cpol(pol), i, mir_entry(m, i, a1, s1), fuel);
    let r2 = mir_run_fn(m, cpol(pol), i, mir_entry(m, i, a2, s2), fuel);
    if r1 is Some && r2 is Some {
        lemma_run_rel(m, pol, root, p, infos, a1, s1, fuel);
        lemma_run_rel(m, pol, root, p, infos, a2, s2, fuel);
        lemma_ls0(m, pol, root, p, infos, ls);
        lemma_args_agree(m, pol, root, p, infos, ls, a1, a2, s1, s2);
        lemma_core_ct(p, ls, a1, a2, s1, s2, fuel, r1->Some_0, r2->Some_0);
        lemma_ct_some(ls[0].locals@, r1, r2);
    } else {
        lemma_ct_none(ls[0].locals@, r1, r2);
    }
}

proof fn lemma_ct_some(lab: Seq<bool>, r1: Res, r2: Res)
    requires r1 is Some && r2 is Some, ct_out(lab, r1->Some_0, r2->Some_0),
    ensures ct_runs(lab, r1, r2),
{}

proof fn lemma_ct_none(lab: Seq<bool>, r1: Res, r2: Res)
    requires !(r1 is Some && r2 is Some),
    ensures ct_runs(lab, r1, r2),
{}

/// `b`'s value is the same at two frames with the same locals (as `nth` reads them) and slots.
proof fn lemma_atom_same(f1: Frame, f2: Frame, a: Atom)
    requires f1.slots == f2.slots, forall|x: nat| #[trigger] nth(f1.locals, x) == nth(f2.locals, x),
    ensures atom_val(f1, a) == atom_val(f2, a),
    decreases a,
{
    match a {
        Atom::Gap(x, y) => { lemma_atom_same(f1, f2, *x); lemma_atom_same(f1, f2, *y); },
        Atom::Len(x) => { assert(nth(f1.locals, x as nat) == nth(f2.locals, x as nat)); },
        Atom::Val(x, _) => { assert(nth(f1.locals, x as nat) == nth(f2.locals, x as nat)); },
        _ => {},
    }
}

proof fn lemma_atoms_same(f1: Frame, f2: Frame, s: Seq<Atom>)
    requires f1.slots == f2.slots, forall|x: nat| #[trigger] nth(f1.locals, x) == nth(f2.locals, x),
    ensures atoms_val(f1, s) == atoms_val(f2, s),
    decreases s.len(),
{
    if s.len() > 0 { lemma_atom_same(f1, f2, s[0]); lemma_atoms_same(f1, f2, s.drop_first()); }
}

proof fn lemma_monos_same(f1: Frame, f2: Frame, s: Seq<Mono>)
    requires f1.slots == f2.slots, forall|x: nat| #[trigger] nth(f1.locals, x) == nth(f2.locals, x),
    ensures monos_val(f1, s) == monos_val(f2, s),
    decreases s.len(),
{
    if s.len() > 0 { lemma_atoms_same(f1, f2, s[0].atoms@); lemma_monos_same(f1, f2, s.drop_first()); }
}

/// **The cost theorem over MIR** for a translated root whose image `check_program` accepted and
/// whose summary `b` `analyze` certified.
pub proof fn theorem_cost_mir(m: MirCrate, pol: Policy, root: Seq<u8>, p: c::Program, infos: Seq<FnInfo>, ls: Seq<FnLab>,
    certs: Seq<Cert>, sums: Seq<Option<Poly>>, b: Poly)
    requires lowers(m, pol, root, p, infos), ok_prog(p, ls), certs.len() == p.fns@.len(), sums.len() == p.fns@.len(),
        sums[0] == Some(b), forall|g: int| 0 <= g < p.fns@.len() && sums[g] is Some ==> cert_for(p, g as nat, certs[g], sums),
    ensures cost_mir(m, cpol(pol), infos[0].inst as nat, b),
{
    let i = infos[0].inst as nat;
    assert forall|args: Seq<Val>, slots: Seq<Val>, fuel: nat| wt_args(m, i, args, slots) implies
        (#[trigger] mir_run_fn(m, cpol(pol), i, mir_entry(m, i, args, slots), fuel) matches Some((f, t, n)) ==> n <= poly_val(mir_entry(m, i, args, slots), b)) by {
        lemma_cost_run(m, pol, root, p, infos, ls, certs, sums, b, args, slots, fuel);
    }
}

proof fn lemma_cost_run(m: MirCrate, pol: Policy, root: Seq<u8>, p: c::Program, infos: Seq<FnInfo>, ls: Seq<FnLab>,
    certs: Seq<Cert>, sums: Seq<Option<Poly>>, b: Poly, args: Seq<Val>, slots: Seq<Val>, fuel: nat)
    requires lowers(m, pol, root, p, infos), ok_prog(p, ls), certs.len() == p.fns@.len(), sums.len() == p.fns@.len(),
        sums[0] == Some(b), forall|g: int| 0 <= g < p.fns@.len() && sums[g] is Some ==> cert_for(p, g as nat, certs[g], sums),
        wt_args(m, infos[0].inst as nat, args, slots),
    ensures ({
        let i = infos[0].inst as nat;
        mir_run_fn(m, cpol(pol), i, mir_entry(m, i, args, slots), fuel) matches Some((f, t, n)) ==> n <= poly_val(mir_entry(m, i, args, slots), b)
    }),
{
    let i = infos[0].inst as nat;
    let r = mir_run_fn(m, cpol(pol), i, mir_entry(m, i, args, slots), fuel);
    if r is Some {
        lemma_root_shape(m, pol, root, p, infos);
        theorem_sim(m, pol, root, p, infos, 0, args, slots, fuel);
        lemma_entry_premises(m, pol, root, p, infos, 0, args, slots);
        ctcore::cost::theorem_cost(p, ls, certs, sums, 0, args, slots, fuel, b);
        let rs = choose|rs: Seq<Seq<bool>>| lowers_rs(m, pol, root, p, infos, rs);
        lemma_entry(m, pol, ords(infos), i, p, 0, rs[0], args, slots);
        let fm = mir_entry(m, i, args, slots);
        let fc = ctcore::sem::init_entry(p, 0, args, slots);
        let bm = inst_body(m, i)->Some_0;
        assert forall|x: nat| #[trigger] nth(fm.locals, x) == nth(fc.locals, x) by {
            if x < fm.locals.len() { assert(fm.locals[x as int] == fc.locals[x as int]); }
        }
        lemma_monos_same(fm, fc, b.monos@);
    }
}

// ------------------------------------------------------------------ the report's lines, exec

pub open spec fn acc_ok(m: MirCrate, pol: Policy, a: Seq<Vec<u8>>) -> bool {
    forall|k: int| 0 <= k < a.len() ==> line_ok(m, pol, #[trigger] a[k]@, views(a))
}

proof fn lemma_line_mono(m: MirCrate, pol: Policy, l: Seq<u8>, s1: Seq<Seq<u8>>, s2: Seq<Seq<u8>>)
    requires line_ok(m, pol, l, s1), forall|y: Seq<u8>| s1.contains(y) ==> s2.contains(y),
    ensures line_ok(m, pol, l, s2),
{
    if starts(l, b"root "@) {
        let path = choose|path: Seq<u8>| l == root_line(path) && #[trigger] root_ok(m, pol, path, s1);
        let (i, lab) = choose|i: nat, lab: Seq<bool>| #![trigger root_of(m, path, i), ct_mir(m, cpol(pol), i, lab)]
            root_of(m, path, i) && inst_body(m, i) is Some && lab.len() > inst_body(m, i)->Some_0.arg_count
            && ct_mir(m, cpol(pol), i, lab) && s1.contains(checked_line(fn_path(m, i), pnames(inst_body(m, i)->Some_0), lab));
        assert(root_ok(m, pol, path, s2));
    }
}

proof fn lemma_acc_mono(m: MirCrate, pol: Policy, a: Seq<Vec<u8>>, x: Vec<u8>)
    requires acc_ok(m, pol, a), line_ok(m, pol, x@, views(a.push(x))),
    ensures acc_ok(m, pol, a.push(x)),
{
    let b = a.push(x);
    assert(views(b) =~= views(a).push(x@));
    assert forall|y: Seq<u8>| views(a).contains(y) implies views(b).contains(y) by {
        let k = choose|k: int| 0 <= k < views(a).len() && views(a)[k] == y;
        assert(views(b)[k] == y);
    }
    assert forall|k: int| 0 <= k < b.len() implies line_ok(m, pol, #[trigger] b[k]@, views(b)) by {
        if k < a.len() { assert(b[k] == a[k]); lemma_line_mono(m, pol, a[k]@, views(a), views(b)); }
    }
}

fn kind_ok(l: &Vec<u8>) -> (r: bool)
    ensures r == line_kind(l@),
{
    crate::policy::starts_pub(l, b"root ") || crate::policy::starts_pub(l, b"bounded ") || crate::policy::starts_pub(l, b"reject ")
        || crate::policy::starts_pub(l, b"checked ") || crate::policy::starts_pub(l, b"declassify ") || crate::policy::starts_pub(l, b"none ")
}

/// `l` (with its last `\n`) is not one of the two claim lines.
fn no_claim(l: &Vec<u8>) -> (r: bool)
    ensures r == (!starts(l@, b"root "@) && !starts(l@, b"bounded "@)),
{
    !crate::policy::starts_pub(l, b"root ") && !crate::policy::starts_pub(l, b"bounded ")
}

/// Adds the informational line `clean(body)` + `\n`.
fn info(Ghost(m): Ghost<MirCrate>, Ghost(pol): Ghost<Policy>, acc: &mut Vec<Vec<u8>>, body: &[u8]) -> (r: Result<(), Vec<u8>>)
    requires acc_ok(m, pol, old(acc)@),
    ensures r is Ok ==> acc_ok(m, pol, final(acc)@),
{
    let mut l = Vec::new();
    put_clean(&mut l, body);
    let ghost c = l@;
    l.push(10u8);
    if !no_claim(&l) || !kind_ok(&l) { return Err(cat(b"report line looks like a claim or has no known kind: ", body)); }
    proof {
        lemma_clean_no_nl(body@);
        assert(l@.drop_last() =~= c);
        lemma_acc_mono(m, pol, old(acc)@, l);
    }
    let ghost a0 = acc@;
    acc.push(l);
    proof { lemma_sub_push(a0, acc@.last()); assert(acc@ == a0.push(acc@.last())); }
    Ok(())
}

proof fn lemma_sub_push(a: Seq<Vec<u8>>, x: Vec<u8>)
    ensures forall|y: Seq<u8>| views(a).contains(y) ==> views(a.push(x)).contains(y), views(a.push(x)).contains(x@),
{
    assert(views(a.push(x)) =~= views(a).push(x@));
    assert(views(a.push(x))[a.len() as int] == x@);
    assert forall|y: Seq<u8>| views(a).contains(y) implies views(a.push(x)).contains(y) by {
        let k = choose|k: int| 0 <= k < views(a).len() && views(a)[k] == y;
        assert(views(a.push(x))[k] == y);
    }
}

fn copy_slice(a: &[u8]) -> Vec<u8> { cat(a, b"") }

pub fn cat(a: &[u8], b: &[u8]) -> Vec<u8> {
    let mut e = Vec::new();
    put(&mut e, a);
    put(&mut e, b);
    e
}

/// A translation reject's text, as the old driver's `tr_text`.
fn tr_text(e: &Reject) -> Vec<u8> {
    let mut t = Vec::new();
    match e {
        Reject::Unsupported { path, what, site } => {
            put(&mut t, b"Unsupported "); put(&mut t, site.as_slice()); put(&mut t, b" "); put(&mut t, path.as_slice());
            put(&mut t, b": "); put(&mut t, what.as_slice());
        },
        Reject::Unresolved { path, callee, site } => {
            put(&mut t, b"Unresolved "); put(&mut t, site.as_slice()); put(&mut t, b" "); put(&mut t, path.as_slice());
            put(&mut t, b" calls "); put(&mut t, callee.as_slice());
        },
        Reject::Attr { path, msg } => { put(&mut t, b"Attr "); put(&mut t, path.as_slice()); put(&mut t, b": "); put(&mut t, msg.as_slice()); },
        Reject::Root { path, msg } => { put(&mut t, b"Root "); put(&mut t, path.as_slice()); put(&mut t, b": "); put(&mut t, msg.as_slice()); },
    }
    t
}

fn kind_text(k: &ctcore::RejectKind) -> &'static [u8] {
    match k {
        ctcore::RejectKind::SecretSwitch => b"SecretSwitch",
        ctcore::RejectKind::SecretAssert => b"SecretAssert",
        ctcore::RejectKind::SecretIndex => b"SecretIndex",
        ctcore::RejectKind::SecretDivOperand => b"SecretDivOperand",
        ctcore::RejectKind::SecretShift => b"SecretShift",
        ctcore::RejectKind::SecretAlloc => b"SecretAlloc",
        ctcore::RejectKind::SecretRange => b"SecretRange",
        ctcore::RejectKind::ArgLabel(_) => b"ArgLabel",
        ctcore::RejectKind::RetLabel => b"RetLabel",
        ctcore::RejectKind::MutLabel => b"MutLabel",
        ctcore::RejectKind::NotWf => b"NotWf",
        ctcore::RejectKind::Recursion => b"Recursion",
        ctcore::RejectKind::InferFailed => b"InferFailed",
    }
}

/// A `check_program` reject's text, as the old driver's `reject_text`: `<Kind> <file>:<line> in
/// <fn>`; at a call, also ` calling <callee>`, and for `ArgLabel(j)` ` param #<j+1> <name>`.
fn reject_text(gs: &Vec<(Vec<u8>, Vec<u8>, Vec<u8>)>, p: &c::Program, infos: &Vec<FnInfo>, rj: &ctcore::Reject) -> Vec<u8> {
    let mut t = Vec::new();
    if rj.f >= infos.len() {
        put(&mut t, b"NotWf fn #");
        let d = dec(rj.f as u64);
        put(&mut t, d.as_slice());
        put(&mut t, b" out of range");
        return t;
    }
    let i = &infos[rj.f];
    put(&mut t, kind_text(&rj.kind));
    put(&mut t, b" ");
    let mut site: &[u8] = b"?";
    match rj.stmt {
        Some(s) => if rj.block < i.stmt_sites.len() && s < i.stmt_sites[rj.block].len() { site = i.stmt_sites[rj.block][s].as_slice(); },
        None => if rj.block < i.block_sites.len() { site = i.block_sites[rj.block].as_slice(); },
    }
    let (fp, fs) = at_drop(gs, &i.path, &copy_slice(site));
    put(&mut t, fs.as_slice());
    put(&mut t, b" in ");
    put(&mut t, fp.as_slice());
    if rj.stmt.is_none() && rj.f < p.fns.len() && rj.block < p.fns[rj.f].blocks.len() {
        if let c::Term::Call(c::Callee::Fn(g), _, _, _) = &p.fns[rj.f].blocks[rj.block].term {
            if *g < infos.len() {
                put(&mut t, b" calling ");
                put(&mut t, infos[*g].path.as_slice());
                if let ctcore::RejectKind::ArgLabel(j) = rj.kind {
                    put(&mut t, b" param #");
                    let d = dec((if j < usize::MAX { j + 1 } else { j }) as u64);
                    put(&mut t, d.as_slice());
                    put(&mut t, b" ");
                    if j < infos[*g].param_names.len() { put(&mut t, infos[*g].param_names[j].as_slice()); }
                }
            }
        }
    }
    t
}

/// The first two words of `t`, joined by a space (the per-root dedup key of a reject).
fn key2(t: &Vec<u8>) -> Vec<u8> {
    let ws = crate::policy::words_exec(t.as_slice());
    let mut k = Vec::new();
    if ws.len() > 0 { put(&mut k, ws[0].as_slice()); }
    if ws.len() > 1 { put(&mut k, b" "); put(&mut k, ws[1].as_slice()); }
    k
}

/// `reject <root> <text>` lines, one per first two words of a text, the first such text kept.
fn rejects(Ghost(m): Ghost<MirCrate>, Ghost(pol): Ghost<Policy>, acc: &mut Vec<Vec<u8>>, root: &Vec<u8>, texts: &Vec<Vec<u8>>) -> (r: Result<(), Vec<u8>>)
    requires acc_ok(m, pol, old(acc)@),
    ensures r is Ok ==> acc_ok(m, pol, final(acc)@),
{
    let ts = dedupe(texts);
    let mut k: usize = 0;
    while k < ts.len()
        invariant acc_ok(m, pol, acc@),
        decreases ts.len() - k,
    {
        let mut b = Vec::new();
        put(&mut b, b"reject ");
        put(&mut b, root.as_slice());
        put(&mut b, b" ");
        put(&mut b, ts[k].as_slice());
        info(Ghost(m), Ghost(pol), acc, b.as_slice())?;
        k += 1;
    }
    Ok(())
}

/// The texts whose first two words no earlier text has, in order.
pub fn dedupe(texts: &Vec<Vec<u8>>) -> Vec<Vec<u8>> {
    let mut seen: Vec<Vec<u8>> = Vec::new();
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut k: usize = 0;
    while k < texts.len()
        decreases texts.len() - k,
    {
        let key = key2(&texts[k]);
        if !has_bytes(&seen, &key) {
            seen.push(key);
            out.push(copy(&texts[k]));
        }
        k += 1;
    }
    out
}

fn has_prefix_root(r: &Vec<u8>, krate: &Vec<u8>) -> bool {
    let mut pre = Vec::new();
    put(&mut pre, krate.as_slice());
    put(&mut pre, b"::");
    crate::policy::starts_pub(r, pre.as_slice())
}

/// `true` when `path` has a `c::` segment that starts a path (not `xc::` or `c_x::`).
pub fn names_crate(path: &Vec<u8>, c: &Vec<u8>) -> bool {
    let mut pre = Vec::new();
    put(&mut pre, c.as_slice());
    put(&mut pre, b"::");
    let n = pre.len();
    if n > path.len() { return false; }
    let last = path.len() - n;
    let mut i: usize = 0;
    while i <= last
        invariant n == pre@.len(), last + n == path@.len(), path@.len() <= usize::MAX,
        decreases last + 1 - i,
    {
        let mut k: usize = 0;
        let mut eq = true;
        while k < n && i + k < path.len()
            invariant n == pre@.len(), i <= last, last + n == path@.len(), k <= n, path@.len() <= usize::MAX,
            decreases n - k,
        {
            if path[i + k] != pre[k] { eq = false; }
            k += 1;
        }
        if eq {
            if i == 0 { return true; }
            let b = path[i - 1];
            if !((48 <= b && b <= 57) || (65 <= b && b <= 90) || (97 <= b && b <= 122) || b == 95) { return true; }
        }
        if i == last { return false; }
        i += 1;
    }
    false
}

/// Where each drop glue of root `root`'s closure is reported (8c ruling: a glue reject is
/// reported at the `Drop`'s site): its path, then the site and fn of the first reached `Drop` in
/// closure order that calls it, a glue's own `Drop`s taking the site of the `Drop` that reached
/// that glue.
fn glue_sites(m: &MirCrate, pol: &Policy, root: &Vec<u8>) -> Vec<(Vec<u8>, Vec<u8>, Vec<u8>)> {
    let mut out: Vec<(Vec<u8>, Vec<u8>, Vec<u8>)> = Vec::new();
    let j0 = match crate::lower_fn::root_inst(m, root.as_slice()) { Ok(j) => j, Err(_) => return out };
    let order = crate::lower_fn::closure_order(m, pol, j0);
    let mut i: usize = 0;
    while i < order.len()
        invariant forall|g: int| 0 <= g < order@.len() ==> (#[trigger] order@[g]) < m.insts@.len(),
        decreases order.len() - i,
    {
        let j = order[i];
        let x = &m.insts[j];
        let path = if matches!(x.kind, InstanceKind::Shim) { copy(&x.name) } else { copy(&x.key) };
        let mut from: Option<(Vec<u8>, Vec<u8>)> = None;
        if matches!(x.kind, InstanceKind::Shim) {
            let mut q: usize = 0;
            while q < out.len()
                decreases out.len() - q,
            {
                if bytes_eq(out[q].0.as_slice(), path.as_slice()) { from = Some((copy(&out[q].1), copy(&out[q].2))); }
                q += 1;
            }
        }
        if let Some(b) = crate::look::x_inst_body(m, j) {
            if let Some(seen) = crate::lower_fn::reach(b) {
                let mut bb: usize = 0;
                while bb < b.blocks.len()
                    invariant seen@.len() == b.blocks@.len(),
                    decreases b.blocks.len() - bb,
                {
                    if seen[bb] {
                        if let TerminatorKind::Drop { place, .. } = &b.blocks[bb].terminator.kind {
                            if let Some(t) = crate::lower::x_place_ty(m, b, place) {
                                if let Some(d) = crate::look::x_drop_row(m, t) {
                                    if let Some(jj) = crate::look::x_inst_idx(m, d.glue) {
                                        let g = &m.insts[jj];
                                        let gp = if matches!(g.kind, InstanceKind::Shim) { copy(&g.name) } else { copy(&g.key) };
                                        let mut known = false;
                                        let mut q: usize = 0;
                                        while q < out.len()
                                            decreases out.len() - q,
                                        {
                                            if bytes_eq(out[q].0.as_slice(), gp.as_slice()) { known = true; }
                                            q += 1;
                                        }
                                        if !known {
                                            let (site, fp) = match &from {
                                                Some((s, f)) => (copy(s), copy(f)),
                                                None => (crate::lower_fn::site(m, b.blocks[bb].terminator.span), copy(&path)),
                                            };
                                            out.push((gp, site, fp));
                                        }
                                    }
                                }
                            }
                        }
                    }
                    bb += 1;
                }
            }
        }
        i += 1;
    }
    out
}

/// A reject in fn `path` at `site`, as reported: inside a drop glue, at the `Drop`'s site in the
/// fn that drops.
pub fn at_drop(gs: &Vec<(Vec<u8>, Vec<u8>, Vec<u8>)>, path: &Vec<u8>, site: &Vec<u8>) -> (Vec<u8>, Vec<u8>) {
    let mut q: usize = 0;
    while q < gs.len()
        decreases gs.len() - q,
    {
        if bytes_eq(gs[q].0.as_slice(), path.as_slice()) { return (copy(&gs[q].2), copy(&gs[q].1)); }
        q += 1;
    }
    (copy(path), copy(site))
}

/// `e` with a glue fn's path and site replaced by its `Drop`'s (`at_drop`).
pub fn remap(gs: &Vec<(Vec<u8>, Vec<u8>, Vec<u8>)>, e: &Reject) -> Reject {
    match e {
        Reject::Unsupported { path, what, site } => { let (p, s) = at_drop(gs, path, site); Reject::Unsupported { path: p, what: copy(what), site: s } },
        Reject::Unresolved { path, callee, site } => { let (p, s) = at_drop(gs, path, site); Reject::Unresolved { path: p, callee: copy(callee), site: s } },
        Reject::Attr { path, msg } => Reject::Attr { path: copy(path), msg: copy(msg) },
        Reject::Root { path, msg } => Reject::Root { path: copy(path), msg: copy(msg) },
    }
}

/// The labels source of fn `info`: its attributes, or its `label` line rendered as attributes.
fn attrs_for(pol: &Policy, info: &FnInfo) -> (r: Result<Vec<Vec<u8>>, Vec<u8>>)
    ensures r matches Ok(a) ==> attrs_src(pol.labels@.map_values(|l: (Vec<u8>, Vec<Vec<u8>>, Vec<Vec<u8>>)| label_view(l)), info.path@, views(info.attrs@)) == Some(views(a@)),
{
    let ghost lv = pol.labels@.map_values(|l: (Vec<u8>, Vec<Vec<u8>>, Vec<Vec<u8>>)| label_view(l));
    let mut k: usize = 0;
    while k < pol.labels.len()
        invariant k <= pol.labels@.len(), lv == pol.labels@.map_values(|l: (Vec<u8>, Vec<Vec<u8>>, Vec<Vec<u8>>)| label_view(l)),
            label_at(lv, info.path@, 0) == label_at(lv, info.path@, k as nat),
        decreases pol.labels.len() - k,
    {
        proof { assert(lv[k as int] == label_view(pol.labels@[k as int])); }
        if bytes_eq(pol.labels[k].0.as_slice(), info.path.as_slice()) {
            if info.attrs.len() > 0 { return Err(cat(b"both ct:: attributes and a manifest label line", b"")); }
            let mut a = Vec::new();
            let mut s = Vec::new();
            put(&mut s, b"#[ct::secret(");
            let j = join_exec(&pol.labels[k].1, b",");
            put(&mut s, j.as_slice());
            put(&mut s, b")]");
            let mut q = Vec::new();
            put(&mut q, b"#[ct::public(");
            let j2 = join_exec(&pol.labels[k].2, b",");
            put(&mut q, j2.as_slice());
            put(&mut q, b")]");
            let ghost (sv, qv) = (s@, q@);
            a.push(s);
            a.push(q);
            proof {
                assert(views(a@) =~= seq![sv, qv]);
                assert(views(a@) =~= label_attrs(lv[k as int].1, lv[k as int].2));
                assert(views(info.attrs@).len() == 0);
            }
            return Ok(a);
        }
        k += 1;
    }
    let mut a = Vec::new();
    let mut k: usize = 0;
    while k < info.attrs.len()
        invariant k <= info.attrs@.len(), views(a@) =~= views(info.attrs@).subrange(0, k as int),
        decreases info.attrs.len() - k,
    {
        let ghost o = a@;
        a.push(copy(&info.attrs[k]));
        proof { crate::policy::lemma_views_push(o, a@.last()); assert(a@ == o.push(a@.last())); }
        k += 1;
    }
    proof { assert(views(a@) =~= views(info.attrs@)); }
    Ok(a)
}

proof fn lemma_info0(m: MirCrate, infos: Seq<FnInfo>, b0: Body)
    requires infos.len() >= 1, info_ok(m, infos[0], 0), b0 == inst_body(m, infos[0].inst as nat)->Some_0,
    ensures views(infos[0].param_names@) == pnames(b0), infos[0].path@ == fn_path(m, infos[0].inst as nat),
        views(infos[0].attrs@) == item_attrs(m, m.insts@[infos[0].inst as int].def), pnames(b0).len() == b0.arg_count,
{}

/// Fn `infos[0]`'s declared labels are `d`, as `declared` says.
pub open spec fn root_decl(m: MirCrate, pol: Policy, i: nat, d: Option<Vec<bool>>) -> bool {
    d matches Some(v) && declared(m, pol, i) == Some(Some(v@))
}

/// The declared labels of every fn (`decl` for `check_program`), or the attribute and root rejects.
fn decls(Ghost(m): Ghost<MirCrate>, Ghost(root): Ghost<Seq<u8>>, p: &c::Program, pol: &Policy, infos: &Vec<FnInfo>)
    -> (r: Result<Vec<Option<Vec<bool>>>, Vec<Vec<u8>>>)
    requires lowers(m, *pol, root, *p, infos@),
    ensures r matches Ok(d) ==> d@.len() == infos@.len() && infos@.len() >= 1 && root_decl(m, *pol, infos@[0].inst as nat, d@[0]),
{
    proof { lemma_root_shape(m, *pol, root, *p, infos@); lemma_root_ghost(m, *pol, root, *p, infos@); }
    let ghost i0 = infos@[0].inst as nat;
    let ghost b0 = inst_body(m, i0)->Some_0;
    let mut out: Vec<Option<Vec<bool>>> = Vec::new();
    let mut errs: Vec<Vec<u8>> = Vec::new();
    let mut g: usize = 0;
    while g < infos.len()
        invariant g <= infos@.len(), errs@.len() == 0 ==> out@.len() == g,
            infos@.len() >= 1, info_ok(m, infos@[0], 0), i0 == infos@[0].inst as nat, inst_body(m, i0) is Some, b0 == inst_body(m, i0)->Some_0,
            p.fns@.len() >= 1, b0.arg_count < b0.locals@.len(), b0.locals@.len() <= p.fns@[0].locals@.len(),
            forall|j: int| 0 <= j < b0.arg_count ==> (#[trigger] p.fns@[0].locals@[j + 1] is Unit) == ghost_params(m, b0)[j],
            errs@.len() == 0 && g > 0 ==> root_decl(m, *pol, i0, out@[0]),
        decreases infos.len() - g,
    {
        let info = &infos[g];
        let mut ghost: Vec<bool> = Vec::new();
        let mut j: usize = 0;
        while j < info.param_names.len()
            invariant ghost@.len() == j, j <= info.param_names@.len(), info == &infos@[g as int],
                g == 0 ==> forall|k: int| 0 <= k < j ==> ghost@[k] == ghost_params(m, b0)[k],
                infos@.len() >= 1, info_ok(m, infos@[0], 0), i0 == infos@[0].inst as nat, b0 == inst_body(m, i0)->Some_0,
                p.fns@.len() >= 1, b0.arg_count < b0.locals@.len(), b0.locals@.len() <= p.fns@[0].locals@.len(),
                forall|j: int| 0 <= j < b0.arg_count ==> (#[trigger] p.fns@[0].locals@[j + 1] is Unit) == ghost_params(m, b0)[j],
            decreases info.param_names.len() - j,
        {
            proof { if g == 0 { lemma_info0(m, infos@, b0); } }
            let u = g < p.fns.len() && j + 1 < p.fns[g].locals.len() && matches!(p.fns[g].locals[j + 1], c::Ty::Unit);
            proof { if g == 0 { assert(p.fns@[0].locals@[j + 1] is Unit == ghost_params(m, b0)[j as int]); } }
            ghost.push(u);
            j += 1;
        }
        proof {
            if g == 0 {
                lemma_info0(m, infos@, b0);
                assert(ghost@ =~= ghost_params(m, b0));
            }
        }
        let d = match attrs_for(pol, info) {
            Err(e) => Err(e),
            Ok(a) => {
                let d = decl_exec(&a, &info.param_names, &ghost);
                proof {
                    if g == 0 && d is Ok {
                        assert(declared(m, *pol, i0) == decl_spec(views(a@), pnames(b0), ghost_params(m, b0)));
                    }
                }
                d
            },
        };
        match d {
            Err(e) => errs.push(tr_text(&Reject::Attr { path: copy(&info.path), msg: e })),
            Ok(d) => {
                // `is_root` is `g == 0` (`info_ok`)
                if (info.is_root || g == 0) && d.is_none() {
                    errs.push(tr_text(&Reject::Root { path: copy(&info.path), msg: cat(b"a root needs a ct:: attribute", b"") }));
                }
                let ghost o = out@;
                out.push(d);
                proof { if errs@.len() == 0 && g > 0 { assert(out@[0] == o[0]); } if errs@.len() == 0 { assert(out@[g as int] == d); } }
            },
        }
        g += 1;
    }
    if errs.len() > 0 { Err(errs) } else { Ok(out) }
}

/// `check_program`'s `decl_ok` on the root's declared labels: each declared secret is secret.
proof fn lemma_root_decl(m: MirCrate, pol: Policy, i: nat, decl: Seq<Option<Vec<bool>>>, ls: Seq<FnLab>)
    requires decl.len() >= 1, root_decl(m, pol, i, decl[0]), ctcore::ct::decl_ok(decl, ls),
    ensures secrets_in(declared(m, pol, i), ls[0].locals@),
{
    let v = decl[0]->Some_0;
    assert forall|j: int| 0 <= j < v@.len() && #[trigger] v@[j] implies ls[0].locals@[1 + j] by {
        assert(decl[0]->Some_0@[j]);
    }
}

proof fn lemma_root_claim(m: MirCrate, pol: Policy, root: Seq<u8>, p: c::Program, infos: Seq<FnInfo>, ls: Seq<FnLab>)
    requires lowers(m, pol, root, p, infos), ok_prog(p, ls),
    ensures ({
        let i = infos[0].inst as nat;
        let b = inst_body(m, i)->Some_0;
        &&& infos.len() >= 1 && ls.len() == infos.len() && root_of(m, root, i) && inst_body(m, i) is Some
        &&& ls[0].locals@.len() > b.arg_count && ct_mir(m, cpol(pol), i, ls[0].locals@)
        &&& infos[0].path@ == fn_path(m, i) && views(infos[0].param_names@) == pnames(b)
    }),
{
    lemma_root_shape(m, pol, root, p, infos);
    assert(ctcore::ct::ok_body(p, ls, 0nat));
    theorem_ct_mir(m, pol, root, p, infos, ls);
}

/// Per-fn declassify sites across the ok roots: path, sites (sorted, distinct).
pub type Declass = Vec<(Vec<u8>, Vec<Vec<u8>>)>;

pub fn add_site(ds: &mut Declass, path: &Vec<u8>, site: &Vec<u8>) {
    let mut k: usize = 0;
    while k < ds.len()
        decreases ds.len() - k,
    {
        if bytes_eq(ds[k].0.as_slice(), path.as_slice()) {
            let mut v = Vec::new();
            std::mem::swap(&mut v, &mut ds[k].1);
            insert_sorted(&mut v, copy(site));
            std::mem::swap(&mut v, &mut ds[k].1);
            return;
        }
        k += 1;
    }
    let mut v = Vec::new();
    v.push(copy(site));
    ds.push((copy(path), v));
}

/// Records fn `path`'s `checked` line `l`; a second, different `checked` line for one path is an
/// error (the root line's labels would be ambiguous).
pub fn one_checked(cks: &mut Vec<(Vec<u8>, Vec<u8>)>, path: &Vec<u8>, l: &Vec<u8>) -> Result<(), Vec<u8>> {
    let mut k: usize = 0;
    while k < cks.len()
        decreases cks.len() - k,
    {
        if bytes_eq(cks[k].0.as_slice(), path.as_slice()) {
            if bytes_eq(cks[k].1.as_slice(), l.as_slice()) { return Ok(()); }
            return Err(cat(b"two different checked lines for ", path.as_slice()));
        }
        k += 1;
    }
    cks.push((copy(path), copy(l)));
    Ok(())
}

/// `declassify <fn>#<k> <site>` per fn, its sites numbered from 1 in their (sorted) order.
pub fn declass_bodies(ds: &Declass) -> Vec<Vec<u8>> {
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut k: usize = 0;
    while k < ds.len()
        decreases ds.len() - k,
    {
        let mut q: usize = 0;
        while q < ds[k].1.len()
            invariant k < ds@.len(),
            decreases ds@[k as int].1@.len() - q,
        {
            let mut b = Vec::new();
            put(&mut b, b"declassify ");
            put(&mut b, ds[k].0.as_slice());
            put(&mut b, b"#");
            let d = dec((if q < usize::MAX { q + 1 } else { q }) as u64);
            put(&mut b, d.as_slice());
            put(&mut b, b" ");
            put(&mut b, ds[k].1[q].as_slice());
            out.push(b);
            q += 1;
        }
        k += 1;
    }
    out
}

/// One CT root's lines.
fn check_root(m: &MirCrate, pol: &Policy, r: &Vec<u8>, keys: &mut Keys, acc: &mut Vec<Vec<u8>>, ds: &mut Declass,
    cks: &mut Vec<(Vec<u8>, Vec<u8>)>) -> (res: Result<(), Vec<u8>>)
    requires acc_ok(*m, *pol, old(acc)@),
    ensures res is Ok ==> acc_ok(*m, *pol, final(acc)@),
{
    let (p, infos) = match lower(m, pol, r.as_slice(), keys) {
        Ok(x) => x,
        Err(es) => {
            let gs = glue_sites(m, pol, r);
            let mut ts = Vec::new();
            let mut k: usize = 0;
            while k < es.len() decreases es.len() - k { ts.push(tr_text(&remap(&gs, &es[k]))); k += 1; }
            return rejects(Ghost(*m), Ghost(*pol), acc, r, &ts);
        },
    };
    let decl = match decls(Ghost(*m), Ghost(r@), &p, pol, &infos) { Ok(d) => d, Err(ts) => return rejects(Ghost(*m), Ghost(*pol), acc, r, &ts) };
    let ls = match ctcore::check_program(&p, &decl) {
        Ok(ls) => ls,
        Err(rs) => {
            let gs = glue_sites(m, pol, r);
            let mut ts = Vec::new();
            let mut k: usize = 0;
            while k < rs.len() decreases rs.len() - k { ts.push(reject_text(&gs, &p, &infos, &rs[k])); k += 1; }
            return rejects(Ghost(*m), Ghost(*pol), acc, r, &ts);
        },
    };
    proof { lemma_root_claim(*m, *pol, r@, p, infos@, ls@); lemma_root_decl(*m, *pol, infos@[0].inst as nat, decl@, ls@); }
    let ghost i = infos@[0].inst as nat;
    let ghost lab = ls@[0].locals@;
    let ghost a0 = acc@;
    // the root's `checked` line first: the root line's claim names it
    let c0 = checked_text(&infos[0].path, &infos[0].param_names, &ls[0].locals);
    if has_nl(crate::policy::sub(c0.as_slice(), 0, c0.len() - 1).as_slice()) || !no_claim(&c0) || !kind_ok(&c0) {
        return Err(cat(b"a checked line holds a newline: ", infos[0].path.as_slice()));
    }
    one_checked(cks, &infos[0].path, &c0)?;
    proof {
        assert(c0@ == checked_line(fn_path(*m, i), pnames(inst_body(*m, i)->Some_0), lab));
        assert(c0@.drop_last() =~= c0@.subrange(0, c0@.len() - 1));
        lemma_acc_mono(*m, *pol, acc@, c0);
        lemma_sub_push(acc@, c0);
    }
    acc.push(c0);
    let mut g: usize = 1;
    while g < infos.len()
        invariant acc_ok(*m, *pol, acc@), ls@.len() == infos@.len(),
            views(acc@).contains(checked_line(fn_path(*m, i), pnames(inst_body(*m, i)->Some_0), lab)),
        decreases infos.len() - g,
    {
        let cg = checked_text(&infos[g].path, &infos[g].param_names, &ls[g].locals);
        if cg.len() == 0 || has_nl(crate::policy::sub(cg.as_slice(), 0, cg.len() - 1).as_slice()) || !no_claim(&cg) || !kind_ok(&cg) {
            return Err(cat(b"a checked line holds a newline: ", infos[g].path.as_slice()));
        }
        one_checked(cks, &infos[g].path, &cg)?;
        proof {
            assert(cg@.drop_last() =~= cg@.subrange(0, cg@.len() - 1));
            lemma_acc_mono(*m, *pol, acc@, cg);
            lemma_sub_push(acc@, cg);
        }
        acc.push(cg);
        g += 1;
    }
    let mut g: usize = 0;
    while g < infos.len()
        decreases infos.len() - g,
    {
        let mut k: usize = 0;
        while k < infos[g].declassify_sites.len()
            invariant g < infos@.len(),
            decreases infos@[g as int].declassify_sites@.len() - k,
        {
            add_site(ds, &infos[g].path, &infos[g].declassify_sites[k]);
            k += 1;
        }
        g += 1;
    }
    let mut l = Vec::new();
    put(&mut l, b"root ");
    put(&mut l, r.as_slice());
    put(&mut l, b" ok");
    if has_nl(l.as_slice()) { return Err(cat(b"a root path holds a newline: ", r.as_slice())); }
    let ghost body = l@;
    l.push(10u8);
    if crate::policy::starts_pub(&l, b"bounded ") { return Err(cat(b"a root line looks like a bound: ", r.as_slice())); }
    proof {
        assert(l@ =~= root_line(r@));
        assert(l@.drop_last() =~= body);
        assert(l@.subrange(0, 5) =~= b"root "@);
        assert(line_kind(l@));
        lemma_sub_push(acc@, l);
        assert(root_ok(*m, *pol, r@, views(acc@.push(l))));
        lemma_acc_mono(*m, *pol, acc@, l);
    }
    acc.push(l);
    Ok(())
}

fn why_text(w: &ctcore::loops::CostWhy) -> Option<Vec<u8>> {
    use ctcore::loops::CostWhy;
    let mut t = Vec::new();
    match w {
        CostWhy::NotCounted(h) => { put(&mut t, b"NotCounted("); let d = dec(*h as u64); put(&mut t, d.as_slice()); put(&mut t, b")"); },
        CostWhy::CalleeNone(g) => { put(&mut t, b"CalleeNone("); let d = dec(*g as u64); put(&mut t, d.as_slice()); put(&mut t, b")"); },
        CostWhy::Validator(b) => { put(&mut t, b"Validator("); let d = dec(*b as u64); put(&mut t, d.as_slice()); put(&mut t, b")"); },
        CostWhy::Unresolved => put(&mut t, b"Unresolved"),
        CostWhy::Recursion => put(&mut t, b"Recursion"),
        CostWhy::DegreeCap => put(&mut t, b"DegreeCap"),
        CostWhy::Overflow => put(&mut t, b"Overflow"),
        CostWhy::NotWf => put(&mut t, b"NotWf"),
        CostWhy::NotTyped => put(&mut t, b"NotTyped"),
        CostWhy::Bounded => return None,
    }
    Some(t)
}

fn none_line(Ghost(m): Ghost<MirCrate>, Ghost(pol): Ghost<Policy>, acc: &mut Vec<Vec<u8>>, r: &Vec<u8>, why: &[u8]) -> (res: Result<(), Vec<u8>>)
    requires acc_ok(m, pol, old(acc)@),
    ensures res is Ok ==> acc_ok(m, pol, final(acc)@),
{
    let mut b = Vec::new();
    put(&mut b, b"none ");
    put(&mut b, r.as_slice());
    put(&mut b, b" ");
    put(&mut b, why);
    info(Ghost(m), Ghost(pol), acc, b.as_slice())
}

/// One cost root's line. `Err` is a hard error: no fn for the root, an ambiguous key, or no reason.
fn cost_root(m: &MirCrate, pol: &Policy, r: &Vec<u8>, keys: &mut Keys, acc: &mut Vec<Vec<u8>>) -> (res: Result<(), Vec<u8>>)
    requires acc_ok(*m, *pol, old(acc)@),
    ensures res is Ok ==> acc_ok(*m, *pol, final(acc)@),
{
    let (p, infos) = match lower(m, pol, r.as_slice(), keys) {
        Ok(x) => x,
        Err(es) => {
            let mut k: usize = 0;
            while k < es.len() decreases es.len() - k {
                if let Reject::Root { .. } = &es[k] { return Err(tr_text(&es[k])); }
                k += 1;
            }
            if es.len() == 0 { return Err(cat(b"no translation reject text: ", r.as_slice())); }
            let gs = glue_sites(m, pol, r);
            return none_line(Ghost(*m), Ghost(*pol), acc, r, tr_text(&remap(&gs, &es[0])).as_slice());
        },
    };
    let mut decl: Vec<Option<Vec<bool>>> = Vec::new();
    while decl.len() < p.fns.len() decreases p.fns.len() - decl.len() { decl.push(None); }
    let _ls = match ctcore::check_program(&p, &decl) {
        Ok(ls) => ls,
        Err(rs) => {
            let mut rec = false;
            let mut k: usize = 0;
            while k < rs.len() decreases rs.len() - k {
                if let ctcore::RejectKind::Recursion = rs[k].kind { rec = true; }
                k += 1;
            }
            return none_line(Ghost(*m), Ghost(*pol), acc, r, if rec { b"Recursion" } else { b"NotTyped" });
        },
    };
    let (sums, _certs, whys) = ctcore::analyze(&p);
    if sums.len() > 0 {
        if let Some(poly) = &sums[0] {
            proof {
                lemma_root_claim(*m, *pol, r@, p, infos@, _ls@);
                theorem_cost_mir(*m, *pol, r@, p, infos@, _ls@, _certs@, sums@, *poly);
            }
            let ghost i = infos@[0].inst as nat;
            let mut l = Vec::new();
            put(&mut l, b"bounded ");
            put(&mut l, r.as_slice());
            put(&mut l, b" deg=");
            let d = dec(deg(poly));
            put(&mut l, d.as_slice());
            put(&mut l, b" steps <= ");
            let t = poly_text(poly, &infos[0].param_names);
            put(&mut l, t.as_slice());
            if has_nl(l.as_slice()) { return Err(cat(b"a bounded line holds a newline: ", r.as_slice())); }
            let ghost body = l@;
            l.push(10u8);
            if crate::policy::starts_pub(&l, b"root ") { return Err(cat(b"a bounded line looks like a root line: ", r.as_slice())); }
            proof {
                assert(l@ =~= bounded_line(r@, deg_spec(*poly), poly_text_spec(*poly, pnames(inst_body(*m, i)->Some_0))));
                assert(l@.subrange(0, 8) =~= b"bounded "@);
                assert(line_kind(l@));
                assert(l@.drop_last() =~= body);
                assert(bounded_ok(*m, *pol, l@));
                lemma_acc_mono(*m, *pol, acc@, l);
            }
            acc.push(l);
            return Ok(());
        }
    }
    if whys.len() == 0 { return Err(cat(b"analyze gave no summary and no reason: ", r.as_slice())); }
    match why_text(&whys[0]) {
        Some(w) => none_line(Ghost(*m), Ghost(*pol), acc, r, w.as_slice()),
        None => Err(cat(b"analyze gave no summary and no reason: ", r.as_slice())),
    }
}

/// `a < b`, bytewise (as `String`'s order).
fn lt_bytes(a: &Vec<u8>, b: &Vec<u8>) -> bool {
    let mut i: usize = 0;
    while i < a.len() && i < b.len()
        decreases a.len() - i,
    {
        if a[i] != b[i] { return a[i] < b[i]; }
        i += 1;
    }
    a.len() < b.len()
}

/// Inserts `x` into the sorted `v` unless it is there.
fn insert_sorted(v: &mut Vec<Vec<u8>>, x: Vec<u8>)
    ensures forall|y: Seq<u8>| views(final(v)@).contains(y) <==> (views(old(v)@).contains(y) || y == x@),
{
    let mut k: usize = 0;
    while k < v.len() && lt_bytes(&v[k], &x)
        invariant k <= v@.len(), v@ == old(v)@,
        decreases v.len() - k,
    {
        k += 1;
    }
    if k < v.len() && bytes_eq(v[k].as_slice(), x.as_slice()) {
        proof {
            assert(views(v@)[k as int] == x@);
            assert forall|y: Seq<u8>| views(v@).contains(y) <==> (views(v@).contains(y) || y == x@) by {
                if y == x@ { assert(views(v@)[k as int] == y); }
            }
        }
        return;
    }
    let ghost o = v@;
    v.insert(k, x);
    proof {
        assert(v@ == o.insert(k as int, x));
        assert forall|q: int| 0 <= q < k implies #[trigger] v@[q] == o[q] by {}
        assert forall|q: int| k < q < v@.len() implies #[trigger] v@[q] == o[q - 1] by {}
        assert(v@[k as int] == x);
        assert forall|y: Seq<u8>| views(v@).contains(y) <==> (views(o).contains(y) || y == x@) by {
            if views(v@).contains(y) {
                let q = choose|q: int| 0 <= q < views(v@).len() && views(v@)[q] == y;
                if q < k { assert(views(o)[q] == y); } else if q > k { assert(views(o)[q - 1] == v@[q]@); }
            }
            if views(o).contains(y) {
                let q = choose|q: int| 0 <= q < views(o).len() && views(o)[q] == y;
                if q < k { assert(views(v@)[q] == y); } else { assert(v@[q + 1] == o[q]); assert(views(v@)[q + 1] == y); }
            }
            if y == x@ { assert(views(v@)[k as int] == y); }
        }
        assert(o == old(v)@);
        assert(forall|y: Seq<u8>| views(v@).contains(y) <==> (views(old(v)@).contains(y) || y == x@));
    }
}

/// **The pipeline.** The dump's bytes, the manifests' bytes in order, and the mode in; the
/// report's bytes out, or why there is no report. (The lines come out sorted bytewise and
/// distinct, as the old driver's; the ensures does not state the order.)
pub fn pipeline(dump: &[u8], manifests: &Vec<Vec<u8>>, mode: &Mode) -> (r: Result<Vec<u8>, Vec<u8>>)
    ensures r is Ok ==> report_sound(dump@, manifests@, *mode, r->Ok_0@),
{
    let j = match parse(dump) { Some(j) => j, None => return Err(cat(b"dump: not JSON in the dump's subset", b"")) };
    let ghost jj = j;
    let m = match decode(j) { Some(m) => m, None => return Err(cat(b"dump: does not decode as a MIR crate", b"")) };
    let pol = parse_manifests(manifests)?;
    let mut k: usize = 0;
    while k < pol.ghost_unit.len()
        decreases pol.ghost_unit.len() - k,
    {
        if names_crate(&pol.ghost_unit[k], &m.crate_name) && !bytes_eq(pol.ghost_unit[k].as_slice(), b"ct_fixtures::ct::ghost_fallback") {
            return Err(cat(b"a ghost line inside the analysed crate: ", pol.ghost_unit[k].as_slice()));
        }
        k += 1;
    }
    let mut acc: Vec<Vec<u8>> = Vec::new();
    let mut keys: Keys = Vec::new();
    match mode {
        Mode::Check => {
            let mut ds: Declass = Vec::new();
            let mut cks: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
            let mut any = false;
            let mut k: usize = 0;
            while k < pol.roots.len()
                invariant acc_ok(m, pol, acc@),
                decreases pol.roots.len() - k,
            {
                if has_prefix_root(&pol.roots[k], &m.crate_name) {
                    any = true;
                    check_root(&m, &pol, &pol.roots[k], &mut keys, &mut acc, &mut ds, &mut cks)?;
                }
                k += 1;
            }
            if !any { return Err(cat(b"no manifest root for analysed crate ", m.crate_name.as_slice())); }
            let bs = declass_bodies(&ds);
            let mut k: usize = 0;
            while k < bs.len()
                invariant acc_ok(m, pol, acc@),
                decreases bs.len() - k,
            {
                info(Ghost(m), Ghost(pol), &mut acc, bs[k].as_slice())?;
                k += 1;
            }
        },
        Mode::Cost => {
            let mut k: usize = 0;
            while k < pol.cost_roots.len()
                invariant acc_ok(m, pol, acc@),
                decreases pol.cost_roots.len() - k,
            {
                if has_prefix_root(&pol.cost_roots[k], &m.crate_name) {
                    cost_root(&m, &pol, &pol.cost_roots[k], &mut keys, &mut acc)?;
                }
                k += 1;
            }
        },
        Mode::Selftest(_) => return Err(cat(b"selftest: Task 8", b"")),
    }
    // sorted, distinct
    let mut sorted: Vec<Vec<u8>> = Vec::new();
    let mut k: usize = 0;
    while k < acc.len()
        invariant k <= acc@.len(),
            forall|y: Seq<u8>| views(sorted@).contains(y) ==> views(acc@).contains(y),
            forall|q: int| 0 <= q < k ==> views(sorted@).contains(#[trigger] acc@[q]@),
        decreases acc.len() - k,
    {
        proof { assert(views(acc@)[k as int] == acc@[k as int]@); }
        insert_sorted(&mut sorted, copy(&acc[k]));
        k += 1;
    }
    let mut out: Vec<u8> = Vec::new();
    let mut k: usize = 0;
    while k < sorted.len()
        invariant k <= sorted@.len(), out@ == views(sorted@).subrange(0, k as int).flatten_alt(),
        decreases sorted.len() - k,
    {
        put(&mut out, sorted[k].as_slice());
        k += 1;
        proof { assert(views(sorted@).subrange(0, k as int).drop_last() =~= views(sorted@).subrange(0, k - 1)); }
    }
    proof {
        let lines = views(sorted@);
        assert(lines.subrange(0, sorted@.len() as int) =~= lines);
        lines.lemma_flatten_and_flatten_alt_are_equivalent();
        assert forall|y: Seq<u8>| views(acc@).contains(y) implies lines.contains(y) by {
            let q = choose|q: int| 0 <= q < views(acc@).len() && views(acc@)[q] == y;
            assert(views(sorted@).contains(acc@[q]@));
        }
        assert forall|q: int| 0 <= q < lines.len() implies line_ok(m, pol, #[trigger] lines[q], lines) by {
            assert(views(acc@).contains(lines[q]));
            let a = choose|a: int| 0 <= a < views(acc@).len() && views(acc@)[a] == lines[q];
            assert(line_ok(m, pol, acc@[a]@, views(acc@)));
            lemma_line_mono(m, pol, lines[q], views(acc@), lines);
        }
        assert forall|j2: Json| #[trigger] print(j2) == dump@ implies jeq(j2, jj) by {
            crate::json_inj::theorem_print_injective(j2, jj);
        }
        assert(report_sound(dump@, manifests@, *mode, out@));
    }
    Ok(out)
}

} // verus!
