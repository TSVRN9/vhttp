//! ct-dump (TRUSTED, unverified, decision-free): `CT_MODE=dump` writes `$CT_OUT/mir-<crate>.json`,
//! the object of the spec's §Dump. Every value in it is `serde_json::to_string` of a rustc_public
//! value or of a query's answer. Ids (`Ty`, `Span`, `AllocId`, `InstanceDef`, `TyConstId`, `DefId`)
//! serialize as bare integers, so the tables say what an id denotes; each table key is the id
//! serialized the same way.
//!
//! Which bodies: the closure from every monomorphic local fn item over every `Call`'s resolved
//! callee and every `Drop`'s glue, following each instance whose `body()` is `Some`, in any crate.
//! Nothing is filtered by crate, name or manifest. The only conditions on values are "already
//! visited?", `Option`/`Result` to `null`, the spec's selections (local *fn* items, calls whose
//! callee has `FnDef` type, `RigidTy::Adt` for `adts`), the structural matches that reach ids the
//! rustc_public visitors skip, the held-types rule of `layouts`, and `discr` = `null` off enums
//! (`discriminant_for_variant` asserts `is_enum`). After writing, `dangling` re-reads the file and fails the build on an id that a
//! reference position holds but its table does not define.

use crate::ct_key;
use rustc_public::mir::alloc::{AllocId, GlobalAlloc};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::visit::Location;
use rustc_public::mir::{AggregateKind, Body, MirVisitor, ProjectionElem, Rvalue, TerminatorKind, VarDebugInfo, VarDebugInfoContents};
use rustc_public::ty::{AdtDef, AdtKind, Allocation, ConstantKind, GenericArgs, MirConst, RigidTy, Span, Ty, TyConst, TyConstId, TyConstKind, TyKind};
use rustc_public::visitor::{Visitable, Visitor};
use rustc_public::{CrateDef, CrateDefType, ItemKind};
use serde_json::Value;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::ops::ControlFlow;
use std::path::Path;

macro_rules! js {
    ($e:expr) => {
        serde_json::to_string(&$e).expect("serde_json::to_string")
    };
}

#[derive(Default)]
struct Dump {
    insts: Vec<String>,
    calls: Vec<String>,
    drops: Vec<String>,
    tys: Vec<String>,
    adts: Vec<String>,
    consts: Vec<String>,
    layouts: Vec<String>,
    allocs: Vec<String>,
    spans: Vec<String>,
    seen_inst: HashSet<Instance>,
    seen_call: HashSet<Ty>,
    seen_drop: HashSet<Ty>,
    seen_ty: HashSet<Ty>,
    seen_const: HashSet<TyConstId>,
    seen_alloc: HashSet<AllocId>,
    seen_span: HashSet<Span>,
    seen_lay: HashSet<Ty>,
    adt_fields: HashMap<Ty, Vec<Ty>>,
    inst_work: Vec<Instance>,
    ty_work: Vec<Ty>,
    alloc_work: Vec<AllocId>,
    lay_work: Vec<Ty>,
}

/// Dumps crate `krate` to `out/mir-<krate>.json`, then fails on a dangling id (the file stays).
pub fn dump(krate: &str, out: &Path) -> Result<(), String> {
    let mut d = Dump::default();
    let mut items = Vec::new();
    for item in rustc_public::all_local_items() {
        if item.kind() != ItemKind::Fn {
            continue;
        }
        let inst = Instance::try_from(item).ok();
        inst.into_iter().for_each(|i| d.inst(i));
        let attrs: Vec<String> = item.all_tool_attrs().iter().map(|a| a.as_str().to_string()).collect();
        items.push(format!(r#"{{"def":{},"name":{},"inst":{},"attrs":{}}}"#, js!(item.def_id()), js!(item.name()), js!(inst.map(|i| i.def)), js!(attrs)));
    }
    d.run()?;
    d.layouts();
    let mut text = format!(r#"{{"crate":{}"#, js!(krate));
    let tables = [("items", &items), ("insts", &d.insts), ("calls", &d.calls), ("drops", &d.drops), ("tys", &d.tys), ("adts", &d.adts)];
    for (name, rows) in tables.into_iter().chain([("consts", &d.consts), ("layouts", &d.layouts), ("allocs", &d.allocs), ("spans", &d.spans)]) {
        text += &format!(r#","{name}":[{}]"#, rows.join(","));
    }
    text += "}";
    let file = out.join(format!("mir-{krate}.json"));
    std::fs::write(&file, &text).map_err(|e| format!("{}: {e}", file.display()))?;
    let v: Value = serde_json::from_str(&text).map_err(|e| format!("{}: re-read: {e}", file.display()))?;
    let bad = dangling(&v);
    if bad.is_empty() {
        return Ok(());
    }
    let first: Vec<&str> = bad.iter().take(10).map(|s| s.as_str()).collect();
    Err(format!("{}: {} dangling ids, first: {}", file.display(), bad.len(), first.join(", ")))
}

impl Dump {
    fn run(&mut self) -> Result<(), String> {
        loop {
            if let Some(i) = self.inst_work.pop() {
                self.instance(i)?;
            } else if let Some(a) = self.alloc_work.pop() {
                self.global(a);
            } else if let Some(t) = self.ty_work.pop() {
                self.ty(t);
            } else {
                return Ok(());
            }
        }
    }

    fn inst(&mut self, i: Instance) {
        if self.seen_inst.insert(i) {
            self.inst_work.push(i);
        }
    }

    fn alloc(&mut self, a: &Allocation) {
        for (_, p) in &a.provenance.ptrs {
            if self.seen_alloc.insert(p.0) {
                self.alloc_work.push(p.0);
            }
        }
    }

    fn span(&mut self, s: Span) {
        if self.seen_span.insert(s) {
            let line = s.get_lines().start_line;
            self.spans.push(format!(r#"{{"id":{},"file":{},"line":{}}}"#, js!(s), js!(s.get_filename()), js!(line)));
        }
    }

    fn instance(&mut self, i: Instance) -> Result<(), String> {
        let body = i.body();
        let sig = i.ty().kind().fn_sig().map(|s| s.skip_binder());
        let _ = sig.visit(self);
        if let Some(b) = &body {
            self.body(b)?;
        }
        let (id, name, key, krate, kind) = (js!(i.def), js!(i.name()), js!(ct_key(&i)), js!(i.def.krate().name), js!(i.kind));
        let row = format!(r#"{{"id":{id},"name":{name},"key":{key},"krate":{krate},"kind":{kind},"body":{},"fn_sig":{}}}"#, js!(body), js!(sig));
        self.insts.push(row);
        Ok(())
    }

    /// Every Ty, TyConst, Span and AllocId of `b`, and a `calls`/`drops` entry for each `Call` of an
    /// `FnDef`-typed callee and each `Drop`, over all blocks (cleanup ones too).
    fn body(&mut self, b: &Body) -> Result<(), String> {
        self.visit_body(b);
        for l in b.locals() {
            self.span(l.span); // `super_local_decl` passes it only as a `Location`
        }
        for blk in &b.blocks {
            match &blk.terminator.kind {
                TerminatorKind::Call { func, .. } => {
                    let t = func.ty(b.locals()).map_err(|e| format!("callee type: {e}"))?;
                    let kind = t.kind();
                    let Some((def, args)) = kind.fn_def() else { continue };
                    let _ = Visitor::visit_ty(self, &t);
                    if !self.seen_call.insert(t) {
                        continue;
                    }
                    let r = Instance::resolve(def, args).ok();
                    r.into_iter().for_each(|r| self.inst(r));
                    self.calls.push(format!(r#"{{"fn_ty":{},"def":{},"args":{},"resolved":{}}}"#, js!(t), js!(def), js!(args), js!(r.map(|r| r.def))));
                }
                TerminatorKind::Drop { place, .. } => {
                    let t = place.ty(b.locals()).map_err(|e| format!("dropped place type: {e}"))?;
                    let _ = Visitor::visit_ty(self, &t);
                    if !self.seen_drop.insert(t) {
                        continue;
                    }
                    let g = Instance::resolve_drop_in_place(t);
                    self.inst(g);
                    self.drops.push(format!(r#"{{"ty":{},"glue":{},"empty":{}}}"#, js!(t), js!(g.def), js!(g.is_empty_shim())));
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn ty(&mut self, t: Ty) {
        let kind = t.kind();
        let _ = t.super_visit(self);
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = &kind {
            self.adt(t, *def, args);
        }
        self.tys.push(format!(r#"{{"id":{},"kind":{}}}"#, js!(t), js!(kind)));
    }

    fn adt(&mut self, t: Ty, def: AdtDef, args: &GenericArgs) {
        let kind = def.kind();
        let mut vs = Vec::new();
        for v in def.variants_iter() {
            let fields: Vec<Ty> = v.fields().iter().map(|f| f.ty_with_args(args)).collect();
            let _ = fields.visit(self);
            self.adt_fields.entry(t).or_default().extend(&fields);
            // `discriminant_for_variant` asserts `is_enum`: a struct or union has no discriminant.
            let discr = (kind == AdtKind::Enum).then(|| def.discriminant_for_variant(v.idx()).val);
            vs.push(format!(r#"{{"discr":{},"fields":{}}}"#, js!(discr), js!(fields)));
        }
        self.adts.push(format!(r#"{{"ty":{},"name":{},"kind":{},"is_box":{},"variants":[{}]}}"#, js!(t), js!(def.name()), js!(kind), js!(def.is_box()), vs.join(",")));
    }

    fn lay(&mut self, t: Ty) {
        if self.seen_lay.insert(t) {
            self.lay_work.push(t);
        }
    }

    /// `layouts`, after `run` (so `adt_fields` is complete): the type of every allocated constant
    /// and, transitively, the types a value of it holds: ADT fields, tuple and array elements, a
    /// pointer's pointee. A fn pointer's signature and a `dyn`'s predicates hold no value and sit
    /// under a binder, where `layout` ICEs on escaping bound vars, so they are not followed.
    fn layouts(&mut self) {
        while let Some(t) = self.lay_work.pop() {
            let shape = t.layout().ok().map(|l| l.shape());
            self.layouts.push(format!(r#"{{"ty":{},"shape":{}}}"#, js!(t), js!(shape)));
            let held = match t.kind().rigid() {
                Some(RigidTy::Adt(..)) => self.adt_fields.get(&t).cloned().unwrap_or_default(),
                Some(RigidTy::Tuple(ts)) => ts.clone(),
                Some(RigidTy::Array(e, _) | RigidTy::Slice(e) | RigidTy::Pat(e, _) | RigidTy::Ref(_, e, _) | RigidTy::RawPtr(e, _)) => vec![*e],
                _ => vec![],
            };
            held.into_iter().for_each(|k| self.lay(k));
        }
    }

    fn global(&mut self, a: AllocId) {
        let g = GlobalAlloc::from(a);
        match &g {
            GlobalAlloc::Memory(m) => self.alloc(m),
            GlobalAlloc::VTable(t, tr) => {
                let _ = Visitor::visit_ty(self, t);
                let _ = tr.as_ref().map(|b| b.value.generic_args.visit(self));
            }
            GlobalAlloc::TypeId { ty } => {
                let _ = Visitor::visit_ty(self, ty);
            }
            GlobalAlloc::Function(_) | GlobalAlloc::Static(_) => {}
        }
        self.allocs.push(format!(r#"{{"id":{},"alloc":{}}}"#, js!(a), js!(g)));
    }
}

/// The type-level walk: records each Ty and TyConst once; `run` expands a Ty's kind later.
impl Visitor for Dump {
    type Break = ();
    fn visit_ty(&mut self, t: &Ty) -> ControlFlow<()> {
        if self.seen_ty.insert(*t) {
            self.ty_work.push(*t);
        }
        ControlFlow::Continue(())
    }
    fn visit_const(&mut self, c: &TyConst) -> ControlFlow<()> {
        if self.seen_const.insert(c.id) {
            if let TyConstKind::Value(t, a) = c.kind() {
                self.alloc(a); // `Visitable for Allocation` is a no-op
                self.lay(*t);
            }
            self.consts.push(format!(r#"{{"id":{},"usize":{}}}"#, js!(c.id), js!(c.eval_target_usize().ok())));
        }
        c.super_visit(self)
    }
}

/// The body walk, plus the ids rustc_public's `MirVisitor` passes over.
impl MirVisitor for Dump {
    fn visit_ty(&mut self, t: &Ty, _: Location) {
        let _ = Visitor::visit_ty(self, t);
    }
    fn visit_ty_const(&mut self, c: &TyConst, _: Location) {
        let _ = Visitor::visit_const(self, c);
    }
    fn visit_span(&mut self, s: &Span) {
        self.span(*s);
    }
    fn visit_args(&mut self, a: &GenericArgs, _: Location) {
        let _ = a.visit(self);
    }
    fn visit_mir_const(&mut self, c: &MirConst, _: Location) {
        if let ConstantKind::Allocated(a) = c.kind() {
            self.alloc(a);
            self.lay(c.ty());
        }
        let _ = c.visit(self); // the kind's TyConst and args, and the type
    }
    fn visit_rvalue(&mut self, r: &Rvalue, l: Location) {
        if let Rvalue::Aggregate(k, _) = r {
            match k {
                AggregateKind::Array(t) | AggregateKind::RawPtr(t, _) => MirVisitor::visit_ty(self, t, l),
                AggregateKind::Adt(_, _, a, ..)
                | AggregateKind::Closure(_, a)
                | AggregateKind::Coroutine(_, a)
                | AggregateKind::CoroutineClosure(_, a) => self.visit_args(a, l),
                AggregateKind::Tuple => {}
            }
        }
        self.super_rvalue(r, l)
    }
    fn visit_var_debug_info(&mut self, v: &VarDebugInfo) {
        for p in v.composite.iter().flat_map(|c| &c.projection) {
            if let ProjectionElem::Field(_, t) | ProjectionElem::OpaqueCast(t) = p {
                let _ = Visitor::visit_ty(self, t);
            }
        }
        if let VarDebugInfoContents::Const(c) = &v.value {
            self.span(c.span); // `super_var_debug_info` skips the `ConstOperand`'s span
        }
        self.super_var_debug_info(v)
    }
}

/// The ids a dump references but does not define, as `"<table> <id>"`. The reference positions
/// are read off rustc_public's type definitions (`mir/body.rs`, `ty.rs`, `mir/alloc.rs`) and the
/// spec's own records, not off the walk above, so a gap in the walk shows up here:
/// - Ty: the keys `ty`, `fn_ty` (a number) and `fields`, `inputs_and_output` (a list of them); the
///   variants `Slice`, `OpaqueCast`, `Type`, `ZSTValue`, `Array` (a number), `Tuple` (each
///   element), and payload index 0 of `Array`, `RawPtr`, `Pat`, `Value`, `VTable`, `Reborrow`, 1
///   of `Ref`, `Field`, 2 of `Cast`;
/// - AllocId: the second element of each `ptrs` pair (`ProvenanceMap`);
/// - Span: the key `span`; InstanceDef: the keys `inst`, `resolved`, `glue`.
///
/// A position holding a non-number (`Ref`'s `BorrowKind`, `FieldsShape::Array`'s object) is not
/// a reference.
pub fn dangling(d: &Value) -> Vec<String> {
    let mut r: [BTreeSet<u64>; 4] = Default::default();
    refs(d, &mut r);
    let mut bad = Vec::new();
    for (k, table) in ["tys", "allocs", "spans", "insts"].iter().enumerate() {
        let def: BTreeSet<u64> = d[table].as_array().into_iter().flatten().filter_map(|e| e["id"].as_u64()).collect();
        bad.extend(r[k].difference(&def).map(|id| format!("{table} {id}")));
    }
    bad
}

const TY: usize = 0;
const ALLOC: usize = 1;
const SPAN: usize = 2;
const INST: usize = 3;

fn refs(v: &Value, r: &mut [BTreeSet<u64>; 4]) {
    let at = |v: &Value, i: usize| v.get(i).and_then(Value::as_u64);
    match v {
        Value::Array(a) => a.iter().for_each(|x| refs(x, r)),
        Value::Object(o) => {
            for (k, x) in o {
                let (one, all, idx) = match k.as_str() {
                    "ty" | "fn_ty" | "Slice" | "OpaqueCast" | "Type" | "ZSTValue" => (Some((TY, x.as_u64())), false, None),
                    "fields" | "inputs_and_output" | "Tuple" => (None, true, None),
                    "Array" => (Some((TY, x.as_u64())), false, Some(0)),
                    "RawPtr" | "Pat" | "Value" | "VTable" | "Reborrow" => (None, false, Some(0)),
                    "Ref" | "Field" => (None, false, Some(1)),
                    "Cast" => (None, false, Some(2)),
                    "span" => (Some((SPAN, x.as_u64())), false, None),
                    "inst" | "resolved" | "glue" => (Some((INST, x.as_u64())), false, None),
                    "ptrs" => {
                        x.as_array().into_iter().flatten().filter_map(|p| at(p, 1)).for_each(|id| {
                            r[ALLOC].insert(id);
                        });
                        (None, false, None)
                    }
                    _ => (None, false, None),
                };
                if let Some((table, Some(id))) = one {
                    r[table].insert(id);
                }
                if all {
                    r[TY].extend(x.as_array().into_iter().flatten().filter_map(Value::as_u64));
                }
                if let Some(id) = idx.and_then(|i| at(x, i)) {
                    r[TY].insert(id);
                }
                refs(x, r);
            }
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::dangling;
    use serde_json::json;

    /// A tiny dump in the spec's shape: a body assigning an `Aggregate` of `Adt` kind, whose args
    /// name Ty 7, and an allocation whose provenance points at an allocation that points at 31.
    fn dump(adt_arg: u64, inner_ptr: u64) -> serde_json::Value {
        let body = json!({"blocks": [{"statements": [{"kind": {"Assign": [
            {"local": 1, "projection": [{"Field": [0, 4]}]},
            {"Aggregate": [{"Adt": [12, 0, [{"Type": adt_arg}, {"Lifetime": {"kind": "ReErased"}}], null, null]}, []]}]},
            "span": 50}],
            "terminator": {"kind": {"Drop": {"place": {"local": 1, "projection": []}, "target": 1, "unwind": "Continue"}}, "span": 51}}],
            "locals": [{"ty": 3, "span": 50, "mutability": "Mut"}, {"ty": 4, "span": 51, "mutability": "Not"}],
            "arg_count": 0, "var_debug_info": [], "spread_arg": null, "span": 50});
        let alloc = |ptr: u64| json!({"Memory": {"bytes": [1, null], "provenance": {"ptrs": [[0, ptr]]}, "align": 8, "mutability": "Not"}});
        json!({"crate": "kc",
            "items": [{"def": 0, "name": "kc::f", "inst": 9, "attrs": ["#[ct::secret(a)]"]}],
            "insts": [{"id": 9, "name": "kc::f", "key": "kc::f", "krate": "kc", "kind": "Item", "body": body,
                       "fn_sig": {"inputs_and_output": [3], "c_variadic": false, "safety": "Safe", "abi": "Rust"}},
                      {"id": 10, "name": "drop_in_place", "key": "drop_in_place", "krate": "core", "kind": "Shim", "body": null, "fn_sig": null}],
            "calls": [],
            "drops": [{"ty": 4, "glue": 10, "empty": true}],
            "tys": [{"id": 3, "kind": {"RigidTy": {"Tuple": []}}},
                    {"id": 4, "kind": {"RigidTy": {"Ref": [{"kind": "ReErased"}, 5, "Not"]}}},
                    {"id": 5, "kind": {"RigidTy": {"Array": [6, {"kind": {"Value": [7, {"bytes": [2], "provenance": {"ptrs": []}, "align": 8, "mutability": "Not"}]}, "id": 0}]}}},
                    {"id": 6, "kind": {"RigidTy": {"Uint": "U8"}}},
                    {"id": 7, "kind": {"RigidTy": {"Uint": "Usize"}}}],
            "adts": [],
            "consts": [{"id": 0, "usize": 2}],
            "layouts": [{"ty": 6, "shape": {"fields": "Primitive", "variants": {"Single": {"index": 0}}, "abi": {"Scalar": {"Initialized": {"value": {"Int": {"length": "I8", "signed": false}}, "valid_range": {"start": 0, "end": 255}}}}, "abi_align": 1, "size": {"num_bits": 8}}}],
            "allocs": [{"id": 30, "alloc": alloc(inner_ptr)}, {"id": 31, "alloc": alloc(30)}],
            "spans": [{"id": 50, "file": "kc.rs", "line": 1}, {"id": 51, "file": "kc.rs", "line": 2}]})
    }

    #[test]
    fn closed_dump_has_no_dangling_id() {
        assert_eq!(dangling(&dump(7, 31)), Vec::<String>::new());
    }

    #[test]
    fn dangling_ty_in_aggregate_args_and_alloc_in_nested_provenance() {
        assert_eq!(dangling(&dump(8, 32)), ["tys 8", "allocs 32"]);
    }

    #[test]
    fn each_table_is_checked() {
        let mut d = dump(7, 31);
        d["spans"].as_array_mut().unwrap().pop();
        d["insts"].as_array_mut().unwrap().pop();
        d["tys"].as_array_mut().unwrap().remove(2); // Ty 5, named only by Ty 4's `Ref`
        assert_eq!(dangling(&d), ["tys 5", "spans 51", "insts 10"]);
        let mut d = dump(7, 31);
        d["tys"].as_array_mut().unwrap().remove(3); // Ty 6, named by an `Array` and a layout
        assert_eq!(dangling(&d), ["tys 6"]);
    }

    #[test]
    fn non_numbers_at_ty_positions_are_not_references() {
        let d = json!({"tys": [], "x": [{"Ref": [{"kind": "ReErased"}, "Shared", {"local": 0}]},
                                        {"fields": {"Arbitrary": {"offsets": [0, 8]}}},
                                        {"Array": {"stride": 8, "count": 2}}]});
        assert_eq!(dangling(&d), Vec::<String>::new());
    }
}
