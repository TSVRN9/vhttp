//! ct-dump (TRUSTED, unverified, decision-free): the driver writes `$CT_OUT/mir-<crate>.json`, the spec's §Dump
//! object: rustc_public values and query answers, each `serde_json::to_string`'d, plus the tables that say what an
//! integer id denotes. Bodies: the closure from every monomorphic local fn item over every resolved callee and drop
//! glue, in any crate. Value conditions are only "already visited?", `null` for `None`/`Err`, the spec's selections,
//! structural matches past rustc_public visitor gaps, and the query preconditions noted inline. `dangling` re-reads
//! the output; the file gets its final name only if no id dangles.

use crate::ct_key;
use rustc_public::mir::alloc::{AllocId, GlobalAlloc};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::visit::Location;
use rustc_public::mir::{AggregateKind, Body, MirVisitor, ProjectionElem, Rvalue, TerminatorKind, VarDebugInfo};
use rustc_public::mir::VarDebugInfoContents;
use rustc_public::ty::{AdtDef, AdtKind, Allocation, ConstantKind, GenericArgs, MirConst, Pattern, RigidTy, Span, Ty};
use rustc_public::ty::{TyConst, TyConstId, TyConstKind, TyKind};
use rustc_public::visitor::{Visitable, Visitor};
use rustc_public::{CrateDef, CrateDefType, ItemKind};
use serde_json::Value;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::ops::ControlFlow;
use std::path::Path;

macro_rules! js { ($e:expr) => { serde_json::to_string(&$e).expect("serde_json::to_string") }; }

/// The output tables (rows as JSON text), the visited sets and the work lists.
#[derive(Default)]
struct Dump {
    insts: Vec<String>, calls: Vec<String>, drops: Vec<String>, tys: Vec<String>, adts: Vec<String>,
    consts: Vec<String>, layouts: Vec<String>, allocs: Vec<String>, spans: Vec<String>,
    seen_inst: HashSet<Instance>, seen_call: HashSet<Ty>, seen_drop: HashSet<Ty>, seen_ty: HashSet<Ty>,
    seen_const: HashSet<TyConstId>, seen_alloc: HashSet<AllocId>, seen_span: HashSet<Span>, seen_lay: HashSet<Ty>,
    adt_fields: HashMap<Ty, Vec<Ty>>,
    inst_work: Vec<Instance>, ty_work: Vec<Ty>, alloc_work: Vec<AllocId>, lay_work: Vec<Ty>,
}

/// Dumps crate `krate` to `out/mir-<krate>.json`. On a dangling id it fails, leaving only `mir-<krate>.json.tmp`.
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
        let (def, name, inst) = (js!(item.def_id()), js!(item.name()), js!(inst.map(|i| i.def)));
        items.push(format!(r#"{{"def":{def},"name":{name},"inst":{inst},"attrs":{}}}"#, js!(attrs)));
    }
    d.run()?;
    d.layouts();
    let mut text = format!(r#"{{"crate":{}"#, js!(krate));
    let tables = [
        ("items", &items), ("insts", &d.insts), ("calls", &d.calls), ("drops", &d.drops), ("tys", &d.tys),
        ("adts", &d.adts), ("consts", &d.consts), ("layouts", &d.layouts), ("allocs", &d.allocs), ("spans", &d.spans),
    ];
    for (name, rows) in tables {
        text += &format!(r#","{name}":[{}]"#, rows.join(","));
    }
    text += "}";
    let (file, tmp) = (out.join(format!("mir-{krate}.json")), out.join(format!("mir-{krate}.json.tmp")));
    std::fs::write(&tmp, &text).map_err(|e| format!("{}: {e}", tmp.display()))?;
    let v: Value = serde_json::from_str(&text).map_err(|e| format!("{}: re-read: {e}", tmp.display()))?;
    let bad = dangling(&v);
    if !bad.is_empty() {
        let first: Vec<&str> = bad.iter().take(10).map(|s| s.as_str()).collect();
        return Err(format!("{}: {} dangling ids, first: {}", tmp.display(), bad.len(), first.join(", ")));
    }
    std::fs::rename(&tmp, &file).map_err(|e| format!("{}: {e}", file.display()))
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
            let (id, file, line) = (js!(s), js!(s.get_filename()), js!(s.get_lines().start_line));
            self.spans.push(format!(r#"{{"id":{id},"file":{file},"line":{line}}}"#));
        }
    }

    fn instance(&mut self, i: Instance) -> Result<(), String> {
        let body = i.body();
        let sig = i.ty().kind().fn_sig().map(|s| s.skip_binder());
        let _ = sig.visit(self);
        if let Some(b) = &body {
            self.body(b)?;
        }
        let (id, def, name, key) = (js!(i.def), js!(i.def.def_id()), js!(i.name()), js!(ct_key(&i)));
        let (krate, kind, body, sig) = (js!(i.def.krate().name), js!(i.kind), js!(body), js!(sig));
        let row = format!(r#"{{"id":{id},"def":{def},"name":{name},"key":{key},"krate":{krate},"kind":{kind},"#);
        self.insts.push(format!(r#"{row}"body":{body},"fn_sig":{sig}}}"#));
        Ok(())
    }

    /// Every id in `b`, and a `calls`/`drops` row per `FnDef`-typed callee and dropped type, over all blocks.
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
                    let (fn_ty, def_name, args, r) = (js!(t), js!(def.name()), js!(args), js!(r.map(|r| r.def)));
                    let row = format!(r#"{{"fn_ty":{fn_ty},"def":{},"def_name":{def_name},"args":{args},"resolved":{r}}}"#, js!(def));
                    self.calls.push(row);
                }
                TerminatorKind::Drop { place, .. } => {
                    let t = place.ty(b.locals()).map_err(|e| format!("dropped place type: {e}"))?;
                    let _ = Visitor::visit_ty(self, &t);
                    if !self.seen_drop.insert(t) {
                        continue;
                    }
                    let g = Instance::resolve_drop_in_place(t);
                    self.inst(g);
                    let row = format!(r#"{{"ty":{},"glue":{},"empty":{}}}"#, js!(t), js!(g.def), js!(g.is_empty_shim()));
                    self.drops.push(row);
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn ty(&mut self, t: Ty) {
        let kind = t.kind();
        let _ = t.super_visit(self);
        match &kind {
            TyKind::RigidTy(RigidTy::Adt(def, args)) => self.adt(t, *def, args),
            TyKind::RigidTy(RigidTy::Pat(_, p)) => self.pat(p), // `Visitable for RigidTy` skips the pattern
            _ => {}
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
        let (ty, name, kind, is_box) = (js!(t), js!(def.name()), js!(kind), js!(def.is_box()));
        self.adts.push(format!(r#"{{"ty":{ty},"name":{name},"kind":{kind},"is_box":{is_box},"variants":[{}]}}"#, vs.join(",")));
    }

    fn pat(&mut self, p: &Pattern) {
        match p {
            Pattern::Range { start, end, .. } => { let _ = (Visitor::visit_const(self, start), Visitor::visit_const(self, end)); }
            Pattern::Or(ps) => ps.iter().for_each(|p| self.pat(p)),
            Pattern::NotNull => {}
        }
    }

    fn lay(&mut self, t: Ty) {
        if self.seen_lay.insert(t) {
            self.lay_work.push(t);
        }
    }

    /// `layouts`, after `run` (`adt_fields` complete): each allocated constant's type, then the types a value holds.
    /// Not `FnPtr` or `Dynamic`: they hold no value and sit under a binder, where `layout` ICEs on escaping bound vars.
    fn layouts(&mut self) {
        while let Some(t) = self.lay_work.pop() {
            let shape = t.layout().ok().map(|l| l.shape());
            self.layouts.push(format!(r#"{{"ty":{},"shape":{}}}"#, js!(t), js!(shape)));
            let held = match t.kind().rigid() {
                Some(RigidTy::Adt(..)) => self.adt_fields.get(&t).cloned().unwrap_or_default(),
                Some(RigidTy::Tuple(ts)) => ts.clone(),
                Some(RigidTy::Array(e, _) | RigidTy::Slice(e) | RigidTy::Pat(e, _)) => vec![*e],
                Some(RigidTy::Ref(_, e, _) | RigidTy::RawPtr(e, _)) => vec![*e],
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
            GlobalAlloc::TypeId { ty } => { let _ = Visitor::visit_ty(self, ty); }
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
            let row = format!(r#"{{"id":{},"usize":{}}}"#, js!(c.id), js!(c.eval_target_usize().ok()));
            self.consts.push(row);
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
                AggregateKind::Adt(_, _, a, ..) | AggregateKind::Closure(_, a) => self.visit_args(a, l),
                AggregateKind::Coroutine(_, a) | AggregateKind::CoroutineClosure(_, a) => self.visit_args(a, l),
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

/// The ids a dump references but does not define, as `"<table> <id>"`. The reference positions are read off
/// rustc_public's type definitions (`mir/body.rs`, `ty.rs`, `mir/alloc.rs`) and the spec's records, not off the walk
/// above, so a gap in the walk shows up here:
/// - Ty: the keys `ty`, `fn_ty` and the lists `fields`, `inputs_and_output`; the variants `Slice`, `OpaqueCast`,
///   `Type`, `ZSTValue`, `Array` (a number), each element of `Tuple`, and payload index 0 of `Array`, `RawPtr`,
///   `Pat`, `Value`, `VTable`, `Reborrow`, 1 of `Ref`, `Field`, 2 of `Cast`;
/// - TyConstId: the `id` of the `{kind, id}` TyConst at payload index 1 of `Array` and `Repeat`, under the variants
///   `Const` (`GenericArgKind`, `TermKind`) and `Ty` (`ConstantKind`), and under `Pattern::Range`'s `start`, `end`;
/// - AllocId: the second element of each `ptrs` pair (`ProvenanceMap`);
/// - Span: the key `span`; InstanceDef: the keys `inst`, `resolved`, `glue`.
///
/// A non-number at a Ty position (`Ref`'s `BorrowKind`, `FieldsShape::Array`'s object), or a TyConst position not
/// holding an object with a numeric `id` (`WrappingRange`'s `start`), is not a reference.
pub fn dangling(d: &Value) -> Vec<String> {
    let mut r: [BTreeSet<u64>; 5] = Default::default();
    refs(d, &mut r);
    let mut bad = Vec::new();
    for (k, table) in ["tys", "consts", "allocs", "spans", "insts"].iter().enumerate() {
        let def: BTreeSet<u64> = d[table].as_array().into_iter().flatten().filter_map(|e| e["id"].as_u64()).collect();
        bad.extend(r[k].difference(&def).map(|id| format!("{table} {id}")));
    }
    bad
}

const TY: usize = 0;
const CONST: usize = 1;
const ALLOC: usize = 2;
const SPAN: usize = 3;
const INST: usize = 4;

fn refs(v: &Value, r: &mut [BTreeSet<u64>; 5]) {
    let at = |v: &Value, i: usize| v.get(i).and_then(Value::as_u64);
    let cid = |c: Option<&Value>| c.filter(|c| c.is_object()).and_then(|c| c.get("id")).and_then(Value::as_u64);
    let list = |x: &Value| x.as_array().into_iter().flatten().filter_map(Value::as_u64).collect::<Vec<_>>();
    match v {
        Value::Array(a) => a.iter().for_each(|x| refs(x, r)),
        Value::Object(o) => {
            for (k, x) in o {
                let found: Vec<(usize, Option<u64>)> = match k.as_str() {
                    "ty" | "fn_ty" | "Slice" | "OpaqueCast" | "Type" | "ZSTValue" => vec![(TY, x.as_u64())],
                    "fields" | "inputs_and_output" | "Tuple" => list(x).into_iter().map(|id| (TY, Some(id))).collect(),
                    "Array" => vec![(TY, x.as_u64()), (TY, at(x, 0)), (CONST, cid(x.get(1)))],
                    "RawPtr" | "Pat" | "Value" | "VTable" | "Reborrow" => vec![(TY, at(x, 0))],
                    "Ref" | "Field" => vec![(TY, at(x, 1))],
                    "Cast" => vec![(TY, at(x, 2))],
                    "Repeat" => vec![(CONST, cid(x.get(1)))],
                    "Const" | "Ty" | "start" | "end" => vec![(CONST, cid(Some(x)))],
                    "ptrs" => x.as_array().into_iter().flatten().map(|p| (ALLOC, at(p, 1))).collect(),
                    "span" => vec![(SPAN, x.as_u64())],
                    "inst" | "resolved" | "glue" => vec![(INST, x.as_u64())],
                    _ => vec![],
                };
                for (table, id) in found {
                    r[table].extend(id);
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
    use serde_json::{json, Value};

    /// A tiny dump in the spec's shape: a body assigning an `Aggregate` of `Adt` kind, whose args name Ty 7, and an
    /// allocation whose provenance points at an allocation that points at 31. Ty 5 is `[u8; c0]`, Ty 8 a `u8` pattern
    /// type over `c1..=c2`.
    fn dump(adt_arg: u64, inner_ptr: u64) -> Value {
        let mem = |bytes: Value, ptrs: Value| json!({"bytes": bytes, "provenance": {"ptrs": ptrs}, "align": 8, "mutability": "Not"});
        let c = |id: u64, v: u64| json!({"kind": {"Value": [7, mem(json!([v]), json!([]))]}, "id": id});
        let place = json!({"local": 1, "projection": [{"Field": [0, 4]}]});
        let adt = json!({"Adt": [12, 0, [{"Type": adt_arg}, {"Lifetime": {"kind": "ReErased"}}], null, null]});
        let drop = json!({"Drop": {"place": {"local": 1, "projection": []}, "target": 1, "unwind": "Continue"}});
        let body = json!({
            "blocks": [{"statements": [{"kind": {"Assign": [place, {"Aggregate": [adt, []]}]}, "span": 50}],
                        "terminator": {"kind": drop, "span": 51}}],
            "locals": [{"ty": 3, "span": 50, "mutability": "Mut"}, {"ty": 4, "span": 51, "mutability": "Not"}],
            "arg_count": 0, "var_debug_info": [], "spread_arg": null, "span": 50});
        let sig = json!({"inputs_and_output": [3], "c_variadic": false, "safety": "Safe", "abi": "Rust"});
        let range = json!({"start": 0, "end": 255});
        let scalar = json!({"Initialized": {"value": {"Int": {"length": "I8", "signed": false}}, "valid_range": range}});
        let shape = json!({"fields": "Primitive", "variants": {"Single": {"index": 0}}, "abi": {"Scalar": scalar},
                           "abi_align": 1, "size": {"num_bits": 8}});
        json!({"crate": "kc",
            "items": [{"def": 0, "name": "kc::f", "inst": 9, "attrs": ["#[ct::secret(a)]"]}],
            "insts": [{"id": 9, "def": 0, "name": "kc::f", "key": "kc::f", "krate": "kc", "kind": "Item", "body": body,
                       "fn_sig": sig},
                      {"id": 10, "def": 5, "name": "drop_in_place", "key": "drop_in_place", "krate": "core", "kind": "Shim",
                       "body": null, "fn_sig": null}],
            "calls": [],
            "drops": [{"ty": 4, "glue": 10, "empty": true}],
            "tys": [{"id": 3, "kind": {"RigidTy": {"Tuple": []}}},
                    {"id": 4, "kind": {"RigidTy": {"Ref": [{"kind": "ReErased"}, 5, "Not"]}}},
                    {"id": 5, "kind": {"RigidTy": {"Array": [6, c(0, 2)]}}},
                    {"id": 6, "kind": {"RigidTy": {"Uint": "U8"}}},
                    {"id": 7, "kind": {"RigidTy": {"Uint": "Usize"}}},
                    {"id": 8, "kind": {"RigidTy": {"Pat": [6, {"Range": {"start": c(1, 1), "end": c(2, 9), "include_end": true}}]}}}],
            "adts": [],
            "consts": [{"id": 0, "usize": 2}, {"id": 1, "usize": 1}, {"id": 2, "usize": 9}],
            "layouts": [{"ty": 6, "shape": shape}],
            "allocs": [{"id": 30, "alloc": {"Memory": mem(json!([1, null]), json!([[0, inner_ptr]]))}},
                       {"id": 31, "alloc": {"Memory": mem(json!([1, null]), json!([[0, 30]]))}}],
            "spans": [{"id": 50, "file": "kc.rs", "line": 1}, {"id": 51, "file": "kc.rs", "line": 2}]})
    }

    fn rows<'a>(d: &'a mut Value, table: &str) -> &'a mut Vec<Value> {
        d[table].as_array_mut().unwrap()
    }

    #[test]
    fn closed_dump_has_no_dangling_id() {
        assert_eq!(dangling(&dump(7, 31)), Vec::<String>::new());
    }

    #[test]
    fn dangling_ty_in_aggregate_args_and_alloc_in_nested_provenance() {
        assert_eq!(dangling(&dump(9, 32)), ["tys 9", "allocs 32"]);
    }

    #[test]
    fn each_table_is_checked() {
        let mut d = dump(7, 31);
        rows(&mut d, "spans").pop();
        rows(&mut d, "insts").pop();
        rows(&mut d, "tys").remove(2); // Ty 5, named only by Ty 4's `Ref`
        assert_eq!(dangling(&d), ["tys 5", "spans 51", "insts 10"]);
        let mut d = dump(7, 31);
        rows(&mut d, "tys").remove(3); // Ty 6, named by an `Array`, a `Pat` and a layout
        assert_eq!(dangling(&d), ["tys 6"]);
    }

    #[test]
    fn dangling_ty_const_in_array_length_and_pattern_range() {
        let mut d = dump(7, 31);
        rows(&mut d, "consts").remove(0); // the `Array` length
        rows(&mut d, "consts").pop(); // the `Range` end
        assert_eq!(dangling(&d), ["consts 0", "consts 2"]);
    }

    #[test]
    fn non_references_at_reference_positions() {
        let d = json!({"tys": [], "consts": [], "x": [{"Ref": [{"kind": "ReErased"}, "Shared", {"local": 0}]},
                                                     {"fields": {"Arbitrary": {"offsets": [0, 8]}}},
                                                     {"Array": {"stride": 8, "count": 2}},
                                                     {"valid_range": {"start": 0, "end": 255}}]});
        assert_eq!(dangling(&d), Vec::<String>::new());
    }
}
