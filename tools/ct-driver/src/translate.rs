//! MIR → ctcore translator (TRUSTED, unverified): the thin, mechanical, fail-closed mapping of
//! the design spec's §Front end table. Each `match` arm below is one row of that table (a row
//! that lists several MIR forms gets one arm per form). Every MIR form not in the table is a
//! `TrErr::Unsupported` carrying its span; no catch-all arm produces core code.
//!
//! Structure: `translate_closure` resolves one manifest root, then translates the bodies it
//! reaches by the spec's callee lookup order (`intr` line, else internal fn, else `Unresolved`).
//! Fn 0 of the returned `Program` is the root. MIR locals and blocks map 1:1 to core locals and
//! blocks; a block not reachable along normal (non-unwind) edges becomes an empty `Abort` block.
//!
//! It applies no label rule: `ct::` attributes are only parsed into `FnInfo::decl` (or
//! `FnInfo::attr_err`), and check mode (`main.rs`) decides which are errors.
//!
//! Labels: only `secret(..)` is enforced (via `decl` and `check_program`'s `decl_ok`). A
//! `public(..)` name is a declaration only; a declared-public param that inference makes secret
//! is accepted. That is sound for constant time (the theorem's argument agreement just covers
//! that slot less), so never read `public(..)` as a checked guarantee that a value is public.
use crate::manifest::Manifest;
use crate::{bind_key, ct_key, is_internal, key_id, local_fns, normal_blocks, pick_roots, strip_generic_args, KeyId};
use ctcore as c;
use rustc_public::mir::alloc::GlobalAlloc;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    AggregateKind, BinOp, BorrowKind, CastKind, Mutability, Operand, Place, PointerCoercion, ProjectionElem, Rvalue, Statement,
    StatementKind, Terminator, TerminatorKind, UnOp,
};
use rustc_public::ty::{
    AdtDef, AdtKind, Allocation, ConstantKind, GenericArgs, MirConst, RigidTy, Span, Ty, UintTy, VariantIdx,
};
use rustc_public::CrateDef;
use rustc_public_bridge::IndexedVal;
use std::collections::{HashMap, HashSet};

/// What check mode and the report need about one translated fn (index = its core fn index).
pub struct FnInfo {
    /// `ct_key` of the instance.
    pub path: String,
    pub is_root: bool,
    /// One entry per MIR argument, `true` = declared secret; ghost/unit params are `false`.
    /// `None` when the fn has no `ct::` attribute and no manifest `label` line (or they don't
    /// parse; then `attr_err` says why).
    pub decl: Option<Vec<bool>>,
    /// One per MIR argument, from `var_debug_info`; `""` when the argument has no plain name.
    pub param_names: Vec<String>,
    /// Per block, the terminator's `<file>:<line>`.
    pub block_spans: Vec<String>,
    /// `<file>:<line>` of each `Declassify` call in this fn.
    pub declassify_sites: Vec<String>,
    /// Per block, per core statement, its `<file>:<line>` (dropped MIR statements have none).
    pub stmt_spans: Vec<Vec<String>>,
    /// Why the `ct::` attributes or the `label` line don't parse (unknown attribute, unknown,
    /// duplicate or missing parameter name).
    pub attr_err: Option<String>,
}

pub enum TrErr {
    Unsupported { path: String, what: String, span: String },
    Unresolved { path: String, callee: String, span: String },
    Attr { path: String, msg: String },
    Root { path: String, msg: String },
}

/// Translates the closure of manifest root `root` (a `ct_key` in the crate being compiled).
pub fn translate_closure(m: &Manifest, root: &str) -> Result<(c::Program, Vec<FnInfo>), Vec<TrErr>> {
    let krate = rustc_public::local_crate().name;
    let r = root.to_string();
    let inst = match pick_roots(&krate, &[&r], &local_fns()) {
        Ok(v) => v[0],
        Err(msg) => return Err(vec![TrErr::Root { path: r, msg }]),
    };
    let mut tr = Tr { m, krate, index: HashMap::new(), order: vec![inst], by_key: HashMap::new(), errs: Vec::new() };
    tr.index.insert(inst, 0);
    let _ = bind_key(&mut tr.by_key, root, key_id(&tr.krate, m, &inst));
    let (mut fns, mut infos) = (Vec::new(), Vec::new());
    let mut i = 0;
    while i < tr.order.len() {
        let inst = tr.order[i];
        if let Some((b, info)) = tr.body(inst, i == 0) {
            fns.push(b);
            infos.push(info);
        }
        i += 1;
    }
    if tr.errs.is_empty() {
        Ok((c::Program { fns }, infos))
    } else {
        Err(tr.errs)
    }
}

/// The closure being translated: fn indices by instance, and the keys seen (`bind_key`: roots and
/// internal fns by instance, leaves and `intr` callees by def; a key naming two is an error).
struct Tr<'m> {
    m: &'m Manifest,
    krate: String,
    index: HashMap<Instance, usize>,
    order: Vec<Instance>,
    by_key: HashMap<String, KeyId>,
    errs: Vec<TrErr>,
}

/// One body being translated. `residue`: the fn-pointer-typed temporaries, which may only hold
/// the erased `Ghost(..)` argument (a `ClosureFnPointer` cast of a closure constant) and only
/// flow into a `GhostUnit` call; every other use reaches `place` and is rejected.
struct Cx<'b> {
    path: String,
    body: &'b rustc_public::mir::Body,
    residue: HashSet<usize>,
    span: String,
}

pub fn site(sp: &Span) -> String {
    format!("{}:{}", sp.get_filename(), sp.get_lines().start_line)
}

impl Tr<'_> {
    fn body(&mut self, inst: Instance, is_root: bool) -> Option<(c::Body, FnInfo)> {
        let path = ct_key(&inst);
        let Some(body) = inst.body() else {
            let span = site(&inst.def.span());
            self.errs.push(TrErr::Unsupported { path, what: "no MIR body".into(), span });
            return None;
        };
        let nargs = body.arg_locals().len();
        let residue = (nargs + 1..body.locals().len())
            .filter(|&l| matches!(body.locals()[l].ty.kind().rigid(), Some(RigidTy::FnPtr(_))))
            .collect();
        let mut cx = Cx { path: path.clone(), body: &body, residue, span: site(&body.span) };
        let n0 = self.errs.len();
        if body.spread_arg().is_some() {
            self.errs.push(cx.uns("a rust-call (closure) body".into()));
        }
        let mut locals = Vec::new();
        for (l, d) in body.locals().iter().enumerate() {
            cx.span = site(&d.span);
            match cx.local_ty(l, d.ty) {
                Ok(t) => locals.push(t),
                Err(e) => self.errs.push(e),
            }
        }
        let reach: HashSet<usize> = normal_blocks(&body).into_iter().collect();
        let (mut blocks, mut block_spans, mut stmt_spans, mut declassify_sites) = (vec![], vec![], vec![], vec![]);
        for (b, blk) in body.blocks.iter().enumerate() {
            block_spans.push(site(&blk.terminator.span));
            let (mut stmts, mut spans) = (vec![], vec![]);
            if !reach.contains(&b) {
                blocks.push(c::Block { stmts, term: c::Term::Abort });
                stmt_spans.push(spans);
                continue;
            }
            for s in &blk.statements {
                cx.span = site(&s.span);
                match cx.stmt(s) {
                    Ok(Some(st)) => {
                        stmts.push(st);
                        spans.push(cx.span.clone());
                    }
                    Ok(None) => {}
                    Err(e) => self.errs.push(e),
                }
            }
            cx.span = site(&blk.terminator.span);
            match self.term(&cx, &blk.terminator) {
                Ok((term, declass)) => {
                    if declass {
                        declassify_sites.push(cx.span.clone());
                    }
                    blocks.push(c::Block { stmts, term });
                }
                Err(e) => self.errs.push(e),
            }
            stmt_spans.push(spans);
        }
        // Param names from the argument locals' debug info (`argument_index` is 1-based).
        let param_names: Vec<String> = (1..=nargs)
            .map(|j| {
                let v = body.var_debug_info.iter().find(|v| v.argument_index == Some(j as u16) && v.local() == Some(j));
                v.map_or_else(String::new, |v| v.name.clone())
            })
            .collect();
        let ghost: Vec<bool> = (1..=nargs).map(|j| matches!(locals.get(j), Some(c::Ty::Unit))).collect();
        let mut attrs: Vec<String> =
            inst.def.all_tool_attrs().iter().map(|a| a.as_str().trim().to_string()).filter(|a| a.starts_with("#[ct::")).collect();
        let (decl, attr_err) = match self.m.labels.iter().find(|(p, _, _)| *p == path) {
            Some(_) if !attrs.is_empty() => (None, Some("both ct:: attributes and a manifest label line".to_string())),
            Some((_, s, p)) => {
                attrs.push(format!("#[ct::secret({})]", s.join(",")));
                attrs.push(format!("#[ct::public({})]", p.join(",")));
                split(labels(&attrs, &param_names, &ghost))
            }
            None => split(labels(&attrs, &param_names, &ghost)),
        };
        if self.errs.len() > n0 {
            return None;
        }
        let info = FnInfo { path, is_root, decl, param_names, block_spans, declassify_sites, stmt_spans, attr_err };
        Some((c::Body { nargs, locals, blocks }, info))
    }

    fn term(&mut self, cx: &Cx, t: &Terminator) -> Result<(c::Term, bool), TrErr> {
        let term = match &t.kind {
            TerminatorKind::Goto { target } => c::Term::Goto(*target),
            TerminatorKind::SwitchInt { discr, targets } => {
                c::Term::Switch(cx.operand(discr)?, targets.branches().collect(), targets.otherwise())
            }
            TerminatorKind::Assert { cond, expected, target, .. } => c::Term::Assert(cx.operand(cond)?, *expected, *target),
            TerminatorKind::Return => c::Term::Return,
            TerminatorKind::Unreachable => c::Term::Abort,
            TerminatorKind::Drop { place, target, .. } => {
                // Only drop glue that frees a `Vec` buffer, which the model does not observe.
                let ty = place.ty(cx.body.locals()).map_err(|e| cx.uns(format!("drop place type: {e}")))?;
                if !vec_of(ty, |e| int_ty(e).is_some()) {
                    return Err(cx.uns(format!("drop of {ty} (only Vec<int> drop glue is supported)")));
                }
                c::Term::Goto(*target)
            }
            TerminatorKind::Call { func, args, destination, target, .. } => return self.call(cx, func, args, destination, *target),
            TerminatorKind::Resume | TerminatorKind::Abort | TerminatorKind::InlineAsm { .. } => {
                return Err(cx.uns(format!("terminator {:?}", t.kind)));
            }
        };
        Ok((term, false))
    }

    /// The callee lookup order: an `intr` line; else an internal fn; else `Unresolved`.
    fn call(&mut self, cx: &Cx, func: &Operand, args: &[Operand], dst: &Place, target: Option<usize>) -> Result<(c::Term, bool), TrErr> {
        let Some(next) = target else { return Err(cx.uns("a diverging call".into())) };
        let fty = func.ty(cx.body.locals()).map_err(|e| cx.uns(format!("callee type: {e}")))?;
        let Some((def, gargs)) = fty.kind().fn_def().map(|(d, a)| (d, a.clone())) else {
            return Err(cx.uns("a call through a fn pointer or closure value".into()));
        };
        let unresolved = |callee: String| TrErr::Unresolved { path: cx.path.clone(), callee, span: cx.span.clone() };
        let callee = Instance::resolve(def, &gargs).map_err(|_| unresolved(strip_generic_args(&def.name())))?;
        let key = ct_key(&callee);
        if let Err((d, prev)) = bind_key(&mut self.by_key, &key, key_id(&self.krate, self.m, &callee)) {
            let prev = prev.map_or_else(|| d.name(), |p| p.name());
            return Err(cx.uns(format!("ambiguous key {key}: reached as {prev} and {}", callee.name())));
        }
        if let Some((_, k)) = self.m.intr.iter().find(|(p, _)| *p == key) {
            cx.intr_types(k, args, dst)?;
            let ghost = matches!(k, c::Intrinsic::GhostUnit);
            let ops = args.iter().map(|a| if ghost { cx.ghost_operand(a) } else { cx.operand(a) }).collect::<Result<_, _>>()?;
            let term = c::Term::Call(c::Callee::Intr(intr_copy(k)), ops, cx.place(dst)?, next);
            return Ok((term, matches!(k, c::Intrinsic::Declassify)));
        }
        if is_internal(&self.krate, self.m, &callee) {
            if matches!(callee.ty().kind().rigid(), Some(RigidTy::Closure(..))) {
                return Err(cx.uns(format!("a call to closure {key}")));
            }
            let ops = args.iter().map(|a| cx.operand(a)).collect::<Result<_, _>>()?;
            let dst = cx.place(dst)?;
            let n = self.order.len();
            let g = *self.index.entry(callee).or_insert(n);
            if g == n {
                self.order.push(callee);
            }
            return Ok((c::Term::Call(c::Callee::Fn(g), ops, dst, next), false));
        }
        Err(unresolved(key))
    }
}

impl Cx<'_> {
    fn uns(&self, what: String) -> TrErr {
        TrErr::Unsupported { path: self.path.clone(), what, span: self.span.clone() }
    }

    fn local_ty(&self, l: usize, t: Ty) -> Result<c::Ty, TrErr> {
        if self.residue.contains(&l) {
            return Ok(c::Ty::Unit); // the Ghost residue's fn pointer (see `Cx`)
        }
        self.ty(t, 0)
    }

    /// Types map structurally. `depth` bounds recursive types (`struct T { v: Vec<T> }`).
    fn ty(&self, t: Ty, depth: usize) -> Result<c::Ty, TrErr> {
        if depth > 16 {
            return Err(self.uns(format!("type nested too deeply (recursive?): {t}")));
        }
        let kind = t.kind();
        let Some(r) = kind.rigid() else { return Err(self.uns(format!("non-rigid type {t}"))) };
        let sub = |t: Ty| self.ty(t, depth + 1).map(Box::new);
        Ok(match r {
            RigidTy::Bool | RigidTy::Int(_) | RigidTy::Uint(_) => c::Ty::Int(int_ty(t).unwrap()),
            RigidTy::Tuple(ts) if ts.is_empty() => c::Ty::Unit,
            RigidTy::Tuple(ts) => c::Ty::Tuple(ts.iter().map(|t| self.ty(*t, depth + 1)).collect::<Result<_, _>>()?),
            RigidTy::Adt(def, args) => return self.adt(*def, args, depth),
            RigidTy::Array(e, n) => c::Ty::Array(sub(*e)?, n.eval_target_usize().map_err(|e| self.uns(format!("array length: {e}")))?),
            RigidTy::Slice(e) => c::Ty::Slice(sub(*e)?),
            RigidTy::Ref(_, p, Mutability::Not) => c::Ty::Shr(sub(*p)?),
            RigidTy::Ref(_, p, Mutability::Mut) => c::Ty::Mut(sub(*p)?),
            // ZST fn items, and the type of ghost closures (calling a closure is rejected)
            RigidTy::FnDef(..) | RigidTy::Closure(..) => c::Ty::Unit,
            _ => return Err(self.uns(format!("type {t}"))),
        })
    }

    fn adt(&self, def: AdtDef, args: &GenericArgs, depth: usize) -> Result<c::Ty, TrErr> {
        let name = def.name();
        match name.as_str() {
            "vstd::prelude::Ghost" | "vstd::prelude::Tracked" => return Ok(c::Ty::Unit),
            "std::vec::Vec" => {
                let e = args.0.first().and_then(|a| a.ty()).ok_or_else(|| self.uns("Vec without element type".into()))?;
                return Ok(c::Ty::Vec(Box::new(self.ty(*e, depth + 1)?)));
            }
            // interior mutability
            "std::cell::UnsafeCell" | "core::cell::UnsafeCell" => return Err(self.uns(format!("interior mutability ({name})"))),
            _ => {}
        }
        if def.is_box() || def.kind() == AdtKind::Union {
            return Err(self.uns(format!("Box or union type {name}")));
        }
        // Core `Discr` reads the variant index; MIR switches on discriminant values.
        let n = def.num_variants();
        if def.kind() == AdtKind::Enum && (0..n).any(|i| def.discriminant_for_variant(VariantIdx::to_val(i)).val != i as u128) {
            return Err(self.uns(format!("enum {name} with explicit discriminants")));
        }
        let mut vs = Vec::new();
        for v in def.variants_iter() {
            let fs = v.fields().iter().map(|f| self.ty(rustc_public::CrateDefType::ty_with_args(f, args), depth + 1)).collect::<Result<_, _>>()?;
            vs.push(fs);
        }
        Ok(c::Ty::Adt(vs))
    }

    fn int(&self, t: Ty) -> Result<c::IntTy, TrErr> {
        int_ty(t).ok_or_else(|| self.uns(format!("non-integer operand type {t}")))
    }

    fn op_ty(&self, o: &Operand) -> Result<Ty, TrErr> {
        o.ty(self.body.locals()).map_err(|e| self.uns(format!("operand type: {e}")))
    }

    fn place(&self, p: &Place) -> Result<c::Place, TrErr> {
        if self.residue.contains(&p.local) {
            return Err(self.uns("a fn-pointer local used outside the Ghost residue".into()));
        }
        let mut proj = Vec::new();
        for e in &p.projection {
            proj.push(match e {
                ProjectionElem::Deref => c::Proj::Deref,
                ProjectionElem::Field(i, _) => c::Proj::Field(*i),
                ProjectionElem::Index(l) => c::Proj::Index(*l),
                ProjectionElem::ConstantIndex { offset, from_end: false, .. } => c::Proj::ConstIndex(*offset),
                ProjectionElem::Downcast(v) => c::Proj::Downcast(v.to_index()),
                _ => return Err(self.uns(format!("projection {e:?}"))),
            });
        }
        Ok(c::Place { local: p.local, proj })
    }

    fn operand(&self, o: &Operand) -> Result<c::Operand, TrErr> {
        match o {
            Operand::Copy(p) | Operand::Move(p) => Ok(c::Operand::Copy(self.place(p)?)),
            Operand::Constant(k) => self.constant(&k.const_),
            Operand::RuntimeChecks(_) => Err(self.uns("a RuntimeChecks operand".into())),
        }
    }

    /// A `GhostUnit` argument: also a bare residue local (its value is never read).
    fn ghost_operand(&self, o: &Operand) -> Result<c::Operand, TrErr> {
        match o {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() && self.residue.contains(&p.local) => {
                Ok(c::Operand::Copy(c::Place { local: p.local, proj: vec![] }))
            }
            _ => self.operand(o),
        }
    }

    /// Scalars give `Const`; ZSTs (fn items, unit, `PhantomData`, `Ghost<_>`, closures) give
    /// `Lit(Unit)`; constant arrays and refs to them give `Lit(ConstVal)`, decoded little-endian.
    fn constant(&self, k: &MirConst) -> Result<c::Operand, TrErr> {
        let t = k.ty();
        match k.kind() {
            ConstantKind::ZeroSized => {
                self.ty(t, 0)?;
                Ok(c::Operand::Lit(c::ConstVal::Unit))
            }
            ConstantKind::Allocated(a) => match self.ty(t, 0)? {
                c::Ty::Int(it) => Ok(c::Operand::Const(it, self.scalar(a, 0, t)?)),
                c::Ty::Unit if a.bytes.is_empty() => Ok(c::Operand::Lit(c::ConstVal::Unit)),
                _ => Ok(c::Operand::Lit(self.const_val(t, a, 0, 0)?)),
            },
            _ => Err(self.uns(format!("unevaluated constant of type {t}"))),
        }
    }

    fn scalar(&self, a: &Allocation, off: usize, t: Ty) -> Result<u128, TrErr> {
        let w = int_bytes(t).ok_or_else(|| self.uns(format!("constant of type {t}")))?;
        if a.provenance.ptrs.iter().any(|(o, _)| (off..off + w).contains(o)) {
            return Err(self.uns("pointer in an integer constant".into()));
        }
        a.read_partial_uint(off..off + w).map_err(|e| self.uns(format!("constant: {e}")))
    }

    /// Arrays of ints (nested allowed) and shared refs to them.
    fn const_val(&self, t: Ty, a: &Allocation, off: usize, depth: usize) -> Result<c::ConstVal, TrErr> {
        if depth > 16 {
            return Err(self.uns("constant nested too deeply".into()));
        }
        match t.kind().rigid() {
            Some(RigidTy::Bool | RigidTy::Int(_) | RigidTy::Uint(_)) => Ok(c::ConstVal::Int(self.scalar(a, off, t)?)),
            Some(RigidTy::Array(e, n)) => {
                let n = n.eval_target_usize().map_err(|e| self.uns(format!("array length: {e}")))? as usize;
                let w = size_of(*e).ok_or_else(|| self.uns(format!("constant array of {e}")))?;
                (0..n).map(|i| self.const_val(*e, a, off + i * w, depth + 1)).collect::<Result<_, _>>().map(c::ConstVal::Arr)
            }
            Some(RigidTy::Ref(_, p, Mutability::Not)) if matches!(p.kind().rigid(), Some(RigidTy::Array(..))) => {
                let prov = a.provenance.ptrs.iter().find(|(o, _)| *o == off).ok_or_else(|| self.uns("dangling constant ref".into()))?;
                let GlobalAlloc::Memory(inner) = GlobalAlloc::from(prov.1 .0) else {
                    return Err(self.uns("constant ref to a non-memory allocation".into()));
                };
                let at = a.read_partial_uint(off..off + 8).map_err(|e| self.uns(format!("constant: {e}")))? as usize;
                Ok(c::ConstVal::Shr(Box::new(self.const_val(*p, &inner, at, depth + 1)?)))
            }
            _ => Err(self.uns(format!("constant of type {t}"))),
        }
    }

    fn stmt(&self, s: &Statement) -> Result<Option<c::Stmt>, TrErr> {
        Ok(Some(match &s.kind {
            StatementKind::Assign(p, rv @ Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::ClosureFnPointer(_)), ..)) => {
                if !(p.projection.is_empty() && self.residue.contains(&p.local)) {
                    return Err(self.uns("a closure-to-fn-pointer cast outside the Ghost residue".into()));
                }
                c::Stmt::Assign(c::Place { local: p.local, proj: vec![] }, self.rvalue(rv)?)
            }
            StatementKind::Assign(p, rv) => c::Stmt::Assign(self.place(p)?, self.rvalue(rv)?),
            StatementKind::SetDiscriminant { place, variant_index } => c::Stmt::SetDiscr(self.place(place)?, variant_index.to_index()),
            StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::Nop
            | StatementKind::FakeRead(..)
            | StatementKind::PlaceMention(_)
            | StatementKind::AscribeUserType { .. }
            | StatementKind::Coverage(_)
            | StatementKind::ConstEvalCounter => return Ok(None),
            StatementKind::Intrinsic(_) => return Err(self.uns(format!("statement {:?}", s.kind))),
        }))
    }

    fn rvalue(&self, rv: &Rvalue) -> Result<c::Rvalue, TrErr> {
        let lit_unit = c::Rvalue::Use(c::Operand::Lit(c::ConstVal::Unit));
        Ok(match rv {
            Rvalue::Use(o, _) => c::Rvalue::Use(self.operand(o)?),
            Rvalue::BinaryOp(op, a, b) => c::Rvalue::Bin(self.binop(*op)?, self.int(self.op_ty(a)?)?, self.operand(a)?, self.operand(b)?),
            Rvalue::UnaryOp(UnOp::Not, o) => c::Rvalue::Un(c::UnOp::Not, self.int(self.op_ty(o)?)?, self.operand(o)?),
            Rvalue::UnaryOp(UnOp::Neg, o) => c::Rvalue::Un(c::UnOp::Neg, self.int(self.op_ty(o)?)?, self.operand(o)?),
            Rvalue::UnaryOp(UnOp::PtrMetadata, o) => {
                // the length of a slice reference
                let t = self.op_ty(o)?;
                let slice_ref = matches!(t.kind().rigid(), Some(RigidTy::Ref(_, p, _)) if matches!(p.kind().rigid(), Some(RigidTy::Slice(_))));
                match o {
                    Operand::Copy(p) | Operand::Move(p) if slice_ref => c::Rvalue::Len(self.place(p)?),
                    _ => return Err(self.uns(format!("PtrMetadata of {t}"))),
                }
            }
            Rvalue::Len(p) => c::Rvalue::Len(self.place(p)?),
            Rvalue::Cast(CastKind::IntToInt, o, to) => c::Rvalue::Cast(self.int(self.op_ty(o)?)?, self.int(*to)?, self.operand(o)?),
            Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize), o, _) => c::Rvalue::Use(self.operand(o)?),
            Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::ClosureFnPointer(_)), o, _) => {
                // the erased `Ghost(..)` argument: a closure constant; the dst is checked in `stmt`
                let closure = matches!(o, Operand::Constant(k) if matches!(k.const_.kind(), ConstantKind::ZeroSized)
                    && matches!(k.const_.ty().kind().rigid(), Some(RigidTy::Closure(..))));
                if !closure {
                    return Err(self.uns("a fn-pointer cast of a non-constant closure".into()));
                }
                lit_unit
            }
            Rvalue::Aggregate(AggregateKind::Tuple, ops) => c::Rvalue::Aggregate(c::AggKind::Tuple, self.operands(ops)?),
            Rvalue::Aggregate(AggregateKind::Array(_), ops) => c::Rvalue::Aggregate(c::AggKind::Array, self.operands(ops)?),
            Rvalue::Aggregate(AggregateKind::Adt(_, v, _, _, None), ops) => c::Rvalue::Aggregate(c::AggKind::Adt(v.to_index()), self.operands(ops)?),
            Rvalue::Aggregate(AggregateKind::Closure(..), _) => lit_unit, // ghost closures only; calling one is rejected
            Rvalue::Repeat(o, n) => {
                c::Rvalue::Repeat(self.operand(o)?, n.eval_target_usize().map_err(|e| self.uns(format!("repeat count: {e}")))?)
            }
            Rvalue::Ref(_, BorrowKind::Shared, p) => c::Rvalue::RefShr(self.place(p)?),
            Rvalue::Ref(_, BorrowKind::Mut { .. }, p) => c::Rvalue::RefMut(self.place(p)?),
            Rvalue::Discriminant(p) => c::Rvalue::Discr(self.place(p)?),
            Rvalue::CopyForDeref(p) => c::Rvalue::Use(c::Operand::Copy(self.place(p)?)),
            _ => return Err(self.uns(format!("rvalue {rv:?}"))),
        })
    }

    fn operands(&self, ops: &[Operand]) -> Result<Vec<c::Operand>, TrErr> {
        ops.iter().map(|o| self.operand(o)).collect()
    }

    /// Wrapping (non-overflow) operators only: no `*Unchecked`, `Cmp` or `Offset`.
    fn binop(&self, op: BinOp) -> Result<c::BinOp, TrErr> {
        Ok(match op {
            BinOp::Add => c::BinOp::Add,
            BinOp::Sub => c::BinOp::Sub,
            BinOp::Mul => c::BinOp::Mul,
            BinOp::Div => c::BinOp::Div,
            BinOp::Rem => c::BinOp::Rem,
            BinOp::BitXor => c::BinOp::BitXor,
            BinOp::BitAnd => c::BinOp::BitAnd,
            BinOp::BitOr => c::BinOp::BitOr,
            BinOp::Shl => c::BinOp::Shl,
            BinOp::Shr => c::BinOp::Shr,
            BinOp::Eq => c::BinOp::Eq,
            BinOp::Ne => c::BinOp::Ne,
            BinOp::Lt => c::BinOp::Lt,
            BinOp::Le => c::BinOp::Le,
            BinOp::Gt => c::BinOp::Gt,
            BinOp::Ge => c::BinOp::Ge,
            _ => return Err(self.uns(format!("binary operator {op:?}"))),
        })
    }

    /// The width/type-arg guard. `ct_key` drops generic args, so one `intr` line covers every
    /// instantiation of its def; a call is mapped only at the intrinsic's declared types: the
    /// argument and result types of its spec row, with element type `u8` for the Vec/slice
    /// intrinsics and `ty` for `Wrapping(op, ty)`.
    // ponytail: element type is u8 only (the only one in the crypto census); widen per intrinsic
    // when a checked crate needs another, the Vec rows are element-agnostic in sem.rs.
    fn intr_types(&self, k: &c::Intrinsic, args: &[Operand], dst: &Place) -> Result<(), TrErr> {
        use c::Intrinsic as I;
        let a = args.iter().map(|o| self.op_ty(o)).collect::<Result<Vec<_>, _>>()?;
        let d = dst.ty(self.body.locals()).map_err(|e| self.uns(format!("call destination type: {e}")))?;
        let (u8_, usize_, unit) = (|t: Ty| is_uint(t, UintTy::U8), |t: Ty| is_uint(t, UintTy::Usize), |t: Ty| matches!(t.kind().rigid(), Some(RigidTy::Tuple(ts)) if ts.is_empty()));
        let vec_u8 = |t: Ty| vec_of(t, u8_);
        let slice_u8 = |t: Ty| matches!(t.kind().rigid(), Some(RigidTy::Slice(e)) if u8_(*e));
        let array_u8 = |t: Ty| matches!(t.kind().rigid(), Some(RigidTy::Array(e, _)) if u8_(*e));
        let ok = match (k, &a[..]) {
            (I::Declassify, [x]) => *x == d,
            (I::GhostUnit, _) => matches!(self.ty(d, 0), Ok(c::Ty::Unit)),
            (I::VecNew, []) => vec_u8(d),
            (I::VecWithCapacity, [n]) => usize_(*n) && vec_u8(d),
            (I::VecPush, [v, x]) => ref_to(*v, Mutability::Mut, vec_u8) && u8_(*x) && unit(d),
            (I::VecExtendFromSlice, [v, s]) => ref_to(*v, Mutability::Mut, vec_u8) && ref_to(*s, Mutability::Not, slice_u8) && unit(d),
            (I::VecAsSlice, [v]) => ref_to(*v, Mutability::Not, vec_u8) && ref_to(d, Mutability::Not, slice_u8),
            (I::ArrayAsSlice, [r]) => ref_to(*r, Mutability::Not, array_u8) && ref_to(d, Mutability::Not, slice_u8),
            (I::VecLen, [v]) => ref_to(*v, Mutability::Not, vec_u8) && usize_(d),
            (I::VecSet, [v, i, x]) => ref_to(*v, Mutability::Mut, vec_u8) && usize_(*i) && u8_(*x) && unit(d),
            (I::VecIndex, [v, i]) => ref_to(*v, Mutability::Not, vec_u8) && usize_(*i) && ref_to(d, Mutability::Not, u8_),
            (I::SliceSubrange, [s, lo, hi]) => {
                ref_to(*s, Mutability::Not, slice_u8) && usize_(*lo) && usize_(*hi) && ref_to(d, Mutability::Not, slice_u8)
            }
            (I::SliceToVec, [s]) => ref_to(*s, Mutability::Not, slice_u8) && vec_u8(d),
            (I::Wrapping(op, it), [x, y]) => {
                let is = |t: Ty| int_ty(t).is_some_and(|u| same_int(&u, it));
                let shift = matches!(op, c::BinOp::Shl | c::BinOp::Shr);
                is(*x) && (is(*y) || (shift && int_ty(*y).is_some())) && is(d)
            }
            _ => false,
        };
        if ok {
            Ok(())
        } else {
            let a: Vec<String> = a.iter().map(|t| t.to_string()).collect();
            Err(self.uns(format!("intrinsic {} reached at types ({}) -> {d}, not its declared types", intr_name(k), a.join(", "))))
        }
    }
}

fn split(r: Result<Option<Vec<bool>>, String>) -> (Option<Vec<bool>>, Option<String>) {
    match r {
        Ok(d) => (d, None),
        Err(e) => (None, Some(e)),
    }
}

/// The `ct::` attributes of a fn (pretty-printed, e.g. `#[ct::secret(k, n)]`), as `decl`: one
/// entry per param, `true` = secret. `Ok(None)` when there are none. Every non-ghost param must be
/// named exactly once across `secret(..)`/`public(..)`; bare `ct::public` names them all. Errors:
/// an unknown `ct::` attribute, an unknown or ghost name, a name twice, a param not named.
/// Label lines are rendered as these attributes, so they get the same check.
pub fn labels(attrs: &[String], names: &[String], ghost: &[bool]) -> Result<Option<Vec<bool>>, String> {
    if attrs.is_empty() {
        return Ok(None);
    }
    let mut seen: Vec<Option<bool>> = vec![None; names.len()];
    for a in attrs {
        let inner = a.strip_prefix("#[ct::").and_then(|s| s.strip_suffix(']')).ok_or_else(|| format!("malformed attribute {a}"))?;
        let (name, list) = match inner.split_once('(') {
            Some((n, rest)) => (n.trim(), Some(rest.strip_suffix(')').ok_or_else(|| format!("malformed attribute {a}"))?)),
            None => (inner.trim(), None),
        };
        let secret = match name {
            "secret" => true,
            "public" => false,
            _ => return Err(format!("unknown attribute ct::{name}")),
        };
        let idx: Vec<usize> = match list {
            None if !secret => (0..names.len()).filter(|&j| !ghost[j]).collect(),
            None => return Err("ct::secret needs a parameter list".into()),
            Some(l) => l
                .split(',')
                .map(str::trim)
                .filter(|n| !n.is_empty())
                .map(|n| match names.iter().position(|x| x == n) {
                    Some(j) if !ghost[j] => Ok(j),
                    Some(_) => Err(format!("parameter {n} is ghost/unit-typed and takes no label")),
                    None => Err(format!("unknown parameter name {n}")),
                })
                .collect::<Result<_, _>>()?,
        };
        for j in idx {
            if seen[j].replace(secret).is_some() {
                return Err(format!("parameter {} named twice", names[j]));
            }
        }
    }
    if let Some(j) = (0..names.len()).find(|&j| !ghost[j] && seen[j].is_none()) {
        return Err(format!("parameter {} (#{}) not named", names[j], j + 1));
    }
    Ok(Some(seen.iter().map(|s| *s == Some(true)).collect()))
}

pub fn int_ty(t: Ty) -> Option<c::IntTy> {
    use rustc_public::ty::IntTy as S;
    Some(match t.kind().rigid()? {
        RigidTy::Bool => c::IntTy::Bool,
        RigidTy::Uint(UintTy::U8) => c::IntTy::U8,
        RigidTy::Uint(UintTy::U16) => c::IntTy::U16,
        RigidTy::Uint(UintTy::U32) => c::IntTy::U32,
        RigidTy::Uint(UintTy::U64) => c::IntTy::U64,
        RigidTy::Uint(UintTy::U128) => c::IntTy::U128,
        RigidTy::Uint(UintTy::Usize) => c::IntTy::Usize,
        RigidTy::Int(S::I8) => c::IntTy::I8,
        RigidTy::Int(S::I16) => c::IntTy::I16,
        RigidTy::Int(S::I32) => c::IntTy::I32,
        RigidTy::Int(S::I64) => c::IntTy::I64,
        RigidTy::Int(S::I128) => c::IntTy::I128,
        RigidTy::Int(S::Isize) => c::IntTy::Isize,
        _ => return None,
    })
}

fn int_bytes(t: Ty) -> Option<usize> {
    match t.kind().rigid()? {
        RigidTy::Bool => Some(1),
        RigidTy::Uint(u) => Some(u.num_bytes()),
        RigidTy::Int(i) => Some(i.num_bytes()),
        _ => None,
    }
}

fn size_of(t: Ty) -> Option<usize> {
    match t.kind().rigid()? {
        RigidTy::Array(e, n) => Some(size_of(*e)? * n.eval_target_usize().ok()? as usize),
        _ => int_bytes(t),
    }
}

fn is_uint(t: Ty, u: UintTy) -> bool {
    matches!(t.kind().rigid(), Some(RigidTy::Uint(x)) if *x == u)
}

/// `Vec<E>` with `elem(E)`.
fn vec_of(t: Ty, elem: impl Fn(Ty) -> bool) -> bool {
    match t.kind().rigid() {
        Some(RigidTy::Adt(def, args)) if def.name() == "std::vec::Vec" => args.0.first().and_then(|a| a.ty()).is_some_and(|e| elem(*e)),
        _ => false,
    }
}

/// `&T` / `&mut T` with `pointee(T)`.
fn ref_to(t: Ty, m: Mutability, pointee: impl Fn(Ty) -> bool) -> bool {
    matches!(t.kind().rigid(), Some(RigidTy::Ref(_, p, x)) if *x == m && pointee(*p))
}

fn same_int(a: &c::IntTy, b: &c::IntTy) -> bool {
    std::mem::discriminant(a) == std::mem::discriminant(b)
}

/// `ctcore`'s types derive nothing (they are `verus!` exec types), so intrinsics are copied by hand.
fn intr_copy(k: &c::Intrinsic) -> c::Intrinsic {
    use c::Intrinsic as I;
    match k {
        I::Declassify => I::Declassify,
        I::GhostUnit => I::GhostUnit,
        I::VecNew => I::VecNew,
        I::VecWithCapacity => I::VecWithCapacity,
        I::VecPush => I::VecPush,
        I::VecExtendFromSlice => I::VecExtendFromSlice,
        I::VecAsSlice => I::VecAsSlice,
        I::ArrayAsSlice => I::ArrayAsSlice,
        I::VecLen => I::VecLen,
        I::VecSet => I::VecSet,
        I::VecIndex => I::VecIndex,
        I::SliceSubrange => I::SliceSubrange,
        I::SliceToVec => I::SliceToVec,
        I::Wrapping(op, t) => I::Wrapping(binop_copy(op), intty_copy(t)),
    }
}

fn binop_copy(op: &c::BinOp) -> c::BinOp {
    use c::BinOp as B;
    match op {
        B::Add => B::Add,
        B::Sub => B::Sub,
        B::Mul => B::Mul,
        B::Div => B::Div,
        B::Rem => B::Rem,
        B::BitXor => B::BitXor,
        B::BitAnd => B::BitAnd,
        B::BitOr => B::BitOr,
        B::Shl => B::Shl,
        B::Shr => B::Shr,
        B::Eq => B::Eq,
        B::Ne => B::Ne,
        B::Lt => B::Lt,
        B::Le => B::Le,
        B::Gt => B::Gt,
        B::Ge => B::Ge,
    }
}

fn intty_copy(t: &c::IntTy) -> c::IntTy {
    use c::IntTy as T;
    match t {
        T::U8 => T::U8,
        T::U16 => T::U16,
        T::U32 => T::U32,
        T::U64 => T::U64,
        T::U128 => T::U128,
        T::Usize => T::Usize,
        T::I8 => T::I8,
        T::I16 => T::I16,
        T::I32 => T::I32,
        T::I64 => T::I64,
        T::I128 => T::I128,
        T::Isize => T::Isize,
        T::Bool => T::Bool,
    }
}

fn intr_name(k: &c::Intrinsic) -> &'static str {
    use c::Intrinsic as I;
    match k {
        I::Declassify => "Declassify",
        I::GhostUnit => "GhostUnit",
        I::VecNew => "VecNew",
        I::VecWithCapacity => "VecWithCapacity",
        I::VecPush => "VecPush",
        I::VecExtendFromSlice => "VecExtendFromSlice",
        I::VecAsSlice => "VecAsSlice",
        I::ArrayAsSlice => "ArrayAsSlice",
        I::VecLen => "VecLen",
        I::VecSet => "VecSet",
        I::VecIndex => "VecIndex",
        I::SliceSubrange => "SliceSubrange",
        I::SliceToVec => "SliceToVec",
        I::Wrapping(..) => "Wrapping",
    }
}

#[cfg(test)]
mod tests {
    use super::labels;

    fn l(attrs: &[&str], names: &[&str], ghost: &[bool]) -> Result<Option<Vec<bool>>, String> {
        let a: Vec<String> = attrs.iter().map(|s| s.to_string()).collect();
        let n: Vec<String> = names.iter().map(|s| s.to_string()).collect();
        labels(&a, &n, ghost)
    }

    #[test]
    fn labels_by_name_not_position() {
        let r = l(&["#[ct::secret(k)]", "#[ct::public(p)]"], &["p", "k"], &[false, false]);
        assert_eq!(r, Ok(Some(vec![false, true])));
        assert_eq!(l(&["#[ct::secret(a, b)]"], &["a", "b"], &[false, false]), Ok(Some(vec![true, true])));
        assert_eq!(l(&[], &["a"], &[false]), Ok(None));
    }

    #[test]
    fn bare_public_and_ghost_params() {
        assert_eq!(l(&["#[ct::public]"], &["a", "", "b"], &[false, true, false]), Ok(Some(vec![false, false, false])));
        // a ghost param need not (and may not) be named
        assert_eq!(l(&["#[ct::secret(k)]"], &["k", "g"], &[false, true]), Ok(Some(vec![true, false])));
        assert!(l(&["#[ct::secret(k, g)]"], &["k", "g"], &[false, true]).unwrap_err().contains("parameter g is ghost"));
    }

    #[test]
    fn label_errors() {
        let two = [false, false];
        for (attrs, what) in [
            (&["#[ct::secret(z)]"][..], "unknown parameter name z"),
            (&["#[ct::secret(a)]"][..], "parameter b (#2) not named"),
            (&["#[ct::secret(a)]", "#[ct::public(a, b)]"][..], "named twice"),
            (&["#[ct::secret(a, a)]", "#[ct::public(b)]"][..], "named twice"),
            (&["#[ct::public]", "#[ct::secret(a)]"][..], "named twice"),
            (&["#[ct::secrett(a, b)]"][..], "unknown attribute ct::secrett"),
            (&["#[ct::secret]", "#[ct::public(a, b)]"][..], "needs a parameter list"),
            (&["#[ct::secret(a, b"][..], "malformed"),
        ] {
            let e = l(attrs, &["a", "b"], &two).unwrap_err();
            assert!(e.contains(what), "{attrs:?}: {e} (wanted {what})");
        }
    }
}
