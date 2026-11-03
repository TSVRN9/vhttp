//! Core interpreter (unverified, test-only, NOT in the TCB): runs a translated `ctcore::Program`
//! on concrete values, for the selftest (translation validation by vectors). It mirrors
//! `crates/ctcore/src/sem.rs` construct for construct; each fn names the spec fn it mirrors.
//!
//! Differences that do not change results:
//! - frames are updated in place, and a run loops over blocks instead of recursing per block
//!   (`run_from`'s fuel is per activation, so the loop decrements its own copy);
//! - events are recorded only when asked (`trace`), since the selftest compares values;
//! - `binop`/`unop`/`cast` use Rust's own wrapping ops per `IntTy` (`Bool` is a 1-bit unsigned).
use ctcore as c;
use std::borrow::Cow;

/// `sem::Val`. `Mut` carries `sem::Loc` (root and path).
#[derive(Clone, PartialEq, Debug)]
pub enum IVal {
    Int(u128),
    Unit,
    Tup(Vec<IVal>),
    Adt(usize, Vec<IVal>),
    Arr(Vec<IVal>),
    Shr(Box<IVal>),
    Mut(IRoot, Vec<IPe>),
}

/// `sem::Root`.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum IRoot {
    Local(usize),
    Slot(usize),
}

/// `sem::PE`. `Index` keeps the full u128 read from the index local.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum IPe {
    Field(usize),
    Index(u128),
    Variant(usize),
}

/// `sem::Frame`.
#[derive(Clone, PartialEq, Debug)]
pub struct IFrame {
    pub locals: Vec<IVal>,
    pub slots: Vec<IVal>,
}

/// `sem::Event`.
#[derive(Clone, PartialEq, Debug)]
pub enum IEv {
    Cond(u128),
    Idx(u128),
    DivOps(u128, u128),
    Shamt(u128),
    Declass(IVal),
    Alloc(u128),
    Range(u128, u128),
}

/// `sem::USIZE_MAX`.
const USIZE_MAX: u128 = 0xffff_ffff_ffff_ffff;

/// `run_fn(p, f, init_entry(p, f, args, slots), fuel)`, returning local 0 and the steps. The
/// slot of each `&mut` parameter is that parameter's `args` entry (its pointee). The selftest
/// uses `run_fn` directly, since it also compares the final slots.
#[allow(dead_code)]
pub fn run(p: &c::Program, f: usize, args: Vec<IVal>, fuel: u64) -> Option<(IVal, u64)> {
    let slots = entry_slots(p, f, &args);
    let (fr, _, n) = run_fn(p, f, init_entry(p, f, &args, slots), fuel, false)?;
    Some((fr.locals.into_iter().next().unwrap_or(IVal::Unit), n))
}

/// Slot `j` = `args[j]` for each `Ty::Mut` param `1 + j`, `Unit` otherwise.
pub fn entry_slots(p: &c::Program, f: usize, args: &[IVal]) -> Vec<IVal> {
    let Some(b) = p.fns.get(f) else { return vec![] };
    (0..args.len()).map(|j| if is_mut_param(b, j) { args[j].clone() } else { IVal::Unit }).collect()
}

pub fn is_mut_param(b: &c::Body, j: usize) -> bool {
    j < b.nargs && matches!(b.locals.get(1 + j), Some(c::Ty::Mut(_)))
}

/// `sem::init_entry`.
pub fn init_entry(p: &c::Program, f: usize, args: &[IVal], slots: Vec<IVal>) -> IFrame {
    let Some(body) = p.fns.get(f) else { return IFrame { locals: vec![], slots } };
    let locals = (0..body.locals.len())
        .map(|i| {
            if 1 <= i && i <= body.nargs {
                if matches!(body.locals[i], c::Ty::Mut(_)) {
                    IVal::Mut(IRoot::Slot(i - 1), vec![])
                } else {
                    args.get(i - 1).cloned().unwrap_or(IVal::Unit)
                }
            } else {
                IVal::Unit
            }
        })
        .collect();
    IFrame { locals, slots }
}

/// `sem::run_fn`: the final frame, the events (empty unless `trace`) and the steps.
pub fn run_fn(p: &c::Program, f: usize, fr: IFrame, fuel: u64, trace: bool) -> Option<(IFrame, Vec<IEv>, u64)> {
    run_from(p, f, 0, fr, fuel, trace)
}

/// `sem::run_from`.
pub fn run_from(p: &c::Program, f: usize, b: usize, mut fr: IFrame, fuel: u64, trace: bool) -> Option<(IFrame, Vec<IEv>, u64)> {
    let mut it = In { p, ev: trace.then(Vec::new) };
    let n = it.run_from(f, b, &mut fr, fuel)?;
    Some((fr, it.ev.unwrap_or_default(), n))
}

struct In<'p> {
    p: &'p c::Program,
    ev: Option<Vec<IEv>>,
}

// ------------------------------------------------------------------ arithmetic

/// `sem::bits`.
fn bits(t: &c::IntTy) -> u32 {
    use c::IntTy as T;
    match t {
        T::U8 | T::I8 => 8,
        T::U16 | T::I16 => 16,
        T::U32 | T::I32 => 32,
        T::U64 | T::I64 | T::Usize | T::Isize => 64,
        T::U128 | T::I128 => 128,
        T::Bool => 1,
    }
}

/// `sem::uval` as a raw u128: the low `bits(t)` bits.
fn uval(t: &c::IntTy, a: u128) -> u128 {
    let n = bits(t);
    if n == 128 {
        a
    } else {
        a & ((1u128 << n) - 1)
    }
}

/// One binop at native type `$t` (unsigned twin `$u`, width `$n`), back to raw bits.
macro_rules! wop {
    ($op:expr, $a:expr, $b:expr, $t:ty, $u:ty, $n:expr) => {{
        let (x, y) = ($a as $u as $t, $b as $u as $t);
        let sh = (($b as $u) % ($n as $u)) as u32; // sem: uval(ty, b) % bits(ty)
        let r: $t = match $op {
            c::BinOp::Add => x.wrapping_add(y),
            c::BinOp::Sub => x.wrapping_sub(y),
            c::BinOp::Mul => x.wrapping_mul(y),
            c::BinOp::Div => if y == 0 { 0 } else { x.wrapping_div(y) },
            c::BinOp::Rem => if y == 0 { 0 } else { x.wrapping_rem(y) },
            c::BinOp::BitXor => x ^ y,
            c::BinOp::BitAnd => x & y,
            c::BinOp::BitOr => x | y,
            c::BinOp::Shl => x.wrapping_shl(sh),
            c::BinOp::Shr => x.wrapping_shr(sh),
            c::BinOp::Eq => (x == y) as $t,
            c::BinOp::Ne => (x != y) as $t,
            c::BinOp::Lt => (x < y) as $t,
            c::BinOp::Le => (x <= y) as $t,
            c::BinOp::Gt => (x > y) as $t,
            c::BinOp::Ge => (x >= y) as $t,
        };
        r as $u as u128
    }};
}

/// `sem::binop`.
pub fn binop(op: &c::BinOp, t: &c::IntTy, a: u128, b: u128) -> u128 {
    use c::IntTy as T;
    match t {
        T::U8 => wop!(op, a, b, u8, u8, 8),
        T::U16 => wop!(op, a, b, u16, u16, 16),
        T::U32 => wop!(op, a, b, u32, u32, 32),
        T::U64 | T::Usize => wop!(op, a, b, u64, u64, 64),
        T::U128 => wop!(op, a, b, u128, u128, 128),
        T::I8 => wop!(op, a, b, i8, u8, 8),
        T::I16 => wop!(op, a, b, i16, u16, 16),
        T::I32 => wop!(op, a, b, i32, u32, 32),
        T::I64 | T::Isize => wop!(op, a, b, i64, u64, 64),
        T::I128 => wop!(op, a, b, i128, u128, 128),
        // 1-bit unsigned: operate on the low bit, keep the low bit; shift amounts are % 1 = 0
        T::Bool => wop!(op, a & 1, b & 1, u8, u8, 1) & 1,
    }
}

/// `sem::unop`.
pub fn unop(op: &c::UnOp, t: &c::IntTy, a: u128) -> u128 {
    let x = uval(t, a);
    match op {
        c::UnOp::Not => uval(t, !x),
        // trunc(-ival(a)): two's complement negation of the low bits
        c::UnOp::Neg => uval(t, x.wrapping_neg()),
    }
}

/// `sem::cast`: sign-extend from a signed `from` (Rust `as` to i128), then truncate to `to`.
pub fn cast(from: &c::IntTy, to: &c::IntTy, a: u128) -> u128 {
    use c::IntTy as T;
    let v: u128 = match from {
        T::I8 => a as u8 as i8 as i128 as u128,
        T::I16 => a as u16 as i16 as i128 as u128,
        T::I32 => a as u32 as i32 as i128 as u128,
        T::I64 | T::Isize => a as u64 as i64 as i128 as u128,
        _ => uval(from, a),
    };
    uval(to, v)
}

/// `sem::as_int`.
fn as_int(v: &IVal) -> u128 {
    match v {
        IVal::Int(n) => *n,
        _ => 0,
    }
}

// ------------------------------------------------------------------ value navigation

/// `sem::get`, borrowing where it can.
fn get<'a>(v: Cow<'a, IVal>, e: &IPe) -> Cow<'a, IVal> {
    let unit = || Cow::Owned(IVal::Unit);
    match v {
        Cow::Borrowed(r) => match (r, e) {
            (IVal::Tup(vs) | IVal::Adt(_, vs), IPe::Field(i)) => vs.get(*i).map_or_else(unit, Cow::Borrowed),
            (IVal::Arr(vs), IPe::Index(i)) => idx(vs.len(), *i).map_or_else(unit, |i| Cow::Borrowed(&vs[i])),
            (IVal::Adt(_, vs), IPe::Variant(k)) => Cow::Owned(IVal::Adt(*k, vs.clone())),
            _ => unit(),
        },
        Cow::Owned(o) => match (o, e) {
            (IVal::Tup(mut vs) | IVal::Adt(_, mut vs), IPe::Field(i)) if *i < vs.len() => Cow::Owned(vs.swap_remove(*i)),
            (IVal::Arr(mut vs), IPe::Index(i)) if idx(vs.len(), *i).is_some() => Cow::Owned(vs.swap_remove(*i as usize)),
            (IVal::Adt(_, vs), IPe::Variant(k)) => Cow::Owned(IVal::Adt(*k, vs)),
            _ => unit(),
        },
    }
}

fn idx(len: usize, i: u128) -> Option<usize> {
    (i < len as u128).then_some(i as usize)
}

/// `sem::read_at`.
fn read_at<'a>(v: Cow<'a, IVal>, path: &[IPe]) -> Cow<'a, IVal> {
    path.iter().fold(v, get)
}

/// `sem::write_at` (with `sem::put` and `sem::pad`), in place.
fn write_at(v: &mut IVal, path: &[IPe], w: IVal) {
    let Some((e, rest)) = path.split_first() else {
        *v = w;
        return;
    };
    if matches!(v, IVal::Adt(..)) && matches!(e, IPe::Variant(_)) {
        // put(Adt(k, vs), Variant, w') keeps k and takes w''s fields when w' is an Adt; the
        // inner write_at(Adt(k2, vs), rest, w) only touches fields, so it can run on v itself.
        if rest.is_empty() {
            if let (IVal::Adt(_, vs), IVal::Adt(_, ws)) = (v, w) {
                *vs = ws;
            }
        } else {
            write_at(v, rest, w);
        }
        return;
    }
    match (v, e) {
        (IVal::Tup(vs) | IVal::Adt(_, vs), IPe::Field(i)) => {
            if vs.len() < i + 1 {
                vs.resize(i + 1, IVal::Unit);
            }
            write_at(&mut vs[*i], rest, w);
        }
        (IVal::Arr(vs), IPe::Index(i)) => {
            if let Some(i) = idx(vs.len(), *i) {
                write_at(&mut vs[i], rest, w);
            }
        }
        _ => {}
    }
}

// ------------------------------------------------------------------ frames and places
/// `sem::read_loc`.
fn read_loc<'a>(fr: &'a IFrame, root: IRoot, path: &[IPe]) -> Cow<'a, IVal> {
    let base = match root {
        IRoot::Local(i) => fr.locals.get(i),
        IRoot::Slot(j) => fr.slots.get(j),
    };
    match base {
        Some(v) => read_at(Cow::Borrowed(v), path),
        None => Cow::Owned(IVal::Unit),
    }
}

/// `sem::write_loc`.
fn write_loc(fr: &mut IFrame, root: IRoot, path: &[IPe], w: IVal) {
    let base = match root {
        IRoot::Local(i) => fr.locals.get_mut(i),
        IRoot::Slot(j) => fr.slots.get_mut(j),
    };
    if let Some(v) = base {
        write_at(v, path, w);
    }
}

/// `sem::Cur`.
enum Cur<'a> {
    L(IRoot, Vec<IPe>),
    V(Cow<'a, IVal>),
}

// ------------------------------------------------------------------ the interpreter

impl<'p> In<'p> {
    fn emit(&mut self, e: impl FnOnce() -> IEv) {
        if let Some(ev) = &mut self.ev {
            ev.push(e());
        }
    }

    /// `sem::step` / `sem::descend`, folded over the projections: `sem::place_walk` (and `walk`).
    fn place_walk<'a>(&mut self, fr: &'a IFrame, pl: &c::Place) -> Cur<'a> {
        let mut cur = Cur::L(IRoot::Local(pl.local), vec![]);
        for pr in &pl.proj {
            let e = match pr {
                c::Proj::Deref => {
                    // follows a Mut from a location; enters a Shr snapshot; else Unit (also a
                    // Mut inside a snapshot)
                    cur = match cur {
                        Cur::L(root, path) => match read_loc(fr, root, &path) {
                            Cow::Borrowed(IVal::Mut(r2, p2)) => Cur::L(*r2, p2.clone()),
                            Cow::Owned(IVal::Mut(r2, p2)) => Cur::L(r2, p2),
                            v => Cur::V(into_shr(v)),
                        },
                        Cur::V(v) => Cur::V(into_shr(v)),
                    };
                    continue;
                }
                c::Proj::Field(i) => IPe::Field(*i),
                c::Proj::Index(x) => {
                    let i = as_int(&read_loc(fr, IRoot::Local(*x), &[]));
                    self.emit(|| IEv::Idx(i));
                    IPe::Index(i)
                }
                c::Proj::ConstIndex(k) => IPe::Index(*k as u128),
                c::Proj::Downcast(k) => IPe::Variant(*k),
            };
            cur = match cur {
                Cur::L(root, mut path) => {
                    path.push(e);
                    Cur::L(root, path)
                }
                Cur::V(v) => Cur::V(get(v, &e)),
            };
        }
        cur
    }

    /// `sem::read_place`.
    fn read_place<'a>(&mut self, fr: &'a IFrame, pl: &c::Place) -> Cow<'a, IVal> {
        match self.place_walk(fr, pl) {
            Cur::L(root, path) => read_loc(fr, root, &path),
            Cur::V(v) => v,
        }
    }

    /// `sem::place_loc`.
    fn place_loc(&mut self, fr: &IFrame, pl: &c::Place) -> Option<(IRoot, Vec<IPe>)> {
        match self.place_walk(fr, pl) {
            Cur::L(root, path) => Some((root, path)),
            Cur::V(_) => None,
        }
    }

    /// `sem::assign`: a write to a `None` place is a no-op (its walk events are still emitted).
    fn assign(&mut self, fr: &mut IFrame, pl: &c::Place, v: IVal) {
        if let Some((root, path)) = self.place_loc(fr, pl) {
            write_loc(fr, root, &path, v);
        }
    }

    /// `sem::eval_op`.
    fn eval_op<'a>(&mut self, fr: &'a IFrame, op: &c::Operand) -> Cow<'a, IVal> {
        match op {
            c::Operand::Copy(pl) => self.read_place(fr, pl),
            c::Operand::Const(_, n) => Cow::Owned(IVal::Int(*n)),
            c::Operand::Lit(k) => Cow::Owned(const_val(k)),
        }
    }

    /// `sem::op_vals`, emitting `sem::ops_ev` (left to right).
    fn op_vals(&mut self, fr: &IFrame, ops: &[c::Operand]) -> Vec<IVal> {
        ops.iter().map(|o| self.eval_op(fr, o).into_owned()).collect()
    }

    /// `sem::eval_rv`, one arm per `Rvalue` as there; events in sem's order (operands left to
    /// right, then `op_ev`; `Len`/`Discr`/`RefShr`/`RefMut` the place walk's).
    fn eval_rv(&mut self, fr: &IFrame, rv: &c::Rvalue) -> IVal {
        match rv {
            c::Rvalue::Use(op) => self.eval_op(fr, op).into_owned(),
            c::Rvalue::Bin(op, ty, a, b) => {
                let x = as_int(&self.eval_op(fr, a));
                let y = as_int(&self.eval_op(fr, b));
                self.op_ev(op, x, y);
                IVal::Int(binop(op, ty, x, y))
            }
            c::Rvalue::Un(op, ty, a) => IVal::Int(unop(op, ty, as_int(&self.eval_op(fr, a)))),
            c::Rvalue::Cast(from, to, a) => IVal::Int(cast(from, to, as_int(&self.eval_op(fr, a)))),
            c::Rvalue::Len(pl) => {
                let v = self.read_place(fr, pl);
                IVal::Int(elems(fr, v).len() as u128)
            }
            c::Rvalue::Discr(pl) => IVal::Int(match &*self.read_place(fr, pl) {
                IVal::Adt(k, _) => *k as u128,
                _ => 0,
            }),
            c::Rvalue::Aggregate(kind, ops) => {
                let vs = self.op_vals(fr, ops);
                match kind {
                    c::AggKind::Tuple => IVal::Tup(vs),
                    c::AggKind::Array => IVal::Arr(vs),
                    c::AggKind::Adt(k) => IVal::Adt(*k, vs),
                }
            }
            c::Rvalue::Repeat(op, n) => IVal::Arr(vec![self.eval_op(fr, op).into_owned(); *n as usize]),
            c::Rvalue::RefShr(pl) => IVal::Shr(Box::new(self.read_place(fr, pl).into_owned())),
            c::Rvalue::RefMut(pl) => match self.place_loc(fr, pl) {
                Some((root, path)) => IVal::Mut(root, path),
                None => IVal::Unit,
            },
        }
    }

    /// `sem::op_ev`.
    fn op_ev(&mut self, op: &c::BinOp, a: u128, b: u128) {
        match op {
            c::BinOp::Div | c::BinOp::Rem => self.emit(|| IEv::DivOps(a, b)),
            c::BinOp::Shl | c::BinOp::Shr => self.emit(|| IEv::Shamt(b)),
            _ => {}
        }
    }

    /// `sem::exec_stmt`: the rvalue's events, then the place's; then the write.
    fn exec_stmt(&mut self, fr: &mut IFrame, s: &c::Stmt) {
        match s {
            c::Stmt::Assign(pl, rv) => {
                let v = self.eval_rv(fr, rv);
                self.assign(fr, pl, v);
            }
            c::Stmt::SetDiscr(pl, k) => {
                if let Some((root, path)) = self.place_loc(fr, pl) {
                    let v = match read_loc(fr, root, &path).into_owned() {
                        IVal::Adt(_, vs) => IVal::Adt(*k, vs),
                        v => v,
                    };
                    write_loc(fr, root, &path, v);
                }
            }
        }
    }

    /// `sem::exec_intr` (with `sem::intr_eff` and `sem::intr_cost`): the args' events, the
    /// intrinsic's, then the dst's, written on the post-effect frame. `None` on Vec overflow.
    fn exec_intr(&mut self, k: &c::Intrinsic, fr: &mut IFrame, args: &[c::Operand], dst: &c::Place) -> Option<u64> {
        use c::Intrinsic as I;
        let vs = self.op_vals(fr, args);
        let nth = |i: usize| vs.get(i).cloned().unwrap_or(IVal::Unit);
        let (a0, a1, a2) = (nth(0), nth(1), nth(2));
        let mut cost = 0;
        let r = match k {
            I::Declassify => {
                self.emit(|| IEv::Declass(a0.clone()));
                a0
            }
            I::GhostUnit => IVal::Unit,
            I::VecNew => IVal::Arr(vec![]),
            I::VecWithCapacity => {
                self.emit(|| IEv::Alloc(as_int(&a0)));
                IVal::Arr(vec![])
            }
            I::VecPush => {
                grow(fr, &a0, vec![a1])?;
                IVal::Unit
            }
            I::VecExtendFromSlice => {
                let xs = elems(fr, Cow::Owned(a1)).into_owned();
                cost = xs.len() as u64;
                grow(fr, &a0, xs)?;
                IVal::Unit
            }
            I::VecAsSlice | I::ArrayAsSlice => a0,
            I::VecLen => IVal::Int(elems(fr, Cow::Owned(a0)).len() as u128),
            I::VecSet => {
                let i = as_int(&a1);
                if let IVal::Mut(root, path) = &a0 {
                    let mut path = path.clone();
                    path.push(IPe::Index(i));
                    write_loc(fr, *root, &path, a2);
                }
                self.emit(|| IEv::Idx(i));
                IVal::Unit
            }
            I::VecIndex => {
                let i = as_int(&a1);
                self.emit(|| IEv::Idx(i));
                let s = elems(fr, Cow::Owned(a0));
                IVal::Shr(Box::new(idx(s.len(), i).map_or(IVal::Unit, |i| s[i].clone())))
            }
            I::SliceSubrange => {
                let s = elems(fr, Cow::Owned(a0));
                let (lo, hi) = (as_int(&a1), as_int(&a2));
                let h = hi.min(s.len() as u128) as usize;
                let l = lo.min(h as u128) as usize;
                let r = IVal::Shr(Box::new(IVal::Arr(s[l..h].to_vec())));
                self.emit(|| IEv::Range(lo, hi));
                r
            }
            I::SliceToVec => {
                let s = elems(fr, Cow::Owned(a0)).into_owned();
                cost = s.len() as u64;
                if s.len() as u128 > USIZE_MAX {
                    return None;
                }
                IVal::Arr(s)
            }
            I::Wrapping(op, ty) => {
                let (a, b) = (as_int(&a0), as_int(&a1));
                self.op_ev(op, a, b);
                IVal::Int(binop(op, ty, a, b))
            }
        };
        self.assign(fr, dst, r);
        Some(cost)
    }

    /// `sem::call_enter`: the callee frame and the write-back locs (the arg events are emitted).
    fn call_enter(&mut self, g: usize, fr: &IFrame, args: &[c::Operand]) -> (IFrame, Vec<Option<(IRoot, Vec<IPe>)>>) {
        let vs = self.op_vals(fr, args);
        let n = self.p.fns.get(g).map_or(0, |b| b.locals.len());
        let locals = (0..n)
            .map(|i| {
                if 1 <= i && i <= vs.len() {
                    match &vs[i - 1] {
                        IVal::Mut(..) => IVal::Mut(IRoot::Slot(i - 1), vec![]),
                        v => v.clone(),
                    }
                } else {
                    IVal::Unit
                }
            })
            .collect();
        let slots = vs
            .iter()
            .map(|v| match v {
                IVal::Mut(root, path) => read_loc(fr, *root, path).into_owned(),
                _ => IVal::Unit,
            })
            .collect();
        let wb = vs
            .into_iter()
            .map(|v| match v {
                IVal::Mut(root, path) => Some((root, path)),
                _ => None,
            })
            .collect();
        (IFrame { locals, slots }, wb)
    }

    /// `sem::call_leave` (with `sem::write_back`, in caller order), then `dst := callee._0`.
    fn call_leave(&mut self, fr: &mut IFrame, callee: IFrame, wb: Vec<Option<(IRoot, Vec<IPe>)>>, dst: &c::Place) {
        let IFrame { locals, slots } = callee;
        for (j, l) in wb.into_iter().enumerate() {
            if let Some((root, path)) = l {
                write_loc(fr, root, &path, slots.get(j).cloned().unwrap_or(IVal::Unit));
            }
        }
        self.assign(fr, dst, locals.into_iter().next().unwrap_or(IVal::Unit));
    }

    /// `sem::run_from`: each block transition and each call consumes 1 fuel of this activation
    /// (a callee and this fn's continuation both get `fuel - 1`); steps are one per statement and
    /// terminator, plus callee steps and intrinsic costs.
    fn run_from(&mut self, f: usize, mut b: usize, fr: &mut IFrame, mut fuel: u64) -> Option<u64> {
        let (p, mut steps) = (self.p, 0u64);
        loop {
            let body = p.fns.get(f)?;
            let blk = body.blocks.get(b)?;
            if fuel == 0 {
                return None;
            }
            for s in &blk.stmts {
                self.exec_stmt(fr, s);
            }
            steps += blk.stmts.len() as u64 + 1;
            fuel -= 1;
            match &blk.term {
                c::Term::Goto(b2) => b = *b2,
                // Switch and Assert: the operand's events, then Cond(v)
                c::Term::Switch(op, ts, otherwise) => {
                    let v = as_int(&self.eval_op(fr, op));
                    self.emit(|| IEv::Cond(v));
                    b = ts.iter().find(|(x, _)| *x == v).map_or(*otherwise, |(_, t)| *t); // sem::switch_target
                }
                c::Term::Assert(op, expected, b2) => {
                    let v = as_int(&self.eval_op(fr, op));
                    self.emit(|| IEv::Cond(v));
                    if (v != 0) != *expected {
                        return None;
                    }
                    b = *b2;
                }
                c::Term::Return => return Some(steps),
                c::Term::Abort => return None,
                // sem: call_enter, run_from(g, 0, .., fuel - 1), call_leave, then the continuation
                c::Term::Call(c::Callee::Fn(g), args, dst, next) => {
                    let (mut cf, wb) = self.call_enter(*g, fr, args);
                    steps += self.run_from(*g, 0, &mut cf, fuel)?;
                    self.call_leave(fr, cf, wb, dst);
                    b = *next;
                }
                // sem: exec_intr (steps + intr_cost), then the continuation
                c::Term::Call(c::Callee::Intr(k), args, dst, next) => {
                    steps += self.exec_intr(k, fr, args, dst)?;
                    b = *next;
                }
            }
        }
    }
}

/// The pointee of a `Shr`; `Unit` for anything else.
fn into_shr(v: Cow<'_, IVal>) -> Cow<'_, IVal> {
    match v {
        Cow::Borrowed(IVal::Shr(b)) => Cow::Borrowed(&**b),
        Cow::Owned(IVal::Shr(b)) => Cow::Owned(*b),
        _ => Cow::Owned(IVal::Unit),
    }
}

/// `sem::const_val`.
fn const_val(k: &c::ConstVal) -> IVal {
    match k {
        c::ConstVal::Int(n) => IVal::Int(*n),
        c::ConstVal::Unit => IVal::Unit,
        c::ConstVal::Arr(cs) => IVal::Arr(cs.iter().map(const_val).collect()),
        c::ConstVal::Shr(b) => IVal::Shr(Box::new(const_val(b))),
    }
}

/// `sem::elems`: the elements of an `Arr`, looking through one `Shr`/`Mut`; empty otherwise.
fn elems<'a>(fr: &'a IFrame, v: Cow<'a, IVal>) -> Cow<'a, [IVal]> {
    let t = match v {
        Cow::Borrowed(IVal::Shr(b)) => Cow::Borrowed(&**b),
        Cow::Owned(IVal::Shr(b)) => Cow::Owned(*b),
        Cow::Borrowed(IVal::Mut(root, path)) => read_loc(fr, *root, path),
        Cow::Owned(IVal::Mut(root, path)) => read_loc(fr, root, &path),
        v => v,
    };
    match t {
        Cow::Borrowed(IVal::Arr(s)) => Cow::Borrowed(&s[..]),
        Cow::Owned(IVal::Arr(s)) => Cow::Owned(s),
        _ => Cow::Owned(vec![]),
    }
}

/// `sem::grow`: appends `xs` to the `Arr` that `m` targets; `None` past usize::MAX elements.
fn grow(fr: &mut IFrame, m: &IVal, xs: Vec<IVal>) -> Option<()> {
    let IVal::Mut(root, path) = m else { return Some(()) };
    let mut s = match read_loc(fr, *root, path).into_owned() {
        IVal::Arr(s) => s,
        _ => return Some(()),
    };
    if s.len() as u128 + xs.len() as u128 > USIZE_MAX {
        return None;
    }
    s.extend(xs);
    write_loc(fr, *root, path, IVal::Arr(s));
    Some(())
}

// ------------------------------------------------------------------ selftest vectors

/// Per-activation fuel for a vector run: far above any crypto loop's block count.
const FUEL: u64 = 1 << 32;

/// One `selftest.txt` line after its path: `<arg>... => <ret> <mut-out>...`.
pub struct Vector {
    /// Per param: `true` for a `mut:` arg (a `&mut` param; the value is its initial pointee).
    pub args: Vec<(bool, IVal)>,
    /// The return value, then the final pointee of each `mut:` param, in param order.
    pub want: Vec<IVal>,
    /// Per param: the suffix width of an int arg (`0x2au8` is 8), checked against the param.
    pub int_bits: Vec<Option<u32>>,
}

/// Parses the tokens after the path. Values: hex bytes (an `Arr` of byte `Int`s; `-` is the
/// empty one), `0x<hex><int suffix>` (an `Int`, e.g. `0x0388u128`), `true`/`false` (a `Bool`
/// `Int`), `[v,v,..]` (an `Arr`), `(v,v,..)` (a `Tup`), `()`, `None`, `Some(v)`, and `#k(v,..)`
/// (variant `k` of an enum, with those fields; `#k()` has none).
/// A plain arg that is an `Arr` is passed by shared reference (`Shr`): a slice or `&[T; N]`; so is
/// any plain arg of a `Shr` param (`check_vector`).
pub fn parse_vector(toks: &[&str]) -> Result<Vector, String> {
    let at = toks.iter().position(|t| *t == "=>").ok_or("no `=>`")?;
    let args = toks[..at]
        .iter()
        .map(|t| match t.strip_prefix("mut:") {
            Some(v) => Ok((true, value(v)?)),
            None => value(t).map(|v| (false, if matches!(v, IVal::Arr(_)) { IVal::Shr(Box::new(v)) } else { v })),
        })
        .collect::<Result<_, String>>()?;
    let want = toks[at + 1..].iter().map(|t| value(t)).collect::<Result<_, _>>()?;
    let int_bits = toks[..at].iter().map(|t| int_lit(t.strip_prefix("mut:").unwrap_or(t)).map(|(_, w)| w)).collect();
    Ok(Vector { args, want, int_bits })
}

/// An int literal `0x<hex><suffix>`: its digits and the suffix's width.
fn int_lit(t: &str) -> Option<(&str, u32)> {
    let r = t.strip_prefix("0x")?;
    let (digits, suf) = r.split_at(r.find(|ch: char| !ch.is_ascii_hexdigit()).unwrap_or(r.len()));
    let w = match suf {
        "u8" | "i8" => 8,
        "u16" | "i16" => 16,
        "u32" | "i32" => 32,
        "u64" | "i64" | "usize" | "isize" => 64,
        "u128" | "i128" => 128,
        _ => return None,
    };
    Some((digits, w))
}

/// `s` split at the commas outside any `(..)`/`[..]`; empty pieces dropped.
fn split_top(s: &str) -> Vec<&str> {
    let (mut out, mut depth, mut start) = (Vec::new(), 0i32, 0);
    for (i, ch) in s.char_indices() {
        match ch {
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            ',' if depth == 0 => {
                out.push(&s[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    out.push(&s[start..]);
    out.into_iter().filter(|p| !p.is_empty()).collect()
}

fn values(s: &str) -> Result<Vec<IVal>, String> {
    split_top(s).into_iter().map(value).collect()
}

fn value(t: &str) -> Result<IVal, String> {
    if t == "-" {
        return Ok(IVal::Arr(vec![]));
    }
    if t == "()" {
        return Ok(IVal::Unit);
    }
    match t {
        "true" => return Ok(IVal::Int(1)),
        "false" => return Ok(IVal::Int(0)),
        _ => {}
    }
    // core::option::Option: variant 0 is None, 1 is Some
    if t == "None" {
        return Ok(IVal::Adt(0, vec![]));
    }
    if let Some(inner) = t.strip_prefix("Some(").and_then(|r| r.strip_suffix(')')) {
        return Ok(IVal::Adt(1, vec![value(inner)?]));
    }
    if let Some((k, inner)) = t.strip_prefix('#').and_then(|r| r.strip_suffix(')')).and_then(|r| r.split_once('(')) {
        let k = k.parse().map_err(|e| format!("{t}: variant index: {e}"))?;
        return Ok(IVal::Adt(k, values(inner)?));
    }
    if let Some(inner) = t.strip_prefix('(').and_then(|r| r.strip_suffix(')')) {
        return values(inner).map(IVal::Tup);
    }
    if t.starts_with("0x") {
        let (digits, w) =
            int_lit(t).ok_or_else(|| format!("{t}: an int needs a type suffix (u8 .. u128, usize, i8 .. i128, isize)"))?;
        let n = u128::from_str_radix(digits, 16).map_err(|e| format!("{t}: {e}"))?;
        if w < 128 && n >> w != 0 {
            return Err(format!("{t}: does not fit in {w} bits"));
        }
        return Ok(IVal::Int(n));
    }
    if let Some(inner) = t.strip_prefix('[').and_then(|r| r.strip_suffix(']')) {
        return values(inner).map(IVal::Arr);
    }
    if t.len() % 2 != 0 || !t.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err(format!("{t}: not a value"));
    }
    Ok(IVal::Arr((0..t.len()).step_by(2).map(|i| IVal::Int(u128::from_str_radix(&t[i..i + 2], 16).unwrap())).collect()))
}

/// Runs fn 0 of `p` (the translated root) on the vector's args and compares, exactly, the
/// return value and the final pointee of every `&mut` param. `Ok(steps)` on a match.
pub fn check_vector(p: &c::Program, v: &Vector) -> Result<u64, String> {
    let b = p.fns.first().ok_or("empty program")?;
    if v.args.len() != b.nargs {
        return Err(format!("{} args for {} params", v.args.len(), b.nargs));
    }
    for (j, (m, _)) in v.args.iter().enumerate() {
        if *m != is_mut_param(b, j) {
            return Err(format!("param #{}: `mut:` must mark exactly the &mut params", j + 1));
        }
    }
    for (j, w) in v.int_bits.iter().enumerate() {
        let ty = match b.locals.get(1 + j) {
            Some(c::Ty::Mut(t)) => Some(&**t),
            t => t,
        };
        match (w, ty) {
            (None, _) => {}
            (Some(w), Some(c::Ty::Int(t))) if bits(t) == *w => {}
            (Some(w), Some(c::Ty::Int(t))) => return Err(format!("param #{}: a {w}-bit int arg for a {}-bit param", j + 1, bits(t))),
            (Some(w), _) => return Err(format!("param #{}: a {w}-bit int arg for a non-int param", j + 1)),
        }
    }
    let muts: Vec<usize> = (0..b.nargs).filter(|&j| v.args[j].0).collect();
    if v.want.len() != 1 + muts.len() {
        return Err(format!("{} expected values for 1 return value and {} &mut params", v.want.len(), muts.len()));
    }
    let args: Vec<IVal> = v
        .args
        .iter()
        .enumerate()
        .map(|(j, (m, a))| match (m, b.locals.get(1 + j), a) {
            (false, Some(c::Ty::Shr(_)), v) if !matches!(v, IVal::Shr(_)) => IVal::Shr(Box::new(v.clone())),
            _ => a.clone(),
        })
        .collect();
    let fr = init_entry(p, 0, &args, entry_slots(p, 0, &args));
    let (fr, _, steps) = run_fn(p, 0, fr, FUEL, false).ok_or("the run gave None (abort, failed assert or fuel)")?;
    let mut got = vec![fr.locals.into_iter().next().unwrap_or(IVal::Unit)];
    got.extend(muts.iter().map(|&j| fr.slots.get(j).cloned().unwrap_or(IVal::Unit)));
    if got != v.want {
        let show = |vs: &[IVal]| vs.iter().map(show).collect::<Vec<_>>().join(" ");
        return Err(format!("got {} want {}", show(&got), show(&v.want)));
    }
    Ok(steps)
}

/// A value in the vector syntax where it has one (byte arrays as hex), else `Debug`.
fn show(v: &IVal) -> String {
    match v {
        IVal::Arr(vs) if vs.iter().all(|x| matches!(x, IVal::Int(n) if *n < 256)) => {
            if vs.is_empty() {
                return "-".into();
            }
            vs.iter().map(|x| format!("{:02x}", as_int(x))).collect()
        }
        IVal::Arr(vs) => format!("[{}]", vs.iter().map(show).collect::<Vec<_>>().join(",")),
        IVal::Int(n) => format!("{n:#x}"),
        IVal::Unit => "()".into(),
        v => format!("{v:?}"),
    }
}

#[cfg(test)]
mod tests {
    //! Task 2's sanity programs (`crates/ctcore/src/sem_sanity.rs`), each built to satisfy its
    //! lemma's `requires`, run here; each test expects exactly the frame, events and steps the
    //! lemma's `ensures` proves (named per test). `sanity_push_overflow_is_none` is left out: its
    //! slot is an `Arr` of usize::MAX elements.
    use super::*;
    use c::{BinOp as B, IntTy as T, Intrinsic as K};
    use IVal::{Arr, Int, Unit};

    fn pl(local: usize, proj: Vec<c::Proj>) -> c::Place {
        c::Place { local, proj }
    }
    fn lp(local: usize) -> c::Place {
        pl(local, vec![])
    }
    fn cp(local: usize) -> c::Operand {
        c::Operand::Copy(lp(local))
    }
    fn k8(n: u128) -> c::Operand {
        c::Operand::Const(T::U8, n)
    }
    fn set(d: c::Place, rv: c::Rvalue) -> c::Stmt {
        c::Stmt::Assign(d, rv)
    }
    fn blk(stmts: Vec<c::Stmt>, term: c::Term) -> c::Block {
        c::Block { stmts, term }
    }
    fn body(nargs: usize, locals: Vec<c::Ty>, blocks: Vec<c::Block>) -> c::Body {
        c::Body { nargs, locals, blocks }
    }
    /// One fn; local types do not matter to `run_from`.
    fn prog1(blocks: Vec<c::Block>) -> c::Program {
        c::Program { fns: vec![body(0, vec![], blocks)] }
    }
    fn ret_const(n: u128) -> c::Block {
        blk(vec![set(lp(0), c::Rvalue::Use(k8(n)))], c::Term::Return)
    }
    fn fr(locals: Vec<IVal>, slots: Vec<IVal>) -> IFrame {
        IFrame { locals, slots }
    }
    fn fr1(v: IVal) -> IFrame {
        fr(vec![v], vec![])
    }
    fn fr3(a: IVal, b: IVal, x: IVal) -> IFrame {
        fr(vec![a, b, x], vec![])
    }
    fn fr4(a: IVal, b: IVal, x: IVal) -> IFrame {
        fr(vec![a, b, x, Unit], vec![])
    }
    fn arr(xs: &[u128]) -> IVal {
        Arr(xs.iter().map(|&x| Int(x)).collect())
    }
    fn shr(v: IVal) -> IVal {
        IVal::Shr(Box::new(v))
    }
    fn slot0() -> IVal {
        IVal::Mut(IRoot::Slot(0), vec![])
    }
    fn loc1() -> IVal {
        IVal::Mut(IRoot::Local(1), vec![])
    }
    fn run(p: &c::Program, f: IFrame, fuel: u64) -> Option<(IFrame, Vec<IEv>, u64)> {
        run_fn(p, 0, f, fuel, true)
    }
    /// `intr_prog(p, k)` with `intr_args(p) == args`.
    fn intr_prog(k: c::Intrinsic, args: Vec<c::Operand>) -> c::Program {
        prog1(vec![blk(vec![], c::Term::Call(c::Callee::Intr(k), args, lp(0), 1)), blk(vec![], c::Term::Return)])
    }
    fn switch_prog(v: u128, ts: Vec<(u128, usize)>, o: usize) -> c::Program {
        prog1(vec![blk(vec![], c::Term::Switch(k8(v), ts, o)), ret_const(10), ret_const(20)])
    }
    fn bin_prog(op: c::BinOp) -> c::Program {
        prog1(vec![blk(vec![set(lp(0), c::Rvalue::Bin(op, T::U32, cp(1), cp(2)))], c::Term::Return)])
    }

    #[test]
    fn sanity_switch_matching_target() {
        let p = switch_prog(1, vec![(0, 2), (1, 1), (1, 2)], 2);
        assert_eq!(run(&p, fr1(Unit), 3), Some((fr1(Int(10)), vec![IEv::Cond(1)], 3)));
    }

    #[test]
    fn sanity_switch_otherwise() {
        let p = switch_prog(5, vec![(0, 1), (1, 1)], 2);
        assert_eq!(run(&p, fr1(Unit), 3), Some((fr1(Int(20)), vec![IEv::Cond(5)], 3)));
    }

    #[test]
    fn sanity_assert_failure_is_none() {
        let p = prog1(vec![blk(vec![], c::Term::Assert(c::Operand::Const(T::Bool, 1), false, 1)), blk(vec![], c::Term::Return)]);
        assert_eq!(run(&p, fr1(Unit), 3), None);
    }

    #[test]
    fn sanity_index_emits_idx() {
        let p = prog1(vec![blk(vec![set(lp(0), c::Rvalue::Use(c::Operand::Copy(pl(1, vec![c::Proj::Index(2)]))))], c::Term::Return)]);
        let a = arr(&[10, 20, 30]);
        let got = run(&p, fr(vec![Unit, a.clone(), Int(1)], vec![]), 1);
        assert_eq!(got, Some((fr(vec![Int(20), a, Int(1)], vec![]), vec![IEv::Idx(1)], 2)));
    }

    #[test]
    fn sanity_div_emits_operands() {
        let got = run(&bin_prog(B::Div), fr3(Unit, Int(7), Int(2)), 1);
        assert_eq!(got, Some((fr3(Int(binop(&B::Div, &T::U32, 7, 2)), Int(7), Int(2)), vec![IEv::DivOps(7, 2)], 2)));
        assert_eq!(binop(&B::Div, &T::U32, 7, 2), 3);
    }

    #[test]
    fn sanity_shift_emits_amount() {
        let got = run(&bin_prog(B::Shl), fr3(Unit, Int(1), Int(3)), 1);
        assert_eq!(got, Some((fr3(Int(8), Int(1), Int(3)), vec![IEv::Shamt(3)], 2)));
    }

    #[test]
    fn sanity_steps_count() {
        let p = prog1(vec![blk(vec![set(lp(0), c::Rvalue::Use(k8(1))), set(lp(0), c::Rvalue::Use(k8(2)))], c::Term::Goto(1)), ret_const(3)]);
        assert_eq!(run(&p, fr1(Unit), 2), Some((fr1(Int(3)), vec![], 5)));
    }

    #[test]
    fn sanity_mut_arg_written_back() {
        let caller = body(
            0,
            vec![],
            vec![
                blk(vec![set(lp(1), c::Rvalue::Use(k8(0))), set(lp(2), c::Rvalue::RefMut(lp(1)))], c::Term::Call(c::Callee::Fn(1), vec![cp(2)], lp(3), 1)),
                blk(vec![set(lp(0), c::Rvalue::Use(cp(1)))], c::Term::Return),
            ],
        );
        let callee = body(
            1,
            vec![c::Ty::Unit, c::Ty::Mut(Box::new(c::Ty::Int(T::U8)))],
            vec![blk(vec![set(pl(1, vec![c::Proj::Deref]), c::Rvalue::Use(k8(7)))], c::Term::Return)],
        );
        let p = c::Program { fns: vec![caller, callee] };
        assert_eq!(run(&p, fr4(Unit, Unit, Unit), 2), Some((fr4(Int(7), Int(7), loc1()), vec![], 7)));
    }

    #[test]
    fn sanity_shr_snapshot() {
        let p = prog1(vec![blk(
            vec![set(lp(2), c::Rvalue::RefShr(lp(1))), set(lp(0), c::Rvalue::Len(pl(2, vec![c::Proj::Deref])))],
            c::Term::Return,
        )]);
        let a = arr(&[1, 2, 3]);
        assert_eq!(run(&p, fr3(Unit, a.clone(), Unit), 1), Some((fr3(Int(3), a.clone(), shr(a)), vec![], 3)));
    }

    #[test]
    fn sanity_push_appends() {
        let p = intr_prog(K::VecPush, vec![cp(1), k8(9)]);
        let got = run(&p, fr(vec![Unit, slot0()], vec![arr(&[1])]), 2);
        assert_eq!(got, Some((fr(vec![Unit, slot0()], vec![arr(&[1, 9])]), vec![], 2)));
    }

    #[test]
    fn sanity_declassify_event() {
        let p = intr_prog(K::Declassify, vec![cp(1)]);
        let got = run(&p, fr(vec![Unit, Int(42)], vec![]), 2);
        assert_eq!(got, Some((fr(vec![Int(42), Int(42)], vec![]), vec![IEv::Declass(Int(42))], 2)));
    }

    #[test]
    fn sanity_subrange_clamps() {
        let p = intr_prog(K::SliceSubrange, vec![cp(1), c::Operand::Const(T::Usize, 1), c::Operand::Const(T::Usize, 10)]);
        let (r, d) = (shr(arr(&[1, 2, 3])), shr(arr(&[2, 3])));
        let got = run(&p, fr(vec![Unit, r.clone()], vec![]), 2);
        assert_eq!(got, Some((fr(vec![d, r], vec![]), vec![IEv::Range(1, 10)], 2)));
    }

    #[test]
    fn sanity_call_trace_includes_callee() {
        let caller = body(
            0,
            vec![],
            vec![
                blk(vec![], c::Term::Call(c::Callee::Fn(1), vec![c::Operand::Copy(pl(1, vec![c::Proj::Index(2)]))], lp(3), 1)),
                blk(vec![], c::Term::Return),
            ],
        );
        let callee = body(
            1,
            vec![c::Ty::Unit, c::Ty::Int(T::U8)],
            vec![blk(vec![], c::Term::Assert(c::Operand::Const(T::Bool, 1), true, 1)), blk(vec![], c::Term::Return)],
        );
        let p = c::Program { fns: vec![caller, callee] };
        let f0 = fr4(Unit, arr(&[10, 20, 30]), Int(1));
        assert_eq!(run(&p, f0.clone(), 3), Some((f0, vec![IEv::Idx(1), IEv::Cond(1)], 4)));
    }

    #[test]
    fn sanity_vec_set_events() {
        let set_fr = |x: u128| fr(vec![Unit, slot0(), arr(&[1, 7]), Int(0)], vec![arr(&[5, x])]);
        let p = intr_prog(K::VecSet, vec![cp(1), c::Operand::Copy(pl(2, vec![c::Proj::Index(3)])), k8(9)]);
        assert_eq!(run(&p, set_fr(6), 2), Some((set_fr(9), vec![IEv::Idx(0), IEv::Idx(1)], 2)));
    }

    #[test]
    fn sanity_with_capacity_alloc() {
        let p = intr_prog(K::VecWithCapacity, vec![c::Operand::Const(T::Usize, 16)]);
        assert_eq!(run(&p, fr1(Unit), 2), Some((fr1(Arr(vec![])), vec![IEv::Alloc(16)], 2)));
    }

    #[test]
    fn sanity_vec_index_idx() {
        let p = intr_prog(K::VecIndex, vec![cp(1), c::Operand::Const(T::Usize, 1)]);
        let r = shr(arr(&[10, 20]));
        let got = run(&p, fr(vec![Unit, r.clone()], vec![]), 2);
        assert_eq!(got, Some((fr(vec![shr(Int(20)), r], vec![]), vec![IEv::Idx(1)], 2)));
    }

    #[test]
    fn sanity_wrapping_events() {
        let p = intr_prog(K::Wrapping(B::Div, T::U32), vec![c::Operand::Const(T::U32, 7), c::Operand::Const(T::U32, 2)]);
        assert_eq!(run(&p, fr1(Unit), 2), Some((fr1(Int(3)), vec![IEv::DivOps(7, 2)], 2)));
    }

    #[test]
    fn sanity_extend_cost() {
        let ext_fr = |v: &[u128]| fr(vec![Unit, slot0(), shr(arr(&[3, 4]))], vec![arr(v)]);
        let p = intr_prog(K::VecExtendFromSlice, vec![cp(1), cp(2)]);
        assert_eq!(run(&p, ext_fr(&[1]), 2), Some((ext_fr(&[1, 3, 4]), vec![], 4)));
    }

    #[test]
    fn sanity_fuel_zero_is_none() {
        let p = prog1(vec![blk(vec![], c::Term::Return)]);
        assert_eq!(run(&p, fr1(Unit), 0), None);
    }

    #[test]
    fn sanity_entry_mut_param() {
        let p = c::Program { fns: vec![body(1, vec![c::Ty::Unit, c::Ty::Mut(Box::new(c::Ty::Int(T::U8)))], vec![])] };
        assert_eq!(init_entry(&p, 0, &[Int(5)], vec![Int(6)]), fr(vec![Unit, slot0()], vec![Int(6)]));
    }

    /// The briefed `run`: `init_entry` puts a `&mut` param's arg in its slot; `_0` comes back.
    #[test]
    fn run_entry_with_mut_param() {
        // fn(x: &mut u8) -> u8 { *x = 7; *x }
        let b = body(
            1,
            vec![c::Ty::Int(T::U8), c::Ty::Mut(Box::new(c::Ty::Int(T::U8)))],
            vec![blk(
                vec![
                    set(pl(1, vec![c::Proj::Deref]), c::Rvalue::Use(k8(7))),
                    set(lp(0), c::Rvalue::Use(c::Operand::Copy(pl(1, vec![c::Proj::Deref])))),
                ],
                c::Term::Return,
            )],
        );
        let p = c::Program { fns: vec![b] };
        assert_eq!(entry_slots(&p, 0, &[Int(5)]), vec![Int(5)]);
        assert_eq!(super::run(&p, 0, vec![Int(5)], 1), Some((Int(7), 3)));
    }

    #[test]
    fn vector_syntax() {
        let v = parse_vector(&["00ff", "-", "0x2au128", "mut:[0x1u64,0x2u64]", "=>", "()", "[0x1u64]"]).unwrap();
        assert_eq!(v.args[0], (false, shr(arr(&[0, 0xff]))));
        assert_eq!(v.args[1], (false, shr(Arr(vec![]))));
        assert_eq!(v.args[2], (false, Int(0x2a)));
        assert_eq!(v.args[3], (true, arr(&[1, 2])));
        assert_eq!(v.want, vec![Unit, arr(&[1])]);
        let v = parse_vector(&["=>", "None", "Some(0a)"]).unwrap();
        assert_eq!(v.want, vec![IVal::Adt(0, vec![]), IVal::Adt(1, vec![arr(&[10])])]);
        for bad in [&["0x1", "=>", "()"][..], &["0x100u8", "=>", "()"], &["abc", "=>", "()"], &["00"]] {
            assert!(parse_vector(bad).is_err(), "{bad:?}");
        }
    }

    #[test]
    fn vector_tuple_values() {
        let v = parse_vector(&["[(0x1u64,0x2u64),(0x3u64,0x4u64)]", "=>", "Some((0x5u64,0x6usize))"]).unwrap();
        let pair = |a, b| IVal::Tup(vec![Int(a), Int(b)]);
        assert_eq!(v.args[0], (false, shr(Arr(vec![pair(1, 2), pair(3, 4)]))));
        assert_eq!(v.want, vec![IVal::Adt(1, vec![pair(5, 6)])]);
        assert_eq!(parse_vector(&["=>", "(0a0b,())"]).unwrap().want, vec![IVal::Tup(vec![arr(&[10, 11]), Unit])]);
        assert!(parse_vector(&["=>", "(0x1u8,0x2)"]).is_err());
    }

    #[test]
    fn vector_bool_values() {
        assert_eq!(parse_vector(&["true", "=>", "false"]).unwrap().want, vec![Int(0)]);
        assert_eq!(parse_vector(&["true", "=>", "false"]).unwrap().args[0], (false, Int(1)));
        assert!(parse_vector(&["=>", "True"]).is_err());
    }

    #[test]
    fn vector_enum_values() {
        let v = parse_vector(&["#0()", "=>", "#1(#0(0x105u64))", "#2(0x7u8,[(0x1u64,0x2u64)])"]).unwrap();
        assert_eq!(v.args[0], (false, IVal::Adt(0, vec![])));
        assert_eq!(v.want[0], IVal::Adt(1, vec![IVal::Adt(0, vec![Int(0x105)])]));
        assert_eq!(v.want[1], IVal::Adt(2, vec![Int(7), Arr(vec![IVal::Tup(vec![Int(1), Int(2)])])]));
        for bad in ["#x(0x1u8)", "#1(0x1u8", "#1"] {
            assert!(parse_vector(&["=>", bad]).is_err(), "{bad}");
        }
    }

    /// A plain arg of a `Shr` param is passed by reference (an `Arr` already is).
    #[test]
    fn vector_shr_param_gets_a_ref() {
        // fn(p: &Phase) -> Phase { *p }
        let b = body(
            1,
            vec![c::Ty::Adt(vec![vec![]]), c::Ty::Shr(Box::new(c::Ty::Adt(vec![vec![]])))],
            vec![blk(vec![set(lp(0), c::Rvalue::Use(c::Operand::Copy(pl(1, vec![c::Proj::Deref]))))], c::Term::Return)],
        );
        let p = c::Program { fns: vec![b] };
        assert_eq!(check_vector(&p, &parse_vector(&["#0()", "=>", "#0()"]).unwrap()), Ok(2));
    }

    /// A suffixed int arg must have its param's width (through `&mut` too), and goes only to an
    /// int param.
    #[test]
    fn vector_int_width_matches_param() {
        let ret = || vec![blk(vec![], c::Term::Return)];
        let p = c::Program { fns: vec![body(1, vec![c::Ty::Int(T::U8), c::Ty::Int(T::U8)], ret())] };
        let run = |p: &c::Program, args: &[&str]| check_vector(p, &parse_vector(args).unwrap());
        assert_eq!(run(&p, &["0x1u8", "=>", "0x0u8"]), Err("got () want 0x0".into()));
        assert!(run(&p, &["0x1u128", "=>", "()"]).unwrap_err().contains("param #1"));
        assert!(run(&p, &["0x1u16", "=>", "()"]).unwrap_err().contains("param #1"));
        assert!(run(&p, &["0x1usize", "=>", "()"]).unwrap_err().contains("param #1"));
        let mt = c::Ty::Mut(Box::new(c::Ty::Int(T::U8)));
        let p = c::Program { fns: vec![body(1, vec![c::Ty::Unit, mt], ret())] };
        assert_eq!(run(&p, &["mut:0x7u8", "=>", "()", "0x7u8"]), Ok(1));
        assert!(run(&p, &["mut:0x7u32", "=>", "()", "0x7u8"]).unwrap_err().contains("param #1"));
        let p = c::Program { fns: vec![body(1, vec![c::Ty::Unit, c::Ty::Shr(Box::new(c::Ty::Int(T::U8)))], ret())] };
        assert!(run(&p, &["0x7u8", "=>", "()"]).unwrap_err().contains("param #1"));
    }

    /// The in-place `Variant` write equals sem's `put(v, Variant(k), write_at(get(v, Variant(k)),
    /// rest, w))`: the fields change and v's own tag stays. `get`'s owned arm reads the same.
    #[test]
    fn variant_write_keeps_tag() {
        use IPe::{Field, Index, Variant};
        let mut v = IVal::Adt(0, vec![Int(1)]);
        write_at(&mut v, &[Variant(1), Field(0)], Int(9));
        assert_eq!(v, IVal::Adt(0, vec![Int(9)]));
        write_at(&mut v, &[Variant(1)], IVal::Adt(1, vec![Int(4), Int(5)]));
        assert_eq!(v, IVal::Adt(0, vec![Int(4), Int(5)]));
        let rd = |v: &IVal, path: &[IPe]| read_at(Cow::Owned(v.clone()), path).into_owned();
        assert_eq!(rd(&v, &[Variant(1), Field(1)]), Int(5));
        assert_eq!(rd(&v, &[Variant(1), Field(0)]), Int(4));
        assert_eq!(rd(&v, &[Variant(1)]), IVal::Adt(1, vec![Int(4), Int(5)]));
        assert_eq!(rd(&v, &[Field(2)]), Unit);
        assert_eq!(rd(&arr(&[3, 4]), &[Index(1)]), Int(4));
        assert_eq!(rd(&arr(&[3, 4]), &[Index(2)]), Unit);
        assert_eq!(rd(&Int(3), &[Field(0)]), Unit);
        for path in [&[Variant(1), Field(1)][..], &[Field(0)], &[Index(0)]] {
            assert_eq!(rd(&v, path), read_at(Cow::Borrowed(&v), path).into_owned(), "{path:?}");
        }
    }

    /// Rust's wrapping semantics per `IntTy`, at the edges `sem::binop`/`cast` define.
    #[test]
    fn arithmetic_edges() {
        assert_eq!(binop(&B::Sub, &T::U8, 0, 1), 0xff);
        assert_eq!(binop(&B::Div, &T::I8, 0x80, 0xff), 0x80); // i8::MIN / -1 wraps
        assert_eq!(binop(&B::Rem, &T::I8, 0x80, 0xff), 0);
        assert_eq!(binop(&B::Div, &T::U32, 7, 0), 0);
        assert_eq!(binop(&B::Rem, &T::I32, 7, 0), 0);
        assert_eq!(binop(&B::Shl, &T::U32, 1, 33), 2); // amount % 32
        assert_eq!(binop(&B::Shr, &T::I8, 0x80, 1), 0xc0); // arithmetic
        assert_eq!(binop(&B::Lt, &T::I8, 0xff, 0), 1); // -1 < 0
        assert_eq!(binop(&B::Lt, &T::U8, 0xff, 0), 0);
        assert_eq!(binop(&B::Add, &T::Bool, 1, 1), 0);
        assert_eq!(binop(&B::Shl, &T::U128, 1, 127), 1 << 127);
        assert_eq!(unop(&c::UnOp::Not, &T::U8, 0x0f), 0xf0);
        assert_eq!(unop(&c::UnOp::Not, &T::Bool, 1), 0);
        assert_eq!(unop(&c::UnOp::Neg, &T::I8, 1), 0xff);
        assert_eq!(cast(&T::I8, &T::U32, 0xff), 0xffff_ffff);
        assert_eq!(cast(&T::U8, &T::U32, 0xff), 0xff);
        assert_eq!(cast(&T::U64, &T::U8, 0x1234), 0x34);
        assert_eq!(cast(&T::I64, &T::U128, u64::MAX as u128), u128::MAX);
        assert_eq!(cast(&T::Bool, &T::U8, 1), 1);
    }
}
