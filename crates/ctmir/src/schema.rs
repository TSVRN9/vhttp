//! The schema decode. `decode_<t>(j, x)` (trusted) says that `x` is the value serde's derive
//! writes as `j`, for the types in `mir`:
//! - a struct is an object with exactly its fields, keys in declaration order (checked by position);
//! - a newtype struct is its inner value, a tuple is an array, `Option` is `null` or the bare value;
//! - an enum is externally tagged: a unit variant is its name as a string, any other variant is
//!   `{"Name": payload}`, where a one-field tuple variant's payload is the field itself, a wider one
//!   an array, a struct variant an object;
//! - an integer is a non-negative `Num` within its rustc width (a range check);
//! - a name the mirror does not know decodes to that enum's `Unknown(j)`; a known name with the
//!   wrong shape decodes to nothing.
//!
//! Each relation branches on `j` only and pins every field of `x` by `==` or a sub-relation, so it
//! is a function of `j` up to `Vec` views. The exec `dec_<t>` take `j` by value and move the raw
//! `Json` parts into the result (a copy could not be proved equal: `Vec` equality does not follow
//! from view equality). Each ensures `Some(x) => decode_<t>(j, x)` and
//! `None => forall|x| !decode_<t>(j, x)`.
use crate::json::{bytes_eq, Json};
use crate::mir::*;
use vstd::prelude::*;

verus! {

// ================================================================== the trusted spec

// ------------------------------------------------------------------ JSON shapes

pub open spec fn items(j: Json) -> Seq<Json> { match j { Json::Arr(v) => v@, _ => Seq::empty() } }
/// An array of exactly `n` elements; `at(j, i)` is element `i`.
pub open spec fn arr(j: Json, n: nat) -> bool { j is Arr && items(j).len() == n }
pub open spec fn at(j: Json, i: int) -> Json { items(j)[i] }

pub open spec fn members(j: Json) -> Seq<(Vec<u8>, Json)> { match j { Json::Obj(f) => f@, _ => Seq::empty() } }
/// An object of exactly `n` members; `key(j, i)` and `fld(j, i)` are member `i`'s name and value.
pub open spec fn obj(j: Json, n: nat) -> bool { j is Obj && members(j).len() == n }
pub open spec fn key(j: Json, i: int) -> Seq<u8> { members(j)[i].0@ }
pub open spec fn fld(j: Json, i: int) -> Json { members(j)[i].1 }

/// An externally tagged enum value: a name, or a one-member object `{"Name": payload}`.
pub open spec fn is_enum(j: Json) -> bool { j is Str || obj(j, 1) }
pub open spec fn tag(j: Json) -> Seq<u8> { match j { Json::Str(s) => s@, _ => key(j, 0) } }
/// A unit variant (no payload). The payload of any other variant is `fld(j, 0)`.
pub open spec fn unit(j: Json) -> bool { j is Str }

// ------------------------------------------------------------------ scalars, options, lists

pub open spec fn decode_usize(j: Json, x: usize) -> bool { j == Json::Num(false, x as u128) }
pub open spec fn decode_u128(j: Json, x: u128) -> bool { j == Json::Num(false, x) }
pub open spec fn decode_u64(j: Json, x: u64) -> bool { j == Json::Num(false, x as u128) }
pub open spec fn decode_u32(j: Json, x: u32) -> bool { j == Json::Num(false, x as u128) }
pub open spec fn decode_u16(j: Json, x: u16) -> bool { j == Json::Num(false, x as u128) }
pub open spec fn decode_u8(j: Json, x: u8) -> bool { j == Json::Num(false, x as u128) }
pub open spec fn decode_bool(j: Json, x: bool) -> bool { j == Json::Bool(x) }
pub open spec fn decode_str(j: Json, x: Vec<u8>) -> bool { j == Json::Str(x) }

pub open spec fn decode_opt_usize(j: Json, x: Option<usize>) -> bool {
    if j == Json::Null { x is None } else { x matches Some(n) && decode_usize(j, n) }
}
pub open spec fn decode_opt_u128(j: Json, x: Option<u128>) -> bool {
    if j == Json::Null { x is None } else { x matches Some(n) && decode_u128(j, n) }
}
pub open spec fn decode_opt_u64(j: Json, x: Option<u64>) -> bool {
    if j == Json::Null { x is None } else { x matches Some(n) && decode_u64(j, n) }
}
pub open spec fn decode_opt_u16(j: Json, x: Option<u16>) -> bool {
    if j == Json::Null { x is None } else { x matches Some(n) && decode_u16(j, n) }
}
pub open spec fn decode_opt_u8(j: Json, x: Option<u8>) -> bool {
    if j == Json::Null { x is None } else { x matches Some(n) && decode_u8(j, n) }
}
pub open spec fn decode_opt_body(j: Json, x: Option<Body>) -> bool {
    if j == Json::Null { x is None } else { x matches Some(b) && decode_body(j, b) }
}
pub open spec fn decode_opt_fn_sig(j: Json, x: Option<FnSig>) -> bool {
    if j == Json::Null { x is None } else { x matches Some(s) && decode_fn_sig(j, s) }
}

/// A `Vec<T>`: an array whose elements decode, in order, to `xs`.
pub open spec fn decode_list<T>(j: Json, xs: Seq<T>, f: spec_fn(Json, T) -> bool) -> bool {
    j is Arr && items(j).len() == xs.len() && forall|i: int| #![trigger xs[i]] 0 <= i < xs.len() ==> f(items(j)[i], xs[i])
}

pub open spec fn decode_strs(j: Json, xs: Seq<Vec<u8>>) -> bool { decode_list(j, xs, |j: Json, x: Vec<u8>| decode_str(j, x)) }
pub open spec fn decode_tys(j: Json, xs: Seq<Ty>) -> bool { decode_list(j, xs, |j: Json, x: Ty| decode_usize(j, x)) }
pub open spec fn decode_bytes(j: Json, xs: Seq<Option<u8>>) -> bool { decode_list(j, xs, |j: Json, x: Option<u8>| decode_opt_u8(j, x)) }

// ------------------------------------------------------------------ bodies (mir/body.rs)

pub open spec fn decode_body(j: Json, x: Body) -> bool {
    obj(j, 6)
    && key(j, 0) == b"blocks"@ && decode_blocks(fld(j, 0), x.blocks@)
    && key(j, 1) == b"locals"@ && decode_locals(fld(j, 1), x.locals@)
    && key(j, 2) == b"arg_count"@ && decode_usize(fld(j, 2), x.arg_count)
    && key(j, 3) == b"var_debug_info"@ && decode_var_debug_infos(fld(j, 3), x.var_debug_info@)
    && key(j, 4) == b"spread_arg"@ && decode_opt_usize(fld(j, 4), x.spread_arg)
    && key(j, 5) == b"span"@ && decode_usize(fld(j, 5), x.span)
}
pub open spec fn decode_blocks(j: Json, xs: Seq<BasicBlock>) -> bool { decode_list(j, xs, |j: Json, x: BasicBlock| decode_basic_block(j, x)) }
pub open spec fn decode_locals(j: Json, xs: Seq<LocalDecl>) -> bool { decode_list(j, xs, |j: Json, x: LocalDecl| decode_local_decl(j, x)) }
pub open spec fn decode_var_debug_infos(j: Json, xs: Seq<VarDebugInfo>) -> bool {
    decode_list(j, xs, |j: Json, x: VarDebugInfo| decode_var_debug_info(j, x))
}

pub open spec fn decode_local_decl(j: Json, x: LocalDecl) -> bool {
    obj(j, 3)
    && key(j, 0) == b"ty"@ && decode_usize(fld(j, 0), x.ty)
    && key(j, 1) == b"span"@ && decode_usize(fld(j, 1), x.span)
    && key(j, 2) == b"mutability"@ && decode_mutability(fld(j, 2), x.mutability)
}

pub open spec fn decode_basic_block(j: Json, x: BasicBlock) -> bool {
    obj(j, 2)
    && key(j, 0) == b"statements"@ && decode_statements(fld(j, 0), x.statements@)
    && key(j, 1) == b"terminator"@ && decode_terminator(fld(j, 1), x.terminator)
}
pub open spec fn decode_statements(j: Json, xs: Seq<Statement>) -> bool { decode_list(j, xs, |j: Json, x: Statement| decode_statement(j, x)) }

pub open spec fn decode_terminator(j: Json, x: Terminator) -> bool {
    obj(j, 2)
    && key(j, 0) == b"kind"@ && decode_terminator_kind(fld(j, 0), x.kind)
    && key(j, 1) == b"span"@ && decode_usize(fld(j, 1), x.span)
}

pub open spec fn decode_terminator_kind(j: Json, x: TerminatorKind) -> bool {
    let (n, p) = (tag(j), fld(j, 0));
    is_enum(j) && if n == b"Goto"@ {
        x matches TerminatorKind::Goto { target } && !unit(j) && obj(p, 1)
        && key(p, 0) == b"target"@ && decode_usize(fld(p, 0), target)
    } else if n == b"SwitchInt"@ {
        x matches TerminatorKind::SwitchInt { discr, targets } && !unit(j) && obj(p, 2)
        && key(p, 0) == b"discr"@ && decode_operand(fld(p, 0), discr)
        && key(p, 1) == b"targets"@ && decode_switch_targets(fld(p, 1), targets)
    } else if n == b"Resume"@ { unit(j) && x == TerminatorKind::Resume
    } else if n == b"Abort"@ { unit(j) && x == TerminatorKind::Abort
    } else if n == b"Return"@ { unit(j) && x == TerminatorKind::Return
    } else if n == b"Unreachable"@ { unit(j) && x == TerminatorKind::Unreachable
    } else if n == b"Drop"@ {
        x matches TerminatorKind::Drop { place, target, unwind } && !unit(j) && obj(p, 3)
        && key(p, 0) == b"place"@ && decode_place(fld(p, 0), place)
        && key(p, 1) == b"target"@ && decode_usize(fld(p, 1), target)
        && key(p, 2) == b"unwind"@ && unwind == fld(p, 2)
    } else if n == b"Call"@ {
        x matches TerminatorKind::Call { func, args, destination, target, unwind } && !unit(j) && obj(p, 5)
        && key(p, 0) == b"func"@ && decode_operand(fld(p, 0), func)
        && key(p, 1) == b"args"@ && decode_operands(fld(p, 1), args@)
        && key(p, 2) == b"destination"@ && decode_place(fld(p, 2), destination)
        && key(p, 3) == b"target"@ && decode_opt_usize(fld(p, 3), target)
        && key(p, 4) == b"unwind"@ && unwind == fld(p, 4)
    } else if n == b"Assert"@ {
        x matches TerminatorKind::Assert { cond, expected, msg, target, unwind } && !unit(j) && obj(p, 5)
        && key(p, 0) == b"cond"@ && decode_operand(fld(p, 0), cond)
        && key(p, 1) == b"expected"@ && decode_bool(fld(p, 1), expected)
        && key(p, 2) == b"msg"@ && msg == fld(p, 2)
        && key(p, 3) == b"target"@ && decode_usize(fld(p, 3), target)
        && key(p, 4) == b"unwind"@ && unwind == fld(p, 4)
    } else if n == b"InlineAsm"@ {
        x matches TerminatorKind::InlineAsm { template, operands, options, line_spans, destination, unwind } && !unit(j) && obj(p, 6)
        && key(p, 0) == b"template"@ && template == fld(p, 0)
        && key(p, 1) == b"operands"@ && operands == fld(p, 1)
        && key(p, 2) == b"options"@ && options == fld(p, 2)
        && key(p, 3) == b"line_spans"@ && line_spans == fld(p, 3)
        && key(p, 4) == b"destination"@ && destination == fld(p, 4)
        && key(p, 5) == b"unwind"@ && unwind == fld(p, 5)
    } else { x == TerminatorKind::Unknown(j) }
}

pub open spec fn decode_statement(j: Json, x: Statement) -> bool {
    obj(j, 2)
    && key(j, 0) == b"kind"@ && decode_statement_kind(fld(j, 0), x.kind)
    && key(j, 1) == b"span"@ && decode_usize(fld(j, 1), x.span)
}

pub open spec fn decode_statement_kind(j: Json, x: StatementKind) -> bool {
    let (n, p) = (tag(j), fld(j, 0));
    is_enum(j) && if n == b"Assign"@ {
        x matches StatementKind::Assign(pl, rv) && !unit(j) && arr(p, 2) && decode_place(at(p, 0), pl) && decode_rvalue(at(p, 1), rv)
    } else if n == b"FakeRead"@ {
        x matches StatementKind::FakeRead(c, pl) && !unit(j) && arr(p, 2) && c == at(p, 0) && decode_place(at(p, 1), pl)
    } else if n == b"SetDiscriminant"@ {
        x matches StatementKind::SetDiscriminant { place, variant_index } && !unit(j) && obj(p, 2)
        && key(p, 0) == b"place"@ && decode_place(fld(p, 0), place)
        && key(p, 1) == b"variant_index"@ && decode_usize(fld(p, 1), variant_index)
    } else if n == b"StorageLive"@ { x matches StatementKind::StorageLive(l) && !unit(j) && decode_usize(p, l)
    } else if n == b"StorageDead"@ { x matches StatementKind::StorageDead(l) && !unit(j) && decode_usize(p, l)
    } else if n == b"PlaceMention"@ { x matches StatementKind::PlaceMention(pl) && !unit(j) && decode_place(p, pl)
    } else if n == b"AscribeUserType"@ {
        x matches StatementKind::AscribeUserType { place, projections, variance } && !unit(j) && obj(p, 3)
        && key(p, 0) == b"place"@ && decode_place(fld(p, 0), place)
        && key(p, 1) == b"projections"@ && projections == fld(p, 1)
        && key(p, 2) == b"variance"@ && variance == fld(p, 2)
    } else if n == b"Coverage"@ { x matches StatementKind::Coverage(c) && !unit(j) && c == p
    } else if n == b"Intrinsic"@ { x matches StatementKind::Intrinsic(i) && !unit(j) && i == p
    } else if n == b"ConstEvalCounter"@ { unit(j) && x == StatementKind::ConstEvalCounter
    } else if n == b"Nop"@ { unit(j) && x == StatementKind::Nop
    } else { x == StatementKind::Unknown(j) }
}

pub open spec fn decode_rvalue(j: Json, x: Rvalue) -> bool {
    let (n, p) = (tag(j), fld(j, 0));
    is_enum(j) && if n == b"AddressOf"@ {
        x matches Rvalue::AddressOf(k, pl) && !unit(j) && arr(p, 2) && k == at(p, 0) && decode_place(at(p, 1), pl)
    } else if n == b"Aggregate"@ {
        x matches Rvalue::Aggregate(k, ops) && !unit(j) && arr(p, 2) && decode_aggregate_kind(at(p, 0), k) && decode_operands(at(p, 1), ops@)
    } else if n == b"BinaryOp"@ {
        x matches Rvalue::BinaryOp(op, a, b) && !unit(j) && arr(p, 3)
        && decode_bin_op(at(p, 0), op) && decode_operand(at(p, 1), a) && decode_operand(at(p, 2), b)
    } else if n == b"Cast"@ {
        x matches Rvalue::Cast(k, a, t) && !unit(j) && arr(p, 3)
        && decode_cast_kind(at(p, 0), k) && decode_operand(at(p, 1), a) && decode_usize(at(p, 2), t)
    } else if n == b"CheckedBinaryOp"@ {
        x matches Rvalue::CheckedBinaryOp(op, a, b) && !unit(j) && arr(p, 3)
        && decode_bin_op(at(p, 0), op) && decode_operand(at(p, 1), a) && decode_operand(at(p, 2), b)
    } else if n == b"CopyForDeref"@ { x matches Rvalue::CopyForDeref(pl) && !unit(j) && decode_place(p, pl)
    } else if n == b"Discriminant"@ { x matches Rvalue::Discriminant(pl) && !unit(j) && decode_place(p, pl)
    } else if n == b"Len"@ { x matches Rvalue::Len(pl) && !unit(j) && decode_place(p, pl)
    } else if n == b"Ref"@ {
        x matches Rvalue::Ref(r, k, pl) && !unit(j) && arr(p, 3)
        && r == at(p, 0) && decode_borrow_kind(at(p, 1), k) && decode_place(at(p, 2), pl)
    } else if n == b"Repeat"@ {
        x matches Rvalue::Repeat(a, c) && !unit(j) && arr(p, 2) && decode_operand(at(p, 0), a) && decode_ty_const(at(p, 1), c)
    } else if n == b"ThreadLocalRef"@ { x matches Rvalue::ThreadLocalRef(i) && !unit(j) && i == p
    } else if n == b"UnaryOp"@ {
        x matches Rvalue::UnaryOp(op, a) && !unit(j) && arr(p, 2) && decode_un_op(at(p, 0), op) && decode_operand(at(p, 1), a)
    } else if n == b"Use"@ {
        x matches Rvalue::Use(a, r) && !unit(j) && arr(p, 2) && decode_operand(at(p, 0), a) && r == at(p, 1)
    } else if n == b"Reborrow"@ {
        x matches Rvalue::Reborrow(t, m, pl) && !unit(j) && arr(p, 3)
        && decode_usize(at(p, 0), t) && decode_mutability(at(p, 1), m) && decode_place(at(p, 2), pl)
    } else { x == Rvalue::Unknown(j) }
}

pub open spec fn decode_bin_op(j: Json, x: BinOp) -> bool {
    let n = tag(j);
    is_enum(j) && if n == b"Add"@ { unit(j) && x == BinOp::Add }
    else if n == b"AddUnchecked"@ { unit(j) && x == BinOp::AddUnchecked }
    else if n == b"Sub"@ { unit(j) && x == BinOp::Sub }
    else if n == b"SubUnchecked"@ { unit(j) && x == BinOp::SubUnchecked }
    else if n == b"Mul"@ { unit(j) && x == BinOp::Mul }
    else if n == b"MulUnchecked"@ { unit(j) && x == BinOp::MulUnchecked }
    else if n == b"Div"@ { unit(j) && x == BinOp::Div }
    else if n == b"Rem"@ { unit(j) && x == BinOp::Rem }
    else if n == b"BitXor"@ { unit(j) && x == BinOp::BitXor }
    else if n == b"BitAnd"@ { unit(j) && x == BinOp::BitAnd }
    else if n == b"BitOr"@ { unit(j) && x == BinOp::BitOr }
    else if n == b"Shl"@ { unit(j) && x == BinOp::Shl }
    else if n == b"ShlUnchecked"@ { unit(j) && x == BinOp::ShlUnchecked }
    else if n == b"Shr"@ { unit(j) && x == BinOp::Shr }
    else if n == b"ShrUnchecked"@ { unit(j) && x == BinOp::ShrUnchecked }
    else if n == b"Eq"@ { unit(j) && x == BinOp::Eq }
    else if n == b"Lt"@ { unit(j) && x == BinOp::Lt }
    else if n == b"Le"@ { unit(j) && x == BinOp::Le }
    else if n == b"Ne"@ { unit(j) && x == BinOp::Ne }
    else if n == b"Ge"@ { unit(j) && x == BinOp::Ge }
    else if n == b"Gt"@ { unit(j) && x == BinOp::Gt }
    else if n == b"Cmp"@ { unit(j) && x == BinOp::Cmp }
    else if n == b"Offset"@ { unit(j) && x == BinOp::Offset }
    else { x == BinOp::Unknown(j) }
}

pub open spec fn decode_un_op(j: Json, x: UnOp) -> bool {
    let n = tag(j);
    is_enum(j) && if n == b"Not"@ { unit(j) && x == UnOp::Not }
    else if n == b"Neg"@ { unit(j) && x == UnOp::Neg }
    else if n == b"PtrMetadata"@ { unit(j) && x == UnOp::PtrMetadata }
    else { x == UnOp::Unknown(j) }
}

pub open spec fn decode_aggregate_kind(j: Json, x: AggregateKind) -> bool {
    let (n, p) = (tag(j), fld(j, 0));
    is_enum(j) && if n == b"Array"@ { x matches AggregateKind::Array(t) && !unit(j) && decode_usize(p, t)
    } else if n == b"Tuple"@ { unit(j) && x == AggregateKind::Tuple
    } else if n == b"Adt"@ {
        x matches AggregateKind::Adt(d, v, args, u, f) && !unit(j) && arr(p, 5)
        && decode_usize(at(p, 0), d) && decode_usize(at(p, 1), v) && decode_generic_args(at(p, 2), args)
        && u == at(p, 3) && decode_opt_usize(at(p, 4), f)
    } else if n == b"Closure"@ {
        x matches AggregateKind::Closure(d, args) && !unit(j) && arr(p, 2) && decode_usize(at(p, 0), d) && decode_generic_args(at(p, 1), args)
    } else if n == b"Coroutine"@ { x matches AggregateKind::Coroutine(d, a) && !unit(j) && arr(p, 2) && d == at(p, 0) && a == at(p, 1)
    } else if n == b"CoroutineClosure"@ {
        x matches AggregateKind::CoroutineClosure(d, a) && !unit(j) && arr(p, 2) && d == at(p, 0) && a == at(p, 1)
    } else if n == b"RawPtr"@ {
        x matches AggregateKind::RawPtr(t, m) && !unit(j) && arr(p, 2) && decode_usize(at(p, 0), t) && decode_mutability(at(p, 1), m)
    } else { x == AggregateKind::Unknown(j) }
}

pub open spec fn decode_operand(j: Json, x: Operand) -> bool {
    let (n, p) = (tag(j), fld(j, 0));
    is_enum(j) && if n == b"Copy"@ { x matches Operand::Copy(pl) && !unit(j) && decode_place(p, pl)
    } else if n == b"Move"@ { x matches Operand::Move(pl) && !unit(j) && decode_place(p, pl)
    } else if n == b"Constant"@ { x matches Operand::Constant(c) && !unit(j) && decode_const_operand(p, c)
    } else if n == b"RuntimeChecks"@ { x matches Operand::RuntimeChecks(r) && !unit(j) && r == p
    } else { x == Operand::Unknown(j) }
}
pub open spec fn decode_operands(j: Json, xs: Seq<Operand>) -> bool { decode_list(j, xs, |j: Json, x: Operand| decode_operand(j, x)) }

pub open spec fn decode_place(j: Json, x: Place) -> bool {
    obj(j, 2)
    && key(j, 0) == b"local"@ && decode_usize(fld(j, 0), x.local)
    && key(j, 1) == b"projection"@ && decode_projection(fld(j, 1), x.projection@)
}
pub open spec fn decode_projection(j: Json, xs: Seq<ProjectionElem>) -> bool {
    decode_list(j, xs, |j: Json, x: ProjectionElem| decode_projection_elem(j, x))
}

pub open spec fn decode_const_operand(j: Json, x: ConstOperand) -> bool {
    obj(j, 3)
    && key(j, 0) == b"span"@ && decode_usize(fld(j, 0), x.span)
    && key(j, 1) == b"user_ty"@ && x.user_ty == fld(j, 1)
    && key(j, 2) == b"const_"@ && decode_mir_const(fld(j, 2), x.const_)
}

pub open spec fn decode_var_debug_info(j: Json, x: VarDebugInfo) -> bool {
    obj(j, 5)
    && key(j, 0) == b"name"@ && decode_str(fld(j, 0), x.name)
    && key(j, 1) == b"source_info"@ && x.source_info == fld(j, 1)
    && key(j, 2) == b"composite"@ && x.composite == fld(j, 2)
    && key(j, 3) == b"value"@ && decode_var_debug_info_contents(fld(j, 3), x.value)
    && key(j, 4) == b"argument_index"@ && decode_opt_u16(fld(j, 4), x.argument_index)
}

pub open spec fn decode_var_debug_info_contents(j: Json, x: VarDebugInfoContents) -> bool {
    let (n, p) = (tag(j), fld(j, 0));
    is_enum(j) && if n == b"Place"@ { x matches VarDebugInfoContents::Place(pl) && !unit(j) && decode_place(p, pl)
    } else if n == b"Const"@ { x matches VarDebugInfoContents::Const(c) && !unit(j) && decode_const_operand(p, c)
    } else { x == VarDebugInfoContents::Unknown(j) }
}

pub open spec fn decode_projection_elem(j: Json, x: ProjectionElem) -> bool {
    let (n, p) = (tag(j), fld(j, 0));
    is_enum(j) && if n == b"Deref"@ { unit(j) && x == ProjectionElem::Deref
    } else if n == b"Field"@ {
        x matches ProjectionElem::Field(f, t) && !unit(j) && arr(p, 2) && decode_usize(at(p, 0), f) && decode_usize(at(p, 1), t)
    } else if n == b"Index"@ { x matches ProjectionElem::Index(l) && !unit(j) && decode_usize(p, l)
    } else if n == b"ConstantIndex"@ {
        x matches ProjectionElem::ConstantIndex { offset, min_length, from_end } && !unit(j) && obj(p, 3)
        && key(p, 0) == b"offset"@ && decode_u64(fld(p, 0), offset)
        && key(p, 1) == b"min_length"@ && decode_u64(fld(p, 1), min_length)
        && key(p, 2) == b"from_end"@ && decode_bool(fld(p, 2), from_end)
    } else if n == b"Subslice"@ {
        x matches ProjectionElem::Subslice { from, to, from_end } && !unit(j) && obj(p, 3)
        && key(p, 0) == b"from"@ && decode_u64(fld(p, 0), from)
        && key(p, 1) == b"to"@ && decode_u64(fld(p, 1), to)
        && key(p, 2) == b"from_end"@ && decode_bool(fld(p, 2), from_end)
    } else if n == b"Downcast"@ { x matches ProjectionElem::Downcast(v) && !unit(j) && decode_usize(p, v)
    } else if n == b"OpaqueCast"@ { x matches ProjectionElem::OpaqueCast(t) && !unit(j) && decode_usize(p, t)
    } else { x == ProjectionElem::Unknown(j) }
}

pub open spec fn decode_switch_targets(j: Json, x: SwitchTargets) -> bool {
    obj(j, 2)
    && key(j, 0) == b"branches"@ && decode_branches(fld(j, 0), x.branches@)
    && key(j, 1) == b"otherwise"@ && decode_usize(fld(j, 1), x.otherwise)
}
pub open spec fn decode_branch(j: Json, x: (u128, BasicBlockIdx)) -> bool { arr(j, 2) && decode_u128(at(j, 0), x.0) && decode_usize(at(j, 1), x.1) }
pub open spec fn decode_branches(j: Json, xs: Seq<(u128, BasicBlockIdx)>) -> bool {
    decode_list(j, xs, |j: Json, x: (u128, BasicBlockIdx)| decode_branch(j, x))
}

pub open spec fn decode_borrow_kind(j: Json, x: BorrowKind) -> bool {
    let (n, p) = (tag(j), fld(j, 0));
    is_enum(j) && if n == b"Shared"@ { unit(j) && x == BorrowKind::Shared
    } else if n == b"Fake"@ { x matches BorrowKind::Fake(k) && !unit(j) && k == p
    } else if n == b"Mut"@ { x matches BorrowKind::Mut { kind } && !unit(j) && obj(p, 1) && key(p, 0) == b"kind"@ && kind == fld(p, 0)
    } else { x == BorrowKind::Unknown(j) }
}

pub open spec fn decode_mutability(j: Json, x: Mutability) -> bool {
    let n = tag(j);
    is_enum(j) && if n == b"Not"@ { unit(j) && x == Mutability::Not }
    else if n == b"Mut"@ { unit(j) && x == Mutability::Mut }
    else { x == Mutability::Unknown(j) }
}

pub open spec fn decode_pointer_coercion(j: Json, x: PointerCoercion) -> bool {
    let (n, p) = (tag(j), fld(j, 0));
    is_enum(j) && if n == b"ReifyFnPointer"@ { x matches PointerCoercion::ReifyFnPointer(s) && !unit(j) && s == p
    } else if n == b"UnsafeFnPointer"@ { unit(j) && x == PointerCoercion::UnsafeFnPointer
    } else if n == b"ClosureFnPointer"@ { x matches PointerCoercion::ClosureFnPointer(s) && !unit(j) && s == p
    } else if n == b"MutToConstPointer"@ { unit(j) && x == PointerCoercion::MutToConstPointer
    } else if n == b"ArrayToPointer"@ { unit(j) && x == PointerCoercion::ArrayToPointer
    } else if n == b"Unsize"@ { unit(j) && x == PointerCoercion::Unsize
    } else { x == PointerCoercion::Unknown(j) }
}

pub open spec fn decode_cast_kind(j: Json, x: CastKind) -> bool {
    let (n, p) = (tag(j), fld(j, 0));
    is_enum(j) && if n == b"PointerExposeAddress"@ { unit(j) && x == CastKind::PointerExposeAddress
    } else if n == b"PointerWithExposedProvenance"@ { unit(j) && x == CastKind::PointerWithExposedProvenance
    } else if n == b"PointerCoercion"@ { x matches CastKind::PointerCoercion(c) && !unit(j) && decode_pointer_coercion(p, c)
    } else if n == b"IntToInt"@ { unit(j) && x == CastKind::IntToInt
    } else if n == b"FloatToInt"@ { unit(j) && x == CastKind::FloatToInt
    } else if n == b"FloatToFloat"@ { unit(j) && x == CastKind::FloatToFloat
    } else if n == b"IntToFloat"@ { unit(j) && x == CastKind::IntToFloat
    } else if n == b"PtrToPtr"@ { unit(j) && x == CastKind::PtrToPtr
    } else if n == b"FnPtrToPtr"@ { unit(j) && x == CastKind::FnPtrToPtr
    } else if n == b"Transmute"@ { unit(j) && x == CastKind::Transmute
    } else if n == b"Subtype"@ { unit(j) && x == CastKind::Subtype
    } else { x == CastKind::Unknown(j) }
}

// ------------------------------------------------------------------ constants and types (ty.rs)

pub open spec fn decode_mir_const(j: Json, x: MirConst) -> bool {
    obj(j, 3)
    && key(j, 0) == b"kind"@ && decode_constant_kind(fld(j, 0), x.kind)
    && key(j, 1) == b"ty"@ && decode_usize(fld(j, 1), x.ty)
    && key(j, 2) == b"id"@ && decode_usize(fld(j, 2), x.id)
}

pub open spec fn decode_constant_kind(j: Json, x: ConstantKind) -> bool {
    let (n, p) = (tag(j), fld(j, 0));
    is_enum(j) && if n == b"Ty"@ { x matches ConstantKind::Ty(c) && !unit(j) && decode_ty_const(p, c)
    } else if n == b"Allocated"@ { x matches ConstantKind::Allocated(a) && !unit(j) && decode_allocation(p, a)
    } else if n == b"Unevaluated"@ { x matches ConstantKind::Unevaluated(u) && !unit(j) && u == p
    } else if n == b"Param"@ { x matches ConstantKind::Param(c) && !unit(j) && c == p
    } else if n == b"ZeroSized"@ { unit(j) && x == ConstantKind::ZeroSized
    } else { x == ConstantKind::Unknown(j) }
}

pub open spec fn decode_allocation(j: Json, x: Allocation) -> bool {
    obj(j, 4)
    && key(j, 0) == b"bytes"@ && decode_bytes(fld(j, 0), x.bytes@)
    && key(j, 1) == b"provenance"@ && decode_provenance_map(fld(j, 1), x.provenance)
    && key(j, 2) == b"align"@ && decode_u64(fld(j, 2), x.align)
    && key(j, 3) == b"mutability"@ && decode_mutability(fld(j, 3), x.mutability)
}

pub open spec fn decode_provenance_map(j: Json, x: ProvenanceMap) -> bool {
    obj(j, 1) && key(j, 0) == b"ptrs"@ && decode_ptrs(fld(j, 0), x.ptrs@)
}
pub open spec fn decode_ptr(j: Json, x: (usize, AllocId)) -> bool { arr(j, 2) && decode_usize(at(j, 0), x.0) && decode_usize(at(j, 1), x.1) }
pub open spec fn decode_ptrs(j: Json, xs: Seq<(usize, AllocId)>) -> bool { decode_list(j, xs, |j: Json, x: (usize, AllocId)| decode_ptr(j, x)) }

pub open spec fn decode_ty_const(j: Json, x: TyConst) -> bool {
    obj(j, 2)
    && key(j, 0) == b"kind"@ && x.kind == fld(j, 0)
    && key(j, 1) == b"id"@ && decode_usize(fld(j, 1), x.id)
}

pub open spec fn decode_ty_kind(j: Json, x: TyKind) -> bool {
    let (n, p) = (tag(j), fld(j, 0));
    is_enum(j) && if n == b"RigidTy"@ { x matches TyKind::RigidTy(t) && !unit(j) && decode_rigid_ty(p, t)
    } else if n == b"Alias"@ { x matches TyKind::Alias(k, t) && !unit(j) && arr(p, 2) && k == at(p, 0) && t == at(p, 1)
    } else if n == b"Param"@ { x matches TyKind::Param(t) && !unit(j) && t == p
    } else if n == b"Bound"@ { x matches TyKind::Bound(i, t) && !unit(j) && arr(p, 2) && i == at(p, 0) && t == at(p, 1)
    } else { x == TyKind::Unknown(j) }
}

pub open spec fn decode_rigid_ty(j: Json, x: RigidTy) -> bool {
    let (n, p) = (tag(j), fld(j, 0));
    is_enum(j) && if n == b"Bool"@ { unit(j) && x == RigidTy::Bool
    } else if n == b"Char"@ { unit(j) && x == RigidTy::Char
    } else if n == b"Int"@ { x matches RigidTy::Int(t) && !unit(j) && decode_int_ty(p, t)
    } else if n == b"Uint"@ { x matches RigidTy::Uint(t) && !unit(j) && decode_uint_ty(p, t)
    } else if n == b"Float"@ { x matches RigidTy::Float(t) && !unit(j) && t == p
    } else if n == b"Adt"@ {
        x matches RigidTy::Adt(d, args) && !unit(j) && arr(p, 2) && decode_usize(at(p, 0), d) && decode_generic_args(at(p, 1), args)
    } else if n == b"Foreign"@ { x matches RigidTy::Foreign(d) && !unit(j) && d == p
    } else if n == b"Str"@ { unit(j) && x == RigidTy::Str
    } else if n == b"Array"@ {
        x matches RigidTy::Array(t, c) && !unit(j) && arr(p, 2) && decode_usize(at(p, 0), t) && decode_ty_const(at(p, 1), c)
    } else if n == b"Pat"@ { x matches RigidTy::Pat(t, pat) && !unit(j) && arr(p, 2) && decode_usize(at(p, 0), t) && pat == at(p, 1)
    } else if n == b"Slice"@ { x matches RigidTy::Slice(t) && !unit(j) && decode_usize(p, t)
    } else if n == b"RawPtr"@ {
        x matches RigidTy::RawPtr(t, m) && !unit(j) && arr(p, 2) && decode_usize(at(p, 0), t) && decode_mutability(at(p, 1), m)
    } else if n == b"Ref"@ {
        x matches RigidTy::Ref(r, t, m) && !unit(j) && arr(p, 3)
        && r == at(p, 0) && decode_usize(at(p, 1), t) && decode_mutability(at(p, 2), m)
    } else if n == b"FnDef"@ {
        x matches RigidTy::FnDef(d, args) && !unit(j) && arr(p, 2) && decode_usize(at(p, 0), d) && decode_generic_args(at(p, 1), args)
    } else if n == b"FnPtr"@ { x matches RigidTy::FnPtr(s) && !unit(j) && s == p
    } else if n == b"Closure"@ {
        x matches RigidTy::Closure(d, args) && !unit(j) && arr(p, 2) && decode_usize(at(p, 0), d) && decode_generic_args(at(p, 1), args)
    } else if n == b"Coroutine"@ { x matches RigidTy::Coroutine(d, a) && !unit(j) && arr(p, 2) && d == at(p, 0) && a == at(p, 1)
    } else if n == b"CoroutineClosure"@ { x matches RigidTy::CoroutineClosure(d, a) && !unit(j) && arr(p, 2) && d == at(p, 0) && a == at(p, 1)
    } else if n == b"Dynamic"@ { x matches RigidTy::Dynamic(d, r) && !unit(j) && arr(p, 2) && d == at(p, 0) && r == at(p, 1)
    } else if n == b"Never"@ { unit(j) && x == RigidTy::Never
    } else if n == b"Tuple"@ { x matches RigidTy::Tuple(ts) && !unit(j) && decode_tys(p, ts@)
    } else if n == b"CoroutineWitness"@ { x matches RigidTy::CoroutineWitness(d, a) && !unit(j) && arr(p, 2) && d == at(p, 0) && a == at(p, 1)
    } else { x == RigidTy::Unknown(j) }
}

pub open spec fn decode_int_ty(j: Json, x: IntTy) -> bool {
    let n = tag(j);
    is_enum(j) && if n == b"Isize"@ { unit(j) && x == IntTy::Isize }
    else if n == b"I8"@ { unit(j) && x == IntTy::I8 }
    else if n == b"I16"@ { unit(j) && x == IntTy::I16 }
    else if n == b"I32"@ { unit(j) && x == IntTy::I32 }
    else if n == b"I64"@ { unit(j) && x == IntTy::I64 }
    else if n == b"I128"@ { unit(j) && x == IntTy::I128 }
    else { x == IntTy::Unknown(j) }
}

pub open spec fn decode_uint_ty(j: Json, x: UintTy) -> bool {
    let n = tag(j);
    is_enum(j) && if n == b"Usize"@ { unit(j) && x == UintTy::Usize }
    else if n == b"U8"@ { unit(j) && x == UintTy::U8 }
    else if n == b"U16"@ { unit(j) && x == UintTy::U16 }
    else if n == b"U32"@ { unit(j) && x == UintTy::U32 }
    else if n == b"U64"@ { unit(j) && x == UintTy::U64 }
    else if n == b"U128"@ { unit(j) && x == UintTy::U128 }
    else { x == UintTy::Unknown(j) }
}

/// A newtype struct: its inner `Vec<GenericArgKind>`.
pub open spec fn decode_generic_args(j: Json, x: GenericArgs) -> bool { decode_generic_arg_kinds(j, x.0@) }
pub open spec fn decode_generic_arg_kinds(j: Json, xs: Seq<GenericArgKind>) -> bool {
    decode_list(j, xs, |j: Json, x: GenericArgKind| decode_generic_arg_kind(j, x))
}

pub open spec fn decode_generic_arg_kind(j: Json, x: GenericArgKind) -> bool {
    let (n, p) = (tag(j), fld(j, 0));
    is_enum(j) && if n == b"Lifetime"@ { x matches GenericArgKind::Lifetime(r) && !unit(j) && r == p
    } else if n == b"Type"@ { x matches GenericArgKind::Type(t) && !unit(j) && decode_usize(p, t)
    } else if n == b"Const"@ { x matches GenericArgKind::Const(c) && !unit(j) && decode_ty_const(p, c)
    } else { x == GenericArgKind::Unknown(j) }
}

pub open spec fn decode_fn_sig(j: Json, x: FnSig) -> bool {
    obj(j, 4)
    && key(j, 0) == b"inputs_and_output"@ && decode_tys(fld(j, 0), x.inputs_and_output@)
    && key(j, 1) == b"c_variadic"@ && decode_bool(fld(j, 1), x.c_variadic)
    && key(j, 2) == b"safety"@ && x.safety == fld(j, 2)
    && key(j, 3) == b"abi"@ && x.abi == fld(j, 3)
}

pub open spec fn decode_adt_kind(j: Json, x: AdtKind) -> bool {
    let n = tag(j);
    is_enum(j) && if n == b"Enum"@ { unit(j) && x == AdtKind::Enum }
    else if n == b"Union"@ { unit(j) && x == AdtKind::Union }
    else if n == b"Struct"@ { unit(j) && x == AdtKind::Struct }
    else { x == AdtKind::Unknown(j) }
}

pub open spec fn decode_instance_kind(j: Json, x: InstanceKind) -> bool {
    let (n, p) = (tag(j), fld(j, 0));
    is_enum(j) && if n == b"Item"@ { unit(j) && x == InstanceKind::Item
    } else if n == b"Intrinsic"@ { unit(j) && x == InstanceKind::Intrinsic
    } else if n == b"Virtual"@ {
        x matches InstanceKind::Virtual { idx } && !unit(j) && obj(p, 1) && key(p, 0) == b"idx"@ && decode_usize(fld(p, 0), idx)
    } else if n == b"Shim"@ { unit(j) && x == InstanceKind::Shim
    } else { x == InstanceKind::Unknown(j) }
}

pub open spec fn decode_global_alloc(j: Json, x: GlobalAlloc) -> bool {
    let (n, p) = (tag(j), fld(j, 0));
    is_enum(j) && if n == b"Function"@ { x matches GlobalAlloc::Function(i) && !unit(j) && i == p
    } else if n == b"VTable"@ { x matches GlobalAlloc::VTable(t, r) && !unit(j) && arr(p, 2) && t == at(p, 0) && r == at(p, 1)
    } else if n == b"Static"@ { x matches GlobalAlloc::Static(d) && !unit(j) && decode_usize(p, d)
    } else if n == b"Memory"@ { x matches GlobalAlloc::Memory(a) && !unit(j) && decode_allocation(p, a)
    } else if n == b"TypeId"@ {
        x matches GlobalAlloc::TypeId { ty } && !unit(j) && obj(p, 1) && key(p, 0) == b"ty"@ && decode_usize(fld(p, 0), ty)
    } else { x == GlobalAlloc::Unknown(j) }
}

// ------------------------------------------------------------------ layouts (abi.rs)

pub open spec fn decode_layout_shape(j: Json, x: LayoutShape) -> bool {
    obj(j, 5)
    && key(j, 0) == b"fields"@ && decode_fields_shape(fld(j, 0), x.fields)
    && key(j, 1) == b"variants"@ && decode_variants_shape(fld(j, 1), x.variants)
    && key(j, 2) == b"abi"@ && x.abi == fld(j, 2)
    && key(j, 3) == b"abi_align"@ && decode_u64(fld(j, 3), x.abi_align)
    && key(j, 4) == b"size"@ && decode_machine_size(fld(j, 4), x.size)
}

pub open spec fn decode_machine_size(j: Json, x: MachineSize) -> bool {
    obj(j, 1) && key(j, 0) == b"num_bits"@ && decode_usize(fld(j, 0), x.num_bits)
}
pub open spec fn decode_machine_sizes(j: Json, xs: Seq<MachineSize>) -> bool {
    decode_list(j, xs, |j: Json, x: MachineSize| decode_machine_size(j, x))
}

pub open spec fn decode_fields_shape(j: Json, x: FieldsShape) -> bool {
    let (n, p) = (tag(j), fld(j, 0));
    is_enum(j) && if n == b"Primitive"@ { unit(j) && x == FieldsShape::Primitive
    } else if n == b"Union"@ { x matches FieldsShape::Union(c) && !unit(j) && c != 0 && decode_usize(p, c)
    } else if n == b"Array"@ {
        x matches FieldsShape::Array { stride, count } && !unit(j) && obj(p, 2)
        && key(p, 0) == b"stride"@ && decode_machine_size(fld(p, 0), stride)
        && key(p, 1) == b"count"@ && decode_u64(fld(p, 1), count)
    } else if n == b"Arbitrary"@ {
        x matches FieldsShape::Arbitrary { offsets } && !unit(j) && obj(p, 1)
        && key(p, 0) == b"offsets"@ && decode_machine_sizes(fld(p, 0), offsets@)
    } else { x == FieldsShape::Unknown(j) }
}

pub open spec fn decode_variants_shape(j: Json, x: VariantsShape) -> bool {
    let (n, p) = (tag(j), fld(j, 0));
    is_enum(j) && if n == b"Empty"@ { unit(j) && x == VariantsShape::Empty
    } else if n == b"Single"@ {
        x matches VariantsShape::Single { index } && !unit(j) && obj(p, 1) && key(p, 0) == b"index"@ && decode_usize(fld(p, 0), index)
    } else if n == b"Multiple"@ {
        x matches VariantsShape::Multiple { tag, tag_encoding, tag_field, variants } && !unit(j) && obj(p, 4)
        && key(p, 0) == b"tag"@ && decode_scalar(fld(p, 0), tag)
        && key(p, 1) == b"tag_encoding"@ && decode_tag_encoding(fld(p, 1), tag_encoding)
        && key(p, 2) == b"tag_field"@ && decode_usize(fld(p, 2), tag_field)
        && key(p, 3) == b"variants"@ && decode_variant_fields_list(fld(p, 3), variants@)
    } else { x == VariantsShape::Unknown(j) }
}

pub open spec fn decode_variant_fields(j: Json, x: VariantFields) -> bool {
    obj(j, 1) && key(j, 0) == b"offsets"@ && decode_machine_sizes(fld(j, 0), x.offsets@)
}
pub open spec fn decode_variant_fields_list(j: Json, xs: Seq<VariantFields>) -> bool {
    decode_list(j, xs, |j: Json, x: VariantFields| decode_variant_fields(j, x))
}

pub open spec fn decode_tag_encoding(j: Json, x: TagEncoding) -> bool {
    let (n, p) = (tag(j), fld(j, 0));
    is_enum(j) && if n == b"Direct"@ { unit(j) && x == TagEncoding::Direct
    } else if n == b"Niche"@ {
        x matches TagEncoding::Niche { untagged_variant, niche_variants, niche_start } && !unit(j) && obj(p, 3)
        && key(p, 0) == b"untagged_variant"@ && decode_usize(fld(p, 0), untagged_variant)
        && key(p, 1) == b"niche_variants"@ && decode_range_inclusive(fld(p, 1), niche_variants)
        && key(p, 2) == b"niche_start"@ && decode_u128(fld(p, 2), niche_start)
    } else { x == TagEncoding::Unknown(j) }
}

pub open spec fn decode_range_inclusive(j: Json, x: RangeInclusive) -> bool {
    obj(j, 2)
    && key(j, 0) == b"start"@ && decode_usize(fld(j, 0), x.start)
    && key(j, 1) == b"end"@ && decode_usize(fld(j, 1), x.end)
}

pub open spec fn decode_scalar(j: Json, x: Scalar) -> bool {
    let (n, p) = (tag(j), fld(j, 0));
    is_enum(j) && if n == b"Initialized"@ {
        x matches Scalar::Initialized { value, valid_range } && !unit(j) && obj(p, 2)
        && key(p, 0) == b"value"@ && decode_primitive(fld(p, 0), value)
        && key(p, 1) == b"valid_range"@ && decode_wrapping_range(fld(p, 1), valid_range)
    } else if n == b"Union"@ {
        x matches Scalar::Union { value } && !unit(j) && obj(p, 1) && key(p, 0) == b"value"@ && decode_primitive(fld(p, 0), value)
    } else { x == Scalar::Unknown(j) }
}

pub open spec fn decode_primitive(j: Json, x: Primitive) -> bool {
    let (n, p) = (tag(j), fld(j, 0));
    is_enum(j) && if n == b"Int"@ {
        x matches Primitive::Int { length, signed } && !unit(j) && obj(p, 2)
        && key(p, 0) == b"length"@ && decode_integer_length(fld(p, 0), length)
        && key(p, 1) == b"signed"@ && decode_bool(fld(p, 1), signed)
    } else if n == b"Float"@ {
        x matches Primitive::Float { length } && !unit(j) && obj(p, 1) && key(p, 0) == b"length"@ && length == fld(p, 0)
    } else if n == b"Pointer"@ { x matches Primitive::Pointer(a) && !unit(j) && decode_u32(p, a)
    } else { x == Primitive::Unknown(j) }
}

pub open spec fn decode_integer_length(j: Json, x: IntegerLength) -> bool {
    let n = tag(j);
    is_enum(j) && if n == b"I8"@ { unit(j) && x == IntegerLength::I8 }
    else if n == b"I16"@ { unit(j) && x == IntegerLength::I16 }
    else if n == b"I32"@ { unit(j) && x == IntegerLength::I32 }
    else if n == b"I64"@ { unit(j) && x == IntegerLength::I64 }
    else if n == b"I128"@ { unit(j) && x == IntegerLength::I128 }
    else { x == IntegerLength::Unknown(j) }
}

pub open spec fn decode_wrapping_range(j: Json, x: WrappingRange) -> bool {
    obj(j, 2)
    && key(j, 0) == b"start"@ && decode_u128(fld(j, 0), x.start)
    && key(j, 1) == b"end"@ && decode_u128(fld(j, 1), x.end)
}

// ------------------------------------------------------------------ the dump's tables (spec §Dump)

pub open spec fn decode_crate(j: Json, x: MirCrate) -> bool {
    obj(j, 11)
    && key(j, 0) == b"crate"@ && decode_str(fld(j, 0), x.crate_name)
    && key(j, 1) == b"items"@ && decode_items(fld(j, 1), x.items@)
    && key(j, 2) == b"insts"@ && decode_insts(fld(j, 2), x.insts@)
    && key(j, 3) == b"calls"@ && decode_calls(fld(j, 3), x.calls@)
    && key(j, 4) == b"drops"@ && decode_drops(fld(j, 4), x.drops@)
    && key(j, 5) == b"tys"@ && decode_ty_rows(fld(j, 5), x.tys@)
    && key(j, 6) == b"adts"@ && decode_adts(fld(j, 6), x.adts@)
    && key(j, 7) == b"consts"@ && decode_consts(fld(j, 7), x.consts@)
    && key(j, 8) == b"layouts"@ && decode_layouts(fld(j, 8), x.layouts@)
    && key(j, 9) == b"allocs"@ && decode_allocs(fld(j, 9), x.allocs@)
    && key(j, 10) == b"spans"@ && decode_spans(fld(j, 10), x.spans@)
}

pub open spec fn decode_items(j: Json, xs: Seq<Item>) -> bool { decode_list(j, xs, |j: Json, x: Item| decode_item(j, x)) }
pub open spec fn decode_insts(j: Json, xs: Seq<Inst>) -> bool { decode_list(j, xs, |j: Json, x: Inst| decode_inst(j, x)) }
pub open spec fn decode_calls(j: Json, xs: Seq<Call>) -> bool { decode_list(j, xs, |j: Json, x: Call| decode_call(j, x)) }
pub open spec fn decode_drops(j: Json, xs: Seq<DropRow>) -> bool { decode_list(j, xs, |j: Json, x: DropRow| decode_drop_row(j, x)) }
pub open spec fn decode_ty_rows(j: Json, xs: Seq<TyRow>) -> bool { decode_list(j, xs, |j: Json, x: TyRow| decode_ty_row(j, x)) }
pub open spec fn decode_adts(j: Json, xs: Seq<Adt>) -> bool { decode_list(j, xs, |j: Json, x: Adt| decode_adt(j, x)) }
pub open spec fn decode_consts(j: Json, xs: Seq<ConstRow>) -> bool { decode_list(j, xs, |j: Json, x: ConstRow| decode_const_row(j, x)) }
pub open spec fn decode_layouts(j: Json, xs: Seq<LayoutRow>) -> bool { decode_list(j, xs, |j: Json, x: LayoutRow| decode_layout_row(j, x)) }
pub open spec fn decode_allocs(j: Json, xs: Seq<AllocRow>) -> bool { decode_list(j, xs, |j: Json, x: AllocRow| decode_alloc_row(j, x)) }
pub open spec fn decode_spans(j: Json, xs: Seq<SpanRow>) -> bool { decode_list(j, xs, |j: Json, x: SpanRow| decode_span_row(j, x)) }

pub open spec fn decode_item(j: Json, x: Item) -> bool {
    obj(j, 4)
    && key(j, 0) == b"def"@ && decode_usize(fld(j, 0), x.def)
    && key(j, 1) == b"name"@ && decode_str(fld(j, 1), x.name)
    && key(j, 2) == b"inst"@ && decode_opt_usize(fld(j, 2), x.inst)
    && key(j, 3) == b"attrs"@ && decode_strs(fld(j, 3), x.attrs@)
}

pub open spec fn decode_inst(j: Json, x: Inst) -> bool {
    obj(j, 8)
    && key(j, 0) == b"id"@ && decode_usize(fld(j, 0), x.id)
    && key(j, 1) == b"def"@ && decode_usize(fld(j, 1), x.def)
    && key(j, 2) == b"name"@ && decode_str(fld(j, 2), x.name)
    && key(j, 3) == b"key"@ && decode_str(fld(j, 3), x.key)
    && key(j, 4) == b"krate"@ && decode_str(fld(j, 4), x.krate)
    && key(j, 5) == b"kind"@ && decode_instance_kind(fld(j, 5), x.kind)
    && key(j, 6) == b"body"@ && decode_opt_body(fld(j, 6), x.body)
    && key(j, 7) == b"fn_sig"@ && decode_opt_fn_sig(fld(j, 7), x.fn_sig)
}

pub open spec fn decode_call(j: Json, x: Call) -> bool {
    obj(j, 5)
    && key(j, 0) == b"fn_ty"@ && decode_usize(fld(j, 0), x.fn_ty)
    && key(j, 1) == b"def"@ && decode_usize(fld(j, 1), x.def)
    && key(j, 2) == b"def_name"@ && decode_str(fld(j, 2), x.def_name)
    && key(j, 3) == b"args"@ && decode_generic_args(fld(j, 3), x.args)
    && key(j, 4) == b"resolved"@ && decode_opt_usize(fld(j, 4), x.resolved)
}

pub open spec fn decode_drop_row(j: Json, x: DropRow) -> bool {
    obj(j, 3)
    && key(j, 0) == b"ty"@ && decode_usize(fld(j, 0), x.ty)
    && key(j, 1) == b"glue"@ && decode_usize(fld(j, 1), x.glue)
    && key(j, 2) == b"empty"@ && decode_bool(fld(j, 2), x.empty)
}

pub open spec fn decode_ty_row(j: Json, x: TyRow) -> bool {
    obj(j, 2)
    && key(j, 0) == b"id"@ && decode_usize(fld(j, 0), x.id)
    && key(j, 1) == b"kind"@ && decode_ty_kind(fld(j, 1), x.kind)
}

pub open spec fn decode_adt(j: Json, x: Adt) -> bool {
    obj(j, 5)
    && key(j, 0) == b"ty"@ && decode_usize(fld(j, 0), x.ty)
    && key(j, 1) == b"name"@ && decode_str(fld(j, 1), x.name)
    && key(j, 2) == b"kind"@ && decode_adt_kind(fld(j, 2), x.kind)
    && key(j, 3) == b"is_box"@ && decode_bool(fld(j, 3), x.is_box)
    && key(j, 4) == b"variants"@ && decode_adt_variants(fld(j, 4), x.variants@)
}

pub open spec fn decode_adt_variants(j: Json, xs: Seq<AdtVariant>) -> bool { decode_list(j, xs, |j: Json, x: AdtVariant| decode_adt_variant(j, x)) }

pub open spec fn decode_adt_variant(j: Json, x: AdtVariant) -> bool {
    obj(j, 2)
    && key(j, 0) == b"discr"@ && decode_opt_u128(fld(j, 0), x.discr)
    && key(j, 1) == b"fields"@ && decode_tys(fld(j, 1), x.fields@)
}

pub open spec fn decode_const_row(j: Json, x: ConstRow) -> bool {
    obj(j, 2)
    && key(j, 0) == b"id"@ && decode_usize(fld(j, 0), x.id)
    && key(j, 1) == b"usize"@ && decode_opt_u64(fld(j, 1), x.usize)
}

pub open spec fn decode_layout_row(j: Json, x: LayoutRow) -> bool {
    obj(j, 2)
    && key(j, 0) == b"ty"@ && decode_usize(fld(j, 0), x.ty)
    && key(j, 1) == b"shape"@ && decode_layout_shape(fld(j, 1), x.shape)
}

pub open spec fn decode_alloc_row(j: Json, x: AllocRow) -> bool {
    obj(j, 2)
    && key(j, 0) == b"id"@ && decode_usize(fld(j, 0), x.id)
    && key(j, 1) == b"alloc"@ && decode_global_alloc(fld(j, 1), x.alloc)
}

pub open spec fn decode_span_row(j: Json, x: SpanRow) -> bool {
    obj(j, 3)
    && key(j, 0) == b"id"@ && decode_usize(fld(j, 0), x.id)
    && key(j, 1) == b"file"@ && decode_str(fld(j, 1), x.file)
    && key(j, 2) == b"line"@ && decode_usize(fld(j, 2), x.line)
}

// ================================================================== the exec decoders (verified)

// ------------------------------------------------------------------ shapes, moving parts out

/// Moves element `i` out of `v`, leaving `Null` in its place.
fn take(v: &mut Vec<Json>, i: usize) -> (r: Json)
    requires i < old(v)@.len(),
    ensures
        r == old(v)@[i as int], final(v)@.len() == old(v)@.len(),
        forall|k: int| 0 <= k < old(v)@.len() && k != i ==> final(v)@[k] == old(v)@[k],
{
    let mut t = Json::Null;
    v.set_and_swap(i, &mut t);
    t
}

/// Moves member `i`'s value out of `f`.
fn take_fld(f: &mut Vec<(Vec<u8>, Json)>, i: usize) -> (r: Json)
    requires i < old(f)@.len(),
    ensures
        r == old(f)@[i as int].1, final(f)@.len() == old(f)@.len(),
        forall|k: int| 0 <= k < old(f)@.len() && k != i ==> final(f)@[k] == old(f)@[k],
{
    let mut t = (Vec::new(), Json::Null);
    f.set_and_swap(i, &mut t);
    t.1
}

fn is_null(j: &Json) -> (r: bool) ensures r == (*j == Json::Null) { match j { Json::Null => true, _ => false } }
fn is_str(j: &Json) -> (r: bool) ensures r == (*j is Str) { match j { Json::Str(_) => true, _ => false } }
fn is_obj(j: &Json, n: usize) -> (r: bool) ensures r == obj(*j, n as nat) { match j { Json::Obj(f) => f.len() == n, _ => false } }
fn is_enum_x(j: &Json) -> (r: bool) ensures r == is_enum(*j) {
    match j { Json::Str(_) => true, Json::Obj(f) => f.len() == 1, _ => false }
}

fn key_is(j: &Json, i: usize, k: &[u8]) -> (r: bool)
    ensures r == (j is Obj && i < members(*j).len() && key(*j, i as int) == k@),
{
    match j { Json::Obj(f) => i < f.len() && bytes_eq(f[i].0.as_slice(), k), _ => false }
}

fn tag_x(j: &Json) -> (r: &[u8])
    requires is_enum(*j),
    ensures r@ == tag(*j),
{
    match j { Json::Str(s) => s.as_slice(), Json::Obj(f) => f[0].0.as_slice(), _ => vstd::pervasive::unreached() }
}

fn into_members(j: Json) -> (r: Vec<(Vec<u8>, Json)>)
    requires j is Obj,
    ensures r@ == members(j),
{
    match j { Json::Obj(f) => f, _ => vstd::pervasive::unreached() }
}

fn into_arr(j: Json, n: usize) -> (r: Option<Vec<Json>>)
    ensures match r { Some(v) => arr(j, n as nat) && v@ == items(j), None => !arr(j, n as nat) },
{
    match j { Json::Arr(v) => if v.len() == n { Some(v) } else { None }, _ => None }
}

/// The payload of a non-unit variant.
fn payload(j: Json) -> (r: Json)
    requires obj(j, 1),
    ensures r == fld(j, 0),
{
    let mut f = into_members(j);
    take_fld(&mut f, 0)
}

// ------------------------------------------------------------------ scalars and options

pub fn dec_usize(j: Json) -> (r: Option<usize>)
    ensures match r { Some(x) => decode_usize(j, x), None => forall|x: usize| !decode_usize(j, x) },
{
    match j { Json::Num(neg, m) => if !neg && m <= usize::MAX as u128 { Some(m as usize) } else { None }, _ => None }
}

pub fn dec_u128(j: Json) -> (r: Option<u128>)
    ensures match r { Some(x) => decode_u128(j, x), None => forall|x: u128| !decode_u128(j, x) },
{
    match j { Json::Num(neg, m) => if !neg { Some(m) } else { None }, _ => None }
}

pub fn dec_u64(j: Json) -> (r: Option<u64>)
    ensures match r { Some(x) => decode_u64(j, x), None => forall|x: u64| !decode_u64(j, x) },
{
    match j { Json::Num(neg, m) => if !neg && m <= u64::MAX as u128 { Some(m as u64) } else { None }, _ => None }
}

pub fn dec_u32(j: Json) -> (r: Option<u32>)
    ensures match r { Some(x) => decode_u32(j, x), None => forall|x: u32| !decode_u32(j, x) },
{
    match j { Json::Num(neg, m) => if !neg && m <= u32::MAX as u128 { Some(m as u32) } else { None }, _ => None }
}

pub fn dec_u16(j: Json) -> (r: Option<u16>)
    ensures match r { Some(x) => decode_u16(j, x), None => forall|x: u16| !decode_u16(j, x) },
{
    match j { Json::Num(neg, m) => if !neg && m <= u16::MAX as u128 { Some(m as u16) } else { None }, _ => None }
}

pub fn dec_u8(j: Json) -> (r: Option<u8>)
    ensures match r { Some(x) => decode_u8(j, x), None => forall|x: u8| !decode_u8(j, x) },
{
    match j { Json::Num(neg, m) => if !neg && m <= u8::MAX as u128 { Some(m as u8) } else { None }, _ => None }
}

pub fn dec_bool(j: Json) -> (r: Option<bool>)
    ensures match r { Some(x) => decode_bool(j, x), None => forall|x: bool| !decode_bool(j, x) },
{
    match j { Json::Bool(b) => Some(b), _ => None }
}

pub fn dec_str(j: Json) -> (r: Option<Vec<u8>>)
    ensures match r { Some(x) => decode_str(j, x), None => forall|x: Vec<u8>| !decode_str(j, x) },
{
    match j { Json::Str(s) => Some(s), _ => None }
}

pub fn dec_opt_usize(j: Json) -> (r: Option<Option<usize>>)
    ensures match r { Some(x) => decode_opt_usize(j, x), None => forall|x: Option<usize>| !decode_opt_usize(j, x) },
{
    if is_null(&j) { return Some(None); }
    Some(Some(dec_usize(j)?))
}

pub fn dec_opt_u128(j: Json) -> (r: Option<Option<u128>>)
    ensures match r { Some(x) => decode_opt_u128(j, x), None => forall|x: Option<u128>| !decode_opt_u128(j, x) },
{
    if is_null(&j) { return Some(None); }
    Some(Some(dec_u128(j)?))
}

pub fn dec_opt_u64(j: Json) -> (r: Option<Option<u64>>)
    ensures match r { Some(x) => decode_opt_u64(j, x), None => forall|x: Option<u64>| !decode_opt_u64(j, x) },
{
    if is_null(&j) { return Some(None); }
    Some(Some(dec_u64(j)?))
}

pub fn dec_opt_u16(j: Json) -> (r: Option<Option<u16>>)
    ensures match r { Some(x) => decode_opt_u16(j, x), None => forall|x: Option<u16>| !decode_opt_u16(j, x) },
{
    if is_null(&j) { return Some(None); }
    Some(Some(dec_u16(j)?))
}

pub fn dec_opt_u8(j: Json) -> (r: Option<Option<u8>>)
    ensures match r { Some(x) => decode_opt_u8(j, x), None => forall|x: Option<u8>| !decode_opt_u8(j, x) },
{
    if is_null(&j) { return Some(None); }
    Some(Some(dec_u8(j)?))
}

pub fn dec_opt_body(j: Json) -> (r: Option<Option<Body>>)
    ensures match r { Some(x) => decode_opt_body(j, x), None => forall|x: Option<Body>| !decode_opt_body(j, x) },
{
    if is_null(&j) { return Some(None); }
    Some(Some(dec_body(j)?))
}

pub fn dec_opt_fn_sig(j: Json) -> (r: Option<Option<FnSig>>)
    ensures match r { Some(x) => decode_opt_fn_sig(j, x), None => forall|x: Option<FnSig>| !decode_opt_fn_sig(j, x) },
{
    if is_null(&j) { return Some(None); }
    Some(Some(dec_fn_sig(j)?))
}

// ------------------------------------------------------------------ pairs

fn dec_branch(j: Json) -> (r: Option<(u128, BasicBlockIdx)>)
    ensures match r { Some(x) => decode_branch(j, x), None => forall|x: (u128, BasicBlockIdx)| !decode_branch(j, x) },
{
    let mut a = into_arr(j, 2)?;
    let v = dec_u128(take(&mut a, 0))?;
    let b = dec_usize(take(&mut a, 1))?;
    Some((v, b))
}

fn dec_ptr(j: Json) -> (r: Option<(usize, AllocId)>)
    ensures match r { Some(x) => decode_ptr(j, x), None => forall|x: (usize, AllocId)| !decode_ptr(j, x) },
{
    let mut a = into_arr(j, 2)?;
    let o = dec_usize(take(&mut a, 0))?;
    let p = dec_usize(take(&mut a, 1))?;
    Some((o, p))
}

} // verus!

/// `$name(j)` decodes a `Vec<$t>` against `$spec` (a `decode_list` of `$espec`), element by
/// element with `$elem`.
macro_rules! dec_list {
    ($name:ident, $t:ty, $spec:ident, $espec:ident, $elem:ident) => {
        verus! {
        pub fn $name(j: Json) -> (r: Option<Vec<$t>>)
            ensures match r { Some(xs) => $spec(j, xs@), None => forall|xs: Seq<$t>| !$spec(j, xs) },
        {
            let mut v = match j { Json::Arr(v) => v, _ => { return None; } };
            let ghost s = v@;
            let mut out: Vec<$t> = Vec::new();
            let mut i: usize = 0;
            while i < v.len()
                invariant
                    j is Arr, s == items(j), i <= v.len(), v@.len() == s.len(),
                    forall|k: int| i <= k < s.len() ==> #[trigger] v@[k] == s[k],
                    out@.len() == i, forall|k: int| 0 <= k < i ==> $espec(s[k], #[trigger] out@[k]),
                decreases v.len() - i,
            {
                match $elem(take(&mut v, i)) {
                    Some(e) => { out.push(e); },
                    None => {
                        assert forall|xs: Seq<$t>| !$spec(j, xs) by {
                            if $spec(j, xs) { assert($espec(s[i as int], xs[i as int])); }
                        }
                        return None;
                    },
                }
                i += 1;
            }
            Some(out)
        }
        }
    };
}

dec_list!(dec_strs, Vec<u8>, decode_strs, decode_str, dec_str);
dec_list!(dec_tys, Ty, decode_tys, decode_usize, dec_usize);
dec_list!(dec_bytes, Option<u8>, decode_bytes, decode_opt_u8, dec_opt_u8);
dec_list!(dec_branches, (u128, BasicBlockIdx), decode_branches, decode_branch, dec_branch);
dec_list!(dec_ptrs, (usize, AllocId), decode_ptrs, decode_ptr, dec_ptr);
dec_list!(dec_blocks, BasicBlock, decode_blocks, decode_basic_block, dec_basic_block);
dec_list!(dec_locals, LocalDecl, decode_locals, decode_local_decl, dec_local_decl);
dec_list!(dec_var_debug_infos, VarDebugInfo, decode_var_debug_infos, decode_var_debug_info, dec_var_debug_info);
dec_list!(dec_statements, Statement, decode_statements, decode_statement, dec_statement);
dec_list!(dec_operands, Operand, decode_operands, decode_operand, dec_operand);
dec_list!(dec_projection, ProjectionElem, decode_projection, decode_projection_elem, dec_projection_elem);
dec_list!(dec_generic_arg_kinds, GenericArgKind, decode_generic_arg_kinds, decode_generic_arg_kind, dec_generic_arg_kind);
dec_list!(dec_machine_sizes, MachineSize, decode_machine_sizes, decode_machine_size, dec_machine_size);
dec_list!(dec_variant_fields_list, VariantFields, decode_variant_fields_list, decode_variant_fields, dec_variant_fields);
dec_list!(dec_adt_variants, AdtVariant, decode_adt_variants, decode_adt_variant, dec_adt_variant);
dec_list!(dec_items, Item, decode_items, decode_item, dec_item);
dec_list!(dec_insts, Inst, decode_insts, decode_inst, dec_inst);
dec_list!(dec_calls, Call, decode_calls, decode_call, dec_call);
dec_list!(dec_drops, DropRow, decode_drops, decode_drop_row, dec_drop_row);
dec_list!(dec_ty_rows, TyRow, decode_ty_rows, decode_ty_row, dec_ty_row);
dec_list!(dec_adts, Adt, decode_adts, decode_adt, dec_adt);
dec_list!(dec_consts, ConstRow, decode_consts, decode_const_row, dec_const_row);
dec_list!(dec_layouts, LayoutRow, decode_layouts, decode_layout_row, dec_layout_row);
dec_list!(dec_allocs, AllocRow, decode_allocs, decode_alloc_row, dec_alloc_row);
dec_list!(dec_spans, SpanRow, decode_spans, decode_span_row, dec_span_row);

verus! {

// ------------------------------------------------------------------ bodies

pub fn dec_body(j: Json) -> (r: Option<Body>)
    ensures match r { Some(x) => decode_body(j, x), None => forall|x: Body| !decode_body(j, x) },
{
    if !(is_obj(&j, 6) && key_is(&j, 0, b"blocks") && key_is(&j, 1, b"locals") && key_is(&j, 2, b"arg_count")
        && key_is(&j, 3, b"var_debug_info") && key_is(&j, 4, b"spread_arg") && key_is(&j, 5, b"span")) { return None; }
    let mut f = into_members(j);
    let blocks = dec_blocks(take_fld(&mut f, 0))?;
    let locals = dec_locals(take_fld(&mut f, 1))?;
    let arg_count = dec_usize(take_fld(&mut f, 2))?;
    let var_debug_info = dec_var_debug_infos(take_fld(&mut f, 3))?;
    let spread_arg = dec_opt_usize(take_fld(&mut f, 4))?;
    let span = dec_usize(take_fld(&mut f, 5))?;
    Some(Body { blocks, locals, arg_count, var_debug_info, spread_arg, span })
}

fn dec_local_decl(j: Json) -> (r: Option<LocalDecl>)
    ensures match r { Some(x) => decode_local_decl(j, x), None => forall|x: LocalDecl| !decode_local_decl(j, x) },
{
    if !(is_obj(&j, 3) && key_is(&j, 0, b"ty") && key_is(&j, 1, b"span") && key_is(&j, 2, b"mutability")) { return None; }
    let mut f = into_members(j);
    let ty = dec_usize(take_fld(&mut f, 0))?;
    let span = dec_usize(take_fld(&mut f, 1))?;
    let mutability = dec_mutability(take_fld(&mut f, 2))?;
    Some(LocalDecl { ty, span, mutability })
}

fn dec_basic_block(j: Json) -> (r: Option<BasicBlock>)
    ensures match r { Some(x) => decode_basic_block(j, x), None => forall|x: BasicBlock| !decode_basic_block(j, x) },
{
    if !(is_obj(&j, 2) && key_is(&j, 0, b"statements") && key_is(&j, 1, b"terminator")) { return None; }
    let mut f = into_members(j);
    let statements = dec_statements(take_fld(&mut f, 0))?;
    let terminator = dec_terminator(take_fld(&mut f, 1))?;
    Some(BasicBlock { statements, terminator })
}

fn dec_terminator(j: Json) -> (r: Option<Terminator>)
    ensures match r { Some(x) => decode_terminator(j, x), None => forall|x: Terminator| !decode_terminator(j, x) },
{
    if !(is_obj(&j, 2) && key_is(&j, 0, b"kind") && key_is(&j, 1, b"span")) { return None; }
    let mut f = into_members(j);
    let kind = dec_terminator_kind(take_fld(&mut f, 0))?;
    let span = dec_usize(take_fld(&mut f, 1))?;
    Some(Terminator { kind, span })
}

pub fn dec_terminator_kind(j: Json) -> (r: Option<TerminatorKind>)
    ensures match r { Some(x) => decode_terminator_kind(j, x), None => forall|x: TerminatorKind| !decode_terminator_kind(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    if bytes_eq(t, b"Goto") {
        if u { return None; }
        let p = payload(j);
        if !(is_obj(&p, 1) && key_is(&p, 0, b"target")) { return None; }
        let mut f = into_members(p);
        let target = dec_usize(take_fld(&mut f, 0))?;
        Some(TerminatorKind::Goto { target })
    } else if bytes_eq(t, b"SwitchInt") {
        if u { return None; }
        let p = payload(j);
        if !(is_obj(&p, 2) && key_is(&p, 0, b"discr") && key_is(&p, 1, b"targets")) { return None; }
        let mut f = into_members(p);
        let discr = dec_operand(take_fld(&mut f, 0))?;
        let targets = dec_switch_targets(take_fld(&mut f, 1))?;
        Some(TerminatorKind::SwitchInt { discr, targets })
    } else if bytes_eq(t, b"Resume") {
        if u { Some(TerminatorKind::Resume) } else { None }
    } else if bytes_eq(t, b"Abort") {
        if u { Some(TerminatorKind::Abort) } else { None }
    } else if bytes_eq(t, b"Return") {
        if u { Some(TerminatorKind::Return) } else { None }
    } else if bytes_eq(t, b"Unreachable") {
        if u { Some(TerminatorKind::Unreachable) } else { None }
    } else if bytes_eq(t, b"Drop") {
        if u { return None; }
        let p = payload(j);
        if !(is_obj(&p, 3) && key_is(&p, 0, b"place") && key_is(&p, 1, b"target") && key_is(&p, 2, b"unwind")) { return None; }
        let mut f = into_members(p);
        let place = dec_place(take_fld(&mut f, 0))?;
        let target = dec_usize(take_fld(&mut f, 1))?;
        let unwind = take_fld(&mut f, 2);
        Some(TerminatorKind::Drop { place, target, unwind })
    } else if bytes_eq(t, b"Call") {
        if u { return None; }
        let p = payload(j);
        if !(is_obj(&p, 5) && key_is(&p, 0, b"func") && key_is(&p, 1, b"args") && key_is(&p, 2, b"destination")
            && key_is(&p, 3, b"target") && key_is(&p, 4, b"unwind")) { return None; }
        let mut f = into_members(p);
        let func = dec_operand(take_fld(&mut f, 0))?;
        let args = dec_operands(take_fld(&mut f, 1))?;
        let destination = dec_place(take_fld(&mut f, 2))?;
        let target = dec_opt_usize(take_fld(&mut f, 3))?;
        let unwind = take_fld(&mut f, 4);
        Some(TerminatorKind::Call { func, args, destination, target, unwind })
    } else if bytes_eq(t, b"Assert") {
        if u { return None; }
        let p = payload(j);
        if !(is_obj(&p, 5) && key_is(&p, 0, b"cond") && key_is(&p, 1, b"expected") && key_is(&p, 2, b"msg")
            && key_is(&p, 3, b"target") && key_is(&p, 4, b"unwind")) { return None; }
        let mut f = into_members(p);
        let cond = dec_operand(take_fld(&mut f, 0))?;
        let expected = dec_bool(take_fld(&mut f, 1))?;
        let msg = take_fld(&mut f, 2);
        let target = dec_usize(take_fld(&mut f, 3))?;
        let unwind = take_fld(&mut f, 4);
        Some(TerminatorKind::Assert { cond, expected, msg, target, unwind })
    } else if bytes_eq(t, b"InlineAsm") {
        if u { return None; }
        let p = payload(j);
        if !(is_obj(&p, 6) && key_is(&p, 0, b"template") && key_is(&p, 1, b"operands") && key_is(&p, 2, b"options")
            && key_is(&p, 3, b"line_spans") && key_is(&p, 4, b"destination") && key_is(&p, 5, b"unwind")) { return None; }
        let mut f = into_members(p);
        let template = take_fld(&mut f, 0);
        let operands = take_fld(&mut f, 1);
        let options = take_fld(&mut f, 2);
        let line_spans = take_fld(&mut f, 3);
        let destination = take_fld(&mut f, 4);
        let unwind = take_fld(&mut f, 5);
        Some(TerminatorKind::InlineAsm { template, operands, options, line_spans, destination, unwind })
    } else {
        Some(TerminatorKind::Unknown(j))
    }
}

fn dec_statement(j: Json) -> (r: Option<Statement>)
    ensures match r { Some(x) => decode_statement(j, x), None => forall|x: Statement| !decode_statement(j, x) },
{
    if !(is_obj(&j, 2) && key_is(&j, 0, b"kind") && key_is(&j, 1, b"span")) { return None; }
    let mut f = into_members(j);
    let kind = dec_statement_kind(take_fld(&mut f, 0))?;
    let span = dec_usize(take_fld(&mut f, 1))?;
    Some(Statement { kind, span })
}

pub fn dec_statement_kind(j: Json) -> (r: Option<StatementKind>)
    ensures match r { Some(x) => decode_statement_kind(j, x), None => forall|x: StatementKind| !decode_statement_kind(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    if bytes_eq(t, b"Assign") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let pl = dec_place(take(&mut a, 0))?;
        let rv = dec_rvalue(take(&mut a, 1))?;
        Some(StatementKind::Assign(pl, rv))
    } else if bytes_eq(t, b"FakeRead") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let c = take(&mut a, 0);
        let pl = dec_place(take(&mut a, 1))?;
        Some(StatementKind::FakeRead(c, pl))
    } else if bytes_eq(t, b"SetDiscriminant") {
        if u { return None; }
        let p = payload(j);
        if !(is_obj(&p, 2) && key_is(&p, 0, b"place") && key_is(&p, 1, b"variant_index")) { return None; }
        let mut f = into_members(p);
        let place = dec_place(take_fld(&mut f, 0))?;
        let variant_index = dec_usize(take_fld(&mut f, 1))?;
        Some(StatementKind::SetDiscriminant { place, variant_index })
    } else if bytes_eq(t, b"StorageLive") {
        if u { return None; }
        Some(StatementKind::StorageLive(dec_usize(payload(j))?))
    } else if bytes_eq(t, b"StorageDead") {
        if u { return None; }
        Some(StatementKind::StorageDead(dec_usize(payload(j))?))
    } else if bytes_eq(t, b"PlaceMention") {
        if u { return None; }
        Some(StatementKind::PlaceMention(dec_place(payload(j))?))
    } else if bytes_eq(t, b"AscribeUserType") {
        if u { return None; }
        let p = payload(j);
        if !(is_obj(&p, 3) && key_is(&p, 0, b"place") && key_is(&p, 1, b"projections") && key_is(&p, 2, b"variance")) { return None; }
        let mut f = into_members(p);
        let place = dec_place(take_fld(&mut f, 0))?;
        let projections = take_fld(&mut f, 1);
        let variance = take_fld(&mut f, 2);
        Some(StatementKind::AscribeUserType { place, projections, variance })
    } else if bytes_eq(t, b"Coverage") {
        if u { return None; }
        Some(StatementKind::Coverage(payload(j)))
    } else if bytes_eq(t, b"Intrinsic") {
        if u { return None; }
        Some(StatementKind::Intrinsic(payload(j)))
    } else if bytes_eq(t, b"ConstEvalCounter") {
        if u { Some(StatementKind::ConstEvalCounter) } else { None }
    } else if bytes_eq(t, b"Nop") {
        if u { Some(StatementKind::Nop) } else { None }
    } else {
        Some(StatementKind::Unknown(j))
    }
}

pub fn dec_rvalue(j: Json) -> (r: Option<Rvalue>)
    ensures match r { Some(x) => decode_rvalue(j, x), None => forall|x: Rvalue| !decode_rvalue(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    if bytes_eq(t, b"AddressOf") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let k = take(&mut a, 0);
        let pl = dec_place(take(&mut a, 1))?;
        Some(Rvalue::AddressOf(k, pl))
    } else if bytes_eq(t, b"Aggregate") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let k = dec_aggregate_kind(take(&mut a, 0))?;
        let ops = dec_operands(take(&mut a, 1))?;
        Some(Rvalue::Aggregate(k, ops))
    } else if bytes_eq(t, b"BinaryOp") {
        if u { return None; }
        let mut a = into_arr(payload(j), 3)?;
        let op = dec_bin_op(take(&mut a, 0))?;
        let x = dec_operand(take(&mut a, 1))?;
        let y = dec_operand(take(&mut a, 2))?;
        Some(Rvalue::BinaryOp(op, x, y))
    } else if bytes_eq(t, b"Cast") {
        if u { return None; }
        let mut a = into_arr(payload(j), 3)?;
        let k = dec_cast_kind(take(&mut a, 0))?;
        let x = dec_operand(take(&mut a, 1))?;
        let ty = dec_usize(take(&mut a, 2))?;
        Some(Rvalue::Cast(k, x, ty))
    } else if bytes_eq(t, b"CheckedBinaryOp") {
        if u { return None; }
        let mut a = into_arr(payload(j), 3)?;
        let op = dec_bin_op(take(&mut a, 0))?;
        let x = dec_operand(take(&mut a, 1))?;
        let y = dec_operand(take(&mut a, 2))?;
        Some(Rvalue::CheckedBinaryOp(op, x, y))
    } else if bytes_eq(t, b"CopyForDeref") {
        if u { return None; }
        Some(Rvalue::CopyForDeref(dec_place(payload(j))?))
    } else if bytes_eq(t, b"Discriminant") {
        if u { return None; }
        Some(Rvalue::Discriminant(dec_place(payload(j))?))
    } else if bytes_eq(t, b"Len") {
        if u { return None; }
        Some(Rvalue::Len(dec_place(payload(j))?))
    } else if bytes_eq(t, b"Ref") {
        if u { return None; }
        let mut a = into_arr(payload(j), 3)?;
        let reg = take(&mut a, 0);
        let k = dec_borrow_kind(take(&mut a, 1))?;
        let pl = dec_place(take(&mut a, 2))?;
        Some(Rvalue::Ref(reg, k, pl))
    } else if bytes_eq(t, b"Repeat") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let x = dec_operand(take(&mut a, 0))?;
        let c = dec_ty_const(take(&mut a, 1))?;
        Some(Rvalue::Repeat(x, c))
    } else if bytes_eq(t, b"ThreadLocalRef") {
        if u { return None; }
        Some(Rvalue::ThreadLocalRef(payload(j)))
    } else if bytes_eq(t, b"UnaryOp") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let op = dec_un_op(take(&mut a, 0))?;
        let x = dec_operand(take(&mut a, 1))?;
        Some(Rvalue::UnaryOp(op, x))
    } else if bytes_eq(t, b"Use") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let x = dec_operand(take(&mut a, 0))?;
        let retag = take(&mut a, 1);
        Some(Rvalue::Use(x, retag))
    } else if bytes_eq(t, b"Reborrow") {
        if u { return None; }
        let mut a = into_arr(payload(j), 3)?;
        let ty = dec_usize(take(&mut a, 0))?;
        let m = dec_mutability(take(&mut a, 1))?;
        let pl = dec_place(take(&mut a, 2))?;
        Some(Rvalue::Reborrow(ty, m, pl))
    } else {
        Some(Rvalue::Unknown(j))
    }
}

pub fn dec_bin_op(j: Json) -> (r: Option<BinOp>)
    ensures match r { Some(x) => decode_bin_op(j, x), None => forall|x: BinOp| !decode_bin_op(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    let x = if bytes_eq(t, b"Add") { BinOp::Add }
        else if bytes_eq(t, b"AddUnchecked") { BinOp::AddUnchecked }
        else if bytes_eq(t, b"Sub") { BinOp::Sub }
        else if bytes_eq(t, b"SubUnchecked") { BinOp::SubUnchecked }
        else if bytes_eq(t, b"Mul") { BinOp::Mul }
        else if bytes_eq(t, b"MulUnchecked") { BinOp::MulUnchecked }
        else if bytes_eq(t, b"Div") { BinOp::Div }
        else if bytes_eq(t, b"Rem") { BinOp::Rem }
        else if bytes_eq(t, b"BitXor") { BinOp::BitXor }
        else if bytes_eq(t, b"BitAnd") { BinOp::BitAnd }
        else if bytes_eq(t, b"BitOr") { BinOp::BitOr }
        else if bytes_eq(t, b"Shl") { BinOp::Shl }
        else if bytes_eq(t, b"ShlUnchecked") { BinOp::ShlUnchecked }
        else if bytes_eq(t, b"Shr") { BinOp::Shr }
        else if bytes_eq(t, b"ShrUnchecked") { BinOp::ShrUnchecked }
        else if bytes_eq(t, b"Eq") { BinOp::Eq }
        else if bytes_eq(t, b"Lt") { BinOp::Lt }
        else if bytes_eq(t, b"Le") { BinOp::Le }
        else if bytes_eq(t, b"Ne") { BinOp::Ne }
        else if bytes_eq(t, b"Ge") { BinOp::Ge }
        else if bytes_eq(t, b"Gt") { BinOp::Gt }
        else if bytes_eq(t, b"Cmp") { BinOp::Cmp }
        else if bytes_eq(t, b"Offset") { BinOp::Offset }
        else { return Some(BinOp::Unknown(j)); };
    if u { Some(x) } else { None }
}

pub fn dec_un_op(j: Json) -> (r: Option<UnOp>)
    ensures match r { Some(x) => decode_un_op(j, x), None => forall|x: UnOp| !decode_un_op(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    let x = if bytes_eq(t, b"Not") { UnOp::Not }
        else if bytes_eq(t, b"Neg") { UnOp::Neg }
        else if bytes_eq(t, b"PtrMetadata") { UnOp::PtrMetadata }
        else { return Some(UnOp::Unknown(j)); };
    if u { Some(x) } else { None }
}

fn dec_aggregate_kind(j: Json) -> (r: Option<AggregateKind>)
    ensures match r { Some(x) => decode_aggregate_kind(j, x), None => forall|x: AggregateKind| !decode_aggregate_kind(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    if bytes_eq(t, b"Array") {
        if u { return None; }
        Some(AggregateKind::Array(dec_usize(payload(j))?))
    } else if bytes_eq(t, b"Tuple") {
        if u { Some(AggregateKind::Tuple) } else { None }
    } else if bytes_eq(t, b"Adt") {
        if u { return None; }
        let mut a = into_arr(payload(j), 5)?;
        let d = dec_usize(take(&mut a, 0))?;
        let v = dec_usize(take(&mut a, 1))?;
        let args = dec_generic_args(take(&mut a, 2))?;
        let ut = take(&mut a, 3);
        let fi = dec_opt_usize(take(&mut a, 4))?;
        Some(AggregateKind::Adt(d, v, args, ut, fi))
    } else if bytes_eq(t, b"Closure") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let d = dec_usize(take(&mut a, 0))?;
        let args = dec_generic_args(take(&mut a, 1))?;
        Some(AggregateKind::Closure(d, args))
    } else if bytes_eq(t, b"Coroutine") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let d = take(&mut a, 0);
        let args = take(&mut a, 1);
        Some(AggregateKind::Coroutine(d, args))
    } else if bytes_eq(t, b"CoroutineClosure") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let d = take(&mut a, 0);
        let args = take(&mut a, 1);
        Some(AggregateKind::CoroutineClosure(d, args))
    } else if bytes_eq(t, b"RawPtr") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let ty = dec_usize(take(&mut a, 0))?;
        let m = dec_mutability(take(&mut a, 1))?;
        Some(AggregateKind::RawPtr(ty, m))
    } else {
        Some(AggregateKind::Unknown(j))
    }
}

pub fn dec_operand(j: Json) -> (r: Option<Operand>)
    ensures match r { Some(x) => decode_operand(j, x), None => forall|x: Operand| !decode_operand(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    if bytes_eq(t, b"Copy") {
        if u { return None; }
        Some(Operand::Copy(dec_place(payload(j))?))
    } else if bytes_eq(t, b"Move") {
        if u { return None; }
        Some(Operand::Move(dec_place(payload(j))?))
    } else if bytes_eq(t, b"Constant") {
        if u { return None; }
        Some(Operand::Constant(dec_const_operand(payload(j))?))
    } else if bytes_eq(t, b"RuntimeChecks") {
        if u { return None; }
        Some(Operand::RuntimeChecks(payload(j)))
    } else {
        Some(Operand::Unknown(j))
    }
}

pub fn dec_place(j: Json) -> (r: Option<Place>)
    ensures match r { Some(x) => decode_place(j, x), None => forall|x: Place| !decode_place(j, x) },
{
    if !(is_obj(&j, 2) && key_is(&j, 0, b"local") && key_is(&j, 1, b"projection")) { return None; }
    let mut f = into_members(j);
    let local = dec_usize(take_fld(&mut f, 0))?;
    let projection = dec_projection(take_fld(&mut f, 1))?;
    Some(Place { local, projection })
}

fn dec_const_operand(j: Json) -> (r: Option<ConstOperand>)
    ensures match r { Some(x) => decode_const_operand(j, x), None => forall|x: ConstOperand| !decode_const_operand(j, x) },
{
    if !(is_obj(&j, 3) && key_is(&j, 0, b"span") && key_is(&j, 1, b"user_ty") && key_is(&j, 2, b"const_")) { return None; }
    let mut f = into_members(j);
    let span = dec_usize(take_fld(&mut f, 0))?;
    let user_ty = take_fld(&mut f, 1);
    let const_ = dec_mir_const(take_fld(&mut f, 2))?;
    Some(ConstOperand { span, user_ty, const_ })
}

fn dec_var_debug_info(j: Json) -> (r: Option<VarDebugInfo>)
    ensures match r { Some(x) => decode_var_debug_info(j, x), None => forall|x: VarDebugInfo| !decode_var_debug_info(j, x) },
{
    if !(is_obj(&j, 5) && key_is(&j, 0, b"name") && key_is(&j, 1, b"source_info") && key_is(&j, 2, b"composite")
        && key_is(&j, 3, b"value") && key_is(&j, 4, b"argument_index")) { return None; }
    let mut f = into_members(j);
    let name = dec_str(take_fld(&mut f, 0))?;
    let source_info = take_fld(&mut f, 1);
    let composite = take_fld(&mut f, 2);
    let value = dec_var_debug_info_contents(take_fld(&mut f, 3))?;
    let argument_index = dec_opt_u16(take_fld(&mut f, 4))?;
    Some(VarDebugInfo { name, source_info, composite, value, argument_index })
}

fn dec_var_debug_info_contents(j: Json) -> (r: Option<VarDebugInfoContents>)
    ensures match r {
        Some(x) => decode_var_debug_info_contents(j, x),
        None => forall|x: VarDebugInfoContents| !decode_var_debug_info_contents(j, x),
    },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    if bytes_eq(t, b"Place") {
        if u { return None; }
        Some(VarDebugInfoContents::Place(dec_place(payload(j))?))
    } else if bytes_eq(t, b"Const") {
        if u { return None; }
        Some(VarDebugInfoContents::Const(dec_const_operand(payload(j))?))
    } else {
        Some(VarDebugInfoContents::Unknown(j))
    }
}

fn dec_projection_elem(j: Json) -> (r: Option<ProjectionElem>)
    ensures match r { Some(x) => decode_projection_elem(j, x), None => forall|x: ProjectionElem| !decode_projection_elem(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    if bytes_eq(t, b"Deref") {
        if u { Some(ProjectionElem::Deref) } else { None }
    } else if bytes_eq(t, b"Field") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let fi = dec_usize(take(&mut a, 0))?;
        let ty = dec_usize(take(&mut a, 1))?;
        Some(ProjectionElem::Field(fi, ty))
    } else if bytes_eq(t, b"Index") {
        if u { return None; }
        Some(ProjectionElem::Index(dec_usize(payload(j))?))
    } else if bytes_eq(t, b"ConstantIndex") {
        if u { return None; }
        let p = payload(j);
        if !(is_obj(&p, 3) && key_is(&p, 0, b"offset") && key_is(&p, 1, b"min_length") && key_is(&p, 2, b"from_end")) { return None; }
        let mut f = into_members(p);
        let offset = dec_u64(take_fld(&mut f, 0))?;
        let min_length = dec_u64(take_fld(&mut f, 1))?;
        let from_end = dec_bool(take_fld(&mut f, 2))?;
        Some(ProjectionElem::ConstantIndex { offset, min_length, from_end })
    } else if bytes_eq(t, b"Subslice") {
        if u { return None; }
        let p = payload(j);
        if !(is_obj(&p, 3) && key_is(&p, 0, b"from") && key_is(&p, 1, b"to") && key_is(&p, 2, b"from_end")) { return None; }
        let mut f = into_members(p);
        let from = dec_u64(take_fld(&mut f, 0))?;
        let to = dec_u64(take_fld(&mut f, 1))?;
        let from_end = dec_bool(take_fld(&mut f, 2))?;
        Some(ProjectionElem::Subslice { from, to, from_end })
    } else if bytes_eq(t, b"Downcast") {
        if u { return None; }
        Some(ProjectionElem::Downcast(dec_usize(payload(j))?))
    } else if bytes_eq(t, b"OpaqueCast") {
        if u { return None; }
        Some(ProjectionElem::OpaqueCast(dec_usize(payload(j))?))
    } else {
        Some(ProjectionElem::Unknown(j))
    }
}

fn dec_switch_targets(j: Json) -> (r: Option<SwitchTargets>)
    ensures match r { Some(x) => decode_switch_targets(j, x), None => forall|x: SwitchTargets| !decode_switch_targets(j, x) },
{
    if !(is_obj(&j, 2) && key_is(&j, 0, b"branches") && key_is(&j, 1, b"otherwise")) { return None; }
    let mut f = into_members(j);
    let branches = dec_branches(take_fld(&mut f, 0))?;
    let otherwise = dec_usize(take_fld(&mut f, 1))?;
    Some(SwitchTargets { branches, otherwise })
}

fn dec_borrow_kind(j: Json) -> (r: Option<BorrowKind>)
    ensures match r { Some(x) => decode_borrow_kind(j, x), None => forall|x: BorrowKind| !decode_borrow_kind(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    if bytes_eq(t, b"Shared") {
        if u { Some(BorrowKind::Shared) } else { None }
    } else if bytes_eq(t, b"Fake") {
        if u { return None; }
        Some(BorrowKind::Fake(payload(j)))
    } else if bytes_eq(t, b"Mut") {
        if u { return None; }
        let p = payload(j);
        if !(is_obj(&p, 1) && key_is(&p, 0, b"kind")) { return None; }
        let mut f = into_members(p);
        let kind = take_fld(&mut f, 0);
        Some(BorrowKind::Mut { kind })
    } else {
        Some(BorrowKind::Unknown(j))
    }
}

pub fn dec_mutability(j: Json) -> (r: Option<Mutability>)
    ensures match r { Some(x) => decode_mutability(j, x), None => forall|x: Mutability| !decode_mutability(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    let x = if bytes_eq(t, b"Not") { Mutability::Not }
        else if bytes_eq(t, b"Mut") { Mutability::Mut }
        else { return Some(Mutability::Unknown(j)); };
    if u { Some(x) } else { None }
}

fn dec_pointer_coercion(j: Json) -> (r: Option<PointerCoercion>)
    ensures match r { Some(x) => decode_pointer_coercion(j, x), None => forall|x: PointerCoercion| !decode_pointer_coercion(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    if bytes_eq(t, b"ReifyFnPointer") {
        if u { return None; }
        Some(PointerCoercion::ReifyFnPointer(payload(j)))
    } else if bytes_eq(t, b"UnsafeFnPointer") {
        if u { Some(PointerCoercion::UnsafeFnPointer) } else { None }
    } else if bytes_eq(t, b"ClosureFnPointer") {
        if u { return None; }
        Some(PointerCoercion::ClosureFnPointer(payload(j)))
    } else if bytes_eq(t, b"MutToConstPointer") {
        if u { Some(PointerCoercion::MutToConstPointer) } else { None }
    } else if bytes_eq(t, b"ArrayToPointer") {
        if u { Some(PointerCoercion::ArrayToPointer) } else { None }
    } else if bytes_eq(t, b"Unsize") {
        if u { Some(PointerCoercion::Unsize) } else { None }
    } else {
        Some(PointerCoercion::Unknown(j))
    }
}

fn dec_cast_kind(j: Json) -> (r: Option<CastKind>)
    ensures match r { Some(x) => decode_cast_kind(j, x), None => forall|x: CastKind| !decode_cast_kind(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    if bytes_eq(t, b"PointerExposeAddress") { if u { Some(CastKind::PointerExposeAddress) } else { None } }
    else if bytes_eq(t, b"PointerWithExposedProvenance") { if u { Some(CastKind::PointerWithExposedProvenance) } else { None } }
    else if bytes_eq(t, b"PointerCoercion") {
        if u { return None; }
        Some(CastKind::PointerCoercion(dec_pointer_coercion(payload(j))?))
    }
    else if bytes_eq(t, b"IntToInt") { if u { Some(CastKind::IntToInt) } else { None } }
    else if bytes_eq(t, b"FloatToInt") { if u { Some(CastKind::FloatToInt) } else { None } }
    else if bytes_eq(t, b"FloatToFloat") { if u { Some(CastKind::FloatToFloat) } else { None } }
    else if bytes_eq(t, b"IntToFloat") { if u { Some(CastKind::IntToFloat) } else { None } }
    else if bytes_eq(t, b"PtrToPtr") { if u { Some(CastKind::PtrToPtr) } else { None } }
    else if bytes_eq(t, b"FnPtrToPtr") { if u { Some(CastKind::FnPtrToPtr) } else { None } }
    else if bytes_eq(t, b"Transmute") { if u { Some(CastKind::Transmute) } else { None } }
    else if bytes_eq(t, b"Subtype") { if u { Some(CastKind::Subtype) } else { None } }
    else { Some(CastKind::Unknown(j)) }
}

// ------------------------------------------------------------------ constants and types

fn dec_mir_const(j: Json) -> (r: Option<MirConst>)
    ensures match r { Some(x) => decode_mir_const(j, x), None => forall|x: MirConst| !decode_mir_const(j, x) },
{
    if !(is_obj(&j, 3) && key_is(&j, 0, b"kind") && key_is(&j, 1, b"ty") && key_is(&j, 2, b"id")) { return None; }
    let mut f = into_members(j);
    let kind = dec_constant_kind(take_fld(&mut f, 0))?;
    let ty = dec_usize(take_fld(&mut f, 1))?;
    let id = dec_usize(take_fld(&mut f, 2))?;
    Some(MirConst { kind, ty, id })
}

fn dec_constant_kind(j: Json) -> (r: Option<ConstantKind>)
    ensures match r { Some(x) => decode_constant_kind(j, x), None => forall|x: ConstantKind| !decode_constant_kind(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    if bytes_eq(t, b"Ty") {
        if u { return None; }
        Some(ConstantKind::Ty(dec_ty_const(payload(j))?))
    } else if bytes_eq(t, b"Allocated") {
        if u { return None; }
        Some(ConstantKind::Allocated(dec_allocation(payload(j))?))
    } else if bytes_eq(t, b"Unevaluated") {
        if u { return None; }
        Some(ConstantKind::Unevaluated(payload(j)))
    } else if bytes_eq(t, b"Param") {
        if u { return None; }
        Some(ConstantKind::Param(payload(j)))
    } else if bytes_eq(t, b"ZeroSized") {
        if u { Some(ConstantKind::ZeroSized) } else { None }
    } else {
        Some(ConstantKind::Unknown(j))
    }
}

fn dec_allocation(j: Json) -> (r: Option<Allocation>)
    ensures match r { Some(x) => decode_allocation(j, x), None => forall|x: Allocation| !decode_allocation(j, x) },
{
    if !(is_obj(&j, 4) && key_is(&j, 0, b"bytes") && key_is(&j, 1, b"provenance") && key_is(&j, 2, b"align")
        && key_is(&j, 3, b"mutability")) { return None; }
    let mut f = into_members(j);
    let bytes = dec_bytes(take_fld(&mut f, 0))?;
    let provenance = dec_provenance_map(take_fld(&mut f, 1))?;
    let align = dec_u64(take_fld(&mut f, 2))?;
    let mutability = dec_mutability(take_fld(&mut f, 3))?;
    Some(Allocation { bytes, provenance, align, mutability })
}

fn dec_provenance_map(j: Json) -> (r: Option<ProvenanceMap>)
    ensures match r { Some(x) => decode_provenance_map(j, x), None => forall|x: ProvenanceMap| !decode_provenance_map(j, x) },
{
    if !(is_obj(&j, 1) && key_is(&j, 0, b"ptrs")) { return None; }
    let mut f = into_members(j);
    let ptrs = dec_ptrs(take_fld(&mut f, 0))?;
    Some(ProvenanceMap { ptrs })
}

fn dec_ty_const(j: Json) -> (r: Option<TyConst>)
    ensures match r { Some(x) => decode_ty_const(j, x), None => forall|x: TyConst| !decode_ty_const(j, x) },
{
    if !(is_obj(&j, 2) && key_is(&j, 0, b"kind") && key_is(&j, 1, b"id")) { return None; }
    let mut f = into_members(j);
    let kind = take_fld(&mut f, 0);
    let id = dec_usize(take_fld(&mut f, 1))?;
    Some(TyConst { kind, id })
}

pub fn dec_ty_kind(j: Json) -> (r: Option<TyKind>)
    ensures match r { Some(x) => decode_ty_kind(j, x), None => forall|x: TyKind| !decode_ty_kind(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    if bytes_eq(t, b"RigidTy") {
        if u { return None; }
        Some(TyKind::RigidTy(dec_rigid_ty(payload(j))?))
    } else if bytes_eq(t, b"Alias") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let k = take(&mut a, 0);
        let ty = take(&mut a, 1);
        Some(TyKind::Alias(k, ty))
    } else if bytes_eq(t, b"Param") {
        if u { return None; }
        Some(TyKind::Param(payload(j)))
    } else if bytes_eq(t, b"Bound") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let i = take(&mut a, 0);
        let ty = take(&mut a, 1);
        Some(TyKind::Bound(i, ty))
    } else {
        Some(TyKind::Unknown(j))
    }
}

pub fn dec_rigid_ty(j: Json) -> (r: Option<RigidTy>)
    ensures match r { Some(x) => decode_rigid_ty(j, x), None => forall|x: RigidTy| !decode_rigid_ty(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    if bytes_eq(t, b"Bool") { if u { Some(RigidTy::Bool) } else { None } }
    else if bytes_eq(t, b"Char") { if u { Some(RigidTy::Char) } else { None } }
    else if bytes_eq(t, b"Int") {
        if u { return None; }
        Some(RigidTy::Int(dec_int_ty(payload(j))?))
    } else if bytes_eq(t, b"Uint") {
        if u { return None; }
        Some(RigidTy::Uint(dec_uint_ty(payload(j))?))
    } else if bytes_eq(t, b"Float") {
        if u { return None; }
        Some(RigidTy::Float(payload(j)))
    } else if bytes_eq(t, b"Adt") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let d = dec_usize(take(&mut a, 0))?;
        let args = dec_generic_args(take(&mut a, 1))?;
        Some(RigidTy::Adt(d, args))
    } else if bytes_eq(t, b"Foreign") {
        if u { return None; }
        Some(RigidTy::Foreign(payload(j)))
    } else if bytes_eq(t, b"Str") { if u { Some(RigidTy::Str) } else { None } }
    else if bytes_eq(t, b"Array") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let ty = dec_usize(take(&mut a, 0))?;
        let c = dec_ty_const(take(&mut a, 1))?;
        Some(RigidTy::Array(ty, c))
    } else if bytes_eq(t, b"Pat") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let ty = dec_usize(take(&mut a, 0))?;
        let pat = take(&mut a, 1);
        Some(RigidTy::Pat(ty, pat))
    } else if bytes_eq(t, b"Slice") {
        if u { return None; }
        Some(RigidTy::Slice(dec_usize(payload(j))?))
    } else if bytes_eq(t, b"RawPtr") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let ty = dec_usize(take(&mut a, 0))?;
        let m = dec_mutability(take(&mut a, 1))?;
        Some(RigidTy::RawPtr(ty, m))
    } else if bytes_eq(t, b"Ref") {
        if u { return None; }
        let mut a = into_arr(payload(j), 3)?;
        let reg = take(&mut a, 0);
        let ty = dec_usize(take(&mut a, 1))?;
        let m = dec_mutability(take(&mut a, 2))?;
        Some(RigidTy::Ref(reg, ty, m))
    } else if bytes_eq(t, b"FnDef") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let d = dec_usize(take(&mut a, 0))?;
        let args = dec_generic_args(take(&mut a, 1))?;
        Some(RigidTy::FnDef(d, args))
    } else if bytes_eq(t, b"FnPtr") {
        if u { return None; }
        Some(RigidTy::FnPtr(payload(j)))
    } else if bytes_eq(t, b"Closure") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let d = dec_usize(take(&mut a, 0))?;
        let args = dec_generic_args(take(&mut a, 1))?;
        Some(RigidTy::Closure(d, args))
    } else if bytes_eq(t, b"Coroutine") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let d = take(&mut a, 0);
        let args = take(&mut a, 1);
        Some(RigidTy::Coroutine(d, args))
    } else if bytes_eq(t, b"CoroutineClosure") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let d = take(&mut a, 0);
        let args = take(&mut a, 1);
        Some(RigidTy::CoroutineClosure(d, args))
    } else if bytes_eq(t, b"Dynamic") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let d = take(&mut a, 0);
        let reg = take(&mut a, 1);
        Some(RigidTy::Dynamic(d, reg))
    } else if bytes_eq(t, b"Never") { if u { Some(RigidTy::Never) } else { None } }
    else if bytes_eq(t, b"Tuple") {
        if u { return None; }
        Some(RigidTy::Tuple(dec_tys(payload(j))?))
    } else if bytes_eq(t, b"CoroutineWitness") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let d = take(&mut a, 0);
        let args = take(&mut a, 1);
        Some(RigidTy::CoroutineWitness(d, args))
    } else {
        Some(RigidTy::Unknown(j))
    }
}

fn dec_int_ty(j: Json) -> (r: Option<IntTy>)
    ensures match r { Some(x) => decode_int_ty(j, x), None => forall|x: IntTy| !decode_int_ty(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    let x = if bytes_eq(t, b"Isize") { IntTy::Isize }
        else if bytes_eq(t, b"I8") { IntTy::I8 }
        else if bytes_eq(t, b"I16") { IntTy::I16 }
        else if bytes_eq(t, b"I32") { IntTy::I32 }
        else if bytes_eq(t, b"I64") { IntTy::I64 }
        else if bytes_eq(t, b"I128") { IntTy::I128 }
        else { return Some(IntTy::Unknown(j)); };
    if u { Some(x) } else { None }
}

fn dec_uint_ty(j: Json) -> (r: Option<UintTy>)
    ensures match r { Some(x) => decode_uint_ty(j, x), None => forall|x: UintTy| !decode_uint_ty(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    let x = if bytes_eq(t, b"Usize") { UintTy::Usize }
        else if bytes_eq(t, b"U8") { UintTy::U8 }
        else if bytes_eq(t, b"U16") { UintTy::U16 }
        else if bytes_eq(t, b"U32") { UintTy::U32 }
        else if bytes_eq(t, b"U64") { UintTy::U64 }
        else if bytes_eq(t, b"U128") { UintTy::U128 }
        else { return Some(UintTy::Unknown(j)); };
    if u { Some(x) } else { None }
}

fn dec_generic_args(j: Json) -> (r: Option<GenericArgs>)
    ensures match r { Some(x) => decode_generic_args(j, x), None => forall|x: GenericArgs| !decode_generic_args(j, x) },
{
    Some(GenericArgs(dec_generic_arg_kinds(j)?))
}

fn dec_generic_arg_kind(j: Json) -> (r: Option<GenericArgKind>)
    ensures match r { Some(x) => decode_generic_arg_kind(j, x), None => forall|x: GenericArgKind| !decode_generic_arg_kind(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    if bytes_eq(t, b"Lifetime") {
        if u { return None; }
        Some(GenericArgKind::Lifetime(payload(j)))
    } else if bytes_eq(t, b"Type") {
        if u { return None; }
        Some(GenericArgKind::Type(dec_usize(payload(j))?))
    } else if bytes_eq(t, b"Const") {
        if u { return None; }
        Some(GenericArgKind::Const(dec_ty_const(payload(j))?))
    } else {
        Some(GenericArgKind::Unknown(j))
    }
}

fn dec_fn_sig(j: Json) -> (r: Option<FnSig>)
    ensures match r { Some(x) => decode_fn_sig(j, x), None => forall|x: FnSig| !decode_fn_sig(j, x) },
{
    if !(is_obj(&j, 4) && key_is(&j, 0, b"inputs_and_output") && key_is(&j, 1, b"c_variadic") && key_is(&j, 2, b"safety")
        && key_is(&j, 3, b"abi")) { return None; }
    let mut f = into_members(j);
    let inputs_and_output = dec_tys(take_fld(&mut f, 0))?;
    let c_variadic = dec_bool(take_fld(&mut f, 1))?;
    let safety = take_fld(&mut f, 2);
    let abi = take_fld(&mut f, 3);
    Some(FnSig { inputs_and_output, c_variadic, safety, abi })
}

fn dec_adt_kind(j: Json) -> (r: Option<AdtKind>)
    ensures match r { Some(x) => decode_adt_kind(j, x), None => forall|x: AdtKind| !decode_adt_kind(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    let x = if bytes_eq(t, b"Enum") { AdtKind::Enum }
        else if bytes_eq(t, b"Union") { AdtKind::Union }
        else if bytes_eq(t, b"Struct") { AdtKind::Struct }
        else { return Some(AdtKind::Unknown(j)); };
    if u { Some(x) } else { None }
}

fn dec_instance_kind(j: Json) -> (r: Option<InstanceKind>)
    ensures match r { Some(x) => decode_instance_kind(j, x), None => forall|x: InstanceKind| !decode_instance_kind(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    if bytes_eq(t, b"Item") {
        if u { Some(InstanceKind::Item) } else { None }
    } else if bytes_eq(t, b"Intrinsic") {
        if u { Some(InstanceKind::Intrinsic) } else { None }
    } else if bytes_eq(t, b"Virtual") {
        if u { return None; }
        let p = payload(j);
        if !(is_obj(&p, 1) && key_is(&p, 0, b"idx")) { return None; }
        let mut f = into_members(p);
        let idx = dec_usize(take_fld(&mut f, 0))?;
        Some(InstanceKind::Virtual { idx })
    } else if bytes_eq(t, b"Shim") {
        if u { Some(InstanceKind::Shim) } else { None }
    } else {
        Some(InstanceKind::Unknown(j))
    }
}

fn dec_global_alloc(j: Json) -> (r: Option<GlobalAlloc>)
    ensures match r { Some(x) => decode_global_alloc(j, x), None => forall|x: GlobalAlloc| !decode_global_alloc(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    if bytes_eq(t, b"Function") {
        if u { return None; }
        Some(GlobalAlloc::Function(payload(j)))
    } else if bytes_eq(t, b"VTable") {
        if u { return None; }
        let mut a = into_arr(payload(j), 2)?;
        let ty = take(&mut a, 0);
        let tr = take(&mut a, 1);
        Some(GlobalAlloc::VTable(ty, tr))
    } else if bytes_eq(t, b"Static") {
        if u { return None; }
        Some(GlobalAlloc::Static(dec_usize(payload(j))?))
    } else if bytes_eq(t, b"Memory") {
        if u { return None; }
        Some(GlobalAlloc::Memory(dec_allocation(payload(j))?))
    } else if bytes_eq(t, b"TypeId") {
        if u { return None; }
        let p = payload(j);
        if !(is_obj(&p, 1) && key_is(&p, 0, b"ty")) { return None; }
        let mut f = into_members(p);
        let ty = dec_usize(take_fld(&mut f, 0))?;
        Some(GlobalAlloc::TypeId { ty })
    } else {
        Some(GlobalAlloc::Unknown(j))
    }
}

// ------------------------------------------------------------------ layouts

fn dec_layout_shape(j: Json) -> (r: Option<LayoutShape>)
    ensures match r { Some(x) => decode_layout_shape(j, x), None => forall|x: LayoutShape| !decode_layout_shape(j, x) },
{
    if !(is_obj(&j, 5) && key_is(&j, 0, b"fields") && key_is(&j, 1, b"variants") && key_is(&j, 2, b"abi")
        && key_is(&j, 3, b"abi_align") && key_is(&j, 4, b"size")) { return None; }
    let mut f = into_members(j);
    let fields = dec_fields_shape(take_fld(&mut f, 0))?;
    let variants = dec_variants_shape(take_fld(&mut f, 1))?;
    let abi = take_fld(&mut f, 2);
    let abi_align = dec_u64(take_fld(&mut f, 3))?;
    let size = dec_machine_size(take_fld(&mut f, 4))?;
    Some(LayoutShape { fields, variants, abi, abi_align, size })
}

fn dec_machine_size(j: Json) -> (r: Option<MachineSize>)
    ensures match r { Some(x) => decode_machine_size(j, x), None => forall|x: MachineSize| !decode_machine_size(j, x) },
{
    if !(is_obj(&j, 1) && key_is(&j, 0, b"num_bits")) { return None; }
    let mut f = into_members(j);
    let num_bits = dec_usize(take_fld(&mut f, 0))?;
    Some(MachineSize { num_bits })
}

fn dec_fields_shape(j: Json) -> (r: Option<FieldsShape>)
    ensures match r { Some(x) => decode_fields_shape(j, x), None => forall|x: FieldsShape| !decode_fields_shape(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    if bytes_eq(t, b"Primitive") {
        if u { Some(FieldsShape::Primitive) } else { None }
    } else if bytes_eq(t, b"Union") {
        if u { return None; }
        let c = dec_usize(payload(j))?;
        if c == 0 { return None; }
        Some(FieldsShape::Union(c))
    } else if bytes_eq(t, b"Array") {
        if u { return None; }
        let p = payload(j);
        if !(is_obj(&p, 2) && key_is(&p, 0, b"stride") && key_is(&p, 1, b"count")) { return None; }
        let mut f = into_members(p);
        let stride = dec_machine_size(take_fld(&mut f, 0))?;
        let count = dec_u64(take_fld(&mut f, 1))?;
        Some(FieldsShape::Array { stride, count })
    } else if bytes_eq(t, b"Arbitrary") {
        if u { return None; }
        let p = payload(j);
        if !(is_obj(&p, 1) && key_is(&p, 0, b"offsets")) { return None; }
        let mut f = into_members(p);
        let offsets = dec_machine_sizes(take_fld(&mut f, 0))?;
        Some(FieldsShape::Arbitrary { offsets })
    } else {
        Some(FieldsShape::Unknown(j))
    }
}

fn dec_variants_shape(j: Json) -> (r: Option<VariantsShape>)
    ensures match r { Some(x) => decode_variants_shape(j, x), None => forall|x: VariantsShape| !decode_variants_shape(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    if bytes_eq(t, b"Empty") {
        if u { Some(VariantsShape::Empty) } else { None }
    } else if bytes_eq(t, b"Single") {
        if u { return None; }
        let p = payload(j);
        if !(is_obj(&p, 1) && key_is(&p, 0, b"index")) { return None; }
        let mut f = into_members(p);
        let index = dec_usize(take_fld(&mut f, 0))?;
        Some(VariantsShape::Single { index })
    } else if bytes_eq(t, b"Multiple") {
        if u { return None; }
        let p = payload(j);
        if !(is_obj(&p, 4) && key_is(&p, 0, b"tag") && key_is(&p, 1, b"tag_encoding") && key_is(&p, 2, b"tag_field")
            && key_is(&p, 3, b"variants")) { return None; }
        let mut f = into_members(p);
        let tag = dec_scalar(take_fld(&mut f, 0))?;
        let tag_encoding = dec_tag_encoding(take_fld(&mut f, 1))?;
        let tag_field = dec_usize(take_fld(&mut f, 2))?;
        let variants = dec_variant_fields_list(take_fld(&mut f, 3))?;
        Some(VariantsShape::Multiple { tag, tag_encoding, tag_field, variants })
    } else {
        Some(VariantsShape::Unknown(j))
    }
}

fn dec_variant_fields(j: Json) -> (r: Option<VariantFields>)
    ensures match r { Some(x) => decode_variant_fields(j, x), None => forall|x: VariantFields| !decode_variant_fields(j, x) },
{
    if !(is_obj(&j, 1) && key_is(&j, 0, b"offsets")) { return None; }
    let mut f = into_members(j);
    let offsets = dec_machine_sizes(take_fld(&mut f, 0))?;
    Some(VariantFields { offsets })
}

fn dec_tag_encoding(j: Json) -> (r: Option<TagEncoding>)
    ensures match r { Some(x) => decode_tag_encoding(j, x), None => forall|x: TagEncoding| !decode_tag_encoding(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    if bytes_eq(t, b"Direct") {
        if u { Some(TagEncoding::Direct) } else { None }
    } else if bytes_eq(t, b"Niche") {
        if u { return None; }
        let p = payload(j);
        if !(is_obj(&p, 3) && key_is(&p, 0, b"untagged_variant") && key_is(&p, 1, b"niche_variants")
            && key_is(&p, 2, b"niche_start")) { return None; }
        let mut f = into_members(p);
        let untagged_variant = dec_usize(take_fld(&mut f, 0))?;
        let niche_variants = dec_range_inclusive(take_fld(&mut f, 1))?;
        let niche_start = dec_u128(take_fld(&mut f, 2))?;
        Some(TagEncoding::Niche { untagged_variant, niche_variants, niche_start })
    } else {
        Some(TagEncoding::Unknown(j))
    }
}

fn dec_range_inclusive(j: Json) -> (r: Option<RangeInclusive>)
    ensures match r { Some(x) => decode_range_inclusive(j, x), None => forall|x: RangeInclusive| !decode_range_inclusive(j, x) },
{
    if !(is_obj(&j, 2) && key_is(&j, 0, b"start") && key_is(&j, 1, b"end")) { return None; }
    let mut f = into_members(j);
    let start = dec_usize(take_fld(&mut f, 0))?;
    let end = dec_usize(take_fld(&mut f, 1))?;
    Some(RangeInclusive { start, end })
}

fn dec_scalar(j: Json) -> (r: Option<Scalar>)
    ensures match r { Some(x) => decode_scalar(j, x), None => forall|x: Scalar| !decode_scalar(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    if bytes_eq(t, b"Initialized") {
        if u { return None; }
        let p = payload(j);
        if !(is_obj(&p, 2) && key_is(&p, 0, b"value") && key_is(&p, 1, b"valid_range")) { return None; }
        let mut f = into_members(p);
        let value = dec_primitive(take_fld(&mut f, 0))?;
        let valid_range = dec_wrapping_range(take_fld(&mut f, 1))?;
        Some(Scalar::Initialized { value, valid_range })
    } else if bytes_eq(t, b"Union") {
        if u { return None; }
        let p = payload(j);
        if !(is_obj(&p, 1) && key_is(&p, 0, b"value")) { return None; }
        let mut f = into_members(p);
        let value = dec_primitive(take_fld(&mut f, 0))?;
        Some(Scalar::Union { value })
    } else {
        Some(Scalar::Unknown(j))
    }
}

fn dec_primitive(j: Json) -> (r: Option<Primitive>)
    ensures match r { Some(x) => decode_primitive(j, x), None => forall|x: Primitive| !decode_primitive(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    if bytes_eq(t, b"Int") {
        if u { return None; }
        let p = payload(j);
        if !(is_obj(&p, 2) && key_is(&p, 0, b"length") && key_is(&p, 1, b"signed")) { return None; }
        let mut f = into_members(p);
        let length = dec_integer_length(take_fld(&mut f, 0))?;
        let signed = dec_bool(take_fld(&mut f, 1))?;
        Some(Primitive::Int { length, signed })
    } else if bytes_eq(t, b"Float") {
        if u { return None; }
        let p = payload(j);
        if !(is_obj(&p, 1) && key_is(&p, 0, b"length")) { return None; }
        let mut f = into_members(p);
        let length = take_fld(&mut f, 0);
        Some(Primitive::Float { length })
    } else if bytes_eq(t, b"Pointer") {
        if u { return None; }
        Some(Primitive::Pointer(dec_u32(payload(j))?))
    } else {
        Some(Primitive::Unknown(j))
    }
}

fn dec_integer_length(j: Json) -> (r: Option<IntegerLength>)
    ensures match r { Some(x) => decode_integer_length(j, x), None => forall|x: IntegerLength| !decode_integer_length(j, x) },
{
    if !is_enum_x(&j) { return None; }
    let u = is_str(&j);
    let t = tag_x(&j);
    let x = if bytes_eq(t, b"I8") { IntegerLength::I8 }
        else if bytes_eq(t, b"I16") { IntegerLength::I16 }
        else if bytes_eq(t, b"I32") { IntegerLength::I32 }
        else if bytes_eq(t, b"I64") { IntegerLength::I64 }
        else if bytes_eq(t, b"I128") { IntegerLength::I128 }
        else { return Some(IntegerLength::Unknown(j)); };
    if u { Some(x) } else { None }
}

fn dec_wrapping_range(j: Json) -> (r: Option<WrappingRange>)
    ensures match r { Some(x) => decode_wrapping_range(j, x), None => forall|x: WrappingRange| !decode_wrapping_range(j, x) },
{
    if !(is_obj(&j, 2) && key_is(&j, 0, b"start") && key_is(&j, 1, b"end")) { return None; }
    let mut f = into_members(j);
    let start = dec_u128(take_fld(&mut f, 0))?;
    let end = dec_u128(take_fld(&mut f, 1))?;
    Some(WrappingRange { start, end })
}

// ------------------------------------------------------------------ the tables

/// Decodes one parsed `mir-<crate>.json`.
pub fn decode(j: Json) -> (r: Option<MirCrate>)
    ensures match r { Some(x) => decode_crate(j, x), None => forall|x: MirCrate| !decode_crate(j, x) },
{
    if !(is_obj(&j, 11) && key_is(&j, 0, b"crate") && key_is(&j, 1, b"items") && key_is(&j, 2, b"insts")
        && key_is(&j, 3, b"calls") && key_is(&j, 4, b"drops") && key_is(&j, 5, b"tys") && key_is(&j, 6, b"adts")
        && key_is(&j, 7, b"consts") && key_is(&j, 8, b"layouts") && key_is(&j, 9, b"allocs")
        && key_is(&j, 10, b"spans")) { return None; }
    let mut f = into_members(j);
    let crate_name = dec_str(take_fld(&mut f, 0))?;
    let items = dec_items(take_fld(&mut f, 1))?;
    let insts = dec_insts(take_fld(&mut f, 2))?;
    let calls = dec_calls(take_fld(&mut f, 3))?;
    let drops = dec_drops(take_fld(&mut f, 4))?;
    let tys = dec_ty_rows(take_fld(&mut f, 5))?;
    let adts = dec_adts(take_fld(&mut f, 6))?;
    let consts = dec_consts(take_fld(&mut f, 7))?;
    let layouts = dec_layouts(take_fld(&mut f, 8))?;
    let allocs = dec_allocs(take_fld(&mut f, 9))?;
    let spans = dec_spans(take_fld(&mut f, 10))?;
    Some(MirCrate { crate_name, items, insts, calls, drops, tys, adts, consts, layouts, allocs, spans })
}

fn dec_item(j: Json) -> (r: Option<Item>)
    ensures match r { Some(x) => decode_item(j, x), None => forall|x: Item| !decode_item(j, x) },
{
    if !(is_obj(&j, 4) && key_is(&j, 0, b"def") && key_is(&j, 1, b"name") && key_is(&j, 2, b"inst") && key_is(&j, 3, b"attrs")) {
        return None;
    }
    let mut f = into_members(j);
    let def = dec_usize(take_fld(&mut f, 0))?;
    let name = dec_str(take_fld(&mut f, 1))?;
    let inst = dec_opt_usize(take_fld(&mut f, 2))?;
    let attrs = dec_strs(take_fld(&mut f, 3))?;
    Some(Item { def, name, inst, attrs })
}

fn dec_inst(j: Json) -> (r: Option<Inst>)
    ensures match r { Some(x) => decode_inst(j, x), None => forall|x: Inst| !decode_inst(j, x) },
{
    if !(is_obj(&j, 8) && key_is(&j, 0, b"id") && key_is(&j, 1, b"def") && key_is(&j, 2, b"name") && key_is(&j, 3, b"key")
        && key_is(&j, 4, b"krate") && key_is(&j, 5, b"kind") && key_is(&j, 6, b"body") && key_is(&j, 7, b"fn_sig")) {
        return None;
    }
    let mut f = into_members(j);
    let id = dec_usize(take_fld(&mut f, 0))?;
    let def = dec_usize(take_fld(&mut f, 1))?;
    let name = dec_str(take_fld(&mut f, 2))?;
    let key = dec_str(take_fld(&mut f, 3))?;
    let krate = dec_str(take_fld(&mut f, 4))?;
    let kind = dec_instance_kind(take_fld(&mut f, 5))?;
    let body = dec_opt_body(take_fld(&mut f, 6))?;
    let fn_sig = dec_opt_fn_sig(take_fld(&mut f, 7))?;
    Some(Inst { id, def, name, key, krate, kind, body, fn_sig })
}

fn dec_call(j: Json) -> (r: Option<Call>)
    ensures match r { Some(x) => decode_call(j, x), None => forall|x: Call| !decode_call(j, x) },
{
    if !(is_obj(&j, 5) && key_is(&j, 0, b"fn_ty") && key_is(&j, 1, b"def") && key_is(&j, 2, b"def_name")
        && key_is(&j, 3, b"args") && key_is(&j, 4, b"resolved")) { return None; }
    let mut f = into_members(j);
    let fn_ty = dec_usize(take_fld(&mut f, 0))?;
    let def = dec_usize(take_fld(&mut f, 1))?;
    let def_name = dec_str(take_fld(&mut f, 2))?;
    let args = dec_generic_args(take_fld(&mut f, 3))?;
    let resolved = dec_opt_usize(take_fld(&mut f, 4))?;
    Some(Call { fn_ty, def, def_name, args, resolved })
}

fn dec_drop_row(j: Json) -> (r: Option<DropRow>)
    ensures match r { Some(x) => decode_drop_row(j, x), None => forall|x: DropRow| !decode_drop_row(j, x) },
{
    if !(is_obj(&j, 3) && key_is(&j, 0, b"ty") && key_is(&j, 1, b"glue") && key_is(&j, 2, b"empty")) { return None; }
    let mut f = into_members(j);
    let ty = dec_usize(take_fld(&mut f, 0))?;
    let glue = dec_usize(take_fld(&mut f, 1))?;
    let empty = dec_bool(take_fld(&mut f, 2))?;
    Some(DropRow { ty, glue, empty })
}

fn dec_ty_row(j: Json) -> (r: Option<TyRow>)
    ensures match r { Some(x) => decode_ty_row(j, x), None => forall|x: TyRow| !decode_ty_row(j, x) },
{
    if !(is_obj(&j, 2) && key_is(&j, 0, b"id") && key_is(&j, 1, b"kind")) { return None; }
    let mut f = into_members(j);
    let id = dec_usize(take_fld(&mut f, 0))?;
    let kind = dec_ty_kind(take_fld(&mut f, 1))?;
    Some(TyRow { id, kind })
}

fn dec_adt(j: Json) -> (r: Option<Adt>)
    ensures match r { Some(x) => decode_adt(j, x), None => forall|x: Adt| !decode_adt(j, x) },
{
    if !(is_obj(&j, 5) && key_is(&j, 0, b"ty") && key_is(&j, 1, b"name") && key_is(&j, 2, b"kind") && key_is(&j, 3, b"is_box")
        && key_is(&j, 4, b"variants")) { return None; }
    let mut f = into_members(j);
    let ty = dec_usize(take_fld(&mut f, 0))?;
    let name = dec_str(take_fld(&mut f, 1))?;
    let kind = dec_adt_kind(take_fld(&mut f, 2))?;
    let is_box = dec_bool(take_fld(&mut f, 3))?;
    let variants = dec_adt_variants(take_fld(&mut f, 4))?;
    Some(Adt { ty, name, kind, is_box, variants })
}

fn dec_adt_variant(j: Json) -> (r: Option<AdtVariant>)
    ensures match r { Some(x) => decode_adt_variant(j, x), None => forall|x: AdtVariant| !decode_adt_variant(j, x) },
{
    if !(is_obj(&j, 2) && key_is(&j, 0, b"discr") && key_is(&j, 1, b"fields")) { return None; }
    let mut f = into_members(j);
    let discr = dec_opt_u128(take_fld(&mut f, 0))?;
    let fields = dec_tys(take_fld(&mut f, 1))?;
    Some(AdtVariant { discr, fields })
}

fn dec_const_row(j: Json) -> (r: Option<ConstRow>)
    ensures match r { Some(x) => decode_const_row(j, x), None => forall|x: ConstRow| !decode_const_row(j, x) },
{
    if !(is_obj(&j, 2) && key_is(&j, 0, b"id") && key_is(&j, 1, b"usize")) { return None; }
    let mut f = into_members(j);
    let id = dec_usize(take_fld(&mut f, 0))?;
    let usize = dec_opt_u64(take_fld(&mut f, 1))?;
    Some(ConstRow { id, usize })
}

fn dec_layout_row(j: Json) -> (r: Option<LayoutRow>)
    ensures match r { Some(x) => decode_layout_row(j, x), None => forall|x: LayoutRow| !decode_layout_row(j, x) },
{
    if !(is_obj(&j, 2) && key_is(&j, 0, b"ty") && key_is(&j, 1, b"shape")) { return None; }
    let mut f = into_members(j);
    let ty = dec_usize(take_fld(&mut f, 0))?;
    let shape = dec_layout_shape(take_fld(&mut f, 1))?;
    Some(LayoutRow { ty, shape })
}

fn dec_alloc_row(j: Json) -> (r: Option<AllocRow>)
    ensures match r { Some(x) => decode_alloc_row(j, x), None => forall|x: AllocRow| !decode_alloc_row(j, x) },
{
    if !(is_obj(&j, 2) && key_is(&j, 0, b"id") && key_is(&j, 1, b"alloc")) { return None; }
    let mut f = into_members(j);
    let id = dec_usize(take_fld(&mut f, 0))?;
    let alloc = dec_global_alloc(take_fld(&mut f, 1))?;
    Some(AllocRow { id, alloc })
}

fn dec_span_row(j: Json) -> (r: Option<SpanRow>)
    ensures match r { Some(x) => decode_span_row(j, x), None => forall|x: SpanRow| !decode_span_row(j, x) },
{
    if !(is_obj(&j, 3) && key_is(&j, 0, b"id") && key_is(&j, 1, b"file") && key_is(&j, 2, b"line")) { return None; }
    let mut f = into_members(j);
    let id = dec_usize(take_fld(&mut f, 0))?;
    let file = dec_str(take_fld(&mut f, 1))?;
    let line = dec_usize(take_fld(&mut f, 2))?;
    Some(SpanRow { id, file, line })
}

} // verus!
