//! The MIR AST: the rustc_public types this phase reads, with the same names, fields and variant
//! order (trusted; review side by side with `$(rustc --print sysroot)/lib/rustlib/rustc-src/rust/
//! compiler/rustc_public/src`, cited per type as `file:line`). A field the semantics never reads is
//! kept as the raw `Json` serde wrote for it, so nothing is dropped. Every enum ends in
//! `Unknown(Json)`: a variant name this mirror does not know (a toolchain bump), kept whole.
//!
//! Ids are serialized by rustc_public as bare integers (ty.rs:1605 `serialize_index_impl`), so
//! they are `usize` aliases here. `crate_def!` types (`AdtDef`, `FnDef`, `ClosureDef`, `StaticDef`)
//! are newtypes of `DefId` and serialize the same way.
use crate::json::Json;
use vstd::prelude::*;

verus! {

/// ty.rs:17
pub type Ty = usize;
/// ty.rs:261
pub type Span = usize;
/// crate_def.rs:9
pub type DefId = usize;
/// mir/alloc.rs:51
pub type AllocId = usize;
/// mir/mono.rs:245
pub type InstanceDef = usize;
/// ty.rs:157
pub type TyConstId = usize;
/// ty.rs:218
pub type MirConstId = usize;
/// ty.rs:1640
pub type VariantIdx = usize;
/// mir/body.rs:847
pub type Local = usize;
/// mir/body.rs:865
pub type FieldIdx = usize;
/// mir/body.rs:40
pub type BasicBlockIdx = usize;

// ------------------------------------------------------------------ bodies (mir/body.rs)

/// mir/body.rs:15
#[derive(Debug, PartialEq, Eq)]
pub struct Body {
    pub blocks: Vec<BasicBlock>,
    pub locals: Vec<LocalDecl>,
    pub arg_count: usize,
    pub var_debug_info: Vec<VarDebugInfo>,
    pub spread_arg: Option<Local>,
    pub span: Span,
}

/// mir/body.rs:127
#[derive(Debug, PartialEq, Eq)]
pub struct LocalDecl { pub ty: Ty, pub span: Span, pub mutability: Mutability }

/// mir/body.rs:134
#[derive(Debug, PartialEq, Eq)]
pub struct BasicBlock { pub statements: Vec<Statement>, pub terminator: Terminator }

/// mir/body.rs:140
#[derive(Debug, PartialEq, Eq)]
pub struct Terminator { pub kind: TerminatorKind, pub span: Span }

/// mir/body.rs:154. `unwind` is `UnwindAction` (body.rs:253), `msg` is `AssertMessage` (body.rs:261).
#[derive(Debug, PartialEq, Eq)]
#[allow(inconsistent_fields)]
pub enum TerminatorKind {
    Goto { target: BasicBlockIdx },
    SwitchInt { discr: Operand, targets: SwitchTargets },
    Resume,
    Abort,
    Return,
    Unreachable,
    Drop { place: Place, target: BasicBlockIdx, unwind: Json },
    Call { func: Operand, args: Vec<Operand>, destination: Place, target: Option<BasicBlockIdx>, unwind: Json },
    Assert { cond: Operand, expected: bool, msg: Json, target: BasicBlockIdx, unwind: Json },
    InlineAsm { template: Json, operands: Json, options: Json, line_spans: Json, destination: Json, unwind: Json },
    Unknown(Json),
}

/// mir/body.rs:469
#[derive(Debug, PartialEq, Eq)]
pub struct Statement { pub kind: StatementKind, pub span: Span }

/// mir/body.rs:475. Raw: `FakeReadCause` (body.rs:432), `UserTypeProjection` (body.rs:841),
/// `Variance` (body.rs:448), `Coverage`, `NonDivergingIntrinsic` (body.rs:463).
#[derive(Debug, PartialEq, Eq)]
pub enum StatementKind {
    Assign(Place, Rvalue),
    FakeRead(Json, Place),
    SetDiscriminant { place: Place, variant_index: VariantIdx },
    StorageLive(Local),
    StorageDead(Local),
    PlaceMention(Place),
    AscribeUserType { place: Place, projections: Json, variance: Json },
    Coverage(Json),
    Intrinsic(Json),
    ConstEvalCounter,
    Nop,
    Unknown(Json),
}

/// mir/body.rs:490. Raw: `RawPtrKind` (body.rs:935), `Region` (ty.rs:223), `CrateItem`,
/// `WithRetag` (body.rs:442).
#[derive(Debug, PartialEq, Eq)]
pub enum Rvalue {
    AddressOf(Json, Place),
    Aggregate(AggregateKind, Vec<Operand>),
    BinaryOp(BinOp, Operand, Operand),
    Cast(CastKind, Operand, Ty),
    CheckedBinaryOp(BinOp, Operand, Operand),
    CopyForDeref(Place),
    Discriminant(Place),
    Len(Place),
    Ref(Json, BorrowKind, Place),
    Repeat(Operand, TyConst),
    ThreadLocalRef(Json),
    UnaryOp(UnOp, Operand),
    Use(Operand, Json),
    Reborrow(Ty, Mutability, Place),
    Unknown(Json),
}

/// mir/body.rs:353
#[derive(Debug, PartialEq, Eq)]
pub enum BinOp {
    Add, AddUnchecked, Sub, SubUnchecked, Mul, MulUnchecked, Div, Rem, BitXor, BitAnd, BitOr,
    Shl, ShlUnchecked, Shr, ShrUnchecked, Eq, Lt, Le, Ne, Ge, Gt, Cmp, Offset,
    Unknown(Json),
}

/// mir/body.rs:388
#[derive(Debug, PartialEq, Eq)]
pub enum UnOp { Not, Neg, PtrMetadata, Unknown(Json) }

/// mir/body.rs:658. The `Adt` fourth field is `Option<UserTypeAnnotationIndex>` (raw); the
/// `Coroutine`/`CoroutineClosure` defs and args are raw.
#[derive(Debug, PartialEq, Eq)]
pub enum AggregateKind {
    Array(Ty),
    Tuple,
    Adt(DefId, VariantIdx, GenericArgs, Json, Option<FieldIdx>),
    Closure(DefId, GenericArgs),
    Coroutine(Json, Json),
    CoroutineClosure(Json, Json),
    RawPtr(Ty, Mutability),
    Unknown(Json),
}

/// mir/body.rs:669. `RuntimeChecks` (body.rs:697) is raw.
#[derive(Debug, PartialEq, Eq)]
pub enum Operand { Copy(Place), Move(Place), Constant(ConstOperand), RuntimeChecks(Json), Unknown(Json) }

/// mir/body.rs:677
#[derive(Debug, PartialEq, Eq)]
pub struct Place { pub local: Local, pub projection: Vec<ProjectionElem> }

/// mir/body.rs:690. `user_ty` is `Option<UserTypeAnnotationIndex>` (raw).
#[derive(Debug, PartialEq, Eq)]
pub struct ConstOperand { pub span: Span, pub user_ty: Json, pub const_: MirConst }

/// mir/body.rs:708. Raw: `SourceInfo` (body.rs:750), `Option<VarDebugInfoFragment>` (body.rs:756).
#[derive(Debug, PartialEq, Eq)]
pub struct VarDebugInfo {
    pub name: Vec<u8>,
    pub source_info: Json,
    pub composite: Json,
    pub value: VarDebugInfoContents,
    pub argument_index: Option<u16>,
}

/// mir/body.rs:762
#[derive(Debug, PartialEq, Eq)]
pub enum VarDebugInfoContents { Place(Place), Const(ConstOperand), Unknown(Json) }

/// mir/body.rs:773
#[derive(Debug, PartialEq, Eq)]
pub enum ProjectionElem {
    Deref,
    Field(FieldIdx, Ty),
    Index(Local),
    ConstantIndex { offset: u64, min_length: u64, from_end: bool },
    Subslice { from: u64, to: u64, from_end: bool },
    Downcast(VariantIdx),
    OpaqueCast(Ty),
    Unknown(Json),
}

/// mir/body.rs:871
#[derive(Debug, PartialEq, Eq)]
pub struct SwitchTargets { pub branches: Vec<(u128, BasicBlockIdx)>, pub otherwise: BasicBlockIdx }

/// mir/body.rs:908. Raw: `FakeBorrowKind` (body.rs:960), `MutBorrowKind` (body.rs:953).
#[derive(Debug, PartialEq, Eq)]
pub enum BorrowKind { Shared, Fake(Json), Mut { kind: Json }, Unknown(Json) }

/// mir/body.rs:971
#[derive(Debug, PartialEq, Eq)]
pub enum Mutability { Not, Mut, Unknown(Json) }

/// mir/body.rs:983. `Safety` (body.rs:977) is raw.
#[derive(Debug, PartialEq, Eq)]
pub enum PointerCoercion {
    ReifyFnPointer(Json), UnsafeFnPointer, ClosureFnPointer(Json), MutToConstPointer, ArrayToPointer, Unsize,
    Unknown(Json),
}

/// mir/body.rs:1010
#[derive(Debug, PartialEq, Eq)]
pub enum CastKind {
    PointerExposeAddress, PointerWithExposedProvenance, PointerCoercion(PointerCoercion), IntToInt, FloatToInt,
    FloatToFloat, IntToFloat, PtrToPtr, FnPtrToPtr, Transmute, Subtype,
    Unknown(Json),
}

// ------------------------------------------------------------------ constants and types (ty.rs)

/// ty.rs:161
#[derive(Debug, PartialEq, Eq)]
pub struct MirConst { pub kind: ConstantKind, pub ty: Ty, pub id: MirConstId }

/// ty.rs:1381. Raw: `UnevaluatedConst` (ty.rs:1398), `ParamConst` (ty.rs:1392).
#[derive(Debug, PartialEq, Eq)]
pub enum ConstantKind { Ty(TyConst), Allocated(Allocation), Unevaluated(Json), Param(Json), ZeroSized, Unknown(Json) }

/// ty.rs:1305. `bytes` is `Bytes` (ty.rs:1284): `None` is an uninitialized byte.
#[derive(Debug, PartialEq, Eq)]
pub struct Allocation { pub bytes: Vec<Option<u8>>, pub provenance: ProvenanceMap, pub align: u64, pub mutability: Mutability }

/// ty.rs:1298. Each entry is `(Size, Prov)`: `Size` is ty.rs:1287 `usize`, `Prov` (ty.rs:1290) a
/// newtype of `AllocId`, so a bare integer.
#[derive(Debug, PartialEq, Eq)]
pub struct ProvenanceMap { pub ptrs: Vec<(usize, AllocId)> }

/// ty.rs:119. `kind` is `TyConstKind` (ty.rs:146, raw); its value is in the `consts` table by `id`.
#[derive(Debug, PartialEq, Eq)]
pub struct TyConst { pub kind: Json, pub id: TyConstId }

/// ty.rs:309. Raw: `AliasKind`, `AliasTy`, `ParamTy`, `BoundTy`.
#[derive(Debug, PartialEq, Eq)]
pub enum TyKind { RigidTy(RigidTy), Alias(Json, Json), Param(Json), Bound(Json, Json), Unknown(Json) }

/// ty.rs:548. Raw: `FloatTy`, `ForeignDef`, `Pattern` (ty.rs:111), `Region`, `PolyFnSig`, the
/// coroutine defs and args, `Dynamic`'s predicates and region.
#[derive(Debug, PartialEq, Eq)]
pub enum RigidTy {
    Bool,
    Char,
    Int(IntTy),
    Uint(UintTy),
    Float(Json),
    Adt(DefId, GenericArgs),
    Foreign(Json),
    Str,
    Array(Ty, TyConst),
    Pat(Ty, Json),
    Slice(Ty),
    RawPtr(Ty, Mutability),
    Ref(Json, Ty, Mutability),
    FnDef(DefId, GenericArgs),
    FnPtr(Json),
    Closure(DefId, GenericArgs),
    Coroutine(Json, Json),
    CoroutineClosure(Json, Json),
    Dynamic(Json, Json),
    Never,
    Tuple(Vec<Ty>),
    CoroutineWitness(Json, Json),
    Unknown(Json),
}

/// ty.rs:587
#[derive(Debug, PartialEq, Eq)]
pub enum IntTy { Isize, I8, I16, I32, I64, I128, Unknown(Json) }

/// ty.rs:610
#[derive(Debug, PartialEq, Eq)]
pub enum UintTy { Usize, U8, U16, U32, U64, U128, Unknown(Json) }

/// ty.rs:1002
#[derive(Debug, PartialEq, Eq)]
pub struct GenericArgs(pub Vec<GenericArgKind>);

/// ty.rs:1021. `Region` is raw.
#[derive(Debug, PartialEq, Eq)]
pub enum GenericArgKind { Lifetime(Json), Type(Ty), Const(TyConst), Unknown(Json) }

/// ty.rs:1096. Raw: `Safety`, `Abi` (ty.rs:1138).
#[derive(Debug, PartialEq, Eq)]
pub struct FnSig { pub inputs_and_output: Vec<Ty>, pub c_variadic: bool, pub safety: Json, pub abi: Json }

/// ty.rs:808
#[derive(Debug, PartialEq, Eq)]
pub enum AdtKind { Enum, Union, Struct, Unknown(Json) }

/// mir/mono.rs:30
#[derive(Debug, PartialEq, Eq)]
pub enum InstanceKind { Item, Intrinsic, Virtual { idx: usize }, Shim, Unknown(Json) }

/// mir/alloc.rs:15. Raw: `Instance`, the vtable's type and trait ref.
#[derive(Debug, PartialEq, Eq)]
pub enum GlobalAlloc { Function(Json), VTable(Json, Json), Static(DefId), Memory(Allocation), TypeId { ty: Ty }, Unknown(Json) }

// ------------------------------------------------------------------ layouts (abi.rs)

/// abi.rs:72. `abi` is `ValueAbi` (abi.rs:242, raw); `abi_align` is `Align` (ty.rs:1292, u64).
#[derive(Debug, PartialEq, Eq)]
pub struct LayoutShape { pub fields: FieldsShape, pub variants: VariantsShape, pub abi: Json, pub abi_align: u64, pub size: MachineSize }

/// target.rs:36, abi.rs's `Size`.
#[derive(Debug, PartialEq, Eq)]
pub struct MachineSize { pub num_bits: usize }

/// abi.rs:124. `Union` holds a `NonZero<usize>`.
#[derive(Debug, PartialEq, Eq)]
pub enum FieldsShape {
    Primitive,
    Union(usize),
    Array { stride: MachineSize, count: u64 },
    Arbitrary { offsets: Vec<MachineSize> },
    Unknown(Json),
}

/// abi.rs:174
#[derive(Debug, PartialEq, Eq)]
pub enum VariantsShape {
    Empty,
    Single { index: VariantIdx },
    Multiple { tag: Scalar, tag_encoding: TagEncoding, tag_field: usize, variants: Vec<VariantFields> },
    Unknown(Json),
}

/// abi.rs:196
#[derive(Debug, PartialEq, Eq)]
pub struct VariantFields { pub offsets: Vec<MachineSize> }

/// abi.rs:213
#[derive(Debug, PartialEq, Eq)]
pub enum TagEncoding {
    Direct,
    Niche { untagged_variant: VariantIdx, niche_variants: RangeInclusive, niche_start: u128 },
    Unknown(Json),
}

/// `std::ops::RangeInclusive<VariantIdx>`, which serde writes as the struct `{start, end}`.
#[derive(Debug, PartialEq, Eq)]
pub struct RangeInclusive { pub start: VariantIdx, pub end: VariantIdx }

/// abi.rs:280
#[derive(Debug, PartialEq, Eq)]
pub enum Scalar { Initialized { value: Primitive, valid_range: WrappingRange }, Union { value: Primitive }, Unknown(Json) }

/// abi.rs:310. `FloatLength` is raw; `Pointer` holds `AddressSpace(u32)` (abi.rs:384), a newtype.
#[derive(Debug, PartialEq, Eq)]
#[allow(inconsistent_fields)]
pub enum Primitive { Int { length: IntegerLength, signed: bool }, Float { length: Json }, Pointer(u32), Unknown(Json) }

/// abi.rs:340
#[derive(Debug, PartialEq, Eq)]
pub enum IntegerLength { I8, I16, I32, I64, I128, Unknown(Json) }

/// abi.rs:399
#[derive(Debug, PartialEq, Eq)]
pub struct WrappingRange { pub start: u128, pub end: u128 }

// ------------------------------------------------------------------ the dump's tables (spec §Dump)

/// One `mir-<crate>.json`. The first field is the dump's `"crate"`.
#[derive(Debug, PartialEq, Eq)]
pub struct MirCrate {
    pub crate_name: Vec<u8>,
    pub items: Vec<Item>,
    pub insts: Vec<Inst>,
    pub calls: Vec<Call>,
    pub drops: Vec<DropRow>,
    pub tys: Vec<TyRow>,
    pub adts: Vec<Adt>,
    pub consts: Vec<ConstRow>,
    pub layouts: Vec<LayoutRow>,
    pub allocs: Vec<AllocRow>,
    pub spans: Vec<SpanRow>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Item { pub def: DefId, pub name: Vec<u8>, pub inst: Option<InstanceDef>, pub attrs: Vec<Vec<u8>> }

#[derive(Debug, PartialEq, Eq)]
pub struct Inst {
    pub id: InstanceDef,
    pub def: DefId,
    pub name: Vec<u8>,
    pub key: Vec<u8>,
    pub krate: Vec<u8>,
    pub kind: InstanceKind,
    pub body: Option<Body>,
    pub fn_sig: Option<FnSig>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Call { pub fn_ty: Ty, pub def: DefId, pub def_name: Vec<u8>, pub args: GenericArgs, pub resolved: Option<InstanceDef> }

#[derive(Debug, PartialEq, Eq)]
pub struct DropRow { pub ty: Ty, pub glue: InstanceDef, pub empty: bool }

#[derive(Debug, PartialEq, Eq)]
pub struct TyRow { pub id: Ty, pub kind: TyKind }

#[derive(Debug, PartialEq, Eq)]
pub struct Adt { pub ty: Ty, pub name: Vec<u8>, pub kind: AdtKind, pub is_box: bool, pub variants: Vec<AdtVariant> }

/// `discr` is `None` unless the ADT is an enum.
#[derive(Debug, PartialEq, Eq)]
pub struct AdtVariant { pub discr: Option<u128>, pub fields: Vec<Ty> }

/// `usize` is `TyConst::eval_target_usize` (`None` on error).
#[derive(Debug, PartialEq, Eq)]
pub struct ConstRow { pub id: TyConstId, pub usize: Option<u64> }

#[derive(Debug, PartialEq, Eq)]
pub struct LayoutRow { pub ty: Ty, pub shape: LayoutShape }

#[derive(Debug, PartialEq, Eq)]
pub struct AllocRow { pub id: AllocId, pub alloc: GlobalAlloc }

/// `line` is `LineInfo::start_line` (ty.rs:296, usize).
#[derive(Debug, PartialEq, Eq)]
pub struct SpanRow { pub id: Span, pub file: Vec<u8>, pub line: usize }

} // verus!
