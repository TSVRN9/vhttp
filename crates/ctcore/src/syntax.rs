//! Core syntax: MIR-shaped bodies, a vector of basic blocks each with statements and one
//! terminator. Local 0 is the return place, locals `1..=nargs` are the parameters.
use vstd::prelude::*;

verus! {

pub enum IntTy { U8, U16, U32, U64, U128, Usize, I8, I16, I32, I64, I128, Isize, Bool }
pub enum BinOp { Add, Sub, Mul, Div, Rem, BitXor, BitAnd, BitOr, Shl, Shr, Eq, Ne, Lt, Le, Gt, Ge }
pub enum UnOp { Not, Neg }
pub enum Proj { Deref, Field(usize), Index(usize /* local */), ConstIndex(u64), Downcast(usize) }
pub struct Place { pub local: usize, pub proj: Vec<Proj> }
pub enum ConstVal { Int(u128), Unit, Arr(Vec<ConstVal>), Shr(Box<ConstVal>) }   // promoteds, const arrays
pub enum Operand { Copy(Place), Const(IntTy, u128), Lit(ConstVal) }
pub enum AggKind { Tuple, Array, Adt(usize /* variant */) }
pub enum Rvalue {
    Use(Operand), Bin(BinOp, IntTy, Operand, Operand), Un(UnOp, IntTy, Operand),
    Cast(IntTy /* from */, IntTy /* to */, Operand), Len(Place), Discr(Place),
    Aggregate(AggKind, Vec<Operand>), Repeat(Operand, u64), RefShr(Place), RefMut(Place),
}
pub enum Stmt { Assign(Place, Rvalue), SetDiscr(Place, usize) }
pub enum Intrinsic {   // closed by 8a Task 2 Step 0 (callee census); adding one is a SPEC-CHANGE
    Declassify, GhostUnit, VecNew, VecWithCapacity, VecPush, VecExtendFromSlice, VecAsSlice,
    ArrayAsSlice, VecLen, VecSet, VecIndex, SliceSubrange, SliceToVec, Wrapping(BinOp, IntTy),
}
pub enum Callee { Fn(usize), Intr(Intrinsic) }
pub enum Term {
    Goto(usize), Switch(Operand, Vec<(u128, usize)>, usize), Assert(Operand, bool, usize),
    Call(Callee, Vec<Operand>, Place, usize), Return, Abort,
}
pub struct Block { pub stmts: Vec<Stmt>, pub term: Term }
pub enum Ty { Int(IntTy), Unit, Tuple(Vec<Ty>), Adt(Vec<Vec<Ty>>), Array(Box<Ty>, u64),
              Slice(Box<Ty>), Vec(Box<Ty>), Shr(Box<Ty>), Mut(Box<Ty>) }
pub struct Body { pub nargs: usize, pub locals: Vec<Ty>, pub blocks: Vec<Block> }
pub struct Program { pub fns: Vec<Body> }

} // verus!
