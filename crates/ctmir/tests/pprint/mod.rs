//! A debug printer of `ctcore::Program` (test tooling, not trusted) for `tests/lower.rs`: one block
//! per fn, fns sorted by path, a `Fn` callee printed as its path, so two lowered programs diff line
//! by line.
use ctcore::{AggKind, BinOp, Block, Body, Callee, ConstVal, IntTy, Intrinsic, Operand, Place, Program, Proj, Rvalue, Stmt, Term, Ty, UnOp};
use std::fmt::Write;

pub fn program_text(p: &Program, paths: &[String]) -> String {
    let mut fns: Vec<(String, String)> = p.fns.iter().enumerate().map(|(g, b)| (paths[g].clone(), body(b, paths))).collect();
    fns.sort();
    let mut s = String::new();
    for (path, b) in fns {
        let _ = write!(s, "fn {path}\n{b}");
    }
    s
}

fn body(b: &Body, paths: &[String]) -> String {
    let mut s = format!("  nargs={} locals=[{}]\n", b.nargs, b.locals.iter().map(ty).collect::<Vec<_>>().join(", "));
    for (i, blk) in b.blocks.iter().enumerate() {
        let _ = writeln!(s, "  bb{i}: {}", block(blk, paths));
    }
    s
}

fn block(blk: &Block, paths: &[String]) -> String {
    let mut parts: Vec<String> = blk.stmts.iter().map(stmt).collect();
    parts.push(format!("-> {}", term(&blk.term, paths)));
    parts.join("; ")
}

pub fn ty(t: &Ty) -> String {
    match t {
        Ty::Int(i) => ity(i).into(),
        Ty::Unit => "()".into(),
        Ty::Tuple(ts) => format!("({})", ts.iter().map(ty).collect::<Vec<_>>().join(", ")),
        Ty::Adt(vs) => format!("adt[{}]", vs.iter().map(|v| format!("({})", v.iter().map(ty).collect::<Vec<_>>().join(", "))).collect::<Vec<_>>().join(" | ")),
        Ty::Array(e, n) => format!("[{}; {n}]", ty(e)),
        Ty::Slice(e) => format!("[{}]", ty(e)),
        Ty::Vec(e) => format!("Vec<{}>", ty(e)),
        Ty::Shr(e) => format!("&{}", ty(e)),
        Ty::Mut(e) => format!("&mut {}", ty(e)),
    }
}

fn ity(i: &IntTy) -> &'static str {
    match i {
        IntTy::U8 => "u8", IntTy::U16 => "u16", IntTy::U32 => "u32", IntTy::U64 => "u64", IntTy::U128 => "u128",
        IntTy::Usize => "usize", IntTy::I8 => "i8", IntTy::I16 => "i16", IntTy::I32 => "i32", IntTy::I64 => "i64",
        IntTy::I128 => "i128", IntTy::Isize => "isize", IntTy::Bool => "bool",
    }
}

fn binop(o: &BinOp) -> &'static str {
    match o {
        BinOp::Add => "Add", BinOp::Sub => "Sub", BinOp::Mul => "Mul", BinOp::Div => "Div", BinOp::Rem => "Rem",
        BinOp::BitXor => "BitXor", BinOp::BitAnd => "BitAnd", BinOp::BitOr => "BitOr", BinOp::Shl => "Shl",
        BinOp::Shr => "Shr", BinOp::Eq => "Eq", BinOp::Ne => "Ne", BinOp::Lt => "Lt", BinOp::Le => "Le",
        BinOp::Gt => "Gt", BinOp::Ge => "Ge",
    }
}

fn place(p: &Place) -> String {
    let mut s = format!("_{}", p.local);
    for e in &p.proj {
        match e {
            Proj::Deref => s = format!("(*{s})"),
            Proj::Field(i) => s += &format!(".{i}"),
            Proj::Index(l) => s += &format!("[_{l}]"),
            Proj::ConstIndex(k) => s += &format!("[{k}]"),
            Proj::Downcast(v) => s += &format!(" as v{v}"),
        }
    }
    s
}

fn cv(c: &ConstVal) -> String {
    match c {
        ConstVal::Int(n) => n.to_string(),
        ConstVal::Unit => "unit".into(),
        ConstVal::Arr(cs) => format!("[{}]", cs.iter().map(cv).collect::<Vec<_>>().join(",")),
        ConstVal::Shr(b) => format!("&{}", cv(b)),
    }
}

fn op(o: &Operand) -> String {
    match o {
        Operand::Copy(p) => place(p),
        Operand::Const(i, n) => format!("{n}_{}", ity(i)),
        Operand::Lit(c) => format!("lit {}", cv(c)),
    }
}

fn ops(os: &[Operand]) -> String {
    os.iter().map(op).collect::<Vec<_>>().join(", ")
}

fn rv(r: &Rvalue) -> String {
    match r {
        Rvalue::Use(o) => op(o),
        Rvalue::Bin(b, i, x, y) => format!("{}.{}({}, {})", binop(b), ity(i), op(x), op(y)),
        Rvalue::Un(u, i, x) => format!("{}.{}({})", match u { UnOp::Not => "Not", UnOp::Neg => "Neg" }, ity(i), op(x)),
        Rvalue::Cast(f, t, x) => format!("Cast.{}.{}({})", ity(f), ity(t), op(x)),
        Rvalue::Len(p) => format!("Len({})", place(p)),
        Rvalue::Discr(p) => format!("Discr({})", place(p)),
        Rvalue::Aggregate(k, os) => format!("{}({})", match k { AggKind::Tuple => "Tuple".into(), AggKind::Array => "Array".into(), AggKind::Adt(v) => format!("Adt{v}") }, ops(os)),
        Rvalue::Repeat(o, n) => format!("[{}; {n}]", op(o)),
        Rvalue::RefShr(p) => format!("&{}", place(p)),
        Rvalue::RefMut(p) => format!("&mut {}", place(p)),
    }
}

fn stmt(s: &Stmt) -> String {
    match s {
        Stmt::Assign(p, r) => format!("{} = {}", place(p), rv(r)),
        Stmt::SetDiscr(p, k) => format!("discr({}) = {k}", place(p)),
    }
}

fn intr(k: &Intrinsic) -> String {
    match k {
        Intrinsic::Declassify => "Declassify".into(),
        Intrinsic::GhostUnit => "GhostUnit".into(),
        Intrinsic::VecNew => "VecNew".into(),
        Intrinsic::VecWithCapacity => "VecWithCapacity".into(),
        Intrinsic::VecPush => "VecPush".into(),
        Intrinsic::VecExtendFromSlice => "VecExtendFromSlice".into(),
        Intrinsic::VecAsSlice => "VecAsSlice".into(),
        Intrinsic::ArrayAsSlice => "ArrayAsSlice".into(),
        Intrinsic::VecLen => "VecLen".into(),
        Intrinsic::VecSet => "VecSet".into(),
        Intrinsic::VecIndex => "VecIndex".into(),
        Intrinsic::SliceSubrange => "SliceSubrange".into(),
        Intrinsic::SliceToVec => "SliceToVec".into(),
        Intrinsic::Wrapping(o, i) => format!("Wrapping.{}.{}", binop(o), ity(i)),
    }
}

fn term(t: &Term, paths: &[String]) -> String {
    match t {
        Term::Goto(b) => format!("goto bb{b}"),
        Term::Switch(o, ts, d) => format!(
            "switch {} [{}] else bb{d}",
            op(o),
            ts.iter().map(|(v, b)| format!("{v} => bb{b}")).collect::<Vec<_>>().join(", ")
        ),
        Term::Assert(o, e, b) => format!("assert {} == {e} -> bb{b}", op(o)),
        Term::Call(c, a, d, n) => {
            let callee = match c {
                Callee::Fn(g) => paths.get(*g).cloned().unwrap_or_else(|| format!("#{g}")),
                Callee::Intr(k) => format!("intr {}", intr(k)),
            };
            format!("{} = call {callee}({}) -> bb{n}", place(d), ops(a))
        }
        Term::Return => "return".into(),
        Term::Abort => "abort".into(),
    }
}
