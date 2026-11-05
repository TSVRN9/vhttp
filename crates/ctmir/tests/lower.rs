use ctmir::json::parse;
use ctmir::lower::{FnInfo, Reject};
use ctmir::lower_fn::lower;
use ctmir::mir::*;
use ctmir::policy::Policy;
use ctmir::schema::decode;

mod pprint;

const TINY: &[u8] = include_bytes!("data/tiny.json");

fn dec(b: &[u8]) -> MirCrate { decode(parse(b).expect("parse")).expect("decode") }

fn s(b: &[u8]) -> String { String::from_utf8_lossy(b).into_owned() }

fn v(x: &str) -> Vec<u8> { x.as_bytes().to_vec() }

fn pol0() -> Policy {
    Policy {
        roots: vec![], cost_roots: vec![], labels: vec![], internal_crates: vec![], translate_crates: vec![],
        declassify: vec![], ghost_unit: vec![],
    }
}

fn reject_line(r: &Reject) -> String {
    match r {
        Reject::Unsupported { path, what, site } => format!("reject Unsupported {} {} # {}\n", s(site), s(path), s(what)),
        Reject::Unresolved { path, callee, site } => format!("reject Unresolved {} {} # {}\n", s(site), s(path), s(callee)),
        Reject::Attr { path, msg } => format!("reject Attr {} # {}\n", s(path), s(msg)),
        Reject::Root { path, msg } => format!("reject Root {} # {}\n", s(path), s(msg)),
    }
}

fn text(m: &MirCrate, pol: &Policy, root: &str) -> String { text_k(m, pol, root, &mut Vec::new()) }

fn text_k(m: &MirCrate, pol: &Policy, root: &str, keys: &mut ctmir::lower_term::Keys) -> String {
    match lower(m, pol, root.as_bytes(), keys) {
        Ok((p, infos)) => pprint::program_text(&p, &infos.iter().map(|i: &FnInfo| s(&i.path)).collect::<Vec<_>>()),
        Err(es) => {
            let mut lines: Vec<String> = es.iter().map(reject_line).collect();
            lines.sort();
            lines.dedup();
            lines.concat()
        }
    }
}

/// `b` with its only occurrence of `from` replaced by `to`.
fn edit(b: &[u8], from: &str, to: &str) -> Vec<u8> {
    let s = std::str::from_utf8(b).unwrap();
    assert_eq!(s.matches(from).count(), 1, "{from}");
    s.replacen(from, to, 1).into_bytes()
}

fn kinds(m: &MirCrate, root: &str) -> Vec<String> {
    match lower(m, &pol0(), root.as_bytes(), &mut Vec::new()) {
        Ok(_) => vec![],
        Err(es) => es.iter().map(|r| reject_line(r).split_whitespace().nth(1).unwrap().to_string()).collect(),
    }
}

#[test]
fn tiny_lowers() {
    let m = dec(TINY);
    // `a[i & 3] ^ x[1]`: the bounds check, then the read (rustc folded `x[1]` to `2`).
    assert_eq!(text(&m, &pol0(), "tiny::tiny"), "fn tiny::tiny\n  nargs=2 locals=[u8, &[u8; 4], usize, [u8; 3], u8, usize, bool]\n\
        \x20 bb0: _3 = Array(1_u8, 2_u8, 3_u8); _5 = BitAnd.usize(_2, 3_usize); _6 = Lt.usize(_5, 4_usize); -> assert _6 == true -> bb1\n\
        \x20 bb1: _4 = (*_1)[_5]; _0 = BitXor.u8(_4, 2_u8); -> return\n");
    let (p, infos) = lower(&m, &pol0(), b"tiny::call", &mut Vec::new()).ok().unwrap();
    assert_eq!((p.fns.len(), s(&infos[0].path), s(&infos[1].path), infos[1].inst), (2, "tiny::call".into(), "tiny::tiny".into(), 2));
    // `Some(3)` and `None` are ADT constants: one temp each, read by the assignment.
    let opt = text(&m, &pol0(), "tiny::opt");
    assert!(opt.contains("bb1: _2 = Adt1(3_u8); _0 = _2; -> goto bb3") && opt.contains("bb2: _3 = Adt0(); _0 = _3; -> goto bb3"), "{opt}");
}

/// Review Focus 1: a missing table entry is a reject, never acceptance.
#[test]
fn missing_rows_reject() {
    let mut m = dec(TINY);
    m.calls.clear();
    assert_eq!(kinds(&m, "tiny::call"), ["Unresolved"]);
    let mut m = dec(TINY);
    m.adts.clear();
    assert!(!kinds(&m, "tiny::opt").is_empty());
    assert!(kinds(&m, "tiny::opt").iter().all(|k| k == "Unsupported"));
}

/// Review Focus 4: an uninitialized byte or a pointer in an integer constant.
#[test]
fn bad_constant_bytes_reject() {
    let m = dec(&edit(TINY, "\"bytes\":[2,0,0,0,0,0,0,0]", "\"bytes\":[null,0,0,0,0,0,0,0]"));
    assert_eq!(kinds(&m, "tiny::call"), ["Unsupported"]);
    let m = dec(&edit(TINY, "\"bytes\":[2,0,0,0,0,0,0,0],\"provenance\":{\"ptrs\":[]}", "\"bytes\":[2,0,0,0,0,0,0,0],\"provenance\":{\"ptrs\":[[0,0]]}"));
    assert_eq!(kinds(&m, "tiny::call"), ["Unsupported"]);
    assert_eq!(kinds(&dec(TINY), "tiny::call"), Vec::<String>::new());
}

/// Two instances under one key: the root (or a callee) is ambiguous.
#[test]
fn shared_key_rejects() {
    let mut m = dec(TINY);
    m.insts[1].key = v("tiny::tiny");
    match lower(&m, &pol0(), b"tiny::tiny", &mut Vec::new()) {
        Err(es) => match &es[..] { [Reject::Root { msg, .. }] => assert!(s(msg).contains("ambiguous")), _ => panic!() },
        Ok(_) => panic!("accepted"),
    }
}

fn ambiguous(r: &Result<(ctcore::Program, Vec<FnInfo>), Vec<Reject>>) -> bool {
    match r {
        Err(es) => es.iter().any(|e| matches!(e, Reject::Unsupported { what, .. } if s(what).starts_with("ambiguous key"))),
        Ok(_) => false,
    }
}

/// A callee whose key is the root's but is another instance: `Unsupported` "ambiguous key".
#[test]
fn ambiguous_callee_key() {
    let mut m = dec(TINY);
    // `tiny::call` calls `tiny::tiny`; give the callee the root's key (and drop its item, so the
    // root still names one fn)
    m.insts[2].key = v("tiny::call"); // insts[2] is `tiny::tiny` (id 0)
    m.items.retain(|it| it.inst != Some(0));
    assert!(ambiguous(&lower(&m, &pol0(), b"tiny::call", &mut Vec::new())));
}

/// Two roots share one key map: the second reaches a different instance under the first's key.
#[test]
fn ambiguous_across_roots() {
    let mut m = dec(TINY);
    // a second instance of `tiny::tiny` (id 3), which `tiny::call`'s call now resolves to
    let mut copy = dec(TINY).insts.remove(2);
    copy.id = 3;
    copy.key = v("tiny::tiny");
    copy.def = m.insts[2].def;
    m.insts.push(copy);
    m.calls[0].resolved = Some(3);
    assert!(lower(&m, &pol0(), b"tiny::call", &mut Vec::new()).is_ok(), "alone, the second root lowers");
    let mut keys = Vec::new();
    assert!(lower(&m, &pol0(), b"tiny::tiny", &mut keys).is_ok());
    assert!(ambiguous(&lower(&m, &pol0(), b"tiny::call", &mut keys)));
    // the root path: `tiny::call`'s closure binds `tiny::tiny` to instance 3; root `tiny::tiny`
    // (instance 0) on the same map is a `Root` reject
    let mut keys = Vec::new();
    assert!(lower(&m, &pol0(), b"tiny::call", &mut keys).is_ok());
    match lower(&m, &pol0(), b"tiny::tiny", &mut keys) {
        Err(es) => match &es[..] { [Reject::Root { msg, .. }] => assert!(s(msg).contains("ambiguous key")), _ => panic!() },
        Ok(_) => panic!("accepted"),
    }
}

/// Probe (Task 5 C2): label inference and `ctcore::explain` on the new `pos_drop_secret_option`
/// program, the root's parameter declared secret, then with the glue's parameter declared secret.
/// `CT_T5_OUT=<dir> cargo test -p ctmir --release --test lower -- --ignored probe_secret_option --nocapture`.
#[test]
#[ignore]
fn probe_secret_option() {
    let out = std::path::PathBuf::from(std::env::var("CT_T5_OUT").expect("CT_T5_OUT"));
    let m = dec(&std::fs::read(out.join("fixtures/mir-ct_fixtures.json")).unwrap());
    let (p, infos) = lower(&m, &pol0(), b"ct_fixtures::fx::pos_drop_secret_option", &mut Vec::new()).ok().expect("lowers");
    let paths: Vec<String> = infos.iter().map(|i| s(&i.path)).collect();
    eprint!("{}", pprint::program_text(&p, &paths));
    let kind = |k: &ctcore::RejectKind| -> String {
        use ctcore::RejectKind as K;
        match k {
            K::SecretSwitch => "SecretSwitch".into(), K::SecretAssert => "SecretAssert".into(), K::SecretIndex => "SecretIndex".into(),
            K::SecretDivOperand => "SecretDivOperand".into(), K::SecretShift => "SecretShift".into(), K::SecretAlloc => "SecretAlloc".into(),
            K::SecretRange => "SecretRange".into(), K::ArgLabel(j) => format!("ArgLabel({j})"), K::RetLabel => "RetLabel".into(),
            K::MutLabel => "MutLabel".into(), K::NotWf => "NotWf".into(), K::Recursion => "Recursion".into(), K::InferFailed => "InferFailed".into(),
        }
    };
    for glue_secret in [None, Some(false), Some(true)] {
        let decl: Vec<Option<Vec<bool>>> = infos.iter().map(|i| if i.is_root { Some(vec![true]) } else { glue_secret.map(|g| vec![g]) }).collect();
        eprintln!("== glue decl {glue_secret:?}");
        match ctcore::infer::infer_labels(&p, &decl) {
            Ok(ls) => {
                for (g, l) in ls.iter().enumerate() { eprintln!("labels {}: {:?}", paths[g], l.locals); }
                for r in ctcore::explain(&p, &ls) {
                    eprintln!("reject {} at {} bb{} stmt {:?}", kind(&r.kind), paths[r.f], r.block, r.stmt);
                }
            }
            Err(f) => eprintln!("infer failed at fn {}", paths[f]),
        }
    }
}

/// The reject messages of root `root` (empty when it lowers).
fn whats(m: &MirCrate, pol: &Policy, root: &str) -> Vec<String> {
    match lower(m, pol, root.as_bytes(), &mut Vec::new()) {
        Ok(_) => vec![],
        Err(es) => es.iter().map(|r| match r { Reject::Unsupported { what, .. } => s(what), r => reject_line(r) }).collect(),
    }
}

fn body_of<'a>(m: &'a mut MirCrate, name: &str) -> &'a mut Body {
    m.insts.iter_mut().find(|x| s(&x.name) == name).unwrap().body.as_mut().unwrap()
}

fn local(ty: Ty) -> LocalDecl { LocalDecl { ty, span: 0, mutability: Mutability::Mut } }

/// tiny with `[u8; 0]` (ty 13, const 7), `&[u8; 0]` (14), `([u8; 0],)` (15), `(u8, [u8; 0])` (16)
/// and `&mut u8` (12).
fn tiny_plus() -> MirCrate {
    let mut m = dec(TINY);
    m.consts.push(ConstRow { id: 7, usize: Some(0) });
    m.tys.push(TyRow { id: 12, kind: TyKind::RigidTy(RigidTy::Ref(ctmir::json::Json::Null, 2, Mutability::Mut)) });
    m.tys.push(TyRow { id: 13, kind: TyKind::RigidTy(RigidTy::Array(2, TyConst { kind: ctmir::json::Json::Null, id: 7 })) });
    m.tys.push(TyRow { id: 14, kind: TyKind::RigidTy(RigidTy::Ref(ctmir::json::Json::Null, 13, Mutability::Not)) });
    m.tys.push(TyRow { id: 15, kind: TyKind::RigidTy(RigidTy::Tuple(vec![13])) });
    m.tys.push(TyRow { id: 16, kind: TyKind::RigidTy(RigidTy::Tuple(vec![2, 13])) });
    m
}

fn call_term(m: &mut MirCrate) -> &mut TerminatorKind { &mut body_of(m, "tiny::call").blocks[0].terminator.kind }

fn set_dest(m: &mut MirCrate, p: Place) {
    if let TerminatorKind::Call { destination, .. } = call_term(m) { *destination = p } else { panic!() }
}

/// Task 6 `dest_ok`: a call destination is evaluated before the call in sem and after the
/// write-back in core, so one that reads the frame (`Index`, `Deref`) is rejected.
#[test]
fn call_dest_reads_reject() {
    let mut m = tiny_plus();
    body_of(&mut m, "tiny::call").locals.push(local(12));
    set_dest(&mut m, Place { local: 2, projection: vec![ProjectionElem::Deref] });
    assert_eq!(whats(&m, &pol0(), "tiny::call"), ["a call into a place behind a reference"]);
    let mut m = tiny_plus();
    body_of(&mut m, "tiny::call").locals.extend([local(11), local(1)]);
    set_dest(&mut m, Place { local: 2, projection: vec![ProjectionElem::Index(3)] });
    assert_eq!(whats(&m, &pol0(), "tiny::call"), ["a call into an indexed place"]);
}

/// Task 6: `Discriminant` of a struct (sem gives 0, core the stored variant).
#[test]
fn struct_discriminant_rejects() {
    let mut m = tiny_plus();
    let b = body_of(&mut m, "tiny::opt");
    b.locals.push(local(1));
    b.blocks[1].statements.push(Statement {
        kind: StatementKind::Assign(Place { local: 2, projection: vec![] }, Rvalue::Discriminant(Place { local: 0, projection: vec![] })),
        span: 0,
    });
    assert_eq!(whats(&m, &pol0(), "tiny::opt"), Vec::<String>::new(), "an enum's discriminants are its indices");
    m.adts[0].kind = AdtKind::Struct;
    assert_eq!(whats(&m, &pol0(), "tiny::opt"), ["discriminant of a struct, of an enum with explicit discriminants, or of a non-ADT"]);
}

/// Task 6 `plain_ty`: a declassify argument of type `[u8; 0]` (a unit-like value: its trace
/// event would carry a producer-chosen form).
#[test]
fn declassify_empty_array_rejects() {
    let mut pol = pol0();
    pol.declassify.push(v("tiny::tiny"));
    let deref1 = || Operand::Copy(Place { local: 1, projection: vec![ProjectionElem::Deref] });
    let mut m = tiny_plus();
    if let TerminatorKind::Call { args, .. } = call_term(&mut m) { *args = vec![deref1()] }
    assert_eq!(whats(&m, &pol, "tiny::call"), Vec::<String>::new(), "a declassify of `*_1: [u8; 4]` lowers");
    body_of(&mut m, "tiny::call").locals[1].ty = 14;
    assert_eq!(whats(&m, &pol, "tiny::call"), ["a declassify of a value that is not an int, bool or array of them"]);
}

/// Fix round 1: a local, a `ZeroSized` constant or a call destination of a unit-like type holding
/// an array (sem keeps its structural value; core's is `Unit`).
#[test]
fn unit_like_array_rejects() {
    let local_msg = "a local of a unit-like type holding an array";
    for ty in [13, 15] {
        let mut m = tiny_plus();
        body_of(&mut m, "tiny::tiny").locals.push(local(ty));
        assert_eq!(whats(&m, &pol0(), "tiny::tiny"), [local_msg], "ty {ty}");
    }
    // a parameter too
    let mut m = tiny_plus();
    let b = body_of(&mut m, "tiny::call");
    b.locals.insert(2, local(13));
    b.arg_count = 2;
    assert!(whats(&m, &pol0(), "tiny::call").contains(&local_msg.to_string()));
    // `(u8, [u8; 0])` is not unit-like
    let mut m = tiny_plus();
    body_of(&mut m, "tiny::tiny").locals.push(local(16));
    assert_eq!(whats(&m, &pol0(), "tiny::tiny"), Vec::<String>::new());
    // a `ZeroSized` `[u8; 0]` written into `_7.1`
    let zst = Operand::Constant(ConstOperand {
        span: 0, user_ty: ctmir::json::Json::Null, const_: MirConst { kind: ConstantKind::ZeroSized, ty: 13, id: 0 },
    });
    let b = body_of(&mut m, "tiny::tiny");
    b.blocks[0].statements.push(Statement {
        kind: StatementKind::Assign(Place { local: 7, projection: vec![ProjectionElem::Field(1, 13)] }, Rvalue::Use(zst, ctmir::json::Json::Null)),
        span: 0,
    });
    assert_eq!(whats(&m, &pol0(), "tiny::tiny"), ["a zero-sized constant of a unit-like type holding an array"]);
    // a call into `_2.1: [u8; 0]`
    let mut m = tiny_plus();
    body_of(&mut m, "tiny::call").locals.push(local(16));
    set_dest(&mut m, Place { local: 2, projection: vec![ProjectionElem::Field(1, 13)] });
    assert_eq!(whats(&m, &pol0(), "tiny::call"), ["a call into a place of a unit-like type holding an array"]);
}
