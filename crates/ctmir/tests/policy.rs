//! The manifest parser, the labels (`decl_exec`, as `decl_spec`), the bound text and the
//! pipeline's report: the old driver's `manifest.rs`, `translate.rs` `labels` and `main.rs`
//! `poly_text` tests, ported to the verified implementations.
use ctcore::cost::{Atom, Mono, Poly};
use ctcore::IntTy;
use ctmir::pipeline::{pipeline, Mode};
use ctmir::policy::{decl_exec, parse_manifests, Policy};
use ctmir::text::poly_text;

const TINY: &[u8] = include_bytes!("data/tiny.json");

fn v(x: &str) -> Vec<u8> { x.as_bytes().to_vec() }

fn vs(xs: &[&str]) -> Vec<Vec<u8>> { xs.iter().map(|x| v(x)).collect() }

fn s(b: &[u8]) -> String { String::from_utf8_lossy(b).into_owned() }

fn p(texts: &[&str]) -> Result<Policy, String> { parse_manifests(&vs(texts)).map_err(|e| s(&e)) }

fn err(text: &str) -> String {
    match p(&[text]) {
        Ok(_) => panic!("accepted: {text}"),
        Err(e) => e,
    }
}

// ------------------------------------------------------------------ manifest.rs

#[test]
fn parses_every_kind() {
    let m = p(&["# header\n\
                 root crypto::aes::aes128_encrypt_block   # trailing comment\n\
                 cost-root <a::B as a::C>::parse   # predicted: bounded\n\
                 root std::array::<impl [u8; 16]>::as_slice\n\
                 declassify crypto::ct::declassify\n\
                 ghost vstd::prelude::Ghost::assume_new_fallback\n\
                 label foo::bar secret(a,b) public(c)\n\
                 label foo::baz public()\n\
                 translate-crate vstd\n\
                 internal-crate wire\n\
                 \n"])
    .unwrap();
    assert_eq!(m.roots, vs(&["crypto::aes::aes128_encrypt_block", "std::array::<impl [u8; 16]>::as_slice"]));
    assert_eq!(m.cost_roots, vs(&["<a::B as a::C>::parse"]));
    assert_eq!(m.declassify, vs(&["crypto::ct::declassify"]));
    assert_eq!(m.ghost_unit, vs(&["vstd::prelude::Ghost::assume_new_fallback"]));
    assert_eq!(m.labels.len(), 2);
    assert_eq!(m.labels[0], (v("foo::bar"), vs(&["a", "b"]), vs(&["c"])));
    assert_eq!(m.labels[1], (v("foo::baz"), vec![], vec![]));
    assert_eq!(m.translate_crates, vs(&["vstd"]));
    assert_eq!(m.internal_crates, vs(&["wire"]));
}

#[test]
fn hash_inside_a_token_is_not_a_comment() {
    assert_eq!(p(&["root crypto::f::{closure#0}\n"]).unwrap().roots, vs(&["crypto::f::{closure#0}"]));
}

#[test]
fn errors_name_manifest_and_line() {
    for (text, what) in [
        ("\nexclude crypto::x\n", "unknown kind"),
        ("\nroot\n", "malformed"),
        ("\ncost-root\n", "malformed"),
        ("\ncost-root crypto::a\ncost-root crypto::a\n", "duplicate"),
        ("\nintr std::vec::Vec::push VecPush\n", "obsolete"),
        ("\nintr crypto::ct::declassify Declassify\n", "obsolete"),
        ("\nlabel foo::bar\n", "malformed"),
        ("\nlabel foo::bar secret(a b)\n", "malformed"),
        ("\nlabel foo::bar secret(a,,b)\n", "malformed"),
        ("\nlabel foo::bar secret(a) secret(b)\n", "malformed"),
        ("\nlabel secret(a)\n", "malformed"),
        ("\nlabel foo::bar secret(a,a)\n", "malformed"),
        ("\nlabel foo::bar secret(a) public(a)\n", "malformed"),
        ("\nlabel foo::bar secret(a-b)\n", "malformed"),
        ("\nlabel a::b secret(x)\nlabel a::b public(y)\n", "duplicate"),
        ("\ntranslate-crate\n", "malformed"),
        ("\ntranslate-crate a b\n", "malformed"),
        ("\ninternal-crate\n", "malformed"),
        ("\ndeclassify\n", "malformed"),
        ("\ndeclassify crypto::ct::declassify_all\n", "declassify names only"),
        ("\ndeclassify std::convert::identity\n", "declassify names only"),
        ("\ndeclassify crypto::x::ct::declassify\n", "declassify names only"),
        ("\ndeclassify crypto::ct::declassify\ndeclassify crypto::ct::declassify\n", "duplicate"),
        ("\nghost\n", "malformed"),
        ("\nghost a::f\nghost a::f\n", "duplicate"),
        ("\nroot crypto::a\nroot crypto::a\n", "duplicate"),
    ] {
        let e = err(text);
        let line = text.lines().count();
        assert!(e.starts_with(&format!("manifest 1:{line}: ")), "{e}");
        assert!(e.contains(what), "{e} (wanted {what})");
    }
}

#[test]
fn manifests_merge_in_order_and_errors_name_the_manifest() {
    let m = p(&["root x::f\n", "root x::g\n"]).unwrap();
    assert_eq!(m.roots, vs(&["x::f", "x::g"]));
    let e = p(&["root x::f\n", "root x::g\nbogus\n"]).err().unwrap();
    assert!(e.starts_with("manifest 2:2: "), "{e}");
    assert!(p(&["root x::f\n", "root x::f\n"]).err().unwrap().starts_with("manifest 2:1: duplicate"));
}

#[test]
fn crlf_and_tabs_are_whitespace() {
    assert_eq!(p(&["root\tx::f\r\ncost-root  x::g \r\n"]).unwrap().roots, vs(&["x::f"]));
}

// ------------------------------------------------------------------ translate.rs `labels`

fn l(attrs: &[&str], names: &[&str], ghost: &[bool]) -> Result<Option<Vec<bool>>, String> {
    decl_exec(&vs(attrs), &vs(names), &ghost.to_vec()).map_err(|e| s(&e))
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

// ------------------------------------------------------------------ main.rs `poly_text`

#[test]
fn poly_text_names_parameters() {
    let val = |x| Atom::Val(x, IntTy::Usize);
    let mono = |coef, atoms| Mono { coef, atoms };
    let gap = Atom::Gap(Box::new(Atom::Len(1)), Box::new(val(2)));
    let poly = Poly {
        monos: vec![
            mono(1, vec![Atom::Len(1)]),
            mono(13, vec![val(2), gap]),
            mono(0, vec![val(2)]),
            mono(3, vec![val(3)]),
            mono(2, vec![val(9), val(0)]),
            mono(7, vec![]),
        ],
    };
    let names = vs(&["s", "n", ""]);
    assert_eq!(s(&poly_text(&poly, &names)), "len(s) + 13*n*sat(len(s) - n) + 3*#3 + 2*_9*_0 + 7");
    assert_eq!(s(&poly_text(&Poly { monos: vec![] }, &names)), "0");
}

// ------------------------------------------------------------------ the pipeline's report

/// `tiny.json` with `tiny::tiny`'s attributes set to `attrs` (a JSON array body).
fn tiny_with(attrs: &str) -> Vec<u8> {
    let t = std::str::from_utf8(TINY).unwrap();
    let from = "{\"def\":0,\"name\":\"tiny::tiny\",\"inst\":0,\"attrs\":[]}";
    assert_eq!(t.matches(from).count(), 1);
    t.replacen(from, &format!("{{\"def\":0,\"name\":\"tiny::tiny\",\"inst\":0,\"attrs\":[{attrs}]}}"), 1).into_bytes()
}

fn run(dump: &[u8], ms: &[&str], mode: Mode) -> Result<String, String> { pipeline(dump, &vs(ms), &mode).map(|r| s(&r)).map_err(|e| s(&e)) }

#[test]
fn check_report() {
    let d = tiny_with("\"#[ct::secret(a)]\",\"#[ct::public(i)]\"");
    let r = run(&d, &["root tiny::tiny\nroot other::f\n"], Mode::Check).unwrap();
    assert!(r.contains("root tiny::tiny ok\n") && r.contains("checked tiny::tiny secret=a ret="), "{r}");
    assert!(r.split_inclusive('\n').all(|l| l.ends_with('\n')));
    let lines: Vec<&str> = r.lines().collect();
    let sorted = { let mut s = lines.clone(); s.sort(); s.dedup(); s };
    assert_eq!(lines, sorted);
    // a root without a ct:: attribute, and an unknown parameter name
    let r = run(TINY, &["root tiny::tiny\n"], Mode::Check).unwrap();
    assert_eq!(r, "reject tiny::tiny Root tiny::tiny: a root needs a ct:: attribute\n");
    let r = run(&tiny_with("\"#[ct::secret(zz)]\""), &["root tiny::tiny\n"], Mode::Check).unwrap();
    assert!(r.starts_with("reject tiny::tiny Attr tiny::tiny: unknown parameter name zz"), "{r}");
    // a label line instead of the attribute; both is an error
    let r = run(TINY, &["root tiny::tiny\nlabel tiny::tiny public(a,i)\n"], Mode::Check).unwrap();
    assert!(r.contains("root tiny::tiny ok\n"), "{r}");
    let r = run(&d, &["root tiny::tiny\nlabel tiny::tiny public(a,i)\n"], Mode::Check).unwrap();
    assert!(r.contains("both ct:: attributes and a manifest label line"), "{r}");
}

#[test]
fn hard_errors() {
    assert!(run(TINY, &["root other::f\n"], Mode::Check).unwrap_err().contains("no manifest root for analysed crate tiny"));
    assert!(run(TINY, &["root tiny::tiny\nghost tiny::opt\n"], Mode::Check).unwrap_err().contains("a ghost line inside the analysed crate"));
    assert!(run(b"{", &["root tiny::tiny\n"], Mode::Check).unwrap_err().starts_with("dump:"));
    assert!(run(TINY, &["intr a::b VecLen\n"], Mode::Check).unwrap_err().contains("obsolete"));
    // a cost root that names no fn is a hard error; none at all is an empty report
    assert!(run(TINY, &["cost-root tiny::nope\n"], Mode::Cost).unwrap_err().starts_with("Root tiny::nope"));
    assert_eq!(run(TINY, &["root tiny::tiny\n"], Mode::Cost).unwrap(), "");
    assert!(run(TINY, &[], Mode::Selftest(vec![])).is_err());
}

#[test]
fn cost_report() {
    let r = run(TINY, &["cost-root tiny::tiny\ncost-root tiny::call\n"], Mode::Cost).unwrap();
    let ls: Vec<&str> = r.lines().collect();
    assert_eq!(ls.len(), 2, "{r}");
    assert!(ls.iter().all(|l| l.starts_with("bounded tiny::") && l.contains(" deg=0 steps <= ")), "{r}");
}
