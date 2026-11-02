//! Manifest reader (TRUSTED, unverified). One entry per line; a token starting with `#` begins a
//! comment that runs to the end of the line. Paths are `ct_key`s (see `main.rs`): the resolved
//! instance name with every `::<…>` generic-argument list removed, so they may contain spaces
//! (`std::array::<impl [u8; 16]>::as_slice`).
//!
//! ```text
//! root <path>                          CT root; must resolve in its crate
//! cost-root <path>                     step-bound root (`CT_MODE=cost`); must resolve in its crate
//! intr <path> <Intrinsic>              e.g. `VecPush`; `Wrapping` takes `<BinOp> <IntTy>`
//! label <path> secret(a,b) public(c)   labels for bodies that can't carry attributes
//! translate-crate <crate>              foreign crate whose bodies may be translated
//! ```
//!
//! Each `intr` line asserts that a std/vstd fn behaves as its core intrinsic. `intr` lines need not
//! resolve in a given build. Rules, whatever `CT_CRATES` is:
//! - `<crate>::ct::declassify` maps only to `Declassify`, and `Declassify` only from such a path;
//! - `ct_fixtures::ct::ghost_fallback` maps only to `GhostUnit` (no other crate gets this shim:
//!   a `GhostUnit` mapping skips the body, so an in-crate one with real code would go unchecked).
//! An `intr` path inside a crate listed in `CT_CRATES` is an error (it would override that crate's
//! own body), except those shims.
//!
//! Labels (here and in `#[cfg_attr(ct_check, ct::secret(..), ct::public(..))]`): only `secret(..)`
//! is enforced, as "this param is secret". A `public(..)` name is a declaration only; the checker
//! accepts a declared-public param whose inferred label is secret. That is sound for constant time
//! (the theorem's argument agreement just covers that slot less), so never read `public(..)` as a
//! checked guarantee that the value is public.
use ctcore::{BinOp, IntTy, Intrinsic};
use std::path::PathBuf;

#[derive(Default)]
pub struct Manifest {
    pub roots: Vec<String>,
    pub cost_roots: Vec<String>,
    pub intr: Vec<(String, Intrinsic)>,
    pub labels: Vec<(String, Vec<String>, Vec<String>)>,
    pub translate_crates: Vec<String>,
}

/// Reads and merges `paths` in order. `CT_CRATES` (comma-separated) names the analysed crates.
pub fn load(paths: &[PathBuf]) -> Result<Manifest, String> {
    let crates: Vec<String> =
        std::env::var("CT_CRATES").unwrap_or_default().split(',').filter(|s| !s.is_empty()).map(String::from).collect();
    let mut m = Manifest::default();
    for p in paths {
        let file = p.display().to_string();
        let text = std::fs::read_to_string(p).map_err(|e| format!("{file}: {e}"))?;
        parse(&mut m, &file, &text, &crates)?;
    }
    Ok(m)
}

fn parse(m: &mut Manifest, file: &str, text: &str, crates: &[String]) -> Result<(), String> {
    for (n, line) in text.lines().enumerate() {
        let err = |what: &str| format!("{file}:{}: {what}: {}", n + 1, line.trim());
        let toks: Vec<&str> = line.split_whitespace().take_while(|t| !t.starts_with('#')).collect();
        let Some((&kind, rest)) = toks.split_first() else { continue };
        match kind {
            "root" => {
                if rest.is_empty() {
                    return Err(err("malformed root line"));
                }
                let path = rest.join(" ");
                if m.roots.contains(&path) {
                    return Err(err("duplicate root"));
                }
                m.roots.push(path);
            }
            "cost-root" => {
                if rest.is_empty() {
                    return Err(err("malformed cost-root line"));
                }
                let path = rest.join(" ");
                if m.cost_roots.contains(&path) {
                    return Err(err("duplicate cost-root"));
                }
                m.cost_roots.push(path);
            }
            "intr" => {
                let (path, k) = intr(rest).ok_or_else(|| err("malformed intr line"))?;
                let shim = ct_shim(&path);
                match (shim, &k) {
                    (Some("declassify"), Intrinsic::Declassify) | (Some("ghost_fallback"), Intrinsic::GhostUnit) => {}
                    (Some(_), _) => return Err(err("a ct:: shim path maps only to its own intrinsic")),
                    (None, Intrinsic::Declassify) => return Err(err("Declassify maps only from <crate>::ct::declassify")),
                    (None, _) => {
                        if crates.iter().any(|c| names_crate(&path, c)) {
                            return Err(err("intr path inside an analysed crate (CT_CRATES)"));
                        }
                    }
                }
                if m.intr.iter().any(|(p, _)| *p == path) {
                    return Err(err("duplicate intr path"));
                }
                m.intr.push((path, k));
            }
            "label" => {
                let l = label(rest).ok_or_else(|| err("malformed label line"))?;
                if m.labels.iter().any(|(p, _, _)| *p == l.0) {
                    return Err(err("duplicate label path"));
                }
                m.labels.push(l);
            }
            "translate-crate" => match rest {
                [c] => m.translate_crates.push(c.to_string()),
                _ => return Err(err("malformed translate-crate line")),
            },
            _ => return Err(err("unknown kind")),
        }
    }
    Ok(())
}

/// `Some(name)` when `path` is `<crate>::ct::declassify` or `ct_fixtures::ct::ghost_fallback`.
fn ct_shim(path: &str) -> Option<&str> {
    match path.split("::").collect::<Vec<_>>()[..] {
        ["ct_fixtures", "ct", "ghost_fallback"] => Some("ghost_fallback"),
        [c, "ct", name @ "declassify"] if !c.is_empty() && c.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_') => Some(name),
        _ => None,
    }
}

/// `true` when `path` has a `c::` segment that starts a path (not `xc::` or `c_x::`).
fn names_crate(path: &str, c: &str) -> bool {
    let pre = format!("{c}::");
    path.match_indices(&pre).any(|(i, _)| i == 0 || !matches!(path.as_bytes()[i - 1], b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_'))
}

/// `<path tokens> <Intrinsic>` or `<path tokens> Wrapping <BinOp> <IntTy>`.
fn intr(rest: &[&str]) -> Option<(String, Intrinsic)> {
    let n = rest.len();
    if n >= 4 && rest[n - 3] == "Wrapping" {
        return Some((rest[..n - 3].join(" "), Intrinsic::Wrapping(binop(rest[n - 2])?, intty(rest[n - 1])?)));
    }
    if n < 2 {
        return None;
    }
    let k = match rest[n - 1] {
        "Declassify" => Intrinsic::Declassify,
        "GhostUnit" => Intrinsic::GhostUnit,
        "VecNew" => Intrinsic::VecNew,
        "VecWithCapacity" => Intrinsic::VecWithCapacity,
        "VecPush" => Intrinsic::VecPush,
        "VecExtendFromSlice" => Intrinsic::VecExtendFromSlice,
        "VecAsSlice" => Intrinsic::VecAsSlice,
        "ArrayAsSlice" => Intrinsic::ArrayAsSlice,
        "VecLen" => Intrinsic::VecLen,
        "VecSet" => Intrinsic::VecSet,
        "VecIndex" => Intrinsic::VecIndex,
        "SliceSubrange" => Intrinsic::SliceSubrange,
        "SliceToVec" => Intrinsic::SliceToVec,
        _ => return None,
    };
    Some((rest[..n - 1].join(" "), k))
}

fn binop(s: &str) -> Option<BinOp> {
    Some(match s {
        "Add" => BinOp::Add,
        "Sub" => BinOp::Sub,
        "Mul" => BinOp::Mul,
        "Div" => BinOp::Div,
        "Rem" => BinOp::Rem,
        "BitXor" => BinOp::BitXor,
        "BitAnd" => BinOp::BitAnd,
        "BitOr" => BinOp::BitOr,
        "Shl" => BinOp::Shl,
        "Shr" => BinOp::Shr,
        "Eq" => BinOp::Eq,
        "Ne" => BinOp::Ne,
        "Lt" => BinOp::Lt,
        "Le" => BinOp::Le,
        "Gt" => BinOp::Gt,
        "Ge" => BinOp::Ge,
        _ => return None,
    })
}

fn intty(s: &str) -> Option<IntTy> {
    Some(match s {
        "U8" => IntTy::U8,
        "U16" => IntTy::U16,
        "U32" => IntTy::U32,
        "U64" => IntTy::U64,
        "U128" => IntTy::U128,
        "Usize" => IntTy::Usize,
        "I8" => IntTy::I8,
        "I16" => IntTy::I16,
        "I32" => IntTy::I32,
        "I64" => IntTy::I64,
        "I128" => IntTy::I128,
        "Isize" => IntTy::Isize,
        "Bool" => IntTy::Bool,
        _ => return None,
    })
}

/// `<path tokens> [secret(a,..)] [public(b,..)]`, each list at most once, at least one present.
fn label(rest: &[&str]) -> Option<(String, Vec<String>, Vec<String>)> {
    let i = rest.iter().position(|t| t.starts_with("secret(") || t.starts_with("public("))?;
    if i == 0 {
        return None;
    }
    let (mut secret, mut public) = (None, None);
    for t in &rest[i..] {
        let (slot, inner) = if let Some(s) = t.strip_prefix("secret(") {
            (&mut secret, s)
        } else {
            (&mut public, t.strip_prefix("public(")?)
        };
        let inner = inner.strip_suffix(')')?;
        let names: Vec<String> = if inner.is_empty() { vec![] } else { inner.split(',').map(String::from).collect() };
        if slot.is_some() || names.iter().any(|x| x.is_empty() || !x.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')) {
            return None;
        }
        *slot = Some(names);
    }
    // Each name at most once across both lists.
    let all: Vec<&String> = secret.iter().chain(public.iter()).flatten().collect();
    if (1..all.len()).any(|i| all[..i].contains(&all[i])) {
        return None;
    }
    Some((rest[..i].join(" "), secret.unwrap_or_default(), public.unwrap_or_default()))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(text: &str) -> Result<Manifest, String> {
        let mut m = Manifest::default();
        parse(&mut m, "m.txt", text, &["crypto".to_string()]).map(|()| m)
    }

    fn err(text: &str) -> String {
        match p(text) {
            Ok(_) => panic!("accepted: {text}"),
            Err(e) => e,
        }
    }

    #[test]
    fn parses_every_kind() {
        let m = p("# header\n\
                   root crypto::aes::aes128_encrypt_block   # trailing comment\n\
                   cost-root <a::B as a::C>::parse   # predicted: bounded\n\
                   intr std::vec::Vec::push VecPush\n\
                   intr std::array::<impl [u8; 16]>::as_slice ArrayAsSlice\n\
                   intr core::num::<impl u32>::wrapping_add Wrapping Add U32\n\
                   intr crypto::ct::declassify Declassify\n\
                   label foo::bar secret(a,b) public(c)\n\
                   label foo::baz public()\n\
                   translate-crate vstd\n\
                   \n")
        .unwrap();
        assert_eq!(m.roots, ["crypto::aes::aes128_encrypt_block"]);
        assert_eq!(m.cost_roots, ["<a::B as a::C>::parse"]);
        assert_eq!(m.intr.len(), 4);
        assert!(m.intr[0].0 == "std::vec::Vec::push" && matches!(m.intr[0].1, Intrinsic::VecPush));
        assert!(m.intr[1].0 == "std::array::<impl [u8; 16]>::as_slice" && matches!(m.intr[1].1, Intrinsic::ArrayAsSlice));
        assert!(matches!(m.intr[2].1, Intrinsic::Wrapping(BinOp::Add, IntTy::U32)));
        assert!(matches!(m.intr[3].1, Intrinsic::Declassify));
        assert_eq!(m.labels[0], ("foo::bar".to_string(), vec!["a".to_string(), "b".to_string()], vec!["c".to_string()]));
        assert_eq!(m.labels[1], ("foo::baz".to_string(), vec![], vec![]));
        assert_eq!(m.translate_crates, ["vstd"]);
    }

    #[test]
    fn hash_inside_a_token_is_not_a_comment() {
        let m = p("root crypto::f::{closure#0}\n").unwrap();
        assert_eq!(m.roots, ["crypto::f::{closure#0}"]);
    }

    #[test]
    fn errors_name_file_and_line() {
        for (text, what) in [
            ("\nexclude crypto::x\n", "unknown kind"),
            ("\nroot\n", "malformed"),
            ("\ncost-root\n", "malformed"),
            ("\ncost-root crypto::a\ncost-root crypto::a\n", "duplicate"),
            ("\nintr std::vec::Vec::push\n", "malformed"),
            ("\nintr std::vec::Vec::push VecPop\n", "malformed"),
            ("\nintr core::num::<impl u32>::wrapping_add Wrapping Add\n", "malformed"),
            ("\nintr core::num::<impl u32>::wrapping_add Wrapping Add U31\n", "malformed"),
            ("\nintr core::num::<impl u32>::wrapping_add Add U32\n", "malformed"),
            ("\nlabel foo::bar\n", "malformed"),
            ("\nlabel foo::bar secret(a b)\n", "malformed"),
            ("\nlabel foo::bar secret(a,,b)\n", "malformed"),
            ("\nlabel foo::bar secret(a) secret(b)\n", "malformed"),
            ("\nlabel secret(a)\n", "malformed"),
            ("\ntranslate-crate\n", "malformed"),
            ("\ntranslate-crate a b\n", "malformed"),
            ("\nintr crypto::aes::sbox_ct VecLen\n", "analysed crate"),
            ("\nintr <std::vec::Vec<u8> as crypto::T>::f VecLen\n", "analysed crate"),
            ("\nintr crypto::ct::declassify_all Declassify\n", "Declassify maps only"),
            ("\nintr crypto::ct::declassify_all VecLen\n", "analysed crate"),
            ("\nlabel foo::bar secret(a,a)\n", "malformed"),
            ("\nlabel foo::bar secret(a) public(a)\n", "malformed"),
            ("\nlabel a::b secret(x)\nlabel a::b public(y)\n", "duplicate"),
            ("\nintr crypto::ct::declassify GhostUnit\n", "own intrinsic"),
            ("\nintr crypto::ct::declassify VecLen\n", "own intrinsic"),
            ("\nintr ct_fixtures::ct::ghost_fallback Declassify\n", "own intrinsic"),
            ("\nintr ct_fixtures::ct::ghost_fallback VecLen\n", "own intrinsic"),
            ("\nintr crypto::ct::ghost_fallback GhostUnit\n", "analysed crate"),
            ("\nintr std::convert::identity Declassify\n", "Declassify maps only"),
            ("\nintr std::vec::Vec::len Declassify\n", "Declassify maps only"),
            ("\nintr crypto::x::ct::declassify Declassify\n", "Declassify maps only"),
            ("\nroot crypto::a\nroot crypto::a\n", "duplicate"),
            ("\nintr std::vec::Vec::push VecPush\nintr std::vec::Vec::push VecLen\n", "duplicate"),
        ] {
            let e = err(text);
            let line = text.lines().count();
            assert!(e.starts_with(&format!("m.txt:{line}: ")), "{e}");
            assert!(e.contains(what), "{e} (wanted {what})");
        }
    }

    #[test]
    fn ct_shims_load_whatever_ct_crates_is() {
        let shims = "intr crypto::ct::declassify Declassify\n\
                     intr ct_fixtures::ct::declassify Declassify\nintr ct_fixtures::ct::ghost_fallback GhostUnit\n";
        for crates in [vec![], vec!["crypto".to_string()], vec!["wire".to_string()], vec!["ct_fixtures".to_string()]] {
            let mut m = Manifest::default();
            parse(&mut m, "m.txt", shims, &crates).unwrap();
            assert_eq!(m.intr.len(), 3);
        }
        // GhostUnit stays legal on a non-shim, non-analysed path (vstd's Ghost residue).
        assert!(p("intr vstd::prelude::Ghost::assume_new_fallback GhostUnit\n").is_ok());
    }

    #[test]
    fn analysed_crate_rule_is_by_path_segment() {
        // `notcrypto::` and `crypto_x::` are other crates.
        assert!(p("intr notcrypto::f VecLen\nintr crypto_x::f VecLen\n").is_ok());
    }

    #[test]
    fn load_merges_files_and_names_missing_ones() {
        let dir = std::env::temp_dir().join(format!("ct-manifest-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let (a, b) = (dir.join("a.txt"), dir.join("b.txt"));
        std::fs::write(&a, "root x::f\n").unwrap();
        std::fs::write(&b, "root x::g\nbogus\n").unwrap();
        let ok = load(&[a.clone()]).unwrap();
        assert_eq!(ok.roots, ["x::f"]);
        let e = load(&[a.clone(), b.clone()]).err().unwrap();
        assert!(e.starts_with(&format!("{}:2: ", b.display())), "{e}");
        let missing = dir.join("none.txt");
        assert!(load(&[missing.clone()]).err().unwrap().starts_with(&missing.display().to_string()));
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
