//! ct-dump (TRUSTED, unverified, decision-free; `tools/ct-driver`): the MIR dumper of the
//! verified front end. It runs as `RUSTC_WORKSPACE_WRAPPER`. A crate named in `CT_CRATES`
//! (comma-separated) compiles in-process under rustc_public with the analysis flags and is dumped to
//! `$CT_OUT/mir-<crate>.json` (`dump.rs`; `CT_OUT` is created if missing); every other invocation
//! passes through to rustc unchanged. A crate named in `CT_ENCODE_MIR` (comma-separated) also gets
//! `-Zalways-encode-mir`, so the crates compiled after it see all its bodies; ct-check.sh names the
//! manifests' `translate-crate` crates there. The flag changes which MIR is available, never what it
//! is. Every check, verdict and report is `ctmir::pipeline`'s, run by `tools/ct-front`.
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
#[macro_use]
extern crate rustc_public;
extern crate rustc_public_bridge;
extern crate serde_json;

mod dump;

use rustc_public::mir::mono::Instance;
use rustc_public::CompilerError;
use std::path::PathBuf;
use std::process::{exit, Command};

/// The key of a dumped instance (`insts[].key`): the resolved instance's name with every `::<…>`
/// generic-argument list removed. `::<impl …>` segments stay, so
/// `std::array::<impl [u8; 16]>::as_slice` keeps its N and `core::num::<impl u32>` its width.
pub fn ct_key(inst: &Instance) -> String {
    strip_generic_args(&inst.name())
}

/// `s` with every `::<…>` generic-argument list removed; `::<impl …>` segments are kept. The `>`
/// of `->` does not close a list. An unbalanced list is kept verbatim.
pub fn strip_generic_args(s: &str) -> String {
    let b = s.as_bytes();
    let (mut out, mut i, mut kept) = (String::new(), 0, 0);
    while i < b.len() {
        if b[i..].starts_with(b"::<") && !b[i..].starts_with(b"::<impl ") {
            let (mut depth, mut j, mut end) = (0usize, i + 2, None);
            while j < b.len() {
                match b[j] {
                    b'<' => depth += 1,
                    b'>' if b[j - 1] != b'-' => {
                        depth -= 1;
                        if depth == 0 {
                            end = Some(j);
                            break;
                        }
                    }
                    _ => {}
                }
                j += 1;
            }
            let Some(e) = end else { break };
            out.push_str(&s[kept..i]);
            i = e + 1;
            kept = i;
        } else {
            i += 1;
        }
    }
    out.push_str(&s[kept..]);
    out
}

fn env_list(var: &str) -> Vec<String> {
    std::env::var(var).unwrap_or_default().split(',').filter(|s| !s.is_empty()).map(String::from).collect()
}

fn die(msg: &str) -> ! {
    eprintln!("ct-driver: {msg}");
    exit(1)
}

fn main() {
    // argv[1] is the real rustc (RUSTC_WORKSPACE_WRAPPER protocol), the rest its arguments.
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        die("usage: ct-driver <rustc> <args..> (run as RUSTC_WORKSPACE_WRAPPER)");
    }
    let krate = args.iter().position(|a| a == "--crate-name").and_then(|i| args.get(i + 1)).cloned();
    let Some(krate) = krate.filter(|k| env_list("CT_CRATES").contains(k)) else {
        let st = Command::new(&args[0]).args(&args[1..]).status().unwrap_or_else(|e| die(&format!("{}: {e}", args[0])));
        exit(st.code().unwrap_or(1));
    };
    let out = PathBuf::from(std::env::var("CT_OUT").unwrap_or_else(|_| die("CT_OUT is not set")));
    std::fs::create_dir_all(&out).unwrap_or_else(|e| die(&format!("{}: {e}", out.display())));
    for f in ["-Zinline-mir=no", "--cfg", "ct_check", "-Zcrate-attr=feature(register_tool)", "-Zcrate-attr=register_tool(ct)"] {
        args.push(f.to_string());
    }
    if env_list("CT_ENCODE_MIR").contains(&krate) {
        args.push("-Zalways-encode-mir".into());
    }
    let res = run!(&args, || match dump::dump(&krate, &out) {
        Ok(()) => ControlFlow::Continue(()),
        Err(e) => ControlFlow::Break(e),
    });
    match res {
        Ok(()) => {}
        Err(CompilerError::Skipped) => die(&format!("rustc ran no analysis for crate {krate}")),
        Err(CompilerError::Interrupted(e)) => die(&e),
        Err(CompilerError::Failed) => exit(1),
    }
}

#[cfg(test)]
mod tests {
    use super::strip_generic_args as k;

    #[test]
    fn ct_key_strips_generic_args_only() {
        assert_eq!(k("std::vec::Vec::<u8>::push"), "std::vec::Vec::push");
        assert_eq!(k("std::vec::Vec::<u8, std::alloc::Global>::with_capacity"), "std::vec::Vec::with_capacity");
        assert_eq!(k("vstd::prelude::Ghost::<vstd::seq::Seq<u8>>::assume_new_fallback"), "vstd::prelude::Ghost::assume_new_fallback");
        assert_eq!(k("vstd::slice::slice_subrange::<u8>"), "vstd::slice::slice_subrange");
        assert_eq!(k("core::num::<impl u32>::wrapping_add"), "core::num::<impl u32>::wrapping_add");
        assert_eq!(k("std::array::<impl [u8; 16]>::as_slice"), "std::array::<impl [u8; 16]>::as_slice");
        assert_eq!(k("<std::vec::Vec<u8> as vstd::pervasive::VecAdditionalExecFns<u8>>::set"),
                   "<std::vec::Vec<u8> as vstd::pervasive::VecAdditionalExecFns<u8>>::set");
        assert_eq!(k("a::f::<fn() -> u8, u8>::g"), "a::f::g");
        assert_eq!(k("crypto::aes::encrypt_rk::{closure#0}"), "crypto::aes::encrypt_rk::{closure#0}");
        assert_eq!(k("crypto::é::<u8>"), "crypto::é");
    }

    #[test]
    fn ct_key_keeps_unbalanced_input() {
        assert_eq!(k("a::<b"), "a::<b");
        assert_eq!(k("a::<b<c>"), "a::<b<c>");
        assert_eq!(k("a::<"), "a::<");
    }
}
