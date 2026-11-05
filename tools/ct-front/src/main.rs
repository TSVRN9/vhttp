//! ct-front (TRUSTED, I/O only): reads the dump and manifest files, calls the verified
//! `ctmir::pipeline::pipeline` once, and writes its `Ok` report to the out-file, or its `Err` to
//! stderr with exit 1. It decides nothing.
//!
//! Usage: `ct-front <check | cost | selftest=<vectors>> <dump.json> <out-file> <manifest>...`
use ctmir::pipeline::{pipeline, Mode};
use std::process::exit;

fn die(msg: &str) -> ! {
    eprintln!("ct-front: {msg}");
    exit(1)
}

fn read(path: &str) -> Vec<u8> {
    std::fs::read(path).unwrap_or_else(|e| die(&format!("{path}: {e}")))
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() < 4 {
        die("usage: ct-front <check | cost | selftest=<vectors>> <dump.json> <out-file> <manifest>...");
    }
    let mode = match args[0].as_str() {
        "check" => Mode::Check,
        "cost" => Mode::Cost,
        m => match m.strip_prefix("selftest=") {
            Some(v) => Mode::Selftest(read(v)),
            None => die(&format!("unknown mode {m:?}")),
        },
    };
    let dump = read(&args[1]);
    let manifests: Vec<Vec<u8>> = args[3..].iter().map(|p| read(p)).collect();
    match pipeline(&dump, &manifests, &mode) {
        Ok(report) => std::fs::write(&args[2], report).unwrap_or_else(|e| die(&format!("{}: {e}", args[2]))),
        Err(e) => die(&String::from_utf8_lossy(&e)),
    }
}
