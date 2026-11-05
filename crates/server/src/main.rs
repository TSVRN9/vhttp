use std::net::SocketAddr;
use std::process::exit;

fn fail(msg: String) -> ! {
    eprintln!("server: {msg}");
    exit(1);
}

fn main() {
    let (mut cert, mut key, mut schemes, mut addr) = (None, None, Vec::new(), "127.0.0.1:4433".to_string());
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        let mut val = |f: &str| args.next().unwrap_or_else(|| fail(format!("{f} needs a value")));
        match a.as_str() {
            "--cert" => cert = Some(val("--cert")),
            "--key" => key = Some(val("--key")),
            "--chain-schemes" => {
                schemes = val("--chain-schemes")
                    .split(',')
                    .map(|s| u16::from_str_radix(s, 16).unwrap_or_else(|_| fail("bad --chain-schemes".into())))
                    .collect()
            }
            _ if a.starts_with("--") => fail(format!("unknown flag {a}")),
            _ => addr = a,
        }
    }
    let (Some(cert), Some(key)) = (cert, key) else { fail("usage: server --cert CHAIN.pem --key KEY.pem [--chain-schemes 0403,...] [ADDR]".into()) };
    let read = |f: &str| std::fs::read(f).unwrap_or_else(|e| fail(format!("{f}: {}", e.kind())));
    let cfg = server::load_config(&read(&cert), &read(&key), schemes).unwrap_or_else(|e| fail(format!("{cert}, {key}: {e}")));
    let addr: SocketAddr = addr.parse().unwrap_or_else(|e| fail(format!("bad address: {e}")));
    if let Err(e) = server::bind(addr).and_then(|s| server::run(s, &cfg)) {
        fail(e.to_string());
    }
}
