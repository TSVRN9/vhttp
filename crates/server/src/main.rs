use std::net::SocketAddr;
use std::process::exit;

fn main() {
    let addr: SocketAddr = match std::env::args().nth(1).unwrap_or_else(|| "127.0.0.1:4433".into()).parse() {
        Ok(a) => a,
        Err(e) => {
            eprintln!("server: bad address: {e}");
            exit(1);
        }
    };
    if let Err(e) = server::bind(addr).and_then(server::run) {
        eprintln!("server: {e}");
        exit(1);
    }
}
