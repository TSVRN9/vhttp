//! Phase 4 exit: other HTTP/3 clients fetch the static response. Run with `--ignored`.
use server::*;
use std::process::Command;

fn start() -> u16 {
    let cfg: &'static _ = Box::leak(Box::new(
        load_config(include_bytes!("data/cert.pem"), include_bytes!("data/key.pem"), vec![]).unwrap(),
    ));
    let sock = bind("127.0.0.1:0".parse().unwrap()).unwrap();
    let port = sock.local_addr().unwrap().port();
    std::thread::spawn(move || run(sock, cfg));
    port
}

fn curl_has_http3() -> bool {
    Command::new("curl").arg("--version").output().map_or(false, |o| String::from_utf8_lossy(&o.stdout).contains("HTTP3"))
}

fn curl(args: &[&str]) -> std::process::Output {
    Command::new("curl").args(["--http3-only", "-k", "-sS", "--max-time", "10"]).args(args).output().unwrap()
}

#[test]
#[ignore]
fn curl_fetches() {
    if !curl_has_http3() {
        eprintln!("skipped: curl lacks HTTP3");
        return;
    }
    let port = start();
    let o = curl(&["-o", "-", "-w", "\n%{http_code} %{http_version}", &format!("https://127.0.0.1:{port}/")]);
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let mut want = RESPONSE_BODY.to_vec();
    want.extend_from_slice(b"\n200 3");
    assert_eq!(o.stdout, want);
}

/// Two requests, one connection (curl reuses it for the second URL).
#[test]
#[ignore]
fn curl_two_requests() {
    if !curl_has_http3() {
        eprintln!("skipped: curl lacks HTTP3");
        return;
    }
    let port = start();
    let u = format!("https://127.0.0.1:{port}/");
    let o = curl(&["-o", "-", "-w", "\n%{http_code} %{http_version} %{num_connects}\n", &u, "-o", "-", "-w", "\n%{http_code} %{http_version} %{num_connects}\n", &u]);
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let body = String::from_utf8_lossy(RESPONSE_BODY);
    assert_eq!(String::from_utf8_lossy(&o.stdout), format!("{body}\n200 3 1\n{body}\n200 3 0\n"));
}

#[test]
#[ignore]
fn quiche_fetches() {
    let Ok(bin) = std::env::var("QUICHE_CLIENT") else {
        eprintln!("skipped: QUICHE_CLIENT unset");
        return;
    };
    let port = start();
    let o = Command::new(bin).args(["--no-verify", &format!("https://127.0.0.1:{port}/")]).output().unwrap();
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    assert_eq!(o.stdout, RESPONSE_BODY);
}
