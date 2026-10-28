use quic::stateless::*;

fn hex(s: &str) -> Vec<u8> {
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

fn dgram(first: u8, version: [u8; 4], dcid: &[u8], scid: &[u8], len: usize) -> Vec<u8> {
    let mut b = vec![first];
    b.extend(version);
    b.push(dcid.len() as u8);
    b.extend(dcid);
    b.push(scid.len() as u8);
    b.extend(scid);
    b.resize(len, 0);
    b
}

#[test]
fn vn_response() {
    let b = dgram(0xc0, [0x1a, 0x2a, 0x3a, 0x4a], &hex("0001020304050607"), &hex("0a0b0c0d"), 1200);
    assert_eq!(
        version_negotiation(&b),
        Some(hex("c000000000040a0b0c0d08000102030405060700000001"))
    );
}

#[test]
fn vn_cid_lengths() {
    for n in [21usize, 255] {
        let dcid = vec![7u8; n];
        let b = dgram(0xc0, [0x1a, 0x2a, 0x3a, 0x4a], &dcid, &[1, 2], 1200);
        let mut want = vec![0xc0, 0, 0, 0, 0, 2, 1, 2, n as u8];
        want.extend(&dcid);
        want.extend([0, 0, 0, 1]);
        assert_eq!(version_negotiation(&b), Some(want));
    }
    let b = dgram(0xc0, [0, 0, 0, 1], &[7u8; 21], &[1, 2], 1200);
    assert_eq!(version_negotiation(&b), None);
}

#[test]
fn vn_not_sent() {
    let v = [0x1a, 0x2a, 0x3a, 0x4a];
    let dcid = hex("0001020304050607");
    let scid = hex("0a0b0c0d");
    assert_eq!(version_negotiation(&dgram(0xc0, v, &dcid, &scid, 1199)), None);
    assert_eq!(version_negotiation(&dgram(0xc0, [0, 0, 0, 1], &dcid, &scid, 1200)), None);
    assert_eq!(version_negotiation(&dgram(0xc0, [0; 4], &dcid, &scid, 1200)), None);
    assert_eq!(version_negotiation(&vec![0x40; 1200]), None);
}

#[test]
fn stateless_reset_sizes() {
    // u[0] = 0xff: the top two bits must be masked off; the rest are distinct and non-zero.
    let mut u: Vec<u8> = (1..=27).collect();
    u[0] = 0xff;
    let token = [0xaa; 16];
    assert_eq!(stateless_reset(21, &u, &token), None);
    for (trigger, len) in [(22, 21), (43, 42), (44, 43), (1200, 43)] {
        let r = stateless_reset(trigger, &u, &token).unwrap();
        assert_eq!(r.len(), len);
        assert_eq!(r[0], 0x7f);
        assert_eq!(r[1..len - 16], u[1..len - 16]);
        assert_eq!(r[len - 16..], token);
    }
}
