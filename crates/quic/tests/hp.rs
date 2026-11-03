//! Phase 3e Task 1: header protection against RFC 9001 Appendix A.2 and A.3.
mod common;
use common::*;
use quic::hp::*;

const A2_SAMPLE: &str = "d1b1c98dd7689fb8ec11d242b123dc9b";

fn a2_input() -> Vec<u8> {
    let mut v = hex("c300000001088394c8f03e5157080000449e00000002");
    v.extend_from_slice(&A2[22..38]);
    v
}

fn a3_input() -> Vec<u8> {
    let mut v = hex("c1000000010008f067a5502a4262b50040750001");
    v.extend_from_slice(&A3[20..38]);
    v
}

#[test]
fn a2_mask() {
    assert_eq!(hp_mask(&CLIENT.hp, &hex(A2_SAMPLE)).to_vec(), hex("437b9aec36"));
}

#[test]
fn a3_mask() {
    assert_eq!(hp_mask(&SERVER.hp, &hex("2cd0991cd25b0aac406a5816b6394100")).to_vec(), hex("2ec0d8356a"));
}

#[test]
fn a2_apply() {
    let input = a2_input();
    let mut b = input.clone();
    apply_hp(&mut b, 0, 18, &CLIENT.hp);
    assert_eq!(b[..22], hex("c000000001088394c8f03e5157080000449e7b9aec34")[..]);
    assert_eq!(b[22..], input[22..]);
    assert_eq!(b[..], A2[..38]);
    assert_eq!(remove_hp(&b, 18, &CLIENT.hp), input);
}

#[test]
fn a3_apply() {
    let input = a3_input();
    let mut b = input.clone();
    apply_hp(&mut b, 0, 18, &SERVER.hp);
    assert_eq!(b[..20], hex("cf000000010008f067a5502a4262b5004075c0d9")[..]);
    assert_eq!(b[..], A3[..38]);
    assert_eq!(remove_hp(&b, 18, &SERVER.hp), input);
}

#[test]
fn apply_at_offset() {
    let mut b = vec![0xee; 7];
    b.extend(a3_input());
    apply_hp(&mut b, 7, 18, &SERVER.hp);
    assert_eq!(b[..7], [0xee; 7]);
    assert_eq!(b[7..27], hex("cf000000010008f067a5502a4262b5004075c0d9")[..]);
    assert_eq!(b[7..], A3[..38]);
}

#[test]
fn short_header_bits() {
    let mut input = vec![0x41];
    input.extend([0x11; 8]);
    input.extend([0xa0, 0xa1, 0, 0]);
    input.extend(hex(A2_SAMPLE));
    input.extend([0; 3]);
    let mut b = input.clone();
    apply_hp(&mut b, 0, 9, &CLIENT.hp);
    // mask 437b9aec36, pn_len 2 (from 0x41, before masking)
    assert_eq!(b[0], 0x42);
    assert_eq!(b[1..9], input[1..9]);
    assert_eq!(b[9..11], [0xdb, 0x3b]);
    assert_eq!(b[11..], input[11..]);
    assert_eq!(remove_hp(&b, 9, &CLIENT.hp), input);
}
