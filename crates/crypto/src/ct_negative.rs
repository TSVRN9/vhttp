// Negative control for scripts/ct-check.sh: compiled only with --cfg ct_negative; must be rejected.
#[cfg_attr(ct_check, ct::secret(k))]
pub fn secret_branch(k: &[u8; 16]) -> u8 {
    if k[0] == 0 { 1 } else { 0 }
}
