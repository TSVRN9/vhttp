# The RFC-quantity gate read constants by bare name from every .rs file under crates/ (C8)

- **Defect**: `tools/rfc_quantity.py` pins each `allowed_*err` root's vouches to a sha256 of the text they rest on,
  including "every `const`/`static` that text names". It found those constants with one regex,
  `(const|static) NAME:`, over every `.rs` file under `crates/` (`acceptance.rs_files`: `src/`, `tests/`, `examples/`
  alike), and hashed every match of a name the text uses, in every crate. So a root's digest held:
  - test-file constants that share a token with the hashed text: `const A` (h3/tests/static_table.rs,
    quic/tests/cid.rs), `const N` (quic/tests/reassembly.rs), `const T4` (crypto/tests/aes_gcm.rs);
  - const generic parameters, read as definitions and hashed up to the next `;` (a chunk of code): `<const N: usize>`
    in crypto/tests/dudect.rs, quic/tests/common/mod.rs and twice in wire/src/varint.rs;
  - other crates' same-named items beside the one the code uses: tls's `CRYPTO_BUFFER_EXCEEDED`, `PROTOCOL_VIOLATION`
    and `H3_ALPN` next to quic's, in all seven roots.
  Fix: 9b2 Task 1 fix round 3 (this commit's tools/acceptance.py, tools/rfc_quantity.py).
- **Incidents**: 2026-11-12, an untracked `crates/quic/examples/frags_measure.rs` (a 9b1 measurement) moved root digests;
  2026-11-13, `crates/quic/tests/input_cost.rs` and `crates/tls/tests/reader_cost.rs` (9b2 Task 1) defined `const A`,
  `const B`, `const G` and moved five digests (`quick: rfc-quantity failed`). Both times the gate asked for a re-review
  of vouches whose predicates had not changed. The second was worked around by renaming the test constants
  (`COST_A`, `COST_B`, `GAP_RUN`), which fixed the instance, not the class.
- **Escape**: the gate's demos edit only the fixture's `src/` files, which held one definition per name and no generics, so
  nothing exercised a constant outside `src/`, a generic parameter or a second crate. The digest is opaque: a reviewer
  re-pinning after an unrelated move sees only "changed", never which text moved it, so the extra text stayed in the
  digests unseen. The failure is a false alarm (fail closed), which is why it
  read as noise rather than as a bug; but the same bare-name lookup meant the pinned text was not the text the code
  compiles against.
- **Class**: C8 (the RFC-quantity gate reads names, not Rust's resolution).
- **Catch**:
  - `acceptance.rs_files` yields only `crates/<crate>/src/**.rs`; `acceptance.scan` refuses a `verus!` block anywhere
    else under `crates/` (so no verified code goes unscanned), and scripts/acceptance.sh's independent fn count still
    walks every file. The rfc-quantity annotation check still reads every file, so a stray `// rfc-quantity:` outside
    `src/` fails as stale.
  - `Gate.items()` indexes `const`/`static` (and Verus `spec const`) items only: a match after `<` or `,` is a generic
    parameter and skipped.
  - `Gate.const_of(name, file)` resolves a name from the file whose text reads it: the file's own item; else what its
    `use` lines import (explicit, then glob, following `pub use`; private items are not importable across modules,
    non-`pub` items not across crates); else its crate's item; never another crate unimported. More than one candidate
    at the first level that has any fails ("reads the constant N, which names k definitions ...: ambiguous").
  - Other gates sharing the scan: `acceptance` (now src/ only, refusing `verus!` elsewhere); `cost_charge` reads a fixed
    file list (no bare-name lookup); `quick.py scope` maps changed paths to crates (a test change still re-runs that
    crate, as it should); `escape-gate.sh` greps every `.rs` file (wider is the fail-closed direction). None looks a
    name up across files.
- **Evidence**: scripts/gate-demos.sh, RFC-quantity section: a test file's and an untracked example's same-named consts
  change no digest (both fail under the old lookup: "re-review the vouches"); a const generic parameter is not read (the
  old lookup failed on it); a bare constant two modules define, imported by neither, fails closed; the same constant
  imported explicitly resolves.
- **Re-pin**: all seven root digests moved. For each, the new hashed text is the old text with lines removed and none
  added (checked by diffing the hashed bodies): crypto_allowed_err and recv_allowed_err lose tls's duplicate code and
  the tests' `const A`; allowed_tp_err, allowed_tp_err_from and tp_allowed_err also lose `N` (the test const and the
  generic-parameter chunks) and `T4`; superseded_allowed_err loses tls's `H3_ALPN` and `PROTOCOL_VIOLATION`,
  key_changes_allowed_err tls's `PROTOCOL_VIOLATION`. No `name` vouch in tools/rfc-quantity-allow.txt reads a constant,
  so no vouched read resolves differently; the constants kept are quic's (and wire's `VARINT_MAX`), the ones the code
  uses, with the RFC values (RFC 9000 §18.2, §20.1). The per-root review is in the commit message.
