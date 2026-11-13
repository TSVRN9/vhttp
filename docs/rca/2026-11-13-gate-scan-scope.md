# The RFC-quantity gate's constant text: read by bare name from every .rs file, and cut at the first `;` (C8)

`tools/rfc_quantity.py` pins each `allowed_*err` root's vouches to a sha256 of the text they rest on, including "every
`const`/`static` that text names". Two defects in how it found that text.

## Defect 1: constants looked up by bare name across every .rs file

- **Defect**: one regex, `(const|static) NAME:`, over every `.rs` file under `crates/` (`acceptance.rs_files`: `src/`,
  `tests/`, `examples/` alike); every match of a name the text uses, in every crate, was hashed. So a root's digest held:
  - test-file constants that share a token with the hashed text: `const A` (h3/tests/static_table.rs,
    quic/tests/cid.rs), `const N` (quic/tests/reassembly.rs), `const T4` (crypto/tests/aes_gcm.rs);
  - const generic parameters, read as definitions and hashed up to the next `;` (a chunk of code): `<const N: usize>`
    in crypto/tests/dudect.rs, quic/tests/common/mod.rs and twice in wire/src/varint.rs;
  - other crates' same-named items beside the one the code uses: tls's `CRYPTO_BUFFER_EXCEEDED`, `PROTOCOL_VIOLATION`
    and `H3_ALPN` next to quic's, in all seven roots.
  And a path-qualified read `a::b::NAME` was looked up by `NAME` alone, so another crate's constant named that way was
  hashed only if the bare name happened to match (fail open), and the reading crate's same-named one could be hashed in
  its place. Associated constants (`impl T { const X .. }`) were read as module items, so a bare `X` could pin `T::X`,
  and a read `T::X` or `Self::X` hashed whatever bare `X` resolved to (found in Task 1's round-4 review: a reviewer's
  `DemoT::DEMO_K` changed from 3 to 4 left the digest unchanged).
- **Incidents**: 2026-11-12, an untracked `crates/quic/examples/frags_measure.rs` (a 9b1 measurement) moved root digests;
  2026-11-13, `crates/quic/tests/input_cost.rs` and `crates/tls/tests/reader_cost.rs` (9b2 Task 1) defined `const A`,
  `const B`, `const G` and moved five digests (`quick: rfc-quantity failed`). Both times the gate asked for a re-review
  of vouches whose predicates had not changed. The second was first worked around by renaming the test constants
  (`COST_A`, `COST_B`, `GAP_RUN`), which fixed the instance, not the class.
- **Escape**: the gate's demos edit only the fixture's `src/` files, which held one definition per name, no generics,
  one crate and no qualified constant, so nothing exercised a constant outside `src/`, a generic parameter, a second
  crate or a path. The digest is opaque: a reviewer re-pinning after an unrelated move sees only "changed", never which
  text moved it, so the extra text stayed in the digests unseen. The visible failure is a false alarm (fail closed),
  which is why it read as noise rather than a bug; the same lookup also failed open on qualified reads.
- **Class**: C8 (the RFC-quantity gate reads names, not Rust's resolution).

## Defect 2: a constant item cut at its first `;`

- **Defect**: the item's text ended at the first `;` after its name, which for an array type is inside the type:
  `pub const H3_ALPN: [u8; 2] = *b"h3";` hashed as `const H3_ALPN: [u8;`, so its value was never hashed (changing it to
  `*b"h4"` left superseded_allowed_err's digest unchanged, found in Task 1's review). Every other constant the seven
  roots name has a scalar type and was hashed whole.
- **Escape**: the fixture's constants are all `u64`; no demo changed a constant with brackets in its type, and the
  hashed text is never shown, so the truncation was invisible.
- **Class**: C8.

## Catch (both)

- `acceptance.rs_files` yields only `crates/<crate>/src/**.rs`; `acceptance.scan` refuses a `verus!` block anywhere else
  under `crates/` (so no verified code goes unscanned); scripts/acceptance.sh's independent fn count still walks every
  file, and the rfc-quantity annotation check still reads every file, so a stray `// rfc-quantity:` outside `src/`
  fails as stale.
- `Gate.items()` indexes `const`/`static` (and Verus `spec const`) items only (a match after `<` or `,` is a generic
  parameter and skipped), by module: an inline `mod NAME {` is its own module; a module whose attributes hold
  `#[cfg(test)]` or `#[cfg(all(.., test, ..))]`, inline or declared `mod NAME;` (the file and everything under it), is
  not indexed, so test constants are excluded wherever they live (a `cfg(any(test, ..))` module is indexed). Each item
  ends at its first `;` outside `()`, `[]` and `{}` (string and char literals are blanked before the scan). A constant
  inside an `impl` or `trait` block is an associated item, indexed apart by its type (the impl's self type, or the
  trait); a bare name never resolves to one.
- `Gate.const_of(name, file, offset)` resolves a bare name from the module holding the text: the module's own item; else
  what its `use` lines import (explicit, then glob, following `pub use`; `pub` items across crates, `pub(..)` within
  one, private ones into the module and its descendants); else an item anywhere in its crate. It never takes another
  crate's item that no `use` line imports. More than one candidate at the first level that has any fails ("reads the
  constant N, which names k definitions ...: ambiguous").
- `Gate.const_at` resolves a qualified `a::b::NAME` through the path (`crate`, `self`, `super`, a child module, a crate
  name, or a name a `use` line imports, `use a::{self}` included) to exactly one item, else fails. A path ending in a
  type, `T::NAME` (also `T::<..>::NAME`), or `Self::NAME` (the enclosing impl's type, and the trait it implements)
  resolves to exactly one associated item of that name, else fails; a `T` that no struct, enum, union, trait or type
  alias in the crates' src/ declares (a std or vstd type) is not ours and its constant is not hashed. A qualified-self
  read `<T as Tr>::NAME` of a name one of our items has fails (not resolved). A path rooted in vstd, std or a primitive
  type is not hashed.
- Other gates sharing the scan: `acceptance` (src/ only, refusing `verus!` elsewhere); `cost_charge` reads a fixed file
  list (no name lookup); `quick.py scope` maps changed paths to crates (a test change still re-runs that crate, as it
  should); `escape-gate.sh` greps every `.rs` file (wider is the fail-closed direction). None looks a name up across
  files.

## Evidence

scripts/gate-demos.sh, RFC-quantity section, each checked against the tool before the fix:
- a test file's and an untracked example's same-named consts change no digest (both failed before: "re-review");
- a const generic parameter is not read (failed before);
- a bare constant two modules define, imported by neither, fails closed; the same constant imported explicitly resolves;
- an array constant's value change moves the digest (passed before: Defect 2);
- a path-qualified constant of another crate, same-named as the reading file's own, and one only that crate defines:
  each value change moves the digest (both passed before);
- an associated constant read as `Type::NAME`: its value change moves the digest (passed before); a bare name with an
  associated and an imported constant of that name resolves to the imported one (moved the digest before);
- an inline module's constant is not the file's own (ambiguous before round 4); test modules, inline and a file
  declared `#[cfg(all(test, ..))]`, are not read (ambiguous before); a constant read through a `use a::{self}` module
  resolves and its value change moves the digest.

## Re-pin

Fix round 3 (commit 9962805) moved all seven root digests: each new hashed body was the old one with lines removed and
none added (bodies diffed): crypto_allowed_err and recv_allowed_err lost tls's duplicate code and the tests' `const A`;
allowed_tp_err, allowed_tp_err_from and tp_allowed_err also lost `N` (the test const and the generic-parameter chunks)
and `T4`; superseded_allowed_err lost tls's `H3_ALPN` and `PROTOCOL_VIOLATION`; key_changes_allowed_err tls's
`PROTOCOL_VIOLATION`. Fix round 4 (Defect 2, qualified paths, inline modules) moved one: superseded_allowed_err, whose
hashed `H3_ALPN` now carries its value `*b"h3"` (RFC 9114 §3.1's ALPN token, "h3"); no other body changed. No `name`
vouch in tools/rfc-quantity-allow.txt and no `// rfc-quantity:` annotation reads a constant, so no vouched read resolves
differently. The constants now hashed were checked: the transport parameter ids 0x00-0x10 (RFC 9000 §18.2), the error
codes 0x01, 0x03, 0x06, 0x07, 0x08, 0x0a, 0x0d (§20.1), `MAX_ACK_DELAY_LIMIT` 2^14 (§18.2), `MAX_STREAMS_LIMIT` 2^60
(§4.6), `MAX_CID_LEN` 20 and `RESET_TOKEN_LEN` 16 (§18.2), `MIN_INITIAL_DATAGRAM` 1200 (§14.1), `VARINT_MAX` 2^62 - 1
(§16) and `H3_ALPN` "h3" carry their RFC values; `MAX_CRYPTO_BUFFER` (16384), `MAX_CRYPTO_RANGES` (4096) and `RAND_LEN`
(129) are implementation limits, not RFC quantities.
