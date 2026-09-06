# Vendored HACL\* extracted C — provenance

This directory contains a **minimal, curated subset** of the C code
extracted by [KaRaMeL](https://github.com/FStarLang/karamel) from the
[HACL\*](https://github.com/hacl-star/hacl-star) formally-verified
cryptographic library (Project Everest, written in F\*/Low\*). It
realises the Ed25519 and SHA-256 `assume val`s used by Factoidal's
Verifiable Credentials Data Integrity pipeline (`VC.DataIntegrity.fst`)
via the vendored-C route (adoption-order option 2 of
`skills/crypto-policy/SKILL.md`).

## Why vendored HACL\*

Per the owner directives recorded in `skills/crypto-policy/SKILL.md`
("Dont roll our own crypto!", "pursue HACL\*") this project never
implements a digest / curve / signature / RNG primitive itself. HACL\*
is the F\*/Low\*-verified library whose extracted C Mozilla ships inside
NSS — the only crypto source matching this project's own
"specs-not-assertions" standard, and literally written in the same
language. Ed25519 sign+verify has **no** acceptable pure-OCaml/F\*
fallback (the crypto-policy skill permits a pure-OCaml DIGEST fallback
for the wasm target only — never a hand-rolled SIGNATURE).

## Source

| Field | Value |
|---|---|
| Upstream repo | `cryspen/hacl-packages` (the maintained packaging home of the HACL\* OCaml/C distribution) |
| Clone URL | https://github.com/cryspen/hacl-packages.git |
| Commit | `05c3d8fb321ed65e3db3a6a8b853019e86fb40a2` (2024-09-30) |
| Extraction | Upstream `src/` + `include/` (already KaRaMeL-extracted C dist) |
| License | Apache-2.0 (see `LICENSE-APACHE`); HACL\* is dual Apache-2.0 / MIT |

## Files vendored (curated transitive closure)

Determined by taking the `#include` closure of the three C translation
units below; unrelated primitives (Blake2, HPKE, P-256, MD5, SHA-1,
SHA-3, vectorized variants, EverCrypt agile layer) were **not**
vendored.

C sources (`src/`):
- `Hacl_Ed25519.c` — Ed25519 `sign` / `verify` / `secret_to_public`
- `Hacl_Curve25519_51.c` — field arithmetic Ed25519 depends on
- `Hacl_Hash_SHA2.c` — SHA-256 (and SHA-512, used internally by Ed25519)

Headers (`include/`, `include/internal/`, `include/krml/`): the 26
public + internal HACL\* headers and the KaRaMeL runtime headers those
three units transitively require.

### JOSE addition, 2026-09-06 — P-256 and the bignum field

Added for the Solid-OIDC / JOSE token layer (`formal/lean4/L4Factoidal/
JOSE/`, design record `docs/designissues/2026-09-06-jose-dpop-over-hacl.md`):
JWS `ES256` needs ECDSA over NIST P-256, and JWS `RS256` needs the RSA
PUBLIC operation `s^e mod n`. Both come from the SAME pinned commit as
the files above; nothing was taken from a different release.

`Hacl_Bignum4096.c` was NOT vendored. The generic 64-bit field
(`Hacl_Bignum64.c`, over `Hacl_Bignum.c`) takes the limb count at run
time, so one translation unit serves 2048-, 3072- and 4096-bit moduli,
where `Hacl_Bignum4096.c` serves only the largest. Fewer files, one
code path, same verified arithmetic.

| Path | SHA-256 |
|---|---|
| `src/Hacl_P256.c` | `876b7bcc7824e2dae453466e782275e369f0ac561af8f769577e215ae715dae1` |
| `src/Hacl_Bignum64.c` | `a6b5f901bd08bd0317edb89c899e387e26baca3dfbadc3a4d4116dd30d81e04e` |
| `src/Hacl_Bignum.c` | `1648d0c094b52bd9c7a0aad74a38e8709ce68fb705d1604a9c58fbca7c5230d4` |
| `include/Hacl_P256.h` | `6d0114e328b20bad0866eb27949c18927bbbdd026b2449584307dedde63e83d2` |
| `include/Hacl_Bignum64.h` | `661a747cba13a7728ad52c6bd78f2fd8abe8dfce971d3716521856b7f369d882` |
| `include/Hacl_Bignum.h` | `cfd8124251d693be57b55d604eb466f687edf80b8c5abe49e4807bc61d5e562b` |
| `include/internal/Hacl_P256.h` | `379829b1d137348fb2ae1649db7a6457a9aea1bbab3e0dd47e35fca964a13e8b` |
| `include/internal/Hacl_P256_PrecompTable.h` | `33a88a31a8d43bfe0906ac4a28e49038dc43f16d0f9e0cd53b18b4a8d8be0aed` |
| `include/internal/Hacl_Bignum.h` | `d1413655685a20fda4368bd4f006d65595b7407f6b845ca666843e312d42505a` |

Reproduce: `git clone https://github.com/cryspen/hacl-packages.git`,
`git checkout 05c3d8fb321ed65e3db3a6a8b853019e86fb40a2`, then
`shasum -a 256` the same nine paths under `src/` and `include/`. The
three headers those units also need — `include/internal/Hacl_Bignum_Base.h`,
`include/Hacl_Krmllib.h`, `include/internal/Hacl_Krmllib.h` — were
already vendored for Ed25519 and were checked byte-identical to the same
commit when the P-256 files were added.

Still NOT vendored: Blake2, HPKE, MD5, SHA-1, SHA-3, the vectorized
variants, the EverCrypt agile layer, and every fixed-width bignum
(`Hacl_Bignum256*`, `Hacl_Bignum4096*`, `Hacl_Bignum32`).

## How it is wired in — Lean 4 tree (`formal/lean4/`)

- `ffi/hacl_ed25519.c` — Ed25519 and SHA-256 (`@[extern]` of
  `L4Factoidal/Crypto/Ed25519.lean`, `Crypto/SHA2Native.lean`).
- `ffi/hacl_p256.c` — P-256 ECDSA verification and public-key validity
  (`Crypto/P256Native.lean`). Two length checks and one pointer offset:
  the JWS `r || s` signature split.
- `ffi/hacl_rsa.c` — the RSA public operation only (`Crypto/RsaNative.lean`).
  No private operation, no padding logic; EMSA-PKCS1-v1_5 lives in
  `L4Factoidal/JOSE/Pkcs1.lean` in pure Lean, with theorems.
- `lakefile.lean`, `extern_lib libl4hacl` — compiles the six HACL\*
  translation units and the three shims into `libl4hacl.a`.
- `Wasm/build-wasm.sh` — the same six units and three shims, compiled for
  wasm32 by Emscripten. Crypto policy: every target links the same HACL\*.

## How it is wired in — F\* tree (`formal/fstar/`)

- `formal/fstar/experimental_ocaml_glue/hacl_stubs.c` — hand-written
  OCaml <-> C FFI (`CAMLprim`), hex-string boundary (same shape as
  `parquet_zstd_stubs.c`). No crypto logic — pure marshalling around
  the vendored `Hacl_*` calls.
- `formal/fstar/ocaml-output/fstar_hacl_crypto.ml` — the `external`
  declarations + thin hex wrappers that realise the F\* `assume val`s.
- `formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/`
  `286_vc_hacl_ed25519_sha256_stubs.sh` — the stub patch that rewrites
  the extracted `failwith` bodies to call the above.

## Updating

Re-run the curation: shallow-clone the pinned commit, copy the three
`src/*.c`, then keep only the transitive `#include` closure of headers.
Reverify with a driver that checks `Hacl_Hash_SHA2_hash_256("abc")`
begins `ba78...` and an Ed25519 sign/verify roundtrip returns true.
Never hand-edit the vendored `Hacl_*` C — it is extracted output.
