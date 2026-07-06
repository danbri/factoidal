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
three units transitively require. No `.c` other than the three above.

## How it is wired in

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
