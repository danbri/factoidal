---
name: crypto-policy
description: The project's cryptography sourcing policy — never write our own crypto primitives; adopt HACL* (the F*/Low*-verified library Mozilla ships inside NSS) to realize the hash/signature assume vals, in a fixed adoption order with a hard wasm compatibility gate. Use when touching any hash/signature/UUID assume val, when implementing VC Data Integrity proofs, when a wasm build crashes inside a digest function, or when someone proposes adding a crypto dependency.
---

# Crypto policy: HACL*, never hand-rolled

Owner directives (2026-07-04/05): "search for prior mozilla work we
can import. Dont roll our own crypto!" and, on issue #63's
disposition, "pursue HACL*". This skill is the durable record of
both.

## Why HACL*

HACL* is the verified crypto library written in F*/Low* (proofs of
memory safety, functional correctness against RFC specs, and
secret-independence) whose extracted C code Mozilla ships inside NSS.
For a project whose whole premise is "F* specs, extracted code,
correctness proven not asserted", it is the only crypto source that
matches our own standard — and it is literally written in our
language.

## Current state (2026-07-05) — HACL* is NOT yet in use

Every crypto-adjacent function is an `assume val` under iron rule #3,
tracked by issue #63, realized by
`formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/63_regex_hash_uuid_stubs.sh`
using the stock OCaml `sha` / `digestif` opam packages:

- `RDF.Canonical.fst`: `hash_sha256`, `hash_sha384` (RDFC-1.0).
- `SPARQL11.Algebra.fst`: `hash_md5`, `hash_sha1`, `hash_sha256`,
  `hash_sha384`, `hash_sha512` (SPARQL 1.1 hash builtins).
- UUID generation (same patch).

VC Data Model stage 1 (2026-07-05) deliberately contains zero
signature/hash code; Data Integrity proofs (eddsa-rdfc-2022 etc.) are
the stage that forces real signature crypto — that stage MUST arrive
via HACL*, not a new opam dependency picked ad hoc.

## Adoption order (from the VC program plan, do not reorder silently)

1. **`hacl-star` opam bindings** — cleanest: F*-verified code behind
   an OCaml API; realizes the existing assume vals with a one-line
   patch change.
2. **Vendored HACL*-extracted C stubs** — if the opam package's
   footprint or build friction is prohibitive, vendor just the
   extracted C for the primitives we use (SHA-2 family first),
   with provenance + version recorded in `third_party/`.
3. **NSS FFI — last resort only** (heavyweight dependency, packaging
   pain), kept on the list because it is the Mozilla-shipped binary
   form of the same verified code.

Encoding layers (multibase, multihash, base58/base64url) are NOT
crypto — implement those in pure F* like any other codec.

## The wasm gate (hard requirement)

Every candidate realisation must pass the wasm_of_ocaml build and the
browser/wasm test suites before landing. History: a C-backed digestif
previously crashed under wasm (`wasm_stub_shims.py` still carries
identity shims for `caml_digestif_*` — SPARQL hash-builtin tests
crash on the wasm runtime today, a known gap noted in that script's
docstring). Candidate wasm paths, in preference order: HACL*'s own
official WebAssembly build (the `hacl-wasm` artifacts) wired in at
the npm-entry layer; or a pure-OCaml fallback digest for the wasm
target only, clearly labelled as the non-HACL* exception with its own
issue. A realisation that only works native is not done.

## Rules of engagement

- Never implement a primitive (digest, curve, signature, RNG) in F*
  or OCaml ourselves — not even "just for tests" (iron rule cousin:
  test-only crypto becomes production crypto within a month).
- Never add a new crypto opam/npm dependency without updating this
  skill and issue #63 in the same commit.
- Any new crypto assume val follows iron rule #3 (stub patch +
  open issue) AND names this skill in its patch header.
- When HACL* lands for a primitive, delete the corresponding stub
  from `63_regex_hash_uuid_stubs.sh` in the same commit, and record
  before/after wasm suite results in the PR.

## Pointers

- Issue #63 — the tracker for all regex/hash/UUID assume vals
  (regex stays out of scope for HACL*; it is a host-engine call-out,
  not crypto).
- `docs/designissues/2026-07-05-vc-program-plan.md` — the VC stages
  that force signature crypto, and where the adoption order above
  was first recorded.
- `formal/fstar/ocaml-output/wasm_stub_shims.py` — the current wasm
  digest gap, in its own words.
