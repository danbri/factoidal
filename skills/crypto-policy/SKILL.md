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

### Self-hosting the `hacl-wasm` bytes (reproduction status, 2026-07-08)

The wasm crypto path uses HACL\*'s official WebAssembly build. Today we
vendor the **prebuilt** `hacl-wasm@1.4.0` `.wasm` (companion commit
`3c303a8`) — verified sha256-identical to the npm tarball. A spike to
rebuild those bytes ourselves via `krml -backend wasm` landed a recipe,
not a self-built binary:

- Byte-identical rebuild is **blocked on the pinned toolchain**.
  `hacl-wasm@1.4.0`'s own `INFO.txt` pins F\* `e617752`, KaRaMeL
  `2cf2974`, Vale `0.3.19`. This env has KaRaMeL `11bb8e1` + F\*
  `2025.12.15` (both newer); KaRaMeL's wasm codegen is not byte-stable
  across versions (proven: a `WasmSupport.wasm` built here is 1131 B vs
  upstream 1135 B, identical through offset 394 then divergent).
- The `krml -backend wasm` **pipeline works with our tools** end to end
  (emits `*.wasm` + `loader.js` + `shell.js` + `layouts.json`). The
  missing input is HACL\*'s crypto `.krml` (an F\* extraction output,
  not shipped upstream, needing a multi-hour verified build).
- Recipe + full write-up:
  [`third_party/hacl/wasm/reproduce-hacl-wasm.sh`](../../third_party/hacl/wasm/reproduce-hacl-wasm.sh),
  [`docs/designissues/2026-07-08-self-hosted-hacl-wasm.md`](../../docs/designissues/2026-07-08-self-hosted-hacl-wasm.md).
- Keep the vendored binary as the shipping artifact until a run with the
  pinned toolchain produces a self-built `.wasm` to swap in and repoint
  the npm-entry. Relates to #63 / #286.

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

## Lean 4 tree amendment (owner-approved 2026-08-22)

Owner decision, verbatim: "yes, approved re policy and browser
strategy (assuming we might choose to look around at other C to WASM
options, and noting that non-webplatform JS eg. Node/Deno is
important too). We'll need HACL* everywhere etc."

Two-tier rule for `formal/lean4/` (analysis:
`docs/designissues/2026-08-22-lean4-external-dependencies.md`):

1. **Hashes over public data** (RDFC-1.0 bnode hashing, the SPARQL
   §17.4.4 MD5/SHA builtins, VC `sha256_hex` of canonical N-Quads):
   a pure Lean implementation is PERMITTED — no secret is involved
   and there is no side channel to protect — provided it carries the
   FIPS 180-4 / RFC test vectors as build-time `#guard`s. This keeps
   the canonicalisation algorithm total and axiom-free end to end.
   Binding HACL*'s `Hacl_Hash_SHA2.c` via Lean FFI as well (for
   speed, and for bit-parity with the F* tree) is encouraged, never
   required. DONE for SHA-256 on 2026-09-02:
   `formal/lean4/L4Factoidal/Crypto/SHA2Native.lean` declares
   `@[extern "l4_hacl_sha256"] opaque sha256Hacl`, realised in
   `ffi/hacl_ed25519.c`. It is ADDITIONAL to the pure Lean `sha256`,
   which stays the specification and stays what every build-time
   `#guard` and every theorem evaluates — a `#guard` runs in the Lean
   interpreter, which cannot call an extern, so an
   `@[implemented_by]` on `sha256` would delete the FIPS 180-4
   build-time vectors. Consumers that want the fast one take a hasher
   PARAMETER (`Storage/BlockMerkle.lean`'s `Hasher`, instantiated by
   `pureHasher` in the library and `Harness.nativeHasher` at the
   executable edge). The two are compared on the FIPS vectors, the
   SHA-256 block/padding boundaries and a 1 MiB buffer by the
   `sha256 differential` section of `lake exe l4vc-probe`, which is a
   required step of `.github/workflows/verify-lean4.yml`.
2. **Signatures and key agreement (Ed25519 for VC Data Integrity and
   did:key; anything touching a secret): HACL* via Lean FFI ONLY**
   (`@[extern]` over an `opaque` declaration, compiled through lake's
   `extern_lib`). Never a hand-written Lean implementation. This is
   the FIRST member of the Lean tree's permitted crypto `extern`
   family; the second is `sha256Hacl` under item 1, added 2026-09-02
   for speed on public block bytes. Both must be labelled in
   `formal/lean4/PORT_NOTES.md`'s assumption report, exactly as rule
   #11 realisations are labelled in F*. Every member of the family is
   HACL* through `ffi/hacl_ed25519.c`; a NEW primitive here needs the
   same three things — a module-header trust statement, a shim with no
   arithmetic, and a run-time vector check in `l4vc-probe`.
3. **HACL* everywhere**: every Lean deployment target links the same
   HACL* — native via the C sources, browser AND non-web JS runtimes
   (Node, Deno) via HACL*'s official wasm build already vendored
   under `npm/factoidal/hacl-wasm/`. No target gets a different
   crypto implementation.

### Hash agility (owner, 2026-08-22)

Owner, verbatim: "wherever we use SHA-256 maybe we should prep the
next one, since it sooner or later will fall and we want to be
ready." Rule for both trees: no consumer calls a concrete hash
function directly. The Lean tree exposes `HashAlgorithm`
(`sha256 | sha384 | sha512`, with `sha3_256`/`shake256` as the
planned next entries) and `hashHex (alg)` dispatchers; RDFC-1.0
(whose spec already parameterises the hash, SHA-256 default, SHA-384
tested alternate), VC Data Integrity cryptosuites, and the SPARQL
hash builtins take the algorithm as a parameter. Adding the successor
is then one constructor + one dispatcher arm + its test vectors, not
a hunt through call sites.
