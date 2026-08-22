# Lean 4 port: the external-dependency surface, and what it costs

Owner question (2026-08-22): RDF Canonicalisation and Verifiable
Credentials will be important soon; they carry external dependencies
(HACL\* etc.). What must we do there? What other external
dependencies does the F\* tree have, and are they available in Lean?

Method: every `assume val` in `formal/fstar/*.fst` (measured
2026-08-22: 88 declarations across 18 modules), classified by what the
host supplies, plus the build-level dependencies that are not visible
as `assume val` at all (OCaml runtime, js_of_ocaml, zarith, C stubs).

## 1. The inventory, classified

| Class | F\* modules (count) | What the host supplies today | Lean 4 answer |
|---|---|---|---|
| **On-disk storage** | Parser.BallyhooCOTTAS (13), RDF.CottasStore.\* (39 across 7 modules), RDF.Store.\* (11), Parquet.Footer (3), SPARQL.Eval.TimeBudget (1: `now_ms`) | file I/O, mmap, zstd (C), page cache, wall clock | **Deferred by owner decision** ("save SPARQL on disk storage and indices until later"). When the time comes: `IO`-typed file access in Lean; zstd via C FFI (`@[extern]` + lake `extern_lib`) or a pure port of the frame decoder. None of it touches the semantics. |
| **Cryptographic hashes** | RDF.Canonical (2: `hash_sha256`, `hash_sha384`), VC.DataIntegrity (1: `hash_sha256_hex`), SPARQL11.Algebra (5: md5/sha1/sha256/sha384/sha512 builtins §17.4.4) | HACL\* C (native), HACL\* wasm (Node/browser) | **Two-tier, per `skills/crypto-policy`** ("never roll our own crypto"): (a) SHA-2 for RDFC-1.0 and the SPARQL builtins operates on PUBLIC data with no secret and no side-channel concern — a pure Lean implementation proved against the FIPS 180-4 test vectors (`#guard`) is acceptable and keeps the canonicalisation algorithm total and axiom-free end to end; (b) for consistency with the F\* tree (and speed), ALSO bind HACL\*'s `Hacl_Hash_SHA2.c` via Lean's C FFI and prove nothing about it — it is F\*-verified upstream. MD5/SHA-1 exist only for the SPARQL builtins; pure Lean ports are small. |
| **Signatures (VC Data Integrity, eddsa-rdfc-2022; did:key)** | VC.DataIntegrity (3: `ed25519_secret_to_public`, `ed25519_sign`, `ed25519_verify`) | HACL\* Ed25519 C / wasm | **FFI to HACL\* only** — Ed25519 involves secrets; a hand-written Lean implementation would violate crypto-policy. Lean's `@[extern "hacl_ed25519_verify"]` over an `opaque` declaration is the exact analogue of the F\* `assume val` + `experimental_ocaml_glue/hacl_stubs.c`; the trust story is unchanged (HACL\* is itself F\*/Low\*-verified). For the BROWSER, HACL\*'s official wasm build is already vendored (`npm/factoidal/hacl-wasm/`, `skills/node-crypto-haclstar-vc-wasm-build`). This is the ONE place the Lean tree would carry an `opaque`/`extern` — it must be labelled as such in the assumption report, exactly like today's rule-#11 realisations. |
| **Unicode case mapping** | SPARQL11.Algebra (2: `string_uppercase_unicode`, `string_lowercase_unicode`) | OCaml `uucp` | Lean core `String.toUpper`/`toLower` (full Unicode via `Char.toUpper`? — core's `Char.toUpper` is ASCII-only; full Unicode case mapping needs a table). Pure: port the needed UnicodeData case-mapping table (or depend on a Lean Unicode library if one matures). The W3C SPARQL tests that exercise UCASE/LCASE are ASCII + a few Latin-1 cases — measure before sizing the table. |
| **Regex** | none — already pure F\* (`Regex.Syntax/Derivative/Exec/XSDPattern`; the `regex_match` assume val was retired) | — | Port as-is (Brzozowski derivatives are a textbook Lean exercise; the F\* proofs about them are candidates for native re-proof). |
| **Clock / randomness** | SPARQL11.Algebra (1: `fx_current_datetime` for NOW()); RAND/UUID/BNODE are already seeded-deterministic in F\* | OCaml `Unix.time` | Parameter: the evaluator takes a `now : String` (xsd:dateTime lexical) argument; `main` reads the clock once in `IO`. No assumption needed. |
| **Federation / host call-outs** | SPARQL11.Algebra (2: `service_endpoint_lookup`, `extension_function_call`); JSONLD.Loader (1: `jsonld_load_document` remote context fetch) | hashtable registries filled by the runner; HTTP (native `--endpoint`, wrap+ sources) | Parameters: an endpoint→graph map and an extension-function map passed into `eval`; a document-loader function passed into JSON-LD expansion (the vendored context cache `third_party/jsonld-context-cache/` becomes the default pure loader). Live HTTP is an `IO` program at the edge. |
| **SMT at runtime** | Tableau.CountingOracle (1: `z3_check_sat`) — the Farkas-certificate class-size oracle shells out to z3 | z3 binary | No Lean equivalent at RUNTIME (Lean's `omega`/`decide` are proof-time tactics). Options: (a) keep it as an `IO` call-out to z3 (honest, typed); (b) port a small exact-rational simplex/ILP for the bounded instances the oracle needs — the F\* tree already has exact-rational arithmetic. Deferred with the tableau track (#448-adjacent). |
| **F\* stdlib quirk** | Parser.FastString.CharBoundary (1: `unsafe_char_of_d7ff`) | a workaround for an `FStar.Char` bound bug | Does not arise: Lean `Char` admits U+D7FF natively. |
| **SHACL target select** | SHACL.Validation (1: `eval_sparql_target_select`) | a forward reference into the SPARQL evaluator (module-structure artifact) | Does not arise in Lean (mutual imports are not needed; order the modules). |
| **Property-path forward-ref** | SPARQL11.Algebra (1: `eval_property_path_fwd`) | same class | Does not arise. |

Net: of 88, **~67 are storage (deferred)**, **11 dissolve by
parameterisation or do not arise**, **8 are hashes** (pure Lean +
optional FFI), **3 are Ed25519** (FFI to HACL\*, the single principled
`extern`), **1 is runtime SMT** (deferred with the tableau).

## 2. Dependencies the `assume val` count does not show

| Dependency | Role in the F\* tree | Lean 4 status |
|---|---|---|
| OCaml toolchain + `zarith` (GMP) | extraction target; `Prims.int` → `Z.t` | Not needed: Lean compiles to C; `Nat`/`Int` are arbitrary-precision natively (GMP-backed in the runtime). |
| `js_of_ocaml` / `wasm_of_ocaml` | the npm package, the hub's live cells, the browser demos | **The largest real gap.** Lean has NO JavaScript backend. Lean → C → **wasm via Emscripten** is feasible (the `lean4web` project runs the Lean compiler itself in the browser that way) but is not turnkey: the Lean runtime (GMP-dependent by default; there is an `LEAN_SMALL_ALLOCATOR`/no-GMP configuration) and its allocator must be cross-compiled. Plan: a Lean `main` exposing a JSON ABI (the same `factoidalNpmEntry` shape) compiled to wasm; accept that the Lean artifact will be larger and slower to start than js_of_ocaml's. Until that exists, the hub keeps running the F\* bundles. |
| KaRaMeL (F\* → C) | the C build track, the delta-log demo | Replaced outright: Lean's native path IS C. |
| HACL\* C + wasm | crypto (above) | Reused as-is via FFI / the vendored wasm. |
| zstd (C) | COTTAS/Parquet pages | Deferred with storage. |
| `uucp` | Unicode tables | Pure port of the needed subset (above). |
| OCaml `Str`/host regex | retired already | — |
| Node/Playwright/11ty | hub + tests infrastructure | Unchanged; the Lean W3C harness (#466 rung 3) is a native Lean executable reading the same manifest files. |

## 3. What RDFC-1.0 and VC specifically need from the Lean port

Dependency order, all pure except the marked FFI:

1. N-Quads parse/serialise (in flight, #466) → 2. the RDFC-1.0
   algorithm itself (`RDF.Canonical.fst` is pure F\* apart from the two
   hash `assume val`s; hash-first-degree-quads / hash-n-degree-quads /
   the issuer and the bnode permutation search port directly; the
   permutation search is where a Lean proof of termination is more
   pleasant than F\*'s fuel) → 3. **SHA-256 in pure Lean** with the
   FIPS 180-4 vectors as `#guard`s → 4. RDFC conformance against the
   W3C rdf-canon suite through the Lean harness (the F\* tree is at
   full pass there; that is the bar) → 5. JSON-LD expansion +
   toRdf for VC documents (pure; large) → 6. VC Data Integrity proof
   creation/verification = RDFC + SHA-256 + **Ed25519 via HACL\* FFI**
   (+ multibase/multicodec/base58btc for did:key, pure).

The Lean tree's assumption report would then read: "zero `sorry`,
zero `axiom`; one `extern` family (HACL\* Ed25519, F\*-verified
upstream), labelled" — strictly better than the F\* tree's ~88.

## 4. Decisions — APPROVED by owner 2026-08-22

Owner, verbatim: "yes, approved re policy and browser strategy
(assuming we might choose to look around at other C to WASM options,
and noting that non-webplatform JS eg. Node/Deno is important too).
We'll need HACL* everywhere etc."

- Two-tier hash/signature policy: recorded as the Lean 4 amendment in
  `skills/crypto-policy/SKILL.md`.
- Runtime strategy: Lean → C → wasm. Emscripten is the first
  candidate, NOT a commitment — evaluate alternatives before building
  (WASI via `wasi-sdk`/`clang --target=wasm32-wasi`, which runs
  natively in Node ≥ 20 and Deno through their WASI support and needs
  no Emscripten JS glue; Zig's `zig cc` as a cross-compiler for the
  Lean runtime). Selection criteria: startup time, artifact size,
  GMP-free runtime build, and ONE artifact serving browser + Node +
  Deno. The F\* bundles remain the hub's engine until the Lean
  artifact passes the same hub node tests and browser sweep.
- HACL\* on every target: C sources linked natively; the vendored
  official wasm build for browser, Node, and Deno.
