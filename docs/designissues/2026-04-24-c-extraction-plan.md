# C Extraction Plan — F* → C via KaRaMeL

Date: 2026-04-24
Status: plan / scoping; no pipeline stood up yet

## Why this matters

Factoidal's product is an F\* specification. Today we extract that spec to
OCaml and run native + JS + (experimental) Wasm via `js_of_ocaml` /
`wasm_of_ocaml`. A C extraction via **KaRaMeL** (`krml`) unlocks:

1. **Portability** — a single C-native binary with no OCaml runtime
   dependency, linkable into browsers (Emscripten/WASI), mobile, embedded,
   or standalone Unix.
2. **Performance ceiling** — OCaml extraction carries the GC + boxed-value
   overhead of `Prims.int` (zarith), `fstar.lib`, etc. C extraction targets
   fixed-width ints, arena allocation, no hidden GC pauses.
3. **Auditability** — C extraction output is a much smaller surface than
   the OCaml runtime stack. For a formally-verified RDF/SPARQL engine,
   shortening the unverified tail matters.
4. **Rule-#10 pressure valve** — patches (`ocaml-patches.sh`) don't
   translate to C. Every piece of OCaml-post-processing logic is
   effectively C-deadweight and must be moved into F\* before the C build
   works. This forces the codebase toward its own design rule.

## Current inventory of blockers

`grep -c "^noeq \|^assume val"` across `formal/fstar/*.fst` summarised by
module. Counts captured 2026-04-24:

| Module | `noeq` types | `assume val` | Notes |
|---|---:|---:|---|
| RDF.Graph.Executable | 10 | 0 | core — needs noeq reduction |
| SPARQL11.Algebra | 12 | 12 | hot path; most assume-vals are hash/uuid/regex stubs |
| SPARQL11.Parser | 2 | 3 | string ops |
| Parser.RDFXML | 2 | 2 | |
| Parser.Turtle | 4 | 0 | |
| Parser.TurtleScanner | 8 | 0 | |
| Parser.TriG | 1 | 0 | |
| Parser.NQuads | 1 | 0 | |
| Parser.IRI | 1 | 0 | |
| Parser.FastString | 0 | 6 | string-primitive stubs |
| **Parquet.Footer** | **0** | **3** | zstd decompress + I/O slicing |
| Parser.BallyhooCOTTAS | 8 | 17 | Parquet-backed RDF store |
| Parser.BallyhooHDT | 9 | 13 | HDT — shells out to `hdtSearch` |
| Parser.BallyhooHDTQ | 7 | 17 | HDT-quads variant |
| Parser.Ballyhoo | 4 | 0 | umbrella module |
| Parser.BallyhooBloom | 1 | 0 | |
| Tableau | 7 | 0 | OWL tableau reasoner |
| SPARQL11.Store | 3 | 0 | |
| SPARQL.HTTP | 1 | 2 | Unix sockets |

`noeq` types block KaRaMeL's structural-equality requirement. `assume
val` declarations need a C implementation for the target; today they
extract as `failwith "Not yet implemented"` in OCaml and are patched
in via `ocaml-patches.sh`.

## Why Parquet currently needs OCaml

User's specific question: why is `Parquet.Footer` OCaml-locked today?

**Short answer:** it's not the F\* spec that's OCaml-locked — it's the
build pipeline. `Parquet.Footer.fst` itself has 3 `assume val`s
(`parquet_read_tail_hex`, `parquet_read_range_hex`,
`parquet_zstd_decompress_hex`) and **zero `noeq` types**. The F\* source
is KaRaMeL-viable.

What ties it to OCaml today is the **stub wiring**:

1. `formal/fstar/experimental_ocaml_glue/parquet_zstd_stubs.c` uses
   OCaml's `CAMLprim`/`caml_alloc_string` API to produce OCaml `value`s
   from a libzstd decompression. This is OCaml-FFI glue, not
   OCaml-native code — libzstd itself is pure C.
2. `ocaml-patches.sh` (applied by `build-ocaml.sh` step 1) rewrites the
   extracted `Parquet_Footer.ml` to replace the `failwith` stubs with
   `external caml_parquet_zstd_decompress_hex`. Patches don't apply to
   a C extraction.
3. In the JS build, `parquet_zstd_stubs.js` + vendored
   `vendor/fzstd.umd.js` replace the same primitives on top of the
   js\_of\_ocaml runtime.

**Under C extraction** (via KaRaMeL), the migration path is actually
simpler than for most modules, because libzstd is already C:

- Drop the `CAMLprim` wrapper. Replace with a plain C function that takes
  `const char *hex, size_t hex_len, size_t expected_size` and returns
  a `bool` + `uint8_t *` output buffer (KaRaMeL's `FStar_Bytes` or a
  handwritten `decode_result` struct).
- Link `-lzstd` directly — no OCaml-runtime mediation.
- The I/O primitives (`parquet_read_tail_hex`,
  `parquet_read_range_hex`) today read from disk via OCaml stdlib;
  under C they should be POSIX `fopen`/`pread` or `mmap`, with a
  matching KaRaMeL-compatible C stub.

So: **Parquet is among the *easiest* modules to port to C**, once the
overall KaRaMeL pipeline is set up. What binds it to OCaml today is the
FFI shape of the existing stub, not any fundamental F\* design choice.

The COTTAS/Parquet RDF-store module (`Parser.BallyhooCOTTAS.fst`) is a
different story — 25 stubs + 8 `noeq` types + its HDT sibling shells out
to an external binary. That layer is genuinely OCaml-shaped today.

## Phased plan

### Phase 0 — Prerequisites (no code yet)

- [ ] Stand up KaRaMeL in CI: `opam install karamel` + a hello-world
      `.fst` → `.c` + `.h` + `clang` link.
- [ ] Document the KaRaMeL installation in `CLAUDE.md` alongside the
      existing F\* / z3 / opam notes.
- [ ] Spike: try extracting `Parser.IRI.fst` (smallest self-contained
      module, 1 noeq + 1 assume val) end-to-end to validate the pipeline.

### Phase 1 — Eliminate noeq types where safe

The `noeq` qualifier in F\* disables structural equality — usually
because a type contains a function, a proof-irrelevant ghost, or an
abstract type. KaRaMeL can handle some of these via alternative
strategies but not all.

- [ ] Audit every `noeq type` in the table above.
- [ ] For each: can it be made `type ... = { ... }` without noeq? (If
      no function-in-struct / no abstract-type-in-struct, usually yes.)
- [ ] For those that need to stay noeq: document *why* in a comment and
      consider whether KaRaMeL's `-fno-eq` flag covers the case.

Expected outcome: ≥50% of `noeq` types become plain types, unblocking
most of `RDF.Graph.Executable`, `SPARQL11.Algebra`, the parser family.

### Phase 2 — Consolidate patches back into F\*

Rule #10 already forbids semantic logic in patches. Audit confirms that
most of `ocaml-patches.sh` is stub-wiring (extension functions + FFI
bindings). But the patch set has grown over time and some edge-case
normalisation logic may have leaked in.

- [ ] Walk `minimal_regrettable_glue_code_each_with_an_open_issue/`.
      Classify each patch as (a) pure stub-wiring → port to C as a
      `.c` stub file, (b) I/O glue → port to POSIX, (c) suspect
      semantic logic → file a GitHub issue, move to F\*.
- [ ] For (a) and (b), author parallel `c-patches/` directory with the
      C-side equivalents.
- [ ] Kill the "known violations" called out in CLAUDE.md rule #10
      (blank-node-as-existential rewriting, #53) by putting that
      logic in F\*.

### Phase 3 — Replace runtime dependencies

OCaml extraction gets a lot of runtime services for free (zarith, sha,
digestif, Unix, Str). C extraction needs equivalents.

| OCaml dep | C equivalent | Effort |
|---|---|---|
| `zarith` (Prims.int) | GMP via `mpz_t` OR compile-time switch to int64 | M |
| `sha` / `digestif` | OpenSSL EVP or mbedTLS or hand-rolled (we have `Fstar_pure_hashes.ml` pure F\* already — reuse!) | S |
| `Str` regex | PCRE2 or `re2` or a pure-F\* regex engine (some shape exists in `SPARQL11.Algebra.fst` regex_* stubs) | M |
| `Unix` | POSIX direct | S |
| `libzstd` | already C-native; link directly | XS |

The existing `fstar_pure_hashes.ml` (MD5/SHA-1/SHA-256/SHA-384/SHA-512
in pure F\*) is a quiet win — it means one runtime dep *already*
disappears under C.

### Phase 4 — Build the first C binary (subset)

Start with the minimal SPARQL engine: RDF parsing + BGP matching, no
Parquet/COTTAS/HDT, no regex, no hashes.

- [ ] Build-script variant `build-c.sh` that runs KaRaMeL, compiles the
      C, links against the C-stub patches, produces `bin/*/factoidal-c`.
- [ ] Match a subset of the W3C tests (everything that doesn't need
      regex / hash / federated / Parquet) against that binary.
- [ ] Publish the numbers: pass/fail parity with the OCaml binary is
      the acceptance gate.

### Phase 5 — Full C binary

Parquet layer (per discussion above), HDT/COTTAS if we still need them,
federated SERVICE via libcurl, …

### Phase 6 — C → Wasm

Once we have a clean C build, Emscripten can produce a `.wasm`
unaffected by the `js_of_ocaml`-specific runtime-stub tangle.

## Acceptance criteria for "C extraction works"

1. `make c-extract` produces `.c` + `.h` for every module listed in the
   OCaml pipeline.
2. `make c-compile` produces `bin/*/factoidal-c` that starts.
3. `./bin/*/factoidal-c --version` returns the git sha, matching the
   OCaml binary.
4. The subset W3C suite (non-regex, non-hash, non-Parquet, non-federated)
   passes at **parity** with the OCaml binary.
5. `make all` builds OCaml, C, JS, and Wasm in one CI job, each with
   its own artifact under `bin/`/`docs/fstar-extracted/`.

## Open questions

- Is the Parquet/COTTAS store layer something we'll *keep* long-term,
  or is it an interim while we prototype? If interim, we don't need to
  port its 25+8 stubs to C.
- OWL tableau reasoner (`Tableau.fst`, 7 noeq) — same question.
- Does KaRaMeL handle our `assume val` style (where the OCaml side is
  patched) cleanly, or do we need to restructure them as `external`
  declarations that both OCaml and C can consume?
- Do we want the C binary to be bit-exact with the OCaml binary (same
  bnode labels, same iteration order), or is "semantically equivalent
  answers" enough?

## Next action

Start with Phase 0's KaRaMeL + `Parser.IRI.fst` spike. One commit, one
binary output, validates whether the pipeline works at all before
committing to the Phase 1 noeq audit.
