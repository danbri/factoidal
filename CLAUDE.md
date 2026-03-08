# Factoidal — Verified RDF/SPARQL from F*

## What This Project Is

A formally verified RDF/SPARQL implementation. The **F\* specifications are the
product**. Executable code is obtained by **extraction**, not by hand-writing
Rust/JS/anything that "mirrors" a spec.

## Iron Rules

1. **F\* is the source of truth.** All RDF/SPARQL logic lives in `.fst` files.
2. **Code is extracted, not hand-written.** Use `fstar.exe --codegen OCaml` (or
   KaRaMeL for C/WASM). Never vibe-code an implementation and claim it "mirrors"
   the spec.
3. **assume val = acknowledged gap.** Every `assume val` must have a stub in
   `ocaml-patches.sh` or the OCaml test harness. No silent holes.
4. **Parsers are test infrastructure, not the product.** Turtle/N-Triples/SPARQL
   query parsers are needed to run W3C tests. Write them in OCaml as part of the
   test runner. Mark them clearly as unverified I/O glue.
5. **SPARQL 1.1 is the target.** Never default to 1.0 manifests when 1.1 exists.
6. **Run the real W3C test files.** Read manifests, `.rq`, `.srx`, `.ttl` from
   disk. Do not construct synthetic queries that are "inspired by" W3C tests.
7. **No cobbling.** No hand-written JS/Rust reimplementations of what F\* defines.

## What Exists (Real)

```
formal/fstar/
  RDF.Graph.Executable.fst     610 lines, zero admit, zero assume val
  SPARQL11.Algebra.fst        2760 lines, 0 admit, 9 assume val (regex, hashes, fwd decls)
  Makefile                     verify + extract-c targets
  build-ocaml.sh               F* -> OCaml -> js_of_ocaml pipeline
  ocaml-patches.sh             wires assume-val stubs (regex, forward refs)
  rdfcore11.fstar.txt          historical textual spec
  sparql11.fstar.txt           historical textual spec
  ocaml-output/
    RDF_Graph_Executable.ml    genuinely F*-extracted OCaml
    SPARQL11_Algebra.ml        genuinely F*-extracted OCaml (patched for assume vals)
    example.ml                 hand-written OCaml demo using extracted modules
    w3c_tests.ml               hand-written OCaml test harness (synthetic, not file-based)
    fstar_int_stubs.js         js_of_ocaml int stubs
```

### assume val inventory (SPARQL11.Algebra.fst)

| assume val | Purpose | Stub |
|-----------|---------|------|
| `regex_match` | SPARQL REGEX — needs real regex engine | OCaml `Str` in ocaml-patches.sh |
| `hash_md5` | MD5 hash | needs OCaml `Digest` stub |
| `hash_sha1` | SHA-1 hash | needs OCaml stub |
| `hash_sha256` | SHA-256 hash | needs OCaml stub |
| `hash_sha384` | SHA-384 hash | needs OCaml stub |
| `hash_sha512` | SHA-512 hash | needs OCaml stub |
| `eval_expr_ebv` | forward decl (mutual recursion) | wired in ocaml-patches.sh |
| `eval_expr_fwd` | forward decl (mutual recursion) | wired in ocaml-patches.sh |
| `eval_exists_fwd` | forward decl (EXISTS) | needs wiring |

## What Was Removed (junk/do_not_use/)

Everything in `junk/do_not_use/` is **vibe-coded or derived from vibe-coded
artifacts**. It was written by Claude, not extracted from F\*. Do not use it.
Do not revive it. It exists only as a historical record of what went wrong.

- `CLAUDE.md.old` — previous CLAUDE.md with inflated scorecards
- `rdf-wasm/` — entire hand-written Rust crate (5,421 lines) + WASM bindings
- `ocaml-output-js/` — hand-written JS parsers and test runners
- `docs-wasm/` — WASM build artifacts and HTML demos
- `docs-fstar-extracted/` — js_of_ocaml output + HTML (rebuild from pipeline)
- `docs-history/` — stale architecture docs
- `c-output/` — KaRaMeL C extraction (legitimate but not standalone; needs Low\*)

## The Plan

### Architecture (as GPT correctly stated)

```
F* formal spec (the product)
    |
    v
fstar.exe --codegen OCaml (extraction, proof-erased)
    |
    v
OCaml test runner (unverified I/O glue)
    |-- reads W3C manifest .ttl files from disk
    |-- parses .rq query files
    |-- parses .srx/.ttl expected results
    |-- calls extracted evaluator
    |-- compares actual vs expected
    |-- emits pass/fail per test
    v
W3C SPARQL 1.1 conformance results
```

### Phase 1 — Run real W3C tests against extracted code

1. Write an OCaml Turtle parser (test infrastructure, clearly marked unverified)
2. Write an OCaml SPARQL query parser (test infrastructure)
3. Write a manifest reader that loads W3C test suites from `tests/w3c/`
4. Write an SRX (SPARQL Results XML) parser for expected results
5. Build a test runner: load graph, parse query, call extracted `eval_select_query`,
   compare results, report pass/fail
6. Target: run ALL of `tests/w3c/sparql/sparql11/` — no cherry-picking

### Phase 2 — Close gaps in F\* spec

Working from W3C test failures, extend the F\* specification:
- Fix remaining assume vals (hash stubs, eval_exists_fwd wiring)
- Add missing SPARQL 1.1 features identified by test failures
- Each fix: F\* first, re-extract, re-test

### Phase 3 — Verified extraction pipeline

- Low\* rewrite of core types for standalone C extraction via KaRaMeL
- EverParse-style verified parsers for N-Triples/Turtle
- CI: verify F\* -> extract -> test -> sign

## F\* Toolchain Notes

### Installation

F\* and dependencies are installed via opam:

```bash
# Activate the F* environment
eval $(opam env --switch=fstar)

# Tools available after activation:
#   fstar.exe    — F* compiler (2025.12.15)
#   krml         — KaRaMeL C extractor
#   z3           — SMT solver (required by F*)
#   ocamlfind    — OCaml package manager
```

### Key Commands

```bash
# Verify F* specs (typechecking + proof discharge via Z3)
cd formal/fstar && make verify

# Extract F* to OCaml
fstar.exe --lax --codegen OCaml --odir ocaml-output RDF.Graph.Executable.fst
fstar.exe --lax --codegen OCaml --odir ocaml-output SPARQL11.Algebra.fst

# Patch assume-val stubs
./ocaml-patches.sh ocaml-output/SPARQL11_Algebra.ml

# Compile native OCaml binary
cd ocaml-output
ocamlfind ocamlopt -package fstar.lib,str -linkpkg -w -8 \
  RDF_Graph_Executable.ml SPARQL11_Algebra.ml example.ml -o example

# Full pipeline (extract + patch + compile + test + js)
./build-ocaml.sh
```

### Extraction notes

- `--lax` skips proof checking during extraction (faster; use `make verify` separately)
- `--codegen OCaml` erases proofs, ghost code, spec-only material at extraction
- Extracted `.ml` files use `FStar_*` runtime modules from the `fstar.lib` opam package
- `assume val` declarations extract as `failwith "Not yet implemented: ..."` — must be patched
- `noeq` types in SPARQL module block KaRaMeL C extraction (OCaml extraction works fine)

### W3C Test Files

```
tests/w3c/                     git submodule: github.com/w3c/rdf-tests
  rdf/rdf11/rdf-n-triples/    N-Triples test suite
  rdf/rdf11/rdf-turtle/        Turtle test suite
  sparql/sparql11/             SPARQL 1.1 test suites (THE target)
  sparql/sparql10/             SPARQL 1.0 (historical, not primary target)
```

Manifests are Turtle files. Tests reference `.rq` (query), `.ttl` (data),
`.srx` (expected XML results) or `.ttl` (expected graph results).

## Key Dependencies

- `fstar` — F\* compiler (opam, 2025.12.15)
- `z3` — SMT solver (z3-4.8.5, z3-4.13.3)
- `fstar.lib` — F\* OCaml runtime library (opam)
- `str` — OCaml regex library (for regex_match stub)
- `js_of_ocaml` — OCaml to JavaScript compiler (optional, for browser demos)
- `zarith_stubs_js` — bigint stubs for js_of_ocaml (optional)

## Repository Structure

```
factoidal/
├── formal/fstar/              THE PRODUCT
│   ├── RDF.Graph.Executable.fst
│   ├── SPARQL11.Algebra.fst
│   ├── Makefile
│   ├── build-ocaml.sh
│   ├── ocaml-patches.sh
│   └── ocaml-output/          extracted + test harness
├── tests/w3c/                 git submodule (W3C test files)
├── kgx/                       SPARQL CONSTRUCT queries (future)
├── docs/
│   ├── designissues/          architecture docs
│   └── skills/                operational knowledge
├── junk/do_not_use/           vibe-coded artifacts (DO NOT USE)
└── CLAUDE.md                  this file
```
