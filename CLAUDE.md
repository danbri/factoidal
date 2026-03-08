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
  ocaml-output/
    RDF_Graph_Executable.ml    genuinely F*-extracted OCaml
    SPARQL11_Algebra.ml        genuinely F*-extracted OCaml (patched for assume vals)
    example.ml                 hand-written OCaml demo using extracted modules
    w3c_tests.ml               hand-written OCaml test harness (synthetic, not file-based)
    ntriples_parser.ml         hand-written N-Triples parser (test infrastructure)
    turtle_parser.ml           hand-written Turtle parser (test infrastructure)
    srx_parser.ml              hand-written SPARQL Results XML parser (test infrastructure)
    sparql_parser.ml           hand-written SPARQL 1.1 query parser (test infrastructure)
    w3c_runner.ml              W3C manifest reader + test runner CLI (test infrastructure)
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
- `rdfcore11.fstar.txt`, `sparql11.fstar.txt` — historical textual specs (pre-`.fst`)

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

### Phase 1 — Run real W3C tests against extracted code (DONE)

All test infrastructure is written and working:

1. N-Triples parser (ntriples_parser.ml)
2. Turtle parser (turtle_parser.ml) — prefixes, base, collections, blank nodes, numerics
3. SPARQL 1.1 query parser (sparql_parser.ml) — full syntax coverage
4. SRX parser (srx_parser.ml) — SPARQL Results XML for expected results
5. W3C manifest reader + test runner CLI (w3c_runner.ml)
6. Runs ALL suites in `tests/w3c/sparql/sparql11/`

**First test run results: 198 pass, 209 fail, 205 skip, 19 unsupported**

Key passing suites: syntax-query (75/94), functions (52/75), bind (7/10),
project-expression (6/7), entailment (24/70).

Known failure categories (inputs for Phase 2):
- Hash functions: assume vals not yet stubbed (hash_md5, hash_sha*)
- EXISTS: eval_exists_fwd not wired
- Property paths: eval returns [] (stub implementation)
- Aggregates: partial support in F\* spec

### Phase 2 — Close gaps in F\* spec

Working from W3C test failures, extend the F\* specification:
- Fix remaining assume vals (hash stubs, eval_exists_fwd wiring)
- Add missing SPARQL 1.1 features identified by test failures
- Each fix: F\* first, re-extract, re-test

### Phase 3 — Verified extraction pipeline

- Low\* rewrite of core types for standalone C extraction via KaRaMeL
- EverParse-style verified parsers for N-Triples/Turtle
- CI: verify F\* -> extract -> test -> sign

## Setup

### First-time clone

```bash
git clone --recurse-submodules https://github.com/danbri/factoidal.git
cd factoidal

# If already cloned without --recurse-submodules:
git submodule update --init --recursive
```

The W3C test files live in `tests/w3c/` (submodule pointing to
`github.com/w3c/rdf-tests`). Without initialising the submodule, the test
runner will have no test data.

### System prerequisites

```bash
# Debian/Ubuntu
sudo apt-get install -y opam libgmp-dev pkg-config
```

### F\* toolchain (opam)

F\* and its OCaml dependencies are managed via opam. If not already installed:

```bash
# Initialize opam (first time only)
opam init -y
# Then create the F* switch:
opam switch create fstar ocaml-base-compiler.4.14.1
eval $(opam env --switch=fstar)
opam install fstar z3 js_of_ocaml js_of_ocaml-compiler zarith_stubs_js

# Activate the F* environment (run in every new shell)
eval $(opam env --switch=fstar)

# Tools available after activation:
#   fstar.exe    — F* compiler (2025.12.15)
#   krml         — KaRaMeL C extractor (if built from source)
#   z3           — SMT solver (required by F*)
#   ocamlfind    — OCaml package manager
```

### Verify everything is working

```bash
eval $(opam env --switch=fstar)
cd formal/fstar

# Check F* can verify the specs
make verify

# Check extraction + compilation works
./build-ocaml.sh
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

# Compile native OCaml binary (example)
cd ocaml-output
ocamlfind ocamlopt -package fstar.lib,str -linkpkg -w -8 \
  RDF_Graph_Executable.ml SPARQL11_Algebra.ml example.ml -o example

# Compile W3C test runner
cd ocaml-output
ocamlfind ocamlopt -package fstar.lib,str,zarith -linkpkg -w -8-26 \
  RDF_Graph_Executable.ml SPARQL11_Algebra.ml \
  ntriples_parser.ml turtle_parser.ml srx_parser.ml sparql_parser.ml \
  w3c_runner.ml -o w3c_runner

# Run W3C SPARQL 1.1 tests
./w3c_runner                    # all suites
./w3c_runner bind functions     # specific suites
./w3c_runner --list             # list available suites

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
- `zarith` — arbitrary-precision integers (F\* extracts `Prims.int` as `Z.t`)
- `js_of_ocaml` — OCaml to JavaScript compiler (optional, for browser demos)
- `zarith_stubs_js` — bigint stubs for js_of_ocaml (optional)
- `libgmp-dev` — system package required by zarith (apt-get)

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
