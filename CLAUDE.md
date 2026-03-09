# Factoidal — Verified RDF/SPARQL from F*

## What This Project Is

A formally verified RDF/SPARQL implementation. The **F\* specifications are the
product**. Executable code is obtained by **extraction**, not by hand-writing
Rust/JS/OCaml/anything that "mirrors" a spec.

## Iron Rules

1. **F\* is the source of truth.** All RDF/SPARQL logic lives in `.fst` files.
2. **Code is extracted, not hand-written.** Use `fstar.exe --codegen OCaml` (or
   KaRaMeL for C/WASM). Never vibe-code an implementation and claim it "mirrors"
   the spec.
3. **assume val = acknowledged gap.** Every `assume val` must have a stub in
   `ocaml-patches.sh` or the OCaml test harness. No silent holes.
4. **Parsers belong in F\*.** RDF serialization parsers (N-Triples, Turtle,
   N-Quads, TriG, RDF/XML, CSV/TSV results) should be implemented in F\* and
   extracted. The existing hand-written OCaml parsers (ntriples_parser.ml,
   turtle_parser.ml, etc.) are **temporary scaffolding** that must be replaced
   with F\*-extracted code. New parsers MUST be written in F\* first.
5. **SPARQL 1.1 is the target.** Never default to 1.0 manifests when 1.1 exists.
6. **Run the real W3C test files.** Read manifests, `.rq`, `.srx`, `.ttl` from
   disk. Do not construct synthetic queries that are "inspired by" W3C tests.
7. **No cobbling.** No hand-written JS/Rust/OCaml reimplementations of what F\*
   defines. If you need new functionality, add it in F\* first, then extract.
8. **RDF semantics are not optional.** The rdf-mt (model theory) tests verify
   fundamental RDF graph semantics — literal equivalence, datatype handling,
   language tag normalization, RDFS closure rules. These are core requirements,
   not "just inference." Dismissing them is wrong.

## Agent Work Strategy

When working on this project with Claude Code:

- **Use subagents aggressively for parallelism.** Launch multiple subagents for
  independent tasks (e.g., F\* verification + OCaml compilation + test running).
  Never get blocked waiting on one thing when other work can proceed.
- **Top-level Claude is the coordinator.** Don't get distracted doing deep work
  that a subagent could handle. Keep subagents productive and track their results.
- **Never block.** If one task is waiting, start another. Use background agents
  for long-running operations (F\* verification, test runs).

## Anti-Patterns — Do NOT Repeat These Mistakes

Previous Claude sessions made these errors. Read and internalize:

1. **Writing OCaml parsers instead of F\* parsers.** Do not write new `.ml`
   parser files. The existing ones (ntriples_parser.ml, turtle_parser.ml, etc.)
   are legacy debt, not a pattern to follow. New parsers go in `.fst` files.

2. **Dismissing rdf-mt tests as "needing an inference engine."** The rdf-mt
   test suite tests fundamental RDF semantics that RDF.Graph.Executable.fst
   must implement:
   - Language tag case-insensitive comparison (`@en-US` = `@en-us`)
   - Plain literal ↔ xsd:string equivalence
   - Datatype value equivalence (`"010"^^xsd:integer` = `"10"^^xsd:integer`)
   - RDFS closure rules (subClassOf, subPropertyOf, domain, range inference)
   These are bugs in the F\* spec, not out-of-scope features.

3. **Reporting misleading test scores.** "383/0 RDF" means nothing when it only
   tests hand-written OCaml parsers against syntax tests. The actual RDF
   implementation (RDF.Graph.Executable.fst) is not tested by parser tests.
   Always report what the numbers actually measure.

4. **Building parallel toolkits.** If the existing F\* code doesn't handle
   something, the fix is to extend the F\* spec — not to write OCaml code that
   does the same thing outside the verified boundary.

5. **Creating symlinks or hacks for version mismatches.** Do not create
   symlinks for z3 or other tool version issues. Fix the actual environment.

## Current State (Honest Assessment)

### F\* Specifications

```
formal/fstar/
  RDF.Graph.Executable.fst     638 lines, 0 admit, 0 assume val
  SPARQL11.Algebra.fst        3065 lines, 2 admit, 11 assume val
  SPARQL11.Parser.fst          F* SPARQL parser (in development)
  Makefile                     verify + extract-c targets
  build-ocaml.sh               F* -> OCaml -> js_of_ocaml pipeline
  ocaml-patches.sh             wires assume-val stubs
```

### Known Gaps in RDF.Graph.Executable.fst

RDF semantics implemented (all pass rdf-mt tests):

- **Language tag case-insensitivity**: DONE (`lang_tag_eq`)
- **Plain literal ↔ xsd:string equivalence**: DONE (`literal_value_eq`)
- **Datatype value equivalence**: DONE (`datatype_value_eq`, `normalize_integer_lexical`)
- **Cross-datatype equivalence**: DONE (xsd:integer ↔ xsd:decimal)
- **RDFS closure rules**: DONE (`rdfs_closure` with subPropertyOf, domain, range,
  subClassOf, container membership)

Remaining gap:
- **Simple entailment** (blank node as existential variable) — basic version done,
  full backtracking search implemented in test runner

### F\*-Extracted Parsers + Test Infrastructure

```
formal/fstar/ocaml-output/
  RDF_Graph_Executable.ml    F*-extracted RDF graph types + operations
  SPARQL11_Algebra.ml        F*-extracted SPARQL algebra + evaluator (patched for assume vals)
  SPARQL11_Parser.ml         F*-extracted SPARQL parser
  Parser_Combinators.ml      F*-extracted parser combinator foundation
  Parser_NTriples.ml         F*-extracted N-Triples parser (70/70 PERFECT)
  Parser_Turtle.ml           F*-extracted Turtle parser (313/313 PERFECT)
  Parser_NQuads.ml           F*-extracted N-Quads parser (87/87 PERFECT)
  Parser_TriG.ml             F*-extracted TriG parser (352/356)
  Parser_XML.ml              F*-extracted non-validating XML parser
  Parser_RDFXML.ml           F*-extracted RDF/XML parser (91/166)
  Parser_SRX.ml              F*-extracted SPARQL Results XML parser
  ntriples_parser.ml         hand-written N-Triples (LEGACY — only used by w3c_runner for utf8 helper)
  w3c_runner.ml              W3C manifest reader + test runner CLI (I/O glue)
  fstar_int_stubs.js         js_of_ocaml int stubs
```

### assume val inventory (SPARQL11.Algebra.fst)

| assume val | Purpose | Stub |
|-----------|---------|------|
| `regex_match` | SPARQL REGEX | OCaml `Str` in ocaml-patches.sh |
| `hash_md5` | MD5 hash | OCaml `Digest` in ocaml-patches.sh |
| `hash_sha1` | SHA-1 hash | OCaml `Digest` in ocaml-patches.sh |
| `hash_sha256` | SHA-256 hash | OCaml `Digest` in ocaml-patches.sh |
| `hash_sha384` | SHA-384 hash | OCaml `Digest` in ocaml-patches.sh |
| `hash_sha512` | SHA-512 hash | OCaml `Digest` in ocaml-patches.sh |
| `eval_expr_ebv` | forward decl (mutual recursion) | wired in ocaml-patches.sh |
| `eval_expr_fwd` | forward decl (mutual recursion) | wired in ocaml-patches.sh |
| `eval_exists_fwd` | forward decl (EXISTS) | wired in ocaml-patches.sh |
| `eval_subselect_fwd` | forward decl (subqueries) | wired in ocaml-patches.sh |
| `eval_property_path_fwd` | forward decl (property paths) | wired in ocaml-patches.sh |

### W3C Test Results (as of 2026-03-09)

**SPARQL 1.1 (252 pass, 155 fail, 205 skip, 19 unsupported)**

Tests the F\*-extracted SPARQL evaluator against W3C SPARQL 1.1 test suites.
Note: regression from 344 pass after switching to F\*-extracted SPARQL parser
(commit 837e4d1). The F\*-extracted parser doesn't yet handle all syntax
variants the hand-written parser did (e.g., OneOf, some BIND scoping).
Skips: 205 UPDATE operations (not in F\* spec).

**RDF 1.1 (952 pass, 79 fail — all F\*-extracted parsers)**

All RDF suites now use F\*-extracted parsers with strict validation:

| Suite | Pass | Fail | Total | Status |
|-------|------|------|-------|--------|
| rdf-n-triples | 70 | 0 | 70 | **PERFECT** |
| rdf-turtle | 313 | 0 | 313 | **PERFECT** |
| rdf-n-quads | 87 | 0 | 87 | **PERFECT** |
| rdf-trig | 352 | 4 | 356 | 98.9% |
| rdf-xml | 91 | 75 | 166 | 54.8% — needs RDF/XML parser improvements |
| rdf-mt | 39 | 0 | 39 | **PERFECT** |

The rdf-mt suite tests actual RDF graph semantics (literal value equivalence,
language tag case-insensitivity, RDFS closure rules). All 39 tests pass.

## What Was Removed (junk/do_not_use/)

Everything in `junk/do_not_use/` is **vibe-coded or derived from vibe-coded
artifacts**. Do not use it. Do not revive it.

## The Plan

### Architecture

```
F* formal spec (the product)
    |
    v
fstar.exe --codegen OCaml (extraction, proof-erased)
    |
    v
OCaml test runner (minimal I/O glue only)
    |-- reads W3C manifest files from disk (I/O)
    |-- calls F*-extracted parsers for .rq/.ttl/.nt/.nq/.trig/.rdf/.srx
    |-- calls F*-extracted evaluator
    |-- compares actual vs expected (using F*-extracted comparison)
    |-- emits pass/fail per test
    v
W3C SPARQL 1.1 + RDF 1.1 conformance results
```

### Phase 1 — SPARQL test infrastructure (DONE)

W3C test runner works. 344/631 SPARQL tests pass.

### Phase 2 — Fix RDF semantics in F\* (MOSTLY DONE)

1. **Language tag case-insensitive comparison** — DONE (`lang_tag_eq` in F\*)
2. **Plain literal ↔ xsd:string equivalence** — DONE (`literal_value_eq`)
3. **Datatype value space equivalence** — DONE (`datatype_value_eq`, `normalize_integer_lexical`)
4. **RDFS closure rules** — DONE (`rdfs_closure` with subPropertyOf, domain, range, subClassOf, container membership)
5. **Simple entailment** (blank node as existential variable) — TODO

Remaining: re-extract, wire into test runner, run rdf-mt tests.

### Phase 3 — F\* parsers (IN PROGRESS)

Replace hand-written OCaml parsers with F\*-extracted implementations.

**Parser architecture**: `Parser.Combinators.fst` provides the combinator
foundation (pchar, pstring, psat, pbind, pmap, palt, pmany, etc.). All parsers
are built on this. `Parser.XML.fst` is a **non-validating XML parser** — it
reads well-formed XML into a tree but does NO DTD processing, NO external entity
resolution, NO schema validation. Only predefined entities (&amp; &lt; &gt;
&quot; &apos;) and character references (&#123; &#x1A;). Namespace prefixes are
preserved as part of element/attribute names (namespace URI resolution is the
RDF/XML layer's job, not the XML parser's).

1. N-Triples parser in F\*
2. Turtle parser in F\*
3. N-Quads parser in F\*
4. TriG parser in F\*
5. RDF/XML parser in F\* (uses Parser.XML.fst — non-validating XML parser)
6. CSV/TSV results format parser in F\*
7. SRX (SPARQL Results XML) parser in F\*
8. SPARQL query parser in F\* (SPARQL11.Parser.fst started)

### Phase 4 — Close SPARQL gaps

Working from test failures, extend the F\* SPARQL spec.

### Phase 5 — Verified extraction pipeline

- Low\* rewrite for standalone C extraction via KaRaMeL
- CI: verify F\* → extract → test → sign

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

```bash
# Initialize opam (first time only)
opam init -y
# Create the F* switch:
opam switch create fstar ocaml-base-compiler.4.14.1
eval $(opam env --switch=fstar)
opam install fstar z3 js_of_ocaml js_of_ocaml-compiler zarith_stubs_js

# Activate (run in every new shell)
eval $(opam env --switch=fstar)
```

### Quick verification

```bash
eval $(opam env --switch=fstar)
cd formal/fstar

# Verify F* specs
make verify

# Extract + compile + test
./build-ocaml.sh

# Run W3C tests (w3c_runner is now built by build-ocaml.sh compile step)
cd ocaml-output
# Manual compilation if needed:
ocamlfind ocamlopt -package fstar.lib,str,zarith -linkpkg -w -8-14-26 \
  RDF_Graph_Executable.ml SPARQL11_Algebra.ml \
  Parser_Combinators.ml Parser_NTriples.ml Parser_Turtle.ml \
  Parser_XML.ml Parser_NQuads.ml Parser_TriG.ml \
  Parser_SRX.ml Parser_RDFXML.ml \
  ntriples_parser.ml sparql_parser.ml w3c_runner.ml -o w3c_runner
./w3c_runner                    # all SPARQL suites
./w3c_runner --rdf              # RDF parser suites
./w3c_runner --all              # both
./w3c_runner --list             # list suites
./w3c_runner bind functions     # specific suites
```

### Extraction notes

- `--lax` skips proof checking during extraction (faster; use `make verify` separately)
- `--codegen OCaml` erases proofs, ghost code, spec-only material
- Extracted `.ml` files use `FStar_*` runtime from `fstar.lib` opam package
- `assume val` declarations extract as `failwith "Not yet implemented"` — must be patched
- `noeq` types block KaRaMeL C extraction (OCaml extraction works fine)

### W3C Test Suites

```
tests/w3c/                          git submodule: github.com/w3c/rdf-tests
  rdf/rdf11/rdf-n-triples/         N-Triples syntax tests (70)
  rdf/rdf11/rdf-turtle/            Turtle syntax+eval tests (313)
  rdf/rdf11/rdf-n-quads/           N-Quads syntax tests (NOT YET SUPPORTED)
  rdf/rdf11/rdf-trig/              TriG syntax+eval tests (NOT YET SUPPORTED)
  rdf/rdf11/rdf-xml/               RDF/XML eval tests (NOT YET SUPPORTED)
  rdf/rdf11/rdf-mt/                Model theory / semantics (NOT YET SUPPORTED)
  sparql/sparql11/                 SPARQL 1.1 test suites (34 suites, 631 tests)
```

## Key Dependencies

- `fstar` — F\* compiler (opam, 2025.12.15)
- `z3` — SMT solver (required by F\*)
- `fstar.lib` — F\* OCaml runtime library (opam)
- `str` — OCaml regex library (for regex_match stub)
- `zarith` — arbitrary-precision integers (F\* extracts `Prims.int` as `Z.t`)
- `js_of_ocaml` — OCaml to JavaScript compiler (optional)
- `zarith_stubs_js` — bigint stubs for js_of_ocaml (optional)
- `libgmp-dev` — system package required by zarith (apt-get)

## Repository Structure

```
factoidal/
├── formal/fstar/              THE PRODUCT
│   ├── RDF.Graph.Executable.fst   RDF graph types + operations
│   ├── SPARQL11.Algebra.fst       SPARQL 1.1 algebra + evaluator
│   ├── SPARQL11.Parser.fst        SPARQL parser (in development)
│   ├── Makefile
│   ├── build-ocaml.sh
│   ├── ocaml-patches.sh
│   └── ocaml-output/          extracted + TEMPORARY test harness
├── tests/w3c/                 git submodule (W3C test files)
├── kgx/                       SPARQL CONSTRUCT queries (future)
├── docs/
│   ├── designissues/          architecture docs
│   └── skills/                operational knowledge
├── junk/do_not_use/           vibe-coded artifacts (DO NOT USE)
└── CLAUDE.md                  this file
```
