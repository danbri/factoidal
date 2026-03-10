# Factoidal — Verified RDF/SPARQL from F*

## :warning: F* Comment Syntax — DANGER :warning:

**F\* comments `(* ... *)` support NESTING.** Any `*)` inside a comment
prematurely closes it, and any `(*` opens a new nesting level. This means
constructs containing `*)` will **silently corrupt the rest of your file**
when placed inside comments.

**This WILL break:**
```fstar
(* ARQ algebra example
   construct(*)
*)
```
The `*)` inside `construct(*)` closes the comment. Everything after it becomes
code. F\* then reports a syntax error **hundreds of lines later**, making
debugging extremely difficult.

**Safe alternatives:**
- Reword to avoid parens-star: `(* COUNT-star special case *)`
- Use `//` line comments (F\* supports them): `// COUNT(*) special case`
- Escape or rephrase: `(* SELECT vars-or-star ... *)`

**Rule: Never put `*)` or `(*` inside an F\* block comment.** Grep your `.fst`
files for these sequences if you get mysterious syntax errors far from the
actual cause.

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
   N-Quads, TriG, RDF/XML, CSV/TSV results) are implemented in F\* and
   extracted. All hand-written OCaml parsers have been removed. New parsers
   MUST be written in F\* first.
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
   parser files. All hand-written OCaml parsers have been deleted. There are
   NO OCaml parser files to use as a pattern. New parsers go in `.fst` files.

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

6. **Promoted type blindness.** When `eval_expr` evaluates a variable bound
   to a numeric literal, it returns `ER_Num`/`ER_Dec`/`ER_Dbl`/`ER_Bool` —
   NOT `ER_Term(T_Literal l)`. Any function that only pattern-matches on
   `ER_Term(T_Literal l)` will silently fail on promoted values. This
   has caused bugs in: `fn_datatype`, `fn_isLiteral`, `fn_lang`,
   `er_string_info`, `eval_concat`. **Rule: every function that handles
   `ER_Term(T_Literal l)` must also handle `ER_Num`, `ER_Dec`, `ER_Dbl`,
   and `ER_Bool` where semantically appropriate.**

7. **Parser/evaluator AST mismatch.** The SPARQL parser may emit different
   AST nodes than the evaluator expects. Example: `COUNT(*)` is parsed as
   `E_Aggregate(Agg_Count, _, E_BoolLit true)` but the evaluator checked
   for `E_Var "*"`. **Rule: when adding evaluator logic for a new construct,
   check what the parser actually emits** (grep SPARQL11_Parser.ml).

8. **parse_to_scaled before parse_double_to_scaled.** `parse_to_scaled`
   treats E-notation characters as fractional digits: `"1.0E2"` parses as
   `(1000, 3)` = 1.0 instead of 100. **Rule: always try
   `parse_double_to_scaled` first** when the input might contain
   E-notation (doubles). `parse_double_to_scaled` falls through to
   `parse_to_scaled` for non-E strings, so it's safe as the default.

9. **Recursive base case kills metadata.** `eval_concat` used
   `er_string ""` (plain xsd:string, no lang tag) as its base case. When
   folding right-to-left, this stripped lang tags from the last element,
   which cascaded up. **Rule: for recursive string functions, handle the
   single-element case explicitly** to preserve language tags and datatypes.

10. **OCaml Str regex: bytes not codepoints.** OCaml's `Str` module
    operates on bytes, not Unicode codepoints. `[^a-z0-9]` matches
    individual bytes of UTF-8 multi-byte characters. Also: referencing
    an unmatched group (`\2` when group 2 didn't participate) raises
    `Not_found`. Both limit REPLACE() conformance. A Unicode-aware regex
    library (Pcre, Re) would fix this but adds a dependency.

11. **`build-ocaml.sh compile` does NOT apply `ocaml-patches.sh`.**
    Only `build-ocaml.sh extract` runs the patches. After a fresh
    extraction, you must either use `extract` or manually run
    `./ocaml-patches.sh ocaml-output/SPARQL11_Algebra.ml`. Forgetting
    this silently regresses all `assume val` stubs to `failwith`.

## Current State (Honest Assessment)

### F\* Specifications

```
formal/fstar/
  RDF.Graph.Executable.fst     638 lines, 0 admit, 0 assume val
  SPARQL11.Algebra.fst        3658 lines, 5 admit, 14 assume val
  SPARQL11.Parser.fst          F* SPARQL parser (in development)
  Makefile                     verify + extract-c targets
  build-ocaml.sh               F* -> OCaml -> js_of_ocaml pipeline
  ocaml-patches.sh             wires assume-val stubs
```

### Known Gaps in RDF.Graph.Executable.fst

The F\* RDF graph spec uses **syntactic equality only**. It lacks:

- **Language tag case-insensitivity**: `literal_eq` compares `lang_tag` with `=`
  (string equality). Per RDF 1.1, `@en-US` and `@en-us` denote the same value.
- **Plain literal ↔ xsd:string equivalence**: Per RDF 1.1, `"foo"` (plain) and
  `"foo"^^xsd:string` are the same value. The spec treats them as distinct.
- **Datatype value equivalence**: `"010"^^xsd:integer` and `"10"^^xsd:integer`
  denote the same value. The spec compares lexical forms as strings.
- **RDFS closure rules**: No subClassOf/subPropertyOf inference, no domain/range
  type inference, no container membership property axioms.

These are not exotic features — they are what the W3C rdf-mt test suite tests.

### OCaml Output (extracted + test glue)

```
formal/fstar/ocaml-output/
  RDF_Graph_Executable.ml    F*-extracted OCaml
  SPARQL11_Algebra.ml        F*-extracted OCaml (patched for assume vals)
  SPARQL11_Parser.ml         F*-extracted SPARQL parser
  Parser_Combinators.ml      F*-extracted parser combinators
  Parser_NTriples.ml         F*-extracted N-Triples parser
  Parser_Turtle.ml           F*-extracted Turtle parser
  Parser_NQuads.ml           F*-extracted N-Quads parser
  Parser_TriG.ml             F*-extracted TriG parser
  Parser_XML.ml              F*-extracted XML parser
  Parser_RDFXML.ml           F*-extracted RDF/XML parser
  Parser_SRX.ml              F*-extracted SRX (SPARQL Results XML) parser
  Parser_CSVResults.ml       F*-extracted CSV/TSV results parser
  w3c_runner.ml              W3C manifest reader + test runner CLI (I/O glue)
  fstar_int_stubs.js         js_of_ocaml int stubs
```

Hand-coded parsers have been deleted. Legacy copies remain in `junk/do_not_use/hand_coded_parsers/` as a warning.

### assume val inventory (SPARQL11.Algebra.fst)

| assume val | Purpose | Stub |
|-----------|---------|------|
| `regex_match` | SPARQL REGEX | OCaml `Str` in ocaml-patches.sh |
| `regex_replace` | SPARQL REPLACE | OCaml `Str` in ocaml-patches.sh (forward ref) |
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

### W3C Test Results (as of 2026-03-10)

**SPARQL 1.1 (303 pass, 105 fail, 205 skip, 18 unsupported)**

F\*-extracted SPARQL parser + evaluator now run. Key suite results:
aggregates 38/44, functions 71/75, bind 9/10, bindings 10/11,
exists 5/6, grouping 4/6, negation 19/20, project-expression 7/10,
property-path 21/25, service 5/5, subquery 10/12.
Skips: 205 UPDATE operations (not in F\* spec).
Unsupported: 18 (JSON/CSV/TSV/Turtle result formats not yet implemented).

**RDF 1.1 (644 pass, 387 fail)**

Tests F\*-extracted parsers against all RDF 1.1 suites: N-Triples (41/70),
Turtle (203/313), N-Quads (53/87), TriG (223/356), RDF/XML (91/166),
rdf-mt (33/39).

**RDF 1.1 Model Theory (33 pass, 6 fail)**

The rdf-mt suite tests actual RDF graph semantics: literal
equivalence, datatype handling, RDFS closure rules. Remaining failures require
RDF.Graph.Executable.fst before they can pass. This is the real measure of
whether the F\* RDF implementation is correct.

### What rdf-mt Actually Tests (48 tests)

| Category | Count | What It Tests | F\* Status |
|----------|-------|---------------|------------|
| Simple matching | 7 | Language tag distinction, URI matching, reification non-entailment | Partially works |
| Literal/datatype semantics | 20 | Value equivalence, plain↔xsd:string, lang tag case, ill-formedness | **Missing in F\*** |
| RDF closure rules | 4 | Container membership (rdf:\_n), rdfs:member superProperty | **Missing in F\*** |
| RDFS closure rules | 14 | subClassOf, subPropertyOf, domain, range, intensional semantics | **Missing in F\*** |
| Advanced model theory | 3 | Value space disjointness, completeness axioms | **Missing in F\*** |

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

W3C test runner works. 303/408 SPARQL eval/syntax tests pass (105 fail,
205 skip/update, 18 unsupported format).

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

### Install z3 (CRITICAL — verification cannot work without it)

**This project is about verified code. z3 is not optional.** Every session must
ensure z3 is available before doing any F\* work. Without z3, extraction and
verification will fail.

```bash
# Check if z3 is available:
z3 --version  # must show 4.13.3

# If z3 is missing, install the pre-built binary (opam build often fails):
cd /tmp
curl -sL "https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-x64-glibc-2.35.zip" -o z3.zip
unzip -q z3.zip
cp z3-4.13.3-x64-glibc-2.35/bin/z3 /usr/local/bin/z3-4.13.3
chmod +x /usr/local/bin/z3-4.13.3
ln -sf /usr/local/bin/z3-4.13.3 /usr/local/bin/z3

# Verify it works:
z3-4.13.3 --version  # must show "Z3 version 4.13.3"
```

**Do NOT use `--lax` at all.** All F\* modules must verify and extract without
`--lax`. The `--lax` flag is banned — it defeats the purpose of formal
verification. Install z3 first, then verify and extract.

### Quick verification

```bash
eval $(opam env --switch=fstar)
cd formal/fstar

# Verify F* specs
make verify

# Extract + compile + test
./build-ocaml.sh

# Run W3C tests (w3c_runner is built by build-ocaml.sh)
cd ocaml-output
./w3c_runner                    # all SPARQL suites
./w3c_runner --rdf              # RDF parser suites
./w3c_runner --all              # both
./w3c_runner --list             # list suites
./w3c_runner bind functions     # specific suites
./w3c_runner -v aggregates      # verbose: full expected/actual dump on stderr
```

**Failure output**: FAIL lines always show UNMATCHED expected rows inline.
Use `-v` for the full expected/actual row dump (goes to stderr).

### Extraction notes

- **Never use `--lax`** — all modules must verify before extraction
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
