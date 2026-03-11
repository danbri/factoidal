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
   `minimal_regrettable_glue_code_each_with_an_open_issue/` (individual patch
   files, each with a GitHub issue number in the filename). No silent holes.
4. **Parsers belong in F\*.** RDF serialization parsers (N-Triples, Turtle,
   N-Quads, TriG, RDF/XML, CSV/TSV results) are implemented in F\* and
   extracted. All hand-written OCaml parsers have been removed. New parsers
   MUST be written in F\* first.
5. **Full SPARQL 1.1 is the target.** This includes Query, Update, Protocol,
   SERVICE (federated query), and all result formats (XML/SRX, JSON, CSV, TSV).
   Never default to 1.0 manifests when 1.1 exists.
6. **Run the real W3C test files.** Read manifests, `.rq`, `.srx`, `.ttl` from
   disk. Do not construct synthetic queries that are "inspired by" W3C tests.
7. **No cobbling.** No hand-written JS/Rust/OCaml reimplementations of what F\*
   defines. If you need new functionality, add it in F\* first, then extract.
8. **RDF semantics are not optional.** The rdf-mt (model theory) tests verify
   fundamental RDF graph semantics — literal equivalence, datatype handling,
   language tag normalization, RDFS closure rules. These are core requirements,
   not "just inference." Dismissing them is wrong.
9. **Commit compiled binaries.** The compiled `w3c_runner` and `factoidal`
   binaries in `ocaml-output/` MUST be committed to git. This lets the repo
   owner check out any commit and immediately run tests without needing an
   F\*/opam toolchain. Do not add them to `.gitignore`. Do not skip them
   when staging. When you run `build-ocaml.sh`, commit the updated binaries.
10. **Patches are for stubs and workarounds, NOT logic.** Post-extraction
    patches live in `minimal_regrettable_glue_code_each_with_an_open_issue/`
    as individual files named `<issue>_<description>.sh`. Each patch MUST
    have a corresponding open GitHub issue. Patches may wire `assume val`
    stubs, fix F\* type system limitations, and do forward-reference wiring.
    They must **never** contain RDF/SPARQL semantic logic. If you find yourself
    writing "if the entailment regime is RDFS then do X" in a patch, STOP —
    that logic belongs in F\*. Every line of logic in a patch is unverified,
    won't extract to C/WASM, and must be re-implemented for every target.
    **Known violations:** RDFS reflexivity axioms (#60), blank-node-as-existential
    rewriting (#53). When an issue is resolved (F\* replaces the patch), delete
    the patch file.

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
    `./ocaml-patches.sh ocaml-output`. Forgetting this silently
    regresses all `assume val` stubs to `failwith` and loses IRI
    resolution, RDF/XML validation, surrogate guards, and RDFS closure.

12. **Using `(*` in F\* comments when writing SPARQL-related code.** F\* comments
    `(* ... *)` nest. If a comment mentions SPARQL's `(*, /)` (multiplicative
    operators) or `COUNT(*)`, the `(*` opens a nested comment that silently
    swallows the rest of the file. F\* extraction will succeed but silently drop
    all definitions after the broken comment. **Use `//` line comments instead**
    when comment text contains `(*` or `*)`.

13. **Editing extracted `.ml` files directly.** Files in `ocaml-output/` that
    come from F\* extraction (`RDF_Graph_Executable.ml`, `SPARQL11_Algebra.ml`,
    `SPARQL11_Parser.ml`, `Parser_*.ml`) are **regenerated by
    `./build-ocaml.sh extract`**, destroying any manual edits. Even
    `w3c_runner.ml` (hand-written I/O glue) is patched by `ocaml-patches.sh`.
    **Rule: never edit extracted `.ml` files directly.** Instead:
    - Fix the F\* source (`.fst`) if possible (durable, verified)
    - If F\* verification blocks the fix, add a patch to `ocaml-patches.sh`
    - `ocaml-patches.sh` accepts a directory and patches all files in sequence
    A GitHub Action checks PRs for direct edits to extracted files.

14. **Never use `|| true` to swallow command failures in shell scripts.**
    `|| true` silently hides real errors. When a command might fail and you
    need the script to continue (e.g., under `set -e`), capture the exit code
    instead: `CMD_RC=0; OUTPUT=$(cmd ...) || CMD_RC=$?`. This lets the script
    continue while preserving the exit code for error reporting. The grep-based
    success checks still gate overall pass/fail.

15. **Sneaking logic into ocaml-patches.sh or w3c_runner.ml.** When a test
    fails, the temptation is to "quickly fix it" by adding OCaml code to the
    patches or test runner. This is cobbling by another name. Examples that
    happened and must be elevated to F\*:
    - RDFS reflexivity axioms computed in `w3c_runner.ml` (issue #60)
    - Blank-node-to-variable rewriting for entailment (issue #61)
    - Entailment regime detection and closure application
    **The test:** if the code makes a semantic decision about RDF or SPARQL,
    it belongs in `.fst` files. If it reads a file or compares strings, it's
    I/O glue and can stay. `ocaml-patches.sh` may only contain: `assume val`
    stubs, forward-reference wiring, F\* type system workarounds (with a
    comment explaining the F\* limitation), and I/O-layer fixes.

16. **Truncating command output with `tail -N` or `head -N`.** Piping test
    runners, build logs, or diagnostic output through `tail -20` (or similar)
    silently discards the vast majority of the output. When a 1000-line test
    run is piped through `tail -20`, 98% of the results vanish — including
    the specific FAIL lines needed for debugging. This happened in
    `build-ocaml.sh` where `w3c_runner --all 2>&1 | tail -20` hid all
    individual test results. **Rule: never truncate command output in
    scripts or CI.** Use `tee` to save full output to a file while still
    streaming to the terminal: `cmd 2>&1 | tee results.log`. If you only
    want a summary on screen, print the summary *after* the full run, don't
    pipe through `tail`. The same applies to `head -N` — it kills the
    process via SIGPIPE once N lines are emitted, so later output (including
    summary lines) is lost entirely.

## Current State (Honest Assessment)

### F\* Specifications

```
formal/fstar/
  RDF.Graph.Executable.fst     638 lines, 0 admit, 0 assume val
  SPARQL11.Algebra.fst        3658 lines, 5 admit, 14 assume val
  SPARQL11.Parser.fst          F* SPARQL parser (in development)
  Makefile                     verify + extract-c targets
  build-ocaml.sh               F* -> OCaml -> js_of_ocaml pipeline
  ocaml-patches.sh             master script: applies all patches from
                               minimal_regrettable_glue_code_each_with_an_open_issue/
  minimal_regrettable_glue_code_each_with_an_open_issue/
                               individual patch files, each named
                               <issue>_<description>.sh with GitHub issue
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

### Plain-English Status Summary (as of 2026-03-11)

Factoidal is a formally verified RDF/SPARQL implementation written in F\* and
tested against the official W3C conformance suites. The core SPARQL query
evaluator passes 363 of 406 applicable query/syntax tests (89%), with strong
results in aggregates (43/44), built-in functions (74/75), BIND (10/10),
negation (11/12), property paths (33/33), entailment (44/70), exists (6/6),
grouping (6/6), project-expression (7/7), and subqueries (9/11). The main
SPARQL gaps are: UPDATE not yet implemented (205 tests skipped — in scope,
tracked by #59), Protocol not yet implemented (34 tests skipped), SERVICE
returns empty (needs HTTP client, tracked by #57), incomplete negative syntax
rejection (parser accepts 1 query it should reject), incomplete xsd:float/double
casting, and JSON/CSV/TSV result format support not yet implemented (20 tests).
CONSTRUCT is partially implemented (2/3 pass).

On the RDF parsing side, F\*-extracted parsers handle all six serialization
formats: N-Triples 41/70, Turtle 296/313, N-Quads 53/87, TriG 334/356,
RDF/XML 120/166, rdf-mt 39/39. Most remaining parser failures involve
prefixed name validation (pname/local name escapes) and a few TriG-specific
negative syntax edge cases.

In short: the query evaluator works well for SELECT queries and the parsers
handle the vast majority of cases. The system is held back by (a) prefixed
name validation edge cases, (b) SPARQL UPDATE/Protocol not yet implemented,
(c) SERVICE (federated query) needs HTTP client, and (d) JSON/CSV/TSV result
formats not yet implemented. All of these are in scope and tracked by #71.

### W3C Test Results (as of 2026-03-11)

**SPARQL 1.1 — 363 pass, 43 fail, 205 skip, 20 unsupported (631 total)**

Per-suite: aggregates 43/47, bind 10/10, bindings 10/11, cast 4/6,
construct 2/7, entailment 44/70, exists 6/6, functions 74/75, grouping 6/6,
negation 11/12, project-expression 7/7, property-path 33/33, service 0/7,
subquery 9/14, syntax-query 93/94, syntax-fed 3/3, delete-insert 8/17.
Not yet implemented: 205 UPDATE operations (add, basic-update, clear, copy,
delete, delete-data, delete-where, drop, move, http-rdf-update,
syntax-update-*, update-silent). Protocol: 34 not yet implemented.
Service-description: 3 not yet implemented. Result format gaps: json-res (4),
csv-tsv-res (6), aggregates (3 Turtle results), construct (4 Turtle results),
subquery (2 Turtle results), bindings (1).

**RDF 1.1 — 883 pass, 148 fail (1031 total)**

Per-suite: N-Triples 41/70, Turtle 296/313, N-Quads 53/87, TriG 334/356,
RDF/XML 120/166, rdf-mt 39/39.

**RDF 1.1 Model Theory — 39 pass, 0 fail (39 total)**

All rdf-mt tests pass: literal equivalence, datatype handling, RDFS closure
rules, language tag normalization, value-space entailment with consistent
blank node mapping.

### What rdf-mt Actually Tests (39 tests)

| Category | Count | What It Tests | F\* Status |
|----------|-------|---------------|------------|
| Simple matching | 7 | Language tag distinction, URI matching, reification non-entailment | **PASS** |
| Literal/datatype semantics | 20 | Value equivalence, plain↔xsd:string, lang tag case, ill-formedness | **PASS** |
| RDF closure rules | 4 | Container membership (rdf:\_n), rdfs:member superProperty | **PASS** |
| RDFS closure rules | 14 | subClassOf, subPropertyOf, domain, range, intensional semantics | **PASS** (via ocaml-patches.sh closure) |
| Advanced model theory | 3 | Value space disjointness, completeness axioms | **PASS** (not tested — 9 skipped) |

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

Working from test failures, extend the F\* SPARQL spec:

1. **Result formats** — JSON Results (`application/sparql-results+json`),
   CSV (`text/csv`), TSV (`text/tab-separated-values`) serializers in F\*.
   SRX parser already exists; JSON/CSV/TSV result parsers needed for test
   comparison. ~20 tests blocked.
2. **SPARQL UPDATE** — INSERT DATA, DELETE DATA, INSERT/DELETE (with WHERE),
   LOAD, CLEAR, DROP, ADD, MOVE, COPY, CREATE. Requires mutable graph store
   model in F\*. 205 tests. Tracked by #59.
3. **SPARQL Protocol** — HTTP interface for query and update operations.
   34 tests. Requires HTTP server, which can use `assume val` with OCaml
   stub (see I/O and networking below).
4. **SERVICE (federated query)** — Requires HTTP client to contact remote
   SPARQL endpoints. 7 tests. Tracked by #57.
5. **Service Description** — 3 tests.

### Phase 5 — I/O, Networking, and Async

F\* extracted code is pure/total by default. Networking (SERVICE, Protocol,
LOAD) requires I/O effects. Strategy:

- **`assume val` for I/O primitives.** Declare HTTP client/server operations
  as `assume val` in F\* with OCaml stubs. This keeps the verified boundary
  around query semantics while allowing real network operations.
- **Simple synchronous blocking API.** For `web_fetch : url -> result`, a
  blocking OCaml stub using `Unix.open_connection` or `Cohttp_lwt_unix` is
  the simplest approach. Good enough for test runner and CLI usage.
- **Async considerations for extracted applications.** When F\*-extracted code
  runs in a larger async context (e.g., a web server), the blocking stubs
  become a problem. Options:
  1. **Thread pool** — run blocking F\* calls in a thread pool, integrate
     with Lwt/Async via `Lwt_preemptive.detach` or similar.
  2. **Effect-polymorphic F\*** — F\* has `Effect` and `PURE`/`DIV`/`ST`
     effect system. In principle, I/O effects can be modeled, but extraction
     of effectful code to async OCaml is not well-supported by F\* today.
  3. **js_of_ocaml + promises** — for browser/Node targets, blocking I/O
     is impossible. The js_of_ocaml path would need promise-based stubs
     with continuation-passing, which is architecturally different.
  The current plan: start with blocking stubs (#57), document the limitation,
  and track async extraction as a separate research issue.

### Phase 6 — Verified extraction pipeline

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
  rdf/rdf11/rdf-n-quads/           N-Quads syntax tests (87)
  rdf/rdf11/rdf-trig/              TriG syntax+eval tests (356)
  rdf/rdf11/rdf-xml/               RDF/XML eval tests (166)
  rdf/rdf11/rdf-mt/                Model theory / semantics (39)
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

## GitHub CLI (`gh`) in Claude Code

The git remote uses a local proxy (`127.0.0.1`), so `gh` commands that infer
the repo from the remote will fail with "none of the git remotes configured
for this repository point to a known GitHub host." **Fix: always pass
`--repo danbri/factoidal` explicitly.**

```bash
# These work:
gh pr create --repo danbri/factoidal --base claude/main --head my-branch ...
gh pr list --repo danbri/factoidal
gh pr view 42 --repo danbri/factoidal

# This does NOT work (no --repo):
gh pr create --base claude/main ...  # ERROR: unknown host
```

## Repository Structure

```
factoidal/
├── formal/fstar/              THE PRODUCT
│   ├── RDF.Graph.Executable.fst   RDF graph types + operations
│   ├── SPARQL11.Algebra.fst       SPARQL 1.1 algebra + evaluator
│   ├── SPARQL11.Parser.fst        SPARQL parser (in development)
│   ├── Makefile
│   ├── build-ocaml.sh
│   ├── ocaml-patches.sh               applies patches from glue directory
│   ├── minimal_regrettable_glue_code_each_with_an_open_issue/
│   │   ├── 53_blank_node_variable_rewriting.sh
│   │   ├── 60_rdfs_closure_reflexivity.sh
│   │   ├── 62_forward_ref_wiring.sh
│   │   ├── 63_regex_hash_uuid_stubs.sh
│   │   ├── 64_sparql_parser_escape_stubs.sh
│   │   ├── 65_base_iri_resolution.sh
│   │   ├── 66_zero_length_property_path.sh
│   │   ├── 67_rdfxml_validation.sh
│   │   ├── 68_unicode_boundary_workarounds.sh
│   │   └── 69_runner_io_glue.sh
│   └── ocaml-output/          extracted + TEMPORARY test harness
├── tests/w3c/                 git submodule (W3C test files)
├── kgx/                       SPARQL CONSTRUCT queries (future)
├── docs/
│   ├── designissues/          architecture docs
│   └── skills/                operational knowledge
├── junk/do_not_use/           vibe-coded artifacts (DO NOT USE)
└── CLAUDE.md                  this file
```
