# RML program plan

Scoping doc for RDF Mapping Language (RML) support, modeled on the
stage structure in
[`2026-07-05-shex-program-plan.md`](2026-07-05-shex-program-plan.md).
RML maps heterogeneous sources (CSV, JSON, XML, relational) into RDF
via declarative Turtle mapping documents. Unlike ShEx and SHACL
(validate a graph against a schema), RML is a *construction* problem:
the engine reads a mapping document plus a data source and emits
triples. The closest precedent in this codebase is JSON-LD's toRdf
pipeline (source document in, RDF dataset out via a spec algorithm),
not the SHACL/ShEx validators.

## Vendored suite: verdict

`third_party/testing/rml` is **already declared as a git submodule**
in `.gitmodules`, pointing at `kg-construct/rml-test-cases.git`, with
a `160000` gitlink pinned at `803dd3ec`. `git ls-remote` against that
repo confirms the pin equals `HEAD`/`refs/heads/master` — current,
but current for the **wrong repo**. `kg-construct/rml-test-cases`'s
own README states it is archived and deprecated (2026-03-11): "new
test cases are available at w3id.org/rml/portal, organized per RML
module." The historical repo's tests are not organized by module
(core/io/cc/fnml/star) and predate the current five-module spec
split — they are a frozen snapshot of an earlier, unstratified RML,
not the conformance target.

**Recommendation: retire the `third_party/testing/rml` gitlink and
add five new submodules**, one per current module, mirroring how
`third_party/testing/shex` and `third_party/testing/json-ld` are each
one upstream test repo:

- `kg-construct/rml-core`
- `kg-construct/rml-io`
- `kg-construct/rml-cc`
- `kg-construct/rml-fnml`
- `kg-construct/rml-star`

Each was inventoried from a disposable scratch clone (no content
committed anywhere by this doc).

### Suite inventory (kg-construct org, 2026-07-05 clones)

| Module | Test dirs | Manifest | Source formats exercised |
|---|---|---|---|
| `rml-core` | 76 | `manifest.ttl` (N-Triples-in-`.ttl`) + `metadata.csv` | JSON only (core is format-agnostic by design; the module's own suite exercises semantics through one format) |
| `rml-io` | 73 (32 `RMLSTC0*` source + 41 `RMLTTC0*` target) | same shape | CSV, JSON, XML, N-Triples, plus compressed variants (`.gz`/`.zip`/`.xz`/`.tar.gz`) on the source side; N-Quads/N-Triples/Turtle/JSON-LD/RDF-XML/RDF-JSON/N3 + compression on the target/output side |
| `rml-cc` | 35 | same shape | JSON (containers/collections: `rdf:List`/`Bag`/`Seq`/`Alt` via `rml:gather`/`rml:gatherAs`) |
| `rml-fnml` | 20 | same shape | CSV (function execution via `fno:`/`grel:`/`idlab-fn:` vocabularies) |
| `rml-star` | 20 | `manifest.ttl` (30 KB) + `manifest.rml.ttl` | CSV/JSON (RDF-star quoted triples via `rml:AssertedTriplesMap`/`rml:quotedTriplesMap`) |

Total: 224 test-case directories across five modules. Every module
ships **both** a `metadata.csv` (17-19 columns: id, title,
description, mapping file, input/output format + filename triples,
`error` boolean) **and** a `manifest.ttl`/`manifest.rml.ttl` that is
plain N-Triples-syntax Turtle (`w3id.org/rml/test/{input,output,
hasError,mappingDocument,defaultBaseIRI}` predicates, `dcterms:
identifier`, typed `test-description#TestCase`). The Turtle manifest
is directly loadable by the existing Turtle/N-Triples parser with
**no Python flattener**, matching ShEx's win over JSON-LD's manifest
(which needed one) rather than JSON-LD's.

Each test directory is self-contained: `mapping.ttl` (the RML rules),
one or more input fixture files, and (unless `error` is `true`) an
`output.nq` expected result — the same shape `bin/jsonld-runner` and
`bin/shex-runner` (planned) already consume.

## Spec landscape and standardization state

**R2RML** (RDB to RDF Mapping Language) is a W3C Recommendation
(2012-09-27), SQL-backed only: one mapping document describes triples
maps whose logical source is `rr:sqlQuery`/`rr:tableName` against a
relational database.

**RML** is maintained by the W3C Knowledge Graph Construction
Community Group, published as a family of module specs at
`w3id.org/rml/<module>/spec`, each currently at **Draft Community
Group Report** status (rml-core's latest dated 2026-03-16; a CG
report, never Recommendation-track — same tier as ShEx's status, per
the ShEx plan). The abstract of RML-Core is explicit: "RML is defined
as a superset of the W3C-standardized mapping language R2RML... RML
follows exactly the same syntax as R2RML; therefore, RML mappings are
themselves RDF graphs." The six current modules:

| Module | Scope |
|---|---|
| RML-Core | TriplesMap/LogicalSource/SubjectMap/PredicateObjectMap/TermMap — the mapping engine itself, format-agnostic |
| RML-IO | Concrete logical sources (CSV/JSON/XML/relational access descriptors) and logical targets (output serialization + compression) |
| RML-CC | Collections and containers (`rdf:List`/`Bag`/`Seq`/`Alt` generation via `rml:gather`) |
| RML-FNML | Function execution (FnO-style transform functions applied inside term maps) |
| RML-star | RDF-star (quoted triple) generation |
| RML-LV | Logical views over data sources (newest module, no test-cases repo found yet — not counted above) |

**Conformance target for this program: RML-Core + RML-IO's
non-relational logical sources (CSV/JSON/XML) + RML-CC.** RML-FNML is
staged in (small, closed function catalog — see below); RML-star and
RML-IO's relational/SQL logical source are deferred (see the R2RML
test suite section below and the Staged plan's Stages 10-11). This
mirrors the ShEx program's ShExJ-first cut: take the modules
whose test corpus is reachable without a new external dependency
(SQL engine) or a missing prerequisite (RDF-star term type), and
build those completely before touching the rest.

### R2RML compatibility is not a namespace swap

RML-Core's claim to be "exactly the same syntax as R2RML" holds at
the RDF-graph level (mapping documents are triples either way) but
**not** at the term level. Current RML-Core has fully migrated off
the historical `rr:` namespace onto `rml:`, and several terms were
renamed in the process, not just re-prefixed: `rr:column` →
`rml:reference`, `rr:logicalTable` → `rml:logicalSource`,
`rr:sqlQuery`/`rr:tableName` → `rml:query`/`rml:iterator` under
`rml:referenceFormulation rml:SQL2008Table`. `rr:subjectMap`,
`rr:predicateObjectMap`, `rr:template`, `rr:class` kept their local
names under the new prefix. **R2RML-mapping compatibility, if ever
needed, is a small finite term-rename table applied at parse time —
not a shared vocabulary and not a shared parser** — this program does
not need to build it; no vendored test suite requires it (see next
section), so it is not on the staged plan below.

## R2RML test suite: assessed and deferred

The W3C `rdb2rdf-tests` suite lives at a static page
(`w3.org/2001/sw/rdb2rdf/test-cases/`), not an actively maintained git
repository — vendoring it means scraping a W3C wiki snapshot, not a
`git submodule` pin. Every test requires standing up a SQL schema
(`CREATE TABLE` + row data) and executing `rr:sqlQuery`/whole-table
access against it before RML/R2RML logic ever runs.

**Assessment: defer relational sources entirely, do not vendor
`rdb2rdf-tests`.** Reasons:

1. Across all 224 vendored RML test cases (the actual current
   conformance target), exactly **one** (`RMLSTC0006a`, "Source with
   D2RQ access description") references a relational/SQL logical
   source at all (`rml:SQL2008Table` + `d2rq:Database` connection
   descriptor) — and even that fixture supplies its data as a plain
   CSV file (`Friends.csv`) with a dummy `d2rq:jdbcDSN`, `iterator`
   naming a whole table with no `rr:sqlQuery` text to parse. It reads
   as a structural-descriptor test, not a SQL-execution test.
2. Standing up SQL means either vendoring SQLite (a large
   assume-val/glue surface: connection open, query execution, cursor
   iteration — a new I/O boundary class beyond file/clock/socket) or
   writing a SQL query executor in F\* (a project on the scale of the
   SPARQL evaluator itself, wildly disproportionate to one test's
   worth of coverage).
3. If relational-source support is ever wanted, the seam is: an
   `assume val sql_execute : connection -> query -> Tot (list row)`
   glue realised by a vendored SQLite (rule #11's ASSUME-IO
   pattern, same shape as `JSONLD.Loader`'s document-fetch assume
   val) feeding rows into the same `RML.Eval` term-map machinery CSV
   rows already feed — additive to the plan below, not a redesign.
   Not scheduled; revisit only if a relational fixture corpus with
   real coverage (not one D2RQ-descriptor smoke test) shows up.

## Iron-rules fit: what's reusable, what's new

**Reusable without change:**

- **Turtle/N-Triples parser** (`Parser.Turtle.fst`,
  `Parser.NTriples.fst`) reads both `mapping.ttl` documents and
  `manifest.ttl` test manifests — zero new tooling, same win as
  ShEx's Turtle manifests.
- **`Parser.JSON.fst`** (405 lines, full RFC 8259 value parser,
  `json_val` tree + `json_get_field`/`json_get_array` accessors)
  reads RML-Core's and RML-CC's JSON logical sources directly. No new
  parser needed for the JSON *tokenization* layer — only a JSONPath
  subset evaluator walking the existing `json_val` tree (see below).
- **`Parser.XML.fst`** (678 lines, `xml_node` tree +
  `child_elements`/`find_attr`/`text_content` accessors) reads
  RML-IO's XML logical sources the same way. Only an XPath subset
  evaluator is new.
- **SPARQL built-in string functions** already in
  `SPARQL11.Algebra.fst` (`SUBSTR`, `REPLACE`, `UCASE` and neighbors)
  cover most of RML-FNML's closed function catalog by direct reuse —
  see the FNML section below.

**Not reusable — needs a new small module:**

- **`Parser.CSVResults.fst`** is the **SPARQL 1.1 CSV/TSV results
  format** (`sparql11-results-csv-tsv`), a different dialect from
  RML's generic RFC 4180 delimited-file logical source: bare IRIs and
  typed-literal lexical conventions belong to the SPARQL results
  format, not to arbitrary tabular data. RML's CSV logical source
  needs a small new tokenizer (header row → column names, per-row
  string values, RFC 4180 quoting) — comparable in size to
  `Parser.SRX.fst`, not to `Parser.Turtle.fst`.

**JSONPath/XPath: F\* subset, not assume-val — surveyed against the
vendored fixtures, not guessed:**

Grepping every `rml:iterator`/`rml:reference`/`rml:path` string
literal across all 224 test cases shows the JSONPath subset in use is
narrow and closed: `$`, dotted field steps (`$.Name`,
`$.manager.name`), array wildcards (`$.amounts[*]`,
`$.companies[*].departments[*].employees[*]`), and field wildcards
(`$.v1.*`). No filter expressions, no recursive descent (`..`), no
slices, no unions appear anywhere in the corpus. The XPath subset is
equally narrow: child-axis steps (`/companies/company/departments`),
one instance of a descendant shorthand (`//Friends/Character`), and
`text()` leaf references (`name/text()`) — no predicates, no axes
beyond child/descendant, no functions besides `text()`.

Both subsets are small, closed, recursive-descent grammars —
structurally the same size class as `Parser.SRX.fst` or the ShEx
plan's `ShEx.Schema.fst` JSON decoder, not the size of a general
JSONPath/XPath engine. Per iron rule #4 (new parsers are F\*-first)
and rule #7 (no cobbling — the path-matching *is* mapping semantics,
not I/O), these belong in F\* as `RML.Sources.fst` functions walking
`json_val`/`xml_node` trees, not behind an `assume val`. An
assume-val here would put term-selection logic — the part of RML
that decides which values become which triples — outside the
verified boundary, which rule #11 reserves for pure I/O and
host-engine call-outs only. If a fixture later needs a JSONPath
feature outside this subset, extend the F\* grammar; do not reach for
a vendored JSONPath library.

**RML-FNML's function catalog is closed and mostly already built.**
Grepping all `rml-fnml` fixtures for `grel:`/`idlab-fn:` function
IRIs surfaces exactly 13 distinct functions across 20 tests
(`grel:toUpperCase`, `string_length`, `string_replace`,
`string_substring`, `escape`; `idlab-fn:equal`, `str`,
`toUpperCaseURL`, `alwaysReturnsABC`, plus parameter/output marker
predicates). `SUBSTR`/`REPLACE`/`UCASE` already exist as SPARQL
built-ins in `SPARQL11.Algebra.fst` — RML-FNML's dispatch table is
mostly a re-exposure of functions the engine already implements, plus
a handful of RML-specific no-arg/identity functions
(`alwaysReturnsABC`, `equal`). Staged in after the core engine, not
deferred with RML-star.

## Module plan

- **`formal/fstar/RML.Mapping.fst`** — the mapping-document AST
  (`triples_map`, `logical_source`, `subject_map`,
  `predicate_object_map`, `term_map` sum types covering
  `template`/`reference`/`constant` + `termType`/`datatype`/
  `language`) and a decoder that reads it out of an already-parsed
  RDF graph (the Turtle parser's
  output), not out of JSON — the mirror-image of `ShEx.Schema.fst`
  (JSON decoder) and closer in shape to how `SHACL.Validation.fst`
  reads shape graphs out of Turtle-parsed triples. `rml:` vocabulary
  term matching only; no evaluation here.
- **`formal/fstar/RML.Sources.fst`** — the logical-source iterator
  model: a `source_row` sum type (`Row_JSON of json_val | Row_XML of
  xml_node | Row_CSV of list (string * string)`), a JSONPath-subset
  evaluator over `json_val` (reusing `Parser.JSON`), an XPath-subset
  evaluator over `xml_node` (reusing `Parser.XML`), and a small new
  CSV tokenizer. Iteration is a `list source_row` per logical source
  — see Perf/storage tie-ins below for the streaming-vs-materialize
  call.
- **`formal/fstar/RML.Eval.fst`** — term-map evaluation given one
  `source_row` (template string interpolation, reference lookup,
  constant, termType coercion), triples-map evaluation (subject +
  predicate-object maps → triples), join conditions
  (`parentTriplesMap`/`joinCondition` — evaluate the child row,
  evaluate the parent triples map's rows, match on the join column),
  RML-CC's `gather`/`gatherAs` (build `rdf:List`/`Bag`/`Seq`/`Alt`
  structures from a nested reference list), and RML-FNML's function
  dispatch (reusing `SPARQL11.Algebra`'s string built-ins plus the
  small RML-specific registry).
- **`bin/rml-runner/rml_runner.ml`** — consumer wiring only (rule
  #11): reads `manifest.ttl` via the existing Turtle/N-Triples
  parser, loads `mapping.ttl` through extracted `RML.Mapping`, loads
  the fixture data file through extracted `RML.Sources`, calls
  extracted `RML.Eval`, compares the resulting dataset against
  `output.nq` via N-Quads isomorphism (reuse the runner-comparison
  machinery already built for `jsonld-runner`). No new `assume val`s
  expected.

## Staged plan

| Stage | Deliverable | Predicted coverage | Gate |
|---|---|---|---|
| 1 | **DONE.** Vendor 5 submodules (`third_party/testing/rml`'s deprecated pin left untouched, per the executing session's brief, rather than retired) + `RML.Mapping.fst` skeleton (TriplesMap/LogicalSource/TermMap AST, Turtle-graph decoder) | Structural parse of `rml-core`'s 76 mapping documents; no pass/fail signal yet — **measured**: 73/76 decode to >=1 TriplesMap; the remaining 3 (`RMLTC0023b/c/e`, all `metadata.csv error=true` "invalid IRI template" fixtures) contain a Turtle-illegal string escape (`\a`, not in Turtle's ECHAR set) that makes the whole document invalid Turtle — the vendored Turtle parser correctly parses 0 triples for those 3, which is the correct outcome for an `error=true` fixture, not a decoder gap. All 76 accounted for. | none |
| 2 | **DONE.** `RML.Sources.fst` JSON logical source (JSONPath subset, extended mid-stage to cover bracket-quoted field names — `$['Country Code']` — that the plan's initial grep survey missed) + `RML.Eval.fst` full term-map evaluation (constant/reference/template, IRI/URI/UnsafeIRI/BlankNode/Literal termType with RML-Core's IRI-safe-vs-URI-safe percent-encoding, `rml:datatype(Map)`/`rml:language(Map)` Cartesian products, `rml:class`/`rml:graph` including the `rml:defaultGraph` sentinel, subject/object multi-valued fan-out and cross products per spec 12.1 — no joins) | Majority of `rml-core`'s 76 tests (single-triples-map, no-join fixtures) — **measured** (scratch driver, not committed — Stage 8 owns `bin/rml-runner/`): 60 pass, 6 mismatch, 10 skipped (join/gather, Stage 5/6 — out of scope this stage), out of 76. The 6 mismatches: 4 are `error=true` fixtures this stage doesn't detect as errors yet (`RMLTC0002g` invalid JSONPath, `RMLTC0007h` non-IRI named graph, `RMLTC0012d` duplicate `rml:subjectMap`, `RMLTC0015b` invalid BCP47 language tag — none of these are validated, so the fixtures produce triples instead of the expected empty output); 1 (`RMLTC0019b`) is the codebase's existing coarse `is_iri` approximation (non-empty + contains a colon) accepting a space-containing string as "already absolute" instead of raising the data error RFC3987 would; 1 (`RMLTC0027b`) is a scratch-driver artifact — the expected `.nq` fixture's deliberately-unsafe IRIREFs (raw spaces/non-ASCII, `rml:UnsafeIRI`'s whole point) make the extracted `Parser.NQuads` stop after the first triple when parsing the *expected* side, undercounting it, not a bug in the generated output. Also fixed in Stage 1's `RML.Mapping.fst` while implementing term-type evaluation: `rml:URI` was wrongly decoded as a "legacy synonym" for `rml:IRI` (same `TT_IRI` variant); the spec's section 8.3.1 gives them genuinely different percent-encoding (IRI-safe vs URI-safe) — added a distinct `TT_URI` variant. | Stage 1 |
| 3 | CSV tokenizer + CSV logical source wired into `RML.Sources` | `rml-io`'s CSV-sourced `RMLSTC0*` tests (~10 of 32) + all 20 of `rml-fnml`'s CSV fixtures become reachable once Stage 7 lands | Stage 2 |
| 4 | XPath subset + XML logical source | `rml-io`'s XML-sourced `RMLSTC0*` tests (~7 of 32) | Stage 2 |
| 5 | Join conditions (`parentTriplesMap`/`joinCondition`) in `RML.Eval` | `rml-core`'s cross-triples-map join tests (a minority of the 76 — the harder tail) | Stage 2 |
| 6 | RML-CC `gather`/`gatherAs` (`rdf:List`/`Bag`/`Seq`/`Alt`) | `rml-cc`'s 35 tests | Stage 2 |
| 7 | RML-FNML dispatch (SPARQL built-in reuse + small registry) | `rml-fnml`'s 20 tests | Stage 3 (CSV) |
| 8 | `bin/rml-runner/` wiring | Score `rml-core` + `rml-io` (non-relational, non-target) + `rml-cc` + `rml-fnml`, labelled by module and stage reached | Stage 3 (first stage with a nontrivial signal) |
| 9 (indefinite) | RML-IO's 41 `RMLTTC0*` target/output-serialization tests | Mostly re-exposes existing serializers (Turtle/N-Quads/N-Triples/JSON-LD/RDF-XML writers already extracted); compression wrapping (`gz`/`zip`/`xz`/`tar`) is OCaml-side I/O glue (rule #11 ASSUME-IO), not mapping semantics — low priority, own commit | Stage 2 |
| 10 (indefinite) | Relational/SQL logical source | Blocked on the assume-val SQL seam decision above; 1 known fixture, no vendored suite | own program |
| 11 (indefinite) | RML-star | Blocked on an RDF-star (quoted-triple) term type — `RDF.Graph.Executable.fst` has no `T_Triple`/quoted-triple constructor today (see `rdf12-compatibility.md`); `rml-star`'s 20 tests need that prerequisite first, in RDF core, not in this program | RDF-star term-type program |

**Recommended commit-sized Stage 1, today:** add the five submodules
(`git submodule add` for `kg-construct/rml-core`, `rml-io`, `rml-cc`,
`rml-fnml`, `rml-star`, removing the stale `rml-test-cases` gitlink)
+ an `RML.Mapping.fst` skeleton: the `triples_map`/`logical_source`/
`term_map` sum types and a Turtle-graph-based decoder for
`rml:TriplesMap` subjects, verified but inert (no evaluation
function yet). Predicted result: parses all 76 `rml-core` mapping
documents — a "does it parse" smoke check, matching the ShEx and
JSON-LD programs' Stage 1 shape.

## Perf/storage tie-ins

- **Streaming iteration vs materialize.** RML's `LogicalSource` model
  is inherently row-at-a-time (the spec's own mental model is "for
  each row in source, apply subject map + predicate-object maps").
  `RML.Sources`'s iterator should therefore expose a row-at-a-time
  shape (fuel-bounded fold, same idiom as
  `SHACL.Validation.fst`'s fixpoint recursion) rather than
  materializing the entire JSON/XML tree's flattened row list before
  evaluation starts — this matters once fixtures grow past the W3C
  suite's small examples into real-world CSV/JSON exports. Phase 1
  (Stages 1-8 above) favors clarity — build the simple
  fully-materialized-list version first, matching the JSON-LD
  program's "Phase 1 favours clarity, measure before optimizing"
  lesson — but design `RML.Sources`'s public API (`next_row`-shaped,
  not `all_rows`-shaped) so the streaming refactor is additive, not a
  rewrite.
- **fn-API builder seam.** The npm functional/dataflow API (`fn.js`)
  already has a "builder seam for streaming parsers" landed in the
  2026-07-05 wave (per `current-state.md`'s standing-priorities log)
  — RML output should plug into that seam as another triple producer
  rather than building a separate output path, the same way JSON-LD's
  toRdf output already does.
- **Future COTTAS on-disk output.** RML's construction output is
  triples/quads — the same shape RDFC-1.0 canonicalization and the
  COTTAS backend already consume. No new storage design is needed
  here; once `RML.Eval` produces a `list quad`, it is a peer input to
  whatever backend (in-memory, HDT, COTTAS) already accepts extracted
  triples from other parsers. Do not build an RML-specific storage
  path.

## Open decisions

1. **Whether to vendor RML-LV** (Logical Views, the newest module).
   No `kg-construct/rml-lv` test-cases repo was found during this
   research pass — check again before Stage 1 lands; if it exists
   with a nontrivial suite, decide whether it folds into this plan or
   stays a follow-up. **Correction (Stage 1 execution, 2026-07-05):**
   `kg-construct/rml-lv` (the spec/ontology repo, not a separate
   `-test-cases` repo — same one-repo-per-module shape as rml-core
   etc.) does carry its own `test-cases/` directory: 41 `RMLLVTC00*`
   fixtures (`manifest.ttl` + `metadata.csv`, same shape as the other
   five modules), scratch-cloned and inventoried but not vendored as
   part of this Stage 1 commit (out of the five-submodule scope this
   session's brief set). Revisit folding it in as a sixth submodule in
   a follow-up stage.
2. **Whether `RML.Mapping.fst`'s Turtle-graph decoder should share
   code with `ShEx.Schema.fst`'s eventual Turtle-vocabulary reading**
   (ShEx is JSON-first per its own plan, so this may not materialize)
   or with `SHACL.Validation.fst`'s existing shape-graph decoder
   pattern — both read typed nodes + property paths out of an
   RDF-graph-shaped input; check for a shared "decode typed RDF node
   into F\* sum type" helper worth factoring out before writing a
   third bespoke decoder.
3. **RML-CC and RML-FNML's actual dependency order.** The staged plan
   above sequences both after Stages 2-4 (core term-map evaluation +
   all three logical sources), but they are mutually independent of
   each other — if a subagent is free before CSV/XPath land, RML-CC
   (JSON-only) can start immediately after Stage 2 rather than
   waiting.
4. **The one relational-source fixture (`RMLSTC0006a`).** Decide
   explicitly whether it counts as a permanent skip (labelled, like
   the SHACL `sh:sparql` custom-constraint skips) or gets a trivial
   hand-realisation (treat the CSV file as the "table," ignore the
   D2RQ connection descriptor entirely since no `rr:sqlQuery` text
   exists to execute) — the second option costs nothing beyond
   `RML.Sources`'s existing CSV path and closes `rml-io` to 33/33
   non-target, non-XPath-blocked tests instead of 32/33. Cheap enough
   that it may not deserve a placement in Stage 10 at all.
5. **RML-star's dependency on RDF-star.** If an RDF-star/RDF 1.2
   quoted-triple term type lands in `RDF.Graph.Executable.fst` for
   unrelated reasons (SPARQL-star, N-Triples-star parsing) before
   this program reaches Stage 11, re-scope Stage 11 as "wire into
   existing quoted-triple support" rather than "blocked" — check
   `rdf12-compatibility.md`'s promotion criteria at that point.
6. **Runner comparison semantics.** Confirm `bin/jsonld-runner`'s
   N-Quads isomorphism + bnode-comparison code is factored generically
   enough to reuse for `bin/rml-runner` without copy-paste — if not,
   factor a shared comparison module before Stage 8, per the
   subagent-prompting "one commit, one deliverable" rule rather than
   duplicating it inline.
