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
| 3 | **DONE.** RFC 4180 CSV tokenizer + CSV logical source, added directly to `RML.Sources.fst` per this table's own module-plan section (not a separate `Parser.CSV.fst` — `Parser.CSVResults.fst` is confirmed the wrong dialect, SPARQL 1.1 CSV/TSV *results*, not arbitrary tabular data); `RML.Eval.fst`'s reference/template evaluation generalized from JSON-only to dispatch on `source_row` (`reference_natural_values`/`reference_cast_strings`) so CSV rows (always `xsd:string` natural typing per the RML-IO spec) and JSON rows share one term-map pipeline; `rml:null` (list-valued, decoded off the **Source node**, not the LogicalSource node — a real bug caught by measurement, see below) filters null-valued column bindings out of a row entirely (same "no term generated" path as a missing JSON field) | `rml-io`'s CSV-sourced `RMLSTC0*` tests (~10 of 32) | **measured** (scratch driver, disposable): `rml-io` `RMLSTC0*` 17 pass, 15 fail (out of 32) — of the 9 CSV-referenceFormulation fixtures (`RMLSTC0004a/b/c`, `0006b`, `0007b`, `0008b`, `0009a`, `0010a`, `0010b`), 8 pass and 1 (`0009a`, "quoted columns", `metadata.csv error=true`) is an open anomaly: RFC 4180 quote-stripping makes its quoted header decode identically to an unquoted one, so this engine produces the same (expected-shape) triples an unquoted-header CSV would rather than the empty output the fixture's `error=true` flag calls for — the RML-IO spec text fetched directly gives no quoting-dialect rationale for why quoted headers should be an error, so this is left as a documented gap, not chased further. `RMLSTC0006a` (D2RQ/SQL2008Table) fails as expected per this plan's own open decision #4 (deferred). Of the other 15 failures: 7 are XPath/XML (`RMLSTC0007c/d`, `0012a-e` — Stage 4, not yet built, matches this row's ~7-of-32 XML prediction below), 4 are compressed JSON archives (`0002b/c/d/e` — `.gz`/`.zip`/`.tar.gz`/`.tar.xz`, an I/O-glue feature this plan's staged table never scheduled a stage for; flagged as an open decision, see plan doc's Open Decisions), 1 is a direct N-Triples/RDF logical source (`0003` — a `referenceFormulation` this program has no stage for at all), 1 is UTF-16-encoded JSON (`0001b`, `rml:encoding rml:UTF-16` — an encoding-declaration this program doesn't transcode, another not-yet-scheduled I/O-glue gap). None of the 15 non-CSV failures are CSV/Stage-3 bugs. Incidentally, running `rml-io` (never measured in Stage 2, which only ran `rml-core`) surfaced a JSONPath gap in `RML.Sources.fst`'s `parse_jsonpath`: a reference with no leading `$` (e.g. `RMLSTC0011b/c`'s `rml:template "http://example.org/{name}"` against a `$.companies[*]`-iterated row) was treated as identity (whole context, wrong) instead of a bare single-field lookup (right) — fixed as part of this stage since it's a one-line, contained, backward-compatible correction in the same file; recovered `0011b`/`0011c`. **Regression check**: re-ran `rml-core`'s 76-test suite after all Stage 3 changes — still 60 pass, 16 fail (same aggregate as Stage 2's "60 pass, 6 mismatch, 10 join-skip" — no regression from the JSON/CSV reference-evaluation generalization). `rml-cc` 0/35 (Stage 6 not built, expected); `rml-fnml` 5/20 (Stage 7 not built — the 5 passes are fixtures whose expected output happens not to depend on function-map evaluation, not a Stage 7 head start). | Stage 2 |
| 4 | XPath subset + XML logical source | `rml-io`'s XML-sourced `RMLSTC0*` tests (~7 of 32) | Stage 2 |
| 5 | **DONE** (same session/commit as Stage 8 below). RefObjectMap/join evaluation in `RML.Eval.fst` (`eval_join_triples_map` + `eval_join_pom`), semantics fetched from the spec's joinconditions.md/output.md sections directly (kg-construct/rml-core@spec/section, 2026-07-05): a join condition is child-map/parent-map expression-map equality — both are bare expression maps evaluated with the existing `eval_plain_strings`, equality implemented as non-empty intersection of the two (possibly multi-valued) value lists; pairing with join conditions is a full nested-loop join (verified: RMLTC0021a's self-join, 3 students / 2 sharing a sport, produces exactly the expected 5 triples), a **joinless** RefObjectMap requires "effectively equal" logical sources per the spec and pairs child/parent iterations **by index** (same ordered iteration sequence — RMLTC0008b); the generated object is the parent triples map's subject map applied to the matching parent iteration (parent's own `rml:baseIRI` in scope), while subject/predicates/graphs come from the child iteration (output.md's dedicated referencing-object-map loop). The same wave closed Stage 2's 6 mismatches: (a) the 4 unvalidated `error=true` fixtures — invalid iterator JSONPath yields no iterations (`RML.Sources.jsonpath_is_valid` + `json_iterate` gate, RMLTC0002g); a declared graph map whose evaluation produces no valid term now **drops** the triple (`placed_triple.pt_drop`) instead of silently falling back to the default graph (RMLTC0007h's Literal-typed graphMap); duplicate `rml:subjectMap` decodes to `None` = data error (`RML.Mapping.decode_subject_map`'s new two-or-more branch, RMLTC0012d); an invalid BCP47 language tag raises a data error (`rml_lang_tag_wf` — first-subtag well-formedness only, 2-8 ASCII letters or bare i/x, RMLTC0015b); (b) RMLTC0019b via an RML-side strict absolute-IRI gate (`rml_is_valid_absolute_iri` = shared coarse `is_iri` AND no 0x00-0x20/RFC3987-excluded bytes, same exclusion set as Parser.JSONLD's `jld_forbidden_byte`; the shared global `is_iri` predicate deliberately untouched — blast radius). Strict gate applies to `rml:IRI`/`rml:URI` only; `rml:UnsafeIRI` keeps the coarse check (`iri_like_term_gated false`) since IRIREF-illegal bytes are its purpose — the first post-gate measurement broke RMLTC0027b (75 pass, 1 fail), caught and fixed; (c) RMLTC0027b's expected-side N-Quads under-parse fixed in the runner via `sanitize_nquads_text` (comparison-only percent-encoding of IRIREF-illegal bytes inside `<...>`, applied to the raw expected fixture text AND to both canonicalized strings; the extracted `Parser_NQuads` stays spec-strict). **Measured: rml-core 76 pass, 0 fail (out of 76).** | Stage 2 |
| 6 | RML-CC `gather`/`gatherAs` (`rdf:List`/`Bag`/`Seq`/`Alt`) | `rml-cc`'s 35 tests | Stage 2 |
| 7 | RML-FNML dispatch (SPARQL built-in reuse + small registry) | `rml-fnml`'s 20 tests | Stage 3 (CSV) |
| 8 | **DONE** (same session/commit as Stage 5 above). `bin/rml-runner/rml_runner.ml` (jsonld_runner mold: repo-root walk, F*-extracted parsers only — metadata.csv read via `RML_Sources.csv_parse_rows` per rule #7, mapping.ttl via `Parser_Turtle`, comparison via `RDF_Canonical.canonicalize_to_nquads`), `.github/test-suites/rml.yaml` (trigger paths: the three RML modules, Turtle/NTriples/JSON/NQuads parsers, RDF.Canonical, SPARQL11.Algebra for the reused ENCODE_FOR_URI, the runner dir, the submodules), and `build-ocaml.sh` wiring (ALL_MODULES extract list + `COMMON_MODULES` + a lock-gated rml_runner stanza + `NATIVE_TARGETS`/`NATIVE_SOURCES` staleness entries — the rif_runner lesson: runners missing from those arrays never rebuild). Runner covers rml-core (primary, gates exit code) + rml-io behind `--io` (secondary; `RMLTTC0*` logical-target fixtures SKIP explicitly — Stage 9's scope, not silent). **Measured (2026-07-05): rml-core 76 pass, 0 fail (out of 76); rml-io 17 pass, 15 fail, 41 skip (out of 73)** — the 41 skips are the RMLTTC0* target tests, the 15 fails are Stage 3's documented gaps unchanged (7 XPath/XML = Stage 4 not built, 4 compressed archives, 1 UTF-16, 1 direct-RDF `.nt` source, 1 SQL/D2RQ deferred, 1 `RMLSTC0009a` quoted-columns anomaly per open decision #9); rml-io aggregate identical before/after this wave — no regression. `rml-cc`/`rml-fnml` sections join the runner when Stages 6-7 land. | Stage 3 (first stage with a nontrivial signal) |
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
7. **`rml-io`'s compressed-archive logical sources (Stage 3 finding).**
   4 of `RMLSTC0*`'s 32 fixtures (`0002b/c/d/e`) point `rml:path` at a
   `.gz`/`.zip`/`.tar.gz`/`.tar.xz`-wrapped JSON file. No stage above
   schedules decompression at all (the staged table's Stage 9 only
   covers compression on the *target/output* side, `RMLTTC0*`). This
   is rule #11 ASSUME-IO glue (an archive-decoder call-out), same
   shape as the SQL seam in the section above — not scheduled; needs
   an explicit stage or an accepted permanent-skip label before
   `rml-io` can reach 33/33 non-XPath, non-relational coverage.
8. **`rml-io`'s direct-RDF and encoding-declared logical sources
   (Stage 3 finding).** `RMLSTC0003` points at a plain `.nt` file with
   no JSONPath/XPath/CSV `referenceFormulation` at all (apparently a
   "read triples straight out of an RDF file" logical source this
   plan never named); `RMLSTC0001b` sets `rml:encoding rml:UTF-16` on
   a `FilePath` source (a byte-transcoding declaration this program
   doesn't apply before handing bytes to `Parser.JSON`). Neither has a
   stage; both are one-off `rml-io` fixtures, not corpus-wide gaps —
   flag for a future stage-boundary decision rather than building
   ad hoc.
9. **`RMLSTC0009a`'s "quoted columns" `error=true` fixture (Stage 3
   finding).** Its header row is fully RFC 4180-quoted
   (`"id","name","age"`); this program's CSV tokenizer quote-strips it
   to the same column names an unquoted header would give, so it
   produces the fixture's expected-shape triples instead of the empty
   output `error=true` calls for. The RML-IO spec text (fetched
   directly, 2026-07-05) gives no quoting-dialect rule that would make
   a quoted header invalid — left as an open, documented mismatch
   rather than guessed at.
