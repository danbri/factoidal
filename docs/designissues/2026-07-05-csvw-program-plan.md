---
templateEngineOverride: md
---

# CSVW program plan

<!-- The templateEngineOverride above stops Eleventy running Nunjucks
     on this file: the URI-template examples below contain `{#...}`,
     which Nunjucks parses as an unterminated comment tag and the
     whole site build fails. -->

Scoping doc for CSV on the Web (CSVW) support, modeled on the stage
structure in
[`2026-07-05-rml-program-plan.md`](2026-07-05-rml-program-plan.md).
CSVW is a **conversion** problem, close in shape to RML: a tabular
source (CSV) plus a metadata document describing its schema/URI
templates/datatypes goes in, an RDF dataset (csv2rdf) or a JSON
document (csv2json) comes out. Unlike RML, there is no separate
mapping-document language — CSVW's metadata format **is** the schema
description, and the conversion algorithm is one fixed, closed
procedure per output format (no arbitrary term-map evaluation, no
joins, no FnO functions). This makes CSVW smaller in surface area
than RML despite covering similar ground (heterogeneous-source-to-
RDF), and — per the spec landscape section below — the target is
frozen: all four specs are decade-old, stable Recommendations, and
the upstream repo was archived in the middle of this research pass.

## Vendored suite: verdict

`.gitmodules` already declares
`third_party/testing/csvw` → `w3c/csvw.git` (`branch = gh-pages`),
currently **uninitialized** (`git submodule status` shows a leading
`-`, pinned commit `2bc84f937be...`). A shallow scratch clone
(disposable, nothing committed) of the `gh-pages` branch confirms the
pin is reachable and the `tests/` directory is present and complete.

**Recommendation: initialize the existing gitlink as-is — no repo
swap needed**, unlike the RML program (which had to retire a stale
gitlink pointing at a deprecated repo). One fact changes the
initialization's urgency slightly: **`w3c/csvw` was archived by its
owner on 2026-05-22** ("This repository was archived... It is now
read-only"), during this same research pass' web lookups. This is
good news for pin stability (the suite cannot drift under us) and
bad news for any bug found in the suite itself (no upstream PR path
— document defects locally instead, the same posture already used
for the one known-defective W3C RIF zip file per `current-state.md`).

### Suite inventory (2026-07-05 scratch clone, `gh-pages` branch)

The `tests/` directory ships **five manifests**, each JSON-LD (with
a parallel Turtle mirror using the same `mf:`/custom-vocabulary
predicates the RDF/SPARQL test manifests already use), so the
existing Turtle/N-Triples parser reads the `.ttl` mirrors directly —
the JSON-LD manifests are the canonical form but not the only way in.

| Manifest | Entries | Test-type breakdown |
|---|---|---|
| `manifest-rdf.jsonld` (csv2rdf) | 270 | 76 `ToRdfTest` (positive, clean), 136 `ToRdfTestWithWarnings` (positive, spec-mandated warnings expected), 58 `NegativeRdfTest` (must fail/produce no output) |
| `manifest-json.jsonld` (csv2json) | 270 | Same 76/136/58 split under `ToJsonTest`/`ToJsonTestWithWarnings`/`NegativeJsonTest` — csv2rdf and csv2json manifests are structurally parallel, generated from the same source-table set |
| `manifest-validation.jsonld` (validation mode — CSV+metadata conformance, no output) | 282 | 76 `PositiveValidationTest`, 61 `WarningValidationTest`, 145 `NegativeValidationTest` — the **largest** of the three, and majority-negative (validation's whole point is catching malformed metadata) |
| `manifest-nonnorm.jsonld` | 19 | Non-normative examples from the spec prose, not conformance-gating |
| `manifest.jsonld` | (top-level index, no direct entries) | Points at the four manifests above |

(Grepped entry counts include one self-referencing `"id"` per file
for the manifest's own top-level object; the table above already
subtracts it — 270/270/282/19 are real per-test entry counts.)

**Fixture shape**: each test is `testNNN[-metadata].json` (metadata
descriptor, optional per test — omission means "infer schema from
the CSV header row"), `testNNN.csv` (or a shared fixture like
`countries.csv`), and `testNNN.{ttl,json}` (expected csv2rdf/csv2json
output for positive tests; absent for negative tests). Two tests
(`test118`, `test119`) use a subdirectory (`test118/action.csv`,
`csv-metadata.json`, `result.ttl`, `result.json`) instead of flat
top-level files — apparently because those specific tests need the
input at a controlled relative path for relative-URL-resolution
checks. All other ~268 tests are flat files at `tests/` top level.
The `tests/` directory holds 867 numbered files total (csv/json/ttl
combined across all manifests — not a test count, a raw file count;
many are shared across the rdf/json manifest pairs since they convert
the same source table to two output formats).

`option` flags seen across the csv2rdf manifest: `noProv: true` on
270 of 270 entries (every single test suppresses provenance
metadata — the suite defaults away from generating
`csvw:TableGroup`/`prov:` triples, which simplifies our conformance
target: standard-mode output comparison rarely needs provenance
triples), `minimal: true` on 7 entries (the "minimal mode" variant —
see Open decision 2), `metadata`/`httpLink` overrides on 5-7 entries
each (explicit metadata-document URL or HTTP `Link:` header
simulation — edge cases, low priority).

## Spec landscape and standardization state

All four Recommendations were published **the same day, 2015-12-17**,
by the (now-closed) CSV on the Web Working Group, and have not been
revised since (confirmed via `w3.org/TR/` publication history
lookups during this research pass — no 2.0 exists for any of the
four). Combined with the source repo's 2026-05-22 archival, this is
the most stable conformance target of any program plan in this
series: no moving spec text, no draft-vs-Rec ambiguity, and (per the
archival) no expectation of new erratum PRs landing upstream either.

| Spec | Scope |
|---|---|
| Model for Tabular Data and Metadata on the Web (`tabular-data-model`) | The abstract data model: rows, columns, cells, a table group; how a metadata document annotates a CSV file; URI template resolution for `aboutUrl`/`propertyUrl`/`valueUrl` |
| Metadata Vocabulary for Tabular Data (`tabular-metadata`) | The JSON vocabulary for describing tables: `tableSchema`, `columns`, `dialect` (delimiter/quote/header options), datatype annotations (`base`/`format`/`length`/facets), inherited properties, `@context: http://www.w3.org/ns/csvw` |
| Generating RDF from Tabular Data on the Web (`csv2rdf`) | The row-by-row conversion algorithm from an annotated table to an RDF dataset — "standard" mode (full triples incl. provenance by default) and "minimal" mode (bare cell-value triples only) |
| Generating JSON from Tabular Data on the Web (`csv2json`) | The parallel conversion algorithm to a JSON structure (arrays of row objects, or a "minimal" flat array) |

## Fit: what's reusable, what's new (and what the brief's framing gets wrong)

**RFC 4180 CSV tokenizer — coordinate with RML, do not fork it, but
it does not exist yet.** The RML program plan (Stage 3 of
`2026-07-05-rml-program-plan.md`) is the natural place for a shared
CSV tokenizer, and this plan should consume whatever `RML.Sources`
lands there rather than building a second one. **As of this research
pass, that work has not landed**: `formal/fstar/RML.Sources.fst`'s
own module banner still reads "CSV (Stage 3) and XML (Stage 4) join
the sum type in Stages 3/4" (present tense future — i.e. pending),
and `grep -n "csv" RML.Sources.fst` turns up only that banner
comment, no tokenizer code. `Parser.CSVResults.fst` exists but is the
**SPARQL 1.1 CSV/TSV results format** (bare IRIs, typed-literal
lexical conventions specific to SPARQL result serialization) — a
different dialect from generic RFC 4180 tabular data, confirmed by
the RML plan's own analysis and re-confirmed here. **This plan's
Stage 1 (metadata parsing) does not need CSV tokenization at all**
(metadata documents are JSON) and can proceed independently; Stage 3
(actual CSV-to-RDF/JSON conversion) is blocked on RML's CSV stage
landing — track it as a shared dependency, not a duplicate build, and
if this program's Stage 3 is ready first, the tokenizer should land
under whichever program gets there first with the other consuming it,
not be written twice.

**JSON-LD reuse is smaller than it first looks — the metadata
vocabulary is not a general JSON-LD processing target.** The brief's
framing (JSON-LD "for metadata processing... dialect descriptions,
inherited properties") is directionally right but overstates the
dependency: every metadata document in the vendored corpus that
declares `@context` at all (269 of ~271 files) uses the **bare
string** `"@context": "http://www.w3.org/ns/csvw"` — a fixed sentinel,
not an arbitrary remote context to fetch/expand/resolve. The CSVW
metadata vocabulary spec (§6, "Normalization") defines its **own**
closed, table-driven normalization procedure (a fixed list of known
properties, each tagged inherited/non-inherited/common per the
spec's own property table) — it does not delegate to general JSON-LD
`@context` term-resolution machinery. **What's actually needed is
`Parser.JSON.fst`'s tokenizer** (already built, 405-line RFC 8259
parser, `json_val` tree + `json_get_field`/`json_get_array`
accessors) **plus a bespoke CSVW-specific decoder walking that tree
against the spec's fixed property table** — structurally closer to
`RML.Mapping.fst`'s "decode a fixed vocabulary out of an already-
parsed tree" pattern than to `JSONLD.Expand.fst`'s general-purpose
context resolution. Reusing `JSONLD.Context`/`JSONLD.Expand`
wholesale would be over-engineering for what the corpus actually
exercises; note the two files that use an array-form `@context`
(`test027-user-metadata.json` and one other) before assuming the
bare-string case is exhaustive.

**URI templates: RFC 6570 Levels 1-2 only, confirmed by corpus
survey, not guessed.** Grepping every `aboutUrl`/`propertyUrl`/
`valueUrl` string literal across the 37 metadata files that use them
shows a narrow, closed set: plain variable substitution (`#gid-
{GID}`, `http://schema.org/{_name}`, `countries.csv{#countryRef}`)
and fragment expansion (`{#countryCode}`, `{#_name}`) — using both
CSVW's ordinary column-name variables and its special `_row`/`_name`/
`_sourceRow` variables (the leading underscore is CSVW's own
convention, not an RFC 6570 feature). **No reserved-string expansion
(`{+var}`), no query-form (`{?var}`), no path-segment (`{/var}`), no
multi-variable lists, and no prefix/explode modifiers (`{var:3}`,
`{var*}`) appear anywhere in the corpus.** This is a smaller subset
than the brief's "Level 4 subset" framing suggested — Level 1
(simple string expansion) plus the fragment-operator half of Level 2
covers every fixture found. Build exactly that; extend only if a
later fixture needs more (see Open decision 3).

**Datatype formatting/parsing — survey says `date`/`decimal`/`float`
dominate, not `dateTime`.** Grepping every `"base"` facet across the
corpus: `date` (124 uses) is by far the most common, ahead of
`decimal` (44), `float` (43), `integer` (27), `dateTime` (19),
`string` (15), `time` (10), plus one-off uses of the full XSD
numeric-subtype hierarchy (`unsignedShort`, `positiveInteger`,
`nonNegativeInteger`, …) and the full XSD date/time family
(`gYear`, `gYearMonth`, `gMonth`, `gMonthDay`, `gDay`,
`dateTimeStamp`, `duration`, `yearMonthDuration`, `dayTimeDuration`).
`XSD.Datatypes.fst` currently implements **only** `dateTime` parsing
and ordering (moved from `SHACL.Validation.fst`) — every other
date/time XSD subtype CSVW's own corpus exercises (`date` alone
outnumbers `dateTime` 6.5-to-1) is a gap, not a reuse. Custom
`format` facets are common too: 58 uses of a non-ISO date pattern
(`M/d/yyyy`), a family of numeric patterns (`#0.0#`, `#,##,##0`,
`##0`) needing `groupChar`/`decimalChar` support, and two boolean
patterns (`Y|N` — CSVW's boolean facet is a `true|false`-string pair,
not XSD's `true`/`1` convention). **This is the single biggest new-
work item in this plan** — closer in size to a new `CSVW.Datatypes`
extension of `XSD.Datatypes` than a thin reuse, and it should be
scoped and staged as such rather than folded silently into
`CSVW.Convert`.

**csv2rdf standard vs minimal mode is a real fork, not a flag.**
Standard mode emits full provenance (table group node, `prov:`
predicates, `csvw:describes`) by default; minimal mode emits bare
subject-predicate-object triples only, no provenance, no table-group
wrapper. The manifest's `noProv: true` on 270/270 csv2rdf entries
means **the vendored suite tests minimal-shaped output almost
exclusively** even under "standard" mode's own test type — build
minimal-mode-equivalent output first (see Open decision 1), not full
provenance generation, since that is what the suite actually scores.

## Module plan

- **`formal/fstar/CSVW.Metadata.fst`** — the metadata-document
  decoder: walks a `Parser.JSON`-parsed `json_val` tree against the
  spec's fixed property table (dialect options: `delimiter`,
  `quoteChar`, `doubleQuote`, `header`/`headerRowCount`,
  `skipRows`, `commentPrefix`, `encoding`, `lineTerminators`;
  `tableSchema.columns[]` with `name`/`titles`/`datatype`/`virtual`/
  `suppressOutput`; `aboutUrl`/`propertyUrl`/`valueUrl` template
  strings; inherited-property propagation from table group → table →
  schema → column per the spec's inheritance rules). Emits a
  `csvw_metadata` sum type. No CSV/RDF logic here — the mirror image
  of `RML.Mapping.fst`'s Turtle-graph decoder, but over JSON instead
  of RDF.
- **`formal/fstar/CSVW.URITemplate.fst`** — the RFC 6570 Level 1 +
  fragment-operator subset confirmed by the corpus survey above:
  plain `{var}` substitution and `{#var}` fragment expansion,
  resolving CSVW's special variables (`_row`, `_name`, `_sourceRow`,
  ordinary column names) against a row's binding context. Small,
  closed grammar — same size class as the RML plan's JSONPath/XPath
  subset modules.
- **`formal/fstar/XSD.Datatypes.fst` — extended, not a new module.**
  Add `xsd:date`/`xsd:time`/`xsd:gYear`/`xsd:gYearMonth`/`xsd:gMonth`/
  `xsd:gMonthDay`/`xsd:gDay`/`xsd:dateTimeStamp` parsing (mostly
  substring slices of the existing `dateTime` parser's calendar
  arithmetic) plus a `format`-facet interpreter for the pattern
  families the corpus actually uses (custom date patterns like
  `M/d/yyyy`; numeric patterns with `groupChar`/`decimalChar`; the
  `Y|N`-style boolean pattern pair). This is the module plan's
  largest single item — see the Fit section above.
- **`formal/fstar/CSVW.Convert.fst`** — the csv2rdf and csv2json
  conversion algorithms: row-at-a-time iteration over a tokenized CSV
  (the shared dependency on the not-yet-landed CSV tokenizer — see
  Fit), resolving each cell against its column's datatype (via the
  extended `XSD.Datatypes`) and URI templates (via
  `CSVW.URITemplate`), assembling triples (csv2rdf, minimal mode
  first) or JSON row objects (csv2json, minimal mode first),
  optionally layering on provenance/table-group wrapping (standard
  mode) once minimal mode is scored.
- **`formal/fstar/CSVW.Validate.fst`** — the validation-mode checks
  the 282-entry `manifest-validation.jsonld` exercises: metadata
  document well-formedness, datatype-facet consistency, duplicate
  column-name detection, and the rest of the spec's normative
  "MUST be rejected" list. Likely shares most of its logic with
  `CSVW.Metadata`'s decoder (a malformed metadata document already
  fails to decode) — factor out before duplicating checks (see Open
  decision 4).
- **`bin/csvw-runner/csvw_runner.ml`** — consumer wiring only (rule
  #11): reads the `.ttl` manifest mirrors via the existing Turtle
  parser, loads each `testNNN[-metadata].json` through extracted
  `CSVW.Metadata`, loads the CSV fixture through the (shared, RML-
  coordinated) CSV tokenizer, calls extracted `CSVW.Convert` or
  `CSVW.Validate`, and compares against `testNNN.ttl`/`.json` via the
  same N-Quads/Turtle isomorphism machinery `bin/jsonld-runner` and
  the planned `bin/rml-runner` already use (factor once, reuse
  thrice — see the RML plan's own Open decision 6 on this exact
  point).

## Staged plan

| Stage | Deliverable | Predicted coverage | Gate |
|---|---|---|---|
| 1 | **DONE.** Initialize `third_party/testing/csvw` submodule; `CSVW.Metadata.fst` skeleton (dialect options + `tableSchema.columns[]` decode, no inheritance yet; no fuel threading needed anywhere — columns/tables are flat lists, not a recursive shapeExpr-style grammar) | Structural parse of a subset of the ~271 metadata documents — measure once built, do not predict. **Measured (2026-07-05, scratch driver over `third_party/testing/csvw/tests`, not committed — no runner stage reached yet): 286/293 metadata documents decode to `Some csvw_metadata` with >=1 table (235 single-table, 51 table-group); 293 is the actual file count from a full directory walk matching `*-metadata.json`/`csv-metadata.json` (including `linked-metadata.json`/`user-metadata.json` httpLink/metadata-override variants and subdirectory fixtures beyond the plan's `test118`/`test119` pair — e.g. `test011`-`test037`, `test123` — not just the ~271 the manifest-entry-count estimate implied).** Of the 7 that return `None` or an empty table group: 1 (`test074-metadata.json`, `"tables": []`) decodes structurally to a valid-but-empty `CSVW_TableGroup`, not a decoder failure — the empty-group case is a semantic question (spec conformance of a zero-table group) out of scope for a structural decoder; 3 (`test092`/`test094`/`test096`) are deliberately malformed negative fixtures (invalid JSON syntax; a bare number where a `Table`/`Column` object belongs) that the decoder correctly rejects — expected `None`, not a gap; 1 (`test107-metadata.json`, `"tableSchema": 1`) is a genuine gap: the spec's own comment on this fixture says an invalid-typed `tableSchema` "MUST act as if it was an empty object" (graceful degradation), but this decoder's leniency policy treats a non-object `tableSchema` as a structural-shape failure that fails the whole table — worth a one-line fix (treat non-JObject `tableSchema` as `Some { ts_columns = []; ... }` instead of `None`) whenever Stage 2 revisits table-schema decode, not chased here since it is a single documented fixture, not a design flaw; 2 (`test034`/`test035`, `"tableSchema": "gov.uk/schema/professions.json"`) use the spec's schema-by-reference form (a URL string instead of an inline object) — fetching and inlining an external schema document is explicitly out of scope for this skeleton (no HTTP I/O in Stage 1) and is a candidate for a later stage's scope note, not a bug. | none |
| 2 | `CSVW.Metadata.fst` complete: inherited-property propagation, `aboutUrl`/`propertyUrl`/`valueUrl` template-string extraction (not resolution yet). **Carried in from Stage 1's measurement**: (a) the `test107` non-object-`tableSchema` case — decode a malformed `tableSchema` as an empty schema per the spec's own "MUST act as if empty object" wording, instead of failing the table; (b) decide whether schema-by-reference (`tableSchema` as a URL string, `test034`/`test035`) is in scope for this stage or deferred again — it needs an I/O seam (fetch + inline) this program hasn't scoped yet, unlike the rest of Stage 2's pure-decode work; (c) decide whether a `CSVW_TableGroup []` (empty `"tables"` array, `test074`) should decode to `None` instead of `Some` once inheritance/validation semantics are in view. | Full metadata-document decode for all non-error-fixture metadata files | Stage 1 |
| 3 | **DONE.** `CSVW.URITemplate.fst` (Level 1 `{var}` simple string expansion + Level 2 `{#var}` fragment expansion; tokenizer mirrors `RML.Mapping.fst`'s `scan_template_acc`/`parse_template` idiom) | Unit-level, no manifest target alone — feeds Stage 6 (built directly, not gated on Stage 4/5) | none (independent of Stage 2) |
| 4 | `XSD.Datatypes.fst` extension: `date`/`time`/`gYear`-family parsing + `format`-facet interpreter — **NOT built in this pass.** `CSVW.Conversion.fst` maps a cell's `base` facet name straight to an `xsd:<name>` (or `rdf:HTML`/`rdf:XMLLiteral`/`csvw:JSON`) datatype IRI and uses the CELL'S RAW TEXT verbatim as the lexical form, per the csv2rdf algorithm's own "a datatype's format annotation is irrelevant to the conversion procedure ... the cell value has already been parsed" — but nothing upstream of this module does that parse, so `format`-driven reformatting (custom date patterns, `groupChar`/`decimalChar` numeric parsing, `Y`\|`N`-style booleans) never happens. **Measured impact (2026-07-05): grepping every csv2rdf-manifest FAIL's own metadata for a `"format"` key finds 105 of 251 failing tests carry one** — the single largest identified contributor to the Stage 6/7 fail count below. | Unit-level; feeds Stage 6's per-cell datatype resolution | none (independent of Stages 2-3) |
| 5 | **DONE.** CSV tokenizer — `RML.Sources.fst`'s `csv_parse_rows`/`csv_iterate` (RFC 4180), reused as-is, not forked, per this plan's own Fit-section directive | Unblocks row iteration | RML Stage 2 (shared dependency) — landed before this plan reached Stage 5, confirming the plan's own "coordinate, don't duplicate" framing |
| 6 | **DONE, both modes** — `CSVW.Conversion.fst`: csv2rdf minimal mode AND standard mode (`csvw:TableGroup`/`Table`/`Row`/`describes`/`rownum`/`url` wrapper). **Correction to this plan's own Stage 6 framing**: the Fit section's read of `csvt:noProv: true` (270/270 manifest-rdf entries) as "the suite tests minimal-shaped output almost exclusively" was WRONG, caught by reading the checked-in fixtures directly rather than trusting the manifest-option name — `noProv` turns out not to suppress the TableGroup/Table/Row wrapper at all (no fixture, minimal or standard, ever emits PROV-vocabulary triples in the first place); only 7 of 270 manifest-rdf entries carry the actual `csvt:minimal: true` flag that selects bare-triple output. Building minimal-only first would have passed almost nothing — both modes were required from the start, and both are implemented, selected per-test from `csvt:minimal`. | See measured csv2rdf score below | Stages 2 (partial — see gap note), 3, 5 |
| 7 | `CSVW.Convert.fst` — provenance/table-group triples (**already covered by Stage 6 above, folded in**) + warning detection (**not built** — `ToRdfTestWithWarnings` is scored identically to `ToRdfTest`, since this program has no signal for "processor MUST warn but still produce the same triples") | Folded into Stage 6's measured score; warning detection itself remains a gap | Stage 6 |
| 8 | `CSVW.Convert.fst` — csv2json (minimal, then full) | Not started this pass | Stages 6, 7 (shares most machinery) |
| 9 | `CSVW.Validate.fst` | `manifest-validation.jsonld`'s 282 entries — the largest manifest, majority-negative. Not started this pass — `NegativeRdfTest` entries in the csv2rdf manifest (below) already show the gap this stage would close: this program has no metadata/data validation layer, so a malformed document that still decodes structurally (Stage 1's deliberate leniency) proceeds straight to conversion and produces non-empty output where a negative fixture expects none. | Stage 2 (shares the metadata decoder) |
| 10 | **DONE.** `bin/csvw-runner/csvw_runner.ml` wiring — walks `manifest-rdf.ttl` (the Turtle mirror, parsed with the existing Turtle parser — no JSON-LD manifest reader needed), classifies `ToRdfTest`/`ToRdfTestWithWarnings`/`NegativeRdfTest`, compares via `RDF.Canonical.canonicalize_to_nquads` (same isomorphism-insensitive-to-blank-node-labels comparison `bin/rml-runner`/`bin/jsonld-runner` use). **Measured (2026-07-05, `bin/csvw-runner/csvw_runner`, standalone `ocamlfind` build against extracted modules, not yet wired into `build-ocaml.sh`): 19 pass, 251 fail (out of 270 manifest-rdf.jsonld entries)** — 0/58 `NegativeRdfTest` (no validation layer, see Stage 9), 9/76 `ToRdfTest`, 10/136 `ToRdfTestWithWarnings` pass. Of the 251 fails: at least 105 involve an unimplemented `format` facet (Stage 4 gap), at least 13 involve the unimplemented `separator`/list-valued-cell facet (not decoded by `CSVW.Metadata` at all), the remaining ~135 span negative-test detection (58, entirely Stage 9's gap), the one-level-only aboutUrl/propertyUrl/valueUrl inheritance approximation (`CSVW.Conversion.fst`'s own scope note — the suite's `test038`-`test049`-family inherited-property-propagation combinatorics specifically stress the full table-group→table→schema→column chain this pass doesn't build), and assorted per-fixture edge cases (subdirectory-rooted tests, boolean `Y`\|`N` lexical forms, etc). Stage-1 metadata decode re-measured with no regression: 287/293 documents decode to `Some csvw_metadata` (286 with >=1 table + `test074`'s valid-but-empty table group), matching the Stage 1 baseline exactly. | Stage 6 (first stage with a nontrivial signal) |
| 11 (indefinite) | `manifest-nonnorm.jsonld`'s 19 non-normative examples | Low priority — not conformance-gating per the manifest's own naming | Stage 10 |

### Two bugs found and fixed during Stage 6/10 (2026-07-05)

Both caught by comparing the runner's actual output against checked-in
fixtures, not by inspection — the exact discipline this project's
testing skill asks for:

1. **URI templates were resolving against the document base instead
   of the table's own URL.** csv2rdf's URI Template Properties
   (tabular-data-model §5.1.1) resolve a relative `aboutUrl`/
   `propertyUrl`/`valueUrl` expansion against "the URL of the table",
   not the outer conversion's base IRI — `CSVW.Conversion.fst`
   originally resolved all three against `base_iri` directly, which
   happened to work when a table's URL and the base coincided (no
   metadata, or metadata whose `url` matched the manifest's own
   directory) but produced a truncated IRI (missing the table's own
   path segment) whenever the metadata's `url` differed from the
   conversion's base — caught by `test011`, whose `aboutUrl:
   "#gid-{GID}"` produced `file://.../test011/#gid-1` instead of the
   expected `file://.../test011/tree-ops.csv#gid-1`. Fixed by
   resolving all three template outputs against
   `csvw_effective_table_url`'s result instead of `base_iri`.
2. **Subdirectory-rooted tests (`test032`/`test035`/`test118`/
   `test119`) used the wrong working directory.** The runner
   originally derived one global `test_dir` for the whole manifest
   run; tests whose `mf:action` points into a subdirectory (e.g.
   `test032/csv-metadata.json`) need their CSV/metadata files read
   relative to THAT subdirectory, not the shared `tests/` root — the
   symptom was total conversion failure (zero triples) for every
   subdirectory-rooted fixture. Fixed by deriving `test_dir` per-test
   from `Filename.dirname` of the resolved `mf:action` path.

A third finding, `test117` ("file-metadata not referencing file"),
is a **suite requirement, not a bug**: CSVW's metadata-discovery
algorithm (tabular-data-model §5.8) requires a same-directory
`<file>-metadata.json` to be IGNORED if it doesn't actually reference
the requested tabular file — implemented as `metadata_references_file`
in the runner, checked before falling back to a discovered (not
explicitly requested) metadata document.

## Perf/storage tie-ins

- **Row-at-a-time, not whole-table materialization** — the same call
  the RML plan makes for its logical sources. CSVW's own processing
  model is explicitly row-oriented (§5 of `tabular-data-model`
  describes annotation and conversion per-row), so `CSVW.Convert`'s
  public API should be `next_row`-shaped from the start, matching
  whatever shape the shared CSV tokenizer settles on for RML.
- **Output is triples/quads or a JSON tree** — no new storage design.
  csv2rdf's output is a peer input to RDFC-1.0 canonicalization, the
  COTTAS backend, or any other triple consumer already in the tree;
  csv2json's output can reuse whatever JSON serializer `Parser.JSON`
  or `JSONLD` already write.

## Open decisions

1. **csv2rdf vs csv2json relative priority.** The two manifests are
   near-identical in size and structure (270 entries each, same
   76/136/58 type split) and most of the conversion logic (row
   iteration, datatype resolution, URI template resolution) is shared
   — only the final serialization step differs (triples vs JSON
   object tree). Recommend building csv2rdf first (matches this
   project's RDF-first mission per CLAUDE.md) but treat csv2json as
   a near-zero-marginal-cost follow-on (Stage 8), not a separate
   program — confirm the shared-logic assumption once `CSVW.Convert`
   exists rather than assuming it holds for every corner case.
2. **Standard vs minimal mode, and which the suite actually
   rewards.** `noProv: true` on all 270 csv2rdf entries means the
   vendored suite's "standard" `ToRdfTest`/`ToRdfTestWithWarnings`
   types are scored without provenance triples in practice — confirm
   this holds across every entry (not just a sample) before deciding
   Stage 6 (minimal-shaped output) is sufficient to pass most of the
   suite, or whether some entries still expect the table-group
   wrapper node even with provenance triples suppressed.
3. **URI-template subset ceiling.** The corpus survey found only
   Level 1 + fragment-operator usage; if a future fixture (or a
   metadata document written by a real-world CSVW publisher, once
   this ships as a usable tool) needs `{+var}`/`{?var}`/prefix
   modifiers, extend `CSVW.URITemplate.fst`'s grammar rather than
   reaching for a general RFC 6570 library — same "extend the F\*
   subset, don't vendor a library" posture the RML plan took for
   JSONPath/XPath.
4. **Whether `CSVW.Validate.fst` shares a decoder with
   `CSVW.Metadata.fst` or duplicates checks.** Most validation-mode
   failures are "the metadata document doesn't decode" — if
   `CSVW.Metadata`'s decoder already returns a structured error
   (not just `None`), `CSVW.Validate` may be a thin wrapper that
   classifies decode failures rather than a parallel checker. Decide
   before Stage 9, not during it, to avoid writing the same
   constraint twice.
5. **The archived-upstream question: does a defect ever get fixed
   locally?** With `w3c/csvw` archived and read-only, any suite bug
   this program finds (in the RIF-defect tradition already documented
   in `current-state.md`) has no upstream PR path. Decide up front
   whether such defects get a local patch-and-document treatment
   (skip + comment, matching the RIF zip-defect precedent) or whether
   they block on a `w3id.org` successor repo appearing — check
   whether the CSVW Community Group's closure (also May 2026, per the
   same archival notice) left a designated successor before Stage 9
   needs the answer.
