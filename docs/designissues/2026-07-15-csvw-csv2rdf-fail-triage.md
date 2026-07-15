# CSVW csv2rdf fail triage — 2026-07-15

Baseline measured this session on the committed `bin/linux-x86_64/csvw_runner`
(`.claude-runs/csvw-baseline-2026-07-15.log`): **218 pass, 52 fail (out of
270)**. This note triages all 52 named fails into root-cause families by
reading each family's representative fixture (metadata JSON + expected
`.ttl`) against the actual `CSVW.Metadata.fst`/`CSVW.Conversion.fst` decode
and conversion logic, and against the W3C csv2rdf test README's own
assertions (`third_party/testing/csvw/tests/README.md`) and the vendored
manifest's `rdfs:comment` on each test entry (which quotes the exact spec
condition under test).

Every fail in this manifest carries `csvt:option [ csvt:noProv true ]` —
that option is a red herring for triage purposes: it applies to all 270
entries (218 passing + 52 failing alike) and, per the suite's own README
("Do not output provenance triples ... these triples are optional and make
comparison using RDF isomorphism impossible"), is a no-op for a processor
that (like this one) never emits non-comparable timestamp/tool provenance
triples in the first place. It does not explain any of the 52 fails.

## Family table

| Family | Count | Named tests | Root cause (one sentence) | Fix sketch | F* module |
|---|---|---|---|---|---|
| A. Table/table-group-level inherited + common properties dropped (Stage 2) | 15 | test038, test039, test047, test048, test049, test126, test148, test149, test275, test276, test277, test278, test305, test306, test307 | `csvw_table`/`csvw_metadata`'s `CSVW_TableGroup` never decoded a value set directly on the table or table-group JSON object (aboutUrl/propertyUrl/valueUrl/lang/null/separator/datatype, or arbitrary rdfs:/dc:-style common properties) — only tableSchema-level and column-level values reached `CSVW.Conversion`, so e.g. `{"url": "x.csv", "aboutUrl": "#row-{_row}", ...}` silently lost its `aboutUrl`. | **FIXED this session.** Added `csvw_inherited_props` (7-field record: about/property/value_url, lang, null, separator, datatype) + `csvw_group_meta` (group common properties + inherited defaults) to `CSVW.Metadata.fst`; decoded at tableSchema/table/table-group level via one shared `csvw_decode_inherited`; merged group→table→schema→column (most-specific-wins) in `CSVW.Conversion.fst`'s `csvw_merge_inherited`/`csvw_build_col_specs`/`csvw_col_spec_of_column`; threaded `grp_inherited`/`grp` through `csvw_convert_table_{minimal,standard}` and `csvw_convert_document_{minimal,standard}`; group common properties attached to the `csvw:TableGroup` node via the existing `csvw_table_common_triples` helper; `lang` applied only when the effective datatype is `xsd:string` (`csvw_build_literal_lang`, RDF 1.1's langString-iff-lang-tag rule); `null` checked alongside the existing `""` no-value rule in `csvw_cell_object`. | `CSVW.Metadata.fst`, `CSVW.Conversion.fst`, `bin/csvw-runner/csvw_runner.ml` (I/O glue: extract `csvw_group_meta` from `CSVW_TableGroup`'s new second field, pass to the two document-level entry points) |
| B. Metadata discovery (implicit/directory/linked) still mismatches after correct document is found | 4 | test011, test012, test014, test016 | The runner's `discover_metadata`/explicit-`csvt:implicit` path already locates the right metadata document (file/directory metadata is implemented, and these fixtures don't need HTTP); the remaining diff is unexplained — not yet isolated to a specific field or code path (test014/016 additionally use `csvt:httpLink`, i.e. Link-header simulation, which the runner has no HTTP layer for at all, so those two may be a distinct, currently out-of-scope sub-case). | Needs a live `-v` diff (temporarily widen `csvw_runner.ml`'s `head` truncation) against `test011/result.ttl` et al. to pin the exact triple-level delta before proposing a fix. | `CSVW.Metadata.fst` or `bin/csvw-runner/csvw_runner.ml`, TBD |
| C. Complex multi-subject/virtual-column/annotation fixtures | 4 | test032, test033, test036, test037 | events-listing.csv (virtual columns + multiple `aboutUrl`-distinguished subjects per row) and tree-ops-ext.csv (`notes`/`oa:Annotation` common-property object, `suppressOutput`, boolean `Y\|N`-style format, `xml` datatype, named `@id` table node) each combine several features at once; per the program plan's own Stage-6 measurement this combinatorial case was flagged as needing "the full table-group→table→schema→column chain" (partially addressed by family A) plus per-feature work (annotation-object common properties, `@id` node identity) this pass didn't touch. | Isolate per-fixture: does family A's inheritance fix already flip these, or is `@id`-as-real-IRI (not synthesized blank node) and/or nested-object common-property emission still missing? | `CSVW.Metadata.fst`, `CSVW.Conversion.fst` |
| D. Schema-by-reference (`tableSchema` as a URL string) | 2 | test034, test035 | `csvw_decode_table_schema` only accepts `tableSchema` as an inline JSON object; these two fixtures give it as a bare URL string (`"tableSchema": "gov.uk/schema/professions.json"`) pointing at an external schema document — explicitly flagged out of scope in the program plan's Stage 1 measurement (needs a local-file fetch+inline I/O seam this program hasn't scoped). | Add a schema-by-reference resolution step (read + decode the referenced local JSON file, inline as if it had been nested) — I/O-glue-shaped work in the runner, semantics in `CSVW.Metadata`. | `CSVW.Metadata.fst`, `bin/csvw-runner/csvw_runner.ml` |
| E. Malformed-metadata-shape graceful-degradation warnings | 5 | test097, test100, test101, test102, test107 | tabular-metadata requires that a property with the wrong JSON *type* (an int where an array is expected, `tableSchema: 1`, etc.) degrade to "as if absent/empty" plus a warning, rather than failing the whole document; `CSVW.Metadata`'s leniency policy already does this for LEAF values but not uniformly for these container-shaped cases (test107's `"tableSchema": 1` was flagged as a known one-line gap back in the Stage 1 measurement). | Treat a non-object `tableSchema`/non-array `columns`/`foreignKeys` as "empty", not a decode failure, matching the spec's literal "MUST act as if it was an empty object/array" wording. | `CSVW.Metadata.fst` |
| F. File/directory/link metadata discovery edge cases (query strings, precedence) | 5 | test116, test118, test121, test122, test123 | `mf:action`s with a `?query` suffix or non-referencing discovered documents exercise discovery-priority and file-path-vs-logical-URL edge cases (e.g. `test116.csv?query` must still open the real on-disk `test116.csv`, but the returned RDF must show `test116.csv?query` in the IRIs) that the current `file_iri_to_path`/`discover_metadata` pairing in the runner does not handle — this is I/O-glue-shaped, not an F* semantics gap. | Split "path to open on disk" from "logical table URL for IRI construction" in the runner: strip a `?query`/fragment before `Sys.file_exists`/`read_file`, but keep it in the value passed as `fallback_url`/`base_iri`. | `bin/csvw-runner/csvw_runner.ml` |
| G. Required-column / cell validation warnings | 2 | test125, test127 | tabular-metadata's `required` column annotation (an empty required cell is a validation ERROR) and table/embedded-metadata schema-compatibility checking are not implemented — `col_required` is decoded (`CSVW.Metadata`) but never consulted by `CSVW.Conversion`. | Add a required-cell check in `csvw_cell_object`/`csvw_process_cell` (empty text + `cs_required` → warning path) and an embedded-vs-referenced schema compatibility check. | `CSVW.Conversion.fst` |
| H. Column-name restriction (invalid chars / reserved `_` prefix) | 2 | test130, test131 | A column `name` that isn't a valid URI Template variable (contains spaces, or starts with `_`) must be treated as absent for default-propertyUrl purposes, falling back to the column's percent-encoded `titles` instead — `CSVW.Metadata`/`CSVW.Conversion` currently use `col_name` verbatim with no validity check. | Add a URI-Template-variable-name validity predicate; when `col_name` fails it, drop to `csvw_col_spec_of_column`'s title-based fallback (already exists for the *absent* case, just needs to also fire on the *invalid* case) and emit a warning. | `CSVW.Metadata.fst` or `CSVW.Conversion.fst` |
| I. Non-builtin / absolute-URL datatype validation warnings | 3 | test150, test151, test238 | A `datatype`/`datatype.base` value that names neither a built-in datatype nor a well-formed absolute URL must fall back to a default and warn; `csvw_decode_datatype`/`csvw_datatype_iri` currently pass such strings through without validating against the built-in-datatype closed vocabulary. | Add a built-in-datatype-name membership check (reuse `XSD.Datatypes`' known-name table) with a string-non-builtin-but-absolute-URL escape hatch. | `CSVW.Metadata.fst`, `CSVW.Conversion.fst` |
| J. Duration format regex facet | 1 | test194 | The `datatype.format` regex pattern for `duration`/`dayTimeDuration`/`yearMonthDuration` needs a regex-matching engine; `CSVW.Formats`' UAX-35 engine covers number/date/boolean formats only, not arbitrary regex. | Out of scope until a regex engine is available to call out to (per the suite's own `remaining` note in `.github/test-suites/csvw.yaml`). | `CSVW.Formats.fst` (blocked on a regex engine) |
| K. `rowTitles` not implemented | 2 | test235, test236 | The `rowTitles` table-schema annotation (insert `csvw:title` triples on the row node from a named column's cell values) has no decode or emission path at all. | Decode `rowTitles` (list of column names) on `csvw_table_schema`; emit `csvw:title` triples in `csvw_row_triples_standard`. | `CSVW.Metadata.fst`, `CSVW.Conversion.fst` |
| L. Cross-table foreign-key validation (NegativeRdf) | 2 | test252, test253 | These fixtures expect the processor to detect a broken `foreignKeys` reference (missing destination column/table) and produce NO output; `CSVW.Conversion` doesn't implement foreign-key referential-integrity checking at all, so it converts each table independently and produces non-empty output. | Add a post-decode cross-table FK validation pass (each table's `foreignKeys` reference resolves to an existing column in an existing sibling table) that short-circuits to empty output on failure — this is exactly the `CSVW.Validate` (Stage 9) gap the program plan already names. | New `CSVW.Validate.fst` (Stage 9) |
| M. HTTP-based metadata discovery / `.well-known/csvm` | 2 | test259, test260 | Both need Link-header simulation or the `/.well-known/csvm` site-wide-configuration well-known path — a networked-protocol feature explicitly parked by owner directive alongside SPARQL Protocol (`.github/test-suites/csvw.yaml`'s `remaining` list). | Out of scope by owner directive. | n/a |
| N. `@type` CURIE built-in-term expansion in common properties | 1 | test263 | A common-property's nested `@type` value that names a CSVW built-in term (e.g. `"Table"`, unprefixed) must expand to `csvw:Table`; the common-property-object emission logic only expands prefixed names (`prefix:local`) and absolute URLs, not bare built-in terms. | Add the CSVW built-in-term table (`Table`, `TableGroup`, `Row`, ...) as a third `@type`-expansion case alongside prefixed-name and absolute-URL. | `CSVW.Conversion.fst` |
| O. `@base` override in `@context` | 1 | test273 | A two-element `@context` array's second element can carry `"@base"`, overriding the metadata document's own location as the base for resolving other URLs in the document; the context array is currently only inspected for `@language` (see `CSVW.Metadata.fst`'s banner: "every ... `@context` ... uses either the bare-string sentinel ... or the two-element array form ... never an arbitrary remote context"), `@base` inside it is ignored. | Read `@base` out of the context array's second element in the runner (base-IRI computation is already I/O-glue-shaped there) and fold it into `base_iri` before calling `CSVW.Conversion`. | `bin/csvw-runner/csvw_runner.ml` |
| P. `header=false` dialect option + schema compatibility | 1 | test023 | Combines an explicit `csvt:metadata` override, `dialect.header` (bool) vs `headerRowCount` precedence, and embedded/referenced schema compatibility — a narrower single-fixture case of family E/G's shape gaps, not yet isolated further. | Needs a live diff to confirm which specific piece (header-row-count precedence vs. something else) is the actual delta. | `CSVW.Conversion.fst`, TBD |

**Total: 15 + 4 + 4 + 2 + 5 + 5 + 2 + 2 + 3 + 1 + 2 + 2 + 2 + 1 + 1 + 1 = 52.**

## What this session fixed

Family A — see the F* diff in `CSVW.Metadata.fst` and
`CSVW.Conversion.fst`. Post-fix measurement (committed binary, this
session): see the commit message for the exact before/after score and
the named pass-flip list.

One regression-guard rider landed with it: the first build of the
inheritance chain regressed test041 ("invalid lang":
`"lang": "notavalidlanguagetag"` at group level) and test046 ("invalid
datatype": `"datatype": "anySimpleType"`) — both fixtures set an
INVALID value for an inherited property, which the pre-change code
passed only by ignoring the level entirely. tabular-metadata section
4's graceful-degradation rule ("behave as if the property had not been
specified", quoted verbatim in both tests' manifest comments) is now
implemented in `csvw_decode_inherited`: a `lang` that is not
BCP47-shaped (`csvw_lang_tag_ok`) and a string `datatype` naming
anything outside the section 5.11.1 built-in list
(`csvw_builtin_datatype_names` — note `anySimpleType` is not in it)
decode to None, exactly as if absent. Column-level decode is
unchanged (families H/I above still stand for the column-level
variants of these checks).

## What's next (by expected yield, unverified — no fixture-level diff done for these counts beyond the family table above)

Families E and F (5 tests each) are the next-largest, but neither is
"trivial after family A" — E needs container-shape leniency rules in
`CSVW.Metadata.fst`'s decoder, F needs runner-side query-string/discovery
plumbing (`bin/csvw-runner/csvw_runner.ml`) — genuinely separate scope,
which is why this session did not fold either into the family-A commit
(per the task's "two largest only if the second is trivial" rule).
Family L (cross-table foreign-key validation) is the one piece of the
long-documented `CSVW.Validate.fst` (Stage 9) gap this manifest actually
exercises with only 2 tests, cheap to isolate as its own follow-up.
