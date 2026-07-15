# CSVW csv2rdf fail triage — 2026-07-15

Burndown ledger. Score history (all measured on freshly rebuilt
`bin/linux-x86_64/csvw_runner`, labelled per anti-pattern #25):

- Round 0 baseline: 218 pass, 52 fail (out of 270) —
  `.claude-runs/csvw-baseline-2026-07-15.log`.
- Round 1 (family A landing, commit 6f5544eb): 228 pass, 42 fail (out
  of 270). Named flips: test101 test121 test122 test125 test126
  test127 test275 test276 test277 test305.
- Round 2 (families E + F + one family-B flip, this landing): **235
  pass, 35 fail (out of 270)**. Named flips: test097 test100 test107
  (family E), test116 test118 test123 (family F), test012 (family B,
  via the same discovery-candidate fix as family F). Zero regressions
  either round (fail-set diff against the previous round's log).

Baseline for the original triage below: **218 pass, 52 fail (out of
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
| A. Table/table-group-level inherited + common properties dropped (Stage 2) | 15 | test038, test039, test047, test048, test049, test126, test148, test149, test275, test276, test277, test278, test305, test306, test307 | `csvw_table`/`csvw_metadata`'s `CSVW_TableGroup` never decoded a value set directly on the table or table-group JSON object (aboutUrl/propertyUrl/valueUrl/lang/null/separator/datatype, or arbitrary rdfs:/dc:-style common properties) — only tableSchema-level and column-level values reached `CSVW.Conversion`, so e.g. `{"url": "x.csv", "aboutUrl": "#row-{_row}", ...}` silently lost its `aboutUrl`. | **PARTIALLY FIXED (round 1, commit 6f5544eb).** The inheritance-chain machinery landed and flipped 5 of this family's 15 (test126, test275, test276, test277, test305) plus 5 tests filed under other families; the OTHER 10 named here (test038, test039, test047-049, test148, test149, test278, test306, test307) still fail post-round-2 — the chain alone wasn't their whole delta; each needs a fresh `-v` diff to re-triage what remains (likely per-feature gaps layered on top: `describes` linking for aboutUrl-grouped subjects, list-value ordering, title-language intersection). Round-1 change detail: added `csvw_inherited_props` (7-field record: about/property/value_url, lang, null, separator, datatype) + `csvw_group_meta` (group common properties + inherited defaults) to `CSVW.Metadata.fst`; decoded at tableSchema/table/table-group level via one shared `csvw_decode_inherited`; merged group→table→schema→column (most-specific-wins) in `CSVW.Conversion.fst`'s `csvw_merge_inherited`/`csvw_build_col_specs`/`csvw_col_spec_of_column`; threaded `grp_inherited`/`grp` through `csvw_convert_table_{minimal,standard}` and `csvw_convert_document_{minimal,standard}`; group common properties attached to the `csvw:TableGroup` node via the existing `csvw_table_common_triples` helper; `lang` applied only when the effective datatype is `xsd:string` (`csvw_build_literal_lang`, RDF 1.1's langString-iff-lang-tag rule); `null` checked alongside the existing `""` no-value rule in `csvw_cell_object`. | `CSVW.Metadata.fst`, `CSVW.Conversion.fst`, `bin/csvw-runner/csvw_runner.ml` (I/O glue: extract `csvw_group_meta` from `CSVW_TableGroup`'s new second field, pass to the two document-level entry points) |
| B. Metadata discovery (implicit/directory/linked) still mismatches after correct document is found | 4 | test011, test012, test014, test016 | The runner's `discover_metadata`/explicit-`csvt:implicit` path already locates the right metadata document (file/directory metadata is implemented, and these fixtures don't need HTTP); the remaining diff is unexplained — not yet isolated to a specific field or code path (test014/016 additionally use `csvt:httpLink`, i.e. Link-header simulation, which the runner has no HTTP layer for at all, so those two may be a distinct, currently out-of-scope sub-case). | **PARTIALLY FIXED (round 2).** test012 was actually a family-F-shaped bug — the runner's directory-metadata candidate name was the spec-literal `metadata.json`, but this corpus names it `csv-metadata.json` (`<extension>-metadata.json`); the round-2 discovery fix flipped it. test014/test016 are `csvt:httpLink` (HTTP-based discovery, out of scope by owner directive). test011 remains: its file-metadata document IS found and mostly converts (the `-v` diff heads are identical); still needs the widened-diff isolation pass. | `CSVW.Metadata.fst` or `bin/csvw-runner/csvw_runner.ml`, TBD |
| C. Complex multi-subject/virtual-column/annotation fixtures | 4 | test032, test033, test036, test037 | events-listing.csv (virtual columns + multiple `aboutUrl`-distinguished subjects per row) and tree-ops-ext.csv (`notes`/`oa:Annotation` common-property object, `suppressOutput`, boolean `Y\|N`-style format, `xml` datatype, named `@id` table node) each combine several features at once; per the program plan's own Stage-6 measurement this combinatorial case was flagged as needing "the full table-group→table→schema→column chain" (partially addressed by family A) plus per-feature work (annotation-object common properties, `@id` node identity) this pass didn't touch. | Isolate per-fixture: does family A's inheritance fix already flip these, or is `@id`-as-real-IRI (not synthesized blank node) and/or nested-object common-property emission still missing? | `CSVW.Metadata.fst`, `CSVW.Conversion.fst` |
| D. Schema-by-reference (`tableSchema` as a URL string) | 2 | test034, test035 | `csvw_decode_table_schema` only accepts `tableSchema` as an inline JSON object; these two fixtures give it as a bare URL string (`"tableSchema": "gov.uk/schema/professions.json"`) pointing at an external schema document — explicitly flagged out of scope in the program plan's Stage 1 measurement (needs a local-file fetch+inline I/O seam this program hasn't scoped). | Add a schema-by-reference resolution step (read + decode the referenced local JSON file, inline as if it had been nested) — I/O-glue-shaped work in the runner, semantics in `CSVW.Metadata`. | `CSVW.Metadata.fst`, `bin/csvw-runner/csvw_runner.ml` |
| E. Malformed-metadata-shape graceful-degradation warnings | 5 | test097, test100, test101, test102, test107 | tabular-metadata requires that a property with the wrong JSON *type* (an int where an array is expected, `tableSchema: 1`, etc.) degrade to "as if absent/empty" plus a warning, rather than failing the whole document; `CSVW.Metadata`'s leniency policy already does this for LEAF values but not uniformly for these container-shaped cases (test107's `"tableSchema": 1` was flagged as a known one-line gap back in the Stage 1 measurement). | **FIXED (rounds 1+2) except test102.** test101 flipped with round 1. Round 2 (`CSVW.Metadata.fst` + `CSVW.Conversion.fst`): a non-object `tableSchema` decodes to an EMPTY schema (test107); a non-object `foreignKeys` array ITEM is ignored, object items still shape-checked (test097, `csvw_fks_all_valid`); a non-string `@id` no longer hard-rejects the document (`csvw_obj_id_ok`, test102's precondition); and a user-supplied schema that degrades to zero columns names its columns positionally (`_col.N`, `csvw_col_specs_positional`) instead of from the CSV header text (test100/test107 — header text naming only applies when NO user schema exists at all). test102 still fails, but for a different reason now: its expected output identifies the table node by the metadata document's own URL (invalid link property degrades to "" and resolves against base), which needs real-IRI table-node identity — family C's `@id` gap, where it now belongs. | `CSVW.Metadata.fst`, `CSVW.Conversion.fst` |
| F. File/directory/link metadata discovery edge cases (query strings, precedence) | 5 | test116, test118, test121, test122, test123 | `mf:action`s with a `?query` suffix or non-referencing discovered documents exercise discovery-priority and file-path-vs-logical-URL edge cases (e.g. `test116.csv?query` must still open the real on-disk `test116.csv`, but the returned RDF must show `test116.csv?query` in the IRIs) that the current `file_iri_to_path`/`discover_metadata` pairing in the runner does not handle — this is I/O-glue-shaped, not an F* semantics gap. | **FIXED (rounds 1+2).** test121/test122 flipped with round 1. Round 2 (`bin/csvw-runner/csvw_runner.ml`, I/O glue only): `strip_query_frag` splits "path to open on disk" from "logical table URL" — CSV disk reads strip `?query`/`#frag`, while `fallback_url`/`tbl_url` keep it for IRI construction (test116/test118); and the directory-metadata discovery candidate is now `<extension>-metadata.json` (`csv-metadata.json` in this corpus — its actual naming convention; the spec-literal `metadata.json` appears in ZERO fixtures), which flipped test123 (and family B's test012). | `bin/csvw-runner/csvw_runner.ml` |
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

## Remaining-fail census after round 2 (35 fails)

| Family | Remaining | Named tests |
|---|---|---|
| A (residue after the inheritance-chain landing — needs re-triage) | 10 | test038, test039, test047, test048, test049, test148, test149, test278, test306, test307 |
| B (test011 unexplained; test014/016 httpLink = out of scope) | 3 | test011, test014, test016 |
| C (complex multi-subject/virtual/annotation, incl. `@id` node identity) | 5 | test032, test033, test036, test037, + test102 (moved from E) |
| D (schema-by-reference) | 2 | test034, test035 |
| H (column-name restriction) | 2 | test130, test131 |
| I (non-builtin datatype validation) | 3 | test150, test151, test238 |
| J (duration regex — blocked on regex engine) | 1 | test194 |
| K (rowTitles) | 2 | test235, test236 |
| L (cross-table FK validation, NegativeRdf) | 2 | test252, test253 |
| M (HTTP `.well-known` discovery — out of scope by owner directive) | 2 | test259, test260 |
| N (`@type` built-in-term expansion) | 1 | test263 |
| O (`@base` in `@context`) | 1 | test273 |
| P (`header=false` + schema compatibility) | 1 | test023 |

Family G has no row: its named tests (test125, test127) flipped with
round 1's landing, so family G as originally scoped is DONE.
Row sum: 10 + 3 + 5 + 2 + 2 + 3 + 1 + 2 + 2 + 2 + 1 + 1 + 1 = 35.
Out-of-scope by directive/blocker: 5 (test014, test016, test194,
test259, test260). Actionable remainder: 30.

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

## What round 2 fixed (2026-07-15, branch csvw-burndown-2)

Families E (minus test102, re-filed under C) and F in full, plus
family B's test012 — see the updated family-table rows above for the
per-fix detail and the remaining-fail census for what's left. F*
changes in `CSVW.Metadata.fst` (non-object `tableSchema` -> empty
schema; non-object FK array items ignored; non-string `@id` degrades
instead of rejecting) and `CSVW.Conversion.fst`
(`csvw_col_specs_positional` for schema-present-but-zero-columns);
runner I/O changes in `bin/csvw-runner/csvw_runner.ml`
(`strip_query_frag` disk/logical-URL split; `<extension>-metadata.json`
directory-discovery candidate). Both F* modules verify clean under
z3 4.13.3, no --lax, no admits.

## What's next (by expected yield)

Family A's 10-test residue is the largest block but needs a re-triage
pass first (the inheritance chain alone was not their delta — get a
fresh `-v` diff per fixture before coding). Of the well-understood
families: I (3 tests, datatype-name validation against the built-in
table — the column-level twin of the round-1 inherited-datatype
check), H (2, column-name validity fallback), K (2, rowTitles), and
L (2, the `CSVW.Validate.fst` Stage 9 cross-table FK check) are each
small and independently commit-sized. Family C (5 incl. test102)
hinges on real-IRI `@id` node identity for table/group nodes — a
CSVW.Conversion signature change, bigger than the others.
