# Lean 4 coverage against the F\* tree: RIF, RML, CSVW validation, RDF/XML, GeoSPARQL, RDF 1.2 entailment

Date: 2026-09-07. Branch `wt/lean-cov-rif`.

The Lean 4 tree is the intended full-scope target (CLAUDE.md, owner
2026-08-29). Six areas are behind the F\* tree. This record lists the
undecided, failing and unrun tests FIRST, by name, so a later commit
can say which of them it turned green. Every score below is measured
in this worktree, not quoted from a dashboard.

Method for each area: run the Lean probe, run or read the F\* ledger,
subtract. Where the Lean side has no probe at all, the gap is the whole
suite and the first step is a probe, not an engine change.

## How a probe finds its fixtures

Some probes were run from the repository root
(`lake -d formal/lean4 exe NAME`, fixture path `third_party/...`) and
some from `formal/lean4` (`lake exe NAME`, fixture path
`../../third_party/...`). A probe that hard-coded one of the two
printed `directory not present` in the other, which reads as a missing
fixture and not as a wrong current directory: `l4rdfxml-probe` reported
no numbers at all from the repository root.

`Harness/Fixtures.lean` resolves a ROOT-RELATIVE default against the
prefixes `""`, `"../../"` and `"../../../"` in that order. An argument
the caller gives is used as is, because it is relative to the caller's
own directory. `l4rif`, `l4rml` and `l4rdfxml-probe` now resolve their
defaults through it, and every probe added here does the same.

## 1. RIF Core

Corpus: `third_party/testing/rif-core-suite/Core_v1.22/Approved`, 46
cases (29 PositiveEntailment, 5 NegativeEntailment, 3 PositiveSyntax,
3 NegativeSyntax, 6 ImportRejection).

* **Lean `l4rif` before**: 24 pass, 2 fail (out of 26 decided); 13
  undecided, 1 not read, 6 import-rejection not attempted.
* **F\* `rif_runner` part 2** (`bin/rif-runner/README.md`, measured
  2026-07-10): 42 pass, 0 fail, 1 local-override, 3 skip (out of 46).

### The 2 Lean failures

| test | Lean verdict | F\* verdict |
| --- | --- | --- |
| `PositiveEntailmentTest/RDF_Combination_Constant_Equivalence_4` | not entailed, and must be | pass |
| `PositiveEntailmentTest/EBusiness_Contract` | not entailed, and must be | pass (dateTime slice: `is-literal-dateTime`, `func:subtract-dateTimes`, `func:days-from-duration`, n-ary reification for the arity-3 `cpt:delivered`) |

### The 13 Lean undecided

Blocked on a built-in outside `L4Factoidal/RIF/Builtins.lean`:

* `PositiveEntailmentTest/Builtins_Numeric`
* `PositiveEntailmentTest/Builtins_String`
* `PositiveEntailmentTest/Builtins_Binary`
* `PositiveEntailmentTest/Builtins_PlainLiteral`
* `PositiveEntailmentTest/Builtins_XMLLiteral`
* `PositiveEntailmentTest/Builtins_List`
* `PositiveEntailmentTest/Builtins_Time`
* `PositiveEntailmentTest/Factorial_Forward_Chaining`
* `PositiveEntailmentTest/IRI_from_RDF_Literal`

Blocked on an entailment regime the port does not implement:

* `PositiveEntailmentTest/Modeling_Brain_Anatomy` (OWL-Direct)
* `PositiveEntailmentTest/OWL_Combination_Vocabulary_Separation_Inconsistency_1`
* `PositiveEntailmentTest/OWL_Combination_Vocabulary_Separation_Inconsistency_2`
* `NegativeEntailmentTest/Non-Annotation_Entailment`

Of these, F\* skips exactly two with a named built-in
(`Builtins_List`, and `Builtins_Time` naming `is-literal-dateTimeStamp`)
plus `NestedListsAreNotFlatLists`. The other ten are F\* passes, so
they are Lean gaps rather than shared limits.

### The 1 Lean not-read

* `PositiveEntailmentTest/RDF_Combination_Constant_Equivalence_Graph_Entailment`
  — the conclusion is an RDF GRAPH (`-conclusion.ttl`), not a RIF
  condition; no `-conclusion.rifps` exists. F\* counts it as a
  local-override and evaluates it through a graph-to-BGP translation.

### The 6 import-rejection cases, not attempted

`Multiple_Context_Error`, `OWL_Combination_Invalid_DL_Formula`,
`OWL_Combination_Invalid_DL_Import`, `RDF_Combination_Invalid_Constant_1`,
`RDF_Combination_Invalid_Constant_2`, `RDF_Combination_Invalid_Profiles_1`.
F\* decides all six in `RIF.Core.Conformance.fst`.

## 2. RML

* **Lean `l4rml` before**: 60 pass, 0 fail, 0 comparison-gave-up (out
  of 60 compared); 1 not read; 15 negative cases not attempted.
* **F\* rml-core**: 76 pass (out of 76).

The 16 uncompared cases are therefore accounted for, not lost:

* **1 not read** — `RMLTC0027b-JSON`: the fixture's own `output.nq`
  writes `<http://example.com/Person/Emily Smith>`, and an IRIREF may
  not contain a space (Turtle §3, N-Quads §7). The fixture is at fault,
  and the F\* runner accepts it. A decision is needed on whether the
  Lean N-Quads reader relaxes for this corpus or the case stays not-read
  with the reason named.
* **15 negative** — the mapping must be REJECTED. `Harness/RmlRun.lean`
  has no mapping validator, so it makes no claim about them.

`rml-io` (`third_party/testing/rml-modules/rml-io/test-cases`, 84
directories) is not run by Lean at all. F\*: 17 pass, 1 fail, 55
logical-target skips (out of 73).

## 3. CSVW validation

* **Lean before**: no run. `l4csvw-rdf` is 270 pass of 270 and
  `l4csvw-json` is 270 pass of 270, but `L4Factoidal/CSVW/Validate.lean`
  (524 lines) is exercised only by its own `#guard`s.
* **F\* `csvw_runner --validate`**: 281 pass, 1 fail (out of 282). The
  single fail is `test308`, and `.github/test-suites/csvw-validation.yaml`
  records why: a value-agnostic rule cannot reject `test308`'s
  non-built-in absolute-URL datatype string without also rejecting
  `test238`, a WarningValidationTest that must conform.

Manifest `third_party/testing/csvw/tests/manifest-validation.jsonld`:
282 entries — 76 `PositiveValidationTest`, 61 `WarningValidationTest`,
145 `NegativeValidationTest`. The whole 282 is the gap.

## 4. RDF/XML

* **Lean `l4rdfxml-probe`**: parse-positive 132 pass, 0 fail (of 132);
  reject-negative 41 pass, 0 fail (of 41); eval-isomorphic 130 pass,
  2 fail (of 132).
* **F\***: does NOT run either case. Both are COMMENTED OUT of the
  vendored manifest
  (`third_party/testing/w3c/rdf/rdf11/rdf-xml/manifest.ttl`, lines 166,
  167 and 1574-1596), so the F\* runner never reaches them. The claim
  that the F\* tree passes both, written into this record on 2026-09-07
  from the task brief, was wrong and is corrected here. The Lean probe
  is directory-driven rather than manifest-driven, which is why it sees
  them at all.

The 2 failures:

* `rdfms-xml-literal-namespaces/test001.rdf` — 1 triple produced, 1
  expected, not isomorphic.
* `rdfms-xml-literal-namespaces/test002.rdf` — 2 triples produced, 2
  expected, not isomorphic.

Both are the `rdf:parseType="Literal"` namespace-fixup rule
(RDF/XML §7.2.17): in-scope namespace declarations that the literal's
own markup uses must be copied onto the literal's outermost element
before canonicalisation.

## 5. GeoSPARQL

* **Lean before**: no probe. `L4Factoidal/Geo/` holds `Wkt`, `Types`,
  `BBox`, `BBoxSound`, `Order`, `Topology`, `Functions` and the two
  `#guard` files `Tests.lean` and `WktTests.lean`,
  `FunctionsTests.lean`.
* **F\* `geosparql-v0`**: 37 pass (of 37).

The F\* 37 is not a W3C corpus. It is
`tests/unit/geosparql_v0_unit.ml`, a hand-built pin file in three
groups: (A) WKT parse to ADT to serialise to re-parse round trips,
(B) Simple Features predicates against hand-computed fixtures including
a point exactly on a polygon edge, (C) `geof:distance` and
`geof:envelope` spot checks. The Lean gap is a scored run over the same
assertions, so the two trees' numbers compare.

## 6. RDF 1.2 entailment (rdf-semantics)

* **Lean before**: no run of the manifest. `l4rdfs-semi` exists but is
  a semi-naive closure probe, not this suite.
* **F\* `rdf-semantics`**: 41 pass, 3 fail, 3 skip (out of 47).

Manifest `third_party/testing/w3c/rdf/rdf12/rdf-semantics/manifest.ttl`:
47 entries — 32 `mf:PositiveEntailmentTest`, 15
`mf:NegativeEntailmentTest`. Each entry carries `mf:entailmentRegime`,
`mf:recognizedDatatypes` and `mf:unrecognizedDatatypes`, which a runner
must read: a datatype named unrecognized must not license a D-entailment.
The whole 47 is the gap.

## Status

Final for the 2026-09-07 session. Every score below was measured in
this worktree by running the probe, not quoted from a report.

| area | before | after | F\* comparison |
| --- | --- | --- | --- |
| RIF Core | 24 pass, 2 fail (of 26 decided); 13 undecided, 1 not read, 6 not attempted | 33 pass, 1 fail (of 34 decided); 11 undecided, 0 not read, 1 local override | 42 pass, 0 fail, 1 local override, 3 skip (of 46) |
| RML core | 60 pass (of 60 compared); 1 not read, 15 not attempted | unchanged | 76 pass (of 76) |
| RML io | not run | not run | 17 pass, 1 fail, 55 skip (of 73) |
| CSVW validation | not run | 266 pass, 14 fail, 2 skip (of 282) | 281 pass, 1 fail (of 282) |
| RDF/XML | 130 pass, 2 fail (of 132 eval-isomorphic) | 132 pass, 0 fail (of 132) | does not run these two |
| GeoSPARQL | no probe | 37 pass, 0 fail, 0 skip (of 37) | 37 pass (of 37) |
| rdf-semantics | not run | 22 pass, 10 fail, 0 skip, 15 unsupported (of 47) | 41 pass, 3 fail, 3 skip (of 47) |

### Closed

* **RDF/XML** — both `rdfms-xml-literal-namespaces` cases. See the
  section below.
* **GeoSPARQL** — all 37 F\* assertions ported, none skipped
  (`lake exe l4geo`). Needed a WKT serialiser, a parenthesised
  MULTIPOINT component parser, `sfOverlaps` with the Polygon/Polygon
  cases of `sfIntersects`/`sfWithin`, and `geof:distance`/
  `geof:envelope`, all fuel-bounded rather than `partial`.
* **RIF** — the 6 `ImportRejectionTest` cases,
  `OWL_Combination_Vocabulary_Separation_Inconsistency_1` and `_2`, and
  `RDF_Combination_Constant_Equivalence_Graph_Entailment`.
  `RDF_Combination_Constant_Equivalence_4` moved from FAIL to the
  local-override bucket, which is where the F\* tree already had it.

### Open, by test id

**RIF (12 cases short of F\*).** One fail: `EBusiness_Contract`, which
needs the dateTime slice (`is-literal-dateTime` accepting `xs:date`
operands at midnight, `func:subtract-dateTimes`,
`func:days-from-duration`) and n-ary reification for its arity-3
`cpt:delivered` relation. Eleven undecided: `Builtins_Numeric`,
`Builtins_String`, `Builtins_Binary`, `Builtins_PlainLiteral`,
`Builtins_XMLLiteral`, `Builtins_List`, `Builtins_Time`,
`IRI_from_RDF_Literal`, `Factorial_Forward_Chaining`,
`Modeling_Brain_Anatomy` and `Non-Annotation_Entailment`. F\* skips
only `Builtins_List` and `Builtins_Time` (naming
`is-literal-dateTimeStamp`); the rest are Lean gaps.

`Factorial_Forward_Chaining` is the one to look at first, and it is
NOT a built-in gap: it names only `numeric-add`, `numeric-multiply`
and `numeric-greater-than-or-equal`, and `RIF/Builtins.lean`
implements all three. The F\* ledger records the same case needing
`Equal`-as-BIND (`?N = External(func:numeric-add(?N1 1))`), an engine
feature rather than a built-in.

**An engine limit worth naming.** `entails` threads a Bool through
`groundTm`/`matchAtom`/`step`/`closure`, so it can say a built-in
blocked a rule but not WHICH. The runner now prints the built-in IRIs
a case uses, clearly labelled as candidates rather than as the
measured cause. Threading the blocking IRI itself is the change that
would let an undecided verdict name its own cause the way the F\*
skips do.

**RML.** `RMLTC0027b-JSON` stays not-read: its own `output.nq` writes
`<http://example.com/Person/Emily Smith>`, and an IRIREF may not
contain a space. The 15 negative cases need a mapping validator; the
whole rml-io section (84 directories) needs a probe.

**CSVW validation, 14 fails.** `test034` and `test035` (foreign-key
`schemaReference` resolution), `test094`, `test100`, `test107`,
`test109`, `test111`, `test124`, `test127`, `test147`, `test148`
(structural and title-compatibility rules), `test257` and `test258`
(cross-table foreign-key referential integrity), and `test308` — the
one the F\* tree also fails, for the reason
`.github/test-suites/csvw-validation.yaml` records. Two skips,
`test092` and `test119`, name fixtures the manifest references that
are not vendored in this checkout.

**rdf-semantics, 10 fails and 15 unsupported.** Fails: `literal-type`,
`triple-terms-propositions` (both need a literal or triple term in
SUBJECT position, which `Triple.s : Subject` cannot represent — F\*
has the same limit), `annotation` and `annotation-unfolded` (the
expected result names an IRI reifier where the action's `{| |}`
shorthand produces a fresh blank node; F\* fails both identically),
`opaque-literal`, `opaque-language-string`,
`opaque-language-string-control`, `opaque-dir-language-string-control`,
`malformed-literal-no-spurious`, `malformed-literal-bnode-neg`.

The 15 unsupported are the 7 `rdf:JSON`, 4 `xsd:float` and 4
`xsd:double` fixtures, all refused by `recognizedDatatypesOf` in
`Harness/Run.lean` because the IRIs are not in
`RDF.Datatypes.modelledDatatypes`. **Adding the three IRIs to that
list is not the fix**, even though it would turn the tests green:
`literalIllFormed` decides ill-formedness only for datatypes whose
LEXICAL SPACE this module knows, and it knows none of these three. A
bare list edit would make every `xsd:double` literal count as
well-formed, malformed ones included, in a suite that contains
malformed-literal tests. The fix is the lexical spaces first
(XSD 1.1 §3.3.5 for double and float, the Lean JSON parser for
`rdf:JSON`), then `literalIllFormed`, then the list. The D-value
comparison itself (`dtValueLeq`, IEEE-754 and structural JSON
equality) is already implemented and `#guard`-pinned.

### RDF/XML: what the fix was, and a finding about the fixtures

`L4Factoidal/RDF/XmlCanon.lean` compared `rdf:XMLLiteral` values with
the xmlns attributes left as written. RDF 1.1 Concepts §5.1 defines
that value space through Exclusive XML Canonicalization 1.0, whose
§3.2 renders a namespace declaration only for a prefix the element
VISIBLY UTILIZES and only when no output ancestor already rendered the
same prefix with the same URI. Adding the namespace axis to the
comparison closed both cases with no regression.

The finding worth keeping: the two fixture families state the same rule
and disagree LEXICALLY — `xml-canon/test001` expects an unused xmlns
copied into the literal, `rdfms-xml-literal-namespaces` expects unused
ones dropped. No byte comparison passes both. Only a namespace-aware
comparison does, which is what the specification asks for anyway.

### `lake build` over the whole tree: RED, then GREEN

The session's engine changes left the tree unbuildable. It builds
again at `1d4c830b7`: **1096 jobs, green**, hygiene audit clean
(`partial def` 172, baseline 172), `tools/blockengine-ibk5-quad-smoke.sh`
passing.

FOUR modules were broken, not the two first seen — the build stops at
the first failure, so each repair revealed the next. All four came from
the same two changes, and three of the four are one mistake in three
places: **a definition that a soundness theorem is stated about was
widened, and the widening was treated as a refactor.**

| module | what broke it | repair |
| --- | --- | --- |
| `Unified/DSchema.lean:281` | `Regime.literalEq` gave every non-`simple` regime `dtValueLeq` instead of `literalValueEq` | `.d` and `.rdf` keep `literalValueEq`; only `.rdfs`/`.rdfsPlus` get `dtValueLeq` |
| `Storage/GeoBBoxIndex.lean:291` | Polygon/Polygon arms added to `sfWithinBase` and `sfIntersectsBase` | `within`/`contains` PROVED; the `sfIntersectsBase` arm removed |
| `Unified/SparqlQuery.lean:434` | the new `Regime.rdfsPlus` constructor, in an exhaustive match | `none`, preserving the table's prior behaviour |
| `Unified/SparqlAdequacy.lean:1194` | `Regime.closure .rdfs` widened from `fullClosure g` to `fullClosure (rdf12ReifiesClosure g)` | `.rdfs` back to `fullClosure`; the reifies step stays in `.rdfsPlus` |

**The rule these three share.** `dtValueLeq` extends `literalValueEq`;
`rdf12ReifiesClosure` extends the identity. Both extensions make
entailment MORE permissive, and soundness does not travel from a
smaller relation to a larger one just because the larger contains it.
A regime that carries a soundness theorem may not be widened without
re-proving it. Regimes that carry none may. The reason is now written
at both definitions, so the next widening has to answer it.

**What the repairs cost, measured:**

* `rdf-semantics` 22 pass → **21 pass**, 11 fail, 15 unsupported (of
  47). One fixture wanted the `rdf:reifies`-range step under the
  `.rdfs` regime. Recover it by giving that fixture the RDFS-Plus
  regime, or by proving the widened closure sound.
* `geosparql-v0` 37 pass → **35 pass**, 2 fail (of 37):
  `sfIntersects(square A, overlapping square B)` and
  `sfDisjoint(square A, far-away square C)`, both now `None`. The
  second follows from the first because `sfDisjoint` is `sfIntersects`
  negated — the correct relation, and it was not decoupled to buy the
  test back.
* `Regime.literalEq`: no cost. Zero tests moved.

**The Geo lemma that would restore the two GeoSPARQL cases.**
`exists_common_point` is TRUE for a polygon pair — two polygons that
intersect share a point, and that point is in both boxes. Our
`polygonsIntersect` is a three-way disjunction and only two disjuncts
hand over a witness (a vertex of either polygon non-exterior to the
other). The third, `polygonBoundariesCross`, does not: two squares
meeting in a plus shape cross with no vertex of either inside the
other. Restoring the arm needs a constructed segment-intersection
point, or a lemma that overlapping boxes contain a common point
(`BBox.overlaps_of_common_point` exists; its converse does not).

**Why none of this was caught in flight.** Four agents shared one
worktree on a disk at its floor, and each was told to build only its
own target to stay off the shared Lake lock. That bought throughput
and paid for it here: a target-scoped build cannot see a module that
merely DEPENDS on what you changed, and adding a constructor to a
widely-used inductive touches every exhaustive match over it. The rule
that follows — one whole-tree `lake build` before a session's last
commit, however green the targeted ones were, and never a session that
ends without one.

### Two working-method failures from this session

**A commit carried files its subject does not name.** Commit
`47b9d2c3a`, whose message describes only RIF work, also contains the
whole GeoSPARQL landing (`Harness/GeoRun.lean`,
`L4Factoidal/Geo/{Types,Wkt,Topology,Functions}.lean`, and the test
inventory row). Four agents shared one worktree; one had staged its
files, and a plain `git commit` after `git add <own paths>` commits
the whole INDEX, not the paths just added. This is anti-pattern #33 in
a new shape — there the files were half-extracted, here they belong to
another agent. The rule that prevents it: in a shared worktree, commit
by PATHSPEC (`git commit -m … -- path1 path2`), which ignores
everything else in the index. Later commits in this session did.

**The disk floor was measured in the wrong place.** The session hit
2.7 GB free on `/System/Volumes/Data` and stopped its parallel builds.
The Lean build caches were not the cause: the five worktrees hold
0.5-0.9 GB each. 13 GB sat in another project's agent scratchpad under
`/private/tmp/claude-501/`, and 4 GB in a five-day-old Factoidal
session scratchpad. CLAUDE.md's Agent Work Strategy tells a session to
size the worktrees; on this machine the agent scratchpads are the
larger consumer, and a session that measures only `.lake` concludes it
has room when it does not. Check `df` itself, and when it is low,
`du -sh /private/tmp/claude-*/*` before assuming the worktrees are at
fault.

## CSVW validation: the 16 undecided tests, one row each

Date: 2026-09-07, branch `wt/finish-csvw`. Measured in this worktree:
`lake -d formal/lean4 exe l4csvw-validate` is **266 pass, 14 fail, 2
skip (out of 282)** — positive 76 pass of 76, warning 59 pass, 1 fail,
1 skip of 61, negative 131 pass, 13 fail, 1 skip of 145. The F\* tree
is 281 pass, 1 fail of 282. `l4csvw-rdf` and `l4csvw-json` are 270
pass of 270 each, with 0 over-strict cross-check reports.

This table is written BEFORE the engine changes, so a later commit can
say which rows it turned green and be checked against the row it
claimed.

Spec references: **DM** = Model for Tabular Data
(https://www.w3.org/TR/tabular-data-model/), **MV** = Metadata
Vocabulary (https://www.w3.org/TR/tabular-metadata/).

### Cluster A — raw-JSON structural rules (5 tests)

| id | kind | what the test expects | what Lean does | the spec sentence |
| --- | --- | --- | --- | --- |
| `test094` | warning | `"tables": [{…}, 1]`. The non-object array item is IGNORED with a warning; the group still holds one valid table, so the document CONFORMS | `checkTableGroup` raises `err "tables must hold table objects"` — the document is rejected | MV §5: "Any items within an array that are not valid objects of the type expected are ignored." |
| `test100` | negative | `"columns"` is a single object, not an array. Proceed as if an EMPTY array had been supplied — a schema of 0 columns against a 5-column CSV, which a validator MUST reject | `checkSchema` reads `columns` with `\| _ => []`, so a non-array is silently the empty column list and NO finding is raised | MV §5.2: "If the supplied value of an array property is not an array … compliant applications MUST issue a warning and proceed as if the property had been supplied with an empty array." |
| `test107` | negative | `"tableSchema": 1`. Proceed as if an empty object had been supplied; a validator MUST then reject | `checkTable` calls `checkSchema` on the integer; every `field?` lookup inside returns `none`, so no finding is raised | MV §5.2: "If the supplied value of an object property is not a string or object … compliant applications MUST issue a warning and proceed as if the property had been specified as an object with no properties." |
| `test109` | negative | column 1 has `"titles": {"a-bad-language": "GID"}`. `a-bad-language` is not a well-formed BCP 47 tag, so the title is unusable and a validator MUST raise an error | `checkTitles` emits `warn`, not `err`, on an invalid language key — a warning does not fail a document | MV §5.1.3: natural-language property objects have "properties … [that] MUST be language codes as defined by [BCP47]". |
| `test111` | negative | column 1 has `"titles": 1`. A titles value that is not a string, array or object is a validation error | `checkTitles` matches only `.object`; every other JSON type falls through to `[]` | MV §5.1.3 / §5.2: "If the supplied value of a natural language property is not a string, array or object … compliant applications MUST issue a warning and proceed as if the property had been specified as an empty array." |

### Cluster B — table-description compatibility (4 tests)

DM §5.4.3 (Table Description Compatibility) and the §6 validator
duty: "if `TM` is not compatible with `EM` validators MUST raise an
error, other processors MUST generate a warning and continue
processing". Lean's `checkDataTable` implements only the WIDTH half of
§5.4.3 (`declaredNonVirt.length != actualWidth`); the per-column
title/name half is absent, and `Validate.lean`'s own section comment
says so ("NOT covered yet … title/header-language compatibility").

| id | kind | what the test expects | what Lean does | the spec sentence |
| --- | --- | --- | --- | --- |
| `test124` | negative | metadata columns carry `name` (`GID1`, `on_street1`, …) and NO titles; `tree-ops.csv` carries titles and no names. A validator MUST reject | no per-column check runs; the widths match (5 = 5), so the document conforms | DM §5.4.3: a column description with a name but no titles is compatible only if that name is the one the CSV's own title encodes to. |
| `test127` | negative | metadata titles `Surname`, `Family Name` against CSV header `Surname`, `FamilyName`. Column 2 has an empty title intersection | as above — widths match, so it conforms | DM §5.4.3: "there is a non-empty case-sensitive intersection between the titles values". |
| `test147` | negative | metadata titles are lower-cased (`gid`, `on street`, …) against `GID`, `On Street`. The intersection is empty because the match is CASE-SENSITIVE | as above | DM §5.4.3, same sentence — "case-sensitive". |
| `test148` | negative | table `"lang": "de"`; column 2 has `"titles": {"en": "On Street"}`. The header cell carries the table's `de`, and `en` does not match `de` | as above | DM §5.4.3: "matches MUST have a matching language; `und` matches any language, and languages match if they are equal when truncated, as defined in [BCP47], to the length of the shortest language tag." |

### Cluster C — foreign-key referential integrity (4 tests)

DM §6.4.9: "Validators MUST raise errors for each row that does not
have a referenced row for each of the foreign keys on the table in
which the row appears." Lean has `checkForeignKeyTarget`, which checks
only that the reference NAMES an existing table and column. Nothing
compares the values.

| id | kind | what the test expects | what Lean does | the spec sentence |
| --- | --- | --- | --- | --- |
| `test257` | negative | a foreign-key value in `test257.csv` has NO referenced row in the target table | the reference resolves, so the document conforms; no value is compared | DM §6.4.9, quoted above. |
| `test258` | negative | a foreign-key value matches MORE THAN ONE row in the target table | as above | DM §6.4.9: the referenced row must be unique — "a referenced row", singular. |
| `test034` | negative | the Public Sector Roles example; `organizations.csv` "intentionally contains an invalid reference". The foreign keys live in EXTERNAL schema files reached by `schemaReference` | as above, and additionally the `foreignKeys` are in `gov.uk/schema/*.json`, which the raw-JSON walk never sees because `tableSchema` is a URL string | DM §6.4.9 plus MV §5.5: a `schemaReference` names the schema whose table the key points into. |
| `test035` | negative | the same document in minimal mode | as above | as above. |

### Cluster D — the datatype string, and the two skips (3 tests)

| id | kind | what the test expects | what Lean does | the spec sentence |
| --- | --- | --- | --- | --- |
| `test308` | negative | `"datatype": "http://example.org/bad/datatype"` — a datatype STRING that is not a built-in name is an error | `checkDatatype` warns and never rejects, deliberately: `test238` is a WarningValidationTest whose datatype string is `http://example.org/datatype`, an equally non-built-in absolute URL that MUST conform | MV §5.11.1 vs the `test238` entry's own comment ("MUST be one of the built-in datatypes … **or an absolute URL**"). The two entries state the rule differently and their values differ only in the URL path, so no value-agnostic rule separates them. F\* fails this test for the same reason (`.github/test-suites/csvw-validation.yaml`). Expected to REMAIN failing. |
| `test092` | negative (SKIP) | `test092-metadata.json` is on disk and is deliberately MALFORMED JSON. "All compliant applications MUST generate errors and stop processing if a metadata document does not use valid JSON syntax" — so the document does not conform and the negative test passes | `CsvwValidateRun.runOne`'s `readMeta` returns `none` for BOTH "file absent" and "file did not parse"; the caller reads `none` as `metaMissing` and reports SKIP. A harness defect, not an engine gap | MV §6.1 / the entry's own comment, quoted. |
| `test119` | warning (SKIP) | `test119/csv-metadata.json` does not reference `test119/action.csv`, so it MUST be ignored and the bare CSV conforms | the fallback branch builds the CSV path as `suiteRelative requested e.action`, resolving `test119/action.csv` against a base that ALREADY ends in it — producing `test119/test119/action.csv`, which is not on disk, so the entry is skipped. A harness path defect | DM §5.2: "If the metadata file found at this location does not explicitly include a reference to the requested tabular data file then it MUST be ignored." |

### Target

282 pass, 0 fail, 0 skip is not reachable while `test308` stands: it
is a corpus contradiction with `test238`, evidenced above and recorded
independently on the F\* side. The target is therefore **281 pass, 1
fail (`test308`), 0 skip** — parity with F\*.
