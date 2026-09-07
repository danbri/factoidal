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
| RIF Core | 24 pass, 2 fail (of 26 decided); 13 undecided, 1 not read, 6 not attempted | **42 pass, 0 fail (of 42 decided); 3 undecided, 0 not read, 1 local override** (2026-09-07 session 2) | 42 pass, 0 fail, 1 local override, 3 skip (of 46) |
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
* **RIF** — every id the F\* tree decides, plus two it skips
  (`Builtins_List`, `NestedListsAreNotFlatLists`). 42 pass, 0 fail
  (out of 42 decided) on 2026-09-07; three ids stay undecided and are
  listed with their causes in the ledger-status table above.
  Previously closed in the first session: the 6 `ImportRejectionTest` cases,
  `OWL_Combination_Vocabulary_Separation_Inconsistency_1` and `_2`, and
  `RDF_Combination_Constant_Equivalence_Graph_Entailment`.
  `RDF_Combination_Constant_Equivalence_4` moved from FAIL to the
  local-override bucket, which is where the F\* tree already had it.

## RIF Core: the 12 open ids, by cause (2026-09-07, session 2)

Branch `wt/finish-rif2`. Measured start: `lake -d formal/lean4 exe l4rif`
gives **33 pass, 1 fail (out of 34 decided), 11 undecided, 1 local
override** against the F\* runner's **42 pass, 0 fail, 1 local
override, 3 skip (out of 46)**.

The table below is written BEFORE any engine change in this session.
Each row names what the id needs, by RIF-DTB section where the need is
a built-in, and the F\* verdict for the same id from
`bin/rif-runner/README.md`. The "built-ins used" lists printed by
`l4rif --verbose` are CANDIDATES; the cause column below was read from
each fixture's own `-premise.rifps`, which is the measurement the
Bool-threaded `blocked` flag cannot give.

| id | Lean before | cause, measured from the fixture | F\* verdict |
| --- | --- | --- | --- |
| `Factorial_Forward_Chaining` | undecided | NOT a built-in gap. `And(...)` puts `External(pred:numeric-greater-than-or-equal(?N1 0))` FIRST, with `?N1` unbound, and `matchFormula` folds conjuncts strictly left to right, so the built-in is called on an unground argument and reports `unknown`. Also needs `?N = External(func:numeric-add(?N1 1))` as a BIND: `matchAtom .equal` only compares two ground sides. RIF-BLD §3.2 makes `And` a set-like conjunction, so conjunct order carries no semantics | pass (ledger: "Equal-as-BIND") |
| `IRI_from_RDF_Literal` | undecided | `External(pred:iri-string(?z ?x))` with `?x` a bound string and `?z` unbound. RIF-DTB §4.3 `pred:iri-string` relates an IRI to its string; `Conformance`/`boundFix` already list it in `bindingBuiltins` for safeness, but `matchAtom` has no binding-pattern execution for it | pass |
| `Builtins_XMLLiteral` | undecided | `External(rdf:XMLLiteral("<br></br>"^^xs:string))` — a constructor cast whose datatype IRI is in the RDF namespace. `builtinName` maps only `func:`, `pred:` and `xs:`, so an `rdf:` cast returns `none` and `groundTm` reports blocked. RIF-DTB §5 (constructors) covers `rdf:XMLLiteral` and `rdf:PlainLiteral` alongside the XSD ones | pass |
| `Builtins_Binary` | undecided | `xs:base64Binary` has no lexical space in `inLexicalSpace` (it returns `none`, i.e. undecided), and the fixture both tests `pred:is-literal-base64Binary` and casts to it. XSD 1.1 §3.3.16 gives the lexical space (groups of four Base64 characters, final group padded with `=`) | pass |
| `Builtins_Numeric` | undecided | `func:numeric-divide` (RIF-DTB §4.4) is not in `evalFunc`, so `groundTm` blocks. Also `2 = External(func:numeric-divide(6 3))` needs `Equal` to compare by VALUE across `xs:integer` and `xs:decimal`, which `matchAtom .equal`'s structural `==` does not | pass |
| `Builtins_String` | undecided | thirteen RIF-DTB §4.5 functions absent from `evalFunc`: `compare`, `string-join`, `substring` (2- and 3-argument), `encode-for-uri`, `iri-to-uri`, `escape-html-uri`, `substring-before`, `substring-after`, `replace`; and one §4.6 predicate, `matches`. `replace` and `matches` need the XPath regex engine, which the Lean tree already has at `L4Factoidal/Regex/XPath.lean` (`compile`/`isMatch`/`replace`, the same engine SPARQL `REGEX`/`REPLACE` use) | pass |
| `Builtins_PlainLiteral` | undecided | RIF-DTB §4.7: `func:PlainLiteral-compare` and `pred:matches-language-range` are absent; the `rdf:PlainLiteral` constructor cast hits the same `builtinName` namespace gap as `Builtins_XMLLiteral`; and `func:string-from-PlainLiteral` / `func:lang-from-PlainLiteral` are applied by the fixture to an `xs:string` argument, which the current guard rejects | pass |
| `EBusiness_Contract` | FAIL (not entailed, must be) | the dateTime slice: `pred:is-literal-dateTime` applied to `"2008-07-22Z"^^xs:date` must hold (RIF-DTB §3.2 — `xs:date` values are `xs:dateTime` values at midnight, and the Approved fixture depends on it); `func:subtract-dateTimes` (§4.8) giving an `xs:dayTimeDuration`; `func:days-from-duration` (§4.8). The arity-3 `cpt:delivered` is NOT a gap in Lean — `RIF.Syntax.Atom.pos` carries a `List Tm` of any length, so the n-ary reification the F\* tree needed here is unnecessary | pass |
| `Builtins_List` | undecided | RIF-DTB §4.9 list functions: `get`, `sublist`, `append`, `concatenate`, `insert-before`, `remove`, `index-of`, `union`, `distinct-values`, `intersect`, `except`. `is-list`, `list-contains`, `make-list`, `count`, `reverse` are already decided | **skip**, named `List` |
| `Builtins_Time` | undecided | the whole RIF-DTB §4.8 date/time/duration family, about 60 built-ins | **skip**, named `is-literal-dateTimeStamp` |
| `Modeling_Brain_Anatomy` | undecided | imports under `http://www.w3.org/ns/entailment/OWL-Direct`. The rule body needs `rdf:type MaterialAnatomicalEntity` on individuals the ontology asserts only through `rdf:type Gyrus` + `rdfs:subClassOf`. F\* closes the imported graph under OWL-RL plus tableau materialisation before merging | pass |
| `Non-Annotation_Entailment` | undecided | a `NegativeEntailmentTest` importing under OWL-Direct. The imported graph declares `dc:title` an `owl:OntologyProperty`, so under the OWL 2 Direct Semantics its use is an ONTOLOGY ANNOTATION and carries no semantic condition (OWL 2 Structural Specification §10, Direct Semantics §2.1) — the rule body `?x[dc:title -> ?y]` therefore has no fact to match and the conclusion does not follow. Answering `doesNotHold` needs the annotation filter AND a statement that the rest of the imported graph is inside the implemented fragment | pass |

Two of the twelve are ids the F\* tree SKIPS with a named missing
built-in (`Builtins_List`, `Builtins_Time`). Under the parity rule
they may stay undecided in Lean only while the same built-ins are
named. The other ten are Lean gaps against a passing F\* verdict.

### Ledger status, measured after the session's last commit

`lake -d formal/lean4 exe l4rif`: **42 pass, 0 fail (out of 42
decided), 3 undecided, 1 local override**, from 33 pass, 1 fail (out
of 34 decided), 11 undecided, 1 local override. `l4sparql-probe`
unchanged at 403 pass, 0 fail (out of 403). Hygiene clean,
`partial def` 172 against the baseline 172.

Against the F\* runner's 42 pass, 0 fail, 1 local override, 3 skip
(out of 46): every id F\* decides, Lean now decides with the same
verdict. Two ids F\* SKIPS -- `Builtins_List` and
`NestedListsAreNotFlatLists`, both naming the `List` construct -- Lean
decides, so the Lean tree is two cases ahead of the F\* tree on this
corpus. The two counts differ in their denominator because the F\*
runner reports 46 cases including three `PositiveSyntaxTest` and
`NegativeSyntaxTest` files it counts separately; the id-by-id table
below is the comparison that does not depend on that.

| id | after this session | note |
| --- | --- | --- |
| `Factorial_Forward_Chaining` | PASS | conjunct deferral plus `Equal`-as-BIND, `74e100afb` |
| `IRI_from_RDF_Literal` | PASS | `pred:iri-string` binding-pattern execution, `74e100afb` |
| `Builtins_Numeric` | PASS | `func:numeric-divide` and exact decimal arithmetic, `67e1ac179` |
| `Builtins_Binary` | PASS | the `xs:base64Binary` lexical space, `67e1ac179` |
| `Builtins_XMLLiteral` | PASS | the RDF-namespace constructors, `67e1ac179` |
| `Builtins_PlainLiteral` | PASS | `func:PlainLiteral-compare`, `pred:matches-language-range`, one `plainParts` reader for both symbol spaces, `ffd5bd9a0` |
| `Builtins_String` | PASS | thirteen RIF-DTB 4.5 functions plus `pred:matches`, the two regex ones over `L4Factoidal.Regex.XPath`, `b079016f1` |
| `EBusiness_Contract` | PASS | the RIF-DTB 4.8 slice: `pred:is-literal-dateTime` over an `xs:date`, `func:subtract-dateTimes`, `func:days-from-duration`, `9c422ac9a`. The arity-3 relation needed nothing -- `Atom.pos` carries a `List Tm` of any length |
| `Builtins_List` | PASS | the RIF-DTB 4.9 list functions, `624af1762`. **Ahead of F\***, which skips this id |
| `NestedListsAreNotFlatLists` | PASS | was already decided by Lean. **Ahead of F\***, which skips it. Not vacuous: the premise fact `ex:p(List(ex:a List(ex:b)))` IS derived, and the goal `ex:p(List(ex:a ex:b))` fails to match it structurally |
| `Builtins_Time` | undecided | OPEN. The rest of RIF-DTB 4.8, about sixty built-ins over durations, timezones and field extraction. F\* skips this id too, naming `is-literal-dateTimeStamp`; the two trees are level here |
| `Modeling_Brain_Anatomy` | undecided | OPEN. Needs the imported graph closed under OWL-RL before it becomes facts, which is what the F\* runner's `apply_import_closure` does. `L4Factoidal/OWL/` has the material; wiring it into `Harness/RifRun.lean`'s import step is the change |
| `Non-Annotation_Entailment` | undecided | OPEN. Needs the OWL-Direct annotation filter: `dc:title` is declared an `owl:OntologyProperty` in the imported graph, so under the Direct Semantics its use carries no semantic condition and the rule body has no fact to match. Answering `doesNotHold` also needs a statement that the rest of that graph is inside the implemented fragment, which is why this is not a one-line filter |
| `RDF_Combination_Constant_Equivalence_4` | local override | unchanged. A corpus data defect, dispositioned the same way the F\* tree disposes of it |

**One reporting limit stays open.** `entails` threads a `Bool`, so an
undecided verdict still cannot say WHICH built-in blocked it; the
runner prints the built-ins a case USES and labels them candidates.
For `Builtins_Time` the design-record row above carries the measured
cause instead. Threading the blocking IRI through
`groundTm`/`matchAtom`/`step`/`closure` is the change that would let
the verdict name its own cause the way the F\* skips do, and it was
not made here.


### Open, by test id

**RIF.** SUPERSEDED on 2026-09-07 by the section
"RIF Core: the 12 open ids, by cause" above and its ledger-status
table. What that paragraph described as twelve open ids is now three:
`Builtins_Time`, `Modeling_Brain_Anatomy` and
`Non-Annotation_Entailment`. The reporting limit it names -- `entails`
threads a `Bool` and cannot say WHICH built-in blocked a rule -- is
still open.

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
