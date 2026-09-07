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

Updated as commits land. Every score below was measured in this
worktree.

| area | before | after | closed | open |
| --- | --- | --- | --- | --- |
| RIF Core | 24 pass, 2 fail (of 26 decided); 13 undecided, 1 not read, 6 not attempted | 32 pass, 2 fail (of 34 decided); 11 undecided, 1 not read, 0 not attempted | the 6 ImportRejectionTest cases; OWL_Combination_Vocabulary_Separation_Inconsistency_1 and _2 | the 2 fails (RDF_Combination_Constant_Equivalence_4, EBusiness_Contract); 9 built-in cases; Modeling_Brain_Anatomy and Non-Annotation_Entailment (OWL-Direct closure); RDF_Combination_Constant_Equivalence_Graph_Entailment (graph conclusion) |
| RML core | 60 pass (of 60 compared); 1 not read, 15 not attempted | unchanged | | RMLTC0027b-JSON (fixture writes an IRIREF with a space); the 15 negative cases need a mapping validator |
| RML io | not run | unchanged | | the whole rml-io section (84 directories) |
| CSVW validation | not run (282 entries) | see the probe's own report | | |
| RDF/XML | 130 pass, 2 fail (of 132 eval-isomorphic) | 132 pass, 0 fail (of 132) | rdfms-xml-literal-namespaces/test001 and test002 | none |
| GeoSPARQL | no probe (F\* 37 of 37) | see the probe's own report | | |
| rdf-semantics | not run (47 entries) | see the probe's own report | | |

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

### Disk

The 2026-09-07 session stopped its parallel builds at 2.7 GB free on
`/System/Volumes/Data`. The space was not the Lean build caches (the
five worktrees hold 0.5-0.9 GB each); 13 GB sat in another project's
agent scratchpad under `/private/tmp/claude-501/` and 4 GB in a
five-day-old Factoidal session scratchpad. Neither was this session's
to remove. The rule in CLAUDE.md's Agent Work Strategy assumes the
worktrees are the consumer; on this machine the agent scratchpads are
the larger one, and a session that only measures `.lake` will conclude
it has room when it does not.
