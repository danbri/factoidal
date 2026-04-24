# OWL 2 Test Harness — scoping + phased wiring plan

**Date:** 2026-04-24
**Owner:** claude/main
**Status:** scoping — starter runner landed in this commit; no reasoning
wired yet.

## Context

The W3C OWL 2 Test Cases corpus has been vendored at
`third_party/testing/owl/`. Unlike the SPARQL 1.1 suite
(`third_party/testing/w3c/`, git submodule) the OWL set was published as
a static drop in 2009-11 with no canonical upstream repo — each file is
a single RDF/XML catalog of `test:TestCase` entries. See the directory's
`README.md` for file-size + source provenance.

This doc inventories the corpus and proposes a phased plan for wiring
it into Factoidal. This is the first non-SPARQL-RDF1.1 test corpus we
exercise, so there is no pre-existing runner dispatch — the companion
commit adds a standalone `owl_runner` (skeleton only).

## Inventory

### 1. File-level `<test:TestCase>` counts

`grep -c '<test:TestCase' <file>`:

| File                              | TestCase count |
|-----------------------------------|---------------:|
| `all.rdf`                         | 489 |
| `semantics-direct.rdf`            | 488 |
| `syntax-dl.rdf`                   | 323 |
| `type-positive-entailment.rdf`    | 206 |
| `type-consistency.rdf`            | 354 |
| `type-inconsistency.rdf`          | 128 |
| `type-negative-entailment.rdf`    | 23  |
| `profile-RL.rdf`                  | 91  |
| `profile-EL.rdf`                  | 87  |
| `profile-QL.rdf`                  | 65  |
| `RL-RDF-rules-tests.rdf`          | 0   |

`RL-RDF-rules-tests.rdf` is effectively empty (725 bytes, only a DOCTYPE
and an empty `<rdf:RDF>` shell). Ignore it.

A single test case may carry **multiple** `rdf:type` values (a test can
be simultaneously a `ProfileIdentificationTest`, a `PositiveEntailmentTest`,
and a `ConsistencyTest`), so the per-category counts below **do not sum
to the file count**.

### 2. Per-catalog breakdown by test type

`grep -c 'rdf:resource="&test;<TYPE>"' <file>`:

| File | Consistency | Inconsistency | Positive-Ent | Negative-Ent | ProfileIdent |
|------|-----:|-----:|-----:|-----:|-----:|
| `profile-RL.rdf`                   | 76  | 14 | 30  |  6 |  91 |
| `profile-EL.rdf`                   | 72  | 14 | 29  |  6 |  87 |
| `profile-QL.rdf`                   | 58  |  6 | 20  |  3 |  65 |
| `type-positive-entailment.rdf`     | 206 |  0 | 206 |  0 | 162 |
| `type-negative-entailment.rdf`     | 23  |  0 |  0  | 23 |  18 |
| `type-consistency.rdf`             | 354 |  0 | 206 | 23 | 291 |
| `type-inconsistency.rdf`           |  0  |128 |  0  |  0 | 126 |
| `semantics-direct.rdf`             | 353 |128 | 206 | 23 | 417 |
| `syntax-dl.rdf`                    | 214 |104 | 90  | 16 | 319 |

Key observation: the three `profile-XX.rdf` files are themselves proper
subsets of the larger catalogs (all their tests appear in `all.rdf` and
in `semantics-direct.rdf`); the profile files additionally carry the
`test:profile &test;XX` annotation that identifies membership.

### 3. Distinct `test:TestCase` type URIs

All catalogs use the same five test types, declared under the
`http://www.w3.org/2007/OWL/testOntology#` namespace (aliased `&test;`
via a DOCTYPE entity):

- `&test;PositiveEntailmentTest`
- `&test;NegativeEntailmentTest`
- `&test;ConsistencyTest`
- `&test;InconsistencyTest`
- `&test;ProfileIdentificationTest`

Each catalog header expands these via a local DOCTYPE:

```
<!DOCTYPE rdf:RDF[
    <!ENTITY rdf  'http://www.w3.org/1999/02/22-rdf-syntax-ns#'>
    <!ENTITY rdfs 'http://www.w3.org/2000/01/rdf-schema#'>
    <!ENTITY owl  'http://www.w3.org/2002/07/owl#'>
    <!ENTITY test 'http://www.w3.org/2007/OWL/testOntology#'>
]>
```

The F\*-extracted `Parser.RDFXML` does NOT currently expand custom
DOCTYPE entity references — it recognises only the five built-in XML
entities (`&amp;`, `&lt;`, `&gt;`, `&quot;`, `&apos;`) in
`Parser.XML.parse_char_ref_body`. The starter runner works around this
by pre-expanding the four known catalog entities (`&rdf;`, `&rdfs;`,
`&owl;`, `&test;`) in OCaml before handing the buffer to
`Parser_RDFXML.parse_rdfxml`. This is pure I/O glue — no RDF/SPARQL
semantics — and is explicitly allowed by CLAUDE.md rule #10. Proper
DOCTYPE-entity support belongs in `Parser.XML.fst` and is tracked as
a follow-up (not blocking the harness skeleton).

## What each test type carries

Below are **two representative `<test:TestCase>` blocks** copied verbatim
from `profile-RL.rdf`, annotated with what the harness would need to do
to evaluate them.

### Example A — PositiveEntailmentTest + ProfileIdentificationTest + ConsistencyTest

```xml
<test:TestCase rdf:about="http://owl.semanticweb.org/id/Chain2trans">
    <rdf:type rdf:resource="&test;ProfileIdentificationTest" />
    <rdf:type rdf:resource="&test;PositiveEntailmentTest" />
    <rdf:type rdf:resource="&test;ConsistencyTest" />
    <test:identifier>chain2trans1</test:identifier>
    <test:creator>Bijan Parsia</test:creator>
    <test:description>A role chain can be a synonym for transitivity.</test:description>
    <test:normativeSyntax rdf:resource="&test;RDFXML" />
    <test:status rdf:resource="&test;Approved" />
    <test:semantics rdf:resource="&test;DIRECT" />
    <test:semantics rdf:resource="&test;RDF-BASED" />
    <test:species rdf:resource="&test;FULL" />
    <test:species rdf:resource="&test;DL" />
    <test:profile rdf:resource="&test;EL" />
    <test:profile rdf:resource="&test;RL" />
    <test:rdfXmlConclusionOntology rdf:datatype="xsd:string">
      &lt;!-- OWL/XML serialisation of the conclusion graph, escaped --&gt;
    </test:rdfXmlConclusionOntology>
    <test:rdfXmlPremiseOntology rdf:datatype="xsd:string">
      &lt;!-- OWL/XML serialisation of the premise graph, escaped --&gt;
    </test:rdfXmlPremiseOntology>
</test:TestCase>
```

Fields:

- `test:rdfXmlPremiseOntology` — XML-escaped RDF/XML string of the
  premise graph `G_P`.
- `test:rdfXmlConclusionOntology` — XML-escaped RDF/XML string of the
  conclusion graph `G_C`.
- `test:profile` — the profile(s) the test case claims membership in
  (RL, EL, QL). A `ProfileIdentificationTest` says: *declared profile ⇒
  premise+conclusion stay inside that profile*. For our purposes (we
  want to score OWL-RL closure), the presence of `&test;RL` is the
  filter.
- Also-available alternative serialisations: `test:fsPremiseOntology` /
  `test:fsConclusionOntology` (OWL 2 Functional Syntax), which we can
  ignore for now since we parse RDF/XML.

Harness task for this family: parse `G_P`, run OWL-RL closure, check
that every triple of `G_C` appears in the closure (simple-entailment
into the closed premise).

### Example B — NegativeEntailmentTest + ConsistencyTest

```xml
<test:TestCase rdf:about="http://owl.semanticweb.org/id/New-2DFeature-2DKeys-2D004">
    <rdf:type rdf:resource="&test;ProfileIdentificationTest" />
    <rdf:type rdf:resource="&test;NegativeEntailmentTest" />
    <rdf:type rdf:resource="&test;ConsistencyTest" />
    <test:identifier>New-Feature-Keys-004</test:identifier>
    <test:profile rdf:resource="&test;EL" />
    <test:profile rdf:resource="&test;RL" />
    <test:rdfXmlNonConclusionOntology rdf:datatype="xsd:string">
      &lt;!-- G_NC: premise must NOT entail this graph --&gt;
    </test:rdfXmlNonConclusionOntology>
    <test:rdfXmlPremiseOntology rdf:datatype="xsd:string">
      &lt;!-- G_P --&gt;
    </test:rdfXmlPremiseOntology>
</test:TestCase>
```

Differs from A in the field name: `rdfXmlNonConclusionOntology` instead
of `rdfXmlConclusionOntology`. Expected outcome: run OWL-RL closure on
`G_P` and confirm that at least one triple of `G_NC` is **absent** from
the closure.

### InconsistencyTest / ConsistencyTest — no conclusion graph

A pure inconsistency test carries only `test:rdfXmlPremiseOntology` and
asserts that the premise has no model (contradiction derivable):

```xml
<test:TestCase rdf:about="http://owl.semanticweb.org/id/DisjointClasses-2D002">
    <rdf:type rdf:resource="&test;ProfileIdentificationTest" />
    <rdf:type rdf:resource="&test;InconsistencyTest" />
    <test:profile rdf:resource="&test;EL" />
    <test:profile rdf:resource="&test;QL" />
    <test:profile rdf:resource="&test;RL" />
    <test:rdfXmlPremiseOntology>
      &lt;!-- G_P asserts Boy disjoint with Girl, and Stewie in both --&gt;
    </test:rdfXmlPremiseOntology>
</test:TestCase>
```

Expected outcome: after OWL-RL closure of `G_P`, detect a
contradiction sentinel (the RL-specific rule `cax-dw` fires and
produces `owl:Nothing` / a false-triple). Requires contradiction
detection, which we do not currently have as a clean API.

A `ConsistencyTest` is the complement — the premise must have a model
(no contradiction derivable).

## Mapping to current Factoidal capabilities

| Category | Profile-RL count | Closest existing capability | Gap |
|---|---:|---|---|
| PositiveEntailmentTest | 30 | `RDF.Graph.Executable.owl_rl_closure_with_reflexivity` + `rdfs_closure_with_reflexivity` — **partial coverage** (RDFS + a subset of RL rules land via existing closure) | Need to verify coverage of eq-ref/eq-sym/eq-trans/eq-rep-s/eq-rep-p/eq-rep-o, prp-dom, prp-rng, prp-fp, prp-ifp, prp-symp, prp-trp, cls-int1..cls-oo, cax-sco, scm-*. Conclusion-graph entailment check (every triple of G\_C appears in closure(G\_P)) is standard `List.for_all (triple_in_graph g_c) g_closure`. |
| NegativeEntailmentTest | 6 | same | Same as above, but invert the check. |
| ConsistencyTest | 76 | none — we have no "is this consistent?" API | Needs a contradiction-detection layer: run closure, then check whether a designated "false" sentinel triple or `owl:Nothing` membership appears. Debatable whether this lives in `Tableau.fst` (DL) or in an RL extension. |
| InconsistencyTest | 14 | none — as above | Same as ConsistencyTest but invert. |
| ProfileIdentificationTest | 91 | none — no syntactic profile check | Future concern: pattern-match the premise ontology against the RL profile grammar (OWL 2 Profiles §4.2). Independent of reasoning. |
| Direct-semantics tests (`semantics-direct.rdf`) | — | `Tableau.fst` (skeletal, large surface area gap) | Out of scope for RL-focused first pass. |

## Phased plan

**Phase 0 (this commit) — skeleton.**
- [x] Vendor the corpus (already done, 2026-04-24 earlier commit).
- [x] Write this scoping doc.
- [x] Add `formal/fstar/ocaml-output/owl_runner.ml` that reads one
      catalog (default `profile-RL.rdf`), expands the 4 catalog DOCTYPE
      entities, parses via `Parser_RDFXML.parse_rdfxml`, and prints
      per-test identifier + types. Prints a final count. Does NOT run
      any reasoning.
- [x] Wire `owl_runner` into `build-ocaml.sh compile` using the same
      recipe as `w3c_runner` (same packages, same platform dir, same
      symlink convention).

**Phase 1 (next commit) — PositiveEntailmentTest @ profile-RL.**
- Read each `test:rdfXmlPremiseOntology` + `test:rdfXmlConclusionOntology`
  string literal out of the manifest, XML-unescape, re-parse each as
  RDF/XML to get two triple lists `G_P` / `G_C`.
- Run `owl_rl_closure_with_reflexivity G_P fuel` → `G_P*`.
- Pass iff every triple of `G_C` is in `G_P*` (modulo bnode renaming;
  for the first pass, require bnode-free conclusion graphs or do
  brute-force bnode isomorphism).
- Emit a labelled score: "N pass, M fail (out of 30) for
  profile-RL PositiveEntailmentTest". Per rule #25: always show the
  denominator.
- Expected first-pass result: low, pending OWL-RL rule completeness in
  `RDF.Graph.Executable.fst`. Captures the actual gap.

**Phase 2 — NegativeEntailmentTest @ profile-RL** (6 tests).
- Same parse path; pass iff at least one triple of `G_NC` is NOT in
  `G_P*`. Straightforward once Phase 1 lands.

**Phase 3 — ConsistencyTest / InconsistencyTest @ profile-RL** (76 + 14).
- Requires either (a) adding contradiction sentinels to OWL-RL closure
  output (check `owl:Nothing` class membership on any named individual,
  plus `owl:sameAs`/`owl:differentFrom` crash on the same pair,
  plus `owl:disjointWith` + shared instance — essentially the RL "false"
  rules from OWL 2 RL/RDF Tables 6, 7), or (b) deferring to a future
  tableau-based check. Pick (a) for RL; it's a handful of F\* rules.

**Phase 4 — ProfileIdentificationTest** (91).
- Syntactic check: walk the premise+conclusion triples and verify
  RL-profile axiom shapes (OWL 2 Profiles §4.3). Independent of
  reasoning; can be a standalone F\* module
  (`OWL.ProfileRL.Identify.fst`). Deferred.

**Phase 5 — extend to profile-EL / profile-QL.**
- OWL 2 EL and QL use different closure calculi. Separate F\* modules
  (`owl_el_closure_*`, `owl_ql_closure_*`) will be needed; the runner
  can share the manifest-reader + entailment-check machinery.

**Phase 6 — direct semantics (`semantics-direct.rdf`, `syntax-dl.rdf`).**
- Requires the DL tableau. Tracked separately; this corpus is the right
  regression set for `Tableau.fst` once its coverage matches RDFS+RL.

## Out of scope for the skeleton commit

- No actual reasoning.
- No scoring, no integration with the existing W3C SPARQL entailment
  suite score, no `w3c_runner --owl` dispatch. This is a separate
  binary.
- No changes to `RDF.Graph.Executable.fst`, `SPARQL11.Algebra.fst`,
  `Parser.RDFXML.fst`, or `Tableau.fst` — those are other agents'
  territory per the task brief.

## References

- W3C OWL 2 Test Cases (source): <https://www.w3.org/2009/11/owl-test/>
- OWL 2 RL/RDF rules: <https://www.w3.org/TR/owl2-profiles/#Reasoning_in_OWL_2_RL_and_RDF_Graphs_using_Rules>
- OWL 2 Profiles §4.2–§4.3 (RL syntactic profile): <https://www.w3.org/TR/owl2-profiles/#OWL_2_RL>
- Entailment plan: `docs/designissues/2026-04-23-entailment-plan.md`
- Relationship to SPARQL entailment suite: see
  `third_party/testing/owl/README.md`.
