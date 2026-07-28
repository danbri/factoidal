---
title: OWL 2 conformance
layout: base.njk
---

# OWL 2 conformance — measured scores and every named residual

Factoidal runs the W3C OWL 2 Test Cases from disk, through the
F\*-extracted reasoner, and reports the result per catalog. This page
states the scores as measured, defines the two entailment regimes they
are measured under, and names **every** test that still fails, with the
reason it fails and how the project dispositions it.

Every number below comes from a re-run of each catalog against the
committed `bin/linux-x86_64/owl_runner` binary on 2026-07-28 (commit
`983d694`). The machine-readable copy is the
[test-results dashboard]({{ '/test-results/' | url }}) and its
`latest.json`; a number here that disagrees with that file is a bug in
one of them, not a judgement call.

Parser and algebra spec are verified in F\*; the on-disk backend has
unverified OCaml-side optimization layers being migrated back to F\*.

## The two regimes

**RL — Datalog closure.** A fixed set of forward-chaining rules
(`OWL.Closure.fst`, extracted from F\*) fires over the asserted triples
until no new triple appears. The result is a materialised graph, and a
conclusion is entailed if it is contained in that graph after
canonicalisation. RL is complete for the rules it has and blind to
everything outside them — no existential reasoning, no case split, no
proof by contradiction. The `profile-RL.rdf`, `profile-EL.rdf`, and
`profile-QL.rdf` catalogs are scored under RL, and each finishes in a
few seconds.

**DL — closure plus tableau plus witness layer.** The DL regime runs
the RL closure, hands the result to `Tableau.tableau_materialise`
(`Tableau.fst` and `Tableau.Refute.fst` — model construction: NNF, lazy
TBox unfolding, disjunction branching under a threaded linear work
budget, depth-capped existential witnesses, and clash rules for
complement, min/max cardinality, counting, and bottom properties), then
runs the RL closure again over whatever the tableau proved. The tableau
only emits entailed membership triples, so a DL answer is never weaker
than the RL answer on the same test; on a per-test wall-clock cap trip
the run falls back to the RL verdict rather than guessing. The four
`type-*` catalogs and `semantics-direct.rdf` are scored under DL.

## Scores

Catalogs overlap: the same `test:TestCase` can appear in several
catalog files and be scored under several section headings. The rows
below are per catalog and per section, as the runner emits them — they
are not additive into a single grand total, and the site does not
publish one.

| Catalog | Section | Regime | Score |
|---|---|---|---|
| `profile-RL.rdf` | PositiveEntailment | RL | 28 pass, 2 fail (out of 30) |
| `profile-RL.rdf` | NegativeEntailment | RL | 6 pass, 0 fail (out of 6) |
| `profile-RL.rdf` | Consistency | RL | 76 pass, 0 fail (out of 76) |
| `profile-RL.rdf` | Inconsistency | RL | 14 pass, 0 fail (out of 14) |
| `profile-EL.rdf` | all four sections | RL | 118 pass, 2 fail (out of 120), 1 skipped |
| `profile-QL.rdf` | all four sections | RL | 85 pass, 2 fail (out of 87) |
| `type-positive-entailment.rdf` | PositiveEntailment | DL | 173 pass, 31 fail (out of 204), 2 skipped |
| `type-positive-entailment.rdf` | Consistency | DL | 204 pass, 0 fail (out of 204), 2 skipped |
| `type-negative-entailment.rdf` | NegativeEntailment | DL | 23 pass, 0 fail (out of 23) |
| `type-negative-entailment.rdf` | Consistency | DL | 23 pass, 0 fail (out of 23) |
| `type-consistency.rdf` | Consistency | DL | 352 pass, 0 fail (out of 352), 2 skipped |
| `type-inconsistency.rdf` | Inconsistency | DL | 124 pass, 3 fail (out of 127), 1 skipped |
| `semantics-direct.rdf` | Consistency | DL | 351 pass, 0 fail (out of 351), 2 skipped |
| `syntax-dl.rdf` | species (DL vs Full) | syntactic | 319 pass, 2 fail (out of 321 scored), 2 skipped |

The `semantics-direct.rdf` catalog also re-scores the positive-entailment
(173 pass, 31 fail), negative-entailment (23 pass, 0 fail), and
inconsistency (124 pass, 3 fail) sections; those numbers agree
test-for-test with the dedicated catalogs above, so they are not
repeated as separate rows.

Skips are two kinds, both reported by the runner rather than hidden:
`functional-syntax-only` (the fixture ships only an OWL
Functional-Style Syntax premise; the parser targets RDF/XML), and
`semantics-rdf-based-only` (the catalog asserts `test:semantics
RDF-BASED` and explicitly denies `DIRECT`, so a Direct Semantics
reasoner has nothing to answer). `WebOnt-Thing-005` is the second kind.

## Disposition vocabulary

Each residual carries one of five labels, from the completeness
ledger's fixed vocabulary (issue
[#308](https://github.com/danbri/factoidal/issues/308)):

- **by-design** — the test asks for something outside what this engine
  claims. Every use below cites the W3C catalog's own metadata or a
  written scope decision, not a preference.
- **planned-family** — a real gap in a named family of missing
  reasoning, tracked and intended.
- **dependency-blocked** — waiting on a capability elsewhere in the
  engine.
- **disputed-fixture** — the fixture itself is defective or its
  expected verdict does not follow; documented per test.
- **environment** — toolchain or harness, not semantics. No OWL
  residual carries this label today.

## Residual failures — positive entailment (31 of 204)

Scored under DL from `type-positive-entailment.rdf`.

Seventeen of these carry `test:species FULL` **and** an explicit
`owl:NegativePropertyAssertion` in the catalog denying `test:species
DL` — the W3C suite states outright that they are not OWL DL
entailments. They are marked by-design on that citation. The owner
approved a flag-gated OWL Full engine mode on 2026-07-28 ("If we can do
it — eg under a flag or engine mode or api if not directly alongside
other OWL variants, then sure"), which would convert this block from
by-design to planned work once such a mode exists; no such mode exists
today, and the default DL engine deliberately does not derive these.

| Test | Disposition | Reason |
|---|---|---|
| `WebOnt-Class-001` | by-design | Catalog denies `test:species DL`. OWL Full meta-modeling: `rdfs:Class owl:equivalentClass owl:Class` from an empty premise. |
| `WebOnt-Class-002` | by-design | Catalog denies `test:species DL`. OWL Full vocabulary synonymy between `rdfs:Class` and `owl:Class` triples. |
| `WebOnt-Class-003` | by-design | Catalog denies `test:species DL`. Same OWL Full vocabulary synonymy, other direction. |
| `WebOnt-FunctionalProperty-003` | by-design | Catalog denies `test:species DL`. Functional + `owl:inverseOf` implies the inverse is InverseFunctional, an OWL Full property-characteristic axiom. |
| `WebOnt-FunctionalProperty-004` | by-design | Catalog denies `test:species DL`. Singleton range implies Functional — extensional reasoning over property ranges. |
| `WebOnt-InverseFunctionalProperty-003` | by-design | Catalog denies `test:species DL`. Dual of FunctionalProperty-003. |
| `WebOnt-InverseFunctionalProperty-004` | by-design | Catalog denies `test:species DL`. Singleton domain implies InverseFunctional. |
| `WebOnt-complementOf-001` | by-design | Catalog denies `test:species DL`. `owl:complementOf` treated as a symmetric RDF property, an OWL Full vocabulary-level axiom. |
| `WebOnt-equivalentProperty-005` | by-design | Catalog denies `test:species DL`. Equal property extensions imply `owl:equivalentProperty`, extensional not axiomatic. |
| `WebOnt-I5.24-002` | by-design | Catalog denies `test:species DL`. "OWL, unlike RDFS, uses iff semantics for range" over an `owl:intersectionOf` built from the range class. |
| `WebOnt-I5.3-014` | by-design | Catalog denies `test:species DL`. Self-describes as holding only under the RDFS-Compatible Semantics for OWL, not the RDF Semantics. |
| `WebOnt-I5.3-015` | by-design | Catalog denies `test:species DL`. Same RDFS-Compatible-Semantics corner case. |
| `WebOnt-I5.8-017` | by-design | Catalog denies `test:species DL`. Aliases of built-in datatypes at the OWL Full vocabulary level. |
| `WebOnt-extra-credit-002` | by-design | Catalog denies `test:species DL`. "A relationship between integer multiplication and OWL Full." |
| `WebOnt-extra-credit-003` | by-design | Catalog denies `test:species DL`. "Prime factorization can be expressed in OWL Full." |
| `WebOnt-extra-credit-004` | by-design | Catalog denies `test:species DL`. Harder prime-factorization variant of the same OWL Full encoding. |
| `rdfbased-sem-restrict-maxqcr-inst-obj-one` | by-design | Catalog denies `test:species DL`. Max-1 qualified cardinality forcing `owl:sameAs`, stated as an RDF-Based (Full) entailment. |
| `WebOnt-I5.8-004` | by-design | `test:status test;Extracredit` — the W3C suite marks it a bonus test. Exact datatype-facet interval counting ("precisely 128 values of `xsd:byte` that are also `xsd:unsignedInt`"). |
| `WebOnt-I5.5-005` | by-design | OWL 1 Full comprehension: premise is a bare class declaration, conclusion asserts an anonymous `owl:unionOf` class exists. Scope decision recorded in `docs/claude-rules/scope.md`. Also one of the two species fails below, where its disposition is disputed-fixture. |
| `WebOnt-I5.26-010` | by-design | OWL 1 Full comprehension: premise is a bare property declaration, conclusion asserts a `minCardinality 1` restriction exists. Same scope decision. |
| `WebOnt-I5.21-002` | planned-family | Property-characteristic propagation: `owl:disjointWith` needs full symmetric closure across an 11-class clique the premise states one-directionally. |
| `WebOnt-SymmetricProperty-002` | planned-family | Same family: extensional `owl:SymmetricProperty` semantics over an `owl:oneOf`-based domain. |
| `WebOnt-cardinality-001` | planned-family | Cardinality shorthand: `owl:cardinality N` is not yet expanded to the `owl:minCardinality` / `owl:maxCardinality` pair. |
| `WebOnt-cardinality-003` | planned-family | Same cardinality-shorthand rule. |
| `WebOnt-I5.24-003` | planned-family | OWL range-iff semantics: "a typical definition of range from description logic", needs range/intersection interaction. |
| `WebOnt-I5.24-004` | planned-family | Same range-iff rule, both directions. |
| `WebOnt-I5.8-010` | planned-family | Datatype value-space intersection: 0 is the only value in both `xsd:nonNegativeInteger` and `xsd:nonPositiveInteger`. |
| `WebOnt-oneOf-004` | planned-family | `owl:dataRange` enumeration over literals, not the IRI-list `owl:oneOf` comprehension that now passes. |
| `WebOnt-unionOf-003` | planned-family | Extensional `owl:unionOf` — deriving the union relationship from the members' extensions, not decomposing a stated union. |
| `WebOnt-unionOf-004` | planned-family | Inverse direction of unionOf-003, same extensional gap. |
| `WebOnt-equivalentProperty-004` | dependency-blocked | Premise property-inclusion sits outside the refuter's role hierarchy; needs role-hierarchy reasoning tracked in [#298](https://github.com/danbri/factoidal/issues/298). |

Two positive-entailment tests are skipped rather than failed:
`Qualified-cardinality-boolean` and `Qualified-cardinality-restricted-int`
ship only an OWL Functional-Style Syntax premise.

## Residual failures — inconsistency (3 of 127)

Scored under DL from `type-inconsistency.rdf`. All three report
`FAIL/unexpected-consistency`: the engine returns "consistent" where
the catalog expects a clash. Under-derivation, not a wrong entailment.

| Test | Disposition | Reason |
|---|---|---|
| `Minus Infinity is not in owl:real` | planned-family | Numeric datatype value-space reasoning: `owl:real` excludes `-INF`, which needs interval handling across `DataAllValuesFrom` / `DataOneOf` / `NegativeDataPropertyAssertion`. |
| `WebOnt-description-logic-502` | planned-family | "The classic 3 SAT problem" encoded as ten `owl:oneOf` enumerations on one class plus 45 three-literal clause classes. The engine returns a definite model with zero refuter cap trips: the clause constraints never reach the tableau, because a class expression's enumeration is read once per class rather than intersected across repeated `owl:oneOf`. A loading gap upstream of the refuter, not a search-budget one. |
| `WebOnt-description-logic-909` | disputed-fixture | Integer multiplication via chained `owl:FunctionalProperty` / `owl:inverseOf` cardinality arithmetic. The clash is not soundly derivable under Direct Semantics as the fixture is written, so the default engine keeps the satisfiable verdict; the owner approved a flag-gated arithmetic-semantics variant (2026-07-28, [#299](https://github.com/danbri/factoidal/issues/299)) rather than a test-ID exemption. Also carries `test:status test;Extracredit`. |

One inconsistency test is skipped: `WebOnt-Thing-005` asserts
`test:semantics RDF-BASED` and denies `DIRECT`.

## Residual failures — species identification (2 of 321 scored)

Scored from `syntax-dl.rdf` by the F\* `OWL2.SyntaxDL` checker (purely
syntactic, no closure or tableau). Both fails return `verdict=FULL`
where the catalog expects `DL`.

| Test | Disposition | Reason |
|---|---|---|
| `FS2RDF-literals-ar` | disputed-fixture | The RDF/XML premise's datatype IRIs are lowercased case-variants (`xsd:unsignedint`, `xsd:anyuri`, `xsd:datetime`) that are not in the OWL 2 datatype map, so the checker reports `reserved-vocabulary-as-datatype` and returns FULL. The catalog's DL label reflects its correctly-cased functional-syntax premise; the runner scores the RDF/XML one. Serialization defect in the fixture, not a checker gap. |
| `WebOnt-I5.5-005` | disputed-fixture | The classified graph is the header-less premise plus its comprehension conclusion, giving `conclusion: no-ontology-header` and a FULL verdict. Its sibling `I5.5-006` is classified on a strict subset of the same graph and is expected FULL, so no monotone graph classifier can call 005 DL while keeping 006 correct. Structurally blocked. |

## Residual failures — profile catalogs (2 each on RL, EL, QL)

`WebOnt-I5.5-005` and `WebOnt-I5.26-010` are the only fails in
`profile-RL.rdf`, `profile-EL.rdf`, and `profile-QL.rdf`. Both are
**by-design**: OWL 1 Full comprehension-principle entailments,
deliberately outside the OWL 2 RL / EL / QL closure, dispositioned in
`docs/claude-rules/scope.md`. Their per-test reasons are in the
positive-entailment table above.

## Disposition counts

Across the 35 distinct tests that fail in at least one catalog:

| Disposition | Count |
|---|---|
| by-design | 20 |
| planned-family | 12 |
| disputed-fixture | 2 |
| dependency-blocked | 1 |
| environment | 0 |

Counting distinct tests, so `WebOnt-I5.5-005` and `WebOnt-I5.26-010`
are each counted once even though they fail in four catalogs, and
`WebOnt-I5.5-005` is counted under its positive-entailment disposition
(by-design) rather than its species-checker one (disputed-fixture).

## Where the numbers live

- Live scores and history: [test-results dashboard]({{ '/test-results/' | url }}).
- Per-suite disposition ledger:
  [`docs/claude-rules/w3c-completeness-ledger.md`](https://github.com/danbri/factoidal/blob/claude/main/docs/claude-rules/w3c-completeness-ledger.md).
- Tracking issues:
  [#308](https://github.com/danbri/factoidal/issues/308) (profile EL/QL
  triage), [#209](https://github.com/danbri/factoidal/issues/209)
  (tableau epic), [#298](https://github.com/danbri/factoidal/issues/298)
  and [#299](https://github.com/danbri/factoidal/issues/299) (entailment
  and inconsistency waves).
- How the tableau works, with runnable cells:
  [OWL reasoning by model construction]({{ '/web/hub/30-owl-reasoning-tableau/' | url }}).
