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
| `profile-RL.rdf` | PositiveEntailment | RL | 30 pass, 0 fail (out of 30) |
| `profile-RL.rdf` | NegativeEntailment | RL | 6 pass, 0 fail (out of 6) |
| `profile-RL.rdf` | Consistency | RL | 76 pass, 0 fail (out of 76) |
| `profile-RL.rdf` | Inconsistency | RL | 14 pass, 0 fail (out of 14) |
| `profile-EL.rdf` | all four sections | RL | 120 pass, 0 fail (out of 120), 1 skipped |
| `profile-QL.rdf` | all four sections | RL | 87 pass, 0 fail (out of 87) |
| `type-positive-entailment.rdf` | PositiveEntailment | DL | 193 pass, 11 fail (out of 204), 2 skipped |
| `type-positive-entailment.rdf` | Consistency | DL | 204 pass, 0 fail (out of 204), 2 skipped |
| `type-negative-entailment.rdf` | NegativeEntailment | DL | 23 pass, 0 fail (out of 23) |
| `type-negative-entailment.rdf` | Consistency | DL | 23 pass, 0 fail (out of 23) |
| `type-consistency.rdf` | Consistency | DL | 352 pass, 0 fail (out of 352), 2 skipped |
| `type-inconsistency.rdf` | Inconsistency | DL | 125 pass, 2 fail (out of 127), 1 skipped |
| `semantics-direct.rdf` | Consistency | DL | 351 pass, 0 fail (out of 351), 2 skipped |
| `syntax-dl.rdf` | species (DL vs Full) | syntactic | 319 pass, 2 fail (out of 321 scored), 2 skipped |

The `semantics-direct.rdf` catalog also re-scores the positive-entailment
(173 pass, 31 fail), negative-entailment (23 pass, 0 fail), and
inconsistency (125 pass, 2 fail) sections; those numbers agree
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

## Residual failures — positive entailment (11 of 204)

Scored under DL from `type-positive-entailment.rdf`.

Every remaining fail is one of three kinds: an OWL Full entailment the
catalog itself denies is OWL DL (`test:species FULL` plus an explicit
`owl:NegativePropertyAssertion` against `test:species DL`), a
`test:status test;Extracredit` bonus test, or one genuinely-hard
case tracked as planned work. Three of the OWL Full tests
(`WebOnt-Class-001/-002/-003`) PASS under the flag-gated
`--semantics rdf-based-full` engine mode landed 2026-07-29 (owner-approved
2026-07-28); the default DL engine deliberately does not derive them.

| Test | Disposition | Reason |
|---|---|---|
| `WebOnt-Class-001` | by-design | Catalog denies `test:species DL`. OWL Full meta-modeling; PASSES under `--semantics rdf-based-full`. |
| `WebOnt-Class-002` | by-design | Catalog denies `test:species DL`. OWL Full `rdfs:Class`/`owl:Class` synonymy; PASSES under `--semantics rdf-based-full`. |
| `WebOnt-Class-003` | by-design | Catalog denies `test:species DL`. Same synonymy, other direction; PASSES under `--semantics rdf-based-full`. |
| `WebOnt-I5.3-014` | by-design | Catalog denies `test:species DL`. Self-describes as holding only under the RDFS-Compatible Semantics for OWL. |
| `WebOnt-I5.3-015` | by-design | Catalog denies `test:species DL`. Same RDFS-Compatible-Semantics corner case. |
| `WebOnt-I5.8-017` | by-design | Catalog denies `test:species DL`. Aliases of built-in datatypes at the OWL Full vocabulary level. |
| `WebOnt-extra-credit-002` | by-design | Catalog denies `test:species DL`. "A relationship between integer multiplication and OWL Full." |
| `WebOnt-extra-credit-003` | by-design | Catalog denies `test:species DL`. "Prime factorization can be expressed in OWL Full." |
| `WebOnt-extra-credit-004` | by-design | Catalog denies `test:species DL`. Harder prime-factorization variant. |
| `WebOnt-I5.8-004` | by-design | `test:status test;Extracredit` — a bonus test. Exact datatype-facet interval counting ("precisely 128 values of `xsd:byte` that are also `xsd:unsignedInt`"). |
| `WebOnt-I5.8-010` | planned-family | Datatype value-space intersection: 0 is the only value in both `xsd:nonNegativeInteger` and `xsd:nonPositiveInteger`. |

Two positive-entailment tests are skipped rather than failed, and sit
outside the 204 denominator: `Qualified-cardinality-boolean` and
`Qualified-cardinality-restricted-int` ship only an OWL
Functional-Style Syntax premise. The engine **does** have an F\*
functional-syntax parser (`Parser.OWLFunctional`, 24 constructs), and
it is wired into every scoring path; what these two need is the
cardinality family (`DataExactCardinality`), which is outside its
current subset — so the parser returns no result and the runner skips
honestly rather than scoring a test it did not read. Both are
finite-value-space entailments (`xsd:boolean` has exactly 2 values; the
restricted integer range [1,3] exactly 3, so an exact-cardinality-N
restriction forces every member), tracked with the datatype
value-space work.

Fixed since this page's first publication (2026-07-28, from 31 residuals
to 11): the metamodeling family — `I5.24-002/-003/-004` (facts derived
ABOUT a property's rdfs:range / rdfs:domain, see below) and
`SymmetricProperty-002` (extensional `owl:SymmetricProperty`) on
2026-07-29; the property-characteristic family
(`complementOf-001`, `FunctionalProperty-003/-004`,
`InverseFunctionalProperty-003/-004`, `equivalentProperty-004/-005`,
`I5.21-002`), cardinality shorthand (`cardinality-001/-003`,
`rdfbased-sem-restrict-maxqcr-inst-obj-one`), and the comprehension
family (`unionOf-003/-004`, `oneOf-004`, `I5.5-005`, `I5.26-010`) —
closure-rule and witness-layer work on 2026-07-28/29, each rule derived
from the OWL 2 RDF-Based Semantics conditions or the OWL 2 RL/RDF rule
tables (see the granular commits on the two wave branches).

### What the I5.24 / SymmetricProperty family needed

Recorded here because the family was mis-labelled "range-iff" while it
was open, and the label was wrong in a way that would mislead anyone
reading these rules later.

OWL does **not** reinterpret `rdfs:range`. The reading of a range
triple stays one-way — from `P rdfs:range C` and `x P y` infer
`y rdf:type C`, and nothing more. A range declaration is never a
minimality claim: many classes are ranges of the same property
simultaneously.

What the I5.24 conclusions exercise is **metamodeling**. Under the OWL
2 RDF-Based Semantics `rdfs:range` is an ordinary property relating two
ordinary resources (a property and a class), so the range relationship
is itself an object of discourse, and Table 5.8 states when a pair
belongs to it. That is what licenses deriving new facts *about* a
property's range rather than only consuming declared ones — including
the behaviour the fixtures' `owl:intersectionOf` conclusions express:
declare two ranges and the ranges compose, so their intersection is
also a range. `WebOnt-SymmetricProperty-002` is a different mechanism
again — Table 5.13's condition on `owl:SymmetricProperty` quantifies
over the property's whole extension in the interpretation, which a
forward-chaining closure can only check where the premise pins that
extension from above (there: inverse-functionality plus an
`owl:oneOf` range whose *own* condition is an equality). Rule-by-rule
citations are in `formal/fstar/OWL.Closure.fsti`.

## Residual failures — inconsistency (3 of 127)

Scored under DL from `type-inconsistency.rdf`. Both report
`FAIL/unexpected-consistency`: the engine returns "consistent" where
the catalog expects a clash. Under-derivation, not a wrong entailment.

| Test | Disposition | Reason |
|---|---|---|
| `Minus Infinity is not in owl:real` | planned-family | Numeric datatype value-space reasoning: `owl:real` excludes `-INF`, which needs interval handling across `DataAllValuesFrom` / `DataOneOf` / `NegativeDataPropertyAssertion`. |
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

## Residual failures — profile catalogs (none)

As of 2026-07-29 every section of `profile-RL.rdf`, `profile-EL.rdf`,
and `profile-QL.rdf` is at 0 fail (RL 126 scored, EL 120 scored + 1
skip, QL 87 scored). The former residual pair `WebOnt-I5.5-005` /
`WebOnt-I5.26-010` passes via the stratified comprehension-witness
layer.

## Disposition counts

Across the 15 distinct tests that fail in at least one catalog
(11 positive-entailment, 2 inconsistency, 2 species; no overlaps —
`WebOnt-I5.5-005` now fails only in the species checker):

(`WebOnt-description-logic-502` left this list on 2026-07-28: its
nominal-branching refutation was landing right at the refuter's
10-CPU-second budget — passing on an idle container, failing under
load. The caps now run on CPU time, and the 127-test
inconsistency-scoring path gets a 30-CPU-second refuter cap, so the
verdict is deterministic: 125 pass, 2 fail (out of 127) at any load.)

| Disposition | Count |
|---|---|
| by-design | 10 |
| planned-family | 2 |
| disputed-fixture | 3 |
| dependency-blocked | 0 |
| environment | 0 |

Counting distinct tests. The 3 disputed-fixture entries are the two
species-checker residuals (`FS2RDF-literals-ar`, `WebOnt-I5.5-005` —
the latter now fails ONLY there) and `WebOnt-description-logic-909`
(inconsistency; flag-gated arithmetic-semantics variant approved,
[#299](https://github.com/danbri/factoidal/issues/299)). The
`Minus Infinity is not in owl:real` inconsistency fail is the one
planned-family entry outside positive entailment; the only one inside
it is `WebOnt-I5.8-010` (datatype value-space intersection).

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
