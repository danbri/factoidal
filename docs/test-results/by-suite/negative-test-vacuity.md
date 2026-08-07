# Negative-test vacuity check (issue #333)

A negative test asserts a non-entailment. An engine that derives nothing passes every one of them for free. This table says how many negative tests the engine actually did work on.

## Scored: entailment-shaped negatives

| suite | negative tests | worked | weak | vacuous | exempt | unscored | untrusted | error |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| rdf-mt | 19 | 1 | 3 | 11 | 4 | 0 | 0 | 0 |
| rdf12-semantics | 15 | 0 | 0 | 8 | 5 | 0 | 0 | 2 |
| sparql11-entailment | 8 | 3 | 2 | 0 | 0 | 3 | 0 | 0 |
| **all scored suites** | **42** | **4** | **5** | **19** | **9** | **3** | **0** | **2** |

Read as: 42 negative tests examined; 4 did premise-attributable, on-target work; 5 did only weak work; 19 are vacuous; 9 are exempt on a data-derived ground; 3 unscored (no criterion defined for their regime); 0 untrusted; 2 errored (out of 42).

## Vacuous tests, by name

### rdf-mt (11 vacuous out of 19 negative)

| test | regime | reason | premise triples | derived |
|---|---|---|---:|---:|
| `datatypes-intensional-xsd-integer-decimal-compatible` | RDFS | no-conclusion-and-no-consistency-check | - | 0 |
| `datatypes-non-well-formed-literal-1` | RDFS | no-conclusion-and-no-consistency-check | - | 0 |
| `rdf-charmod-uris-test003` | RDF | closure-adds-nothing | 1 | 0 |
| `rdf-charmod-uris-test004` | RDF | closure-adds-nothing | 1 | 0 |
| `rdfs-container-membership-superProperty-test001` | RDFS | closure-adds-nothing | 1 | 0 |
| `rdfs-subClassOf-a-Property-test001` | RDFS | no-conclusion-and-no-consistency-check | - | 0 |
| `statement-entailment-test001` | RDF | closure-adds-nothing | 9 | 0 |
| `statement-entailment-test002` | RDF | closure-adds-nothing | 1 | 0 |
| `statement-entailment-test003` | RDFS | closure-adds-nothing | 9 | 0 |
| `statement-entailment-test004` | RDF | closure-adds-nothing | 1 | 0 |
| `xmlsch-02-whitespace-facet-1` | RDFS | closure-adds-nothing | 1 | 0 |

### rdf12-semantics (8 vacuous out of 15 negative)

| test | regime | reason | premise triples | derived |
|---|---|---|---:|---:|
| `double-round-different` | RDF | closure-adds-nothing | 1 | 0 |
| `double-zero` | RDF | closure-adds-nothing | 1 | 0 |
| `float-round-different` | RDF | closure-adds-nothing | 1 | 0 |
| `float-zero` | RDF | closure-adds-nothing | 1 | 0 |
| `json-array-unordered` | RDF | closure-adds-nothing | 1 | 0 |
| `json-round-different` | RDF | closure-adds-nothing | 1 | 0 |
| `json-zero` | RDF | closure-adds-nothing | 1 | 0 |
| `json-zero-array` | RDF | closure-adds-nothing | 1 | 0 |

## Weak tests, by name

### rdf-mt (3 weak)

| test | regime | reason | derived | non-reflexive | on-target |
|---|---|---|---:|---:|---:|
| `horst-01-subPropertyOf-intensional` | RDFS | reflexive-only | 2 | 0 | - |
| `rdfs-domain-and-range-intensionality-domain` | RDFS | reflexive-only | 2 | 0 | - |
| `rdfs-domain-and-range-intensionality-range` | RDFS | reflexive-only | 2 | 0 | - |

### sparql11-entailment (2 weak)

| test | regime | reason | derived | non-reflexive | on-target |
|---|---|---|---:|---:|---:|
| `RDF inference test` | RDF | reflexive-only | 1 | 0 | - |
| `RDFS inference test to show that neither literals in subject position nor newly introduced surrogate blank nodes are to be returned in query answers` | RDFS | reflexive-only | 1 | 0 | - |

## Tests where the engine did work, with the numbers

| suite | test | regime | premise | closure | derived | non-reflexive | on-target | relevance checked |
|---|---|---|---:|---:|---:|---:|---:|---|
| rdf-mt | `horst-01-subClassOf-intensional` | RDFS | 2 | 25 | 7 | 6 | 1 | yes |
| sparql11-entailment | `bnodes are not existentials` | OWL-Direct | 11 | 261 | 38 | 23 | n/a | no |
| sparql11-entailment | `sparqldl-05.rq: simple undistinguished variable test.` | OWL-Direct | 14 | 257 | 31 | 18 | n/a | no |
| sparql11-entailment | `sparqldl-06.rq: cycle of undistinguished variables` | OWL-Direct | 16 | 397 | 169 | 135 | n/a | no |

## Exemptions, with the data property each rests on

| suite | test | exemption | evidence |
|---|---|---|---|
| rdf-mt | `datatypes-test009` | regime-has-no-closure | the test declares mf:entailmentRegime "simple"; simple entailment has no derivation rules, so an empty derivation set is correct rather than a defect |
| rdf-mt | `rdfms-xmllang-test007a` | regime-has-no-closure | the test declares mf:entailmentRegime "simple"; simple entailment has no derivation rules, so an empty derivation set is correct rather than a defect |
| rdf-mt | `rdfms-xmllang-test007b` | regime-has-no-closure | the test declares mf:entailmentRegime "simple"; simple entailment has no derivation rules, so an empty derivation set is correct rather than a defect |
| rdf-mt | `rdfms-xmllang-test007c` | regime-has-no-closure | the test declares mf:entailmentRegime "simple"; simple entailment has no derivation rules, so an empty derivation set is correct rather than a defect |
| rdf12-semantics | `bnodes-in-triple-term-subject-and-object-fail` | regime-has-no-closure | the test declares mf:entailmentRegime "simple"; simple entailment has no derivation rules, so an empty derivation set is correct rather than a defect |
| rdf12-semantics | `constrained-bnodes-in-triple-term-fail` | regime-has-no-closure | the test declares mf:entailmentRegime "simple"; simple entailment has no derivation rules, so an empty derivation set is correct rather than a defect |
| rdf12-semantics | `opaque-dir-language-string` | regime-has-no-closure | the test declares mf:entailmentRegime "simple"; simple entailment has no derivation rules, so an empty derivation set is correct rather than a defect |
| rdf12-semantics | `triple-term-not-asserted` | regime-has-no-closure | the test declares mf:entailmentRegime "simple"; simple entailment has no derivation rules, so an empty derivation set is correct rather than a defect |
| rdf12-semantics | `triple-terms-no-spurious` | regime-has-no-closure | the test declares mf:entailmentRegime "simple"; simple entailment has no derivation rules, so an empty derivation set is correct rather than a defect |

## Unscored and errored tests, with the reason

| suite | test | status | reason |
|---|---|---|---|
| rdf12-semantics | `malformed-literal-bnode-neg` | error | `factoidal --dump` refused the premise, so no closure measurement is possible for this test. The suite runner uses its own lenient loader, so the runner still scores the test; the disagreement between the two loaders is itself worth a look. CLI said: Error: third_party/testing/w3c/rdf/rdf12/rdf-sema |
| rdf12-semantics | `malformed-literal-no-spurious` | error | `factoidal --dump` refused the premise, so no closure measurement is possible for this test. The suite runner uses its own lenient loader, so the runner still scores the test; the disagreement between the two loaders is itself worth a look. CLI said: Error: third_party/testing/w3c/rdf/rdf12/rdf-sema |
| sparql11-entailment | `D-Entailment test to show that  neither literals in subject position n` | unscored | the engine does not implement this regime as a graph closure (D-entailment is handled by literal value equality, RIF by the RIF rule engine), so closure growth is the wrong measurement and no criterion for it is defined here |
| sparql11-entailment | `RIF Core WG tests: Modeling Brain Anatomy` | unscored | the engine does not implement this regime as a graph closure (D-entailment is handled by literal value equality, RIF by the RIF rule engine), so closure growth is the wrong measurement and no criterion for it is defined here |
| sparql11-entailment | `RIF Core WG tests: RDF Combination Blank Node` | unscored | the engine does not implement this regime as a graph closure (D-entailment is handled by literal value equality, RIF by the RIF rule engine), so closure growth is the wrong measurement and no criterion for it is defined here |

## Side findings (engine behaviour noticed while measuring)

- **ntriples-serializer-does-not-escape-literals** — `factoidal --dump` emits literals containing a newline or a double quote verbatim, instead of as the \n and \" escapes the N-Triples grammar requires. The output is therefore not re-readable as N-Triples for any graph with such a literal.
  - effect here: manifest lines carrying multi-line rdfs:comment or embedded-ontology literals cannot be split into triples and are counted in nt_lines_skipped. It is why the OWL 2 catalogs are censused but not scored. It does not affect any verdict here: every predicate this tool reads (rdf:type, mf:action, mf:result, mf:entailmentRegime, mf:entries, sd:entailmentRegime) has an IRI or a single-line literal object.
- **cli-and-runner-loaders-disagree-on-malformed-literals** — third_party/testing/w3c/rdf/rdf12/rdf-semantics/malformed-literal.ttl is rejected by `factoidal --dump` under the issue-325 zero-triples guard, while the suite runner's own loader accepts it and scores the two tests that use it as their premise.
  - effect here: those two tests are recorded `error`, not vacuous — the tool cannot measure what it cannot load.

## Census: every negative-style class found in the vendored manifests

| class | count | of all classified entries | scored | why |
|---|---:|---:|---|---|
| consistency | 125 | 3966 | not-scored | OWL ConsistencyTest asserts an ontology IS consistent, so a reasoner that derives nothing passes it. The measured path is owl_runner's DL/Tableau regime, which `factoidal entail` does not expose (it offers RDFS and OWL-RL materialisation only), so this tool cannot observe the derivations that path makes. |
| entailment-negative | 80 | 3966 | partly-scored | The rdf-mt and rdf12 rdf-semantics manifests are scored with the closure criterion. The OWL 2 catalogs are NOT: their premise and non-conclusion ontologies are embedded as literals inside the catalog, and the engine's own N-Triples serializer emits those literals with raw newlines and unescaped quotes, so they cannot be recovered through `factoidal --dump` without a second parser. Recovering them some other way would mean this tool parsing RDF itself, which it does not do. Count of unrecoverable literal lines per catalog is in census_manifests[].nt_lines_skipped. |
| entailment-positive | 476 | 3966 | not-vacuity-prone | A positive entailment test requires the engine to derive the conclusion. A derive-nothing engine fails it. |
| eval-negative | 8 | 3966 | not-scored | Same shape as syntax-negative: the parser must reject at a specific point. Same missing error-offset API. |
| eval-positive | 496 | 3966 | not-vacuity-prone | A reject-all parser fails these. |
| inconsistency | 128 | 3966 | not-vacuity-prone | An InconsistencyTest requires the engine to PRODUCE a contradiction. A derive-nothing engine fails it. Recorded for contrast with the consistency row, not flagged. |
| query-evaluation | 645 | 3966 | partly-scored | A SPARQL QueryEvaluationTest is negative-shaped exactly when its expected result set is empty -- then a return-nothing engine passes it. Those are identified here by counting <result> elements in the expected .srx and scored with the same closure criterion applied to the test's data graph, when the test declares an entailment regime. Tests with non-empty expected results are not vacuity-prone and are not flagged. |
| syntax-negative | 666 | 3966 | not-scored | A negative SYNTAX test is a different shape: 'did work' means the parser reached and rejected a specific construct, not that it derived triples, so the closure criterion does not apply. Scoring it properly needs the byte offset at which the parser gave up, which the F* parsers do not surface through any CLI today (they return None). The manifest-level anti-vacuity witness that IS computed here is `positive_siblings`: the count of positive syntax/eval tests in the same manifest. A parser that rejects everything fails all of those, so a manifest with passing positive siblings cannot be scored by a reject-all engine. That witness is per-manifest, not per-test: it does not show the rejection happened for the right reason. |
| syntax-positive | 710 | 3966 | not-vacuity-prone | A reject-all parser fails these. |
| validation | 617 | 3966 | not-scored | A SHACL/ShEx ValidationTest carries its polarity in the expected validation report (sh:conforms plus the sh:result list), not in its rdf:type, so it splits into both a vacuity-prone half (expected-conformant: passed for free by a validator that evaluates no constraint) and a non-vacuity-prone half. Splitting them needs the expected report read per test and, to score, a count of constraint components actually evaluated -- which no runner emits today. |
| validation-negative | 15 | 3966 | not-scored | SHACL/ShEx/JSON-Schema expected-invalid tests are passed for free by a report-everything-invalid validator, not by a derive-nothing one. Their degenerate engine is the opposite of the entailment case, so the closure criterion does not transfer. Scoring needs the identity of the constraint component that fired, compared against the expected report -- that is a validator-report comparison, deliberately left to the SHACL/ShEx runners. |
