# Specification coverage ledger — implemented, vendored, wired, scored

> **Landed 2026-09-03, twelve days after it was written.** It sat on an
> abandoned agent branch and was recovered when that worktree was deleted.
> Its scores are quoted from `docs/test-results/latest.json` at commit
> `6da70ea7` (2026-08-22); the same file at commit `7e1fa377b`
> (2026-09-03) is the current one, and the Lean tree has moved further
> since. Read the structure — which specification has an upstream suite,
> whether it is vendored, whether it is wired to a harness — as current,
> and re-read every number from `latest.json` before quoting it.

Date: 2026-08-23. Written to answer one question: **for every
specification this project implements, does an official conformance
suite exist upstream, is that suite vendored here, is it wired into a
harness, and what does it score?**

Sources, all read in this session:

- Implemented: `formal/fstar/*.fst` (212 modules) and
  `formal/lean4/L4Factoidal/` + `formal/lean4/Harness/`.
- Vendored: `.gitmodules` (15 submodules) and every directory under
  `third_party/testing/` plus `third_party/qudt/`.
- Wired: `.github/test-suites/*.yaml` (83 files, of which 81 are
  suites; `_foundational.yaml` and `_README.md` are not),
  `tools/dispatch_test_suites.sh`, `tools/affected-tests.sh`,
  `formal/fstar/generate-report.sh`, `w3c-tests.sh`,
  `formal/lean4/Harness/` (`lake exe l4w3c` + probes).
- Scored: `docs/test-results/latest.json`, timestamp
  `2026-08-22 22:24 UTC`, commit `6da70ea7`, branch `claude/main`.
  Where a number is not in that file, this ledger says so instead of
  inventing one.

Scores below are quoted from `latest.json` unless the row says
otherwise. Every number is written as "N pass, N fail (out of N)".

## 1. Two harnesses, one of which is invisible to the dispatcher

Two independent things run conformance suites:

1. **The F\* harness.** `formal/fstar/generate-report.sh` (driven by
   `./w3c-tests.sh`) runs the full battery and writes
   `docs/test-results/latest.json`. Separately,
   `.github/test-suites/*.yaml` describes 81 suites so
   `tools/dispatch_test_suites.sh` and `tools/affected-tests.sh` can
   run only the suites a diff touches. **These two sets are not the
   same set.** Four suites that `generate-report.sh` runs — `rdf12`,
   `rdf12c14n`, `rdf12entail`, `sparql12` — have no yaml at all, so a
   diff that breaks RDF 1.2 or SPARQL 1.2 selects no suite.
2. **The Lean harness.** `formal/lean4/Harness/Main.lean`
   (`lake exe l4w3c <manifest.ttl>…`) plus 15 probe modules
   (`CsvwProbe`, `CsvwRdfRun`, `CanonProbe`, `JsonLdProbe`,
   `JsonLdApiProbe`, `OwlProbe`, `PropProbe`, `ProtocolRun`,
   `RdfXmlProbe`, `ShaclProbe`, `SparqlSyntaxProbe`, `TurtleProbe`,
   `VcProbe`, `Differential`, `Compare`). **Zero yaml manifests
   describe any of it.** No Lean score reaches
   `docs/test-results/latest.json`; the only recorded Lean numbers are
   prose in `docs/designissues/2026-08-22-lean-fstar-parity-ledger.md`
   and `formal/lean4/README.md`.

That is the structural finding: the owner's goal of "a harness for all
specs" is blocked less by missing test data than by two harnesses that
do not share a manifest format.

## 2. The table

Columns: **Spec** | **Version** | **Official suite upstream** |
**Vendored here** | **F\* yaml** | **Lean harness** | **Latest score**
| **Gap**.

`—` means "not applicable". "never run" means no number exists in
`latest.json`.

### RDF core syntaxes and semantics

| Spec | Version | Official suite upstream | Vendored here | F\* yaml | Lean harness | Latest score | Gap |
|---|---|---|---|---|---|---|---|
| [N-Triples](https://www.w3.org/TR/n-triples/) | RDF 1.1 | [w3c/rdf-tests](https://github.com/w3c/rdf-tests) `rdf/rdf11/rdf-n-triples` | submodule `third_party/testing/w3c` | `rdf-n-triples.yaml` | yes (`l4w3c`) | 70 pass, 0 fail (out of 70) | none |
| [N-Quads](https://www.w3.org/TR/n-quads/) | RDF 1.1 | w3c/rdf-tests `rdf/rdf11/rdf-n-quads` | same submodule | `rdf-n-quads.yaml` | yes | 87 pass, 0 fail (out of 87) | none |
| [Turtle](https://www.w3.org/TR/turtle/) | RDF 1.1 | w3c/rdf-tests `rdf/rdf11/rdf-turtle` | same submodule | `rdf-turtle.yaml` | yes | 313 pass, 0 fail (out of 313) | none |
| [TriG](https://www.w3.org/TR/trig/) | RDF 1.1 | w3c/rdf-tests `rdf/rdf11/rdf-trig` | same submodule | `rdf-trig.yaml` | yes | 356 pass, 0 fail (out of 356) | none |
| [RDF/XML](https://www.w3.org/TR/rdf-syntax-grammar/) | RDF 1.1 | w3c/rdf-tests `rdf/rdf11/rdf-xml` | same submodule | `rdf-xml.yaml` | yes | 166 pass, 0 fail (out of 166) | Lean side 130 pass, 2 fail (out of 132), per the parity ledger |
| [RDF Semantics](https://www.w3.org/TR/rdf11-mt/) | RDF 1.1 | w3c/rdf-tests `rdf/rdf11/rdf-mt` | same submodule | `rdf-mt.yaml` | yes | 38 pass, 0 fail, 1 unsupported (out of 39) | none |
| [RDF 1.2 syntaxes](https://www.w3.org/TR/rdf12-n-triples/) | RDF 1.2 | w3c/rdf-tests `rdf/rdf12/` (n-triples, n-quads, turtle, trig, xml) | same submodule | **no yaml** | yes | 242 pass, 0 fail (out of 242) | **kind (c)** — run only by `generate-report.sh --rdf12`; invisible to `affected-tests.sh` |
| [RDF 1.2 canonical N-Triples/N-Quads](https://www.w3.org/TR/rdf12-n-triples/#canonical-ntriples) | RDF 1.2 | w3c/rdf-tests `rdf/rdf12/*/c14n` | same submodule | **no yaml** | yes | 82 pass, 0 fail (out of 82) | **kind (c)** — same |
| [RDF 1.2 Semantics](https://www.w3.org/TR/rdf12-semantics/) | RDF 1.2 | w3c/rdf-tests `rdf/rdf12/rdf-semantics` | same submodule | **no yaml** | manifest does not load | 41 pass, 3 fail, 3 skip (out of 47) | **kind (c)** — no yaml, 3 reds, and the manifest carries an upstream undeclared `test:` prefix (see §4) |
| [RDF Dataset Canonicalization](https://www.w3.org/TR/rdf-canon/) | RDFC-1.0 | [w3c/rdf-canon](https://github.com/w3c/rdf-canon) | submodule `third_party/testing/rdf-canon` | `rdfc10.yaml` | yes (`CanonProbe`) | 86 pass, 0 fail (out of 86) | none |

### SPARQL

| Spec | Version | Official suite upstream | Vendored here | F\* yaml | Lean harness | Latest score | Gap |
|---|---|---|---|---|---|---|---|
| [SPARQL Query](https://www.w3.org/TR/sparql11-query/) | 1.1 | w3c/rdf-tests `sparql/sparql11` | submodule `third_party/testing/w3c` | `sparql11-query.yaml` | yes | part of 631 pass, 0 fail (out of 631) | none |
| [SPARQL Update](https://www.w3.org/TR/sparql11-update/) | 1.1 | same | same | `sparql11-update.yaml` | yes | part of the 631 | none |
| [SPARQL Protocol](https://www.w3.org/TR/sparql11-protocol/) | 1.1 | same | same | `sparql11-protocol.yaml` | yes (`ProtocolRun`) | 34 pass, 0 fail (out of 34) | none |
| [SPARQL Graph Store Protocol](https://www.w3.org/TR/sparql11-http-rdf-update/) | 1.1 | same (`http-rdf-update`) | same | folded into `sparql11-protocol.yaml` | yes (`GraphStore`) | 19 pass, 0 fail (out of 19) | none |
| [SPARQL Service Description](https://www.w3.org/TR/sparql11-service-description/) | 1.1 | same | same | `sparql11-service-description.yaml` | yes | 3 pass, 0 fail (out of 3) | none |
| [SPARQL Federated Query](https://www.w3.org/TR/sparql11-federated-query/) | 1.1 | same | same | `sparql11-federated-query.yaml` | partial | 7 pass, 0 fail (out of 7) + 3 syntax-fed | none |
| [SPARQL Entailment Regimes](https://www.w3.org/TR/sparql11-entailment/) | 1.1 | same | same | `sparql11-entailment.yaml` | 30 unsupported | 70 pass, 0 fail (out of 70) | Lean side does not answer the 30 OWL-Direct / OWL-RDF-Based / RIF entries |
| [SPARQL Query](https://www.w3.org/TR/sparql12-query/) | **1.2** | w3c/rdf-tests `sparql/sparql12` | same submodule | **no yaml** | not run | 254 pass, 0 fail (out of 254) | **kind (c)** — run only by `generate-report.sh --sparql12` |
| SPARQL Query | 1.0 | w3c/rdf-tests `sparql/sparql10` | same submodule | **no yaml** | no | never run | deliberate — iron rule #5 says never default to 1.0 when 1.1 exists. Recorded here for completeness, not proposed as work |

### Shapes, mapping, rules

| Spec | Version | Official suite upstream | Vendored here | F\* yaml | Lean harness | Latest score | Gap |
|---|---|---|---|---|---|---|---|
| [SHACL](https://www.w3.org/TR/shacl/) | 1.0 Core | [w3c/data-shapes](https://github.com/w3c/data-shapes) | submodule `third_party/testing/shacl` | `shacl-core.yaml` | yes (`ShaclProbe`) | 98 pass, 0 fail (out of 98) | none |
| SHACL SPARQL constraints | 1.0 | same | same | `shacl-sparql.yaml` | yes | 22 pass, 0 fail (out of 22) | none |
| [SHACL 1.2 Core](https://www.w3.org/TR/shacl12-core/) | 1.2 | same repo, `shacl12-test-suite` | same | `shacl12-core.yaml` | no | 138 pass, 0 fail (out of 138) | Lean gap only |
| SHACL 1.2 node expressions | 1.2 | same | same | `shacl12-node-expr.yaml` | no | 142 pass, 0 fail (out of 142) | Lean gap only |
| SHACL 1.2 SPARQL | 1.2 | same | same | `shacl12-sparql.yaml` | no | 25 pass, 0 fail (out of 25) | Lean gap only |
| SHACL 1.2 rules | 1.2 | same | same | `shacl12-rules.yaml`, `shacl12-rules-syntax.yaml` | no | 11 pass, 0 fail (out of 11); syntax 62 pass, 0 fail (out of 62); wellformed 7 pass, 0 fail (out of 7); stratification 8 pass, 0 fail (out of 8) | Lean gap only |
| [ShEx](https://shex.io/shex-semantics/) | 2.1 | [shexSpec/shexTest](https://github.com/shexSpec/shexTest) | submodule `third_party/testing/shex` | `shex.yaml` | modules only | 1182 pass, 0 fail (out of 1182) | Lean side has no runner |
| ShEx negative syntax (ShExC) | 2.1 | same, `negativeSyntax/manifest.ttl` | same | `shex-negative-syntax.yaml` | no | **`present: false`, 0 pass, 0 fail (out of 0)** — the yaml comment claims 100 pass, 0 fail (out of 100), measured 2026-07-10 | **kind (c)** — the suite did not run in the 2026-08-22 report |
| [RML core](https://kg-construct.github.io/rml-core/spec/) | 1.0 | [kg-construct/rml-core](https://github.com/kg-construct/rml-core) | submodule | `rml.yaml` | modules only | 76 pass, 0 fail (out of 76) | none |
| [RML I/O](https://kg-construct.github.io/rml-io/spec/) | 1.0 | [kg-construct/rml-io](https://github.com/kg-construct/rml-io) | submodule | `rml-io.yaml` | no | 17 pass, 1 fail, 55 skip (out of 73) | 55 skips are the largest untouched block in any wired suite |
| RML containers (rml-cc) | 1.0 | [kg-construct/rml-cc](https://github.com/kg-construct/rml-cc) | submodule, 47 test-case dirs | **no yaml** | no | never run | **kind (b)** |
| RML functions (rml-fnml) | 1.0 | [kg-construct/rml-fnml](https://github.com/kg-construct/rml-fnml) | submodule, 32 test-case dirs | **no yaml** | no | never run | **kind (b)** |
| RML-star | 1.0 | [kg-construct/rml-star](https://github.com/kg-construct/rml-star) | submodule, 30 test-case dirs | **no yaml** | no | never run | **kind (b)** |
| RML legacy test cases | — | [kg-construct/rml-test-cases](https://github.com/kg-construct/rml-test-cases) | submodule `third_party/testing/rml` | referenced by `rml.yaml` triggers only | no | never run as its own suite | superseded by the per-module suites; not proposed as work |
| [RIF Core](https://www.w3.org/TR/rif-core/) | 1.0 | W3C RIF Test Cases (wiki, archived) | vendored snapshot `third_party/testing/rif` + `rif-core-suite` | `rif.yaml` | modules only | 46 pass, 0 fail, 1 local override, 3 skip (out of 50) | none |
| [ISO Schematron](https://www.iso.org/standard/74515.html) | ISO 19757-3 | no free official suite; [Schematron/schematron](https://github.com/Schematron/schematron) carries the reference skeleton + cases | vendored 8 hand-built cases | `schematron.yaml` | modules only | 8 pass, 0 fail (out of 8) | **kind (a)** — 8 self-authored cases is not a conformance claim |

### OWL

| Spec | Version | Official suite upstream | Vendored here | F\* yaml | Lean harness | Latest score | Gap |
|---|---|---|---|---|---|---|---|
| [OWL 2 profiles — RL](https://www.w3.org/TR/owl2-profiles/#OWL_2_RL) | 2 | [W3C OWL 2 test suite](https://www.w3.org/2009/11/owl-test/) | vendored `third_party/testing/owl/profile-RL.rdf` | `owl-profile-rl.yaml` | `OwlProbe` | 30 pass, 0 fail (out of 30) | none |
| OWL 2 profiles — QL | 2 | same | `profile-QL.rdf` | `owl-profile-ql.yaml` | partial | 87 pass, 0 fail (out of 87) | Lean side 76 pass, 11 fail (out of 87) |
| OWL 2 profiles — EL | 2 | same | `profile-EL.rdf` | `owl-profile-el.yaml` | no | 119 pass, 1 fail (out of 120) | 1 red |
| [OWL 2 DL species](https://www.w3.org/TR/owl2-syntax/#Ontologies) | 2 | same | `syntax-dl.rdf` | `owl-syntax-dl.yaml` | no | 319 pass, 2 fail, 2 skip (out of 323) | 2 reds |
| [OWL 2 Direct Semantics](https://www.w3.org/TR/owl2-direct-semantics/) | 2 | same | `semantics-direct.rdf` (1127 tests) | `owl-semantics-direct.yaml` | no | not in `latest.json` totals; runs off the dashboard hot path per `generate-report.sh` | **kind (c)** — the heaviest catalog has no recorded score |
| [OWL 2 test types](https://www.w3.org/TR/owl2-test/) | 2 | same | `type-consistency.rdf`, `type-inconsistency.rdf`, `type-positive-entailment.rdf`, `type-negative-entailment.rdf` | 4 yamls | no | inconsistency 126 pass, 1 fail (out of 127); the other three not in `latest.json` totals | **kind (c)** — 3 of 4 wired catalogs have no recorded score |
| OWL 2 RL/RDF rules | 2 | same | `RL-RDF-rules-tests.rdf` | no yaml of its own | no | never run separately | **kind (b)** |

### JSON-LD family

| Spec | Version | Official suite upstream | Vendored here | F\* yaml | Lean harness | Latest score | Gap |
|---|---|---|---|---|---|---|---|
| [JSON-LD toRdf](https://www.w3.org/TR/json-ld11-api/#deserialize-json-ld-to-rdf-algorithm) | 1.1 | [w3c/json-ld-api](https://github.com/w3c/json-ld-api) | submodule `third_party/testing/json-ld` | `jsonld-tordf.yaml` | yes (`JsonLdProbe`) | 467 pass, 0 fail (out of 467) | none |
| JSON-LD expand | 1.1 | same | same | `jsonld-expand.yaml` | `JsonLdApiProbe` | 385 pass, 0 fail (out of 385) | none |
| JSON-LD compact | 1.1 | same | same | `jsonld-compact.yaml` | partial | 245 pass, 0 fail, 1 skip (out of 246) | none |
| JSON-LD flatten | 1.1 | same | same | `jsonld-flatten.yaml` | partial | 58 pass, 0 fail (out of 58) | none |
| JSON-LD fromRdf | 1.1 | same | same | `jsonld-fromrdf.yaml` | partial | 53 pass, 0 fail, 1 skip (out of 54) | none |
| [JSON-LD Framing](https://www.w3.org/TR/json-ld11-framing/) | 1.1 | [w3c/json-ld-framing](https://github.com/w3c/json-ld-framing) | vendored copy `third_party/testing/json-ld-framing` | `jsonld-frame.yaml` | no | not in `latest.json` | **kind (c)** — wired, no recorded score |
| JSON-LD in HTML | 1.1 | w3c/json-ld-api `html-manifest.jsonld` | same submodule | `jsonld-html.yaml` | no | not in `latest.json` | **kind (c)** — wired, no recorded score |

### Tabular data

| Spec | Version | Official suite upstream | Vendored here | F\* yaml | Lean harness | Latest score | Gap |
|---|---|---|---|---|---|---|---|
| [CSV to RDF](https://www.w3.org/TR/csv2rdf/) | CSVW 1.0 | [w3c/csvw](https://github.com/w3c/csvw) (`gh-pages`) | submodule | `csvw.yaml` | `CsvwRdfRun` | 270 pass, 0 fail (out of 270) | Lean side 9 pass, 0 fail (out of 9 attempted; 261 need metadata) |
| [CSV to JSON](https://www.w3.org/TR/csv2json/) | CSVW 1.0 | same | same | `csvw-csv2json.yaml` | `CsvwProbe` | 270 pass, 0 fail (out of 270) | none |
| [Tabular data model / validation](https://www.w3.org/TR/tabular-data-model/) | CSVW 1.0 | same | same | `csvw-validation.yaml` | no | 281 pass, 1 fail (out of 282) | 1 red |
| CSVW non-normative | CSVW 1.0 | same, `manifest-nonnorm.ttl` | same | `csvw-nonnorm.yaml` | no | not in `latest.json`; the yaml records 10 pass, 8 fail (out of 18) | **kind (c)** — wired, no recorded score, 8 known reds |

### Credentials and identifiers

| Spec | Version | Official suite upstream | Vendored here | F\* yaml | Lean harness | Latest score | Gap |
|---|---|---|---|---|---|---|---|
| [VC Data Model](https://www.w3.org/TR/vc-data-model-2.0/) | 2.0 structural | [w3c/vc-data-model-2.0-test-suite](https://github.com/w3c/vc-data-model-2.0-test-suite) | submodule `third_party/testing/vc` | `vc.yaml` | `VcProbe` | 117 pass, 0 fail (out of 117) | none |
| VC Data Model 2.0 issuer/verifier HTTP | 2.0 | same | same | `vc20-api.yaml` | no | 59 pass, 0 fail (out of 59) | none |
| [VC Data Integrity eddsa-rdfc-2022](https://w3c.github.io/vc-di-eddsa-test-suite/) | — | [w3c/vc-di-eddsa-test-suite](https://github.com/w3c/vc-di-eddsa-test-suite) | vendored copy `third_party/testing/vc-di-eddsa` | `vc-di-eddsa.yaml` | no | 31 pass, 0 fail (out of 31) | none |
| [DID Core](https://www.w3.org/TR/did-core/) | 1.0 | [w3c/did-test-suite](https://github.com/w3c/did-test-suite) **is a submodule but its manifest is not used**; the resolver suite is [w3c-ccg/did-key-test-suite](https://github.com/w3c-ccg/did-key-test-suite) | submodule `third_party/testing/did` | `did.yaml`, `manifest: internal` | no | 8 pass, 0 fail (out of 8) | **kind (b)** — a full DID suite sits vendored and unread; 8 internal did:key vectors is the whole claim |
| EECC VC/DID interop fixtures | — | [european-epc-competence-center](https://github.com/european-epc-competence-center) | vendored copy `third_party/testing/eecc` | `eecc-interop.yaml` | no | 4 pass, 0 fail, 51 skip (out of 55) | 51 skips |
| canivc.com community snapshot | — | [digitalbazaar/canivc](https://github.com/digitalbazaar/canivc) aggregated reports | vendored JSON snapshot | no yaml | no | comparison data, not a suite | not a gap |

### XML family

| Spec | Version | Official suite upstream | Vendored here | F\* yaml | Lean harness | Latest score | Gap |
|---|---|---|---|---|---|---|---|
| [XML 1.0](https://www.w3.org/TR/xml/) | 1.0 5e | [W3C/OASIS xmlconf](https://www.w3.org/XML/Test/) | vendored `third_party/testing/xml/xmlconf` | `xml-conformance.yaml` | no | 1447 pass, 0 fail, 1138 skip (out of 2585) | 1138 skips — the largest skip block in the tree |
| [XSLT](https://www.w3.org/TR/xslt-10/) | 1.0 | [apache/xalan-test](https://github.com/apache/xalan-test) (the practical mirror of the OASIS XSLT suite) | submodule `xslt1-xalan/xalan-test-src` + vendored `third_party/testing/xslt` | `xslt.yaml`, `xslt1-xalan.yaml` | no | 87 pass, 0 fail, 1 skip (out of 88) | `xslt1-xalan` has no separate score in `latest.json` |
| [XPath](https://www.w3.org/TR/xpath-10/) | 1.0 | no free W3C XPath 1.0 suite; [w3c/qt3tests](https://github.com/w3c/qt3tests) covers XPath 3.1 | none | `xpath-unit.yaml`, `manifest: internal` | `XPath/Number` | 100 pass, 0 fail (out of 100) | **kind (a)** — 100 self-authored cases; the only external corpus available is qt3tests, which is a different version |
| [XML Schema datatypes](https://www.w3.org/TR/xmlschema11-2/) | 1.1 | [w3c/xsdtests](https://github.com/w3c/xsdtests) | **not vendored** | **no yaml** | no | never run | **kind (a)** — `XSD.Datatypes.fst`, `XSD.Facets.fst`, `XSD.IEEE754.fst`, `Regex.XSDPattern.fst` carry no external conformance evidence at all |
| [MathML](https://www.w3.org/TR/MathML3/) | 3 | [W3C MathML test suite](https://www.w3.org/Math/testsuite/) | vendored self-authored manifest | `mathml.yaml`, `toan-matrix.yaml` | modules only | 81 pass, 0 fail (out of 81); TOAN 11 pass, 0 fail (out of 11) | **kind (a)** — the 81 cases are ours, not W3C's |
| [XForms](https://www.w3.org/TR/xforms/) | 1.1 | [W3C XForms 1.1 test suite](https://www.w3.org/MarkUp/Forms/Test/XForms1.1/) | **not vendored** | `xforms.yaml`, `manifest: internal` | no | 2 pass, 0 fail (out of 2) | **kind (a)** — 2 cases |
| [GRDDL](https://www.w3.org/TR/grddl/) | 1.0 | [W3C GRDDL test suite](https://www.w3.org/2001/sw/grddl-wg/td/) | vendored `third_party/testing/grddl` (normative manifest + docroot) | `grddl.yaml`, `manifest: internal` | no | **18 pass, 50 fail (out of 68)** | worst failing wired suite in the tree; the manifest is vendored but the yaml says `internal` |

### Other

| Spec | Version | Official suite upstream | Vendored here | F\* yaml | Lean harness | Latest score | Gap |
|---|---|---|---|---|---|---|---|
| [JSON Schema](https://json-schema.org/draft-07/schema) | draft-07 | [json-schema-org/JSON-Schema-Test-Suite](https://github.com/json-schema-org/JSON-Schema-Test-Suite) | vendored copy (not a submodule) | `jsonschema.yaml` | modules only | 770 pass, 0 fail (out of 770) | vendored as a snapshot, so it silently ages |
| [GeoSPARQL](https://www.ogc.org/standard/geosparql/) | 1.0/1.1 | [opengeospatial/ogc-geosparql](https://github.com/opengeospatial/ogc-geosparql) + the OGC compliance test suite | **not vendored** | `geosparql.yaml`, `manifest: internal` | modules only | 37 pass, 0 fail (out of 37) | **kind (a)** — 37 self-authored cases |
| [QUDT](https://qudt.org/) | v3.4.0 | QUDT QA test collections | vendored `third_party/qudt` | `qudt.yaml` | no | integrity **0 pass, 0 fail, 29 skip (out of 29)**; user shapes 9 pass, 0 fail (out of 9) | **kind (c)** — the integrity collection measures nothing |
| HDT container | 1.0 (unofficial) | no upstream conformance suite exists; [rdfhdt](https://github.com/rdfhdt) ships fixtures only | vendored 2 `.hdt` fixtures `third_party/testing/hdt` | **no yaml** | no | `hdt_stage4_parity` 6 pass, 0 fail (out of 6) — a parity check, not the fixtures | **kind (b)** — the vendored fixtures drive no suite |
| Apache Parquet footer | 2.x | [apache/parquet-testing](https://github.com/apache/parquet-testing) | **not vendored** | `local-parquet-footer.yaml` (internal) | `Storage/Bytes` | internal only | **kind (a)** — `Parquet.Footer.fst` reads real files with no external corpus |
| WKT | OGC SFA 1.2.1 | folded into the GeoSPARQL suite | — | via `geosparql.yaml` | `Geo/Wkt` | part of the 37 | see GeoSPARQL |
| [SKOS](https://www.w3.org/TR/skos-reference/) | 2009 | no official W3C SKOS test suite exists | — | none | no | never run | not implemented as a module; the `skos-integrity` skill composes SHACL + SPARQL. Not proposed as a suite |
| EARL reporting | 1.0 | [W3C EARL 1.0 Schema](https://www.w3.org/TR/EARL10-Schema/) | — | none | no | never run | not implemented; no runner emits EARL. Would make every score above publishable in the W3C's own format |

**Row count: 62.**

## 3. Gaps by kind

### Kind (a) — implemented, an external suite exists upstream, not vendered here

Six. Each is a spec where the engine's only evidence is cases this
project wrote itself.

| # | Spec | Upstream | Licence | Size | Runner that would consume it |
|---|---|---|---|---|---|
| a1 | XML Schema datatypes 1.1 | [w3c/xsdtests](https://github.com/w3c/xsdtests) | W3C Test Suite Licence | ~35,000 cases across the suite; the datatype subset is the target | new `xsd_runner`, or a mode of `xml_runner` |
| a2 | GeoSPARQL | [opengeospatial/ogc-geosparql](https://github.com/opengeospatial/ogc-geosparql) | Apache-2.0 (the OGC repo); the compliance suite is OGC-licensed | ~100 abstract tests | `w3c_runner` in a `--geosparql` mode, or the existing `tests/unit` path promoted |
| a3 | MathML 3 | [W3C MathML test suite](https://www.w3.org/Math/testsuite/) | W3C Test Suite Licence | ~4,000 files, mostly presentation | `mathml_runner` (exists) |
| a4 | XForms 1.1 | [W3C XForms 1.1 test suite](https://www.w3.org/MarkUp/Forms/Test/XForms1.1/) | W3C Test Suite Licence | ~200 cases | node runner (exists, 2 cases) |
| a5 | Apache Parquet | [apache/parquet-testing](https://github.com/apache/parquet-testing) | Apache-2.0 | ~80 `.parquet` files + bad-data corpus | `parquet_footer` local runner (exists) |
| a6 | ISO Schematron | [Schematron/schematron](https://github.com/Schematron/schematron) | MIT (the skeleton) | ~40 reference cases | `schematron_runner` (exists) |

XPath 1.0 is deliberately not on this list: no free upstream XPath 1.0
suite exists, and `w3c/qt3tests` targets XPath 3.1. Recording it as a
gap would be dishonest about what is available.

### Kind (b) — vendored here, wired into no harness

Six.

| # | Suite | Path | Size | Why it matters |
|---|---|---|---|---|
| b1 | RML containers (rml-cc) | `third_party/testing/rml-modules/rml-cc` | 47 test-case dirs | submodule already pinned; `rml_runner` already walks this exact layout |
| b2 | RML functions (rml-fnml) | `third_party/testing/rml-modules/rml-fnml` | 32 test-case dirs | same |
| b3 | RML-star | `third_party/testing/rml-modules/rml-star` | 30 test-case dirs | same; also the RDF-star bridge |
| b4 | W3C DID test suite | `third_party/testing/did` (submodule) | full W3C suite, `docs/` + per-method dirs | the current DID claim is 8 internal vectors |
| b5 | OWL 2 RL/RDF rules catalog | `third_party/testing/owl/RL-RDF-rules-tests.rdf` | one RDF catalog | `owl_runner` already reads sibling catalogs |
| b6 | HDT fixtures | `third_party/testing/hdt` | 2 byte-real `.hdt` files with published SHA-256 and expected stats | `HDT.Container/Dictionary/Triples` have no suite of their own |

### Kind (c) — wired but scoring zero, never run, or stale

Twelve.

| # | Suite | Symptom |
|---|---|---|
| c1 | RDF 1.2 syntaxes | no yaml; runs only under `generate-report.sh --rdf12`. 242 pass, 0 fail (out of 242) |
| c2 | RDF 1.2 canonicalization | no yaml. 82 pass, 0 fail (out of 82) |
| c3 | RDF 1.2 Semantics | no yaml; **3 fail, 3 skip** of 47; the manifest reports `undefined prefix: test (byte offset 9734)` and the harness continues on the well-formed subset. The Lean harness cannot load it at all (`no_manifest=1`) |
| c4 | SPARQL 1.2 | no yaml. 254 pass, 0 fail (out of 254) |
| c5 | ShEx negative syntax | `present: false`, 0 pass, 0 fail (out of 0) in the 2026-08-22 report, while the yaml records 100 pass, 0 fail (out of 100) from 2026-07-10 |
| c6 | QUDT integrity | 0 pass, 0 fail, 29 skip (out of 29) — measures nothing |
| c7 | GRDDL | 18 pass, 50 fail (out of 68) — the worst wired score in the tree |
| c8 | CSVW non-normative | no score in `latest.json`; yaml records 10 pass, 8 fail (out of 18) |
| c9 | JSON-LD framing | wired, no score in `latest.json` |
| c10 | JSON-LD in HTML | wired, no score in `latest.json` |
| c11 | OWL 2 semantics-direct + 3 of the 4 type-\* catalogs | wired, no score in `latest.json` (off the dashboard hot path) |
| c12 | The entire Lean harness | `lake exe l4w3c` + 15 probes, zero yaml, zero rows in `latest.json` |

Also recorded, not counted as a spec gap: `tests_unit` scores 19 pass,
28 fail (out of 47) and `npm_package` 167 pass, 2 fail, 1 skip (out of
170). Both are internal, both are red.

## 4. The rdf12 rdf-semantics manifest typo, confirmed

`third_party/testing/w3c/rdf/rdf12/rdf-semantics/manifest.ttl` uses a
`test:` prefix it never declares. Verbatim from
`formal/fstar/ocaml-output/rdf12entail_results.log` line 1:

```
Manifest parse warning in third_party/testing/w3c/rdf/rdf12/rdf-semantics/manifest.ttl: undefined prefix: test (byte offset 9734) -- continuing with the well-formed subset
```

The F\* runner degrades to the well-formed subset and still scores 47
entries. The Lean runner does not degrade and reports 0 out of 0. Two
harnesses, two different answers to the same broken input — that
divergence is worth an upstream issue to w3c/rdf-tests and a decision
about which behaviour is correct.

## 5. Recommended order of work

**Cheapest-first is chosen**, for one reason: every kind (b) item is
already on disk with a runner that already parses that layout, so the
cost is a yaml file and a run — and each one converts an unknown into
a number tonight. Highest-value-first would start with a1 (XML Schema
datatypes), which is a multi-session build with no partial credit.

1. **c1, c2, c4 — write yamls for rdf12, rdf12c14n, sparql12.** The
   suites pass 578 tests between them and a diff that breaks them
   selects nothing. Pure bookkeeping, minutes of work, removes a real
   blind spot in `affected-tests.sh`.
2. **b1, b2, b3 — wire rml-cc, rml-fnml, rml-star.** 109 vendored test
   cases, `rml_runner` already walks the identical `test-cases/`
   layout used by `rml-core` and `rml-io`. One yaml each.
3. **c5, c8, c9, c10, c11 — make the silent suites report.** Five
   suites have runners and manifests but no row in `latest.json`. Find
   out whether they are skipped by `generate-report.sh` or failing
   silently. This is the difference between "we score X" and "we
   believe we score X."
4. **c7 — GRDDL, 18 pass, 50 fail (out of 68).** The largest single
   block of red in a wired suite. Also the one place where the public
   dashboard carries a bad number.
5. **b6, b5, b4 — HDT fixtures, the OWL RL/RDF rules catalog, the W3C
   DID suite.** Vendored, unread, each needs runner work rather than
   just a yaml.
6. **c12 — one manifest format for both harnesses.** The Lean tree has
   a working conformance runner whose numbers live only in prose. Give
   the yamls a `harness:` field and let `dispatch_test_suites.sh`
   dispatch `lake exe l4w3c` alongside the F\* runners.
7. **c6 — QUDT integrity, 0 of 29 measured.**
8. **a6, a5, a4 — Schematron, Parquet, XForms.** Small upstream
   corpora, runners already exist, each replaces self-authored cases
   with external ones.
9. **a3, a2 — MathML and GeoSPARQL.** Larger corpora, real porting.
10. **a1 — XML Schema datatypes.** The biggest and the most valuable:
    four F\* modules currently carry no external evidence. Deliberately
    last under cheapest-first; it would be first under
    highest-value-first.

## 6. Issue index

One issue per kind (a) and kind (b) gap, filed 2026-08-23.

<!-- ISSUE-INDEX -->
