# W3C/SemWeb Completeness Ledger

**Standing goal (owner, 2026-07-09):** Exemplary and full implementation
of every OFFICIAL W3C RDF/semweb-related specification we touch —
**RDF 1.2 / RDF-star parked** for now. Anything short of full is listed
here as a **failure**, not softened as a skip. Focus: in-depth coverage
and performance, not protocols. Every capability gets an npm API and
Hub documentation.

**Why 100% first:** complete real test coverage is the FOUNDATION FOR
AUTOMATED PERF RESEARCH (owner, same date). A perf harness over a
partially-conformant engine measures the wrong thing; the coverage
ledger below is the prerequisite checklist for the per-engine perf
program.

Update discipline: numbers here are labelled and dated at last edit;
the live dashboard supersedes them the moment they diverge. Rows sorted
alphabetically. "npm/Hub" = typed API + hub page exist.

| Spec | Measured (2026-07-09) | FAILURES to burn down | npm / Hub |
|---|---|---|---|
| **CSVW** (csv2rdf) | 235 pass, 35 fail (out of 270) [2026-07-15, two burndown rounds: stage-2 inherited + group common properties, metadata-shape degradation, discovery/query-string; ledger `2026-07-15-csvw-csv2rdf-fail-triage.md`; was 218/52] | UAX-35 date/time + number `format` engines landed 2026-07-10 (F\* `CSVW.Formats`: date/time patterns, number patterns incl. groupChar/decimalChar/percent/per-mille/exponent, `Y\|N` booleans, duration lexical checks; plus `separator`/list values and the `-`→`%2D` default-propertyUrl encoding). Remaining 52, enumerated: **metadata discovery, PARKED protocol** — test011/012/014/016, test116/118/121/122/123, test259/260 (Link header, directory metadata, `/.well-known/csvm` — in scope per owner clarification 2026-07-15, round 3); **metadata normalization warnings** — test047/048/049, test097/100/101/102/107, test263/273/275/276/277 (invalid-property pruning, `@base`/`@type` context edge cases, wrong-level properties); **schema compatibility + validation** — test023, test125/126/127, test130/131, test148/149, test150/151, test238, test278 (header=false, required/null, column-name restrictions, title-language intersection, non-builtin datatype names); **complex fixtures** — test032/033/034/035/036/037/038/039 (virtual columns, multi-subject, referenced schemas, inherited-property combinatorics); **rowTitles** — test235/236; **table-level `separator` + ordered lists** — test305/306/307; **duration regex `format`** — test194 (needs regex engine); **2 cross-table NegativeRdf** — test252/253 (foreign-key validation) | ✓ / ✓ (post 13) |
| **DID** (did:key) | 8/8 on stage-1 vectors | depth: suite is a sliver of DID Core (no did:web, no resolution metadata) — needs a real conformance target enumerated | ✓ / ✓ (post 23) |
| **GRDDL** | Stage 2 (local docroot): 15 pass, 53 fail, 0 skip (out of 68) [2026-07-16], was 9/8/51 | Stage 2 (issue #301) landed: namespace-document (§3) and profile-document (§5) transformation discovery now live in F* (`GRDDL.Discovery`: `head_custom_profile_uris` / `profile_doc_transformations` / `root_namespace_uri` / `namespace_doc_transformations`, plus `<base href>`-aware `doc_base`) as pure Tot tree-walks; the runner FETCHES the referenced second documents from the vendored docroot (rule #11 — I/O only, no live network). Every manifest test is now RUN, so all 51 former skips are converted to honest pass/fail. +6 passes over Stage 1: htmlbase3, inline-rdf1/2/3, multipleRepresentations, xmlbase3 (all previously blanket-skipped as `NetworkedTest`). Fail buckets: **30 `fail-graph-mismatch`** (consumed XSLT-engine fidelity gaps, HTTP content-negotiation, recursion/merge, XInclude posture), **6 `fail-known-gap-xslt-feature`** (inline-rdf4/5/6/8/9/10 xml:base/xml:lang in embeddedRDF.xsl), **10 `fail-no-transformation-discovered`** (namespace/profile second-document not vendored: two-transforms, three/four-transforms, ns-*, sq1/sq2, glean/hcarda/card5na/grddlProfileBase3), **7 `fail-transform-not-vendored`** (a discovered stylesheet — .sxsl or a redirect-base path — is not present offline). Residue = recursion + loop-detection (loop/loopx/ns-* chains), HTTP redirect-base and content-negotiation simulation, HTML tag-soup input (Stage 3), and complex real-world transforms (hcard2rdf, grokSheet, glean-profile) that exercise consumed-engine XSLT gaps. Engine bugs are reported, not fixed here. | ✗ / ✗ |
| **JSON-LD 1.1** | toRdf 461 pass, 0 fail, 6 skip (of 467); fromRdf 53 pass, 0 fail, 1 skip (of 54); expand 379 pass, 0 fail, 6 skip (of 385); compact 244 pass, 0 fail, 2 skip (of 246); flatten 56 pass, 0 fail, 2 skip (of 58) [2026-07-10] | **frame / html API suites NOT RUN — counted as failed until measured**. flatten is now MEASURED: `bin/jsonld-flatten-runner` drives `JSONLD.Flatten.fst` (Node Map Generation § 6.2 with the Generate-Blank-Node-Identifier issuer relabelling to `_:b0`/`_:b1`/… in spec issue order, the Flattening Algorithm § 6.1's named-graph folding + code-point node ordering + @id-only dropping, and — for context-bearing entries — compaction of the flattened array through the landed `JSONLD.Compact` machinery with a pinned top-level `@graph`), comparing via the same `Parser.JSONLD.jsonld_expanded_equal` JCS-canonical structural equality as expand/compact; the one NegativeEvaluationTest (conflicting indexes) passes as `flatten_document = None`. No changes to Expand/Context/Compact were needed — toRdf/fromRdf/expand/compact floors re-measured, held. The 17 skips across the five suites are enumerated JSON-LD-1.0-version fixtures (documented per-ID in the runners; flatten's 2: t0014, t0038 — both the 1.0 every-term-is-a-prefix expansion rule; run under JLD_NO_SKIP=1 to re-measure) | partial / ✓ (post 07) |
| **OWL 2** | RL-PE 28 pass, 2 fail (out of 30) [re-measured 2026-07-16]; profile-QL 83 pass, 4 fail (out of 87) + profile-EL 108 pass, 13 fail (out of 121) [aggregate PE+NE+Cons+Inc under RL closure, re-measured 2026-07-16]; syntax-dl species 319 pass, 2 fail (out of 321 scored), 2 skipped (functional-syntax-only) — 323-case catalog [re-measured 2026-07-16; skip count fell from 19 to 2 as the functional-syntax premise parser widened]; DL-regime type-inconsistency 114 pass, 14 fail (out of 128 scored), zero oracle-assisted [2026-07-15: verified Farkas-certificate class-size reasoner decides dl-910 + one=two; earlier 2026-07-14, five tableau waves: datatype facet satisfiability, role box (subPropertyOf/FunctionalProperty/transitive), contrapositive unfolding + exact-cardinality-0 NNF, SHIQ ≤-rule witness merging, named-individual identification + stored FP max-1 bounds — up from 70 pass, 58 fail (out of 128), zero regressions]; type-consistency 352 pass, 0 fail (out of 352) [2026-07-15: empty-premise harness fix +16, XMLLiteral c14n equality retiring WebOnt-202, RDFXML XMLLiteral opaque capture; soundness gate now ZERO unexpected-inconsistency] | Tableau REFUTATION landed 2026-07-10 (`Tableau.Refute.fst`: clash-detecting `tableau_consistent` — NNF, lazy TBox unfolding, disjunction branching under a threaded linear budget, depth-capped ∃-witnesses, complement/min-max/counting/bottom-property clash rules, AllDifferent + self-disjoint-property + rdf:nil graph checks; wired into `owl_runner --regime dl` inconsistency AND consistency scoring with the SIGALRM fallback so DL never scores below RL); five 2026-07-14 waves extended the tableau with datatype facets, role-box reasoning, contrapositive unfolding, SHIQ ≤-rule witness merging, and named-individual identification (soundness gate through the 07-14 waves: exactly one unexpected-inconsistency, WebOnt-miscellaneous-202 — RETIRED 2026-07-15 by XMLLiteral c14n equality; gate is now zero); the 2 syntax-dl species residuals re-triaged 2026-07-16 (checker is F\* `OWL2.SyntaxDL.fst`; species covers premise AND conclusion docs), both structurally blocked / fixture-disputed, no sound zero-regression flip exists: **(1) FS2RDF-literals-ar** — NOT a parser rejection (the RDF/XML premise parses fine); its `test:rdfXmlPremiseOntology` is a defective serialization whose datatype IRIs are lowercased case-variants of the OWL 2 datatype map (`xsd:datetime`/`xsd:unsignedint`/`xsd:negativeinteger`/`xsd:anyuri`/… vs the map's `xsd:dateTime`/`xsd:unsignedInt`/…). Those IRIs are not in `builtin_datatypes`, so `species_violations` reports them `reserved-vocabulary-as-datatype` → FULL. The corpus's DL label reflects the correct-cased `fsPremiseOntology`; the runner prefers the RDF/XML premise, so we score the defective graph. Fixture serialization defect, not a checker gap. **(2) WebOnt-I5.5-005** — the classified graph is premise (`owl:Class a`, header-less) ∪ its comprehension conclusion (a bare header-less `owl:unionOf` class expression not used in any axiom — the description literally calls it "the effect of the comprehension principles in OWL Full"), giving violation `conclusion: no-ontology-header` → FULL. Its sibling **I5.5-006** (in all.rdf, NOT in syntax-dl.rdf; second doc is a cyclic-list `rdfXmlNonConclusionOntology`, not fed as a conclusion) is classified on the identical header-less `owl:Class a` premise ALONE and is expected FULL — which it correctly is. Since 005's fed graph strictly CONTAINS 006's, and the extra triples are precisely the OWL-Full comprehension construct, no monotone graph classifier can call 005 DL while keeping 006 FULL. Structurally blocked; leaving 005 FULL keeps 006 correct. (This corrects the earlier ledger wording "graph-identical I5.5-006 sibling" — the graphs differ, but the shared header-less premise plus the subset relation is what makes the pair inseparable.) Species control over all.rdf incl. the 166 FULL-only negatives absent from syntax-dl.rdf: 482 pass, 5 fail (out of 487 scored), 2 skipped [re-measured 2026-07-16] — 163/166 FULL-only cases correctly rejected; the 5 fails = FS2RDF-literals-ar + I5.5-005 (above) + imports-004/012/014 (verdict=DL expected=FULL): each imports a doc that is FULL only because it types an entity with the legacy `rdfs:Class`/`rdf:Property`/`rdf:List` vocabulary, which `type_object_whitelist` deliberately admits as DL for the many species-DL corpus cases that use the same legacy typings — the same no-separating-graph-function bind, and an import-resolution edge (the imported doc IS loaded via `resolve_species_imports`; the whitelist, not the loader, is why the union scores DL). #262 sameAs perf blowup | closure ✓, tableau ✓ / page queued (#93) |
| **QUDT** (v3.4.0) | NEW ROW [measured 2026-07-10]: user-shapes fixtures 9 pass, 0 fail (out of 9); integrity ruleset 0 pass, 0 fail, 29 skip (out of 29 shapes: 26 wall-clock-budget skips, 2 sh:SPARQLTarget #181, 1 sh:deactivated) | QUDT (qudt.org) is an independent ontology suite, not W3C, and publishes **no official conformance suite** — the measured targets are the ones defined in `docs/designissues/2026-07-10-qudt-scoping.md` (Layer A landed: vendored v3.4.0 distribution + rulesets in `third_party/qudt/`, runner `bin/qudt-runner`, suite `qudt.yaml`). Burn-down: (1) the integrity budget-skips are a PERF failure, not a correctness one — per-focus-node sh:sparql evaluation over the 131k-triple all-in-one exceeds the 10-minute cap for every ruleset shape (fixed cost is only 20s; see performance.md § QUDT corpus); indexed/pre-compiled SPARQL-constraint evaluation is the unlock. (2) Layer B: exact-rational unit conversion + dimension-vector algebra in F\* (provable round-trip identity relative to the pinned v3.4.0 multipliers) with qudt-convert/qudt-dimension derived suites. (3) Layer C: qudtf: SPARQL extension functions. (4) sh:SPARQLTarget (#181). | ✗ / ✗ |
| **RDF 1.1** | 1031/0 (strict) | runner-integrity fix landed: graph equality is now RDFC-1.0 canonicalization + byte-compare (F* `RDF.GraphIsomorphism`, not lenient bnode-collapse), with lang-tag-case value equivalence; score held at 1031/0 under the strict comparison (our parsers produce graphs bnode-isomorphic to the expected N-Triples/N-Quads), 0 canonicalization-budget fallbacks — so 1031 is now earned, not inflated. Remaining: RDF/XML deep-nesting overflow (#279) | ✓ / ✓ |
| **RDFC-1.0** | 86/0 — complete | none on conformance; needs a perf row (HNDQ budget behavior) | ✓ / ✓ (post 08) |
| **RIF Core** | 34 pass, 4 fail, 12 skip | the 4 + the 12, each with a named reason or a fix | ✓ / ✓ (post 10) |
| **SHACL** | core 98 pass, 0 fail (out of 98); sparql-constraints 22 pass, 0 fail (out of 22) [2026-07-10, denominators audited] | audited both denominators against the vendored `third_party/testing/shacl/data-shapes-test-suite` manifest tree: walking `mf:include` from the suite's own top-level `tests/manifest.ttl` (→ `core/manifest.ttl` + `sparql/manifest.ttl`, and every nested section — complex/misc/node/path/property/targets/validation-reports under core; component/node/property/pre-binding under sparql) yields exactly 120 `sht:Validate` entries, matching 98+22 to the test. Both denominators are the FULL suite — no unrun section exists. The one test outside the 120, `sparql/component/nodeValidator-001.ttl`, is the suite's only entry carrying `mf:status sht:proposed` (every other of the 120 is `sht:approved`) and is correctly omitted from `sparql/component/manifest.ttl` by the WG itself — not our gap (it passes when run directly and off-ledger; not counted since it is not part of the approved suite). SHACL 1.2 (`shacl12-test-suite`, node-expr/rules/sparql-targets sections) is a separate not-yet-Recommendation Public Working Draft built on RDF/SPARQL 1.2 (`third_party/testing/shacl/README.md`) — future scope, not this row. SHACL Compact Syntax (`shacl-compact-syntax/`) is a Community Draft with no `mf:Manifest` conformance suite (paired `.shaclc`/`.ttl` fixtures only, no include tree) — a different concrete-syntax parsing concern, not this row's mandate. No runner or F* change required. | ✓ / ✓ (post 05) |
| **ShEx** (CG) | validation 1181 pass, 1 fail (out of 1182; the 1 = the upstream start2RefS2.json p1/p2 fixture defect); negativeSyntax 100 pass, 0 fail (out of 100); ShExC↔ShExJ differential 433 of 433 [2026-07-10] | negativeSyntax first scored 2026-07-10 (`shex_runner --negative-syntax`): initial 85 pass, 15 fail — all 15 were Parser.ShExC permissiveness bugs (bare-`a` outside predicate position, duplicate xsFacets, litNodeConstraint+shapeRef juxtaposition, numeric facet on non-numeric datatype, bnodes in value sets / predicate position, REGEXP escape whitelist, LANGTAG validation, empty language-tag exclusions), fixed in F\* the same landing with the 433/433 differential as the over-tightening guard. Dashboard rows `shex` + `shex_negative_syntax` both emitted. Remaining unscored: `negativeStructure/` (14 fixtures) and `schemas/` RepresentationTest ShExC↔ShExJ round-trips (441; the ShExC→AST direction is what the differential covers). Advisory tree-sitter-shexc three-way probe: `tests/shexc-treesitter/run.sh`; grammar audit: `docs/designissues/2026-07-10-shexc-treesitter-grammar-audit.md` | ✓ / ✓ (post 06) |
| **SPARQL 1.1** | 631/0; regimes 70/70 | ALL 8 strict-runner failures now fixed in F*. Tasks #100 (7 of 8): **BNODE()/BNODE(str)** now per-solution + per-occurrence fresh (row+call-site seed via sha256, pure F*); **UUID()/STRUUID()** distinct per binding (same seed); **NOW()** returns a valid xsd:dateTime (boundary `fx_current_datetime` assume val, #287); the OWL cardinality/someValuesFrom rewrite's internal `?_sv_`/`?_mc_`/`?_mxqc1_` vars are stripped at the FINAL projection only (parent min-1, parent max-1 Female), keeping inner Select_All sub-select correlation intact; **RDF inference test (rdf01)** fixed via rdfD2 (predicate ⇒ rdf:Property) applied only under the ent:RDF regime. Task #101 (last one): **RIF Brain Anatomy (rif04)** — the RIF Import(<import001.rdf> OWL-Direct) directive's declared entailment profile is now materialised. `Parser.RIFXML.parse_rif_program_with_import_profiles` surfaces each import's (location, profile) pair; `RIF.Core.Tests.materialise_import_graph` dispatches the profile IRI to the closure the SPARQL regimes already ship (Simple→plain, RDF/RDFS→`rdfs_closure_with_reflexivity`, OWL-Direct/OWL-RDF-Based→`owl_rl_closure_with_reflexivity`) before the imported triples merge into the premise, so `g1/pcg0 rdf:type MaterialAnatomicalEntity` (from `Gyrus rdfs:subClassOf MaterialAnatomicalEntity`) exists when the RIF rule body matches. 0 canonicalization-budget fallbacks. Also: parser `--admit_smt_queries` regions removed 2026-07-10 (#91) — SPARQL11.Parser.fst verifies with zero admits; Protocol 34/0 + GSP 19/0 pass via in-process dispatch through the verified SPARQL_Protocol/SPARQL_GraphStore modules; factoidal-http serves query/update on the wire (GSP writes behind --rw + delta log); wire-level suite replay harness not yet automated | ✓ / ✓ |
| **VC 2.0 + Data Integrity** | structural Stage 1: 117 pass, 0 fail (out of 117 scorable; 3 fixtures withdrawn upstream of 120 vendored) [2026-07-10]; crypto roundtrip 8 pass, 0 fail; official W3C vc-di-eddsa-test-suite eddsa-rdfc-2022 create+verify (via `bin/vc-api-shim`, task #88): 31 pass, 0 fail (out of 31) [2026-07-14, suite fully green — proof sets/chains + previousProof landed, was 26 pass, 5 fail]; official vc-data-model-2.0-test-suite issuer/verifier HTTP tests (same shim): 59 pass, 0 fail (out of 59) [2026-07-14, suite fully green — relatedResource structural/digest checks (VCDM 2.0 s5.3) + JSON-LD named-graph/@container:@graph VP expansion fix, was 22 pass, 37 fail] | eddsa-rdfc-2022 measured against the official corpus, including multi-proof sets and `previousProof` chains; eddsa-jcs-2022 not implemented (different JCS transform path); context-driven type redefinition; browser/JS bundle not yet measured against the official corpus | ✓ (typed crypto) / ✓ (post 13) |

Parked by owner directive: **RDF 1.2 / RDF-star** (also blocks rml-star
— revisit as one design decision). (The former "Protocols parked" note
is obsolete: Protocol 34/0 and Graph Store 19/0 pass in-process, and
factoidal-http serves them — see the SPARQL row.)

Non-semweb engines (XML, XSLT, XPath, Schematron, JSON Schema, MathML,
XForms, TOAN) stay measured on the dashboard but are outside this
ledger's "full implementation" mandate.

## Dispositions table (2026-07-16 day-closure /goal)

Owner day-closure goal (2026-07-16): every W3C + ShEx suite either
fully green or every residual fail/skip named with a one-line written
disposition. Vocabulary (fixed): **disputed-fixture** (the vendored
corpus fixture itself is wrong/contested upstream) ·
**dependency-blocked(what)** (blocked on a named engine/component not
yet built) · **planned-family(issue/doc)** (a named family with a plan
and a tracker) · **environment(what)** (a checkout/toolchain gap, not
an engine defect) · **by-design(why)** (deliberately out of scope, the
processor's behavior is correct).

Scores below are cross-checked against `git merge-base --is-ancestor`
on this worktree's HEAD (`1e152504`) — a score is reported as "landed"
only when its source commit is a verified ancestor. Suites with zero
fails and zero skips (SPARQL 1.1, RDF 1.1 six-suite, RDFC-1.0, SHACL,
type-consistency 352/0, DID, geosparql, mathml, schematron, xforms,
toan_matrix, vc20_api, vc_di_eddsa, vc_stage1, hdt_stage4_parity,
xpath_unit, rml_core, shex_negative_syntax) are omitted — nothing to
disposition.

| Suite | Score (labelled) | Status |
|---|---|---|
| CSVW csv2rdf | 264 pass, 6 fail (out of 270) [round 4, `c91fd4c7`, ancestor-confirmed] | 🟡 dashboard/ledger headline stale at 235/35 |
| eecc_interop | 4 pass, 0 fail, 51 skip (out of 55) | ✅ fully dispositioned |
| GRDDL stage 1 | 15 pass, 53 fail, 0 skip (out of 68) | ✅ fully dispositioned; stage 3 parked |
| hub_browser_bundle | 234 pass, 1 fail (out of 235) | ✅ fully dispositioned |
| JSON-LD 1.1 (5 sub-suites) | 1193 pass, 0 fail, 17 skip combined (of 1210) | ✅ per existing ledger row |
| JSON Schema draft-07 | 712 pass, 0 fail, 58 skip (out of 770) | ✅ fully dispositioned |
| npm_package | 160 pass, 2 fail, 1 skip (out of 163) | 🔴 2 fails undocumented, no tracking issue |
| OWL 2 DL type-inconsistency (tinc) | 118 pass, 10 fail (out of 128), zero oracle-assisted [`ed8c4a03`, ancestor-confirmed] | ✅ per #299; ⚠️ committed log stale (see note) |
| OWL 2 DL positive entailment (PE) | 135 pass, 69 fail, 2 skip (out of 204) [`81cf6906`, ancestor-confirmed] | 🟡 per #298, families not individually named |
| OWL 2 DL negative entailment (NE) | 22 pass, 1 fail (out of 23) | ✅ fully dispositioned |
| OWL 2 RL positive entailment | 28 pass, 2 fail (out of 30) | ✅ fully dispositioned |
| OWL 2 DL syntax-dl species | 319 pass, 2 fail, 2 skip (out of 323) | ✅ fully dispositioned; ⚠️ ledger headline stale (302/2/19) |
| OWL 2 profile EL | 108 pass, 13 fail (out of 121) | 🧭 untriaged — no owner disposition on file |
| OWL 2 profile QL | 83 pass, 4 fail (out of 87) | 🧭 untriaged — no owner disposition on file |
| QUDT integrity | 0 pass, 0 fail, 29 skip (out of 29) | ✅ fully dispositioned (all-skip is a perf finding, not a dead suite) |
| RIF Core | 46 pass, 1 fail, 3 skip (out of 50) | ✅ fully dispositioned |
| rml_io | 17 pass, 1 fail, 55 skip (out of 73) | ✅ fully dispositioned |
| ShEx validation | 1181 pass, 1 fail (out of 1182) | ✅ per `tests/shex-shexj-twins/README.md` |
| tests_unit | dashboard: 35 pass, 6 fail (out of 41) — stale; this session's fresh run: 45 pass, 0 fail (out of 45) | ✅ dispositioned as environment; dashboard needs republish |
| xml_conformance | 1414 pass, 0 fail, 1171 skip (out of 2585) | ✅ fully dispositioned (runner's own "HONEST BREAKDOWN") |
| XSLT 1.0 | 79 pass, 9 fail (out of 88) [`fd5fc372`, ancestor-confirmed] | 🟡 namespace-node family in flight (`xslt-namespace-nodes`) |

### CSVW csv2rdf — 264 pass, 6 fail (out of 270)

Linked: `docs/designissues/2026-07-15-csvw-csv2rdf-fail-triage.md` +
#297. The ledger's own headline (row above, "235 pass, 35 fail") is
stale — round 3 (`6ee10225`) and round 4 (`c91fd4c7`) are both
ancestors of this worktree's HEAD and bring the real current score to
264/6. Named residuals, from the triage doc's round-4 remaining-detail
section:

- test036, test037, test102 — **planned-family** (#297 family C: `@id`
  real-IRI table/group-node identity, not yet a CSVW.Conversion
  signature change; test036/037 additionally need annotation-object
  common properties).
- test148, test149 — **planned-family** (#297 family A residue:
  title-LANGUAGE-aware column-name derivation, a decode-shape change
  to `csvw_decode_titles`).
- test194 — **dependency-blocked**(regex engine phase 3, #304) — the
  `datatype.format` duration-pattern facet needs a regex match; #304
  phase 2 (Brzozowski-derivative Exec + XSD pattern parser) has landed
  (`e2e2dbb9`, ancestor-confirmed) but the CSVW/OWL consumer swap
  (phase 3) has not.

### eecc_interop — 4 pass, 0 fail, 51 skip (out of 55)

Vendoring commits (`third_party/testing/eecc/PROVENANCE.md`):
`vc-verifier-rules` at `b165d68393485c0fd3c5285eaa32fa9c3602a264`
(2026-06-22), `webuild-attestations` at
`1f1096b06b40b19c3711d635a2e9bada8f8584ef` (2026-07-06), both
Apache-2.0, both retrieved 2026-07-13.

- 4 skips (crypto-verify on the 4 real DataIntegrityProof credentials)
  — **dependency-blocked**(live HTTPS `did:web` resolution; this
  runner is offline/network-free and no fixture bundles the Ed25519
  public key material).
- 47 skips (40 webuild-attestations files + 6 vc-verifier-rules JSON
  Schemas + 1 JWT-VC example) — **by-design**(not W3C VCDM JSON-LD
  credentials — SD-JWT/mdoc/JWT-VC serializations Factoidal has no
  parser for; vendored as reference data only, per the suite's own
  yaml comment).

### GRDDL stage 1 — 15 pass, 53 fail, 0 skip (out of 68)

Linked: #301 + the stage-2 census already in this ledger's GRDDL row
(landed `7d1c36e4`/`5c54fd21`, ancestor-confirmed). Four named
fail-buckets, all **planned-family**(#301, stage 3 — parked as
prioritization not prohibition per owner comment 2026-07-16 on #301:
*"Do what you outlined but not grddl - more polish/optimize our xpath,
xslt ... first"*):

- 30 `fail-graph-mismatch` — consumed XSLT-engine fidelity gaps
  (side-effect improvement expected from the now-prioritized XSLT
  burndown — the #301 comment itself notes "~30 of the 53 fails are
  XSLT-engine fidelity items").
- 6 `fail-known-gap-xslt-feature` — inline-rdf4/5/6/8/9/10, `xml:base`/
  `xml:lang` handling in `embeddedRDF.xsl`.
- 10 `fail-no-transformation-discovered` — namespace/profile
  second-document not vendored offline (two-transforms, three/
  four-transforms, ns-\*, sq1/sq2, glean/hcarda/card5na/
  grddlProfileBase3).
- 7 `fail-transform-not-vendored` — a discovered stylesheet (`.sxsl` or
  a redirect-base path) not present offline.

### hub_browser_bundle — 234 pass, 1 fail (out of 235)

- post18 "the C demo transcript quoted in this post is real" —
  **environment**(the compiled KaRaMeL C binary
  `formal/fstar/c-output/deltalog/demo/delta_log_demo` is listed in
  `formal/fstar/.gitignore:23` and is not built in this checkout — the
  `.c` sources are present, the compile step was never run here).
  Verified: the assertion failure is literally "expected the compiled
  C delta-log demo binary to exist", not a content mismatch.

### JSON-LD 1.1 — 1193 pass, 0 fail, 17 skip combined (of 1210)

toRdf 461/0/6, fromRdf 53/0/1, expand 379/0/6, compact 244/0/2, flatten
56/0/2 — all **by-design**(JSON-LD-1.0-version fixtures, named per-ID
in each runner; frame/html API suites are NOT RUN, already flagged in
the existing ledger row as counting as failed until measured, not a
skip). Note: this session found no unmerged branch touching JSON-LD
skips despite the task brief's "concurrent agents ... jsonld skips"
warning — treated as current, not in flight, but re-verify before
citing if a jsonld-\* branch lands after this commit.

### JSON Schema draft-07 — 712 pass, 0 fail, 58 skip (out of 770)

All 58 — **by-design**(keywords outside the validator's slice-1 scope:
pattern-regex matching, the `format` vocabulary, and remote/anchor
`$ref` resolution — `bin/jsonschema-runner`'s own header comment).
Per-file: `ref.json` 38 (remote/anchor `$ref`), `additionalProperties.json`
8 + `properties.json` 8 (pattern-keyed properties), `definitions.json`
2 + `propertyNames.json` 2 (anchor `$ref` / pattern).

### npm_package — 160 pass, 2 fail, 1 skip (out of 163)

🔴 The 2 fails are **not** covered by any linked design doc or GitHub
issue found in this pass — flagged, not confidently dispositioned:

- Test 44 `openCottas + queryCottas (raw ABI): COUNT/ASK/SELECT match
  the fixture's known content` — fails at
  `cottas-bytes-store.test.js:94` (`ask.boolean` expected `true`, got
  `false`).
- Test 50 `index.js openCottas/queryCottas: SELECT/ASK/COUNT match the
  heap-store answers for the same data` — same file, line 173.

Both are in `npm/factoidal/test/cottas-bytes-store.test.js`, which
compares the binary `.cottas` fixture
(`tests/unit/fixtures/store_capabilities_sample.cottas`) against the
same data parsed live from `tests/local/data/cottas_sample.nq`. Best
working hypothesis, unverified: **environment**(the binary `.cottas`
fixture is stale relative to the `.nq` source it claims to be built
from, and needs regeneration) — but this is a guess, not a diagnosed
root cause, and no tracking issue exists. Needs a live `-v` diff before
it can be reclassified with confidence.

The 1 skip (test 22, "update: without npm-entry bundle rejects with
pending message") is **by-design**(the negative-path test only applies
when no npm-entry bundle is present; this checkout has the bundle, so
the SKIP is the correct outcome — `# SKIP npm-entry bundle present —
pending-message path not reachable`).

### OWL 2 DL type-inconsistency (tinc) — 118 pass, 10 fail (out of 128), zero oracle-assisted

Linked: #299 (`docs/designissues/2026-07-16-owl2-per-node-algebraic-tableau-909.md`),
#298, #209. Landed via `owl2-concrete-domain` (`ed8c4a03`,
ancestor-confirmed) on top of the Wave-C class-size reasoner. ⚠️ The
committed `formal/fstar/ocaml-output/owl_type_inconsistency_results.log`
reads 70 pass, 58 fail — that file is a stale artifact from an earlier
wave, not regenerated after the later landings; the 118/10 figure is
corroborated by three independent sources (the #299 issue-comment
thread, `current-state.md`'s 114/14 entry plus the +4 concrete-domain
flips it doesn't yet reflect, and commit-ancestry confirmation of
`ed8c4a03`). Named residuals, reconstructed from #299's comment thread
+ `docs/designissues/2026-07-16-owl2-per-node-algebraic-tableau-909.md`
§8 + `docs/designissues/2026-07-14-tcon-fail-classification.md`:

- `WebOnt-description-logic-909` — **disputed-fixture**, 🧭 owner
  decision pending (#299 comment 2026-07-16: three independent methods
  — hand-checked one-element model, z3 `sat`, clash-free tableau —
  agree the premise is consistent; the catalog itself marks the test
  `Extracredit`, not `Approved`, with a WG comment that even the
  approved version was defective).
- `WebOnt-description-logic-626`, `WebOnt-description-logic-627` —
  **planned-family**(#299, "double-blocking tableau extension",
  reclassified by the per-node wave's analysis as the next OWL
  dispatch candidate).
- `Inconsistent String Pattern with Disjoint Dataproperties` —
  **dependency-blocked**(regex engine phase 3, #304 — same blocker as
  CSVW test194).
- `WebOnt-description-logic-026`, `WebOnt-description-logic-027`,
  `WebOnt-description-logic-502`, `WebOnt-Thing-005` —
  **planned-family**(#299 Wave E, complementOf/oneOf search +
  budget-outs; note `dl-502`'s corpus `test:description` calls it "the
  classic 3 SAT problem," not a nominals test, per the 2026-07-14
  tcon-fail-classification doc's caveat — the "nominals" label on this
  test is inherited from an earlier, imprecise classification).
- `Inconsistent Disjoint Dataproperties` — **planned-family**(#299,
  "missing DisjointDataProperties clash, not a facet issue").
- `Minus Infinity is not in owl:real` — **planned-family**(#299,
  named scoped-out singleton, no dedicated wave yet).

### OWL 2 DL positive entailment (PE) — 135 pass, 69 fail, 2 skip (out of 204)

Linked: #298. Landed via two refutation waves (`257f2ce3`→`fd0359e5`,
`eb01d209`, both ancestor-confirmed). The 69 remaining are **not**
individually named in the source issue — grouped per #298's own
comment-2/comment-3 breakdown, reported here as a group rather than
fabricating per-test names:

- ~55 — **planned-family**(#299/#298, tableau-completeness: the
  negation is already correct but the tableau can't close — datatype-
  facet and counting territory the concrete-domain + per-node waves
  address).
- 9 (5 `differentFrom`, 4 `sameAs`) — **planned-family**(#298, nominal
  forms need O-rule/nominal-identification machinery, not yet
  dispatched).
- 4 named scoped-out (`equivalentProperty-004`, `equivalentProperty-005`,
  `rdfbased-sem-rdfsext-domain-subprop`, `rdfbased-sem-rdfsext-range-subprop`)
  — **dependency-blocked**(role-hierarchy reasoning outside the
  refuter's current completeness — #298 comment: "premise
  property-inclusion outside the refuter's role hierarchy").
- Remainder (~1, arithmetic residue of the above buckets against 69) —
  unclassified in the source issue; not separately named here rather
  than guessed.

2 skips: `Qualified-cardinality-boolean`, `Qualified-cardinality-restricted-int`
— **by-design**(functional-syntax-only fixtures; the parser targets
RDF/XML premises/conclusions, not OWL functional syntax).

### OWL 2 DL negative entailment (NE) — 22 pass, 1 fail (out of 23)

`WebOnt-imports-002` (`FAIL/unexpected-entailment`) —
**planned-family**(import-resolution edge case; same family as the OWL
2 row's syntax-dl species misses on `imports-004/012/014`). Confirmed
unchanged across every OWL wave this session traced (#298/#299
comments both say "NE 22/1 unchanged").

### OWL 2 RL positive entailment — 28 pass, 2 fail (out of 30)

`WebOnt-I5.5-005`, `WebOnt-I5.26-010` — **by-design**(documented in
`docs/designissues/2026-07-03-owl-rl-pe-fails-fix-sketch.md` as OWL 1
Full comprehension entailments deliberately outside the OWL 2 RL
closure). The suite moved from 27/2/1 (that doc's "end state") to
28/2/0 — the 1 skip it left open has since resolved to a pass; the 2
fails are unchanged.

### OWL 2 DL syntax-dl species — 319 pass, 2 fail, 2 skip (out of 323)

⚠️ This ledger's existing OWL 2 row headline ("302 pass, 2 fail (out of
304 scored), 19 skipped") is stale — the committed
`formal/fstar/ocaml-output/owl_syntax_dl_results.log` confirms 319/2/2
today (17 of the 19 former functional-syntax-only skips now run and
pass; likely the "OWL profiles" work the task brief flagged as
concurrent). The 2 fails are unchanged from the ledger's existing
prose:

- `FS2RDF-literals-ar` — **disputed-fixture**(RDF/XML premise our
  parser rejects; existing ledger text).
- `WebOnt-I5.5-005` — **disputed-fixture**(header-less conclusion; the
  graph-identical `I5.5-006` sibling is judged FULL by the corpus, so
  no graph-level function separates them; existing ledger text).

### OWL 2 profile EL / QL — 108 pass, 13 fail (of 121) / 83 pass, 4 fail (of 87)

🧭 Both rows are new in `docs/test-results/latest.json` (commit
`0f4090d5`, ancestor-confirmed) with no matching row in this ledger and
no GitHub issue found referencing either suite name. Not individually
triaged in this pass — out of the brief's named scope (CSVW/OWL
tinc-tcon-PE-NE/ShEx/XSLT/GRDDL plus the 9 named fresh-investigation
suites) and 17 total fails is more than can be responsibly named from
scratch inside this docs-only pass. Surfacing per rule 3 of "Reading
owner steers": these look like the "OWL profiles" work the task brief
flagged as being landed concurrently — recommend a dedicated triage
pass once that work settles, rather than this session guessing at
per-test dispositions.

### QUDT integrity — 0 pass, 0 fail, 29 skip (out of 29)

Re-run fresh this session (`./bin/linux-x86_64/qudt_runner`, matches
the committed log exactly): all 29 skips are accounted for and the
suite is not silently dead — it parses 131,169 triples + runs
9-for-9 on the sibling `qudt_user_shapes` suite in the same process.
Not a 🔴 finding.

- 26 — **environment**(per-shape wall-clock budget: the 420s cap trips
  before wide-target shapes finish; `docs/designissues/2026-07-10-qudt-scoping.md`
  names this a perf-program work item — indexed SPARQL-constraint
  evaluation, not an engine defect).
- 2 (`Concept-label-IRI-Shape`, `UnitsHaveRdfClassQudtUnitTriple`) —
  **dependency-blocked**(`sh:SPARQLTarget`, #181 — the one acknowledged
  SHACL gap).
- 1 (`UniqueSymbolTypeRestrictedPropertyConstraint`) — **by-design**
  (`sh:deactivated true`, excluded by SHACL semantics itself).

### RIF Core — 46 pass, 1 fail, 3 skip (out of 50)

All named in `.github/test-suites/rif.yaml`'s own header, re-verified
against the committed log:

- `RDF_Combination_Constant_Equivalence_4` — **disputed-fixture**(a
  malformed `xsd:string` datatype IRI present in both the official
  `Core_v1.22.zip` and the archived W3C wiki source; not fixable
  without breaking correct datatype-IRI semantics).
- `Builtins_List`, `NestedListsAreNotFlatLists` —
  **dependency-blocked**(RIF List terms are not modelled in
  `RIF.Core.Syntax.fst`).
- `Builtins_Time` — **dependency-blocked**(the ~60-builtin date/time/
  duration family; only the `EBusiness_Contract` slice is
  implemented).

### rml_io — 17 pass, 1 fail, 55 skip (out of 73)

Re-run fresh this session (`./bin/linux-x86_64/rml_runner --io -v`,
matches the committed log's 17/1/55 exactly):

- `RMLSTC0009a` — expects an empty dataset (`error=true`) but the
  runner produces 3 triples — **planned-family**(no dedicated issue
  found; same shape as an unhandled error-detection case in the
  rml-io source-tests section, needs its own triage — flagged, not
  fabricated a root cause).
- 41 — **by-design**(`RMLTTC0*` logical-target/output-serialization
  tests, out of scope per the 2026-07-05 rml program plan Stage 9).
- 7 — **dependency-blocked**(XPath/XML reference formulation not
  implemented).
- 4 — **dependency-blocked**(compressed source, needs decompression).
- 1 — **dependency-blocked**(relational SQL2008 source, needs an
  RDBMS).
- 1 — **dependency-blocked**(non-UTF-8/UTF-16 source encoding not
  supported).
- 1 — **dependency-blocked**(SPARQL-over-RDF iterator not
  implemented).

### ShEx validation — 1181 pass, 1 fail (out of 1182)

`start2RefS2` — **disputed-fixture**, linked
[`shexSpec/shexTest#43`](https://github.com/shexSpec/shexTest/issues/43)
(closed 2023, unreconciled upstream — `start2RefS2.json`/`.ttl` use
predicate `p1`, `start2RefS2.shex` uses `p2`; per
`tests/shex-shexj-twins/README.md`, our ShExJ-first runner scores
against the JSON and carries the mismatch as a fail rather than
patching a vendored fixture).

### tests_unit — dashboard 35 pass, 6 fail (of 41); fresh run 45 pass, 0 fail (of 45)

**environment**(the dashboard capture ran against a checkout with
gaps this session reproduced the failure signature for: this
worktree's `third_party/testing/w3c/` submodule was NOT populated
until `tools/ensure-test-env.sh` was re-run against the actual
worktree path — an initial run against a sibling checkout's root had
falsely reported "ok". With the submodule missing, 4 tests
(`owl_direct_pipeline_timing`, `owl_rl_bisect`, `owl_rl_closure_diff`,
`owl_rl_sequenced`) fail on `Sys_error("...simple.ttl: No such file or
directory")` — the same ENOENT-from-missing-submodule shape
`workflow-gotchas-debugging` hazard #15 describes, though this
session's reproduction hit 41/4 not the dashboard's 35/6, so the
dashboard's exact capture environment was likely worse-broken still,
e.g. opam switch not activated per iron rule #12). After
`tools/ensure-test-env.sh` + `eval $(opam env --switch=fstar
--set-switch)`, the suite is clean: **45 pass, 0 fail (out of 45)**.
The dashboard number needs republishing from a hazard-15-clean
checkout — flagged for the publication step, not fixed here (docs-only
commit, no rebuild triggered).

### xml_conformance — 1414 pass, 0 fail, 1171 skip (out of 2585)

The runner's own "HONEST BREAKDOWN" (re-verified against the committed
log), five categories, all **by-design**(explicit Stage-A scope
limits, not silent gaps):

- 386 — valid docs rejected at a Stage-A DTD boundary (markup entity /
  external subset / DTD construct beyond the WF slice).
- 332 — not-wf violation is in the DTD internal subset
  (parsed-but-not-validated — Stage-A scope limit).
- 416 — other (DOCTYPE-external-on-valid, encoding-name edge cases,
  invalid/error-by-design, external-entity exemption, file-not-found).
- 37 — out-of-profile (not-wf holds only under XML 1.1 or Namespaces
  in XML; this parser is XML 1.0 non-namespace).
- 0 — vacuous (retired by Stage-A DTD support; the runner asserts this
  stays 0).

### XSLT 1.0 — 79 pass, 9 fail (out of 88)

Linked: #302. Landed via `xslt-burndown-1` (`fd5fc372`,
ancestor-confirmed): "XSLT 79 pass, 9 fail (of 88), was 75/13" —
this ledger's dashboard-adjacent headline is stale at 75/13. Named
residuals, from #302's 2026-07-16 comment:

- `copy-0601`, `match-045`, `namespace-4101`, `namespace-4501`,
  `namespace-4801`, `node-1601` (comment counts this family as "5" but
  names 6 — quoted as written per the steers-quoting discipline rather
  than silently corrected) — 🟡 **in flight**: branch
  `xslt-namespace-nodes`, dispatched per the owner's 2026-07-16
  XSLT-polish priority; not yet merged into this worktree's HEAD
  (branch not found in `git branch -a` as of this measurement).
- `copy-2601`, `select-1001` — **planned-family**(#302, document-node
  prolog/epilog comment handling).
- `id-016` — **planned-family**(#302, DTD-ID `id()` function).

All nine are confirmed in-scope (none PSVI/XSLT-2.0-schema-aware; #302
explicitly excludes that boundary, tracked separately at #190).
