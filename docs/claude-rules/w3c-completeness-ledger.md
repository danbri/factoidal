# W3C/SemWeb Completeness Ledger

**Standing goal (owner, 2026-07-09):** Exemplary and full implementation
of every OFFICIAL W3C RDF/semweb-related specification we touch.
**RDF 1.2 / RDF-star is UN-PARKED and in progress** (owner directive
2026-07-16): the syntax/eval suites are landed at **212 pass, 0 fail**
(Turtle/TriG reified triples `<< >>`, `~` reifiers, `{| |}` annotation
blocks, VERSION directive, N-Triples/N-Quads triple terms; RDF.Canonical
triple-term bnode recursion) behind a threaded `rdf_syntax_mode`
(Mode_11 default, so RDF 1.1 output stays byte-identical); the
rdf-semantics + c14n-1.2 suites are the next waves (#305); SPARQL 1.2
triple-term/reifier syntax landed (219/254, see the SPARQL 1.2 row). Anything short of full is listed here as a **failure**,
not softened as a skip. Focus: in-depth coverage and performance. Every
capability gets an npm API and Hub documentation.

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
| **CSVW** (csv2rdf) | 265 pass, 5 fail (out of 270) [2026-07-16, four burndown rounds + the verified-regex format arm; ledger `2026-07-15-csvw-csv2rdf-fail-triage.md`; was 218/52 on 2026-07-15. Remaining 5: test036/037/102 (family C structural), test148/149 (title-language decode shape)] | UAX-35 date/time + number `format` engines landed 2026-07-10 (F\* `CSVW.Formats`: date/time patterns, number patterns incl. groupChar/decimalChar/percent/per-mille/exponent, `Y\|N` booleans, duration lexical checks; plus `separator`/list values and the `-`→`%2D` default-propertyUrl encoding). Remaining 52, enumerated: **metadata discovery, PARKED protocol** — test011/012/014/016, test116/118/121/122/123, test259/260 (Link header, directory metadata, `/.well-known/csvm` — in scope per owner clarification 2026-07-15, round 3); **metadata normalization warnings** — test047/048/049, test097/100/101/102/107, test263/273/275/276/277 (invalid-property pruning, `@base`/`@type` context edge cases, wrong-level properties); **schema compatibility + validation** — test023, test125/126/127, test130/131, test148/149, test150/151, test238, test278 (header=false, required/null, column-name restrictions, title-language intersection, non-builtin datatype names); **complex fixtures** — test032/033/034/035/036/037/038/039 (virtual columns, multi-subject, referenced schemas, inherited-property combinatorics); **rowTitles** — test235/236; **table-level `separator` + ordered lists** — test305/306/307; **duration regex `format`** — test194 (needs regex engine); **2 cross-table NegativeRdf** — test252/253 (foreign-key validation) | ✓ / ✓ (post 13) |
| **DID** (did:key) | 8/8 on stage-1 vectors | depth: suite is a sliver of DID Core (no did:web, no resolution metadata) — needs a real conformance target enumerated | ✓ / ✓ (post 23) |
| **GRDDL** | Stage 2 (local docroot): 17 pass, 51 fail, 0 skip (out of 68) [2026-07-18, +2 side-flips card5n/projectsSpreadsheet from the XSLT with-param fidelity fix], was 15/53 [2026-07-16], was 9/8/51 | Stage 2 (issue #301) landed: namespace-document (§3) and profile-document (§5) transformation discovery now live in F* (`GRDDL.Discovery`: `head_custom_profile_uris` / `profile_doc_transformations` / `root_namespace_uri` / `namespace_doc_transformations`, plus `<base href>`-aware `doc_base`) as pure Tot tree-walks; the runner FETCHES the referenced second documents from the vendored docroot (rule #11 — I/O only, no live network). Every manifest test is now RUN, so all 51 former skips are converted to honest pass/fail. +6 passes over Stage 1: htmlbase3, inline-rdf1/2/3, multipleRepresentations, xmlbase3 (all previously blanket-skipped as `NetworkedTest`). Fail buckets: **30 `fail-graph-mismatch`** (consumed XSLT-engine fidelity gaps, HTTP content-negotiation, recursion/merge, XInclude posture), **6 `fail-known-gap-xslt-feature`** (inline-rdf4/5/6/8/9/10 xml:base/xml:lang in embeddedRDF.xsl), **10 `fail-no-transformation-discovered`** (namespace/profile second-document not vendored: two-transforms, three/four-transforms, ns-*, sq1/sq2, glean/hcarda/card5na/grddlProfileBase3), **7 `fail-transform-not-vendored`** (a discovered stylesheet — .sxsl or a redirect-base path — is not present offline). Residue = recursion + loop-detection (loop/loopx/ns-* chains), HTTP redirect-base and content-negotiation simulation, HTML tag-soup input (Stage 3), and complex real-world transforms (hcard2rdf, grokSheet, glean-profile) that exercise consumed-engine XSLT gaps. Engine bugs are reported, not fixed here. | ✗ / ✗ |
| **JSON-LD 1.1** | toRdf 461 pass, 0 fail, 6 skip (of 467); fromRdf 53 pass, 0 fail, 1 skip (of 54); expand 379 pass, 0 fail, 6 skip (of 385); compact 244 pass, 0 fail, 2 skip (of 246); flatten 56 pass, 0 fail, 2 skip (of 58) [2026-07-10] | **frame / html API suites NOT RUN — counted as failed until measured**. flatten is now MEASURED: `bin/jsonld-flatten-runner` drives `JSONLD.Flatten.fst` (Node Map Generation § 6.2 with the Generate-Blank-Node-Identifier issuer relabelling to `_:b0`/`_:b1`/… in spec issue order, the Flattening Algorithm § 6.1's named-graph folding + code-point node ordering + @id-only dropping, and — for context-bearing entries — compaction of the flattened array through the landed `JSONLD.Compact` machinery with a pinned top-level `@graph`), comparing via the same `Parser.JSONLD.jsonld_expanded_equal` JCS-canonical structural equality as expand/compact; the one NegativeEvaluationTest (conflicting indexes) passes as `flatten_document = None`. No changes to Expand/Context/Compact were needed — toRdf/fromRdf/expand/compact floors re-measured, held. The 17 skips across the five suites are enumerated JSON-LD-1.0-version fixtures (documented per-ID in the runners; flatten's 2: t0014, t0038 — both the 1.0 every-term-is-a-prefix expansion rule; run under JLD_NO_SKIP=1 to re-measure) | partial / ✓ (post 07) |
| **OWL 2** | RL-PE 28 pass, 2 fail (out of 30) [re-measured 2026-07-16]; profile-QL 83 pass, 4 fail (out of 87) + profile-EL 108 pass, 13 fail (out of 121) [aggregate PE+NE+Cons+Inc under RL closure, re-measured 2026-07-16]; syntax-dl species 319 pass, 2 fail (out of 321 scored), 2 skipped (functional-syntax-only) — 323-case catalog [re-measured 2026-07-16; skip count fell from 19 to 2 as the functional-syntax premise parser widened]; DL-regime type-inconsistency 124 pass, 3 fail (out of 127 scored), 1 skipped (semantics-scope: WebOnt-Thing-005 is RDF-Based-only per catalog), zero oracle-assisted [2026-07-17: +Inconsistent-Disjoint-Dataproperties (integer singleton clash) + Thing-005 recategorization; remaining 3 = dl-909 (disputed fixture), dl-502 (nominal-DPLL wave in flight), Minus-Infinity (owl:real machinery); 2026-07-16: concrete-domain intervals (+4: Float-Discrete, Rational-002, I5.8-001/003), inverse-lifted subPropertyOf (+4: dl-626/627/026/027), verified-regex pattern-facet clash (+1: Inconsistent String Pattern); remaining 5 = dl-909 (disputed fixture, satisfiable by three analyses, Extracredit status — owner call pending #299) + dl-502/Thing-005 + 2 budget/oneOf family; 2026-07-15: verified Farkas-certificate class-size reasoner decides dl-910 + one=two; earlier 2026-07-14, five tableau waves: datatype facet satisfiability, role box (subPropertyOf/FunctionalProperty/transitive), contrapositive unfolding + exact-cardinality-0 NNF, SHIQ ≤-rule witness merging, named-individual identification + stored FP max-1 bounds — up from 70 pass, 58 fail (out of 128), zero regressions]; type-consistency 352 pass, 0 fail (out of 352) [2026-07-15: empty-premise harness fix +16, XMLLiteral c14n equality retiring WebOnt-202, RDFXML XMLLiteral opaque capture; soundness gate now ZERO unexpected-inconsistency] | Tableau REFUTATION landed 2026-07-10 (`Tableau.Refute.fst`: clash-detecting `tableau_consistent` — NNF, lazy TBox unfolding, disjunction branching under a threaded linear budget, depth-capped ∃-witnesses, complement/min-max/counting/bottom-property clash rules, AllDifferent + self-disjoint-property + rdf:nil graph checks; wired into `owl_runner --regime dl` inconsistency AND consistency scoring with the SIGALRM fallback so DL never scores below RL); five 2026-07-14 waves extended the tableau with datatype facets, role-box reasoning, contrapositive unfolding, SHIQ ≤-rule witness merging, and named-individual identification (soundness gate through the 07-14 waves: exactly one unexpected-inconsistency, WebOnt-miscellaneous-202 — RETIRED 2026-07-15 by XMLLiteral c14n equality; gate is now zero); the 2 syntax-dl species residuals re-triaged 2026-07-16 (checker is F\* `OWL2.SyntaxDL.fst`; species covers premise AND conclusion docs), both structurally blocked / fixture-disputed, no sound zero-regression flip exists: **(1) FS2RDF-literals-ar** — NOT a parser rejection (the RDF/XML premise parses fine); its `test:rdfXmlPremiseOntology` is a defective serialization whose datatype IRIs are lowercased case-variants of the OWL 2 datatype map (`xsd:datetime`/`xsd:unsignedint`/`xsd:negativeinteger`/`xsd:anyuri`/… vs the map's `xsd:dateTime`/`xsd:unsignedInt`/…). Those IRIs are not in `builtin_datatypes`, so `species_violations` reports them `reserved-vocabulary-as-datatype` → FULL. The corpus's DL label reflects the correct-cased `fsPremiseOntology`; the runner prefers the RDF/XML premise, so we score the defective graph. Fixture serialization defect, not a checker gap. **(2) WebOnt-I5.5-005** — the classified graph is premise (`owl:Class a`, header-less) ∪ its comprehension conclusion (a bare header-less `owl:unionOf` class expression not used in any axiom — the description literally calls it "the effect of the comprehension principles in OWL Full"), giving violation `conclusion: no-ontology-header` → FULL. Its sibling **I5.5-006** (in all.rdf, NOT in syntax-dl.rdf; second doc is a cyclic-list `rdfXmlNonConclusionOntology`, not fed as a conclusion) is classified on the identical header-less `owl:Class a` premise ALONE and is expected FULL — which it correctly is. Since 005's fed graph strictly CONTAINS 006's, and the extra triples are precisely the OWL-Full comprehension construct, no monotone graph classifier can call 005 DL while keeping 006 FULL. Structurally blocked; leaving 005 FULL keeps 006 correct. (This corrects the earlier ledger wording "graph-identical I5.5-006 sibling" — the graphs differ, but the shared header-less premise plus the subset relation is what makes the pair inseparable.) Species control over all.rdf incl. the 166 FULL-only negatives absent from syntax-dl.rdf: 482 pass, 5 fail (out of 487 scored), 2 skipped [re-measured 2026-07-16] — 163/166 FULL-only cases correctly rejected; the 5 fails = FS2RDF-literals-ar + I5.5-005 (above) + imports-004/012/014 (verdict=DL expected=FULL): each imports a doc that is FULL only because it types an entity with the legacy `rdfs:Class`/`rdf:Property`/`rdf:List` vocabulary, which `type_object_whitelist` deliberately admits as DL for the many species-DL corpus cases that use the same legacy typings — the same no-separating-graph-function bind, and an import-resolution edge (the imported doc IS loaded via `resolve_species_imports`; the whitelist, not the loader, is why the union scores DL). #262 sameAs perf blowup | closure ✓, tableau ✓ / page queued (#93) |
| **QUDT** (v3.4.0) | NEW ROW [measured 2026-07-10]: user-shapes fixtures 9 pass, 0 fail (out of 9); integrity ruleset 0 pass, 0 fail, 29 skip (out of 29 shapes: 26 wall-clock-budget skips, 2 sh:SPARQLTarget #181, 1 sh:deactivated) | QUDT (qudt.org) is an independent ontology suite, not W3C, and publishes **no official conformance suite** — the measured targets are the ones defined in `docs/designissues/2026-07-10-qudt-scoping.md` (Layer A landed: vendored v3.4.0 distribution + rulesets in `third_party/qudt/`, runner `bin/qudt-runner`, suite `qudt.yaml`). Burn-down: (1) the integrity budget-skips are a PERF failure, not a correctness one — per-focus-node sh:sparql evaluation over the 131k-triple all-in-one exceeds the 10-minute cap for every ruleset shape (fixed cost is only 20s; see performance.md § QUDT corpus); indexed/pre-compiled SPARQL-constraint evaluation is the unlock. (2) Layer B: exact-rational unit conversion + dimension-vector algebra in F\* (provable round-trip identity relative to the pinned v3.4.0 multipliers) with qudt-convert/qudt-dimension derived suites. (3) Layer C: qudtf: SPARQL extension functions. (4) sh:SPARQLTarget (#181). | ✗ / ✗ |
| **RDF 1.1** | 1031/0 (strict) | runner-integrity fix landed: graph equality is now RDFC-1.0 canonicalization + byte-compare (F* `RDF.GraphIsomorphism`, not lenient bnode-collapse), with lang-tag-case value equivalence; score held at 1031/0 under the strict comparison (our parsers produce graphs bnode-isomorphic to the expected N-Triples/N-Quads), 0 canonicalization-budget fallbacks — so 1031 is now earned, not inflated. Remaining: RDF/XML deep-nesting overflow (#279) | ✓ / ✓ |
| **RDFC-1.0** | 86/0 — complete | none on conformance; needs a perf row (HNDQ budget behavior) | ✓ / ✓ (post 08) |
| **RIF Core** | 34 pass, 4 fail, 12 skip | the 4 + the 12, each with a named reason or a fix | ✓ / ✓ (post 10) |
| **SHACL** | core 98 pass, 0 fail (out of 98); sparql-constraints 22 pass, 0 fail (out of 22) [2026-07-10, denominators audited] | audited both denominators against the vendored `third_party/testing/shacl/data-shapes-test-suite` manifest tree: walking `mf:include` from the suite's own top-level `tests/manifest.ttl` (→ `core/manifest.ttl` + `sparql/manifest.ttl`, and every nested section — complex/misc/node/path/property/targets/validation-reports under core; component/node/property/pre-binding under sparql) yields exactly 120 `sht:Validate` entries, matching 98+22 to the test. Both denominators are the FULL suite — no unrun section exists. The one test outside the 120, `sparql/component/nodeValidator-001.ttl`, is the suite's only entry carrying `mf:status sht:proposed` (every other of the 120 is `sht:approved`) and is correctly omitted from `sparql/component/manifest.ttl` by the WG itself — not our gap (it passes when run directly and off-ledger; not counted since it is not part of the approved suite). SHACL 1.2 (`shacl12-test-suite`, node-expr/rules/sparql-targets sections) is a separate not-yet-Recommendation Public Working Draft built on RDF/SPARQL 1.2 (`third_party/testing/shacl/README.md`) — future scope, not this row. SHACL Compact Syntax (`shacl-compact-syntax/`) is a Community Draft with no `mf:Manifest` conformance suite (paired `.shaclc`/`.ttl` fixtures only, no include tree) — a different concrete-syntax parsing concern, not this row's mandate. No runner or F* change required. | ✓ / ✓ (post 05) |
| **ShEx** (CG) | validation 1181 pass, 1 fail (out of 1182; the 1 = the upstream start2RefS2.json p1/p2 fixture defect); negativeSyntax 100 pass, 0 fail (out of 100); ShExC↔ShExJ differential 433 of 433 [2026-07-10] | negativeSyntax first scored 2026-07-10 (`shex_runner --negative-syntax`): initial 85 pass, 15 fail — all 15 were Parser.ShExC permissiveness bugs (bare-`a` outside predicate position, duplicate xsFacets, litNodeConstraint+shapeRef juxtaposition, numeric facet on non-numeric datatype, bnodes in value sets / predicate position, REGEXP escape whitelist, LANGTAG validation, empty language-tag exclusions), fixed in F\* the same landing with the 433/433 differential as the over-tightening guard. Dashboard rows `shex` + `shex_negative_syntax` both emitted. Remaining unscored: `negativeStructure/` (14 fixtures) and `schemas/` RepresentationTest ShExC↔ShExJ round-trips (441; the ShExC→AST direction is what the differential covers). Advisory tree-sitter-shexc three-way probe: `tests/shexc-treesitter/run.sh`; grammar audit: `docs/designissues/2026-07-10-shexc-treesitter-grammar-audit.md` | ✓ / ✓ (post 06) |
| **SPARQL 1.1** | 631/0; regimes 70/70 | ALL 8 strict-runner failures now fixed in F*. Tasks #100 (7 of 8): **BNODE()/BNODE(str)** now per-solution + per-occurrence fresh (row+call-site seed via sha256, pure F*); **UUID()/STRUUID()** distinct per binding (same seed); **NOW()** returns a valid xsd:dateTime (boundary `fx_current_datetime` assume val, #287); the OWL cardinality/someValuesFrom rewrite's internal `?_sv_`/`?_mc_`/`?_mxqc1_` vars are stripped at the FINAL projection only (parent min-1, parent max-1 Female), keeping inner Select_All sub-select correlation intact; **RDF inference test (rdf01)** fixed via rdfD2 (predicate ⇒ rdf:Property) applied only under the ent:RDF regime. Task #101 (last one): **RIF Brain Anatomy (rif04)** — the RIF Import(<import001.rdf> OWL-Direct) directive's declared entailment profile is now materialised. `Parser.RIFXML.parse_rif_program_with_import_profiles` surfaces each import's (location, profile) pair; `RIF.Core.Tests.materialise_import_graph` dispatches the profile IRI to the closure the SPARQL regimes already ship (Simple→plain, RDF/RDFS→`rdfs_closure_with_reflexivity`, OWL-Direct/OWL-RDF-Based→`owl_rl_closure_with_reflexivity`) before the imported triples merge into the premise, so `g1/pcg0 rdf:type MaterialAnatomicalEntity` (from `Gyrus rdfs:subClassOf MaterialAnatomicalEntity`) exists when the RIF rule body matches. 0 canonicalization-budget fallbacks. Also: parser `--admit_smt_queries` regions removed 2026-07-10 (#91) — SPARQL11.Parser.fst verifies with zero admits; Protocol 34/0 + GSP 19/0 pass via in-process dispatch through the verified SPARQL_Protocol/SPARQL_GraphStore modules; factoidal-http serves query/update on the wire (GSP writes behind --rw + delta log); wire-level suite replay harness not yet automated | ✓ / ✓ |
| **SPARQL 1.2** | 247 pass, 7 fail (out of 254) [2026-07-19, was 244→240→237→232→219→100] | Triple-term/reifier syntax + VERSION decl + codepoint escapes + directional lang tags + base-direction builtins, all gated behind the `sparql12` lexer/parser bool so SPARQL 1.1 is byte-identical (631/0 protected). Families fully green: syntax-triple-terms-positive **113/0**, syntax-triple-terms-negative **65/0**, **version 9/0**, **codepoint-escapes 8/0**, rdf11 3/0, grouping 1/0. Near-green: **lang-basedir 10/1** (hasLANG/hasLANGDIR/LANGDIR/STRLANGDIR builtins + CONCAT direction-preservation landed; the `E_HasLang`/`E_StrLangDir`/etc. constructors ripple through SHACL.Validation + Parser.JSONResults exhaustive matches). Partial: eval-triple-terms **38/3** (triple-term value equality + CONSTRUCT-WHERE reifier bnode-rewriting, then the reifier-enumeration fix #305: template bnodes mint fresh-per-solution per SS16.2, un-collapsing construct-5's two distinct reifiers). The triple-term-in-`GRAPH` cluster (graphs-1/2 "Reified triples - GRAPH"/"GRAPHs with blank node") is FIXED — root cause was a CONSUMER I/O gap, not the F* algebra: `w3c_runner` routed the `qt:data data-4.trig` multi-graph dataset through the flat single-graph loader, silently dropping the `.trig`'s named graphs so `GRAPH ?g {}` matched nothing. `load_dataset` now parses `.trig`/`.nq` qt:data via the verified `Parser_TriG`/`Parser_NQuads` Mode_12 DATASET entry points and merges `ds_named` (rule #11/#15: parser dispatch, no semantics). Remaining 7 fails: **3 eval-triple-terms** = BIND-CONSTRUCT (expr-01) + ORDER (order-2) + UPDATE reifier templates; 1 lang-basedir; syntax 0/2; expression 0/1. Eight waves landed (100→247), SPARQL 1.1 631/0 + rdf-turtle 313/0 held throughout. Verified clean (no `--lax`/admits). | 🟡 syntax+aux green / eval residue = BIND/ORDER/UPDATE reifier cluster |
| **VC 2.0 + Data Integrity** | structural Stage 1: 117 pass, 0 fail (out of 117 scorable; 3 fixtures withdrawn upstream of 120 vendored) [2026-07-10]; crypto roundtrip 8 pass, 0 fail; official W3C vc-di-eddsa-test-suite eddsa-rdfc-2022 create+verify (via `bin/vc-api-shim`, task #88): 31 pass, 0 fail (out of 31) [2026-07-14, suite fully green — proof sets/chains + previousProof landed, was 26 pass, 5 fail]; official vc-data-model-2.0-test-suite issuer/verifier HTTP tests (same shim): 59 pass, 0 fail (out of 59) [2026-07-14, suite fully green — relatedResource structural/digest checks (VCDM 2.0 s5.3) + JSON-LD named-graph/@container:@graph VP expansion fix, was 22 pass, 37 fail] | eddsa-rdfc-2022 measured against the official corpus, including multi-proof sets and `previousProof` chains; eddsa-jcs-2022 not implemented (different JCS transform path); context-driven type redefinition; browser/JS bundle not yet measured against the official corpus | ✓ (typed crypto) / ✓ (post 13) |

**RDF 1.2 / RDF-star: UN-PARKED (owner, 2026-07-16), in progress** —
syntax/eval suites landed 212/0 (see the header note above); rml-star
unblocked in principle, still sequenced behind the 1.2 semantics/c14n
waves and SPARQL 1.2 (#305). (The former "Protocols parked" note is
also obsolete: Protocol 34/0 and Graph Store 19/0 pass in-process, and
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

**Capability-existence rule (added 2026-07-17, owner escalation on the
`namespace::` axis).** `disputed-fixture` and `by-design` may only be
applied when the underlying capability EXISTS; a missing feature is
always **planned-family**/gap, stated as such. Labelling a hole
"implementation-defined" or "disputed fixture" implies the processor
made a *correct choice among valid behaviours* — false when it produces
nothing because the feature was never built. Full re-audit + the
XPath/XSLT spec-derived coverage matrix that prompted this rule:
[`docs/designissues/2026-07-17-xpath-xslt-coverage-matrix.md`](../designissues/2026-07-17-xpath-xslt-coverage-matrix.md).

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
| XSLT 1.0 (slice-1 pin) | 87 pass, 0 fail, **1 local-override** (out of 88) [2026-07-18, `namespace::` axis IMPLEMENTED (#302 landed, `XPath.Eval.inscope_ns_ordered` + `Ax_Namespace` + `CI_Namespace`); node-1601's sole divergence is namespace-**node sibling order** (implementation-defined per XPath 1.0 §5.4), now a `local-override` — the capability EXISTS and emits a documented deterministic order, so it is a by-design disposition, no longer a gap. Was 87/1 with the axis unmodeled. See `tests/local-overrides/xslt-node-1601.json` + coverage matrix.] | ✅ / by-design override |
| XSLT 1.0 conformance (Apache Xalan mirror) | **1379 pass, 303 fail, 8 skip (out of 1690)** [2026-07-19, burndown: 970 → … → 1361 → 1368 → **1379/303 (attribset: xsl:attribute/@namespace prefix synthesis + AVT-under-document-node force_abs, +11 net incl. corpus-wide path-AVT spillover, #302)** — measured, not a pin. **+409** (17 XSLT waves); boolean fully green]. Corpus: OASIS XSLT 1.0 conformance cases as mirrored by `apache/xalan-test` (Apache-2.0), vendored as submodule `third_party/testing/xslt1-xalan/xalan-test-src` + generated `manifest.json`; run via `xslt_runner --base third_party/testing/xslt1-xalan` (same F\*-extracted `XSLT.Transform` oracle). ✅ The non-ASCII engine CRASHES are fixed (#307, `soc` now UTF-8-safe via `String.string_of_list`): the 4 tests (sort-alphabet-polish/russian, output28/73) that raised `Char.chr` on codepoint>255 no longer crash — they now run and fail-on-value (sort-collation / output-encoding specifics), so ENGINE-EXN is 0 (was 4) and the corpus is crash-free. Xalan TOTAL unchanged (997/685/8) since those 4 still fail on value. Remaining fails cluster onto the matrix holes: numberformat **12** (was 44 — format-number/decimal-format #6 landed, 32/44), impincl **3** (was 29 — xsl:import/include #7 landed, 26/29), numbering **4** (was ~91 — xsl:number + level=any + predicate #4 landed, 89/93), namespace-alias (#16), attribset **12** (was ~16 — xsl:attribute/@namespace prefix synthesis + AVT doc-node paths landed, 35/47; residue = intervening-LRE ns decls + name-QName-prefix-reuse heuristic namespace01/17/18/attribset24), idkey **5** (was 22 — key()/id()/format-number() now resolve inside predicates + xsl:sort keys + match patterns via full-env threading in XPath.Eval.filter_one_pred, 57/62), output **27** (was ~75 — xsl:output #18 + uppercase <META> injection + comment --/trailing- escaping landed, 80/109; residue = disable-output-escaping cluster + DOCTYPE-case), reluri+mdocs (document() partial), string **19** (was 40 — translate/substring #2 landed, 115/135), boolean+expression (lang #3), extend 5 (fallback #17), whitespace **4** (was 15 — xsl:strip-space/preserve-space #15 landed, 19/23), message 2 (#9), processorinfo 1 (system-property #11), plus general axis/match/select/copy corners. Per-category table: `third_party/testing/xslt1-xalan/INFO.txt`. Provenance + license-verdict table: `third_party/testing/xslt1-xalan/PROVENANCE.md`. | 🟡 gap named / burndown target (matrix) |

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

### OWL 2 DL type-inconsistency (tinc) — 124 pass, 3 fail (out of 127 scored), 1 skipped (semantics-scope: RDF-Based only), zero oracle-assisted [re-measured 2026-07-17]

Linked: #299. Score history since the 118/10 measurement: `owl2-double-
blocking` (inverse-lifted subPropertyOf, 122 pass/6 fail — flips dl-626,
dl-627, dl-026, dl-027), a regex-phase3 pattern-facet clash (123/5 —
flip: Inconsistent String Pattern), and `owl2-tableau-completeness`'s
disjoint-dataproperty numeric-singleton clash (`541753cb`, 124 pass, 4
fail out of 128 — flip: Inconsistent Disjoint Dataproperties), all
ancestor-confirmed on top of the `owl2-concrete-domain` wave (`ed8c4a03`).
2026-07-17: `WebOnt-Thing-005` recategorized OUT of the DL-regime
denominator (harness categorization fix, evidence + rationale below) —
scored denominator moves 128 -> 127, pass/fail on the remaining 127
UNCHANGED (124/3, was 124/4 including Thing-005) — a categorization
move, not a verdict change; confirmed by a fresh `owl_runner
type-inconsistency.rdf --regime dl` run whose 3 named FAIL lines are
identical to the pre-fix run's non-Thing-005 fails (`Minus Infinity is
not in owl:real`, `WebOnt-description-logic-502`,
`WebOnt-description-logic-909`).

Named residuals (the 3 scored fails):

- `WebOnt-description-logic-909` — **disputed-fixture**, 🧭 owner
  decision pending (#299 comment 2026-07-16: three independent methods
  — hand-checked one-element model, z3 `sat`, clash-free tableau —
  agree the premise is consistent; the catalog itself marks the test
  `Extracredit`, not `Approved`, with a WG comment that even the
  approved version was defective).
- `WebOnt-description-logic-502` — **encoding-not-loaded** (root cause
  re-diagnosed 2026-07-17, #299/#209 nominal-DPLL wave; see the
  dedicated subsection below). ⚠️ NOT a search-budget problem: the
  engine returns a definite `FAIL/unexpected-consistency` (finds a
  model) with ZERO refuter cap-trips — the 3-SAT constraints never
  reach the tableau, so there is nothing for a DPLL search to refute.
  The prior "complementOf/oneOf search + budget-outs" framing was
  wrong about the layer. The corpus `test:description` calls it "the
  classic 3 SAT problem," not a nominals test (the "nominals" label is
  inherited from an earlier, imprecise classification, per the
  2026-07-14 tcon-fail-classification caveat).
- `Minus Infinity is not in owl:real` — **planned-family**(#299,
  named scoped-out singleton, no dedicated wave yet).

**`WebOnt-Thing-005` disposition (2026-07-17, #299) — outcome (a):
harness categorization bug, FIXED, not an engine gap.** Catalog
evidence, quoted verbatim from
`third_party/testing/owl/type-inconsistency.rdf` (TestCase
`WebOnt-Thing-2D005`):

```
<test:description>The extension of OWL Thing may not be a singleton in OWL Full.</test:description>
<test:status rdf:resource="&test;Proposed" />
<test:semantics rdf:resource="&test;RDF-BASED" />
<test:species rdf:resource="&test;FULL" />
<test:species rdf:resource="&test;DL" />
```
plus a same-subject `owl:NegativePropertyAssertion` immediately after
the `TestCase` block:
```
<owl:sourceIndividual rdf:resource=".../TestCase-3AWebOnt-2DThing-2D005" />
<owl:assertionProperty rdf:resource="&test;semantics" />
<owl:targetIndividual rdf:resource="&test;DIRECT" />
```
i.e. the catalog declares `test:semantics = RDF-BASED` and explicitly
DENIES `test:semantics = DIRECT` for this TestCase — an OWL Full
domain-size/comprehension test ("owl:Thing's own extension may not be a
singleton"), not a Direct-Semantics DL test, despite also carrying
`test:species DL` alongside `FULL` (species and semantics are
orthogonal facets in this catalog — species says which syntactic
profile the document parses as, semantics says which model theory the
inconsistency claim is made under).

Census (2026-07-17 sweep, all 128 `InconsistencyTest` cases in
`type-inconsistency.rdf`, script-verified): 127 carry BOTH
`test:semantics DIRECT` and `RDF-BASED`; exactly 1 —
`WebOnt-Thing-005` — carries `RDF-BASED` alone (and is the only one
with a semantics-`NegativePropertyAssertion`). Not a systemic issue
elsewhere in this catalog — a single named case.

`bin/owl-runner/owl_runner.ml`'s `run_inconsistency_test` (both RL and
DL regime — this catalog is always run `--regime dl` per
`generate-report.sh`) implements Direct Semantics only (`RL closure ->
Tableau.Refute -> RL` model theory; no RDF-Based domain-size reasoning
over `owl:Thing`'s own extension), and — before this fix — never
consulted `test:semantics` at all for `InconsistencyTest` scoring
(unlike `run_negative_entailment`, which already gates its closure mode
on `owl_semantics_mode_for`). Scoring Thing-005 as a DL fail was
therefore a harness categorization bug: fixed by gating
`run_inconsistency_test` on `owl_semantics_mode_for info =
RDF_Graph_Executable.owl_semantics_rdf_based` and returning a new
`Skip_semantics_rdf_based_only` outcome, counted outside the pass/fail
denominator with its own labelled reason line — same pattern as the
pre-existing `Skip_functional_syntax_only`. RDF-Based (OWL Full)
domain-size/comprehension reasoning remains a genuine, undispatched
engine gap; the fix is scope correction, not new capability — if the
engine later grows RDF-Based semantics support, Thing-005 is the test
to re-enable it against.

Scores (`bin/linux-x86_64/owl_runner`, this worktree, 2026-07-17):
- tinc before: 124 pass, 4 fail (out of 128), 0 skipped.
- tinc after: 124 pass, 3 fail (out of 127 scored), 1 skipped
  (semantics-scope: RDF-Based only) — flip: `WebOnt-Thing-005`
  `FAIL/unexpected-consistency` -> `SKIP/semantics-rdf-based-only`; all
  other 127 verdicts unchanged.
- `type-consistency.rdf --regime dl` (tcon, unaffected by construction
  — the fix only touches `run_inconsistency_test`, tcon uses
  `run_consistency_test`): 352 pass, 0 fail (out of 352), zero
  unexpected-inconsistency — gate held.
- floor `rdf-turtle`: 313 pass, 0 fail (out of 313) — gate held.

### dl-502 nominal-DPLL wave (2026-07-17, #299/#209) — analysis-only; root cause re-diagnosed

🧭 **Decision for the next wave: dl-502 is blocked upstream of the
refuter, not inside it.** This wave set out to extend the
`Tableau.Refute` DPLL machinery with nominal identify-branching so the
refuter could search the ~2^9 boolean assignments of `WebOnt-
description-logic-502` ("the classic 3 SAT problem"). Investigation
found that no amount of search extension can flip this test today,
because the SAT instance is never loaded into the tableau. Landed as
analysis-only (no engine change) per the zero-movement-scaffold ban —
adding a nominal-branching tier that fires on zero currently-loadable
tests, and adds wall-clock on the DPLL hot path, would be scaffold.

**The fixture (worked on paper).** `TorF` is a class defined by TEN
`owl:oneOf` enumerations: `{T,F}` (with `T owl:differentFrom F`) and
`{plus_k, minus_k}` for k=1..9. Two `owl:oneOf` on one class force
their enumerations to denote the SAME set, so `{plus_k,minus_k} =
{T,F}`; with `T ≠ F` this is a 2-element set, hence `plus_k ≠ minus_k`
and each of `plus_k/minus_k` is `T` or `F` — the truth value of
boolean variable k (`plus_k = T` ⇔ var k true). Then `T` is asserted
`rdf:type` of 45 anonymous `owl:oneOf {la,lb,lc}` classes — each a
3-literal clause `T = la ∨ T = lb ∨ T = lc`, satisfied iff one literal
equals `T`. The 9-var/45-clause 3-SAT instance is UNSAT, so the
premise is inconsistent.

**Measured current behaviour (`bin/linux-x86_64/owl_runner
type-inconsistency.rdf --regime dl`, this worktree, 2026-07-17,
freshly rebuilt from source):** dl-502 = `FAIL/unexpected-
consistency`; tinc run completes in 46.26s with ZERO refuter cap-trip
/ `owl_closure_timeout` messages. The refuter reaches quiescence and
reports a model — it is NOT exhausting the ~5s / 20000-fuel budget.
This is the decisive datum: **dl-502 is not budget-limited.**

**Root cause (two layers, both verified by source inspection):**

1. `Tableau.fst:303` — `parse_class_expr` reads a class's enumeration
   via `find_first_object g s owl_oneOf`, i.e. only the FIRST
   `owl:oneOf`. `TorF`'s other nine enumerations are dropped. And no
   individual is asserted `rdf:type TorF`, so even the first
   enumeration is inert.
2. `OWL.Closure.fst` has NO `owl:oneOf` rule at all (grep: zero
   matches). The RL closure never materialises the set-equality
   between two enumerations of one class.

Consequently the `{plus_k,minus_k} = {T,F}` variable constraints and
the `plus_k ≠ minus_k` distinctness never reach the tableau. `T`'s 45
clause-labels reference `plus_*/minus_*` individuals that carry no
other constraint, so `T` is freely identifiable with any of them → a
model always exists → correct-given-what-was-loaded "consistent"
verdict → InconsistencyTest FAIL. The 3-SAT structure is invisible to
any search that operates on the loaded state.

**Design for the flip (future wave — three parts, in order):**

- **F1 — multiple-`owl:oneOf` set-equality materialisation** (the
  blocker; a loader/closure change, foundational). For a class C with
  ≥2 `owl:oneOf` enumerations L1, L2: `CEXT(C) = set(L1) = set(L2)`,
  so soundly inject, for each `m ∈ L2`, `m rdf:type oneOf(L1)` (and
  symmetrically) — fully general, no cardinality needed. ⚠️
  Soundness-subtle addendum: the `plus_k ≠ minus_k` distinctness that
  makes each pair a genuine boolean is a CARDINALITY consequence
  (`|{plus_k,minus_k}| = |{T,F}| = 2` because `T ≠ F`), NOT of the
  membership injection. Without it the search admits the degenerate
  `plus_k = minus_k = T` model in which every literal equals `T`, so
  every clause is trivially satisfied and the instance looks
  consistent — the refutation would be unsound-incomplete. F1 must
  emit the distinctness (from a 2-element base whose two members are
  provably distinct), which makes it a narrow, pattern-specific rule
  of exactly the kind CLAUDE.md's "known sound-but-narrow rewrites"
  section cautions about.
- **F2 — nominal identify-branching** in `Tableau.Refute` (the O-rule
  as a BRANCHING rule, not only the existing clash rule). Extend
  `find_identify_nodes` / a new `find_nominal_branch` to offer, for a
  node labelled `CE_OneOf members`, the identifications `i = m` for
  each `m ∈ members`; `identify_branch` already implements the
  AND-semantics (TClash iff every member's identification closes) and
  the threaded-budget measure. Model-theoretic soundness: `i ∈
  {m1..mn}` entails `i = mj` for some j in every model, so refuting
  every j refutes the branch. This piece is sound and self-contained
  but moves zero tests without F1, so it must NOT land alone.
- **F3 — DPLL convergence** on the loaded 9-var/45-clause instance
  within budget. Unit propagation (a `plus_k`/`minus_k` forced by a
  decided sibling) and clash-first pruning already exist for the union
  encoding (`find_union_nodes_scan`, section 8b) and would need the
  nominal analogue. ⚠️ Wall-clock risk: this is the tinc hot path
  (measured 46s for 128 tests); a nominal search that reaches the ~5s
  per-test cap on dl-502 (and its sibling dl-504) alone adds ~+11%,
  close to the +15% gate — F3 must be measured on the full manifest,
  not just dl-502, before landing.

**Gate evidence for this analysis-only landing (no engine change → all
gates hold by construction; measured on the fresh worktree binary):**
tinc 124 pass, 3 fail (out of 127), 1 skip — 46.26s; tcon 352 pass, 0
fail (out of 352), ZERO unexpected-inconsistency — 389.3s; floors
rdf-turtle 313/0, w3c_runner `--rdf12` 29/0.

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
