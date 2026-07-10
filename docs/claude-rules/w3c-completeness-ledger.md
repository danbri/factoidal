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
| **CSVW** (csv2rdf) | 146/270 | UAX-35 date/time `format` patterns; UAX-35 number `format` patterns; metadata discovery (Link header, `/.well-known/csvm`); `separator`/list values; `rowTitles`; 2 cross-table NegativeRdf | ✓ / ✓ (post 13) |
| **DID** (did:key) | 8/8 on stage-1 vectors | depth: suite is a sliver of DID Core (no did:web, no resolution metadata) — needs a real conformance target enumerated | ✓ / ✓ (post 23) |
| **GRDDL** | Stage 1 (local subset): 3 pass, 14 fail, 51 skip (out of 68) [2026-07-10] | pass = the 3 RDF/XML-source (rdfxbase) tests (grddlonrdf, grddlonrdf-xmlmediatype, rdfXMLDoc). Fails: **13 `fail-known-gap-xslt-nametest`** — the GRDDL stylesheets bind `html:`/`h:` prefixes and use prefixed XPath name tests against default-namespace (`xmlns=`) sources, but `XSLT.Transform.fst` lists "prefix-aware match patterns" as deliberately out of scope, so the selections return empty (dominant Stage-1 blocker; fix = namespace-URI-aware XPath name tests in the verified XSLT/XPath engine) — plus **1 `fail-graph-mismatch`** (grokSheet.xsl Gnumeric-spreadsheet transform, fidelity). Skips: **49 `skip-network`** (`NetworkedTest`) + **2 `skip-stage2-ns-or-profile-document`** (profile-document transformation). Stage 2 = namespace/profile-document paths + hCard-family (need a fetch hook, `jsonld_load_document` shape); Stage 3 = HTML tag-soup input. | ✗ / ✗ |
| **JSON-LD 1.1** | toRdf 460/467; fromRdf 49/54 (finisher in flight) | **expand / compact / flatten / frame / html API suites NOT RUN — counted as failed until measured**; toRdf last 1+6; fromRdf last 5 | partial / ✓ (post 07) |
| **OWL 2** | RL-PE 28/2; EL/QL/DL catalogs partial; syntax-dl unscored | Tableau DL catalog wiring (in flight); remaining RL fails; syntax-dl checker; #262 sameAs perf blowup | closure ✓, tableau ✗ / page queued (#93) |
| **RDF 1.1** | 1031/0 (strict) | runner-integrity fix landed: graph equality is now RDFC-1.0 canonicalization + byte-compare (F* `RDF.GraphIsomorphism`, not lenient bnode-collapse), with lang-tag-case value equivalence; score held at 1031/0 under the strict comparison (our parsers produce graphs bnode-isomorphic to the expected N-Triples/N-Quads), 0 canonicalization-budget fallbacks — so 1031 is now earned, not inflated. Remaining: RDF/XML deep-nesting overflow (#279) | ✓ / ✓ |
| **RDFC-1.0** | 86/0 — complete | none on conformance; needs a perf row (HNDQ budget behavior) | ✓ / ✓ (post 08) |
| **RIF Core** | 34 pass, 4 fail, 12 skip | the 4 + the 12, each with a named reason or a fix | ✓ / ✓ (post 10) |
| **SHACL** | core 98/0; sparql-constraints 22/0 | verify both denominators against the FULL W3C suite manifest; implement any unrun sections | ✓ / ✓ (post 05) |
| **ShEx** (CG) | green at last full run | **no dashboard JSON row** (visibility failure); re-measure + row | ✓ / ✓ (post 06) |
| **SPARQL 1.1** | 630/1; regimes 69/70 | 7 of the 8 strict-runner failures fixed in F* (task #100): **BNODE()/BNODE(str)** now per-solution + per-occurrence fresh (row+call-site seed via sha256, pure F*); **UUID()/STRUUID()** distinct per binding (same seed); **NOW()** returns a valid xsd:dateTime (boundary `fx_current_datetime` assume val, #287); the OWL cardinality/someValuesFrom rewrite's internal `?_sv_`/`?_mc_`/`?_mxqc1_` vars are stripped at the FINAL projection only (parent min-1, parent max-1 Female), keeping inner Select_All sub-select correlation intact; **RDF inference test (rdf01)** fixed via rdfD2 (predicate ⇒ rdf:Property) applied only under the ent:RDF regime. Remaining 1 fail: **RIF Brain Anatomy (rif04)** — the RIF Import(<import001.rdf> OWL-Direct) directive's declared entailment profile is not materialised (imports load as plain triples, so `g1/pcg0 rdf:type MaterialAnatomicalEntity` from rdfs:domain is never derived and the rule body never matches); needs import-profile-aware materialisation in the RIF pipeline, a distinct feature. 0 canonicalization-budget fallbacks. Also: parser `--admit_smt_queries` (#91); Protocol/GSP parked | ✓ / ✓ |
| **VC 2.0 + Data Integrity** | 113/120 expected (context-walker in flight) | 1 corpus template artifact (documented); 6 filename-ambiguous skips; full W3C VC-DI proof-options conformance | ✓ (typed crypto) / ✓ (post 13) |

Parked by owner directive: **RDF 1.2 / RDF-star** (also blocks rml-star
— revisit as one design decision). **Protocols** (SPARQL Protocol,
Graph Store) — depth and perf come first.

Non-semweb engines (XML, XSLT, XPath, Schematron, JSON Schema, MathML,
XForms, TOAN) stay measured on the dashboard but are outside this
ledger's "full implementation" mandate.
