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
| **GRDDL** | 0/67 — not started | entire Stage 1 (local subset) queued; Stages 2-3 scoped in the 2026-07-08 doc | ✗ / ✗ |
| **JSON-LD 1.1** | toRdf 460/467; fromRdf 49/54 (finisher in flight) | **expand / compact / flatten / frame / html API suites NOT RUN — counted as failed until measured**; toRdf last 1+6; fromRdf last 5 | partial / ✓ (post 07) |
| **OWL 2** | RL-PE 28/2; EL/QL/DL catalogs partial; syntax-dl unscored | Tableau DL catalog wiring (in flight); remaining RL fails; syntax-dl checker; #262 sameAs perf blowup | closure ✓, tableau ✗ / page queued (#93) |
| **RDF 1.1** | 1031/0 | **runner-integrity failures**: ASK boolean unchecked; bnode matching is lenient, not graph isomorphism; value-equivalence gaps (lang-tag case, plain↔xsd:string); RDF/XML deep-nesting overflow (#279) | ✓ / ✓ |
| **RDFC-1.0** | 86/0 — complete | none on conformance; needs a perf row (HNDQ budget behavior) | ✓ / ✓ (post 08) |
| **RIF Core** | 34 pass, 4 fail, 12 skip | the 4 + the 12, each with a named reason or a fix | ✓ / ✓ (post 10) |
| **SHACL** | core 98/0; sparql-constraints 22/0 | verify both denominators against the FULL W3C suite manifest; implement any unrun sections | ✓ / ✓ (post 05) |
| **ShEx** (CG) | green at last full run | **no dashboard JSON row** (visibility failure); re-measure + row | ✓ / ✓ (post 06) |
| **SPARQL 1.1** | 631/0; regimes 70/70 | parser `--admit_smt_queries` 20 obligations (repair in flight, #91); Protocol/GSP **deprioritized per goal** (parked, not failed) | ✓ / ✓ |
| **VC 2.0 + Data Integrity** | 113/120 expected (context-walker in flight) | 1 corpus template artifact (documented); 6 filename-ambiguous skips; full W3C VC-DI proof-options conformance | ✓ (typed crypto) / ✓ (post 13) |

Parked by owner directive: **RDF 1.2 / RDF-star** (also blocks rml-star
— revisit as one design decision). **Protocols** (SPARQL Protocol,
Graph Store) — depth and perf come first.

Non-semweb engines (XML, XSLT, XPath, Schematron, JSON Schema, MathML,
XForms, TOAN) stay measured on the dashboard but are outside this
ledger's "full implementation" mandate.
