# Project scope — what factoidal does and does not cover

Companion to `CLAUDE.md`. Lists features that are explicitly **not planned**
so future agents (and humans) don't burn cycles attempting them.

## In scope

- RDF 1.1 abstract syntax + all core serialisations (N-Triples, Turtle,
  N-Quads, TriG, RDF/XML, JSON-LD).
- SPARQL 1.1 Query, Update, Protocol, federated `SERVICE`.
- SPARQL 1.1 result formats (XML/SRX, JSON, CSV, TSV).
- RDF model theory / RDFS entailment (forward-chaining closure in F\*).
- OWL 2 RL entailment (rule-based subset, F\* closure rules).
- OWL DL via `OWL.QueryRewrite` rewriter for queryable fragments
  (`someValuesFrom`, `allValuesFrom`, `unionOf`, `intersectionOf`,
  cardinality CEs) — best-effort, not full DL classification.

## Out of scope — not planned

### RIF Core (Rule Interchange Format) — **NOT PLANNED**

RIF Core is a **separate production-rule language** layered on RDF, not
an entailment regime that fits into a verified SPARQL/OWL-RL closure
loop. Implementing it would require a complete second rule engine and
verification effort that is unrelated to the project's
verified-RDF/SPARQL goal.

**Concretely:** the 2 RIF tests under
`third_party/testing/w3c/sparql/sparql11/entailment/` are **permanent
SKIPs**. They are:

- `BindingsClause-Core` — RIF Core BLD subset entailment.
- `RIFCore-NoSubclassNorTyping-1` — RIF Core engine roundtrip.

These will never PASS in factoidal as long as the project scope remains
"verified RDF/SPARQL with built-in RDFS + OWL-RL entailment." If that
ever changes, this doc gets updated and the SKIPs become fails-to-fix.

The runner should report them as `skipped` (not `fail`) so the
entailment scoreboard reflects reality. Score lines that count RIF as
fails are misleading.

### Full OWL DL tableau classifier

The `Tableau.fst` module sketches stages (a)–(e) but a complete
DL tableau (skolemisation, disjunction blocking, complementOf
contrapositive, fresh-individual witnesses) is not the project goal.
Specific DL-only entailment tests (`paper-sparqldl-Q3`,
`WebOnt-I5.26-010`, the OWL 2 RL fp/ifp-differentFrom contrapositive
cases) are tracked in #58 and the OWL-RL triage doc but are not in the
current critical path.

### Non-monotonic / negation-as-failure inference

Tests requiring NaF (e.g. WebOnt fixed-point complementOf) are
monotonically unreachable by OWL-RL closure and out of scope for any
Datalog-style closure loop. Tracked in #58.

### XSD facet semantics beyond datatype subClass hierarchy

The XSD numeric subClass hierarchy (`xsd:byte ⊑ xsd:short ⊑ xsd:int ⊑
xsd:integer` etc.) is in scope as built-in axioms.
Facet-level reasoning (e.g. `xsd:nonNegativeInteger ∩
xsd:nonPositiveInteger ⊑ xsd:short`) is not.

## Update protocol

When a scope decision changes (in either direction), update this file
**in the same commit** that introduces the new feature or removes the
last code path supporting the dropped one. Do not let the doc drift.
