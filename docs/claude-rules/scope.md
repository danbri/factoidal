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
- RIF Core — the frame/BGP-shaped rule-body subset exercised by the
  4 vendored W3C RIF test cases (see below), verified in
  `RIF.Core.Syntax.fst` / `RIF.Core.Translation.fst` /
  `RIF.Core.Eval.fst` + `Parser.RIFXML.fst`, driven end-to-end by
  `bin/rif-runner/rif_runner.ml`.

## Out of scope — not planned

### RIF Core (Rule Interchange Format) — supported subset only

RIF Core is a full production-rule language; factoidal implements only
the fragment the 4 vendored W3C RIF test cases exercise: `Forall` /
`Frame` / `And` / `Implies` rule bodies translated to SPARQL BGPs
(`RIF.Core.Translation.fst`), forward-chaining fixpoint saturation
(`RIF.Core.Eval.fst`), and single `<Import>` companion-graph
resolution (with OWL-Direct closure applied first when the import's
own `<profile>` declares it — see `bin/rif-runner/rif_runner.ml`'s
`apply_import_closure`). General RIF-BLD (built-ins, list terms,
`External` function calls) and RIF-PRD (production rules, actions,
retraction) are **not implemented** and not planned.

**Concretely:** the 4 RIF tests under
`third_party/testing/w3c/sparql/sparql11/entailment/` (manifest IRIs
`:rif01 :rif03 :rif04 :rif06`, all tagged `sd:entailmentRegime ent:RIF`)
now PASS, measured via `bin/rif-runner/rif_runner.ml` (4 pass, 0 fail
out of 4, 2026-07-04):

- `:rif01` — RIF Logical Entailment (referencing RIF XML).
- `:rif03` — RIF Core WG tests: Frames.
- `:rif04` — RIF Core WG tests: Modeling Brain Anatomy (the imported
  ontology needs OWL-Direct closure — `owl_rl_closure_with_reflexivity`
  + `Tableau.tableau_materialise` — before the rule body's
  `rdf:type MaterialAnatomicalEntity` check matches individuals the
  ontology only asserts via `rdf:type Gyrus` + `rdfs:subClassOf`).
- `:rif06` — RIF Core WG tests: RDF Combination Blank Node.

Any RIF document whose rule bodies or imports fall outside the
frame/BGP + single-`<Import>` shape above is out of scope; a runner
encountering one should report an honest FAIL/SKIP with a diagnosis,
not force a PASS.

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
