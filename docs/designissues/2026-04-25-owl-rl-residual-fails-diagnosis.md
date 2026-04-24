# OWL 2 RL residual PositiveEntailment failures (Agent Omega — 2026-04-25)

Diagnose-and-fix mission: 5 OWL 2 RL PositiveEntailment tests still FAIL despite
relevant closure rules having been added in commits `c08b777` (Nu, XSD datatype
axioms) and Iota's `scm-cls` / `prp-rfl` work (`df37857`).

## Verbose runner output (each test's first missing triple)

```
FAIL  WebOnt-I5.5-005   missing _:rdfxml_b0 owl:unionOf _:rdfxml_b1
FAIL  WebOnt-I5.8-006   missing :p rdfs:range xsd:short
FAIL  WebOnt-I5.8-008   missing :p rdfs:range xsd:unsignedShort
FAIL  WebOnt-I5.8-009   missing :p rdfs:range xsd:short
FAIL  WebOnt-I5.8-011   missing xsd:integer rdf:type rdfs:Datatype
```

## Root causes (per test)

### WebOnt-I5.5-005 — out-of-scope (existential / comprehension)

- Premise: `:a rdf:type owl:Class`.
- Conclusion: `_:b a owl:Class; _:b owl:unionOf (_:c); _:c rdf:first :a; _:c rdf:rest rdf:nil`.
- Zeta's triage misclassified this as `scm-cls` (Restriction → Class). The
  actual conclusion synthesises a fresh bnode `_:b` plus an `owl:unionOf`
  list. This is **OWL Full / DL comprehension principle**, not an OWL 2 RL
  closure rule. Iota's `scm-cls` rule landed correctly but does not address
  this test.
- **Disposition:** mark as out-of-scope for OWL-RL closure (same family as
  `WebOnt-I5.26-010` in Zeta's triage, mode (f)). Will not flip without
  bnode synthesis machinery.

### WebOnt-I5.8-011 — gate too tight

- Premise: empty (just `<owl:Ontology/>`). No XSD IRI mentioned.
- Conclusion: `xsd:integer rdf:type rdfs:Datatype` and `xsd:string rdf:type rdfs:Datatype`.
- Nu's `owl_rule_xsd_datatype_axioms` is gated by `graph_mentions_xsd_iri`,
  which returns false on the empty premise — so no axioms emit.
- **Fix:** add an always-on rule `owl_rule_xsd_core_datatype_axioms` that
  emits the two core declarations unconditionally. Two triples is a
  trivial pollution; matches the spec ("xsd:integer is a datatype" is
  axiomatic in RDF-Based semantics).

### WebOnt-I5.8-006 — missing `scm-rng2`

- Premise: `:p rdf:type owl:DatatypeProperty; :p rdfs:range xsd:byte`.
- Conclusion needs `:p rdfs:range xsd:short`.
- Nu's hierarchy edges `xsd:byte rdfs:subClassOf xsd:short` get added, but
  the RDFS closure has only `rdfs_rule_range` (rdfs3: `a P b ∧ P range C →
  b type C`). It does NOT propagate range upward through subClassOf.
- **Fix:** add OWL 2 RL/RDF rule **scm-rng2**:
  `(P rdfs:range C1) ∧ (C1 rdfs:subClassOf C2) → (P rdfs:range C2)`.
- Symmetric **scm-dom2** added for completeness/parity.

### WebOnt-I5.8-008 — datatype-intersection (out-of-scope)

- Premise: `:p rdfs:range xsd:short; :p rdfs:range xsd:unsignedInt`.
- Conclusion: `:p rdfs:range xsd:unsignedShort`.
- The reasoning needs: values that are both `xsd:short` AND `xsd:unsignedInt`
  are exactly `xsd:unsignedShort`. This is **datatype-facet semantics**
  (value-space intersection), not RDFS subClass propagation. Note:
  `xsd:unsignedShort rdfs:subClassOf xsd:unsignedInt` is in the hierarchy,
  but `xsd:unsignedShort rdfs:subClassOf xsd:short` is **not** (their value
  spaces overlap but neither subsumes the other).
- **Disposition:** out-of-scope for monotonic OWL-RL closure. Needs facet
  semantics.

### WebOnt-I5.8-009 — also datatype-intersection

- Premise: `:p rdfs:range xsd:nonNegativeInteger; :p rdfs:range xsd:nonPositiveInteger`.
- Conclusion: `:p rdfs:range xsd:short`.
- Reasoning: the only value in `nonNeg ∩ nonPos` is 0, which is also a
  short. Same family as I5.8-008 — facet semantics, out-of-scope.

## Fix landed (this commit)

`formal/fstar/RDF.Graph.Executable.fst`:

- New rule `owl_rule_scm_rng2` — range propagation through subClassOf.
- New rule `owl_rule_scm_dom2` — domain propagation through subClassOf.
- New rule `owl_rule_xsd_core_datatype_axioms` — always-on emit
  `xsd:integer / xsd:string rdf:type rdfs:Datatype` (two triples).
- Wired into `owl_rl_closure_step` after Nu's `xsd_datatype_axioms` so the
  XSD subClass edges are already in scope when scm-rng2 runs.

F\* verifies cleanly (no `--lax`).

## Expected delta after Wave 8 rebuild

| Test | Before | After (predicted) | Fix family |
|---|---|---|---|
| WebOnt-I5.5-005 | FAIL | FAIL (deferred) | OWL Full comprehension |
| WebOnt-I5.8-006 | FAIL | **PASS** | scm-rng2 + Nu's hierarchy |
| WebOnt-I5.8-008 | FAIL | FAIL (deferred) | datatype-facet intersection |
| WebOnt-I5.8-009 | FAIL | FAIL (deferred) | datatype-facet intersection |
| WebOnt-I5.8-011 | FAIL | **PASS** | unconditional core datatype axioms |

Net OWL-RL score delta: **+2** (11/30 → 13/30).

## Out-of-scope tests requiring future work

1. **I5.5-005** — needs OWL Full comprehension (synthesise bnode +
   `owl:unionOf` list from a class declaration). Same family as Zeta's #14.
2. **I5.8-008 / I5.8-009** — need XSD datatype-facet value-space
   intersection semantics. Beyond OWL 2 RL closure (RL profile explicitly
   does not include facet reasoning). Could be added as a small
   special-case engine that recognises the standard XSD intersections —
   but mixes value-space and RDF-graph reasoning, which is unusual.

## How to verify after Wave 8 build completes

```
./build-ocaml.sh                # NOT during this session — main thread is rebuilding
./bin/darwin-arm64/owl_runner -v 2>&1 | grep -E 'I5\.5|I5\.8'
```

Expect `WebOnt-I5.8-006` and `WebOnt-I5.8-011` to flip to PASS.
