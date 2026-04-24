# 2026-04-24 — Tier-3 XSD Datatype Hierarchy Axioms

Agent: Nu. Source: Zeta's triage `docs/designissues/2026-04-24-owl-rl-posent-triage.md`
(commit `272c81a`).

## Goal

Add an OWL-RL closure step `owl_rule_xsd_datatype_axioms` that materialises the
standard XSD numeric subtype hierarchy as `rdfs:subClassOf` edges plus an
`rdf:type rdfs:Datatype` declaration for each XSD numeric/derived type.

Triggered (gated) when the input graph mentions any IRI under the
`http://www.w3.org/2001/XMLSchema#` namespace, to avoid polluting graphs that
do not use XSD.

## Hierarchy Edges Emitted

```
xsd:byte                rdfs:subClassOf xsd:short
xsd:short               rdfs:subClassOf xsd:int
xsd:int                 rdfs:subClassOf xsd:long
xsd:long                rdfs:subClassOf xsd:integer
xsd:positiveInteger     rdfs:subClassOf xsd:nonNegativeInteger
xsd:unsignedByte        rdfs:subClassOf xsd:unsignedShort
xsd:unsignedShort       rdfs:subClassOf xsd:unsignedInt
xsd:unsignedInt         rdfs:subClassOf xsd:unsignedLong
xsd:unsignedLong        rdfs:subClassOf xsd:nonNegativeInteger
xsd:nonNegativeInteger  rdfs:subClassOf xsd:integer
xsd:negativeInteger     rdfs:subClassOf xsd:nonPositiveInteger
xsd:nonPositiveInteger  rdfs:subClassOf xsd:integer
xsd:integer             rdfs:subClassOf xsd:decimal
xsd:decimal             rdfs:subClassOf xsd:double
```

(`xsd:double rdfs:subClassOf xsd:Number` is omitted — OWL 2 RL covers numerics
via `rdfs:Datatype` instead. We follow the same convention.)

Plus, for every XSD numeric/derived type listed above (and `xsd:string`,
`xsd:boolean`, `xsd:double`, `xsd:decimal`, `xsd:integer`):
`<dt> rdf:type rdfs:Datatype .`

## Trigger

`graph_mentions_xsd_iri g` — true iff the graph contains any triple whose
subject, predicate or object IRI starts with the XSD namespace prefix
`http://www.w3.org/2001/XMLSchema#`. Implemented via `List.Tot.existsb`
over the graph plus a small `iri_in_xsd_ns` helper.

## Insertion Point

In `owl_rl_closure_step`, after Kappa's `owl_rule_named_sameAs_to_equivClass`
(currently `g24`). New step: `g25 = owl_rule_xsd_datatype_axioms g24`.

The rule is monotonic / additive (only adds triples) and idempotent
(`add_triple_if_new` guards), so the existing fixpoint check
(`graph_len g_rdfs = graph_len g`) terminates correctly.

## Tests Expected To Flip

Per Zeta's triage, this should unblock 4 OWL-RL posent tests, including:
- `WebOnt-I5.8-006`
- `WebOnt-I5.8-008`
- `WebOnt-I5.8-009`
- `WebOnt-I5.8-011`

## Constraints

- ≤100 new F* lines.
- F*-verifies without `--lax`.
- No edits outside `RDF.Graph.Executable.fst`.
- Do NOT run `build-ocaml.sh extract` / `compile` (main thread is rebuilding).
