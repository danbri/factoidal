# Tav — parent7 over-count diagnosis (2026-04-25)

## Symptom

After Pe2's commit `b2e8c2a` (cls-maxqc1 cardinality-aware skolem suppression),
parent7 still FAILs but in a new way: 954 rows where 1 (Dudley) is expected.
The leaked bindings include rows like:

```
?_bnode__:bnode_18=<http://www.w3.org/2002/07/owl#Thing>,
?parent=_:__rl_maxqc1_<http://www.w3.org/2000/01/rdf-schema#subClassOf>__on__<http://www.w3.org/2002/07/owl#Class>
```

The skolem name `_:__rl_maxqc1_<P>__on__<C>` reveals the (P, C) the canonical
was emitted for. Here P = `rdfs:subClassOf` and C = `owl:Class` — schema
metavocabulary, not parent7's `:hasChild` / `:Female`.

## Root cause

`owl_rule_cls_maxqc1` (RDF.Graph.Executable.fst:2098) iterates over **every**
non-rdf:type, non-meta edge in g and emits a canonical maxqc1 restriction for
the (edge.p, type-of-edge.o) pair. The "non-meta" guard is:

```fstar
if edge.p = rdf_type || is_owl_metapredicate edge.p then acc
```

`is_owl_metapredicate` (line 1264) only excludes 4 IRIs:
`owl:sameAs`, `owl:inverseOf`, `owl:equivalentClass`, `owl:equivalentProperty`.

It does NOT exclude:

- `rdfs:subClassOf`, `rdfs:subPropertyOf`, `rdfs:domain`, `rdfs:range`
- `owl:onProperty`, `owl:onClass`
- `owl:maxQualifiedCardinality`, `owl:minQualifiedCardinality`,
  `owl:qualifiedCardinality`, `owl:cardinality`,
  `owl:maxCardinality`, `owl:minCardinality`
- `owl:someValuesFrom`, `owl:allValuesFrom`, `owl:hasValue`
- `owl:oneOf`, `owl:intersectionOf`, `owl:unionOf`, `owl:complementOf`
- `owl:disjointWith`, `owl:propertyChainAxiom`
- `owl:distinctMembers`, `owl:members`

After RDFS+OWL closure on `parent.ttl`, every named/anonymous class C carries
many `(C rdfs:subClassOf D)` triples, including reflexivity (C → C), transitive
chains, and (Restriction → owl:Class) via `scm_cls_restriction`. For each such
triple the rule treats `(C rdfs:subClassOf D)` as a "data edge" and asks:
"how many of C's `rdfs:subClassOf` successors are typed `<some class>`?"
For (C, T) pairs where exactly one successor is typed T, the count guard
**passes** (n = 1 ≤ 1) and a canonical
`_:__rl_maxqc1_<rdfs:subClassOf>__on__<T>` is materialised. This produces
hundreds of leaked canonicals, one per accidentally-singleton (C, T) pair.

Pe2's count guard (`n > 1 → suppress`) is correct but cannot save us when
the rule shouldn't fire on schema edges in the first place — singletons are
abundant in schema closure.

The same bug latently affects the other restriction-membership rules
(`cls-minc-qual1`, `cls-svf2-qualified`, `cls-minc1-bridge`, `cls-exactqc1`).
parent4 / parent5 / parent6 / parent8 happen not to trip it because their
queries don't constrain `owl:onClass` to a class that singleton-matches a
schema-edge target, but the over-count canonical bnodes ARE being emitted
into the closure (latent pollution). Fixing maxqc1 alone resolves parent7;
extending the same guard to the sibling rules is the right hygiene.

## Fix (F\*-only)

Introduce a wider predicate `is_schema_metapredicate` that also covers
RDFS schema vocabulary and OWL restriction/class-expression vocabulary
(the predicates listed above). Use it as the gate for `cls-maxqc1`,
`cls-exactqc1`, `cls-minc-qual1`, `cls-svf2-qualified`. Existing
`is_owl_metapredicate` keeps its narrower role (sameAs / equivalentClass /
inverseOf / equivalentProperty) where finer-grained skipping is wanted.

### Sketch

```fstar
let is_schema_metapredicate (p : wf_iri) : bool =
  is_owl_metapredicate p
  || p = rdfs_subClassOf || p = rdfs_subPropertyOf
  || p = rdfs_domain     || p = rdfs_range
  || p = owl_onProperty_iri || p = owl_onClass_iri
  || p = owl_someValuesFrom_iri || p = owl_allValuesFrom_iri
  || p = owl_hasValue_iri  // if defined
  || p = owl_minCardinality_iri
  || p = owl_maxCardinality_iri
  || p = owl_cardinality_iri
  || p = owl_minQualifiedCardinality_iri
  || p = owl_maxQualifiedCardinality_iri
  || p = owl_qualifiedCardinality_iri
  || p = owl_oneOf_iri || p = owl_intersectionOf_iri
  || p = owl_unionOf_iri || p = owl_complementOf_iri
  || p = owl_disjointWith_iri
  || p = owl_propertyChainAxiom
```

(check existing `let owl_*_iri` definitions; add any missing IRI constants.)

Replace gate at lines 2101 (cls-maxqc1), 2153 (cls-exactqc1), 1968
(cls-minc-qual1) etc. with `is_schema_metapredicate`. Pe2's count guard
stays — it remains the right thing for the >= 2 case among real data edges.

## Soundness

cls-maxqc1 (et al.) is intended to materialise restriction membership for
INDIVIDUAL data assertions like `(:Bob :hasChild :Charlie)`. Schema-vocab
predicates link classes/properties, not individuals; emitting
"Female has at most 1 rdfs:subClassOf-successor of type owl:Class" and
making `:Female` a member of that synthetic restriction is meaningless.
Restricting the rule to non-schema predicates is purely a domain
correction, not a semantic compromise.

## Acceptance check

1. F\* verifies (no `--lax`, no `--admit_smt_queries`) for
   RDF.Graph.Executable, OWL.QueryRewrite, Tableau.
2. After main thread re-extracts, sweep parent7 → PASS (1 row, Dudley);
   no `_:__rl_maxqc1_*` skolems leak into ?parent.
3. parent2..parent10 status unchanged (parent4..parent6, parent8..parent10
   already pass; parent7 newly passes).
4. scm-* tests unchanged.
