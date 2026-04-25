# Pe3 — parent7 subject-side guard on restriction-membership rules (2026-04-25)

## Context

Zayin's diagnosis (`docs/designissues/2026-04-25-zayin-parent7-strip-not-effective.md`,
committed in `3b56c92`) confirmed that Tav2's projection-layer `strip_synthetic_bnode_vars`
patch is a verified no-op for parent7. The 311 spurious rows come from 102 distinct
`?parent` bindings, each one a vocabulary IRI / RDFS-axiom subject / self-emitted
`__rl_*` canonical that the cls-* qualified-cardinality rules accept as a "candidate
individual".

The four offending rules currently gate only on `is_schema_metapredicate edge.p`
(predicate side). A non-meta-predicate edge whose **subject** is a vocab IRI like
`rdfs:domain`, `xsd:byte`, or one of the rules' own emitted canonicals
(`_:__rl_maxqc1_<P>__on__<C>`) still fires the rule.

## Fix

Add a subject-side guard `edge_subject_is_safe : triple -> bool` that rejects:

1. `S_IRI i` where `i` is a schema meta-predicate IRI used as a subject (so the
   axiom triple `(rdfs:domain rdf:type rdf:Property)` won't seed a candidate
   individual).
2. `S_BNode b` where `b` starts with `__rl_` (break the self-feedback loop where
   the rule re-fires on its own canonicals across iteration).

Apply early in the fold body of all four rules:

- `owl_rule_cls_maxqc1` (~2487)
- `owl_rule_cls_exactqc1` (~2542)
- `owl_rule_cls_minc_qual1` (~2347)
- `owl_rule_cls_svf2_qualified` (~2291)

## Scope

- F\*-only change in `formal/fstar/RDF.Graph.Executable.fst`.
- ~30 LoC: one helper + 4 one-line guard insertions.
- No new `assume val`, no patch.
- Verification expected to pass cleanly (stricter precondition, monotonic).

## Expected result

- parent7 closure no longer materialises canonicals for vocab-IRI subjects or
  re-iterates on `__rl_*` self-bnodes.
- Sweep delta: +1 SPARQL → entailment 626/1/4 (total ~1657/1/2 modulo other
  in-flight changes). Already-correct parent2..parent6 / parent8..parent10 stay
  correct because:
  - Their candidate individuals are real test-graph IRIs (`:Bob`, `:Dudley`),
    not schema vocab IRIs, so the new guard never rejects them.
  - The rules already skipped meta-predicate edges; the new gate is strictly
    additional and only refines the subject filter.

## Soundness

The guarded edges are ones where the **subject** is itself a piece of the
schema vocabulary (used elsewhere as a meta-predicate) or a canonical bnode the
rule itself emitted. Treating those as "individuals" in OWL-RL was already
incorrect — they are not OWL-RL-allowed individuals, they are schema terms.
Skipping rule firings whose subject is in the schema vocabulary is therefore
not a loss: any genuine individual that is also schema vocab would already be
a punning case outside OWL 2 RL anyway.

## References

- `formal/fstar/RDF.Graph.Executable.fst:2043` — `is_schema_metapredicate`
- `formal/fstar/RDF.Graph.Executable.fst:2291` — `cls-svf2-qualified`
- `formal/fstar/RDF.Graph.Executable.fst:2347` — `cls-minc-qual1`
- `formal/fstar/RDF.Graph.Executable.fst:2487` — `cls-maxqc1`
- `formal/fstar/RDF.Graph.Executable.fst:2542` — `cls-exactqc1`
- `docs/designissues/2026-04-25-zayin-parent7-strip-not-effective.md`
  (Zayin diagnosis)
