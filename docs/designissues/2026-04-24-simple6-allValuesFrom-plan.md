# simple6 allValuesFrom-union plan (Agent Gamma, 2026-04-24)

## Test

`third_party/testing/w3c/sparql/sparql11/entailment/simple6.rq`:

```sparql
SELECT ?x WHERE {
  ?x a [ a owl:Restriction ;
         owl:onProperty :p ;
         owl:allValuesFrom [ a owl:Class ; owl:unionOf ( :A :B :C ) ] ]
}
```

Data (simple.ttl): `:a :p :b`, `:b :p :c`, `:c :p :d`; `:a a :A,:B`; `:b a :B`; `:c a :C`; `:d a :A,:B,:C`.

Expected (simple6.srx): `:a`, `:b`, `:c`. Not `:d` (no outgoing `:p`).

## Semantics

`?x IN forall :p . (A U B U C)` means:
  - there exists some y with `?x :p y`, AND
  - every y with `?x :p y` has `y a Ci` for at least one i.

(The "at least one :p link" requirement excludes `:d` — OWL convention in this test suite.)

## Target SPARQL rewrite

```
?x :p ?_anchor_k .
FILTER NOT EXISTS {
  ?x :p ?_bad_k .
  FILTER NOT EXISTS { ?_bad_k a :A }
  FILTER NOT EXISTS { ?_bad_k a :B }
  FILTER NOT EXISTS { ?_bad_k a :C }
}
```

Anchor `?_anchor_k` guarantees >=1 link (excludes `:d`). The FNE chain asserts no y exists that is linked and in none of the union branches. For a 1-branch `allValuesFrom :C` (named-class filler), use a single inner FNE: `FILTER NOT EXISTS { ?_bad_k a :C }`.

## Algebra building blocks (all present in SPARQL11.Algebra.fst)

- `GP_Filter : expr -> group_graph_pattern -> group_graph_pattern`
- `E_NotExists : group_graph_pattern -> expr`
- `GP_BGP`, triple_pattern, fresh-var via `"_av_" ^ k` / `"_bad_" ^ k`

No new algebra constructs needed.

## Implementation plan for OWL.QueryRewrite.fst

1. Add IRI constant `owl_allValuesFrom_iri`.
2. Extend `ce_combinator` with `CE_AllValuesFrom`.
3. Extend `combinator_of_pred` to recognise `owl:allValuesFrom`.
4. Mirror the restriction-marker scanning (currently only `owl:someValuesFrom`): add a parallel `is_avf_subject` helper; in `restriction_has_nested_filler`, `ce_combinator_for_term`, `add_restriction_markers_acc`, and `add_inner_restrictions_acc`, also look up `owl:allValuesFrom`.
5. Extend `is_nested_bookkeeping` so that `owl:allValuesFrom` on a marker is also a meta-pred.
6. In `expand_ce_subject`, add a `CE_AllValuesFrom` branch that:
   - looks up `owl:onProperty` and `owl:allValuesFrom` for the restriction key
   - if filler is a `CE_Union`: extracts operands, builds the FNE-chain rewrite
   - else (leaf / CE_Intersect / CE_SomeValuesFrom): treats as single-branch filler; emits `?x :p ?anchor . FILTER NOT EXISTS { ?x :p ?bad . FILTER NOT EXISTS <filler-expanded-at-?bad> }` — uniform recursion using `expand_ce_subject` to get `filler_ggp_at_bad`.

## Soundness note

For `allValuesFrom` with a filler CE `F`, "every y with p-link is in F" is rewritten as "no y exists with p-link and not-in-F". For F a named class C, "not in C" = FNE `{ y a C }`. For F a unionOf(C1..Cn), "not in F" = "not in any Ci" = chain of FNE per branch. For F a more complex CE (intersectionOf, nested allValuesFrom, etc.) we would need to express "not (F)" by inverting the expansion, which is nontrivial. **Scope for this commit**: F is either a named class or a flat `owl:unionOf` of named classes (covers simple6). Other filler shapes fall back to leaf.

## Fresh var naming

- anchor = `_av_anchor_<k>`
- bad var = `_av_bad_<k>`

where `k` is the restriction bnode key; unique within one BGP.

## Risk & fallback

If the FNE construction turns out to trip F* totality / decreases (the expansion of the filler inside FILTER NOT EXISTS recurses via `expand_ce_subject`), we already have fuel. If more trouble: write `2026-04-24-simple6-allValuesFrom-blocked.md`.

Budget: 60 min wall.
