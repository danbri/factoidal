# simple8: nested `someValuesFrom` chain — rewriter plan

Date: 2026-04-24
Agent: N
Branch: claude/main @ 83341cb

## Goal

Make `sparql/sparql11/entailment/simple8` pass. Query pattern:

```
?x a [
    a owl:Restriction ;
    owl:onProperty :p ;
    owl:someValuesFrom [
        a owl:Restriction ;
        owl:onProperty :p ;
        owl:someValuesFrom :B
    ]
]
```

Expected: `?x = :b`.

## Semantics (Datalog-safe)

`?x in ∃:p.∃:p.B` unfolds as: `?x :p ?y . ?y :p ?z . ?z a :B .`

Pure conjunctive BGP; no disjunction needed, so fits the rewriter
(per memory `feedback_disjunction_in_rewriter.md`).

## Approach

Extend `OWL.QueryRewrite.fst`:

- The current rewriter handles `_:r a owl:Restriction ; owl:onProperty p ; owl:someValuesFrom C` where `C` is a named class (`?x a [CE]` becomes `?x p ?g . ?g a C`).
- When `C` is itself a blank node tagged as another `owl:Restriction`, recurse: emit `?x p ?g . <recurse on filler bnode>`.
- Strip bookkeeping triples (`rdf:type owl:Restriction`, `owl:onProperty`, `owl:someValuesFrom`) for both inner and outer CE markers via `is_nested_bookkeeping`.

## Risks

- Marker detection may not recognise nested Restriction fillers as another CE.
- Gensym discipline for fresh variables.
- F* verification without `--lax`.

## Fallback

If rewriter edit proves too invasive in 60 min: write blocked-plan doc and
leave the closure untouched.
