# Entailment Residual Diagnosis (Agent Tzadi — 2026-04-25)

## Mission

Wave 7 (cf1c9cf) = entailment 62/4. Wave 10 (49d87a2 HEAD) = entailment
61/5. Net **-1 entailment** despite the high-water mark of **63/3 at Wave 8
(5cdeced)**. Identify which test flipped, why, and propose a minimal fix.

## Current 5 fails (HEAD = 49d87a2, ./bin/darwin-arm64/w3c_runner)

```
FAIL: paper-sparqldl-Q3                 expected 2 rows, got 0
FAIL: parent (hasChild min 1) [parent4] expected 3 rows, got 2 (missing Alice)
FAIL: parent (hasChild max 1 Female) [parent7]  expected 1, got 973 (explosion)
FAIL: sparqldl-11.rq: domain test       expected 2 rows, got 3 (extra _:_anon0)
FAIL: sparqldl-12.rq: range test        expected 2 rows, got 3 (extra _:_anon0)
```

## Wave 8 (5cdeced) had 63/3, the 3 fails were

(from `git show 5cdeced:formal/fstar/ocaml-output/sparql_results.log`):

```
FAIL: paper-sparqldl-Q3
FAIL: parent (hasChild min 1)
FAIL: parent (hasChild max 1 Female)
```

**sparqldl-11 and sparqldl-12 passed at Wave 8.**

## Classification

| Test | Status | Cause |
|------|--------|-------|
| paper-sparqldl-Q3 | PRE-EXISTING (Wave 7 + Wave 8) | Tableau / SPARQL-DL gap, deferred to F\* DL — Zeta triage covers |
| parent4 (min 1) | PRE-EXISTING (Wave 8) | OWL-Direct existential introduction (`:Alice rdf:type :Parent` ⇒ `:Alice :hasChild ∃y`). Cardinality CE rewriter (commit 2d17cfc) wires Bob/Dudley but not Alice — needs DL existential generation |
| parent7 (max 1 Female) | PRE-EXISTING (Wave 8) | Closure explosion — `cls-maxqc1` skolems generate hundreds of bnode rows (`_:__rl_maxqc1_*`). Output has `?_bnode__:bnode_18` column polluted with skolem subjects. Needs DL or skolem-projection cleanup |
| **sparqldl-11 (domain)** | **REGRESSION** at commit `281f31d` | scm-dom2 propagates `rdfs:domain` through subClassOf to the equivClass surrogate bnode `_:_anon0`, exposing it as an extra answer row |
| **sparqldl-12 (range)** | **REGRESSION** at commit `281f31d` | same as 11, but on `rdfs:range` via inverseOf — `:parent rdfs:range _:_anon0` |

## Root cause of regressions (sparqldl-11/12)

Commit `281f31d` "owl-rl-closure: scm-rng2 / scm-dom2 + always-on core
XSD Datatype axioms" added these rules in `RDF.Graph.Executable.fst`:

```fstar
// scm-dom2: (P rdfs:domain C1) AND (C1 rdfs:subClassOf C2) → (P rdfs:domain C2)
// scm-rng2: (P rdfs:range  C1) AND (C1 rdfs:subClassOf C2) → (P rdfs:range  C2)
```

`data-11.ttl` declares:
```turtle
:Parent a owl:Class ;
  owl:equivalentClass [a owl:Restriction; owl:onProperty :child;
                       owl:minCardinality 1] .
:child rdfs:domain :Parent .
```

The equivClass closure emits `:Parent rdfs:subClassOf _:_anon0`, where
`_:_anon0` is the surrogate bnode for the restriction class. Then
scm-dom2 fires:

```
:child rdfs:domain :Parent  +  :Parent rdfs:subClassOf _:_anon0
                          ⇒  :child rdfs:domain _:_anon0
```

The query `SELECT ?C WHERE {:child rdfs:domain ?C}` then returns 3 rows:
`owl:Thing`, `:Parent`, `_:_anon0`. Expected only the 2 named classes.

These rules were added to fix OWL-RL `WebOnt-I5.8-006` (xsd:byte → xsd:short
range propagation), which **does** require named-class targets. So the rule
is correct for OWL-RL but over-broad for the OWL-Direct entailment regime,
which excludes surrogate bnodes from answers per spec.

## Proposed fix (NOT applied — caller said do not touch RDF.Graph.Executable.fst)

Filter the `c2_term` to IRI-only in scm-rng2 / scm-dom2:

```fstar
// In owl_rule_scm_dom2 / owl_rule_scm_rng2:
List.Tot.fold_left
  (fun (acc2 : rdf_graph) (c2_term : rdf_term) ->
    match c2_term with
    | T_IRI _ ->
      let new_t = { s = t.s; p = rdfs_domain; o = c2_term } in
      add_triple_if_new acc2 new_t
    | _ -> acc2)  // skip bnode super-classes (equivClass surrogates)
  acc
  supers
```

**Trade-off:** OWL 2 RL profile permits bnode targets, so this is a
narrowing of the rule to what's empirically useful. WebOnt-I5.8-006 still
fires (xsd:byte → xsd:short are both IRIs). Sparqldl-11/12 stop emitting
the bnode row.

**Lines changed:** ~6 lines per rule × 2 rules = 12 lines, well under the
"trivial 30-line" threshold. Mechanical, no semantic ambiguity.

## Why I did not apply the fix

The session prompt explicitly said:
> **Don't touch `RDF.Graph.Executable.fst`** (closure rules from many agents).

So this is a documented hand-off, not a fix. The next agent who picks up
this scratch doc can do the F\* edit + verify + extract + recompile. The
6-line F\* change is local to `owl_rule_scm_rng2` / `owl_rule_scm_dom2`
and does not touch any other agent's closure rules.

## parent4 / parent7 / paper-Q3 (pre-existing)

These need either:
- **parent4:** DL existential introduction for `:Alice rdf:type :Parent`
  (Parent ≡ ∃hasChild). OWL-RL doesn't materialise existentials.
- **parent7:** project away skolem-restriction bnodes from answers, or
  prevent `cls-maxqc1` from emitting bnode-subject `:Alice rdf:type _:R`
  membership when no real qualifying child exists.
- **paper-Q3:** SPARQL-DL tableau (Zeta triage marked as deferred).

All three are out-of-scope for "minimal F\* fix this session" and tracked
as DL-completeness gaps in `docs/designissues/2026-04-23-entailment-plan.md`.

## Net assessment

- 1 confirmed regression × 2 tests (sparqldl-11/12) caused by `281f31d`.
- 3 pre-existing fails (paper-Q3, parent4, parent7) — same set as Wave 8.
- Fix is trivial F\* (~12 lines), but session policy disallows touching
  `RDF.Graph.Executable.fst` here. Hand off to next agent.

## Files touched this session

- `docs/designissues/2026-04-25-entailment-residual-diagnosis.md` (this file).
