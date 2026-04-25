# 2026-04-25 — Agent Shin: paper-sparqldl-Q3 follow-up (P3 OWL DL)

## Status snapshot (start of session)

After Mem's commit `56175a5` (`tableau: complementOf via disjointWith bridge`)
and the Wave 14 rebuild + sweep at 2026-04-25T10:16Z, paper-sparqldl-Q3 still
fails with **0 rows** (expected 2: `:John`, `:person1`).

## The test

`third_party/testing/w3c/sparql/sparql11/entailment/paper-sparqldl-Q3.rq`:

```sparql
SELECT ?x
WHERE {
  ?x ex:hasPublication _:b0 .
  _:b0 rdf:type [
    owl:onProperty ex:publishedAt ;
    rdf:type owl:Restriction ;
    owl:someValuesFrom [
      rdf:type owl:Class ;
      owl:complementOf ex:Workshop ]
  ]
}
```

Two-level nested CE in the BGP:
* outer: a `Restriction` with `onProperty ex:publishedAt` and
  `someValuesFrom <inner>`;
* inner: an anonymous `owl:Class` with `owl:complementOf ex:Workshop`.

Data (`paper-sparqldl-data.ttl`):
* `:Conference owl:disjointWith :Workshop`
* `:ConferencePaper rdfs:subClassOf [ a owl:Restriction ;
    owl:onProperty :publishedAt ; owl:someValuesFrom :Conference ]`
* `:John :hasPublication :paper1` ; `:paper1 a :ConferencePaper`
* `:person1 :hasPublication :paper1`

## Required entailment chain (OWL-Direct)

1. From `:paper1 a :ConferencePaper` and the `subClassOf` axiom:
   `:paper1` belongs to the restriction
   `(publishedAt some Conference)`. So there exists a witness w with
   `:paper1 :publishedAt w` and `w a :Conference`.
2. `:Conference owl:disjointWith :Workshop` plus `w a :Conference` gives
   `w a (complementOf :Workshop)`. **(This is Mem's bridge.)**
3. `:paper1 :publishedAt w` and `w a (complementOf :Workshop)` therefore
   `:paper1 a (publishedAt some (complementOf :Workshop))`.
4. The query returns `?x` with `?x :hasPublication :paper1` — that's
   `:John` and `:person1`.

## What's actually happening

### Where Mem's bridge lives

`formal/fstar/Tableau.fst:475-494` — inside `is_member`, in the
`CE_ComplementOf c` arm. When `c = CE_Named c_iri` and the graph
contains `c_iri owl:disjointWith d_iri` (or symmetric) plus
`i rdf:type d_iri`, return `Some true`. Helpers
`any_disjoint_witness_in` and `any_disjoint_witness_sym` plus
`has_disjoint_witness` at lines 374-403.

### Why the bridge is necessary but not sufficient

The bridge fires on `is_member g w (CE_ComplementOf (CE_Named :Workshop))`
when given a concrete witness `w` already typed `:Conference`. But
**there is no such `w` in the data**: the chain `:paper1 a
:ConferencePaper -> (publishedAt some :Conference)` is purely
schema-driven; no concrete `:publishedAt` triple exists for `:paper1`.

So `is_member` on `:paper1` for `(publishedAt some (complementOf
:Workshop))` walks `find_objects g :paper1 :publishedAt` (an empty
list — there's no asserted `:publishedAt` edge in the data) and
returns `Some false` / `None` from the existential.

**Mem's bridge doesn't help unless step 1 of the chain has already
materialised a concrete witness** — and it hasn't.

### What materialises witnesses today

I checked `RDF.Graph.Executable.fst` for the closure rules. The
canonical-bnode materialisation creates `_:rSVF(:p,:B)` triples for
named-class restriction fillers and types instances of named
restriction-equivalent classes — but it does **not** synthesise
`:publishedAt` edges from `(publishedAt some :Conference)` to a
fresh witness. That's existential reasoning proper, which the
project explicitly does not do (project deliberately avoids
synthesising fresh OWL individuals — too easy to lose soundness).

The earlier commit `92a9ee1` ("owl-tableau: existential witness
phase 1") was Phase 1 of this work; it added scaffolding but
Phase 1 alone does not synthesise the edge.

### The query rewriter angle

`OWL.QueryRewrite.fst` rewrites the BGP. For the Q3 query it would
need to:

* Recognise the outer marker (Restriction with onProperty + svf
  pointing at a CE bnode) — yes, this is in
  `add_restriction_markers_acc` for nested fillers.
* Rewrite the outer restriction to `?x :publishedAt ?fresh .
  <expand inner CE at ?fresh>`.
* Recognise that the inner CE is a `complementOf` named class —
  the rewriter does **not** currently handle complementOf. Grep
  shows `complementOf` appears only in Tableau.fst and in
  `RDF.Graph.Executable` (closure-side disjointness reasoning).

So even with Mem's bridge, the BGP does not get rewritten into
something that can match. The test depends on **two** missing
pieces:

* **(A)** The closure (or query-time materialisation) needs to
  realise `:paper1 :publishedAt _:w` and `_:w a :Conference` from
  `:ConferencePaper rdfs:subClassOf (publishedAt some :Conference)`
  plus `:paper1 a :ConferencePaper` — i.e., existential
  instantiation. Without it, no candidate witness exists for the
  query.
* **(B)** The query rewriter needs to handle a `complementOf`
  inner CE, expanding to a class-membership check that hits Mem's
  bridge (`?w a ?d . ?d owl:disjointWith :Workshop` style) — or
  the closure needs to materialise `_:w a (complementOf :Workshop)`
  via a complementary disjointness rule.

## Diagnosis (root cause)

**Mem's bridge is correct in isolation but isolated from the test.**
The blocker is that the entailment chain Q3 demands has **no
existing path to a concrete witness in the materialised graph**.
The bridge would save us if a witness existed and we needed the
last step (witness ∈ complementOf Workshop). It doesn't, so the
bridge never gets called for any individual Q3 cares about.

This is **NOT a small fix**. Adding existential instantiation
(witness synthesis) is a substantial OWL-DL piece — multiple new
F\* lemmas, possibly a new closure rule, and careful soundness
arguments about Skolem/canonical witness interaction with the
existing canonical-bnode machinery (`owl_rule_cls_svf2_qualified`).
That's parent4 / parent7 territory in some sense, but neither of
those is currently dispatching this exact case.

A **partial alternative** that could work without true witness
synthesis:

* Handle the Q3 query shape entirely in the query rewriter:
  rewrite `?x :hasPublication ?p . ?p a (publishedAt some
  (complementOf C))` to:
  * `?x :hasPublication ?p .`
  * `?p a ?cls . ?cls rdfs:subClassOf? ?r .`
  * `?r a owl:Restriction ; owl:onProperty :publishedAt ;
     owl:someValuesFrom ?d .`
  * `?d owl:disjointWith C` (or symmetric).

  This pushes Mem's bridge logic up to the BGP layer. Soundness
  is the same one-direction monotonic rule; doesn't synthesise
  any individuals; only emits triples we can actually match.

That rewriter approach is the cleanest path forward and matches
the `feedback_disjunction_in_rewriter` memory: complementOf is a
disjunctive construct, so it belongs in the rewriter side, not
the tableau side.

## Decision

**Stop here. Write the diagnosis. Do not push a half-fix.**

Reasons:
1. Mem's bridge as committed is sound — keep it; it will apply
   the moment any witness becomes materialised.
2. The fix that would make Q3 pass is non-trivial and crosses
   module boundaries (closure ↔ tableau ↔ rewriter). A
   single-agent commit that tries to do all three risks
   breaking adjacent tests (simple1/2/4/5/6/7/8 all share the
   restriction-CE codepaths).
3. Per CLAUDE.md, "A clean diagnosis is more valuable than a
   half-broken fix."

## Recommended next-agent scope

* Pick option (rewriter-side) or (closure-side) — not both.
* Start with simple3 / simple7 / paper-Q3 as the candidate set;
  these all involve a restriction whose svf filler is a
  complementOf CE.
* Touch one of: `OWL.QueryRewrite.fst` OR
  `RDF.Graph.Executable.fst`'s closure rules — not both in one
  agent.
* New fuel target: ≤ 80 LoC F\*; isolated `make verify` for the
  touched module; full sweep run only after F\* clean.

## Files inspected

* `formal/fstar/Tableau.fst` (lines 67-71 — owl_disjointWith ;
  368-403 — bridge helpers; 442-494 — is_member arms; 705-735
  — owl_tableau_entails entry).
* `formal/fstar/OWL.QueryRewrite.fst` (lines 110-167 — predicate
  vocab; 530-768 — marker discovery; doesn't recognise
  complementOf).
* `formal/fstar/OWL.QueryEval.fst` (whole file — pure wiring).
* `third_party/testing/w3c/sparql/sparql11/entailment/paper-sparqldl-Q3.{rq,srx}`
  and `paper-sparqldl-data.ttl`.
