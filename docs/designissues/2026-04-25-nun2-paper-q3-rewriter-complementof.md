# 2026-04-25 — Agent Nun2: paper-Q3 rewriter `complementOf` recognition

Agent scope: gap 2 of 3 from Shin's
[2026-04-25 paper-Q3 follow-up](2026-04-25-shin-paper-q3-followup.md).
The other two gaps (existential witness synthesis on the closure side,
and a `disjointWith`-derived `complementOf` rule on the closure side)
are out of scope here.

## Diagnosis

`paper-sparqldl-Q3.rq` contains the BGP

```sparql
?x ex:hasPublication _:b0 .
_:b0 rdf:type [
  owl:onProperty ex:publishedAt ;
  rdf:type owl:Restriction ;
  owl:someValuesFrom [
    rdf:type owl:Class ;
    owl:complementOf ex:Workshop ]
]
```

The outer restriction (an `owl:someValuesFrom` whose filler is a CE
bnode) IS classified by `find_markers` because
`restriction_has_nested_filler` returns true: the filler bnode is itself
a CE bnode (it is the subject of `owl:complementOf`, which the rewriter
must recognise as making it a class expression).

But:

* `restriction_has_nested_filler` only treats a filler bnode as
  "CE-qualified" if it is a flat marker (intersection / union) OR a
  restriction subject (`is_svf_subject` / `is_avf_subject`). A
  `complementOf` bnode is neither, so the filler is not a CE bnode —
  the outer restriction is therefore NOT marked as a top-level CE,
  the rewriter falls through to the leaf `_:b0 rdf:type _:r` form,
  and the closure has no canonical to bind it against.
* Even if the outer restriction WERE marked, `ce_combinator_for_term`
  has no `CE_ComplementOf` arm. `expand_ce_subject`, on encountering
  the inner bnode, would emit it as a leaf `?fresh rdf:type _:cn`
  triple, which binds nothing.

## Fix

Add a `CE_ComplementOf` combinator to `ce_combinator`.

Add a recogniser for the bnode shape `[a owl:Class ;
owl:complementOf <C>]`:

* `is_complementOf_subject : bgp -> string -> bool` — does the BGP
  have a triple `(k, owl:complementOf, _)`?
* `complementOf_target : bgp -> string -> option pattern_term` — the
  target class term.

Plug `is_complementOf_subject` into:

* `restriction_has_nested_filler`: a complementOf bnode is now a valid
  nested CE filler.
* `ce_combinator_for_term`: a complementOf bnode is a CE bnode of
  combinator `CE_ComplementOf`.

Add an arm to `expand_ce_subject` for `CE_ComplementOf`:

The OWL meaning of `?x rdf:type [owl:complementOf :C]` under the
disjointWith-bridge is "x is in some class that is disjoint with C".
But the cleanest sound-and-actually-binds rewrite is the
**disjointness-targeting shape**, which Shin's diagnosis recommends:

```sparql
{ ?x rdf:type ?d . ?d owl:disjointWith :C }
UNION
{ ?x rdf:type ?d . :C owl:disjointWith ?d }
```

Both branches are a class membership check that hits Mem's bridge
when paired with materialised `?x rdf:type ?d` triples. This is
the rewriter form of the same monotonic rule that lives in
`Tableau.fst`'s `has_disjoint_witness`.

Open issue (gap 1): for paper-Q3 specifically, the witness `w` for
`(publishedAt some ...)` is not materialised; even with this rewrite
the outer existential restriction has no candidate `w` for
`?x :publishedAt w` — that's the existential synthesis step, separate
agent. After gap 1 lands, this rewrite + Mem's bridge close the chain.

## Soundness

The disjointWith-bridge rewrite emits a UNION of two BGPs. Each BGP
asserts: `?x` has some `rdf:type ?d` such that `?d` and `:C` are
declared disjoint (in either direction). By the OWL semantics of
`owl:disjointWith` (a symmetric class-disjointness assertion), if
`?x rdf:type ?d` and `?d` is disjoint from `:C`, then `?x` is
provably NOT in `:C` — i.e., `?x rdf:type (complementOf :C)`.

This is one direction (sound, monotonic) — never produces a binding
that isn't entailed. It is incomplete: complementOf membership can
also be derived from explicit "not in C" assertions or from open-world
disjoint-classes axioms; we don't try those here.

## Discipline

Per `feedback_disjunction_in_rewriter.md` memory: complementOf is a
disjunctive construct; rewriting it as UNION is the right
F\*-first home. The Tableau-side `has_disjoint_witness` keeps its
role as the closure-side bridge for already-materialised individuals;
the rewriter side handles BGP-level pattern emission.

## Files touched

* `formal/fstar/OWL.QueryRewrite.fst` — adds:
  * `owl_complementOf_iri`
  * `is_complementOf_subject`, `complementOf_target`
  * `CE_ComplementOf` constructor
  * `restriction_has_nested_filler` clause
  * `ce_combinator_for_term` arm
  * `expand_ce_subject` arm (emits the disjointWith UNION shape)
  * `is_nested_bookkeeping` clause for stripping
    `(k, owl:complementOf, _)` and `(k, rdf:type, owl:Class)` for
    complementOf markers.

## Tests

Verification: `make verify-OWL.QueryRewrite` (or the module-scoped
verify). Sweep: paper-Q3 stays at 0 rows until gap 1 lands. No
regression on simple1..simple8, sparqldl-*, parent4/parent7.
