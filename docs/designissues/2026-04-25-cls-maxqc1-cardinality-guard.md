# cls-maxqc1 cardinality-aware guard — parent7 (P2 / Pe2, 2026-04-25)

**Agent Pe2 — 2026-04-25 ~10:00 UTC.** Branch `claude/main`, HEAD `d512bc7`.
P2 follow-up to Lamed's plan (`docs/designissues/2026-04-25-owl-dl-tableau-paper-q3-parent-min-max-plan.md`).

## Problem

`owl_rule_cls_maxqc1` in `RDF.Graph.Executable.fst` (line 2018) currently
fires on every `(x P y) (y rdf:type C)` and emits `(x rdf:type
canonical_maxqc1(P,C))` plus the canonical's restriction shape. Because
RDFS closure types every individual under many superclasses (and rdfs
reflexivity / `owl:Thing` axioms add more), each `(x P y)` edge produces
K canonicals where K is the size of y's type set. For parent7 (16
individuals, deep type closure), this materialises ~973 spurious
`(?parent rdf:type _:rb)` triples — the SPARQL bnodes-as-existentials
rewrite then expands them all into `?parent` bindings, swamping the
expected single `:Dudley` answer.

## Fix (closure-side guard, ~30 LoC F*)

Before emitting `(x rdf:type canonical_maxqc1(P,C))`:

1. Count the P-successors of x whose `rdf:type` includes C in g.
2. Only emit if that count is `<= 1` (i.e., the actual data already
   satisfies max-1).

Soundness: max-1 says no x has ≥ 2 distinct P-C-typed successors. If
the data already shows x has 0 or 1 such successors, asserting `(x
∈ maxqc1(P,C))` is sound — the data is consistent with the restriction.
If x has ≥ 2 such successors, asserting `(x ∈ maxqc1(P,C))` would
either commit to a `sameAs` between them (correct DL semantics) or be
unsound; both cases are explicitly *not* what the SPARQL parent7 query
asks for. Suppressing the assertion is the conservative choice —
avoids the explosion, never claims max-1 membership for individuals
who provably have ≥ 2 distinct C-typed successors.

This mirrors the existing BNODE-POLLUTION GUARD pattern (parent9
regression, line 1269): a structural emit-suppression rather than
a tableau merge.

## Out of scope

- True equality decisions / sameAs-merge for ≥ 2 successors — needs
  Tableau.fst work (Lamed/Mem territory).
- `cls-exactqc1` parallel guard — `exactqc1` is = N which has the
  same surface but different semantics (also requires min N
  successors); deferred. For parent8 the existing rule still works
  because the test-case has count = 1 and no over-cardinality
  individuals.

## Hard limits

- ≤ 80 LoC F* edit (single helper + guard inside `owl_rule_cls_maxqc1`).
- F*-verify only `RDF.Graph.Executable.fst`; no extract / compile (Yod3 lock).
- Don't touch Tableau.fst, OWL.QueryRewrite.fst, Parquet.Footer.fst.
- Keep OWL-RL 13/30 baseline — risk surface limited because:
  - The guard is suppression-only (never adds new semantics).
  - parent2/3/4/5/6 use min-side / svf rules unchanged.
  - parent8 (`exactqc1`) uses a separate canonical predicate.
  - cls-maxc2 reads data-side `owl:maxCardinality` not our canonical.

## Commit

`owl-rl-closure: cls-maxqc1 cardinality-aware skolem suppression (parent7)`
