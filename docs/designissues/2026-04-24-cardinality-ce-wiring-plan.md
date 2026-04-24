# Cardinality CE Wiring Plan (Agent Eta — 2026-04-24)

## Goal

Extend `formal/fstar/OWL.QueryRewrite.fst` so that cardinality class
expressions in SPARQL queries are recognised and expanded, paralleling the
existing `someValuesFrom` / `allValuesFrom` / `unionOf` paths added by
Agents M / N / Gamma.

## Target Tests (entailment regime: OWL-Direct)

- `parent4.rq` — `[a owl:Restriction ; owl:onProperty :hasChild ; owl:minCardinality "1"]`
  expected: Alice, Bob, Dudley (the three individuals with ≥1 hasChild
  link in the closure — Alice via `:Parent` equiv `hasChild some Thing`).
- `parent6.rq` — `owl:minQualifiedCardinality "1" ; owl:onClass :Female`
  expected: Dudley (only individual whose hasChild is Female: Alice).
- `parent7.rq` — `owl:maxQualifiedCardinality "1" ; owl:onClass :Female`
  expected: Dudley (only DL-individual passing maxQ 1 Female).
- `parent8.rq` — `owl:qualifiedCardinality "1" ; owl:onClass :Female`
  expected: Dudley (exactly 1 Female child).

Note: parent6/7/8 are pretty closure-driven (DL semantics decide who
satisfies `max 1 Female` under open-world). These will likely still fail
even with the rewriter wired — full DL reasoning is out of scope for this
session. The rewriter side is the precondition.

## Approach (mirrors Gamma's CE_AllValuesFrom shape)

1. **Section 1.** Add IRI constants alongside `owl_someValuesFrom_iri`:
   `owl_minCardinality_iri`, `owl_maxCardinality_iri`,
   `owl_cardinality_iri` (the unqualified "cardinality"), plus the
   qualified variants `owl_minQualifiedCardinality_iri`,
   `owl_maxQualifiedCardinality_iri`, `owl_qualifiedCardinality_iri`,
   and `owl_onClass_iri`.

2. **Section 7 (combinator type).** Extend `ce_combinator`:
   ```
   type ce_combinator =
     | CE_Intersect | CE_Union | CE_SomeValuesFrom | CE_AllValuesFrom
     | CE_MinCardinality
     | CE_MaxCardinality
     | CE_ExactCardinality
   ```
   Qualified variants (with `owl:onClass`) reuse the same combinator —
   the expansion code looks up onClass on demand.

3. **Section 7 (`combinator_of_pred`).** Recognise the new predicates
   so queries that mention them get the right combinator.

4. **Section 7 (marker discovery).** Extend
   `add_restriction_markers_acc` to also mark any bnode that is the
   subject of `owl:minCardinality`, `owl:maxCardinality`,
   `owl:qualifiedCardinality`, or their min/maxQualified variants.

5. **Section 8b (`expand_ce_subject`).** Add cases for the three new
   combinators:

   - **CE_MinCardinality N**:
     - N = 0: vacuously true. Emit `GP_Empty` (every subject matches).
       Subject filter via the residue.
     - N = 1: one anchor triple `subj :p ?_min1_<k>` (existential).
     - N = 2 or 3: chain of distinct fresh vars with FILTER (?a != ?b).
     - N ≥ 4: fall back to N=1 (existential), with a code comment that
       larger cardinality bounds need a different encoding (out of scope
       for this commit). Sound but over-approximates.

   - **CE_MaxCardinality N**:
     - N = 0: `FILTER NOT EXISTS { subj :p ?_max0_<k> }`. To stay
       compatible with the surrounding GP shape, anchor it on a trivial
       BGP that binds nothing (use `GP_Filter (E_NotExists ...) GP_Empty`).
     - N = 1: messy (FNE with 2 distinct vars). Try first; fall back to
       leaf if it doesn't verify.
     - N ≥ 2: not implemented; fall back to leaf.

   - **CE_ExactCardinality N**: compose min N AND max N. Use
     `join_ggps`.

   For each combinator, parse the cardinality value from the literal
   object via `parse_int_string (lit_lexical l)`. If parse fails or N
   is negative, fall back to leaf.

   For qualified variants (mind the on-class bnode), the filter on the
   chained var is `?fresh rdf:type onClass_iri` joined to the property
   triple. (For `parent6` style.)

6. **`is_nested_bookkeeping`.** Extend the marker-meta predicate set
   to strip `owl:minCardinality`, `owl:maxCardinality`,
   `owl:qualifiedCardinality`, the qualified variants, and
   `owl:onClass`.

7. **`tp_is_ce_marker_predicate`.** Add the new cardinality predicates
   so `ggp_has_ce_marker` flags these queries (so `sm_distinct = true`
   gets applied).

## Verification

`fstar.exe --include . --cache_dir .cache OWL.QueryRewrite.fst` (no
`--lax`). No extraction or compile in this session — main thread is
running extract.

## Scoping Notes

- F* edit only. No `RDF.Graph.Executable.fst` edits.
- Cap ≤150 new lines.
- Cap N ≤ 3 for `min`, N=0 for `max` cleanly. Larger cardinalities use
  an over-approximating fallback (sound for adding solutions; soundness
  documented inline).

## Deferred (out of scope)

- Full N-distinct-vars FILTER chains for arbitrary N.
- DL reasoning that decides parent6/7/8 outcomes (closure side).
- Cardinality CE as filler inside someValuesFrom (nested CE inside a
  cardinality CE — not seen in current tests).
