# M3 design: the query rung of e2e deep proofs

G3 milestone 3 (adoption doc § G3): prove that SPARQL ASK/SELECT
under the RDFS entailment regime returns the regime-defined answers
on the rho-df fragment, by evaluating over the closure. This document
scopes the theorem before any dispatch; M1 (rho-df completeness) is
the load-bearing prerequisite and is in flight.

## The reduction

SPARQL 1.1 Entailment Regimes defines RDFS-regime BGP matching as:
solution mappings μ over the BGP's variables such that the scoped
graph RDFS-entails μ(BGP), under the answer-restriction conditions
(C1: terms of μ come from the graph's vocabulary ∪ the query's
vocabulary, keeping answer sets finite; C2: bnode handling per the
regime). The shipping engine instead computes: simple BGP matching
over `rdfs_closure g`.

The theorem factors into three layers, only the first of which is
new mathematics:

1. **Per-solution triple layer** (M1 delivers this): for fragment
   graphs and fragment-vocabulary μ(BGP),
   `μ(BGP) ⊆ rdfs_closure g  <==>  g rdfs-entails μ(BGP)`.
   Left-to-right is closure soundness (landed:
   `rdfs_closure_entails`); right-to-left is exactly M1's
   completeness restricted to ground instantiated patterns. The
   C1 vocabulary restriction is what makes the ⊆ test complete:
   every candidate μ draws its terms from vocabulary the closure
   already contains.
2. **BGP layer**: simple matching of a BGP over a FIXED graph is
   already the verified evaluator's core (the SPARQL algebra
   refinement work); the statement is that the evaluator's solution
   set over `rdfs_closure g` equals
   { μ | μ(BGP) ⊆ rdfs_closure g, μ minimal-scoped } — an existing
   style of theorem, not new machinery.
3. **Algebra layer**: ASK/SELECT are compositional over BGP results;
   the algebra above BGP matching is entailment-agnostic (regimes
   only redefine BGP matching — Entailment Regimes § 2). So the lift
   from layer 2 to full ASK/SELECT is by the existing algebra
   refinement lemmas, instantiated at the closure graph.

## Statement sketch

```
val rdfs_regime_answers_exact :
  g:rdf_graph -> q:bgp -> mu:solution ->
  Lemma
    (requires rho_df_graph g /\ bgp_fragment_scoped q g /\
              answer_restriction_c1 mu g q /\
              <M2's separator-freeness, inherited from M1's statement>)
    (ensures  bgp_matches (rdfs_closure g) q mu <==>
              rdfs_entails_instantiation g q mu)
```

then `ask_regime_exact` / `select_regime_exact` as corollaries via
the algebra layer.

## Scoping decisions (settled now, revisit only with cause)

- **Fragment-scoped queries only**: BGPs whose predicates/classes
  are in the rho-df fragment vocabulary. Queries outside the
  fragment get no claim (the suite's RIF/D-regime tests are out of
  scope for this theorem).
- **No property paths / OPTIONAL semantics changes**: regimes touch
  BGP matching only; everything above is inherited, and the theorem
  says so rather than reproving it.
- **Bnodes in answers**: follow the regime's C2 as the engine
  implements it today; the engine's behavior is the spec target
  (documented divergences, if the proof finds any, are findings —
  the registry discipline).
- **Hypotheses inheritance**: whatever hypotheses M1's final theorem
  carries (separator-freeness, seeded-axioms scoping) flow through
  verbatim. No silent strengthening.

## Sequencing

1. M1 lands (its exact hypotheses are inputs here).
2. Layer-2 lemma dispatched as its own agent task (recipe-shaped:
   existing evaluator refinement patterns).
3. Layer-3 corollaries + the composed theorem (likely one agent).
4. Registry rows + a generated-test pilot for the regime suite's
   RDFS tests (they already pass 70 of 70 — the theorem explains
   why, which is the entire point of G3).
