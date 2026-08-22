# formal/lean — Lean 4 tableau-soundness experiment

Owner decision 2026-08-22, tracked in
[#468](https://github.com/danbri/factoidal/issues/468): try Lean 4 as
the proof home for OWL tableau soundness before the F\* certificate
checker, because the proofs need global inductive invariants over
branching state — a poor fit for SMT-driven F\* automation (external
advisor caution, quoted in the issue).

**This directory does not ship.** Iron rules 1–2 (F\* is the source
of truth; code is extracted) apply to the shipping engine, which is
untouched. This is a proof laboratory; if the experiment concludes,
its production role would be a certificate CHECKER validating clash
certificates emitted by `formal/fstar/Tableau.Refute.fst` — an
independent gate, like the Jena differential column, never the engine.

## Contents

- `TableauSound/Semantics.lean` — model theory for the fragment:
  class expressions (atoms, Booleans, value restrictions, unqualified
  cardinality), interpretations, ABox satisfaction, consistency.
  Review object against OWL 2 Direct Semantics Table 5, same
  discipline as
  [docs/review-guide-w3c-semantics.md](../../docs/review-guide-w3c-semantics.md).
- `TableauSound/Calculus.lean` — the declarative clash calculus
  (`Derives` forward layer + `Refuted` clash layer: complement clash,
  owl:Nothing, min/max count clash, differentFrom-based max-card
  refutation, disjunction branching) and the soundness theorem
  `refuted_sound : Refuted A → no model of A`, by structural
  induction. A `Refuted` tree is exactly a clash certificate.

## Build

```
elan is the toolchain manager; lean-toolchain pins v4.33.1
cd formal/lean && lake build
```

No mathlib, no dependencies — core Lean only, builds in ~2 seconds.

Axiom audit (2026-08-22): `derives_sound` axiom-free;
`refuted_sound` / `refuted_not_consistent` use only `propext` +
`Quot.sound` (standard kernel axioms). Zero `sorry` — a `sorry` here
is the Lean spelling of a silent `assume val` (iron rule #3) and
fails the experiment's own bar.

## Next waves (in issue [#468](https://github.com/danbri/factoidal/issues/468))

1. ∃-witness rule (fresh individuals) — the freshness argument is the
   first proof F\*'s SMT automation would have fought hardest.
2. Role box: subPropertyOf closure, functional properties,
   transitive-role ∀⁺ push.
3. Qualified cardinality + the ≤-rule witness merge.
4. `Type`-valued certificate trees + a decidable checker with a
   correctness lemma, consuming serialized certificates from the F\*
   engine on real W3C inconsistency tests.
