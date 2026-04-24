# Closure rules: scm-eqc2 / scm-eqp2 / eq-diff-sym (2026-04-24)

**Agent Theta — single commit goal.** Implements three OWL 2 RL closure rules
identified by Zeta's triage (`docs/designissues/2026-04-24-owl-rl-posent-triage.md`)
as Tier 1 cheap wins.

## Rules

### scm-eqc2 — symmetric-subClassOf -> equivalentClass
`(C rdfs:subClassOf D) ∧ (D rdfs:subClassOf C) → (C owl:equivalentClass D)`.
Target test: `WebOnt-equivalentClass-003`.
Mirrors the *reverse* of existing `cls-eqc1` / `cls-eqc2` decomposition.

### scm-eqp2 — symmetric-subPropertyOf -> equivalentProperty
`(P rdfs:subPropertyOf Q) ∧ (Q rdfs:subPropertyOf P) → (P owl:equivalentProperty Q)`.
Target test: `WebOnt-equivalentProperty-003`.

### eq-diff-sym — differentFrom symmetry
`(a owl:differentFrom b) → (b owl:differentFrom a)`.
Target test: `WebOnt-differentFrom-001`.
Mirrors `owl_rule_sameAs_symmetry` exactly with `sameAs` replaced by `differentFrom`.

## Wiring

All three rules are added to `RDF.Graph.Executable.fst`, and registered in
`owl_rl_closure_step` after the existing rule list.

## Constraints

- Must verify under F\* without `--lax`.
- No edits to `OWL.QueryRewrite.fst` or `OWL.QueryEval.fst` (other agents).
- No `./build-ocaml.sh extract` or `compile` (main thread is rebuilding).
- Mind rule #12: no `*)` inside block comments.

## Expected delta

If all three land and verify, the F\* layer covers three more PositiveEntailment
tests. Actual PASS confirmation requires the main thread to extract and run
`owl_runner` — out of scope for this commit.
