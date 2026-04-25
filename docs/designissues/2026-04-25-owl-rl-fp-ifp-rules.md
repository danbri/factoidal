# OWL-RL closure: prp-fp + prp-ifp (FunctionalProperty / InverseFunctionalProperty)

**Date:** 2026-04-25
**Agent:** Tsade (P2 — DL informant feature F4)
**Triage origin:** `docs/designissues/2026-04-25-owl-dl-informant-corpus.md`
(Samekh2 — commits `918afd0` + `5eb3a3f`)

## Goal

Add OWL 2 RL/RDF table 5 closure rules for `owl:FunctionalProperty`
(prp-fp) and `owl:InverseFunctionalProperty` (prp-ifp) so that
sameAs identification fires on functionally-typed properties.

OWL 2 RL/RDF rules:

* **prp-fp** — `(P rdf:type owl:FunctionalProperty) ∧ (x P y) ∧ (x P z) ∧ y≠z
  ⇒ (y owl:sameAs z)`. Two values for the same subject under a functional
  property must be equal.
* **prp-ifp** — `(P rdf:type owl:InverseFunctionalProperty) ∧ (x P z) ∧ (y P z) ∧ x≠y
  ⇒ (x owl:sameAs y)`. Two subjects mapping to the same value under an
  inverse-functional property must be equal.

## State before this work

* `owl_InverseFunctionalProperty` IRI was already declared at line 1236 of
  `formal/fstar/RDF.Graph.Executable.fst`.
* `owl_rule_inverse_functional` (prp-ifp) was already implemented at line 1665
  and wired into `owl_rl_closure_step` at line 2688 (variable `g12`).
* `owl_FunctionalProperty` IRI was **not** declared.
* No prp-fp rule existed.
* The header rule list (around line 1210) names prp-ifp but **not** prp-fp,
  and the "missing" comment at line 1222 explicitly flags
  `owl:FunctionalProperty` as unimplemented.

So this work amounts to: add the FP IRI, add `owl_rule_functional`,
wire it next to the existing IFP step, and update the header comment.

## Changes

1. **`formal/fstar/RDF.Graph.Executable.fst`** — add `owl_FunctionalProperty`
   IRI binding adjacent to `owl_InverseFunctionalProperty`.
2. **Same file** — add `owl_rule_functional` immediately before
   `owl_rule_inverse_functional` (mirror of the IFP rule but iterating
   `find_objects g t1.s t1.p` instead of `find_subjects g t1.p t1.o`,
   and emitting `(y sameAs z)` instead of `(x sameAs z)`).
3. **Same file** — call the new rule in `owl_rl_closure_step` between
   `g11` (sameAs_replace_predicate) and `g12` (inverse_functional).
4. **Header comment** — list prp-fp alongside prp-ifp; remove
   `owl:FunctionalProperty` from the "still missing" list.

## Implementation notes

The IFP rule already:

* Tail-recursive folds (`List.Tot.fold_left`).
* Skips `subject_eq z t1.s` self-edges (reflexivity covers that).
* Uses `add_triple_if_new` so the fixpoint terminates.

The FP rule mirrors that exactly. Substitutions:

| IFP                                | FP                                  |
| ---                                | ---                                 |
| `owl_InverseFunctionalProperty`    | `owl_FunctionalProperty`            |
| `find_subjects g t1.p t1.o`        | `find_objects g t1.s t1.p`          |
| iterate `z : subject`              | iterate `z : rdf_term`              |
| emit `(t1.s sameAs subject_to_term z)` | emit `(t1.o-as-subject sameAs z)` (only when t1.o is iri/bnode) |

Because objects can be literals and `owl:sameAs` is defined only on
named individuals (IRI/bnode), prp-fp must guard on `term_to_subject t1.o`.
If the object is a literal, no sameAs triple is emitted (consistent with
RL semantics: literal equality is by value, not by sameAs).

## Test deltas (expected)

Per Samekh2's F4 triage, prp-fp validates on:

* WebOnt-cardinality-003 / -004 (functional cardinality reasoning).
* WebOnt-FunctionalProperty-001 / -003.

`owl_rule_inverse_functional` was already in place, so prp-ifp itself
should not move scores; the gain is from prp-fp. After commit, run
`./w3c_runner -v owl-test` (or whichever suite name maps to the WebOnt
group) to confirm no regression on OWL-RL 13/30 and the new pass-ups.

## Hard limits respected

* ≤ 80 LoC F\* edit (actual: ~46 LoC of new code in
  `RDF.Graph.Executable.fst`: 1 IRI binding for
  `owl_FunctionalProperty`, 1 rule `owl_rule_functional`, 2-line
  pipeline wiring `g11a`, plus header-comment touch-ups).
* No `Tableau.fst`, `OWL.QueryRewrite.fst`, `Parquet.Footer.fst`,
  `SPARQL11.Algebra.fst` touched.
* No extract / compile attempted (Yod3 held the Parquet.Footer
  build lock; Pe2 had an in-flight `cls-maxqc1` edit in the same
  file but in a non-overlapping section near line 2018).
* No `--lax`. F\* verify of `RDF.Graph.Executable.fst` after the edits:
  `Verified module: RDF.Graph.Executable / All verification conditions
  discharged successfully` (`.claude-runs/tsade-fstar-verify-…log`).

## Where the changes landed

Concurrent commits caused the Tsade prp-fp edits and the Pe2 cls-maxqc1
edits to be staged together in the working tree at the same instant.
Pe2 ran `git add formal/fstar/RDF.Graph.Executable.fst` and committed
the merged file in commit **`b2e8c2a` ("owl-rl-closure: cls-maxqc1
cardinality-aware skolem suppression (parent7)")**. That commit's
`+91 / -2` line count covers BOTH features.

In that commit:

* Pe2's `count_p_successors_typed_c` helper + cls-maxqc1 cardinality
  guard (lines ~2017-2071).
* Tsade's `owl_FunctionalProperty` IRI (line 1241).
* Tsade's `owl_rule_functional` (lines 1667-1705).
* Tsade's pipeline wiring `g11a = owl_rule_functional g11` (line 2776).
* Tsade's header-comment update (lines 1210, 1222).

This document is the canonical traceability record for the Tsade-side
work; please cross-reference it from the F4 line in
`docs/designissues/2026-04-25-owl-dl-informant-corpus.md` when closing
out F4.

## Function names + line numbers (final)

* `owl_FunctionalProperty : wf_iri` — `RDF.Graph.Executable.fst:1241`.
* `owl_rule_functional : rdf_graph -> rdf_graph` — line `1673`
  (preceded by an 8-line OWL-2-RL rule comment at line `1667`).
* `let g11a = owl_rule_functional g11` — line `2776` of
  `owl_rl_closure_step`.
* Existing `owl_rule_inverse_functional` (prp-ifp, was already
  present) — line `1715` of the post-edit file.

## Expected OWL-RL test deltas

Per Samekh2 F4 triage:

* **WebOnt-FunctionalProperty-001 / -003** — premise of the form
  `(P a owl:FunctionalProperty) ∧ (x P y) ∧ (x P z)` and conclusion
  `(y owl:sameAs z)` (or a downstream consequence). prp-fp now
  emits the `sameAs` triple; eq-rep-* downstream rules should
  carry it through.
* **WebOnt-cardinality-003 / -004** — exercise functional cardinality
  reasoning where two-distinct-objects-under-functional → contradiction
  (or → identity). prp-fp + existing eq-rep should now resolve the
  positive entailments.
* **OWL-RL Group 13/30** — prp-fp is additive (only emits sameAs);
  no removals, no schema-level rewrites; existing 13/30 passes are
  preserved.

Confirmation pending an OWL-RL runner pass once the build lock clears.
