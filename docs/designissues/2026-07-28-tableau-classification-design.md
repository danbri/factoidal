# Tableau classification/refutation — target-test design map (2026-07-28)

Owner steer (2026-07-28, verbatim): "You've been doing tableau very very
slowly for weeks now. Just get it all done please." — the tableau program
(next-actions doc Groups H + J + the 2 DL98 inconsistency fails) is top
priority. This note maps each target test's premise/conclusion shape (read
from the fixtures, not test names) to the specific mechanism it needs, and
records the probe evidence that classified each test as BUDGET-shaped
(machinery already closes it, given wall clock) or RULE-shaped (a missing
derivation).

Probe method: single-test mini-catalogs (scratchpad tooling), run against
the committed `bin/linux-x86_64/owl_runner` with
`FACTOIDAL_OWL_REFUTE_CAP_SEC=120 FACTOIDAL_OWL_REFUTE_FUEL=2000000` — if a
test flips to PASS with only budget raised, no F\* rule is missing.

## Pipeline recap (what runs where)

DL-regime PE scoring (`bin/owl-runner/owl_runner.ml`
`run_positive_entailment`):
1. conclusion ⊆ DL closure (RL → `Tableau.tableau_materialise` → RL);
2. else PE-via-refutation: `Tableau_Refute.negation_goals` on the
   conclusion; every goal must refute via
   `Tableau_Refute.tableau_consistent (closure @ neg)` = `Some false`,
   under `with_refute_cap` (default 5s) and `refute_fuel` (default 20000);
3. else retry both with the witness-augmented closure.

Inconsistency scoring: `dl_refutes` = `tableau_consistent` over the RL-base
closure, same 5s cap.

## Per-test classification

### WebOnt-description-logic-201/-202/-206/-208/-661/-662 — DL98 ABox family

Conclusion: `rdf:type` assertions of ONE named individual in named classes
(8 conjuncts for 201). Premise: large TBox of `owl:equivalentClass`
definitions over complement/intersection/someValuesFrom + ABox.

- `negation_goals` already emits per-conjunct goals
  (`i rdf:type _:neg`, `_:neg owl:complementOf C`).
- `Tableau.Refute` already carries the machinery the family needs:
  contrapositive equivalence unfolding (section 7), union branching with
  DPLL-style unit propagation (8b), ∃-witnesses, ∀-propagation.

📊 Probe evidence (201): default budget FAIL; fuel 2,000,000 + cap 5s
still FAIL (45s); fuel 20,000 (default) + cap 120s **PASS in 12.5s
total** (~8 goals, ~1-2s each). → **BUDGET-shaped**: the refutation
completes within default fuel but needs more than 5s of wall per
`pe_refute_entails` invocation. 202 already passes on the current binary.
206/208/661/662 probe pending below.

Fix: a separate PE-refutation wall cap (runner budget plumbing, no
semantics): PE goals get their own, larger cap
(`FACTOIDAL_OWL_PE_REFUTE_CAP_SEC`), while the consistency-side refuter
keeps the 5s cap that protects the 352-test type-consistency catalog's
wall time. Measured against the full PE catalog before/after (a
fail-and-stay-fail test pays the new cap up to twice).

### WebOnt-description-logic-901/-903 — cardinality-sum subsumption

Premise: `p ⊑ r` range `A`; `q ⊑ r` range `B`; `A owl:disjointWith B`.
Conclusion: `(≥2 p ⊓ ≥3 q) ⊑ ≥5 r` (901); `(≥200 p ⊓ ≥300 q) ⊑ ≥500 r`
(903).

📊 Probe evidence (901): FAIL in 0.11s with huge budget → **RULE-shaped**.

The subsumption goal puts `≥2 p`, `≥3 q`, `≤4 r` (NNF of ¬≥5 r) on a fresh
node. The existing max-card clash counts materialised successors:
`ensure_min_witnesses` mints distinct witness groups per property, but
cross-group distinctness (p-witnesses vs q-witnesses) is not derivable —
it follows from range disjointness, which no current rule consults. And
903's cardinalities (200/300) exceed `max_generated_witnesses = 12`, so
witness minting cannot scale there regardless.

Fix (one new ANALYTIC clash rule in `Tableau.Refute.fst`, no witnesses):
for a node labelled `≤k r`, find min-labels `{≥mᵢ pᵢ}` on the SAME node
with pairwise-distinct pᵢ, each pᵢ ⊑* r, and range classes pairwise
provably disjoint (`owl:disjointWith`/`owl:complementOf`, either
direction, in the goal graph); if Σ mᵢ > k → clash.
Soundness: each `≥mᵢ pᵢ` forces mᵢ pairwise-distinct pᵢ-successors in
every model; each pᵢ-successor is an r-successor (pᵢ ⊑* r) and lies in
CEXT(range(pᵢ)) (rdfs:range semantics); pairwise-disjoint ranges make the
successor groups pairwise disjoint; hence ≥ Σ mᵢ distinct r-successors,
contradicting `≤k r`. Purely arithmetic — closes 901 and 903 alike in the
first clash round.

### Consistent-but-all-unsat — finite-model counting (bijections + oneOf)

Premise: bijections (Functional+InverseFunctional properties, declared
inverses) between named classes `a ⇄ 2a`, `2a ⇄ bUNIONc`, `b ⇄ a`,
`b ⇄ c`; `bUNIONc ≡ b ⊔ c`; pairwise disjointness; `a ⊑ {i1}⊔{i2}⊔{i3}`
(finiteness). Conclusion: `X ⊑ owl:Nothing` for X ∈ {2a, a, b, c}.
Class-size arithmetic: |b|+|c| = |2a| = |a| = |b| = |c|, b,c disjoint ⇒
|a| = 2|a| with |a| ≤ 3 finite ⇒ |a| = 0. Exactly the
`Tableau.CountingOracle.class_size_unsat` fragment
(FIBER/BIJECTION/DISJOINT-UNION/ONEOF with Farkas-certificate validator)
— but that verified check is consulted only from the InconsistencyTest
path today, never from PE. Probe pending.

Fix: PE subsumption-goal dispatch — when refuting goal graph
`closure @ {fresh x : X, x : ¬Nothing}` the tableau cannot count; consult
`class_size_unsat (closure @ goal)` as an additional verified rung in
`pe_refute_entails` (runner dispatch only — the unsat decision including
its soundness lemma is already F\*-verified).

### WebOnt-I5.2-004 — complementOf conclusion (Group J)

Premise: `Nothing ⊑ (≥1 p) ⊓ (≤0 p)` (unsat by construction);
`A ≡ ∃q.Thing`; `notA ≡ ∀q.Nothing`. Conclusion:
`notA owl:complementOf A` — a predicate `negation_goals` has NO arm for
today (falls to `None`).

Fix part 1 (`Tableau.Refute.fst` `negate_content_triple`): an
`X owl:complementOf Y` arm producing TWO goals (complementOf means
CEXT(X) = Δ \\ CEXT(Y)): (i) fresh x ∈ X ⊓ Y must refute (disjointness
half); (ii) fresh x ∈ ¬X ⊓ ¬Y must refute (coverage half). Both are
faithful: ¬(X = Δ\\Y) ≡ ∃x.(x∈X∩Y) ∨ ∃x.(x∉X ∧ x∉Y), and refuting both
disjuncts refutes the disjunction; conversely the two goals assert
nothing beyond the respective witnesses.
Fix part 2: goal (ii) needs the tableau to close
`x : ¬A ⊓ ¬notA` — i.e. contrapositive unfolding ¬A → ∀q.¬Thing (present,
section 7) and ¬notA → ∃q.¬Nothing (present) then the ∀/∃ interaction
puts `¬Thing` on the minted witness (C2 clash arm `cc = owl:Thing`
present). Expected to close with existing rules once the goals exist;
verify by measurement.

### WebOnt-I5.2-006 — named-subject unionOf conclusion (Group J stretch)

Conclusion: `AorB owl:unionOf (A B)` — `owl:unionOf` is a STRUCTURAL
predicate for `negation_goals`, so the conclusion has zero content
triples → `None`. Needs a content arm for `S owl:unionOf L` with S a
NAMED IRI: class equality S ≡ A⊔B → two subsumption goals (fresh
x ∈ S ⊓ ¬(A⊔B); fresh x ∈ (A⊔B) ⊓ ¬S). The premise routes both halves
through the unsatisfiable-`Nothing` trick; whether the existing rules
close them is to be measured after the arm exists (the deep step:
x:¬A needs ∀q.¬Thing vs notA's ∀q.Nothing — closing may additionally
need normalising provably-unsat named classes to ⊥, deferred unless
measurement shows it).

### WebOnt-description-logic-502 (inconsistency) — 3-SAT over oneOf pairs

Deliberately adversarial 3-SAT encoding (nested oneOf/differentFrom).
Probe pending: if the DPLL-style union machinery (8b) closes it given
budget, it is cap-shaped (inconsistency runs under the 5s refuter cap);
raising THAT cap trades type-consistency catalog wall time — measure
before deciding. Otherwise park behind its own issue.

### WebOnt-description-logic-909 (inconsistency) — cardinality multiplication

N×M pigeonhole via chained functional/inverse bijections and
cardinality 2/3/5 equivalences — the exact fragment the CountingOracle
was built for (its banner names dl-909). Today `class_size_refutes`
consults `class_size_unsat` on the RL-base closure for InconsistencyTests;
it evidently does not fire (probe pending — check whether the fragment
recogniser rejects the premise or the linear system misses the
multiplicative constraint |cardinality-N-times-M| = 3·|cardinality-N|
etc.). The z3 oracle path is explicitly NOT the goal (verified-only).

## Commit plan (one deliverable each)

1. This design note.
2. `Tableau.Refute.fst`: min-sum/disjoint-range analytic clash rule
   (targets 901 + 903; PE catalog + consistency catalogs gated).
3. `owl_runner.ml`: separate PE-refutation cap knob (targets DL98 ABox
   family: 201/206/208/661/662 as measured); full PE catalog re-run for
   wall-time + score.
4. `Tableau.Refute.fst`: `owl:complementOf` negation-goal arm
   (targets I5.2-004).
5. `Tableau.Refute.fst`: named-subject `owl:unionOf`/`owl:intersectionOf`
   negation-goal arm (targets I5.2-006).
6. PE counting rung: consult `class_size_unsat` from `pe_refute_entails`
   (targets Consistent-but-all-unsat) — dispatch-only change.
7. 909/502 as classified by their probes (CountingOracle fragment fix /
   budget decision).

Every commit: verify touched modules (z3 4.13.3, no admits), push source
first, then extract+compile in the worktree, then run the four catalogs
(PE, inconsistency, consistency, NE) and the profile suites before
declaring the milestone.
