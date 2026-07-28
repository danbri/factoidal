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

📊 Full probe table (single-test catalogs, committed binary,
cap 120s + fuel 2M unless noted):

| Test | Probe verdict | Classification |
|---|---|---|
| dl-201 | PASS 12.5s (cap 120, default fuel) | budget |
| dl-202 | PASS already (default budget) | fixed earlier today |
| dl-206 | FAIL at cap 120; cap-450 probe pending | budget(large) or perf |
| dl-208 | FAIL at cap 120 (176s spent); cap-450 probe pending | budget(large) or perf |
| dl-661 | PASS 118s (9-way parallel, inflated) | budget |
| dl-662 | PASS 55s (parallel, inflated) | budget |
| dl-901 | FAIL fast 0.1s | rule → C7 min-sum clash (landed) |
| dl-903 | (same shape as 901, larger k) | rule → C7 |
| Consistent-but-all-unsat | FAIL fast 1.8s | rule → counting extension |
| I5.2-004 | FAIL fast 0.5s | rule → complementOf arm (landed) |
| I5.2-006 | FAIL fast 0.8s | rule → named-unionOf arm (landed) |
| dl-502 (inc) | FAIL fast 0.8s | rule → nominal branching (below) |
| dl-909 (inc) | FAIL fast 0.3s | rule → counting extension |

### dl-502 nominal wave (scoped from the premise, read in full)

The 3-SAT encoding is entirely named-class oneOf machinery:
`TorF owl:oneOf (T F)` plus nine more `TorF owl:oneOf (plus_k minus_k)`
lists (set equalities), ~90 clause labels `T rdf:type [oneOf (l1 l2 l3)]`,
and `T owl:differentFrom F`. Three mechanisms, all in `Tableau.Refute.fst`:
1. **Named-subject oneOf axioms** in `collect_axioms` (z ≡ {ms}, both
   unfolding directions) + **member seeding** at `init_state` (each listed
   member is entailed in CEXT(z) — so members of one list flow into the
   OTHER lists' constraints).
2. **Nominal branching** (the standard O-rule choice): a node labelled
   `{m1..mk}`, not yet identified with any member, branches by
   IDENTIFYING it with each not-provably-distinct member —
   AND-semantics over choices, reusing `identify_branch` verbatim.
   Members provably distinct are dropped (no model realises them); a
   member that cannot be identified (literal) withholds branching.
3. **Group-aware O-rule clash**: the `CE_OneOf` clash arm upgrades
   `all_provably_distinct` to the ident-partition-aware
   `provably_distinct_grouped`, so "m was identified with F and F ≠ T"
   counts as m provably distinct from T.

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

N×M pigeonhole via chained functional/inverse fibers. ❌ PARKED, with
the reason already written into `Tableau.CountingOracle.fst`'s section-8
banner (read this session): "dl-909 is NOT decided by this path: its
class-size system is genuinely satisfiable (the all-empty assignment
with |only-d| >= 1 is a model), so no Farkas certificate exists ...
deriving |finite| >= 1 would need an UNSOUND nonemptiness rule (see the
2026-07-15 refutation note)". Independent hand-analysis this session
reached the same wall: no premise axiom soundly forces |finite| ≥ 1.
Nothing to implement without a new, genuinely different decision
procedure (finite-model reasoning over the ≤-cardinality complement
trick); out of this wave's scope.

### Consistent-but-all-unsat — counting extension, precise remaining design

The PE goal graph (fresh `x : a` + complement scaffolding) reaches the
`class_size_unsat` rung landed this session, but three gaps keep it
from firing, mapped precisely:
1. `in_counting_fragment` REJECTS the goal graph — the PE negation's
   `__factoidal_pe_neg_class owl:complementOf ...` bnode trips
   `ico_authored_complement` (only `__rl_`-canonical complement bnodes
   are exempt). Fix: exempt the `__factoidal_pe_` prefix as well —
   sound for the same reason the gate is advisory (per-row entailment +
   the Farkas validator carry soundness; the banner says so).
2. No MEMBER-nonemptiness row: `x rdf:type a` (x an IRI/bnode) entails
   |CEXT(a)| ≥ 1 in every model where CEXT(a) is finite — the sound
   nonemptiness the 909 note could not have (there, no member exists).
3. No ONEOF UPPER bound row (|a| ≤ 3 from `a ⊑ [unionOf of singleton
   oneOfs]`) — this is also the FINITENESS discipline: integer
   class-size rows are only model-sound for provably-finite classes,
   and today's system never establishes finiteness at all (trust
   boundary prose). A sound extension should build rows only over the
   finiteness-closed component (oneOf-bounded classes + bijection/
   fiber/union closure).
The bijection rows themselves already extract for this premise
(subClassOf-someValuesFrom shape both directions + declared inverses +
functional/inverse-functional: |a|=|2a|=|bUNIONc|, |b|=|a|, |c|=|b|,
disjoint-union |bUNIONc|=|b|+|c|). With (2)+(3) the system is
|a| = 2|a|, 1 ≤ |a| ≤ 3 — Farkas-certifiable. 🟡 Next session's
commit-sized item; the searcher must also learn ≤-rows.

## Final-binary flips (single-test catalogs, all waves + new defaults)

✅ WebOnt-I5.2-006 PASS 0.13s — the bottom-normalise + conjunction-
introduction pair closed exactly the two goals the design trace
predicted. ✅ dl-502 PASS ~5.5s at the new runner defaults (refuter
fuel 20000→5M, cap 5s→10s — dl-502's nominal-branching refutation
needed both; measured failing at either old default alone).
Regression re-check on the same binary: 901/903/I5.2-004/201/662 all
still PASS.

## Interim measured flips (single-test catalogs, post-C7/arms/cap binary)

✅ dl-901 PASS 0.04s (C7) · ✅ dl-903 PASS 0.04s (C7) · ✅ I5.2-004 PASS
0.06s (complementOf arm) · ✅ dl-201 PASS 6.3s (PE cap) · ✅ dl-661 PASS
55.8s (PE cap, contention) · ✅ dl-662 PASS 17.3s (PE cap). ⚠️ dl-206 /
dl-208 refutations complete but need FACTOIDAL_OWL_PE_REFUTE_CAP_SEC
≈ 450 (probe2: 206 PASS at 450s cap; 208 PASS, 252s spent) — the 60s
default keeps them failing in-catalog; raising the default trades PE
catalog wall time (🧭 owner/orchestrator call). Full-catalog gates run
after the final build (nominal + bottom-normalise waves included).

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
