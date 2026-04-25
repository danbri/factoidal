# OWL DL informant corpus — paper-Q3, parent4, parent7 (2026-04-25)

**Agent Samekh2 — P3 informant, not coverage push.** Read-only on `.fst`.
Goal: pick a **small, targeted** subset of W3C OWL 2 Test Cases (vendored
at `third_party/testing/owl/`) that informs what's missing from our DL
tableau for the 3 remaining SPARQL `entailment` fails:

1. `paper-sparqldl-Q3` — needs ∃R.C with C = (¬D), and disjointWith bridge.
2. `parent4` — `(hasChild min 1)`, needs existential-witness from `Parent ≡ ∃hasChild.⊤`.
3. `parent7` — `(hasChild max 1 :Female)`, needs existential merging.

We are NOT trying to pass all 2500 OWL tests. We pick ≤ 30 that act as
oracles/regression for tableau features F1 (existential witness), F2
(disjointWith → complementOf bridge), F3 (max-card merging).

## Source catalogs

| Catalog | Cases | Relevant slice | Notes |
|---|---|---|---|
| `profile-RL.rdf` | 91 | 30 PE — already 13 PASS | OWL-RL only; DL features absent. |
| `type-positive-entailment.rdf` | 206 PE | ~22 in scope | THE primary informant pool. |
| `semantics-direct.rdf` | very large | low priority | Semantics tests, not direct DL probes. |
| `syntax-dl.rdf` | very large | parser, not reasoner | Skip for tableau triage. |
| `type-consistency.rdf` | many | nice-to-have for parent7 (max-card sat) | Sample a handful. |

## Subset chosen (30 tests, ~10 per fail)

### Group A — paper-Q3: complementOf + disjointWith + universal/existential interplay

| # | Test | Source | Why informative for Q3 |
|---|---|---|---|
| A1 | `WebOnt-complementOf-001` | type-pos-ent | Pure complementOf entailment — F2 baseline. |
| A2 | `WebOnt-disjointWith-001` | type-pos-ent | disjointWith induced inconsistency. |
| A3 | `WebOnt-disjointWith-002` | type-pos-ent | disjointWith with named class memberships. |
| A4 | `DisjointClasses-001` | profile-RL | contrapositive complementOf bnode synthesis (Stewie example) — exact F2 pattern. |
| A5 | `DisjointClasses-003` | profile-RL | ternary disjoint, F2 cascade. |
| A6 | `WebOnt-someValuesFrom-001` | type-pos-ent | ∃R.C entailment — same primitive as Q3 outer restriction. |
| A7 | `WebOnt-someValuesFrom-003` | type-pos-ent | someValuesFrom + subClassOf + universal. |
| A8 | `rdfbased-sem-restrict-somevalues-cmp-class` | type-pos-ent | someValuesFrom comparison across class subsumption. |
| A9 | `WebOnt-allValuesFrom-001` | type-pos-ent | universal-restriction entailment, used by Q3's nested CE. |
| A10 | `rdfbased-sem-restrict-allvalues-cmp-class` | type-pos-ent | allValuesFrom comparison — nested CE check. |

### Group B — parent4: someValuesFrom existential witness + min-cardinality

| # | Test | Source | Why informative for parent4 |
|---|---|---|---|
| B1 | `bnode2somevaluesfrom` | type-pos-ent | Bnode → someValuesFrom round-trip — exact F1 trigger. |
| B2 | `somevaluesfrom2bnode` | type-pos-ent | someValuesFrom → bnode — confirms witness materialisation. |
| B3 | `rdfbased-sem-restrict-somevalues-inst-subj` | type-pos-ent | ∃R.C member by subject side — direct parent4 analogue. |
| B4 | `rdfbased-sem-restrict-somevalues-cmp-prop` | type-pos-ent | someValuesFrom across subProperty. |
| B5 | `WebOnt-someValuesFrom-001` | type-pos-ent | (also in Group A) — listed once. |
| B6 | `New-Feature-ObjectQCR-001` | type-pos-ent | Object qualified cardinality, kindred to MinQCard 1. |
| B7 | `New-Feature-ObjectQCR-002` | type-pos-ent | QCR Class-of-Restriction entailment. |
| B8 | `WebOnt-cardinality-001` | type-pos-ent | Plain cardinality 1 entailment — min/max baseline. |
| B9 | `WebOnt-cardinality-002` | type-pos-ent | Cardinality 1 with explicit individual chain. |
| B10 | `Qualified-cardinality-restricted-int` | type-pos-ent | Qualified cardinality numeric edge. |

### Group C — parent7: max-cardinality without DL contradiction

| # | Test | Source | Why informative for parent7 |
|---|---|---|---|
| C1 | `WebOnt-cardinality-003` | type-pos-ent | Cardinality 1 → maxCardinality entailment. |
| C2 | `WebOnt-cardinality-004` | type-pos-ent | Max-card with multiple successors merged. |
| C3 | `WebOnt-cardinality-006` | type-pos-ent | Cardinality with FunctionalProperty. |
| C4 | `WebOnt-FunctionalProperty-001` | type-pos-ent | Functional → max 1 derivation. |
| C5 | `WebOnt-FunctionalProperty-003` | type-pos-ent | Functional propagation through subProperty. |
| C6 | `Qualified-cardinality-boolean` | type-pos-ent | QCR over Boolean datatype, exercises maxQCR projection. |
| C7 | `rdfbased-sem-restrict-maxcard-inst-obj-one` | type-pos-ent | maxCardinality 1 → unique successor (parent7 directly). |
| C8 | `rdfbased-sem-restrict-maxqcr-inst-obj-one` | type-pos-ent | maxQualifiedCardinality 1 — parent7's exact construct. |
| C9 | `WebOnt-InverseFunctionalProperty-001` | type-pos-ent | Inverse-functional max-1 reverse. |
| C10 | `New-Feature-ObjectQCR-002` | type-pos-ent | (also in Group B) — listed once. |

Effective unique tests: **~28** (B5 and C10 dedupe with A6/B7).

## Methodology — running the subset

The current runner accepts a manifest path and runs all PositiveEntailmentTests
in that catalog. It does not have a per-test filter. Strategy:

1. **profile-RL run** (already executed) — 30 PE tests in 1.6s; 13 PASS.
   Picks up A4, A5 directly. Captured in `/tmp/owl_rl_run.out`.
2. **type-positive-entailment.rdf run** (already executed) — 206 PE in 77s.
   Captured in `/tmp/owl_posent_run.out`. Picks up all other Group A/B/C
   tests (under their `rdfbased-sem-*` and `WebOnt-*` IDs).
3. Cross-reference per-test FAIL/PASS lines against the chosen 28; tabulate.

## Per-test results — see `Section: Results below`.

(filled in after second-pass extraction.)

## Projected delta if we add tableau features F1/F2/F3

| Feature | New PASSes (chosen subset) | Net SPARQL delta |
|---|---|---|
| F1 — existential witness for ∃R.C / Min 1 | B1, B2, B3, B5, B6, B7 (~6) | **parent4 +1** |
| F2 — disjointWith → complementOf bridge | A1, A2, A3, A4, A5 (~5) | **paper-Q3 +1** (with F1) |
| F3 — max-card merging guard | C1, C2, C7, C8 (~4) | **parent7 +1** |
| F4 — qualified cardinality projection | B6, B7, B10, C6 (~4) | (already mostly OK) |
| F5 — disjoint class contrapositive (NaF) | A2, A3 closure side | bonus, OWL-RL out-of-scope |

## Out of scope (intentional)

- **Nominals** (oneOf, hasValue against bnode) — defer; only WebOnt-oneOf-002/3/4
  in the corpus, won't be tested here.
- **Property chains beyond k=2** — Kappa/Theta covered. Skip in this triage.
- **Self restriction** — New-Feature-SelfRestriction-001/002 — not used by the 3 fails.
- **Datatype facets** — XSD numeric subClass — Zeta covered for OWL-RL.
- **`type-consistency.rdf`** — sat-only, our tableau output is `Some true`/false,
  consistency itself isn't directly informant (we'd just confirm the runner
  doesn't emit a contradiction).

## Hard-limits respected

- ≤ 250 lines (this doc).
- ≤ 60 min wall-clock.
- Read-only on `.fst`.
- No `extract` / `compile` (Yod3 has the F\* lock).
