# OWL 2 DL Wave C: finite-model counting in the verified tableau — refutation analysis

Date: 2026-07-15. Status: ANALYSIS (no code change to `Tableau.Refute.fst`).

Wave C of the OWL 2 DL completion program
([docs/designissues/2026-07-10-owl2-dl-completion-program.md](2026-07-10-owl2-dl-completion-program.md),
fail family 3) set out to flip three DL type-inconsistency tests in the
VERIFIED tableau by "bounded merge-search under the existing linear
budget": WebOnt-description-logic-909, WebOnt-description-logic-910, and
one=two. The premise was that these are finite-model counting problems a
budgeted pigeonhole over the existing `≤`-rule witness-merging machinery
(`Tableau.Refute.excess_pairs_for_label` / `merge_branch` /
`identify_branch`) could close.

This note records the outcome: a genuine attempt yields ZERO verified
flips, and explains the specific technical blocker per test. Per the
program's own landing discipline ("do not land a zero-movement
scaffold"), no change was made to `Tableau.Refute.fst`. The forward path
that WOULD flip all three (and retire the `#296` oracle for them) is a
different mechanism, sketched at the end.

## What the tableau does today on these three

Measured with the committed `bin/linux-x86_64/owl_runner` (post-z33kr-phase1,
mtime 2026-07-15 18:19) against `third_party/testing/owl/type-inconsistency.rdf`:

| test | oracle on | oracle off (`FACTOIDAL_OWL_Z3_RLIMIT=0`) |
|------|-----------|--------------------------------------------|
| WebOnt-description-logic-909 | FAIL/unexpected-consistency | FAIL/unexpected-consistency |
| WebOnt-description-logic-910 | PASS/oracle-z3 | FAIL/unexpected-consistency |
| one=two | PASS/oracle-z3 | FAIL/unexpected-consistency |

The pure-verified tableau returns `Some true` (`TOpen`) on all three —
it saturates to quiescence and finds no clash. The whole 128-test
InconsistencyTest catalog runs in ~5.6s, so this is a COMPLETENESS gap
(the tableau builds a small clash-free partial model), NOT a budget-out
(`TOut`). Raising `FACTOIDAL_OWL_REFUTE_FUEL` cannot change a `TOpen`
verdict.

## Why each is inconsistent (the arithmetic)

All three are "integer multiplication in OWL DL" pigeonholes: the
contradiction is a linear system over the CARDINALITIES of named
classes, not a clash local to any one individual.

### WebOnt-description-logic-910 (N=20, M=30, N·M ≠ 601)

- `only-d ≡ {d}` (oneOf, one element) `≡ (invP-1-to-N cardinality 20)`
  `≡ (invR-N-times-M-to-1 cardinality 601)`.
- `cardinality-N ≡ (p-N-to-1 someValuesFrom only-d) ≡ (invQ-1-to-M cardinality 30)`.
- `cardinality-N-times-M ≡ (q-M-to-1 someValuesFrom cardinality-N)`
  `≡ (r-N-times-M-to-1 someValuesFrom only-d)`.
- `p`, `q`, `r` are functional; `invP`, `invQ`, `invR` their inverses.

At the class level: `|cardinality-N| = 20·|only-d|`,
`|cardinality-N-times-M| = 30·|cardinality-N|`, and
`|cardinality-N-times-M| = 601·|only-d|` (via the `invR` fiber). With
`|only-d| = 1`: `600 = 601`. Contradiction.

To hit this by materializing individuals, a tableau must build ~600
distinct witnesses of `cardinality-N-times-M` and count them against the
601-bound on `d`. The generating rule is capped at
`max_generated_witnesses = 12` and `max_witness_depth = 3`; even lifting
both caps, ~600 witnesses across a multiplicative cross-product blows the
per-test wall-clock cap the linear budget is meant to hold. Infeasible
for ANY individual-materializing tableau — which is exactly why the
`#296` oracle handles it at the class-size level instead.

### one=two (bijection chain forces |a| = 2·|a|)

- `a ≡ {i,j,k}` (oneOf, three individuals, AllDifferent) — so `|a| = 3`.
- `b-and-c ≡ b ⊔ c`, `b disjointWith c` — so `|b-and-c| = |b| + |c|`.
- Eight object properties, each `owl:FunctionalProperty` AND
  `owl:InverseFunctionalProperty`, wiring 1:1 chains:
  `a=b` (a↔b), `b=c` (b↔c), `2a=a` (2a↔a), `2a=b-and-c` (2a↔b-and-c).

At the class level the 1:1 (F + IFP) properties give `|b| = |a|`,
`|c| = |b|`, `|2a| = |a|`, and `|2a| = |b-and-c| = |b| + |c| = 2·|a|`.
So `|a| = 2·|a|`, forcing `|a| ∈ {0, ∞}`, contradicting `|a| = 3`.

Individual-level trace: the 3 members of `a` force 3 `b`, 3 `c`, hence 6
`b-and-c`; each `b-and-c` forces (via the InverseFunctional
`b-and-c=2a'`) a DISTINCT `2a`; the 6 distinct `2a` each map (via the
InverseFunctional `2a=a`) to a distinct member of `a` — 6 distinct
elements into the 3-element nominal `{i,j,k}`: pigeonhole clash.

This trace is bounded (≈6 witnesses), but out of reach of the current
tableau for three compounding reasons, none of which is a merge-branch
extension:

1. `owl:InverseFunctionalProperty` is NOT modeled. `rstate` carries
   `rs_funcprops` (folded to `≤ 1 P` by `inject_functional`) but has no
   IFP counterpart. Without IFP, functionality alone (`≤ 1` successor)
   never forces the successors to be DISTINCT, so the tableau satisfies
   every `someValuesFrom` by REUSING one witness and reaches `TOpen`.
   The whole contradiction rests on injectivity, which IFP supplies.
2. The forcing cycle a→b→c/b-and-c→2a→a is depth 4-5, past
   `max_witness_depth = 3`.
3. The final clash is an EMERGENT nominal pigeonhole (6 distinct
   elements forced into `oneOf {i,j,k}`), not a single
   `≥ k P.{oneOf …}`-with-`k > m` label the existing
   `CE_MinQualCard`/`CE_OneOf` clash arm recognises. The distinctness of
   the 6 must first be PROPAGATED backward through the IFP chain — again
   machinery that does not exist.

### WebOnt-description-logic-909 (ratios: 2·3 ≠ 5)

Same shape as 910 but the numbers are per-element RATIOS, not absolute:
`finite ≡ (invP cardinality 2) ≡ (invR cardinality 5) ≡ (f some only-d)`;
the chain multiplies to `6·|finite| = 5·|finite|`. This is satisfied by
the all-empty assignment (`|finite| = 0`); the contradiction appears
ONLY once `|finite| ≥ 1` is derived. That lower bound has to come from
the `only-d = {d}` nominal anchor propagating nonemptiness forward
through the existential chain — reasoning `#296` Phase 1 found is outside
even the z3 counting fragment (909 does NOT flip with the oracle, unlike
910 / one=two).

## Why budgeted merge-branch pigeonhole cannot flip any of them

The existing `≤`-rule (`Tableau.Refute.fst` section 6a/6b) is a LOCAL,
per-node rule: it fires when ONE node's `≤ k P` label has a successor
set exceeding `k`, and branches over merging/identifying that node's own
successor pairs. Its soundness and its termination (the
`%[b; List.Tot.length pairs]` measure) both depend on the candidate set
being one node's successors.

The three target contradictions are GLOBAL: a linear system over the
sizes of several named classes, provable only by class-size arithmetic
(910, 909) or by tracing a multi-hop injective cycle whose closure needs
IFP + emergent nominal counting (one=two). No single node ever carries a
`≤ k P` label whose own successor set both exceeds `k` and contains a
forced-distinct pair — the pigeonhole lives across the whole model, not
at a node. So `find_merge_nodes` / `find_identify_nodes` never even fire
a candidate list on these inputs; there is nothing local for the
merge-branch to branch on. This is corroborated by the empirical
`TOpen`: the tableau reaches quiescence with no pending merge obligation.

Corroboration from `#296` Phase 1 (same day): the z3 oracle flips 910
and one=two ONLY by lifting the problem to a QF_LIA linear system over
class SIZES (`Tableau.CountingOracle.encode_counting_smt`'s FIBER /
BIJECTION / DISJOINT-UNION / ONEOF-nonemptiness lemmas), and cannot flip
909 at all. An individual-materializing, budget-bounded tableau is
strictly weaker than that class-size encoding on this fragment, so it
cannot do what even z3-at-class-level cannot.

## The forward path that would actually flip these (verified)

Retarget from "individual-level merge branching" to a VERIFIED F*
class-size linear-arithmetic reasoner — the model-theoretically sound
core of what the `#296` oracle does, brought inside the verified
boundary so the flips are verified, not oracle-assisted:

1. Port the four sound lemmas already written and measured in
   `Tableau.CountingOracle.fst` (FIBER `|D| = k·|X|`, BIJECTION
   `|D| = |Y|`, DISJOINT-UNION `|Z| = |m1| + |m2|`, ONEOF-nonemptiness
   `|C| ≥ 1`) into a total F* pass that emits a linear system over
   per-named-class `nat` size variables. Each lemma already carries its
   Direct-Semantics soundness argument in that module.
2. Replace the `assume val z3_check_sat` decision with a VERIFIED
   unsat check over the specific systems this fragment produces — the
   coefficients are small non-negative integers and the systems are
   tiny (single digits of classes), so a bounded verified
   Gaussian-elimination / Presburger-fragment check is tractable and
   avoids the oracle dependency entirely. `Some false` from it retires
   910 and one=two from `PASS/oracle-z3` to plain verified `PASS`.
3. Add a NONEMPTINESS-PROPAGATION lemma (`|C| ≥ 1` and
   `C ⊑ ∃p.D`-style forcing implies `|D| ≥ 1`, sound under Direct
   Semantics) so the `only-d = {d}` anchor lifts `|finite| ≥ 1`,
   turning 909's `6·|finite| = 5·|finite|` unsat. This is the piece
   `#296` explicitly left open.

This is a class-size reasoner wave, not a Wave-C merge extension; it
should be scoped and gated as its own wave (soundness gate: exactly one
pre-existing `unexpected-inconsistency`, WebOnt-miscellaneous-202; zero
new; floors green). Tracked against `#296` (oracle retirement) and the
completion program's fail-family-3 line.

## Gate evidence for this (zero-code-change) landing

- `Tableau.Refute.fst` unchanged — no `--lax`, no `--admit_smt_queries`,
  no new admits introduced (nothing edited).
- Pure-verified DL type-inconsistency baseline unchanged: 909 / 910 /
  one=two remain `unexpected-consistency` with the oracle off, exactly
  as before; 910 / one=two remain `PASS/oracle-z3` with it on. No test
  regresses (no code path touched).
- Reconciliation note: a direct
  `owl_runner third_party/testing/owl/type-inconsistency.rdf` run
  reports 34 pass / 94 fail (+2 oracle-assisted) on the raw catalog;
  the 112 pass / 16 fail (out of 128) figure cited in the Wave-C brief
  and `#296` is the report-layer DL aggregation and is unchanged by this
  note.
