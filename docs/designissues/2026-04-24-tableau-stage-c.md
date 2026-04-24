# Tableau stage (c): cardinality restrictions — scoping + paper-Q3 diagnosis

**Date:** 2026-04-24
**Author:** stage-c subagent
**Status:** IN PROGRESS — diagnosis phase

## TL;DR (5-min checkpoint)

The task prompt asked me to target `paper-sparqldl-Q3` with stage-(c)
cardinality work. **That targeting is wrong.** `paper-sparqldl-Q3.rq`
is a `owl:complementOf` + `owl:someValuesFrom` query; per the
2026-04-19 tableau plan, that's **stage (d)** (`owl:complementOf` /
classical negation) combined with **stage (e)** (fresh-individual
skolemisation), not stage (c).

The entailment tests that genuinely exercise cardinality are:

- `parent4` — `owl:minCardinality 1` (unqualified)
- `parent6` — `owl:minQualifiedCardinality 1` + `owl:onClass :Female`
- `parent7` — `owl:maxQualifiedCardinality 1` + `owl:onClass :Female`
- `parent8` — `owl:qualifiedCardinality 1` + `owl:onClass :Female`

Agent B + G already landed closure-side rules for `cls-minc1`,
`cls-maxqc1`, `cls-exactqc1` covering the RL regime. So under
**OWL-RL** most of these are either passing or blocked on the
`someValuesFrom`/`allValuesFrom` + skolemisation pieces rather than
the counting logic itself.

For **OWL-DL / tableau**, stage (c) means: teach `is_member_tableau`
to short-circuit `CE_MinCard`, `CE_MaxCard`, `CE_ExactCard`
(qualified variants included) by counting edges already asserted in
the ABox.

## Q3 analysis (the prompt's target)

Query: find `?x` with `hasPublication` whose publisher has type
`[ onProperty publishedAt ; someValuesFrom (complementOf Workshop) ]`.

Data:
- `:ConferencePaper ⊑ ∃ publishedAt.Conference`
- `:paper1 a :ConferencePaper`
- `:Conference owl:disjointWith :Workshop`
- `:John :hasPublication :paper1`
- `:person1 :hasPublication :paper1`

Expected rows: `:John`, `:person1`.

Reasoning path required:

1. `:paper1 a :ConferencePaper` → `∃ Z . :paper1 publishedAt Z ∧ Z a :Conference`
   (fresh-individual skolemisation — **stage e**).
2. `Z a :Conference` ∧ `:Conference owl:disjointWith :Workshop`
   → `Z a (complementOf Workshop)` (complement introduction via
   disjointness — **stage d**).
3. `:paper1 a [ ∃ publishedAt. (¬Workshop) ]`.
4. Query binds `?x = :John / :person1`.

None of the four steps is a cardinality count. Stage (c) does nothing
for Q3 on its own — the prompt's assumption is incorrect.

## Pivot: where stage (c) actually pays off

Re-read `docs/designissues/2026-04-19-tableau-owl-plan.md` §3 Group C:

| Test | Construct | Achievable under stage (c)? |
|------|-----------|-----------------------------|
| parent7 | `maxQualifiedCardinality 1` + `onClass :Female` | Partial — membership of named individual in `maxN` needs sameAs aggregation; safe default: return `None` |
| parent8 | `qualifiedCardinality 1` | Same as parent7 (exactly = min∧max) |
| parent4 | `minCardinality 1` (unqualified) | Straightforward — count outgoing edges on `hasChild` |
| parent6 | `minQualifiedCardinality 1` + `onClass :Female` | Straightforward — count outgoing edges whose target is `:Female` |

## Plan for the remaining timebox

1. Read `Tableau.fst` fully to confirm current `class_expr` shape and
   `is_member_tableau` structure.
2. If the `class_expr` type already has `CE_MinCard / CE_MaxCard /
   CE_ExactCard` constructors, add counting logic in `is_member`
   that returns:
   - `Some true` for min-N when we can positively count ≥N distinct
     edges whose target satisfies the qualifier.
   - `None` for max-N / exact-N unless we have explicit
     `owl:differentFrom` / `owl:AllDifferent` backing (no UNA leak).
3. If the constructors don't exist yet, define them (alongside the
   parser/closure side that already references them), add the
   decision logic, and leave the TBox-axiom side as `None` — keep
   scope tight.
4. **Do NOT** try to fix Q3. That belongs to stages (d)+(e).

## Soundness contract (from stage (b) comment)

- `Some true` ⇒ every model of the KB has `x ∈ C`.
- `Some false` ⇒ no model of the KB has `x ∈ C`.
- `None` ⇒ tableau couldn't decide; caller falls back to closure.

For cardinality:
- `min N P C`: `Some true` iff we can exhibit N distinct
  (pairwise-differentFrom) edges `x P y_i` with `y_i ∈ C`. Otherwise
  `None`.
- `max N P C`: `Some true` iff every outgoing `P`-edge whose target
  is in `C` can be shown sameAs each other, bringing the count below
  or equal to N. Rarely provable without explicit sameAs — default
  `None`. `Some false` iff we can exhibit N+1 pairwise-differentFrom
  edges whose targets are in `C`.
- `exactly N P C`: `Some true` iff both min-N and max-N conditions
  above hold. Very rarely decidable without differentFrom axioms.

## Anticipated pass delta

If stage (c) only lands the min-counting branch and parent4/parent6
are currently failing because of the tableau path (they might already
pass via OWL-RL closure from earlier agents' `cls-minc1-bridge` work),
we gain **0–2 tests**.

Realistically this stage is scaffolding for stages (d)/(e) more than
a test-score win. Soundness first; the headline number will move
when Q3's complementOf/skolemisation lands.

## Final update

Closing the loop: stage (c) here contributes types + decision
skeleton so that stages (d)+(e) have a target to branch from. See
the follow-up commit(s) for concrete diffs.
