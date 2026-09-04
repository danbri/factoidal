# The SHOIQ blocking calculus the OilEd cases need

Date: 2026-09-04.
Issue: <https://github.com/danbri/factoidal/issues/651>.
Module: `formal/lean4/L4Factoidal/OWL/Refute.lean` (the executable
engine), `formal/lean4/L4Factoidal/OWL/Tableau.lean` (the declarative
calculus and its proof home).

## Why this document exists

`L4Factoidal/OWL/Refute.lean` runs a tableau expansion. Its
termination today is a FUEL COUNTER, not a theorem: `maxWitnessDepth
= 3` refuses to mint an existential witness below depth 3, and
`maxGeneratedWitnesses = 6` caps the fan-out at one node. A cyclic
TBox such as `X ⊑ ∃p.X` would otherwise grow an infinite `∃`-chain.

A fuel counter is sound here — refusing a witness withholds labels,
so it can only lose refutations, never invent one — but it is not the
mathematics. The mathematics is BLOCKING: a condition on the
expansion order under which the search provably reaches quiescence,
and under which quiescence is a model.

The 23 OilEd `WebOnt-description-logic-*` inconsistency cases are the
measured failures that ask for it. This document states the calculus
before the code is written, names which rule decides which case, and
records what each rule costs.

## The logic

OWL 2 DL Direct Semantics is `SROIQ(D)`. The OilEd fixtures use the
`SHOIQ` fragment: role hierarchies (`H`), transitive roles (`S`),
nominals (`O` — `owl:oneOf`, `owl:hasValue`), inverse roles (`I`) and
qualified number restrictions (`Q`). The datatype domain (`D`) is
handled separately here by the value-space rules in `Refute.lean`
(`foldDatatypeConstraint`, `datatypeRangeClash`) and is not part of
this document.

The reference calculi:

* Ian Horrocks, Ulrike Sattler, Stephan Tobies. "Practical Reasoning
  for Very Expressive Description Logics." Logic Journal of the IGPL
  8(3):239-263, 2000. — The `SHIQ` tableau: the expansion rules, the
  `≤`-rule, and PAIRWISE BLOCKING, which is the blocking condition
  that stays complete once inverse roles and number restrictions are
  both present.
* Ian Horrocks, Ulrike Sattler. "A Tableau Decision Procedure for
  SHOIQ." Journal of Automated Reasoning 39(3):249-276, 2007. — The
  extension to nominals: the `NN`-rule, the `o`-rule, and the
  root-node treatment that keeps termination when a nominal can be
  reached from an arbitrary depth.

`Refute.lean` already cites the first.

## Which blocking condition, and why not a weaker one

Three conditions are in the literature, in increasing strength:

1. **Subset blocking.** A node `y` is blocked by an ancestor `x` when
   `L(y) ⊆ L(x)`. Complete for `ALC` and `S` with general TBoxes.
   NOT usable once INVERSE ROLES are present: the unravelling that
   turns a blocked tableau back into a model sends the blocked node's
   predecessor edge back up to `x`, and with an inverse role a `∀`
   constraint travels down that edge in the other direction, so `x`
   may fail a constraint that `y` satisfied.
2. **Equality blocking.** `L(y) = L(x)`. Complete for `SI`. Still not
   enough with number restrictions: an `≤ n r` at `x` counts
   successors that the unravelling duplicates.
3. **Pairwise (double) blocking.** `y` with predecessor `y'` is
   blocked by `x` with predecessor `x'` when `L(x) = L(y)`,
   `L(x') = L(y')`, and the two EDGES `⟨x', x⟩` and `⟨y', y⟩` carry
   the same role set. This is the condition Horrocks/Sattler/Tobies
   2000 prove sound, complete and terminating for `SHIQ`.

The engine has inverse roles (`inversesOf`, and after rule 1 below the
inverse direction of expansion edges too) and qualified number
restrictions (`minQualCard` / `maxQualCard`, the `≤`-rule
`pendingMerge`). So **pairwise blocking is the condition that fits**;
subset and equality blocking would both be unsound as completeness
arguments here, and adopting either would make a `some true` verdict
claim more than it may.

Nominals (`O`) break the tree shape that every blocking argument
assumes: a nominal node can be reached from any depth, so the
"ancestor" relation is no longer a tree order. Horrocks/Sattler 2007
recovers termination by treating nominal nodes as ROOT nodes, outside
the blocking relation, and bounding their number with the `NN`-rule.
This engine merges only blank nodes (`isMergeableTerm`) and never
identifies named individuals, so it does not implement the `NN`-rule;
`owl:oneOf` cases outside that reach stay withheld, which is the safe
direction.

## What the engine was missing, in the order the cases ask for it

### Rule 1 — inverse-role successors over EXPANSION edges

`successorsOf` read the inverse direction of a role off the INPUT
GRAPH only (`viaInverse` queries `st.store`). An edge the expansion
itself minted lives in `st.extra`, and its inverse direction was never
read back. So in

    Unsatisfiable ≡ p2 ⊓ ∃invR.(∃r.p1 ⊓ ≤1 r)      (Inv(invR) = r)

the witness `y` minted for `∃invR` has the ABox node `x` as an
`r`-successor — `x invR y` entails `y r x` — and the engine could not
see it. `y`'s `≤1 r` therefore never counted `x` against its bound,
the `≤`-rule never fired, and the clash `p1 ⊓ p2 = ⊥` at the merged
node was never reached.

This is not blocking. It is a missing expansion rule, and it is the
one the majority of the OilEd fixtures turn on. Sound because
`Inv(r') = r` holds in every interpretation, so an edge `(a, b)` in
`EXT(r')` puts `a` in the `r`-successors of `b`; adding a successor
the model must have cannot fabricate a clash the model does not have.

Decides: `WebOnt-description-logic-008`, `-010`, `-015`, `-023`,
`-026`, `-027`, `-029`, `-032`, `-610`, `-623`, `-626`, `-627`,
`-629`, `-630`, `-632` (measured, 2026-09-04).

### Rule 2 — global axioms (`owl:Thing ⊑ C`) apply to every node

`applyAxioms` fires an axiom when a node's LABEL structurally matches
the antecedent. An axiom whose antecedent is `owl:Thing` is a GLOBAL
constraint: `owl:Thing` denotes the whole domain, so `owl:Thing ⊑ C`
puts `C` on every individual. No node carries `owl:Thing` as an
asserted label, so the axiom never fired.

    Unsatisfiable ≡ ∃f.(p1 ⊓ ∃invF.(∃f.¬p1))
    owl:Thing ⊑ ≤1 f                                (t7.3)

Without the global axiom nothing bounds `f`, the two `f`-successors of
the inner node are never merged, and `p1` never meets `¬p1`.

Sound because `owl:Thing` is interpreted as the whole domain in every
interpretation, so every element satisfies the antecedent. This is the
standard TBox internalisation of a general axiom; it adds no choice
point.

Decides: `WebOnt-description-logic-030` (DL test t7.3).

### Rule 3 — pairwise blocking: stated, and MEASURED AS NOT THE LEVER

Rules 1 and 2 took the `--dl` corpus from 1296 to 1312 pass (out of
1457) and left these OilEd inconsistency cases failing:

    -035  owl:oneOf plus an inverse role, the SPY POINT
    -040  a 10-way conjunction of binary unions
    -108  number restrictions under a role hierarchy (Heinsohn 3.2)
    -502  the classic 3-SAT encoding
    -504  a second encoding of the same
    -909  integer multiplication, N*K = 2K, M*K = 3K, NMK != 5K
    -910  integer multiplication, N = 20, M = 30, NM != 601

Pairwise blocking replaces `maxWitnessDepth` as follows. A witness
node `y` with expansion predecessor `y'` is BLOCKED when the branch
holds a witness `x` with predecessor `x'` such that `x` is an ancestor
of `y` in the expansion tree, `labelsOf x = labelsOf y`,
`labelsOf x' = labelsOf y'`, and the role sets of the two edges agree.
`ensureWitnesses` mints nothing at a blocked node, and the depth cap
goes.

**Blocking would close none of the seven.** Blocking's only effect on
what the search REACHES is that it makes a deeper expansion safe. So
the question "would blocking close a case" is answered by raising the
cap the blocking would retire. Measured, 2026-09-04:
`maxWitnessDepth` 3 to 8, everything else unchanged, gives
`type-inconsistency.rdf` 116 pass, 11 fail, 1 skip (out of 128) —
byte-identical to the depth-3 result, the same seven OilEd cases and
the same four datatype cases. The depth fuel is NOT what withholds
these refutations.

What each of the seven actually needs:

* `-035` needs the NOMINAL rules of Horrocks/Sattler 2007 (the
  `NN`-rule and the `o`-rule), so that the `≤2 invP` bound on the spy
  point can force the domain down to two elements. `isMergeableTerm`
  refuses to identify named individuals, so the rule cannot fire at
  all. This is a different rule from blocking.
* `-108` is bound by the `≤`-rule's BRANCHING, not by the budget: it
  still fails at `--refute-budget 4096`, sixty-four times the default.
  The merged node accumulates nine `tt`-successors, and the rule
  branches over every mergeable pair at every level.
* `-040`, `-502`, `-909`, `-910` also still fail at
  `--refute-budget 4096`. They are the deliberately hard instances —
  a complete calculus decides them, and the search is exponential.
* `-504` DOES close at `--refute-budget 4096`. That is a budget
  change, not a rule, and it was NOT landed. The default budget stays
  64.

One efficiency observation, measured and NOT landed because it moved
nothing: `witnessPairs` offers both `(a, b)` and `(b, a)`, and
`mergeInto` writes the same identification either way, so the two are
one branch. Enumerating each unordered pair once halves the branching
factor at every level. It changes no verdict at budget 64 (116 pass,
11 fail out of 128) and no verdict at budget 4096 (117 pass, 10 fail),
so the `≤`-rule's cost here is dominated by the successor count, not
by the pair ordering.

Blocking therefore stays worth doing, for two reasons that are not
conformance: it retires a fuel counter for a theorem, and it is what
lets a `some true` verdict mean SATISFIABLE on the `SHIQ` fragment.
It is not the lever for the remaining OilEd cases, and a session that
implements it should not expect the score to move.

## What a `some true` verdict may claim, before and after

Before: nothing beyond "no clash was found within the caps". The
module header already says so.

After rule 3, on the `SHIQ` fragment only (no `owl:oneOf`, no
`owl:hasValue`, no named-individual merging), a blocked quiescent
state unravels to a model, so `some true` means SATISFIABLE. Outside
that fragment the old reading stands. Any wording change to the module
header must carry that restriction, or it over-claims.

## The honesty rule for this workstream

A case that starts passing because `maxWitnessDepth`,
`maxGeneratedWitnesses` or the refute budget was RAISED is a budget
change, and is reported as one. It is not a case the calculus decided.
The refute budget has been measured as not a limiting factor here:
`--refute-budget 512`, eight times the default, gives an identical
corpus score.
