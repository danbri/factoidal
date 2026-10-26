# OWL refuter bounded witness obligations

Date: 2026-09-08

Issues: https://github.com/danbri/factoidal/issues/617 and
https://github.com/danbri/factoidal/issues/586

## Problem

`ensureWitnesses` deliberately stops below `maxWitnessDepth = 3`, but the
search previously treated the resulting quiet state as `open'`. This made a
bounded implementation claim consistency for an unfinished tableau.

The reproducer in
`/private/tmp/factoidal-dl-depth-boundary-20260908/results.json` uses
`x : (exists p)^d.A` together with `x : (forall p)^d.not A`. The graph is
unsatisfiable at every depth. The native public API found the clash at depths
2 and 3, then incorrectly returned `true` at depths 4 and 5. Satisfiable
controls replace terminal `not A` with `A`.

A separate PositiveEntailment gap classified `i rdf:type owl:Thing` as a
metadata declaration. It is a semantic class-membership assertion and its
negation is bottom, so it must produce a refutation goal.

## Change

`pendingWitnessObligation` checks quiescent nodes for unsatisfied `someOf`,
`minCard`, and `minQualCard` labels using the same successor and filler rules
as witness creation. Search returns `out` when such an obligation remains
after deterministic expansion and all represented branch choices. An `out`
short-circuits sibling exploration, preserving the shared-budget rule: one
unknown branch makes the whole refutation unknown.

This is a conservative boundary repair. It does not implement blocking and
does not prove the depth-4 contradiction inconsistent. It prevents the depth
cap from being reported as consistency. Public and harness diagnostics now
say that `none` may mean visit-budget exhaustion or an unresolved bounded
witness obligation. Harness telemetry calls the combined count
`pe_refuter_indeterminate_limits`.

`owl:Thing` was removed from `isMetaTypeIri`. The existing negation builder
then constructs the complement-membership goal, which the clash rules close.

The module header now states the actual assurance boundary. `some true` is an
open quiescent bounded expansion without a model certificate. `some false`
has an intended OWL 2 Direct Semantics soundness contract, while the general
executable-search-to-`Refuted` refinement theorem remains open. The search
budget bounds state visits; one visit can still be superlinear in graph,
node, label, and axiom counts.

## Checks

Focused build:

```text
lake build L4Factoidal.OWL.RefuteTests l4factoidal l4owl-probe
Build completed successfully (465 jobs).
```

The headline proof audit remained:

```text
search_remaining_le: propext, Classical.choice, Quot.sound
search_zero: propext, Classical.choice, Quot.sound
search_immediate_clash: propext, Classical.choice, Quot.sound
search_changed: propext, Classical.choice, Quot.sound
```

Fresh post-resume native runs with `--fuel 64`:

| depth | satisfiable control | contradiction | user CPU each |
| ---: | --- | --- | ---: |
| 2 | `true` | `false` | 0.02-0.04 s |
| 3 | `true` | `false` | 0.02 s |
| 4 | `unknown` | `unknown` | 0.02 s |
| 5 | `unknown` | `unknown` | 0.02 s |

The depth-4/5 results now withhold instead of returning false consistency.
An empty premise entails `i rdf:type owl:Thing` through refutation at the
default budget. Direct build-time guards also pin a cyclic TBox as unknown,
the depth-3 clash, both depth-4 unknown controls, and an explicit capped
existential obligation.

This change does not establish SROIQ(D) completeness, blocking adequacy, or a
model certificate for open branches. The subsequent native process isolation
is recorded in `docs/20260908-owl-refuter-hard-timeout.md`.
