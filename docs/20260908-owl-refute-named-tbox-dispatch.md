# OWL refuter named TBox dispatch, 2026-09-08

## Scope

`applyAxioms` folded the complete TBox for every node label.  A fresh native
schema.org first-pass profile after the indexed-initialisation change measured
25,543 label visits and 8,573 axioms.  `applyAxioms` took 2,659 ms of the
3,405 ms pass, so it remained the largest measured pass component.

The compiled pass now builds one `NamedAxiomIndex` per pass.  For a
`ClassExpr.named q` label it reads the ordered bucket of axioms whose antecedent
is exactly `.named q`.  Every nonnamed label uses the original complete TBox in
its original order.  The tableau state, rule side conditions, search budgets,
and fallback behaviour are unchanged.

## Equality argument

The public `onePass` remains the list specification.  The existing
`onePass_eq_filtered` `@[csimp]` theorem now reaches the dispatch implementation
through this proof chain:

- `NamedAxiomIndex.add_getD` proves one bucket update appends exactly one
  matching axiom and changes no queried nonmatching bucket.
- `fold_namedAxiomIndex_getD` and `buildNamedAxiomIndex_getD` prove each final
  bucket equals the corresponding ordered TBox filter.
- `namedAxiomFor_rejected` proves every filtered-out axiom has `ceEq = false`
  against the named label.  This uses `ceEq`; it does not substitute structural
  equality for the semantic match guard.
- `applyAxioms_named_filter_eq` applies the existing identity-step fold theorem
  to show that the ordered bucket and complete TBox produce the same state and
  change flag.
- `applyAxiomsDispatched_eq`, `onePassNodeDispatched_eq`, and
  `onePassNodesDispatched_eq` lift the equality through labels and nodes.
- `onePassFiltered_eq` retains the existing equality to public `onePass` while
  also retaining the proved edge, conjunction, and global TBox filters.

`#print axioms` for the new theorems reports only `propext`,
`Classical.choice`, and `Quot.sound`.  No `sorry`, user axiom,
`native_decide`, `unsafe`, `implemented_by`, partial definition, or resource
option was added.

## Fresh schema.org measurements

A temporary native phase harness parsed
`third_party/vocabularies/schemaorg-30.0-current-https.ttl`, ran indexed OWL RL
closure with fuel 100, collected the TBox, initialised the tableau state, and
timed each first-pass component.  The temporary harness and Lake target were
removed after measurement.  These runs occurred after the laptop resumed and
do not span an offline interval.

The closure had 60,770 triples, the state had 4,912 nodes, and all runs visited
25,543 labels.  The pre-change measurement and three post-change runs were:

| Component | Before | After 1 | After 2 | After 3 | After median |
| --- | ---: | ---: | ---: | ---: | ---: |
| named index construction | — | 7 ms | 7 ms | 8 ms | 7 ms |
| `applyAxioms` / dispatched equivalent | 2,659 ms | 619 ms | 603 ms | 627 ms | 619 ms |
| complete profiled pass | 3,405 ms | 1,406 ms | 1,380 ms | 1,476 ms | 1,406 ms |

The median dispatched axiom phase is 76.7% shorter than the fresh baseline;
the complete profiled pass is 58.7% shorter.  The generated C builds the index
inside `onePassFiltered`, calls `onePassNodesDispatched`, and `searchLoop` calls
`onePassFiltered`.

## QUDT boundary

A QUDT phase run reached a 638,420-triple closure, 9,164 TBox axioms, 12,719
initial nodes, and an initial clash result of false.  Its instrumented first
pass did not finish within a further 60 seconds and was interrupted.  No QUDT
pass timing or verdict is claimed from that run. The separate root public request finishes and its initial clash is validated against source statements in the [completion worknote](20260908-lean-dl-completion-and-scale.md#named-dispatch-and-qudt-public-result). The follow-up below confirms that both bounds yield the same graph and a clash on current source.  The per-label IO timing in
the phase harness also adds overhead, so a separate coarse profile is needed
before assigning the remaining QUDT cost to a rule.

## Validation

From `formal/lean4/`:

```text
lake build L4Factoidal.OWL.Refute
lake build L4Factoidal.OWL.RefuteTests
```

Both passed.  `RefuteTests` includes a focused check that named buckets retain
TBox order while excluding interleaved nonmatching and nonnamed antecedents.
The proof audit covers every index, dispatch, node, and pass equality theorem.
The generated-C inspection confirms the compiled search path uses the new
dispatch.  Full-project and catalog builds remain merged-tree integration
checks because depth and negation-goal changes were concurrent.


Follow-up, 2026-09-09: a fresh single-input comparison produces 638,420
triples for both closure fuel 100 and the public bound, with exact list-order
equality. Both initial states clash on current source. The earlier false
clash measurement is not reproduced; its exact cause is not established.
Source and copied tool output are preserved in the completion evidence JSON.
