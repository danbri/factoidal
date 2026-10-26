# OWL refuter TBox prefilter

Date: 2026-09-08

## Change

One tableau saturation pass previously tested the complete TBox in the edge,
intersection, and global rules even though each rule accepts only a small set
of antecedent shapes. The edge rule also called `memCe` before its shape match
rejected the axiom.

The optimized implementation filters three order-preserving TBox subsets once
per pass:

- edge membership: `minCard`, `someOf`, `hasValue`, and `minQualCard`;
- conjunction membership: nonempty `intersection`;
- global injection: `owl:Thing` and the empty intersection.

All semantic checks within an accepted case are unchanged. `applyAxioms`
still receives the complete TBox because every antecedent can match a stored
label.

The readable workers remain specifications. A common theorem proves that
filtering inputs whose fold step is the identity preserves the exact left-fold
result. Specialized theorems prove equality for `applyAxiomsEdges`,
`applyAxiomsConj`, and `injectGlobalAxioms`. `onePassFiltered_eq` then proves
the complete optimized pass equal to `onePass`, including `RState`, Boolean
change result, list order, and fresh-name state. `@[csimp]` theorems select the
filtered implementations for compiled calls.

## Measurement

The input was `third_party/vocabularies/schemaorg-30.0-current-https.ttl`.
The native harness used the same parsed graph, closure, TBox, and initial
state for an explicit unfiltered pass and the filtered pass. It then timed the
compiled public `onePass` call. The temporary harness was removed after the
measurement.

```text
closure triples: 60,770
TBox axioms:       8,573
initial nodes:     4,912
edge subset:           0
conjunction subset:    0
global subset:         1

trial                  1       2       3     median
unfiltered pass     5,857   5,910   5,952      5,910 ms
filtered pass       2,979   2,887   2,814      2,887 ms
public onePass      3,015   2,854   2,839      2,854 ms
```

The controlled direct comparison reduces the median pass time by 51 percent,
or 2.05 times. The similar filtered and public timings confirm that the
compiled replacement fired. Every run produced 4,912 nodes and `changed =
true` on all three paths; the equality theorem establishes the complete state
equality that these runtime counters cannot show.

An earlier instrumented run split one 8.626-second pass into 3.868 seconds in
`applyAxioms`, 3.488 seconds in edge rules, 0.587 seconds in global rules, and
0.582 seconds in conjunction rules. That run used different instrumentation
and is not combined numerically with the controlled comparison above.

A QUDT first-pass timing is not reported. In the preceding phase benchmark,
QUDT initial label insertion had not completed after approximately 90 seconds,
so the run could not reach `onePass`. Optimizing that initialization is a
separate task.

## Validation and limits

`L4Factoidal.OWL.RefuteTests` and the OWL DL `type-inconsistency.rdf` catalog
were run after the change. The catalog reported 118 pass, 9 fail, 1 skip, and
zero cap hits from 128 cases. Its full `wall_ms=323159` is reported as a test
duration only: concurrent work and the newly merged nominal branching make it
unsuitable for isolating the TBox-filter speedup. The emitted C calls
`onePassFiltered` from `searchLoop`, which confirms that the production search
uses the proved replacement. A full Lake build is left to the merged root tree
because concurrent nominal and union changes touch the same module.

The new theorem axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`; the generic fold theorem uses only `propext`. No `sorry`, user
`axiom`, `native_decide`, `unsafe`, `@[implemented_by]`, new `partial`, or
trust option was added. This performance refinement does not change tableau
budgets, rules, or the existing graph-refuter soundness boundary tracked by
https://github.com/danbri/factoidal/issues/586.
