# OWL maximum-zero required successors — 2026-09-08

This correction belongs to the executable tableau work tracked in
https://github.com/danbri/factoidal/issues/586 and the OWL DL completion goal
at https://github.com/danbri/factoidal/issues/651.

## Counterexample

The public `owl-consistent` command returned `true` for this satisfiability
contradiction:

```text
p rdfs:subPropertyOf q
x : some p.C
x : max 0 q
```

The existential expansion created a required `p` edge. Role closure correctly
made it a `q` successor, but the edge carried `counts = false`. That flag
prevents a generated witness from being used as evidence for a positive
cardinality or for pairwise distinct successors. `clashForLabel` therefore
ignored the successor. `pendingMerge` saw it but could offer no pair for a
maximum of zero, and search incorrectly reached an open branch.

The original four public fixtures and outputs are preserved in
`/private/tmp/factoidal-dl-existential-maxzero-20260908/results.json`.

## Correction

A maximum of zero needs no distinctness premise: one required successor is
already too many. The zero cases of `maxCard` and `maxQualCard` now call
`successorsOf` with `counted = false`. Positive maximum cardinalities retain
the previous countable-successor and merge behavior. Qualified zero still
filters the result to successors whose filler label is known.

Two equations pin the exact executable behavior:

- `clashForLabel_maxCard_zero`
- `clashForLabel_maxQualCard_zero`

Both depend only on `propext`, `Classical.choice`, and `Quot.sound`. Regression
guards cover the subproperty contradiction, maximum-one SAT neighbor,
reversed-subproperty SAT neighbor, qualified matching-filler contradiction,
and qualified unrelated-filler SAT neighbor.

`lake build L4Factoidal.OWL.RefuteTests l4factoidal` passed 454 jobs. The four
public controls now return, in order, `false`, `false`, `true`, and `true` for
same-role contradiction, superproperty contradiction, maximum-one control,
and reversed-subproperty control.

This narrow rule does not license generated successors as pairwise distinct.
General minimum-cardinality and positive maximum-cardinality handling still
requires explicit distinctness evidence or a separately justified construction.
