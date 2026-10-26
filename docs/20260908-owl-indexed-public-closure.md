# Indexed OWL RL closure on the public Lean path

Date: 2026-09-08

Tracking: https://github.com/danbri/factoidal/issues/586

## Change

`OWL.RL.closureFix` remains the list-backed specification used by existing
proofs. `OWL.RL.indexedClosureFix` applies the already proved indexed engine
at the same `closureFuelBound`. The new `@[csimp]` theorem
`closureFix_eq_indexedClosureFix` proves equality of the complete public
functions from `indexedClosure_eq`.

`Wasm/Ops/Reason.lean` now imports `RLClosureIndexed` before defining
`owlClosure`, `owlIsConsistent`, and `owlEntails`. Lean code in these public
operations continues to call `closureFix`; code generation replaces that
call with the exactly equal indexed implementation.

## Proof and build checks

`lake build L4Factoidal.OWL.RLTests Wasm.Ops.Reason l4factoidal` passed.
The axiom audit for `closureFix_eq_indexedClosureFix` reports only
`propext`, `Classical.choice`, and `Quot.sound`. A permanent executable
guard also compares `indexedClosureFix` with `closureFix` on the existing
equality fixture.

The emitted `Wasm/Ops/Reason.c` calls `indexedClosureFix` in all three OWL
public operations. It has no call to the list-backed OWL `closureFix`.
The separate RDFS operation still calls the RDFS closure as designed.

Public `owl-entails` controls used a class assertion `x:C`, the axiom
`C rdfs:subClassOf (A owl:unionOf B)`, and `x:not A`. The RL closure did
not contain `x:B`; the DL refutation path returned `true` for `x:B`.
An unrelated `x:D` conclusion returned `false`, which excludes an
inconsistent-premise shortcut. `owl-consistent` returned `true` for the
same premise. Each control completed in about 0.05 seconds.

The DL `type-inconsistency.rdf` catalog remained 116 pass, 11 fail,
1 skip, 0 unsupported out of 128, with no budget exhaustion. This catalog
already uses the indexed harness closure, so it is a semantic regression
check rather than evidence for the public code-generation substitution.

## Corpus measurements

The previous public list-closure binary exceeded a 30-second timeout on
both measured ontologies. The newly built public binary completed both:

| ontology | input triples | previous closure | indexed public closure |
| --- | ---: | ---: | ---: |
| schema.org 30.0 | 17,949 | more than 30 s | 9.23 s |
| QUDT all-in-one | 130,404 | more than 30 s | 88.17 s |

Commands used the native `l4factoidal closure` operation with Turtle input
and `--regime owl-rl`, and discarded serialized closure output. These are
single wall-clock runs on Apple arm64. The operating-system timing command
could not report peak RSS in the restricted environment, so no memory
comparison is claimed. The old runs had concurrent builds and establish
only the recorded timeout floor; they do not support a precise speedup
ratio.

## Limits

The indexed engine still performs naive whole-store rounds. This change
does not implement semi-naive deltas or change `closureFuelBound`. The proof
establishes exact list equality for every input and fuel; it does not expand
the represented OWL RL rules. The DL refuter's soundness and completeness
boundaries remain tracked in issue 586.
