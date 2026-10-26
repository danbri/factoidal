# Forced nominal equality batching

Date: 2026-09-09

Tracking: https://github.com/danbri/factoidal/issues/651 and
https://github.com/danbri/factoidal/issues/586

## Problem

The nominal rule already preferred a label with one live member, but the
search applied only one such equality per state visit. Each visit then ran a
complete tableau pass over every node and TBox rule. The
`WebOnt-description-logic-502` encoding has several equality units exposed in
sequence, so deterministic identifications consumed both visit budget and
repeated whole-state saturation work.

## Change

`forcedNominalPairs` collects only complete nominal candidate lists with one
live equality. It preserves node, label, and member order. Multi-member lists
remain in `pendingNominal`, with every live alternative retained in the
existing depth-first merge frame.

When search reaches the same singleton-nominal arm as before, it applies the
selected equality and then runs `propagateForcedNominals`. A bounded loop
applies all currently forced equalities in source order and repeats because an
identification can expose another singleton. The fuel is the number of state
nodes plus the number of nominal member occurrences stored on those nodes.
Every productive sweep begins with two distinct representatives. If the bound
were exhausted, the function returns the current state and ordinary search can
continue on the next visit; exhaustion does not close a branch.

This deliberately changes rule scheduling and remaining-budget results:
several entailed equalities now share one semantic state visit. It is not an
exact compiled substitution for the former one-equality schedule. Genuine
nominal choices retain their source order and shared sibling budget.

The total search definition and `search_remaining_le` theorem are unchanged.
The generated C uses loops for the node fold, label fold, equality fold, and
fuel recursion; the new scans do not consume an input-sized native call stack.

## Checks

The build-time checks cover:

- a two-link forced equality cascade that clashes within two visits;
- its open satisfiable neighbour;
- exact forced-pair source order;
- the existing two-member nominal where the first branch clashes and the
  second remains open;
- the existing alias, grouped `differentFrom`, literal-member withholding,
  and multiple named `oneOf` controls;
- 25, 50, and 100 independent forced equalities, alongside the existing
  1,000, 2,000, and 4,000-member candidate collection guards.

`lake build L4Factoidal.OWL.RefuteTests l4owl-probe` passed. The printed
search proof dependencies remain `propext`, `Classical.choice`, and
`Quot.sound`.

An initial 100/200/400 forced-batch guard ladder made the Lean test-module
build take about 85 seconds. The committed guards use 25/50/100. This is
interpreter/build cost; neither ladder establishes native runtime scaling.

At `--refute-budget 64 --refute-ms 20000`, a focused native run of the real
`WebOnt-description-logic-502` catalog entry changed from a 20.02-second hard
timeout to a refutation in 15.70 seconds. The closure had 1,114 triples and the
tableau decided the inconsistency. `WebOnt-description-logic-504`, a different
encoding of the same problem, still reached an open branch and failed in 0.20
seconds; that is a semantic coverage gap rather than this visit-budget or
deadline problem.

The focused `WebOnt-description-logic-206` positive-entailment unit still hit
the 20-second refuter deadline. Its whole focused case took 26.68 seconds,
including closure. A standalone premise profile with 5,226 closure triples,
506 state nodes, and 2,438 TBox axioms measured the first tableau pass at
1.803 seconds: conjunction dispatch 0.967 seconds, edge dispatch 0.450,
ordinary/named axiom dispatch 0.272, and global constraints 0.077. Nominal
batching does not address that case. This standalone input differs from the
actual harness path, whose closure has 7,773 triples. Dispatch indexing is a
candidate, pending a profile of that actual input and a split of nonnamed
fallback scans from state-update cost.

These checks establish an executable scheduling improvement. They do not
establish SROIQ completeness, a model certificate for an open branch, or a
general refinement theorem from executable search to the declarative tableau.
