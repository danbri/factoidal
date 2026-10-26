# OWL refuter: total depth-first search

Date: 2026-09-08

Tracking: https://github.com/danbri/factoidal/issues/617 and
https://github.com/danbri/factoidal/issues/586

## Change

`L4Factoidal/OWL/Refute.lean` previously used a `partial def search` with
nested `tryAll` and `tryMerges` recursion. It is now a total fuel-indexed
`searchLoop`. An explicit continuation stack records the unvisited union
or merge siblings. Each state visit consumes one unit. Popping exhausted
frames consumes no semantic budget. An open branch or budget exhaustion
still stops the complete search immediately.

The first implementation rebuilt the union-label removal for every
sibling. The final implementation computes that base state once at the
branch point and reuses it. This preserves the source order and avoids a
repeated comparison with the complete disjunct list.

Four kernel-checked interface facts were added:

* `search_remaining_le`: returned budget is at most supplied budget;
* `search_zero`: zero budget returns `(out, 0)`;
* `search_immediate_clash`: an immediate clash with no continuation
  consumes exactly one state visit;
* `search_changed`: a changing saturation pass consumes one visit and
  continues from the updated state.

The change also fixes a soundness defect in qualified maximum-cardinality
merge selection. `≤ k p.C` now offers merges only between `p` successors
already proved to satisfy `C`. The former code offered all `p` successors
and could refute a satisfiable graph whose `C` extension was empty.

## Behaviour checks

A temporary native differential executable retained the replaced partial
algorithm only for the comparison. It was deleted after the run. Exact
`(Verdict, remaining budget)` results agreed for budgets 0, 1, 2, 3, 8,
16 and 40 on an open leaf, an all-clash union, a union with one open
branch, and the functional-property merge fixture. A nested union whose
first branch performs merge search also agreed:

| budget | old | total |
| ---: | --- | --- |
| 8 | `(out, 0)` | `(out, 0)` |
| 16 | `(clash, 2)` | `(clash, 2)` |
| 32 | `(clash, 18)` | `(clash, 18)` |
| 64 | `(clash, 50)` | `(clash, 50)` |

Permanent guards pin the union and merge boundary budgets. Paired
qualified-cardinality guards pin both directions: the empty-filler graph
returns `some true`; adding both filler memberships returns `some false`.
A `≤0 p.C` pair checks the same restriction.

`lake build L4Factoidal.OWL.RefuteTests l4owl-probe` passed. The axiom
audit for all four new theorems reports only `propext`,
`Classical.choice`, and `Quot.sound`.

The fresh `type-inconsistency.rdf` DL run was 116 pass, 11 fail, 1 skip,
0 unsupported out of 128, with zero refuter budget exhaustion. This is
the same score and disposition as the supplied baseline. The run took
3,611 ms and reported 67 cases decided by refutation.

The test-environment check found the OWL fixtures present. Unrelated XSD,
Xalan XSLT 1.0, Wycheproof, Solid CRUD, Solid WAC, and Solid specification
fixtures were absent. No result for those suites is claimed.

## Resource scaling

The emitted C for both `searchLoop` and `nextAfterClash` contains a
`_start` loop and `goto _start` at recursive transitions. No self-call
remains in either function. Search depth and exhausted-frame depth do not
consume one C stack frame per item.

A temporary native wide-union test used 50,000, 100,000 and 200,000
all-clash disjuncts with budgets 50,001, 100,001 and 200,001. All three
returned `(clash, 0)`. One run on Apple arm64 measured 19.1 ms, 33.3 ms,
and 45.6 ms. These are diagnostic single-run wall times, not a stable
throughput benchmark. They show successful n/2n/4n completion without
input-proportional stack growth.

## Limits

Totality does not establish SROIQ completeness. The search still has a
witness-depth cap of 3, a generated-witness cap of 6, a caller-supplied
visit budget, no general blocking result, and incomplete OWL construct
coverage. `search_remaining_le` is a resource invariant. It is not an
executable-to-`Refuted` certificate theorem. The general procedural
soundness and completeness connections remain tracked in issue 586.
