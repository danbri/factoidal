# OWL refuter indexed initial labels, 2026-09-08

## Scope

`Refute.initState` previously inserted every parsed `rdf:type` label through
`addLabel`.  The state initially has no node identifications, but each insertion
still scanned and rebuilt the growing node list.  This made initial label
grouping quadratic in the number of typed subjects.

The replacement keeps first-subject order in an `Array Subject` and stores each
subject's append-order labels in a `Std.HashMap`.  It preserves the existing
`memCe` check, including its deliberate refusal to identify class expressions
with indefinite components, and still drops a top-level `ClassExpr.unknown`.
The array is converted to the ordinary `List RNode` before
`seedNamedOneOfMembers`; no index is added to mutable tableau state.

## Equality argument

`initialLabelNodesSpec` is the list-fold specification of initial grouping.
The public `initState` definition retains its original graph fold through
`addLabel`; the proof does not replace that specification.  The bridge from
that original definition is:

- `addLabel_initial` proves one `addLabel` update equals one node-list
  specification update when the state has no identifications.
- `fold_addLabel_initial` lifts this equality through all parsed type entries
  while preserving every other `RState` field.
- `fold_initialLabelEntries` proves that folding the filtered parsed entries is
  equal to the original fold directly over graph triples.

`InitialLabelBuilder.WF` states that the subject array is duplicate-free and
has exactly the HashMap's domain.  The following kernel-checked chain connects
the implementation to the specification:

- `InitialLabelBuilder.add_wf` preserves the invariant.
- `InitialLabelBuilder.add_nodes` proves one indexed update has the same node
  list as one specification update.
- `InitialLabelBuilder.fold_nodes` lifts the equality over every input list.
- `initialLabelNodesIndexed_eq_spec` proves equality from the empty builder.
- `indexedInitialState_eq_graphFold` joins both proof chains at the exact old
  graph fold.
- `initStateIndexed_eq` lifts that equality through named-oneOf seeding.
- `initState_eq_indexed` is the `@[csimp]` replacement used by compiled code.

`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for
these proofs.  The change adds no `sorry`, user axiom, `native_decide`,
`unsafe`, `implemented_by`, or partial definition.

## Fresh measurements

Measurements used a temporary native Lake executable which parsed Turtle,
ran `RL.indexedClosure` with fuel 100, and timed the initialisation functions.
The temporary source and Lake target were removed after measurement.  These
runs were made after the laptop resumed and exclude wall times spanning its
offline interval.

On `third_party/vocabularies/schemaorg-30.0-current-https.ttl`, the input had
17,949 triples, the closure had 60,770 triples, and each implementation
produced 4,912 nodes.  Three fresh native runs gave:

| Implementation | Run 1 | Run 2 | Run 3 | Median |
| --- | ---: | ---: | ---: | ---: |
| list specification | 1,032 ms | 1,048 ms | 1,032 ms | 1,032 ms |
| indexed implementation | 269 ms | 267 ms | 269 ms | 269 ms |
| public `initState` after `@[csimp]` | 274 ms | 272 ms | 276 ms | 274 ms |

On `third_party/qudt/QUDT-all-in-one-OWL.ttl`, the input had 130,404 triples,
the closure had 638,420 triples, and both the indexed implementation and public
`initState` produced 12,719 nodes.  One fresh native run took 2,771 ms for the
indexed implementation and 2,774 ms for public `initState`.  The quadratic list
specification was deliberately not rerun on QUDT after resume.

These times isolate state initialisation after closure.  They do not measure a
full public consistency request or claim OWL DL completeness.

The generated C for `tableauConsistent` calls `initStateIndexed`, confirming
that the compiled public reasoning path uses the proved replacement.

## Validation

From `formal/lean4/`:

```text
lake build L4Factoidal.OWL.Refute
lake build L4Factoidal.OWL.RefuteTests
```

Both targets passed.  `RefuteTests` includes a focused guard for first-subject
order, per-subject label order, duplicate handling, ignored top-level unknown,
and retained duplicates whose indefinite components make `ceEq`
non-reflexive.  Full-catalog and full-project builds remain integration checks
for the merged tree because other agents were changing search and union logic
in parallel.
