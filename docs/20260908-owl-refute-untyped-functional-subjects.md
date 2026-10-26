# OWL refuter: untyped assertion subjects

Date: 2026-09-08

## Problem

`initState` created tableau nodes only for subjects of `rdf:type`
triples. Global property rules iterate over those nodes. Consequently,
an untyped subject with two value-distinct assertions of a functional
data property could escape `injectFunctional`. The same happened when
one assertion used a subproperty of the functional property.

The minimized QUDT-shaped case is:

```turtle
qudt:id a owl:DatatypeProperty, owl:FunctionalProperty .
qudt:ansiSQLName rdfs:subPropertyOf qudt:id .
datatype:BOOLEAN qudt:id "T000-01" ;
                 qudt:ansiSQLName "BOOLEAN" .
```

The two strings are distinct values, so functionality makes this graph
inconsistent even though `datatype:BOOLEAN` has no asserted type.

## Change

The explicit `initState` specification now creates an empty node for
every RDF graph subject, in first-subject-appearance order, before it
adds parsed `rdf:type` labels in their original order. RDF subjects
denote resources, so global property characteristics apply to them
whether or not a type assertion is present.

`InitialLabelBuilder.addSubject` implements this grouping with the
existing subject array and hash map. The executable
`initStateIndexed` uses the builder. The following theorems connect it
to the list specification and the public state constructor:

- `InitialLabelBuilder.addSubject_wf`
- `InitialLabelBuilder.addSubject_nodes`
- `InitialLabelBuilder.foldSubject_nodes`
- `InitialLabelBuilder.foldSubject_wf`
- `initialGraphNodesIndexed_eq_spec`
- `fold_ensureInitialSubjects`
- `indexedInitialState_eq_graphFold`
- `initStateIndexed_eq`

The `@[csimp] initState_eq_indexed` replacement therefore still has an
exact proved specification bridge. No search rule, budget, or
three-valued result boundary changed.

## Validation

`lake build L4Factoidal.OWL.RefuteTests` passed 28 jobs. The new guards
cover the untyped functional/subproperty contradiction and satisfiable
neighbors with equal literal values, a nonfunctional superproperty,
and assertions on different subjects.

`#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound` for every new proof and for the existing final compiler
substitution theorems.

## QUDT diagnostic note

The earlier phase harness called `indexedClosure input 100`; the public
diagnostic calls `indexedClosureFix input`, whose fuel is
`closureFuelBound input`. This is a verified code-path difference. It
does not by itself establish that the two QUDT closure graphs differ;
graph equality and relevant membership require a separate measurement.

The executable refuter still has no general model-theoretic soundness
bridge from graph search to OWL interpretations; that existing boundary
is tracked in [tableau soundness](https://github.com/danbri/factoidal/issues/586).


Follow-up, 2026-09-09: a fresh single-input comparison produces 638,420
triples for both closure fuel 100 and the public bound, with exact list-order
equality. Both initial states clash on current source. The earlier false
clash measurement is not reproduced; its exact cause is not established.
Source and copied tool output are preserved in the completion evidence JSON.
