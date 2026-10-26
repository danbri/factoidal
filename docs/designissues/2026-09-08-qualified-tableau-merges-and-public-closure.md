# Qualified tableau merges and the public closure path

Date: 2026-09-08. Findings on `0c331255b3a0fec0306b5459a944749364db891f`.
Tracking: [tableau soundness](https://github.com/danbri/factoidal/issues/586)
and [DL performance](https://github.com/danbri/factoidal/issues/549).

## A qualified cardinality counterexample

`Refute.mergePairsForLabel` handles `.maxQualCard k p _` by passing all
`p` successors to `witnessPairs`. It ignores the qualifying class. This
can force an identification that the ontology does not require.

The native Lean interpreter returned `some false` for this graph at
tableau budget 64:

```turtle
@prefix : <http://example.org/> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
:x a [ a owl:Restriction;
       owl:onProperty :p;
       owl:maxQualifiedCardinality "1"^^xsd:nonNegativeInteger;
       owl:onClass :C ];
   :p :a, :b .
:a a :A .
:b a [ owl:complementOf :A ] .
```

A model has domain `{x, a, b}`, distinct interpretations for these three
names, `A = {a}`, `C = {}`, and `p = {(x,a), (x,b)}`. The number of
`p` successors of `x` in `C` is zero, which satisfies the bound of one.
Both class assertions hold. The graph is satisfiable under the
[OWL 2 Direct Semantics cardinality definition](https://www.w3.org/TR/owl2-direct-semantics/#Class_Expressions).

The unqualified merge branch identifies `a` and `b`, pools `A` and
its complement, and reports a clash in every offered branch. That is
not a valid refutation because the original model requires no merge.

Repair: select only successors with established membership in the
qualifying class before testing the cardinality and generating merge
pairs. `successorsInFiller` already supplies this conservative selection
for the qualified clash rule. It can miss a required merge when membership
has not yet been derived; it cannot require a merge merely because an
unrelated successor exists.

Regression pairs must include the satisfiable graph above, the inconsistent
variant with both successors also in `C`, and qualified zero bounds with
and without established filler membership. The loop-preservation comparison
must isolate this intentional correction from the total-search refactor.

This finding also demonstrates why the sound declarative tableau theorem
does not certify the separate executable graph refuter. The missing bridge
is a practical correctness obligation.

## Parse limits must not create false refutations

Two further satisfiable inputs returned `some false` in fresh interpreter
checks against the baseline library:

1. `x` has a minimum qualified cardinality of 33 on `p`, with a filler
   enumeration of 64 different names. The RDF graph has 134 triples.
   A model chooses 33 distinct members of that enumeration as successors.
   `parseCeMarkers` instead reads a prefix of the RDF list at its small
   expression fuel, then treats that prefix as the whole enumeration.
   The nominal-size clash compares 33 with the truncated list length.
2. `x` has minimum cardinality 2 on `p.A` and maximum cardinality 1 on
   `p.B`, with each filler written under 40 complements. An even number
   of complements leaves each class unchanged. A model makes `A` contain
   two successors and `B` empty. The graph has 88 triples. Expression
   fuel exhaustion turns both distinct fillers into `unknown`, and
   `existsMaxQualLt` compares them with structural equality, which reports
   two `unknown` nodes equal.

The repairs are separate. RDF list reading must return a complete list
or an explicit failure, with a traversal bound justified by graph size.
A failure must not become a shorter enumeration. Semantic filler matching
must require definite expressions through `ceEq`; the structural equality
used for axiom deduplication has a different purpose and stays structural.

Regression pairs include 33-of-64 versus 65-of-64 cardinalities, malformed
and cyclic lists, distinct unknown fillers versus the same known filler,
and negated list expressions. These findings are a limit on the old claim
that every cap merely withholds refutations: that claim requires checking
how the capped parser's result is consumed.

## Public API closure differs from corpus execution

`Wasm/Ops/Reason.lean` calls `OWL.RL.closureFix` for public closure,
consistency, and entailment. This is the list implementation. The OWL
corpus probe calls `stepIO` / `closureIO` over the indexed rule functions.

The existing theorem `RLClosureIndexed.indexedClosure_eq` proves list
equality, including order, at every fuel. An indexed `closureFix` can
therefore use the existing fuel bound and a proved compiler substitution.
Replacing calls to `closure` in a later module does not by itself replace
an already compiled `closureFix`; verify the public operation's emitted C.

Baseline native CLI measurements, during concurrent agent builds:

| Input | Triples parsed | Parse wall seconds | Parse peak RSS bytes | OWL-RL closure |
| --- | ---: | ---: | ---: | --- |
| schema.org 30.0, 1,104,341 bytes | 17,949 | 0.42 | 278,626,304 | process killed at 30 s; no output |
| QUDT, 6,749,312 bytes | 130,404 | 2.59 | 1,820,360,704 | process killed at 30 s; no output |

The separate `owl-consistent --fuel 64` runs also exceeded 30 seconds on
both files. These are bounded baseline observations, not isolated-machine
throughput claims. Parse memory is a separate scaling limit. Each process
was bounded externally; no timed-out Lean task was left running.

The indexed path still needs measurement. This finding identifies a
concrete mismatch between tested and public execution; it does not establish
that indexing alone will meet the scale target.


## Witness freshness counterexample

The executable refuter also accepts unrestricted abstract `Graph` blank-node
identifiers. On 2026-09-08, alpha-renaming an unrelated input node to the
first generated witness identifier changed `tableauConsistent` from
`some true` to `some false`. The original graph says `x : ∃p.C` and
`_:victim : ¬C`. It has a model with two elements: assign the victim
outside C and choose the existential witness inside C.

Renaming the victim to `witnessId x p 0` makes `ensureWitnesses` reuse it.
The function checks existing generated edge objects but not the input
graph's nodes. The new C label clashes with the victim's asserted ¬C.
For `x = http://e/x` and `p = http://e/p`, the colliding identifier is
`_:tw_http://e/x__http://e/p__0`. Abstract blank-node identifiers do not
have a reserved generated namespace. The repair is a deterministic total
fresh-name search over input and branch state, with an alpha-renaming
regression guard. This remains within the executable soundness work at
https://github.com/danbri/factoidal/issues/586.


## Public entailment goal-name collision

A second fresh-name boundary is unsound in the pre-repair public entailment
path. The premise has `s rdf:type D` and an unrelated anonymous class
`_:unrelated owl:complementOf D`. It does not entail `s rdf:type C`: a
model can put s in D and outside C. The public command correctly returns
false. Renaming only that unrelated blank node to
`__factoidal_pe_neg_class` makes the command return true.

The negation-goal builder reuses that fixed identifier for the complement
of C. Appending the goal aliases it with the unrelated input class,
allowing the parser/refuter to derive a contradiction about D. The
`NegationGoals.lean` comment claiming that this prefix cannot occur in
parser output is false: the input is accepted N-Quads. Fixed prefixes
are not freshness guarantees for arbitrary input blank-node identifiers.

The paired public CLI inputs and outputs are retained in the scale
evidence. Repair must cover the premise, conclusion scaffolding, and
generated goal names in both the public API and corpus harness. This is
part of the executable soundness work in
https://github.com/danbri/factoidal/issues/586. The two outputs above are
a regression reproduction, not an acceptable entailment contract.

## Witness-depth exhaustion produces a false satisfiability verdict

The public `owl-consistent --fuel 64` path was tested on the family
`x : (exists p)^d.A` together with `x : (forall p)^d.not A`, for
depths 2, 3, 4, and 5. Every graph is inconsistent: the existential
requires a path of length d whose endpoint belongs to A, and the
universal restriction puts every such endpoint outside A. A paired
control replaces the final `not A` with A and has a finite path model.

The contradictions at depths 2 and 3 return false. At depths 4 and 5
they incorrectly return true. All four controls return true. These
are public Turtle inputs, not states fabricated outside the parser.
The fixtures, commands, and outputs are embedded in the scale evidence.

`ensureWitnesses` returns an unchanged state when `depthOf st i` reaches
`maxWitnessDepth = 3`, even if the existential remains unsatisfied.
After other rules become quiet, `searchLoop` returns `.open'`. The wire
operation presents that as `consistent: true`. Consequently, the cap
does more than withhold refutations: it can produce a false positive
satisfiability answer.

The immediate repair must preserve evidence of unresolved obligations
and return unknown when expansion stops before they are discharged.
Merely raising the cap moves the same counterexample to a larger depth.
Completion needs justified blocking and full obligation handling; an
unknown verdict is a correctness repair, not completion. See
https://github.com/danbri/factoidal/issues/586 and
https://github.com/danbri/factoidal/issues/651.

## Required witnesses and a zero bound on a superproperty

Another public false satisfiability result survives below the depth
boundary. Let `p rdfs:subPropertyOf q`, and assert that x belongs to
both `exists p.C` and `max 0 q`. The existential requires a p edge,
which must also be a q edge, contradicting the zero bound. The public
command returns true. Replacing q in the bound with p returns false.
The paired `max 1 q` and reversed-subproperty controls return true
and both have one-edge models.

Generated existential edges have `counts = false`. The maximum-zero
clash uses only counted successors and misses the required edge. The
merge path sees one successor above zero, but there is no pair to
merge, and an empty pair list is treated as no pending merge. Unlike
a positive maximum, detecting violation of a zero bound requires no
pairwise-distinctness evidence: one required successor is enough.
The same review applies to qualified zero bounds with a known filler.

Fixtures, commands, and outputs are retained in the scale evidence.
This is another executable soundness/decision-contract defect under
https://github.com/danbri/factoidal/issues/586; returning unknown at the
depth limit does not repair it. The next witness/cardinality change
must preserve satisfiable subproperty-direction and maximum-one
controls while closing this contradiction.


## Untyped subjects and global functionality

A functional datatype property `id`, its subproperty `name`, and
`x id "T000-01"; name "BOOLEAN"` are inconsistent because the two
strings denote distinct values. The public refuter currently returns true
unless `x` also has a type assertion. This was found while reducing the
QUDT initial clash. `initState` seeds nodes from types and nominal members;
`injectFunctional` visits only those nodes. Global constraints must also
reach relevant untyped subjects. Equality-of-values and nonfunctional
controls both have models and return true. This is an outstanding
[completion defect](https://github.com/danbri/factoidal/issues/651), with
all six probe inputs and outputs in the scale evidence JSON.
