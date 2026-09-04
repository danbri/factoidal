# B1: a conclusion that restates a class expression

Date: 2026-09-04. Companion to
[`2026-09-03-owl-failure-split.md`](2026-09-03-owl-failure-split.md),
which measured sub-bucket B1 at 56 RL units and 58 `--dl` units and left
the design question open. This document answers it.

Tracked in <https://github.com/danbri/factoidal/issues/404>.

Measured baseline, worktree `agent-abfe56648fe8c729b`, binary
`formal/lean4/.lake/build/bin/l4owl-probe`, corpus
`third_party/testing/owl`, per-closure cap 30000 ms: RL closure only
1138 pass, 309 fail, 2 skip, 8 unsupported (out of 1457). The `--dl`
line is in the landing table in section 7.

## 1. What B1 is, from three test files read from disk

The probe's positive-entailment check is triple containment with a
per-triple blank-node wildcard (`OwlProbe.tripleMatches`): a blank node
in the conclusion matches ANY term at that position, the predicate must
be equal. So a reported `missing _:b0 <P> _:b1` proves that the closure
holds **no triple at all with predicate P**.

**(a) `WebOnt-Class-006`** (`type-positive-entailment.rdf`).
Premise: `premises006#x rdf:type owl:Thing` and
`premises006#c rdf:type owl:Class` — two triples.
Conclusion: `x rdf:type _:u`, `_:u rdf:type owl:Class`,
`_:u owl:unionOf _:l`, the list cell `_:l rdf:first c`,
`_:l rdf:rest _:l2`, `_:l2 rdf:first _:n`,
`_:n owl:complementOf c`. First triple the engine fails to produce:
`_:b0 owl:unionOf _:b1`. The closure has no `owl:unionOf` triple; the
premise has none either. The entailment is the law of excluded middle,
`x : c ⊔ ¬c`.

**(b) `WebOnt-unionOf-003`** (`type-positive-entailment.rdf`).
Premise: `A owl:oneOf (a)`, `B owl:oneOf (b)`,
`A-and-B owl:oneOf (a b)`.
Conclusion: `A-and-B owl:unionOf (A B)`.
First missing triple: `premises003#A-and-B owl:unionOf _:b1`. The
subject is a NAMED class here, so this is not a blank-node labelling
question; the closure has no `owl:unionOf` triple.

**(c) `New-Feature-SelfRestriction-002`** (`profile-EL.rdf`,
`profile-QL.rdf`, `profile-RL.rdf`).
Premise: `likes rdf:type owl:ObjectProperty`, `Peter likes Peter`.
Conclusion: `Peter rdf:type _:r`, `_:r rdf:type owl:Restriction`,
`_:r owl:onProperty likes`, `_:r owl:hasSelf "true"^^xsd:boolean`.
The closure has no `owl:Restriction` scaffolding at all. The
`cls-hs1`/`cls-hs2` rows landed on 2026-09-03 do not close it, as that
landing's own note records.

In all three the conclusion asks for class-expression SCAFFOLDING that
no rule row of the OWL 2 RL tables produces.

## 2. The two routes named in the split, stated precisely

**Route 1 — comprehension.** Add rules that mint the class-expression
term the conclusion asks for: from `c ∈ IC` derive a fresh `z` with
`z owl:complementOf c`, from a list of classes derive a fresh `z` with
`z owl:unionOf` that list, and so on. This is the OWL 2 RDF-Based
Semantics comprehension condition family, e.g. for union:

> "if _s_ sequence of _c1_ , … , _cn_ ∈ IC then ∃ _z_ ∈ IC :
> ( _z_ , _s_ ) ∈ IEXT(_I_(owl:unionOf))"
> — OWL 2 RDF-Based Semantics, §8

Stated over all sequences it is infinitary, so an implementation must
bound it to the vocabulary present, and the bound must be defended.

**Route 2 — a conclusion matcher modulo blank-node structure.** Keep
the engine and change the check: hold the entailment when the
conclusion graph maps into the closure under ONE blank-node mapping,
which is RDF simple entailment:

> "G simply entails a graph E if and only if a subgraph of G is an
> instance of E." — RDF 1.1 Semantics, interpolation lemma

## 3. Which one the conformance definition asks for

Neither. The W3C definition is model-theoretic, over ONTOLOGIES, not
over triples:

> "Entailment tests (or positive entailment tests) specify two ontology
> documents: a premise ontology document d1 and a conclusion ontology
> document d2 where Ont(d1) entails Ont(d2) with respect to the
> specified semantics."
> — OWL 2 Conformance, test types

> "Each semantic test case also specifies whether it is applicable to
> the Direct Semantics, to the RDF-Based Semantics, or to both. A test
> is only relevant for testing conformance of tools that use a
> semantics to which the test applies."
> — OWL 2 Conformance

Three consequences, in order of force.

**(i) Route 2 cannot close a single B1 unit, and this is a measurement,
not an argument.** The harness's present rule already treats a
conclusion blank node as matching any term, INDEPENDENTLY per triple.
Any single consistent blank-node mapping is one of the assignments that
rule already admits, so the interpolation-lemma check is strictly
STRONGER than the check in the tree today. Every B1 failure reports a
missing triple whose predicate is absent from the closure, which no
mapping repairs. Route 2 would therefore lose passes, not gain them.
It is still the correct reading of the mapping question — the present
per-triple rule is unsound in the permissive direction, because it lets
`_:x rdf:type C` and `_:x rdf:type D` be witnessed by two different
individuals — and that soundness gap is recorded in section 6 as a
separate finding. It is not a fix for B1.

**(ii) Route 1 implements conditions the specification has withdrawn
from the normative set.**

> "One important change is that while so called *"comprehension
> conditions"* for the OWL 2 RDF-Based Semantics (see Section 8) still
> exist, these are *not* part of the normative set of semantic
> conditions anymore."
> — OWL 2 RDF-Based Semantics, introduction

> "8 Appendix: Comprehension Conditions (Informative)"
> — its section heading

An engine that mints class-expression terms derives triples that are
not OWL 2 RDF-Based entailed by the normative conditions. That does not
make route 1 useless — it makes any rule row built on it a row whose
soundness theorem must carry the comprehension hypothesis explicitly,
which this repository already anticipated in
[`2026-07-29-rdf-based-semantics-formalization.md`](2026-07-29-rdf-based-semantics-formalization.md)
(bucket E, "*Comprehension-dependent rules*: sound only under the
RDF-Based appendix's **informative** comprehension conditions").

**(iii) Under the Direct Semantics the conclusion is a set of AXIOMS,
and entailment of an axiom is decided by refutation.** The conclusion
of `WebOnt-Class-006` maps to the single axiom
`ClassAssertion(ObjectUnionOf(c, ObjectComplementOf(c)), x)`. Its class
expression is structure INSIDE an axiom, not triples that any closure
must contain. `Ont(d1) ⊨ Ont(d2)` holds iff `Ont(d1) ∪ ¬Ont(d2)` is
unsatisfiable, and an unsatisfiability verdict is exactly what the
tableau refuter already returns for the InconsistencyTest line in
`--dl` mode.

## 4. Recommendation

**Route 3: positive entailment by refutation, in the `--dl` regime, as
a FALLBACK after the containment check fails.** It is the conformance
notion for every test whose `test:semantics` includes DIRECT, it adds
no new trusted component (the refuter's "unsatisfiable" verdict is
already trusted by the InconsistencyTest line), and the machinery is
already in the tree and unused:

- `formal/lean4/L4Factoidal/OWL/NegationGoals.lean` — `negationGoals`,
  a landed port of `formal/fstar/Tableau.Refute.fst` §11a/11b, with the
  soundness contract in its header: each content assertion of the
  conclusion is negated SEPARATELY, an equivalence expands to two
  subsumption goals, an unsupported shape collapses to `none`.
- `formal/lean4/L4Factoidal/OWL/Refute.lean` — `tableauConsistent`.
- `grep` over `formal/lean4` finds NO caller of `negationGoals` outside
  its own file. `Harness/OwlProbe.lean` does not import it. Its own
  header names "the PE-via-refutation fallback through the DL tableau"
  as a not-ported F\* refinement; the library half was ported and the
  harness half was not.

The check landed is: the entailment holds when
`negationGoals gConclusion` returns goals and
`Refute.tableauConsistent (closure ++ goal) budget = some false` for
EVERY goal. `some true` or `none` on any goal leaves the original
containment verdict in place. That is a strictly ADDITIVE check: no
test that passes today can fail because of it.

**One correctness obligation this raises, and how it is discharged.**
The probe parses every document on its own, so a conclusion blank node
`_:b0` and a closure blank node `_:b0` are unrelated but equal as
labels. Feeding `closure ++ goal` to the refuter without renaming
would conflate them and could produce a clash for the wrong reason —
a FALSE pass. The conclusion graph's blank nodes are therefore renamed
under a reserved prefix before `negationGoals` sees them.

**What would falsify the recommendation.**

1. A NegativeEntailmentTest that fails after the change. It cannot
   happen by construction (the change is inside `judgePositive`), and
   the count is gated at every commit; a fail would mean the change
   escaped its scope.
2. A PositiveEntailmentTest passing through the fallback whose premise
   does not in fact entail its conclusion. The tell is a case that
   refutes even with the conclusion's content assertion REMOVED —
   i.e. the premise closure alone is inconsistent. Any such case is a
   fallback that proved nothing, and the fallback must then be gated on
   the premise being consistent.
3. The refuter answering `some false` on `closure ++ goal` where the
   goal's blank-node renaming was the only reason for the clash. The
   rename above is what forecloses this; if a pass disappears when the
   reserved prefix is changed, the pass was an artifact.

## 5. Cost and risk of each route

| Route | Cost | Risk |
|---|---|---|
| 1 — comprehension | A new rule family, a termination bound to defend, and every soundness theorem carrying an informative-condition hypothesis | Derives triples the normative semantics does not entail; the bound is a new place for the closure to blow up |
| 2 — mapping check | Small; a subgraph-instance search over the closure | Closes nothing in B1, and correctly implemented it REMOVES passes the present per-triple rule grants |
| 3 — refutation (recommended) | Wiring only; both halves are landed | Refuter budget exhaustion returns `none` and costs nothing; a blank-node collision would be a false pass, foreclosed by the rename |

## 6. Findings recorded, separate from the fix

- **The harness's blank-node rule is unsound in the permissive
  direction.** `tripleMatches` admits a different witness per triple,
  so a conclusion `_:x rdf:type C . _:x rdf:type D` passes on a closure
  holding `a rdf:type C` and `b rdf:type D`. The interpolation lemma
  asks for one mapping. This is not fixed here — fixing it can only
  reduce the score and belongs with a measurement of which units it
  costs.
- **NegativeEntailmentTest and PositiveEntailmentTest are not duals in
  this harness.** PE gets the refutation fallback; NE keeps "at least
  one non-conclusion triple is missing". A premise that DOES entail its
  non-conclusion by refutation would still be scored PASS. The dual
  check is not landed here because it can only remove passes, and it
  needs its own measurement.

## 7. Landings measured against this decision

Filled in per commit, RL and `--dl`, labelled.
