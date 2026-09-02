---
title: "OWL reasoning by model construction: the tableau"
description: "A model-construction reasoner that classifies individuals into OWL class expressions the Datalog closure cannot reach — someValuesFrom, hasValue, and an unsatisfiable restriction caught as an inconsistency — plus an honest, measured account of what it does not cover."
layout: hub.njk
series: docs-hub
series_order: 30
vocab: none
status: published
tests: tests/hub/post30_test.mjs
---

[Post 3](./03-schemas-that-infer-rdfs-owl.md) derived new triples by
Datalog closure: a fixed set of rules fired forward over the asserted
triples until nothing new appeared. That is OWL 2 **RL** — fast,
complete for the rules it has, and blind to everything outside them. A
**tableau** reasoner works the other way round: instead of firing rules
forward, it tries to *build a model* — a concrete interpretation that
satisfies every axiom — and reports what must hold in every such model.
Where RL asks "which rule fires next?", the tableau asks "can I
construct a world where this individual is *not* a member of this class,
without contradiction?" — and when it cannot, membership is entailed.

Both live in this engine because they cover different ground. RL cannot
recognise that an individual belongs to `∃hasChild.Doctor` (the
existential direction is outside the RL rule set); the tableau can. The
tableau is slower and narrower in other places (below). Factoidal runs
them as two entailment regimes — tagged **[RL]** and **[DL]** on the
[test-results dashboard]({{ '/test-results/' | url }}) — with the DL
regime layering the tableau between two RL passes so a DL answer is
never weaker than the RL one. The reasoner is
[`formal/fstar/Tableau.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/Tableau.fst):
verified F\*, no `assume val`, no `--lax`.

The cells below call the tableau through the npm surface —
`fn.tableauMaterialise` (add the memberships the tableau proves),
`fn.tableauDlInconsistent` (the DL consistency verdict),
`fn.owlIsConsistent` (a three-valued consistency verdict straight from
the clash-detecting refuter), and `fn.owlEntails` (does a premise entail
a conclusion, by closure or by refuting the negated conclusion).

## Covered: existential classification

`ParentOfDoctor` is defined as `∃hasChild.Doctor` — anyone with some
child who is a doctor. Alice is never asserted to be a `ParentOfDoctor`;
she is only asserted to have a child, Bob, who is a doctor.

```observable-js
someValuesOntology = `
@prefix : <http://example.org/> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
:hasChild a owl:ObjectProperty .
:Doctor a owl:Class .
:ParentOfDoctor a owl:Class ;
  owl:equivalentClass [ a owl:Restriction ;
      owl:onProperty :hasChild ;
      owl:someValuesFrom :Doctor ] .
:Alice a owl:NamedIndividual ; :hasChild :Bob .
:Bob a :Doctor , owl:NamedIndividual .
`
```

```observable-js
someValuesMaterialised = await fn.tableauMaterialise(someValuesOntology)
```

```observable-js
parentOfDoctorMembers = (await fn.query(someValuesMaterialised.dataset, `# Individuals typed as the anonymous restriction equivalent to :ParentOfDoctor.
  PREFIX : <http://example.org/>
  PREFIX owl: <http://www.w3.org/2002/07/owl#>
  SELECT ?who WHERE {
    ?who a ?restriction .
    :ParentOfDoctor owl:equivalentClass ?restriction .
    ?restriction owl:someValuesFrom :Doctor .
  }`)).map((row) => row.get("who").value)
```

`someValuesMaterialised.addedCount` reports how many `rdf:type`
memberships the tableau added; the query then finds who is now a member
of the class `ParentOfDoctor` is equivalent to. It returns
`http://example.org/Alice` — a classification the RL closure over the
same graph does not make, because recognising membership from an
`owl:someValuesFrom` restriction is the existential direction RL omits.

## Covered: value restrictions

`hasValue` is the other constructor a plain closure will not classify
from: `BritishCitizen ≡ ∃nationality.{UnitedKingdom}` — anyone whose
`nationality` is the specific individual `UnitedKingdom`.

```observable-js
hasValueOntology = `
@prefix : <http://example.org/> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
:nationality a owl:ObjectProperty .
:UnitedKingdom a owl:NamedIndividual .
:BritishCitizen a owl:Class ;
  owl:equivalentClass [ a owl:Restriction ;
      owl:onProperty :nationality ;
      owl:hasValue :UnitedKingdom ] .
:Alice a owl:NamedIndividual ; :nationality :UnitedKingdom .
`
```

```observable-js
hasValueMaterialised = await fn.tableauMaterialise(hasValueOntology)
```

```observable-js
britishCitizens = (await fn.query(hasValueMaterialised.dataset, `# Individuals typed as the anonymous restriction equivalent to :BritishCitizen.
  PREFIX : <http://example.org/>
  PREFIX owl: <http://www.w3.org/2002/07/owl#>
  SELECT ?who WHERE {
    ?who a ?restriction .
    :BritishCitizen owl:equivalentClass ?restriction .
    ?restriction owl:hasValue :UnitedKingdom .
  }`)).map((row) => row.get("who").value)
```

Alice is classified as a member of `BritishCitizen` from her
`nationality` value alone.

## Covered: an unsatisfiable restriction, caught

A class `∃hasChild.owl:Nothing` — "has some child who is a member of the
empty class" — cannot have members: `owl:Nothing` has none, so no child
can be one. Asserting an individual into it is a contradiction. The
tableau constructs the required child-in-`owl:Nothing` witness, which
lands as an `rdf:type owl:Nothing` membership, and the consistency check
sees it.

```observable-js
unsatisfiableOntology = `
@prefix : <http://example.org/> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
:hasChild a owl:ObjectProperty .
:Alice a owl:NamedIndividual ,
    [ a owl:Restriction ;
      owl:onProperty :hasChild ;
      owl:someValuesFrom owl:Nothing ] ;
  :hasChild :Bob .
:Bob a owl:NamedIndividual .
`
```

```observable-js
inconsistencyVerdict = await fn.tableauDlInconsistent(unsatisfiableOntology)
```

`inconsistencyVerdict` reports `{ inconsistent: true, rlAlone: true }`:
the DL pipeline (RL closure → tableau materialisation → RL closure →
inconsistency check) flags the contradiction — and, since the RL
closure grew its comprehension-witness layer (2026-08), the plain
OWL-RL verdict on this graph now flags it too: membership in a
`someValuesFrom` restriction on `owl:Nothing` is a clash the witness
machinery reaches without a tableau. Harder `WebOnt-Restriction`
shapes still separate the two — the tableau constructs witnesses the
Datalog closure cannot, and those cases are why the DL regime exists.

## Consistency by refutation: a verdict and its clash families

`fn.owlIsConsistent(ontology)` runs the clash-detecting refuter
([`formal/fstar/Tableau.Refute.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/Tableau.Refute.fst))
over the OWL-RL closure and reports a **three-valued** verdict:
`consistent: false` when a clash closes every branch, `true` when a model
is built with no clash, and `consistent: null` when the refuter's linear
budget runs out before it decides — an indeterminate result that is
never reported as `false`. This is the pure verified chain the OWL
runner uses under `--regime dl`; the runner's native z3 counting oracle
is not on this path (a browser cannot spawn z3), so every verdict here
comes from the extracted tableau alone.

Edit the ontology below and re-run it: a class that is both `:Cat` and
`:Dog` where the two are `owl:disjointWith` cannot have members.

```observable-js
disjointClassesOntology = `
@prefix : <http://example.org/> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
:Cat a owl:Class . :Dog a owl:Class .
:Cat owl:disjointWith :Dog .
:Felix a owl:NamedIndividual , :Cat , :Dog .
`
```

```observable-js
disjointClassesVerdict = await fn.owlIsConsistent(disjointClassesOntology)
```

`disjointClassesVerdict` is `{ consistent: false, reason: … }` — the
`reason` string is the refuter's plumbing-level account of the verdict
(there is no full clash trace in the verified core; the `reason` reports
which stage decided). The next two ontologies are different clash
families the same refuter closes.

A cardinality contradiction — `:Sam` is asserted into a class needing at
least two `:knows` edges and a class allowing at most one, over the same
property:

```observable-js
cardinalityClashOntology = `
@prefix : <http://example.org/> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
:knows a owl:ObjectProperty .
:Sociable a owl:Class ; owl:equivalentClass [ a owl:Restriction ;
    owl:onProperty :knows ; owl:minCardinality "2"^^xsd:nonNegativeInteger ] .
:Hermit a owl:Class ; owl:equivalentClass [ a owl:Restriction ;
    owl:onProperty :knows ; owl:maxCardinality "1"^^xsd:nonNegativeInteger ] .
:Sam a owl:NamedIndividual , :Sociable , :Hermit .
`
```

```observable-js
cardinalityClashVerdict = await fn.owlIsConsistent(cardinalityClashOntology)
```

A functional-property contradiction — a functional `:hasSSN` cannot point
at two individuals declared `owl:differentFrom` each other:

```observable-js
functionalClashOntology = `
@prefix : <http://example.org/> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
:hasSSN a owl:FunctionalProperty , owl:ObjectProperty .
:Alice a owl:NamedIndividual ; :hasSSN :N1 , :N2 .
:N1 a owl:NamedIndividual . :N2 a owl:NamedIndividual .
:N1 owl:differentFrom :N2 .
`
```

```observable-js
functionalClashVerdict = await fn.owlIsConsistent(functionalClashOntology)
```

And a satisfiable control — an ordinary graph with no contradiction — so
the `true` verdict is not just the absence of a test:

```observable-js
satisfiableOntology = `
@prefix : <http://example.org/> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
:hasChild a owl:ObjectProperty . :Doctor a owl:Class .
:Alice a owl:NamedIndividual ; :hasChild :Bob .
:Bob a :Doctor , owl:NamedIndividual .
`
```

```observable-js
satisfiableVerdict = await fn.owlIsConsistent(satisfiableOntology)
```

The summary cell collects the four verdicts — three clash families that
close, one control that stays open:

```observable-js
clashFamilySummary = [
  { family: "disjoint classes", consistent: disjointClassesVerdict.consistent,
    reason: disjointClassesVerdict.reason ?? "" },
  { family: "min/max cardinality", consistent: cardinalityClashVerdict.consistent,
    reason: cardinalityClashVerdict.reason ?? "" },
  { family: "functional property", consistent: functionalClashVerdict.consistent,
    reason: functionalClashVerdict.reason ?? "" },
  { family: "satisfiable control", consistent: satisfiableVerdict.consistent,
    reason: satisfiableVerdict.reason ?? "" }
]
```

### The budget-out is not a false

The refuter's search is bounded by a linear fuel budget. When the budget
is too small to close every branch the verdict is `null`, and the
`reason` names the exhausted cap — the reasoner reports "I did not
decide", never a silent "consistent". Re-running the disjoint-classes
ontology with `fuel: 0` forces that path:

```observable-js
budgetOutVerdict = await fn.owlIsConsistent(disjointClassesOntology, { fuel: 0 })
```

`budgetOutVerdict` is `{ consistent: null, reason: … }` — the same
ontology the default budget reports as `false`. Raising `opts.fuel`
past the search depth turns the `null` back into the decided verdict.

## Entailment: closure first, refutation second

`fn.owlEntails(premise, conclusion)` answers "does the premise entail the
conclusion?" by the same two-regime dispatch the OWL runner's
positive-entailment path uses. It first checks whether the conclusion is
already in the OWL-RL closure of the premise (`via: "closure"`); if not,
it negates the conclusion and asks the refuter whether premise-plus-
negation is inconsistent (`via: "refutation"`). Here the conclusion is
`:Alice a :ParentOfDoctor` — a `someValuesFrom` classification the
closure never makes, so the entailment is decided by refuting its
negation:

```observable-js
entailmentPremise = `
@prefix : <http://example.org/> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
:hasChild a owl:ObjectProperty . :Doctor a owl:Class .
:ParentOfDoctor a owl:Class ; owl:equivalentClass [ a owl:Restriction ;
    owl:onProperty :hasChild ; owl:someValuesFrom :Doctor ] .
:Alice a owl:NamedIndividual ; :hasChild :Bob .
:Bob a :Doctor , owl:NamedIndividual .
`
```

```observable-js
entailmentConclusion = `@prefix : <http://example.org/> . :Alice a :ParentOfDoctor .`
```

```observable-js
entailmentVerdict = await fn.owlEntails(entailmentPremise, entailmentConclusion)
```

`entailmentVerdict` is `{ entailed: true, via: "refutation" }`: the
closure alone leaves it undecided, and the refuter proves it by finding
no model of the premise where Alice is *not* a `ParentOfDoctor`. Like
`owlIsConsistent`, `owlEntails` is three-valued — a refutation goal that
exhausts its budget returns `entailed: null` with the cap named, never a
false negative.

## The standing measured proof

The tableau drives the **SPARQL 1.1 entailment regimes** suite —
`parent`, `paper-sparqldl`, `simple`, and `bind` tests built on exactly
these restriction constructors. Its score is a named row on the
[test-results dashboard]({{ '/test-results/' | url }}); read it there
rather than trusting a number frozen into this prose. The same
`Tableau.tableau_materialise` runs under the OWL runner's `--regime dl`,
where DL is defined to fall back to RL on any cap-trip so the DL score is
never below RL.

## Not covered — measured, not hidden

The tableau is a real reasoner over a bounded fragment, and the boundary
is where the honest account lives.

**The DL catalogs still fail many tests.** Under `--regime dl` the OWL 2
conformance catalogs (positive-entailment, inconsistency,
negative-entailment) each carry a large remaining fail count. The DL
regime *raised* the pass counts over RL — the tableau flips a set of
`FAIL → PASS` with zero disagreements (every RL≠DL difference is
sound) — but it does not clear the catalogs. The refutation side
landed 2026-07-10 as `Tableau.Refute.fst`: a clash-detecting
satisfiability check (NNF, lazy TBox unfolding, disjunction branching
with a threaded work budget, existential witnesses, and complement /
min-max / counting / bottom-property clash rules, each with a written
Direct Semantics soundness argument) now scores the DL-regime
inconsistency and consistency rows. The clusters that remain need
constructs the calculus still does not decide: nominal (`owl:oneOf`)
enumeration reasoning, datatype-facet contradictions, inverse-role
interaction, and propositional encodings deep enough to exhaust the
refuter's linear budget (indeterminate results fall back to the RL
verdict, never below it). The live per-catalog numbers are the
OWL rows on the [test-results dashboard]({{ '/test-results/' | url }});
they are not reproduced here so they cannot go stale.

**A performance cliff on `owl:sameAs` cliques.** The DL pipeline is
markedly slower than RL — two closures plus the tableau — and it is
exposed to a `sameAs`-clique blow-up (issue
[#262](https://github.com/danbri/factoidal/issues/262)). Each DL test
runs under a per-test wall-clock cap; on a cap-trip the runner logs it
and falls back to the RL answer. The cap keeps a pathological input from
hanging the suite; it also means a slow-enough DL entailment is reported
as its RL lower bound rather than its true DL answer.

**A sound-but-narrow query rewrite.** The `N=1` qualified
`owl:maxCardinality` path uses an anchor-triple rewrite that, in the
words of the project's own standing note,

> silently drops vacuous-truth individuals (zero `P`-edges satisfy
> max-1) and OWL Full punned class-individuals

— and the strict runner-integrity comparison briefly added a second
entry to its charge sheet: the rewrite leaked internal
`?_mc_`/`?_mxqc1_` variables into result rows, failing two
entailment-regime tests that lenient comparison had waved through.
That leak is fixed (internal variables are stripped at the final
user-facing projection; see the live dashboard for the suite's
current score) — the vacuous-truth narrowness quoted above remains.
It is tracked in issue
[#236](https://github.com/danbri/factoidal/issues/236); generalising it
from an anchor to a `UNION` is the documented fix before relying on it
for OWL DL outside the entailment-regime suite.

**The materialise/refute split.** `Tableau.fst`'s materialisation
stays positive-sound by design: membership it cannot justify
model-theoretically it returns as *unknown*, and the caller falls back
to the Datalog closure — returning unknown is always sound. The
formerly deferred negative side lives in its sibling
`Tableau.Refute.fst` (2026-07-10): fresh-individual `∃`-witnesses
(uncounted, so no-UNA merging can never be contradicted), classical
negation as NNF plus complement-clash with disjunction branch search,
and `max-N` refutation past `k = 0` — counting only successors that
are *pairwise provably distinct* (`owl:differentFrom`, or same-datatype
literal values), exactly the no-unique-name discipline the old banner
said it was waiting for. Where the refuter runs out of budget or meets
a construct outside its fragment it reports *indeterminate*, and the
runner keeps the RL verdict.

Every live cell above is pinned in
[`tests/hub/post30_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post30_test.mjs).
