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
`fn.tableauMaterialise` (add the memberships the tableau proves) and
`fn.tableauDlInconsistent` (the DL consistency verdict).

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
parentOfDoctorMembers = (await fn.query(someValuesMaterialised.dataset, `
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
britishCitizens = (await fn.query(hasValueMaterialised.dataset, `
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

`inconsistencyVerdict` reports `{ inconsistent: true, rlAlone: false }`:
the DL pipeline (RL closure → tableau materialisation → RL closure →
inconsistency check) flags the contradiction, while `rlAlone` — the
plain OWL-RL verdict on the same graph — does not, because the
Datalog closure never introduces the witness that reaches `owl:Nothing`.
This is the shape of the `WebOnt-Restriction` cases the DL regime
decides that RL leaves consistent.

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
sound) — but it does not clear the catalogs. The clusters that remain
need constructs the tableau does not yet decide: full cardinality
refutation, nominal (`owl:oneOf`) enumeration reasoning, and classical
negation with dual-branch search. The live per-catalog numbers are the
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

**Constructs the module excludes by design.** `Tableau.fst`'s own
banner enumerates its class-expression grammar and marks the deferred
stages: no fresh-individual skolemisation for `∃` beyond the ABox's own
successors, no full classical-negation branch search, and
`owl:maxCardinality` / `owl:cardinality` refutation only at `k = 0`
(true `max-N` and `exactly-N` refutation needs `owl:differentFrom`
tracking under the no-unique-name assumption). Membership it cannot
justify model-theoretically it returns as *unknown*, and the caller
falls back to the Datalog closure — returning unknown is always sound.

Every live cell above is pinned in
[`tests/hub/post30_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post30_test.mjs).
