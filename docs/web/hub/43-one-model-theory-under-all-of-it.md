---
title: "One model theory under all of it"
description: "RDF, RDFS, ρdf, OWL 2 RL, OWL DL and SPARQL each carry their own model theory. A Lean 4 programme translates all of them into one first-order language in the LBase/IKL tradition and proves, in both directions, that the translation says what the native semantics says — with the live engine answering the questions the theorems are about."
layout: hub.njk
series: docs-hub
series_order: 43
vocab: none
status: published
tests: tests/hub/post43_test.mjs
---

Ask this engine a question and it answers from a different semantics
depending on which question you asked. `ASK` over a graph uses simple
entailment ([RDF 1.1 Semantics
§5](https://www.w3.org/TR/rdf11-mt/#simpleentailment)). Turn on the ρdf
closure and it uses the six-rule fragment. Turn on RDFS and it uses
[§9](https://www.w3.org/TR/rdf11-mt/#rdfs-entailment). Ask whether an
ontology is consistent and it uses [OWL 2 Direct
Semantics](https://www.w3.org/TR/owl2-direct-semantics/); ask for the
RL closure and it uses [RDF-Based
Semantics](https://www.w3.org/TR/owl2-rdf-based-semantics/) through a
rule table. Six model theories, six formalizations, six sets of
theorems — and, until now, nothing at all connecting them except that
the same code base implements them and the same test suites score them.

"The RDFS answer agrees with the ρdf answer where both apply" was, in
this tree, a statement about test scores. It is now a statement about
models.

## The 2003 proposal

[LBase](https://www.w3.org/TR/lbase/) (R. V. Guha and Patrick Hayes,
W3C Working Group Note, 10 October 2003) proposed the fix: one
first-order base language, one translation per Semantic Web language,
and vocabulary axioms constraining the translated terms, so that "the
model theory of Lbase is the model theory of all the Semantic Web
Languages". The Note supplies a sketch translation table for RDF —
classes to unary predicates, properties to binary relations, a typed
literal `"sss"^^ddd` to the term `LiteralValueOf('sss', TR[ddd])`, a
blank node to a variable, a graph to the existential closure of the
conjunction of its triples.

The Note also states its own limits. §4.0 says LBase cannot express
"propositional attitudes or true second order constructs". And the
translation table carries a caveat printed next to it: "this should not
be referred to as an accurate or normative semantic description". The
accuracy was asserted, not established. LBase was never completed and
never machine-checked.

[IKL](https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html) (Hayes and
Menzel, IKRIS 2006) supplies what §4.0 says is missing: it extends
Common Logic (ISO/IEC 24707) with the term `(that S)`, which denotes
the proposition a sentence expresses.
[Post 41](../41-a-walkthrough-of-the-ikl-guide/) parses that construct
live; `CL/Semantics.lean` in this repository formalizes the ISO/IEC
24707 §6.2/§6.3 clauses plus the IKL proposition domain.

So: carry out LBase's programme in Lean 4, over the languages this
repository implements, with the accuracy proved instead of asserted.
That is
[issue 598](https://github.com/danbri/factoidal/issues/598), seven
stages, 19 modules, 15,631 lines of Lean, no `sorry`, no user `axiom`,
no `native_decide`, no `partial`.

## The device

Three parts.

**A translation.** `rdfToTheory g` is ONE sentence: the existential
closure, over the graph's blank nodes, of the conjunction of one binary
predication per triple. Once at graph level, not once per triple —
because [RDF 1.1 Semantics
§5.2](https://www.w3.org/TR/rdf11-mt/#simpleentailment) defines graph
satisfaction with one assignment for the whole graph.

**A schema.** LBase §2.4's axiom schemas, represented in Lean as a set
of sentences, which may be infinite — the `rdf:_n` container-membership
families need exactly that.

```lean
abbrev Schema := CL.Sentence → Prop

def EntailsSchema (conds : CL.Interp → Prop) (S : Schema)
    (premises : List CL.Sentence) (conclusion : CL.Sentence) : Prop :=
  ∀ i : CL.Interp, conds i → SatisfiesSchema i S →
    CL.SatisfiesAll i premises → CL.Satisfies i conclusion
```

**An adequacy proof, in both directions.** The native Lean
formalizations stay ground truth — the model theory in
`RDF/Semantics.lean`, the closures in `RDFS/` and `OWL/`, the tableau,
the algebra. Each stage's gate theorem says the translated relation and
the native relation pick out exactly the same pairs. Where only one
direction holds, the other is recorded as a gap in
[`docs/theorem-registry.md`](https://github.com/danbri/factoidal/blob/claude/main/docs/theorem-registry.md)
section 9.

## What an answer means

Here is the ρdf closure ([Muñoz, Pérez and Gutierrez's minimal RDFS
fragment](https://www.w3.org/TR/rdf11-mt/#rdfs-entailment), six rules)
answering a question the stated graph does not contain. Three triples
go in: `hasParent` is a subproperty of `hasAncestor`, `hasAncestor` has
range `Person`, and Alice has parent Bob. Nobody typed that Bob is a
Person.

```observable-js
EX = "http://example.org/"
```

```observable-js
statedGraph = `<${EX}hasParent> <http://www.w3.org/2000/01/rdf-schema#subPropertyOf> <${EX}hasAncestor> .
<${EX}hasAncestor> <http://www.w3.org/2000/01/rdf-schema#range> <${EX}Person> .
<${EX}alice> <${EX}hasParent> <${EX}bob> .
`
```

The cell runs the closure, asks the same `ASK` over the stated graph
and over the closure, and runs the engine's ρdf fragment check over the
closure — the executable check that discharges one of the three
hypotheses the decided theorem below carries.

```observable-js
rhoDfAnswer = {
  const q = `# True if bob is asserted, or entailed, to be a Person.
ASK { <${EX}bob> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <${EX}Person> }`;
  const before = await fn.l4Call("queryDataset", [statedGraph, q]);
  const closed = await fn.l4Call("rhoDfClosure", [statedGraph]);
  const after = await fn.l4Call("queryDataset", [closed.ntriples, q]);
  const frag = await fn.l4Call("rhoDfFragmentCheck", [closed.ntriples]);
  return {
    statedTriples: statedGraph.trim().split("\n").length,
    closureTriples: closed.ntriples.trim().split("\n").length,
    rounds: closed.rounds,
    askOverStated: before.boolean,
    askOverClosure: after.boolean,
    fragmentCheckOnClosure: frag.fragment,
  };
}
```

Two rules fired: rdfs7 (subproperty) then rdfs3 (range). The answer
flipped from false to true, and the fragment check on the closure came
back true.

What licenses reading that flip as "the stated graph ρdf-entails it"?
Three theorems, chained. The first relates the translation to the
native model-theoretic relation:

```lean
theorem unified_adequate_rhoDf (g h : RDF.Graph) :
    EntailsSchema condTrue rhoDfSchema [rdfToTheory g] (rdfToTheory h)
      ↔ RDF.RhoDfEntails g h
```

A full `↔`, with no side conditions at all. The design document had
predicted this one would need fragment hypotheses; it does not — they
belong to the second theorem, which reaches the running engine:

```lean
theorem unified_adequate_rhoDf_decided (g h : RDF.Graph) (fuel : Nat)
    (hclosed : RDF.RhoDfClosed (RDFS.closure g fuel))
    (hf : RDF.RhoDfModelFragGraph (RDFS.closure g fuel))
    (hfe : RDF.GraphTtFree h) :
    EntailsSchema condTrue rhoDfSchema [rdfToTheory g] (rdfToTheory h)
      ↔ RDF.simpleEntails (RDFS.closure g fuel) h = true
```

Each of those three hypotheses has an executable sufficient check that
`decide` discharges on a concrete input, so the theorem reaches
concrete inputs rather than stopping at an assumption. `rhoDfFragmentCheck` in the cell above computes one of them
(`RDFS.isRhoDfFrag`) on the closure this page just built.

The third says the engine's closure is a Datalog least fixpoint, so the
"answer" and the "consequence" are the same object:

```lean
theorem rhoDf_engine_iff_datalog_entails (g : Graph) (n m : Nat)
    (hcl : RDF.rhoDfClosedCheck (RDFS.closure g m) = true)
    (hf : RDFS.isRhoDfFrag (RDFS.closure g m) = true)
    (hfa : rhoDfProgram.FuelAdequate (graphFacts g) n)
    (t : Triple) (hto : RDF.RhoDfModelObjectOk t.o) :
    t ∈ RDFS.closure g m ↔
      EntailsSchema condTrue rhoDfProgram.toSchema
        ((graphFacts g).map DAtom.sentence) (tripleFact t).sentence
```

The phrase "closure engines as fragment deciders" needs its fragment
named. This theorem names it: ground-atomic consequences of a
definite-Horn schema, on the ρdf model fragment.

## Where two of the semantics part company

ρdf and RDFS are different entailment relations, and the difference
shows up in one triple. Take the graph
`X rdfs:subClassOf Y` and ask for `X rdfs:subClassOf X`. Full RDFS
entails it — subclass is reflexive on classes,
[§9](https://www.w3.org/TR/rdf11-mt/#rdfs-entailment). ρdf's six rules
do not.

```observable-js
selfLoop = {
  const RDFS = "http://www.w3.org/2000/01/rdf-schema#";
  const premise = `<${EX}X> <${RDFS}subClassOf> <${EX}Y> .\n`;
  const q = `# True if X is asserted, or entailed, to be a subclass of itself.
ASK { <${EX}X> <${RDFS}subClassOf> <${EX}X> }`;
  const rho = await fn.l4Call("rhoDfClosure", [premise]);
  const rdfs = await fn.l4Call("owlClosure", [premise, "RDFS"]);
  return {
    rhoDfTriples: rho.ntriples.trim().split("\n").length,
    rdfsTriples: rdfs.nquads.trim().split("\n").length,
    rhoDfSaysSelfLoop: (await fn.l4Call("queryDataset", [rho.ntriples, q])).boolean,
    rdfsSaysSelfLoop: (await fn.l4Call("queryDataset", [rdfs.nquads, q])).boolean,
  };
}
```

That exact pair — `X rdfs:subClassOf Y` as premise, `X rdfs:subClassOf
X` as conclusion — is Finding C-1 from the ρdf completeness work, and
it appears in the Lean tree twice, once refuted and once proved:

```lean
theorem rhoDf_not_entails_selfLoop_unified :
    ¬ EntailsSchema condTrue rhoDfSchema
        [rdfToTheory c1Prem] (rdfToTheory c1Concl)

theorem rdfs_entails_selfLoop_unified (Dset : RDF.DatatypeSet) :
    EntailsSchema condTrue (rdfsSchema Dset)
      [rdfToTheory c1Prem] (rdfToTheory c1Concl)
```

`c1Prem` and `c1Concl` in the source are the same two triples the cell
computed with. The pair does double duty: it is the strictness witness
proving the RDFS schema is strictly stronger than the ρdf schema, and
it is the reason there is no decided RDFS corollary. RDFS adequacy is
proved as a full `↔` against the model theory:

```lean
theorem unified_adequate_rdfs (Dset : RDF.DatatypeSet) (g h : RDF.Graph) :
    EntailsSchema condTrue (rdfsSchema Dset) [rdfToTheory g] (rdfToTheory h)
      ↔ RDF.RdfsEntails Dset g h
```

— unconditional, every recognised-datatype set. But the executable
characterisation, the RDFS analogue of the decided ρdf theorem above,
does not follow, because C-1 shows RDFS entailment differs from simple
entailment of the closure even on the fragment. For the full RDFS
closure the tree has soundness and stops there, which is what the
registry row says.

## A rule table, checked against models

OWL 2 RL is a different shape of thing: 91 rows of a rule table
([OWL 2 Profiles](https://www.w3.org/TR/owl2-profiles/#OWL_2_RL),
Tables 4–9). The engine ran them; nothing said they were true.

```observable-js
owlRlAnswer = {
  const OWL = "http://www.w3.org/2002/07/owl#";
  const premise = `<${EX}hasWife> <${OWL}inverseOf> <${EX}hasHusband> .
<${EX}john> <${EX}hasWife> <${EX}mary> .
`;
  const conclusion = `<${EX}mary> <${EX}hasHusband> <${EX}john> .\n`;
  const q = `# True if mary is asserted, or entailed, to have husband john.
ASK { <${EX}mary> <${EX}hasHusband> <${EX}john> }`;
  const closed = await fn.l4Call("owlClosure", [premise, "OWL-RL"]);
  const before = await fn.l4Call("queryDataset", [premise, q]);
  const after = await fn.l4Call("queryDataset", [closed.nquads, q]);
  const ent = await fn.l4Call("owlEntails", [premise, conclusion, "{}"]);
  return {
    closureTriples: closed.nquads.trim().split("\n").length,
    askOverStated: before.boolean,
    askOverClosure: after.boolean,
    entailed: ent.entailed,
    via: ent.via,
  };
}
```

Row prp-inv1 fired. Two theorems stand behind that triple. The first
was already there: T2 licensing, `closure_sound`, "every triple the
engine emits is an input triple or a licensed application of a named
table row" — assembled from 56 per-row lemmas. Licensing says which
rule emitted a triple; it says nothing about the triple being true in
every model, and `OWL/RLTheorems.lean`'s header had recorded truth
preservation as not ported since it was written. Stage 4 supplies it, in
`OWL/RLSemantics.lean`, as one condition per rule row and one induction
over the whole of `OWL.RL.Derives`, and then lifts it:

```lean
theorem unified_owlRl_sound {g : RDF.Graph} {t : RDF.Triple}
    (hres : RlReservedFree g) (h : OWL.RL.Derives g t) :
    EntailsSchema OwlRlInterpCond owlRlSchema [rdfToTheory g] (rdfToTheory [t])
```

Three things are visible in the statement.
`RlReservedFree g` cannot be dropped: a graph that uses the engine's
reserved comprehension labels can make the engine confuse a user's
blank node with a comprehension witness, and soundness genuinely fails
there. `OwlRlInterpCond` is the interpretation-class condition carrying
the nine rows that cannot be written as schema sentences — two whose
premise relation is ternary where interpretation extensions are binary,
four whose cardinality literal is a function term rather than a Datalog
term, three with existential heads. And this is **soundness**: the
completeness direction landed in condition-bundle form on a narrow
fragment, and that fragment excludes any graph whose closure carries a
cardinality literal — which includes every graph declaring an
`owl:ObjectProperty`.

## The whole board

| Stage | Gate theorem | Strength |
|---|---|---|
| 1 RDF core | `unified_adequate_simple` | full `↔`, no side conditions |
| 1 datatypes | `unified_adequate_d` | full `↔`, no side conditions, any `D` |
| 2 ρdf | `unified_adequate_rhoDf` | full `↔`, unconditional |
| 2 RDF / RDFS / RDFS+D | `unified_adequate_rdf`, `unified_adequate_rdfs`, `unified_adequate_rdfs_d` | full `↔`, unconditional |
| 2 RDFS closure | `unified_rdfs_closure_sound` | soundness only, two hypotheses |
| 3 Datalog | `datalog_lfp_iff_entails` | full `↔` for ground-atomic consequences |
| 4 OWL 2 RL | `unified_owlRl_sound` | soundness only, `RlReservedFree` |
| 4 OWL 2 RL | `owlRl_complete_ground` | ground completeness, condition-bundle form, narrow fragment |
| 5 OWL DL | `unified_adequate_dl` | full `↔`, no side conditions |
| 5 tableau | `refuted_unified_unsat` | soundness only |
| 6 SPARQL BGP | `unified_adequate_bgp` | full `↔`, two triple-term-freedom hypotheses |
| 6 regimes | `regime_sound_*` | soundness; `x-rdfscore` also answer-preserving as a full `↔` |

Every gate theorem carries an in-source `#print axioms` audit reporting
`propext`, `Classical.choice`, `Quot.sound` and nothing else.

## What the proofs found in the code

The proof attempts exercised the engines where no test did. Five
findings came out of that, four of them in code that was shipping and
scoring green.

**A semantics divergence, and a first attribution that was wrong.**
Attempting the decided form of the datatype theorem produced a
counter-example instead: on `:a :p <<( :a :q "yes"^^xsd:boolean )>>` —
an ill-typed literal inside an RDF 1.2 triple term — the executable
answered "inconsistent" and the model theory answered "satisfiable".
The [first
issue](https://github.com/danbri/factoidal/issues/602) blamed the
executable. It was wrong: [RDF 1.2 Semantics
(WD)](https://www.w3.org/TR/rdf12-semantics/) §5 makes a triple term's
denotation a function of its components' denotations, and the W3C
`malformed-literal` test says in its own manifest comment that
"Malformed literals are allowed in triple terms, but cause
inconsistency". The defective layer was the model theory. Both were
repaired, and the guard is now a rule: a semantics default in a fold
over a syntax type must name the specification clause that licenses it,
and no catch-all match arm over a term type in a verdict function.

**A test suite that had never once loaded.** Deciding that question
needed the rdf12 `rdf-semantics` suite, which turned out never to have
loaded in the Lean harness: an upstream manifest used an undeclared
prefix, the manifest parser was strict, and every umbrella run had
reported 0 pass, 0 fail (out of 0) for its whole life. The first run
after the parse was made lenient-with-report: **19 pass, 11 fail,
0 skip, 17 unsupported (out of 47)** — exposing 9 engine gaps nothing
had ever exercised, and 2 apparent contradictions in the upstream test
suite itself.
([issue 605](https://github.com/danbri/factoidal/issues/605))

**The other engine has the opposite defect.** The differential check
that followed found the F\* engine skipping the inconsistency-verdict
tests entirely (**41 pass, 3 fail, 3 skip (out of 47)**) and scanning
only top-level literals. The two engines disagree with each other on
the same question, and neither had ever been tested on it.
([issue 604](https://github.com/danbri/factoidal/issues/604))

**A query narrowing nobody had written down.** Stage 6 reconnaissance
found that BGP matching treats a blank node in a query pattern as a
constant with that label, where [SPARQL 1.1
§18.3.1](https://www.w3.org/TR/sparql11-query/#BGPsparql) makes it a
non-distinguished variable that may match any term. The engine returns
fewer solutions than the specification licenses, and no comment or test
had flagged it.
([issue 607](https://github.com/danbri/factoidal/issues/607))

**A `decide` that decided something false.** A draft claimed by
computation that all 40 rows of the engine's RDFS seed table appear in
the specification's 38-row table. Two do not: RDF 1.1 Semantics §9.3
does not list the `rdf:XMLLiteral` rows, because recognising that
datatype is optional. The repair was an explicit hypothesis on the
theorem statement.

**An inconsistency verdict that overclaims.** Given
`p rdfs:range xsd:integer` and `:a p "1"^^xsd:int`, the range-clash
layer reports inconsistency. The value 1 is in `xsd:integer`'s value
space, so the graph has a model. The layer compares datatype IRIs where
the specification compares value spaces, and the stage 2 condition
matched the layer. Open.

## What is not claimed

* **No multiplicity result.** SPARQL evaluates to multisets; `Answers`
  is a `Prop` and the engine side is membership. Nothing downstream
  supplies the bag either.
* **The two OWL semantics are not related.** Direct Semantics and
  RDF-Based Semantics sit side by side over the same interpretation
  type here. The OWL 2 correspondence theorem (RDF-Based Semantics
  §7.2) is not machine-checked in this tree.
* **Tableau completeness is open**, so "consistent" from the calculus
  is not a proof of satisfiability, and "unknown" claims nothing
  ([issue 586](https://github.com/danbri/factoidal/issues/586)).
* **SPARQL adequacy is to the ENGINE at the raw `evalBgp` entry
  point** on a pattern containing a blank node, per §18.3.1 above. The
  QUERY path rewrites those blank nodes into non-distinguished
  variables first, and `unified_adequate_bgp_spec` is the gate stated
  over the rewritten pattern with no blank-node hypothesis
  ([issue 607](https://github.com/danbri/factoidal/issues/607), whose
  remaining half is the F* tree's EXISTS bodies).
* **RIF Core never got its stage.** The machinery it needs has been
  landed and generic since stage 3; the theorem does not exist.
* **The `rdf:_n` finite-slice lemma is unproved.** Nothing landed
  consumes it, and it is recorded that way rather than assumed.

The full account, with every gate theorem quoted as landed, every gap
row, and the post-mortems: [the LBase
account](https://github.com/danbri/factoidal/blob/claude/main/docs/designissues/2026-08-26-lbase-account.md)
and
[`docs/theorem-registry.md`](https://github.com/danbri/factoidal/blob/claude/main/docs/theorem-registry.md)
section 9. The programme is
[issue 598](https://github.com/danbri/factoidal/issues/598).
