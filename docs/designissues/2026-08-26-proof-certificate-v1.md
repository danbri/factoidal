# Proof certificate v1 — design

Status: DRAFT for owner review. Written 2026-08-26 alongside the first
implementation agent (issue
[#615](https://github.com/danbri/factoidal/issues/615) item 1).

Owner framing, 2026-08-26, verbatim:

> "In a way what we are doing here is trying to find ways of imparting
> some of YOUR expert knowledge of all these languages and formalisms to
> a LEAN4-backed NPM module (js wrapping wasm), such that Lean can show
> users why something is so, and even JS can emit proof chains."

## 1. What a certificate asserts

A v1 certificate is a claim of one shape:

    under regime R, graph G entails conclusion C

with a derivation that a third party can check without our engine.

`R` is one of the entailment regimes the engine already dispatches:
`simple`, `x-rdfscore` (rho-df), `rdfs`, `x-rdfsplus`, `owl-rl`. `G` is
an RDF graph. `C` is a triple, or a set of triples.

The certificate does NOT assert that C is true. It asserts that C
follows from G under R. Whether G is true of the world is a separate
question, and the certificate carries provenance for G rather than
answering it (section 3).

## 2. Trust model — the reason to build this at all

The property that matters: **a party who does not trust the engine can
still check the answer.**

The checker must therefore need none of the following:
- our engine (4.2 MB of wasm),
- our closure algorithm,
- trust in whoever produced the certificate.

It needs only: the graph, the certificate, and the rule table from the
W3C specification. The checker is a few hundred lines. A reader who
distrusts us can reimplement it from RDF 1.1 Semantics section 8 and
section 9 in an afternoon, and get the same verdict.

This is the difference between a *re-runnable* claim and a *locally
checkable* one. Today the engine's answers are re-runnable: you can
install Factoidal and get the same triples. That requires trusting the
engine. A certificate is checkable: it requires trusting only the
specification.

## 3. Graph identity — the part that is easy to get wrong

A certificate names a graph. RDF graphs contain blank nodes, so two
serialisations of the same graph differ byte for byte while denoting the
same thing. A hash over the serialisation would therefore reject a
correct certificate whenever the producer and the checker serialised
differently.

v1 names the graph by its **RDFC-1.0 canonical form**:

    graph.canonicalHash = SHA-256 of the canonical N-Quads produced by
                          RDFC-1.0 (W3C RDF Dataset Canonicalization)

RDFC-1.0 is already implemented and tested in the Lean tree
(`L4Factoidal/RDF/Canonical.lean`, `CanonicalTheorems.lean`,
`CanonicalTests.lean`) and already exposed over the ABI as
`canonicalizeToNQuads`. No new machinery is required.

This is the join between the two regimes named in section 2.
Canonicalization is what makes "the graph this certificate is about" a
well-defined referent rather than a byte string, so provenance about G
and a proof over G can name the same object.

Blank nodes inside the derivation refer to the canonical labels, not to
whatever labels the input serialisation used.

## 4. Wire format v1

JSON. The byte assembly is done in Lean and extracted, per iron rule #11
— no JS or OCaml wrapper composes certificate text.

```json
{
  "@type": "FactoidalDerivation",
  "version": 1,
  "regime": "rdfs",
  "graph": {
    "canonicalHash": "sha256:...",
    "canonicalNQuads": "..."
  },
  "conclusion": { "s": "...", "p": "...", "o": "..." },
  "steps": [
    { "rule": "axiomatic",
      "conclusion": {"s":"rdfs:isDefinedBy","p":"rdfs:subPropertyOf",
                     "o":"rdfs:seeAlso"},
      "premises": [] },
    { "rule": "rdfD2",
      "conclusion": {"s":"rdfs:subPropertyOf","p":"rdf:type",
                     "o":"rdf:Property"},
      "premises": [0] },
    { "rule": "rdfs6",
      "conclusion": {"s":"rdfs:subPropertyOf","p":"rdfs:subPropertyOf",
                     "o":"rdfs:subPropertyOf"},
      "premises": [1] }
  ]
}
```

Three format rules, each of which exists to close an attack:

1. **Steps are in topological order.** Every index in `premises` is
   strictly less than the step's own index. A checker validates in one
   left-to-right pass and never needs a graph traversal or a cycle
   check.
2. **`rule` names a row of the specification**, one identifier per
   `DerivesFull` constructor (`RDFS/FullClosure.lean:214`, 25
   constructors). An unknown identifier is a rejection, never an ignored
   step.
3. **`canonicalNQuads` may be omitted** when the checker already holds
   G. `canonicalHash` may not. A certificate that does not pin its graph
   proves nothing about any particular graph.

`canonicalNQuads` is included by default because a certificate that
travels without its graph is only checkable by someone who happens to
have the graph.

An RDF serialisation of the same structure is a later profile, not v1.
JSON first because the consumers are JS callers.

## 5. What the checker does, and what it rejects

    checkDerivation : Regime -> Graph -> Derivation -> Bool

For each step, in order:

- `base`: the conclusion is a triple of G.
- `axiomatic`: the conclusion is in the axiomatic set for R.
- any rule row: the named premises are earlier steps, and the row's
  side conditions hold of those premises' conclusions and this step's
  conclusion.

The checker returns `true` only if the last step's conclusion is the
certificate's `conclusion` and every step passed.

Rejections, all of which are real ways a hostile or broken certificate
can try to pass:

| rejection | what it stops |
|---|---|
| premise index >= own index | a step justified by its own consequence |
| premise index out of range | a step with no justification at all |
| unknown `rule` | a made-up inference row |
| conclusion not the row's output for those premises | a real rule cited over the wrong triples |
| `canonicalHash` mismatch | a valid proof about a different graph |
| final conclusion not the claimed one | a proof of something else |
| `version` not understood | silent divergence between producer and checker |

The checker is total. No fuel parameter, because it does one pass over a
finite list.

## 6. The theorem that makes it worth something

A checker is only as good as its relationship to the semantics. The
obligation, in Lean:

```lean
theorem checkDerivation_sound
    (R : Regime) (g : Graph) (d : Derivation)
    (h : checkDerivation R g d = true) :
    DerivesFull (axiomsFor R) g d.conclusion
```

and, through the unified model theory
([#598](https://github.com/danbri/factoidal/issues/598)), onward to
model-theoretic entailment rather than rule-firing:
`unified_adequate_rdfs` turns a `DerivesFull` term into the statement
that every model of G is a model of C.

Read `skills/measuring-inference/SKILL.md` before believing that
theorem when it lands. A checker that returns `false` on everything
satisfies it vacuously. The gate is a matched pair: certificates that
must be accepted, and malformed certificates from the table in section 5
that must be rejected, each pinned.

Completeness — every `DerivesFull` term has an accepted certificate — is
NOT claimed in v1. It is what makes the feature useful rather than
correct, and it should follow from the emitter's soundness plus the
existing `fullClosure` completeness lemmas. Stated here so nobody
records v1 as complete.

## 7. Where IKL and LBase come in

This is the part no other RDF engine can do, and the reason the CL/IKL
work is not a side quest.

A v1 certificate is single-regime. Its steps all come from one rule
table. But a real question crosses formalisms: an RDFS step, then an
OWL RL step, then a RIF rule, then a SPARQL answer over the result.
Chaining those requires the four rule sets to be interpreted in ONE
semantics, or the chain is four separate claims with no relation
between them.

That is exactly what the unified model theory provides. `CL.Interp` is
the host structure; `RdfEmbed`, `OwlRlSchema`, `RifEmbed`,
`SparqlAdequacy` each embed their formalism into it, and the
`unified_adequate_*` family states the adequacy of each embedding. A
cross-formalism certificate is a list of steps whose rule identifiers
range over all four tables, checked against one interpretation.

The IKL contribution specifically: `that`-terms let a certificate refer
to a proposition as an object — which is what a claim ABOUT a
derivation needs ("this endorsement is of that entailment"), rather than
a claim within one. Hayes normalization
(`CL/Normalize.lean`, `NormalizeSemantics.lean`) reduces such a
certificate to a CL one, satisfiability-preservingly, under the
no-intrusion condition that `CL.noIntrSs` decides — so the checker for
the reduced form is the CL checker, not a new IKL-specific one.

v1 does not implement any of this. It fixes the step and rule-identifier
shape so that the cross-formalism version is an extension of the same
format rather than a replacement.

## 8. Out of scope for v1, named so it is not mistaken for coverage

- **Negative answers.** "G does not entail C under R" is a counter-model
  claim, not a failed search. Decision needed (section 9).
- **SPARQL answers.** A different witness: a solution mapping plus the
  triples it matched, not a rule chain.
- **OWL DL.** Tableau refutations are a different proof object.
- **Signatures.** A certificate says nothing about who produced it. If
  endorsement is wanted, it composes with the existing VC Data-Integrity
  path ([#286](https://github.com/danbri/factoidal/issues/286)), which
  already signs canonical N-Quads with Ed25519. That is a separate
  layer and should stay separate: the derivation is checkable by anyone,
  the signature says who is willing to be held to it.
- **Completeness** (section 6).

## 9. Decisions needed from the owner

1. **Negative certificates.** Return a finite counter-model as the
   witness for "not entailed", or keep negatives verdict-only with the
   reason stated? A counter-model is checkable in the same sense as a
   derivation, so option A keeps the property from section 2. It is more
   work and needs a finite-model extraction the engine does not have
   today. `rhoDf_not_entails_selfLoop_unified` is the Lean form of one.
2. **`canonicalNQuads` inline by default?** Included, the certificate is
   self-contained and large. Omitted, it is small and only checkable by
   someone holding G. Proposed: inline by default, omissible by flag.
3. **JSON only for v1, or JSON plus an RDF profile now?** Proposed:
   JSON only. An RDF profile means choosing a vocabulary, which is a
   larger decision than v1 needs.

Nothing in section 9 blocks the item-1 work now in flight.
