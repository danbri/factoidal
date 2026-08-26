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

Owner ruling, 2026-08-26, verbatim:

> "do try to make v1 include evidence from diverse pieces of Factoidal
> eg rdf rdfs owl xml … whatever could be combined in a proof of final
> results"

So v1 is NOT single-regime. A certificate is a chain of steps whose
components differ, ending in the result the caller actually asked for:

    XML document  --(xml)-->    parse tree
                  --(xslt)-->   RDF/XML
                  --(rdf)-->    graph G
                  --(rdfs)-->   closure of G
                  --(owlRl)-->  closure under OWL RL
                  --(sparql)--> the solution mapping returned

Each step names the component that licensed it, the artifacts it
consumed, the artifact it produced, and the Lean theorem that backs the
component's rule (section 6). The chain is the evidence for the final
result; no single component's answer is the certificate.

The certificate does NOT assert that the result is true of the world. It
asserts that the result follows from the named inputs by the named
rules. Whether the input document says something true is a separate
question, and the certificate carries provenance for it rather than
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

Two tables. `artifacts` are content-addressed intermediate values;
`steps` consume and produce them by index.

```json
{
  "@type": "FactoidalDerivation",
  "version": 1,
  "engine": { "gitSha": "...", "leanToolchain": "..." },

  "artifacts": [
    { "kind": "bytes", "mediaType": "application/xml",
      "hash": "sha256:...", "inline": "..." },
    { "kind": "graph",
      "canonicalHash": "sha256:...", "canonicalNQuads": "..." },
    { "kind": "solutions", "hash": "sha256:...", "inline": "..." }
  ],

  "result": { "artifact": 2 },

  "steps": [
    { "component": "xml",    "rule": "wellformed",
      "consumes": [0], "produces": 0,
      "assurance": { "theorem": "XML.Wellformedness.parse_sound",
                     "module": "L4Factoidal.XML.Wellformedness",
                     "tier": "algorithm-correctness" } },

    { "component": "rdfs",   "rule": "rdfD2",
      "consumes": [1], "produces": 1, "premises": [3],
      "assurance": { "theorem": "RDFS.rdfD2For_sound",
                     "module": "L4Factoidal.RDFS.FullClosureTheorems",
                     "tier": "w3c-refinement" } }
  ]
}
```

Format rules, each tied to the attack it closes:

1. **Steps are in topological order.** Every index in `premises` is
   strictly less than the step's own index, and every index in
   `consumes` names an artifact already produced. A checker validates in
   one left-to-right pass and never needs a graph traversal or a cycle
   check.
2. **`component` + `rule` name a row of a specification.** Within
   `rdfs`, the rule identifiers are one per `DerivesFull` constructor
   (`RDFS/FullClosure.lean:214`, 25 constructors). An unknown pair is a
   rejection, never an ignored step.
3. **Every artifact is content-addressed**, graphs by their RDFC-1.0
   canonical hash (section 3), byte artifacts by plain SHA-256 over the
   bytes. A step that consumes an artifact whose hash does not match
   what the previous step produced is a rejection.
4. **`assurance` is mandatory on every step** (section 6), and where a
   rule has no correctness theorem the field says so explicitly rather
   than being absent.
5. **`engine` pins the producing build.** Not trusted by the checker —
   it is provenance, so a divergence between two certificates over the
   same input can be attributed.

Inline artifact bodies may be omitted when the checker already holds
them; hashes may not. A certificate that does not pin its inputs proves
nothing about any particular input.

An RDF serialisation of the same structure is a later profile, not v1.
JSON first because the consumers are JS callers.

## 5. What the checker does, and what it rejects

    checkDerivation : Certificate -> Bool

One left-to-right pass. For each step:

- the artifacts in `consumes` were produced by earlier steps, or are
  declared inputs, and their hashes match;
- the `(component, rule)` pair is one the checker knows;
- the rule's side conditions hold of the named premises' conclusions and
  this step's conclusion;
- for `rdfs`/`owlRl` steps specifically: `base` conclusions are triples
  of the consumed graph, `axiomatic` conclusions are in the axiomatic
  set for the regime, and every other row is checked against its
  specification table.

The checker returns `true` only if the artifact named by `result` was
produced by some step and every step passed. It also reports the
weakest `assurance.tier` in the chain (section 6b), which is
information, not a verdict.

Rejections, all of which are real ways a hostile or broken certificate
can try to pass:

| rejection | what it stops |
|---|---|
| premise index >= own index | a step justified by its own consequence |
| premise or artifact index out of range | a step with no justification at all |
| unknown `(component, rule)` pair | a made-up inference row |
| conclusion not the row's output for those premises | a real rule cited over the wrong triples |
| consumed artifact hash != produced artifact hash | a chain spliced across two different inputs |
| `canonicalHash` mismatch on a graph artifact | a valid proof about a different graph |
| `result` artifact never produced | a chain that does not reach its claim |
| `assurance` field absent | an unproved step passing as a proved one |
| `version` not understood | silent divergence between producer and checker |

The checker is total. No fuel parameter: it does one pass over a finite
list.

Note the fifth row. In a single-component certificate the graph hash
alone was enough. Once the chain crosses components, the splice attack
appears — a valid XSLT step and a valid RDFS step over an unrelated
graph, presented as one argument. Chaining hashes is what closes it, and
it is the main structural cost of the owner's multi-component ruling.

## 6. Two obligations, not one

Owner ruling, 2026-08-26, verbatim:

> "The proof that the code is correct wrt lean4 is also part of this"

A certificate makes two different claims, and conflating them is how a
proof-carrying answer becomes a decoration.

### 6a. The chain is valid

That the steps really do license the result:

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

Read `skills/measuring-inference/SKILL.md` before believing that theorem
when it lands. A checker that returns `false` on everything satisfies it
vacuously. The gate is a matched pair: certificates that must be
accepted, and each malformed shape in the section 5 table that must be
rejected, both pinned.

### 6b. The component that produced each step is itself proved

This is the owner's point, and it is the half that other systems skip. A
step tagged `xslt` is worth what the XSLT implementation is proved to
satisfy — which may be a full refinement against the W3C rule, or an
algorithm-correctness statement, or nothing beyond a totality signature.
The certificate must say which, per step, in the data.

The taxonomy already exists. `docs/test-results/assurance-inventory.json`
classifies every module into one of seven tiers, and the current
distribution over 221 modules is:

| tier | modules |
|---|---|
| merely-tot | 121 |
| algorithm-correctness | 29 |
| unclassified | 17 |
| specification-and-proof | 17 |
| local-lemmas-only | 13 |
| internal-refinement | 13 |
| w3c-refinement | 11 |

1,696 theorems are catalogued; `docs/theorem-registry.md` (2,868 lines)
maps W3C rule ids to engine functions and proof status.

Read that table before making claims about it. **121 of 221 modules are
`merely-tot`** — they carry no correctness statement at all, only a
proof that the function terminates. A step licensed by such a module is
evidence that our code ran, not that it computed the specified thing. A
certificate that did not distinguish those two would be worse than no
certificate, because it would attach the authority of the proved steps
to the unproved ones.

Hence rule 4 of section 4: `assurance` is mandatory, and a rule with no
theorem beyond its constructor records that explicitly
(`constructorOnly`) rather than by omitting the field. A checker may
then apply a policy — accept only chains where every step is at
`w3c-refinement`, or accept any chain but report its weakest link. v1
reports the weakest link and leaves the policy to the caller.

⚠️ **Caveat that must not be lost.** The inventory quoted above is the
**F\* tree's**. The engine behind the wasm ABI is the **Lean** tree, and
it has no equivalent generated inventory today. Until it does, the
`tier` field must be populated from Lean-side evidence — the theorem
exists in `formal/lean4/` and its `#print axioms` output is clean — and
NOT by copying an F\* module's tier onto a Lean step of the same name.
That copy is precisely anti-pattern #31: a matching name is a hint, not
a coverage decision. Producing the Lean-side inventory is a prerequisite
for the `tier` field carrying real information, and is tracked
separately.

### Completeness

Completeness — every derivable result has an accepted certificate — is
NOT claimed in v1. It is what makes the feature useful rather than
correct, and it should follow from the emitter's soundness plus the
existing `fullClosure` completeness lemmas. Stated here so nobody
records v1 as complete.

## 7. Where IKL and LBase come in — and where they do not

Owner ruling, 2026-08-26, verbatim:

> "don't try checking or forcing the Hayes path on consumers"

**Hayes normalization is not in the consumer path.** A caller never has
to run `clNormalize`, and a checker never has to reduce anything to
CL before validating a certificate. The checker in section 5 works
directly on the steps as written. Nothing in v1, and nothing planned,
puts an IKL-to-CL reduction between a consumer and their answer.
`clNormalize` stays what it is: an op a caller may invoke deliberately
when they want the reduction, reporting `preserves: "satisfiability"`
and its `noIntrusion` condition, and nothing else depends on it.

What the CL/IKL work does contribute is the **semantics under which a
multi-component chain means anything at all**. Section 1's chain mixes
an `xslt` step, an `rdfs` step and an `owlRl` step. For that to be one
argument rather than three unrelated ones, the components must be
interpreted in a single semantics. `CL.Interp` is that host structure,
and `RdfEmbed`, `OwlRlSchema`, `RifEmbed` and `SparqlAdequacy` embed
each formalism into it, with the `unified_adequate_*` family stating the
adequacy of each embedding.

So the dependency runs one way only: the unified model theory is what
justifies chaining steps across components, and it sits behind the
checker in the proof, not in front of the consumer in the pipeline.

`that`-terms remain the natural form for a claim ABOUT a derivation —
an endorsement of a certificate, rather than a step within one. That is
a later layer and is not v1.

## 8. Out of scope for v1, named so it is not mistaken for coverage

- **Negative answers.** "G does not entail C under R" is a counter-model
  claim, not a failed search. Decision needed (section 9).
- **OWL DL.** Tableau refutations are a different proof object from a
  rule chain. OWL RL is in; OWL DL is not.
- **Signatures.** A certificate says nothing about who produced it. If
  endorsement is wanted, it composes with the existing VC
  Data-Integrity path
  ([#286](https://github.com/danbri/factoidal/issues/286)), which
  already signs canonical N-Quads with Ed25519. Keep the layers
  separate: the derivation is checkable by anyone, the signature says
  who is willing to be held to it.
- **Completeness** (section 6).
- **A Lean-side assurance inventory.** Section 6b's `tier` field carries
  real information only once the Lean tree has its own generated
  inventory. Until then the field is populated per step from the named
  theorem's own evidence, and never by copying an F\* module's tier onto
  a same-named Lean module. This is a PREREQUISITE for 6b, not a
  nice-to-have, and it is the largest piece of work the owner's third
  ruling implies.

Not out of scope any more, following the owner's 2026-08-26 ruling:
multi-component chains (section 1) and SPARQL solution mappings as a
chain's final artifact. SPARQL's witness is a different shape from a
rule chain — a solution mapping plus the triples it matched — and it
enters as a step kind rather than as a rule row.

## 9. Decisions needed from the owner

1. **Negative certificates.** Return a finite counter-model as the
   witness for "not entailed", or keep negatives verdict-only with the
   reason stated? A counter-model is checkable in the same sense as a
   derivation, so option A keeps the property from section 2. It is more
   work and needs a finite-model extraction the engine does not have
   today. `rhoDf_not_entails_selfLoop_unified` is the Lean form of one.
2. **Inline artifact bodies by default?** Included, the certificate is
   self-contained and large. Omitted, it is small and only checkable by
   someone already holding the inputs. Proposed: inline by default,
   omissible by flag.
3. **JSON only for v1, or JSON plus an RDF profile now?** Proposed:
   JSON only. An RDF profile means choosing a vocabulary, which is a
   larger decision than v1 needs.
4. **Checker policy on weak links.** When a chain contains a step whose
   component is `merely-tot`, should the checker return `true` with the
   weakest tier reported, or `false` unless the caller opted in?
   Proposed: `true` with the tier reported, because a checker that
   silently downgrades a valid chain is as misleading as one that
   silently upgrades it. The caller decides what tier they will accept.

Nothing in section 9 blocks the item-1 work now in flight.
