---
title: "This answer is a theorem: the certified core-RDFS closure"
description: "SPARQL answers over the six-rule core-RDFS (ρdf) closure are machine-checked equivalent to entailment — run the certified engine live, watch the checker refuse false claims, and measure why fewer rules with a theorem beats more rules without one."
layout: hub.njk
series: docs-hub
series_order: 32
status: published
tests: tests/hub/post32_test.mjs
---

Every earlier post showed the engine *passing tests*: 1662 W3C
conformance tests, 0 failures. Tests certify behaviour on the inputs
somebody thought to write down. This post shows something stronger,
landed across 2026-08-05/07: for a precisely-stated fragment of RDFS,
the engine's query answers are **theorems** — machine-checked
equivalent to model-theoretic entailment, on every input in the
fragment, including the ones nobody thought to write down.

The chain, each link an F\* theorem about the shipping code:

> **model theory ⟷ entailment ⟷ closure ⟷ termination test ⟷ index ⟷
> BGP matching ⟷ query answers**

The fragment is **corerdfs**: `rdf:type`, `rdfs:subClassOf`,
`rdfs:subPropertyOf`, `rdfs:domain`, `rdfs:range` — the working core
of RDFS schema reasoning. That is this project's API name for the
fragment the literature calls **ρdf** ("rho-df" in our code and
theorem names), introduced by Muñoz, Pérez & Gutierrez in
[*Simple and Efficient Minimal RDFS*](https://users.dcc.uchile.cl/~cgutierr/papers/jws09.pdf)
(J. Web Semantics 7(3), 2009), who proved it captures exactly the
inferential core of RDFS once the self-referential and infinite rows
are set aside. Everything below runs live in your browser against the
same extracted engine the theorems are about.

## What the two API calls do, in plain terms

**`fn.coreRdfsClosure(data)`** takes an RDF document (Turtle or
N-Triples text) and returns `{ok, ntriples, rounds}`: the same graph
with **every fact the five schema properties imply added as an
explicit triple**. That is all "closure" means. If your data says
`:Engineer rdfs:subClassOf :Employee` and `:ada rdf:type :Engineer`,
the output also contains `:ada rdf:type :Employee` — and every other
consequence, chained to any depth (`rounds` reports how many passes
that took). You run it once, store or query the result, and from then
on **plain SPARQL — no reasoner, no entailment setting — sees every
schema-implied fact**, because the facts are physically there.

**`fn.coreRdfsCheck(data)`** answers one question before you
rely on that: **does the proved guarantee apply to this data?** It
returns `{ok, fragment}`. `fragment: true` means every triple in the
document is inside the shape the theorems quantify over, so the
closure's answers carry the machine-checked soundness *and*
completeness guarantee — nothing false added, nothing implied
missed. `fragment: false` means the data steps outside that shape
(for example a literal where the theorems require an IRI); the
closure still runs and is still sound, but the *completeness* theorem
no longer vouches for it.

Together they replace "trust the vendor's reasoner settings" with a
two-call contract: check whether the guarantee applies, then
materialise the consequences — with both steps' behaviour stated and
proved in the [theorem registry](../../../theorem-registry/).

## A schema, some facts, and a guarantee

An ordinary org-chart ontology. Note one thing: object positions hold
IRIs, not literals — that is a real boundary of the proved fragment,
and the checker below will tell you so rather than leaving you to
find out.

```turtle
PREFIX : <http://example.org/org#>

:Engineer      rdfs:subClassOf :Employee .
:Employee      rdfs:subClassOf :Agent .
:manages       rdfs:domain     :Manager .
:manages       rdfs:subPropertyOf :worksWith .
:Manager       rdfs:subClassOf :Employee .

:ada    a :Engineer .
:grace  :manages :ada .
```

```observable-js
ttl = `
  PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
  PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
  PREFIX : <http://example.org/org#>

  :Engineer      rdfs:subClassOf :Employee .
  :Employee      rdfs:subClassOf :Agent .
  :manages       rdfs:domain     :Manager .
  :manages       rdfs:subPropertyOf :worksWith .
  :Manager       rdfs:subClassOf :Employee .

  :ada    rdf:type :Engineer .
  :grace  :manages :ada .
`
```

**Step 1 — ask whether the guarantee applies.** The fragment predicate
is a decidable check, extracted from the same F\* definition the
theorems quantify over. This is the difference between fine print and
an API: you can ask *before* trusting an answer.

```observable-js
return pretty(await fn.coreRdfsCheck(ttl));
// {ok: true, fragment: true} — the certified path applies to this data
```

**Step 2 — run the certified closure.** Six rules, not the engine's
full twelve: exactly the six the rho-df theorems cover
(rdfs2/3/5/7/9/11). The stopping test is the ordinary length-equality
check — which is itself proved to be a faithful proxy for semantic
saturation on freshly-parsed data, not a heuristic.

```observable-js
closed = fn.coreRdfsClosure(ttl) // a promise: dependent cells receive it awaited
```

**Step 3 — query it.** Is Ada an `:Agent`? No triple says so; two
subclass steps entail it.

```observable-js
const dataset = await fn.parse(closed.ntriples, {format: "ntriples"});
const rows = await fn.query(dataset, `
  # Does the closure make Ada an Agent, via two chained subclass steps?
  PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
  PREFIX : <http://example.org/org#>
  ASK { :ada rdf:type :Agent }
`);
return pretty(rows); // true — and that "true" is the theorem below
```

**Step 4 — say more, get more (RDFS-Plus).** Ask the closure who
works with whom, and it answers one row: `grace → ada` (derived by
rdfs7 from `manages ⊑ worksWith`). But working-with is naturally
mutual, and RDFS cannot even *say* that. One OWL triple can —
`:worksWith rdf:type owl:SymmetricProperty` — and the **RDFS-Plus**
tier (RDFS plus the practical OWL subset: `sameAs`, `inverseOf`,
symmetric/transitive/functional/inverse-functional properties,
class/property equivalence — "RDFS-Plus" in Allemang & Hendler's
*Semantic Web for the Working Ontologist*, "RDFS++" in AllegroGraph)
acts on it:

```observable-js
const withSym = ttl + `\n  :worksWith rdf:type <http://www.w3.org/2002/07/owl#SymmetricProperty> .\n`;
const plus = await fn.rdfsPlusClosure(withSym);
const dataset2 = await fn.parse(plus.ntriples, {format: "ntriples"});
const rows = await fn.query(dataset2, `
  # Who works with whom, now that the symmetric property makes it mutual?
  PREFIX : <http://example.org/org#>
  SELECT * WHERE { ?x :worksWith ?y } ORDER BY ?x
`);
return pretty(rows); // TWO rows now: grace→ada and ada→grace
```

The warrant changes with the vocabulary, and the page says so
plainly: every rule `rdfsPlusClosure` runs carries a **proved
licensing and truth-preservation lemma** (the symmetric step here is
row prp-symp, `prp_symp_licensed`, in the
[registry](../../../theorem-registry/)) — nothing invented, every
derivation certified rule-by-rule. What this tier does *not* carry is
corerdfs's chain-level completeness: `owl:sameAs` is equality, and
the Herbrand construction behind the completeness theorem does not
survive it. Three regimes, three precisely-stated warrants — corerdfs
(sound **and** complete), RDFS-Plus (every step certified), OWL RL
(the full engine, 1662 W3C tests) — each labelled with exactly what
is proved.

**What makes this `true` different**: the landed theorem
`theorem_rdfs_regime_bgp_exact_answer` (with its ASK corollaries,
stated on the literal `eval_ask_query` entry point) says the answers
computed this way are *exactly* the rho-df-entailed consequences —
sound and complete, an if-and-only-if. Not "we tested it a lot":
checked by z3 for every graph in the fragment, under hypotheses that
are themselves decidable checks or theorems (the fragment check you
ran in step 1; saturation-class facts proved for freshly-parsed
data). The full chain, theorem by theorem, lives in the
[theorem registry](../../../theorem-registry/).

## What the checker refused to let us claim

The strongest evidence a proof system is doing work is not the
theorems it proves — it is the claims it rejects. Three from this
program, each caught before it could mislead anyone:

**The goal statement itself was false.** We first asked for:
"`rdfs_closure g` computes exactly the RDFS-entailed fragment
triples." F\* produced counterexamples, now machine-checked theorems:
`[X subClassOf Y]` RDFS-entails `[X subClassOf X]` (reflexivity is
semantically forced), yet no closure rule derives it — and
`cond_resource` entails `[Z rdf:type rdfs:Resource]` for *every* IRI
`Z`, including ones absent from the graph, which no finite closure can
enumerate. The honest theorem quantifies over the six rho-df semantic
conditions instead — the same reduction the published rho-df
literature makes, rediscovered here by refutation.

**Fragment preservation is false.** It is natural to assume a
fragment graph stays in the fragment after closure. It does not:

```observable-js
const escape = `
  PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
  PREFIX : <http://example.org/x#>
  :P rdfs:subPropertyOf rdfs:subPropertyOf .
  :a :P _:b1 .
`;
const before = await fn.coreRdfsCheck(escape);
const closedEsc = await fn.coreRdfsClosure(escape);
const after  = await fn.coreRdfsCheck(closedEsc.ntriples);
return pretty({fragmentBefore: before.fragment, fragmentAfter: after.fragment});
// true, then false — one rdfs7 step derives ':a rdfs:subPropertyOf _:b1',
// whose blank-node object leaves the fragment. Machine-checked as
// rho_df_frag_preservation_fails; the theorems state their hypotheses
// on the closure RESULT because of exactly this graph.
```

**"The solution list contains μ" is false.** The evaluator emits
bindings in a planner-determined order, so the intuitive completeness
statement — a caller-constructed solution appears in the result
list — is refutable with two triple patterns. The true statement is
at the *answer* level: the engine returns a solution instantiating to
the same triples. Nothing downstream inspects binding order, so
nothing weaker was proved — but a subtly false statement was kept out
of the registry.

## What this empowers, per audience

**Analysts / users.** Within the fragment, "no missed inferences" is
now a theorem, not a vendor claim. A `false` ASK answer means the
fact is genuinely not entailed — completeness is the half tests can
never give you, because a test suite only checks the entailments its
authors enumerated. And the fragment checker means you always know
which regime you are in.

**Developers.** Two new API calls (`fn.coreRdfsCheck`,
`fn.coreRdfsClosure`) plus a contract that is unusual in this space: the
[registry](../../../theorem-registry/) names every theorem, every
hypothesis, and every boundary, in one table. The planner lemma
(`lemma_choose_best_tp_cover`) is a developer guarantee too: query
reordering is proved answer-preserving, so optimizer changes cannot
silently alter results on this path.

**Auditors / standards people.** The claims language is calibrated —
"proved sound and complete with respect to an independent F\*
formalisation of the rho-df conditions, under stated hypotheses" —
and the trust surface (three string-ordering axioms, the extraction
step, the assume-val realisations) is enumerated in the same
registry. The refutation section above is reproducible: the
counterexamples are theorems in the tree you can re-check.

## Can the proofs help performance? Measure it here

Yes — in three ways, one of which you can time right now.

**Fewer rules, same answers, with a warrant.** For fragment data, the
six-rule closure provably yields the same fragment query answers as
running more machinery — so the cheaper path needs no safety margin.
The cell below builds a subclass chain, runs both the certified
six-rule closure and the engine's full twelve-rule RDFS closure, times
them in your browser, and *checks the fragment answers agree*:

```observable-js
// A 60-class subclass chain with typed members: fragment-only data.
let chain = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\nPREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\nPREFIX : <http://example.org/c#>\n";
for (let i = 0; i < 60; i++) chain += `:C${i} rdfs:subClassOf :C${i+1} .\n`;
chain += ":x rdf:type :C0 .\n";

const t0 = performance.now();
const six = await fn.coreRdfsClosure(chain);
const t1 = performance.now();
const full = await fn.owlClosure(chain, "RDFS"); // the full twelve-rule RDFS set
const t2 = performance.now();

return pretty({
  sixRuleMs: +(t1 - t0).toFixed(1),
  fullClosureMs: +(t2 - t1).toFixed(1),
  derivedTriples: six.ntriples.split("\n").filter(l => l.trim()).length,
  note: "timings are measured in YOUR browser just now — not vendor numbers"
});
```

The point is not the specific ratio your machine shows; per this
project's measurement discipline no static number is printed here at
all. The point is the *warrant*: dropping half the rules is usually a
correctness gamble, and here it is a theorem.

**A faithful stopping test.** The closure stops when an iteration adds
nothing. That test is now proved equivalent to semantic saturation
(no "one extra round to be safe" needed) — and the same theorems are
the safety net for the planned round-count optimization of the
closure loop (issue #340): any rewrite that preserves the proved
saturation predicate is answer-preserving by composition, so the
optimizer can be aggressive where it used to be conservative.

**Index-only paths.** The index well-formedness *and* completeness
theorems (all six buckets) mean a bucket probe provably serves every
matching triple — no defensive fallback scans on the certified path.

## The honest boundaries

Stated here exactly as the theorems state them: the fragment excludes
literals and RDF 1.2 triple terms in object position (a consequence of
RDF's own syntax forbidding literal subjects — the REC's `lg`/`gl`
surrogate rules are a future milestone, not a patch we skipped), and
`rdfs:subClassOf` reasoning covers IRI-named classes (blank-node
classes are a recorded engine narrowing). Reflexivity rows
(`rdfs6`/`rdfs10`) are outside rho-df by definition. Data can
*contain* literals freely — labels and values simply ride along
outside the entailment claim. Every boundary traces to a named
finding in the [registry](../../../theorem-registry/), most of them
machine-checked counterexamples rather than prose caveats.

*Everything above ran against the extracted engine certified at
commit `17eb2df`: combined 1662 pass, 0 fail (out of 1662) on the
W3C suites, hub cells 253 pass, 0 fail (out of 253 — 262 after
this post's own 9 pins landed).*
