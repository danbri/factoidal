# RDFS materialisation: performance and scalability, in pure F\*

Goal, set by the owner 2026-07-31: **state-of-the-art RDFS semantics
performance and scalability, in pure F\***.

"Pure F\*" is the binding constraint. Every technique below has to be
written in F\*, verified without `admit` / `--lax` / `--admit_smt_queries`,
and extracted. Reaching for hand-written OCaml would be iron rule #1/#4
violation and would surrender the thing that makes this project worth
anything.

---

## 0. Where we actually are

Measured 2026-07-31 on `entail --regime RDFS`, a `subClassOf` chain of
length n plus one typed individual, after the emit-once fix:

| n | wall | output triples |
|---:|---:|---:|
| 20 | 0.03 s | 286 |
| 40 | 0.19 s | 936 |
| 80 | 1.66 s | 3436 |
| 160 | 14.50 s | 13236 |
| 300 | ~120 s (est. from the pre-fix 471 s) | 45155 |

**Time fits n³. Output fits n².** The output exponent is correct — a
chain's transitive closure genuinely has n(n−1)/2 edges. The defect is
the extra factor of n in time: we do cubic work to produce a quadratic
answer.

A 300-class hierarchy is small. SKOS, schema.org, FOAF, Dublin Core, the
Gene Ontology and every real vocabulary are larger. **This is a wall, not
a slope.**

### What is NOT the problem

Three plausible-sounding diagnoses that measurement rules out:

* ⚠️ **Not the round count.** A chain of 300 completes inside `fuel = 100`,
  so derived edges compose with derived edges across rounds and the round
  count is O(log n) by doubling, not O(n). I asserted otherwise in #340
  and was wrong; the correction is on that issue.
* ⚠️ **Not the five rules added on 2026-07-31.** They were a multiplier on
  an algorithm that was already cubic. Post-emit-once they cost ~12%.
* **Not flat data.** 400 flat triples close in 0.06 s, near-linear. The
  cost is specific to recursive rules over hierarchies.

### What IS the problem

**rdfs11 re-derives the entire transitive closure from scratch on every
round.** At round k the graph already holds O(n²) `subClassOf` edges; the
rule iterates all of them and does a successor lookup for each, yielding
O(n) hits — O(n³) work per round to produce O(n²) answers, then repeated
next round. This is textbook *naive* fixed-point evaluation: the engine
recomputes everything it already knows, every round.

Sitting on top of that are large constant factors:

* `rdf_graph = list triple` — no persistent index, membership is O(n).
* `triple_cmp t1 t2 = String.compare (triple_to_key t1) (triple_to_key t2)`
  — **every comparison materialises two fresh strings**. A sort of the
  accumulated graph builds O(n² log n) strings.
* `graph_dedup_sort` re-sorts the whole accumulated graph every round.
* `build_indexed` rebuilds the index from scratch every round.
* No dictionary encoding: terms are compared as strings, everywhere.

### One latent correctness issue, found while measuring

🔴 `rdfs_closure` returns `g` unchanged when `fuel` runs out — no error, no
marker, no diagnostic. Any graph needing more than 100 rounds yields a
**silently incomplete** closure. n = 300 needs ~9 rounds so nothing trips
it today, but the failure mode is exactly the "green means we did not do
the work" shape this project treats as a bug elsewhere (#326, #333, and
the whole negative-test vacuity programme). It needs a marker at minimum,
and ideally a well-founded measure instead of fuel.

---

## 1. What the field already knows

We are not short of ideas; we have been ignoring published ones.

| Technique | Source | Status here |
|---|---|---|
| **Semi-naive (delta) evaluation** | Bancilhon & Ramakrishnan, *An amateur's introduction to recursive query processing strategies*, SIGMOD 1986 | ❌ not used — we are fully naive |
| Dictionary encoding / integer term IDs | universal in RDF stores (HDT, RDF-3X, Virtuoso, RDFox) | ❌ not used in the closure path |
| Persistent SPO/POS/OSP indexes, incrementally maintained | standard | ❌ index rebuilt per round |
| Rule stratification, non-recursive rules evaluated once | standard datalog | ⚠️ attempted 2026-07-31 and **correctly refused** — all five candidate rules turned out to be recursive (see §3) |
| Specialised transitive closure (path doubling, SCC condensation, reachability labelling) | Warren 1975; Nuutila 1995; GRAIL, 2-hop cover | ❌ transitivity computed by iterated join |
| Complexity bounds for RDFS/pD\* entailment | ter Horst, *Completeness, decidability and complexity of entailment for RDF Schema and a semantic extension involving the OWL vocabulary*, JWS 3(2), 2005 | 📖 cited in our docs, not exploited |
| ρdf — a minimal RDFS fragment with better bounds | Muñoz, Pérez, Gutiérrez, *Simple and Efficient Minimal RDFS*, JWS 2009 | 📖 cited, not exploited |
| Parallel / multi-core materialisation | Motik et al., RDFox, AAAI 2014 | ❌ single-threaded (and hard in pure F\*) |
| Distributed closure at web scale | Urbani et al., WebPIE, 2010 | out of scope |
| Backward chaining / query rewriting instead of materialisation | OWL 2 QL is *designed* for first-order rewritability | ❌ we always materialise |

The single highest-value item is the oldest one on the list. Semi-naive
evaluation is from 1986 and is the reason every serious datalog engine is
not cubic.

---

## 2. Plan

Ordered by value per unit of risk. Each phase states its own acceptance
criterion, because "it felt faster" is not a measurement (anti-pattern
#25, and the reason this document exists at all).

### Phase 0 — a closure benchmark. **Blocking everything else.**

There is **no entailment or closure benchmark anywhere in this repo
today.** `tools/bench-competitive.sh` covers SPARQL queries;
`tools/bench-parse-serialize.sh` covers parsing. Closure has nothing.

That is why an O(n³) sat undetected until it knocked out an OWL test:
we discovered a performance problem through a *conformance* failure.
That must not be how we find the next one.

Deliverable: a closure benchmark with synthetic shapes (chain, balanced
tree, diamond/DAG, dense, wide-flat) **and real vocabularies** (SKOS,
schema.org, FOAF, Dublin Core), reporting triples-in, triples-out and
wall time, with committed baselines and a regression gate.

Acceptance: running it reproduces the n³ curve above, and a deliberate
10% slowdown is caught.

### Phase 1 — semi-naive evaluation

Fire rules against the triples derived in the *previous round*, joined
against the accumulated graph, rather than the whole accumulated graph
against itself. Total work becomes proportional to the number of
derivations rather than rounds × graph size.

⚠️ This is where the proof burden lands. `rdfs_closure_sound`,
`rdfs_closure_entails` and the per-row `_licensed` / `_preserves`
theorems must survive, and the delta formulation must be proved to
produce the **same set** as the naive one — not merely a subset. A
semi-naive evaluator that loses derivations is far worse than a slow one.

Acceptance: the chain benchmark drops from n³ toward n²; every W3C score
unchanged; `tools/negative-test-vacuity.py` still reports 11 worked, 14
weak, 3 vacuous (out of 42); the new closure pins still 8 of 8.

### Phase 2 — dictionary encoding

Intern IRIs and literals to integers; compare and index on those. Kills
the string-materialising comparator and shrinks every index.

Design note: this can be confined to the *closure path* — encode on the
way in, decode on the way out — so `RDF.Term` and the parsers need not
change. That keeps the blast radius away from 848 `S_IRI`/`S_BNode`
occurrences across 63 files (the cost RS-3 measured for a different
change).

Acceptance: constant-factor gain measured on Phase 0's real-vocabulary
benchmarks; zero score movement.

### Phase 3 — persistent, incrementally-maintained index

Stop rebuilding `build_indexed` every round. ⚠️ Interacts with the
`ig_wf_sp` proof obligations and #338 — do **not** buy speed by weakening
a theorem.

### Phase 4 — specialised transitive closure

rdfs5 and rdfs11 are the recursive core. Path doubling, or SCC
condensation plus a reachability index, rather than iterated join.

### Phase 5 — backward chaining for query answering

Materialisation is the wrong strategy when the question is a single
query. This is what OWL 2 QL's first-order rewritability is for. Largest
design change; last.

---

## 3. What we tried and why it failed — keep this

**Hoisting the non-recursive rules out of the fixed-point loop** (#340
item 4) was proposed by me on 2026-07-31 and **is unsound**. All five of
rdfs1, rdfs4a, rdfs4b, rdfs8 and rdfs13 produce triples that rdfs9 or
rdfs11 then consume:

| Row | Produces | Consumed by | A hoist loses |
|---|---|---|---|
| rdfs13 | `x rdfs:subClassOf rdfs:Literal` | rdfs9 | `:a a rdfs:Literal` given `:d a rdfs:Datatype . :a a :d .` |
| rdfs1 | `<d> a rdfs:Datatype` | rdfs13 → rdfs9 | the above, one step earlier |
| rdfs8 | `x rdfs:subClassOf rdfs:Resource` | rdfs11 | `:C rdfs:subClassOf :Top` |
| rdfs4a/4b | `x a rdfs:Resource` | rdfs9 | `:a a :Top`, `:b a :Top` |

These are ordinary shapes — "declare a datatype, then use it" — not
exotic ones. The lesson is not "be careful with hoists"; it is that a
stratification argument must be *derived from the rule table*, never
assumed from a rule's appearance.

What landed instead was **emit-once**: each rule emits each result once
rather than once per round, guarded on whether the step's snapshot
already carries it. All twelve rules stay in the loop. Measured 3.7× on
the chain benchmark with byte-identical output, and it restored
`WebOnt-description-logic-501`, which the slowdown had pushed over its
refuter budget.

---

## 4. The F\* dimension

Two questions worth keeping separate.

**Are we using F\* badly?** In places. `triple_cmp` materialising strings
is not an F\* problem, it is a data-structure problem that any language
would punish. Fuel-bounded recursion is a legitimate F\* idiom, but using
it as a *silent* bound is not — a well-founded measure, or at minimum a
marker on exhaustion, is both more honest and more F\*-idiomatic.

**Is verification pushing us toward slow designs?** Yes, and this should
be said plainly rather than discovered later. Snapshot semantics exists
partly because it makes the `ig_wf_sp` proofs tractable. That is proof
convenience shaping a performance-hostile design. It is a real tension,
not a reason to abandon either side — but every phase above must be
explicit about which theorems it has to re-establish, and none may buy
speed by weakening a statement.

The honest position: **pure-F\* is not the reason we are cubic.** We are
cubic because we implement naive evaluation. Semi-naive evaluation is
expressible in F\* and provable in F\*; it is simply work nobody has done
here yet.
