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

## 0.5 🧭 Measured 2026-07-31 after Phase 1a — this reprioritises everything below

The chain benchmark is a **pathological shape that real vocabularies do
not have**. Measured on the actual artifacts:

| workload | in | out | wall | note |
|---|---:|---:|---:|---|
| 300-class chain | 299 | 45485 | 109 s → **3.24 s** | Phase 1a: 33× |
| **schema.org alone** | 17949 | 29275 | 5.00 s → **4.82 s** | Phase 1a: ~4%, i.e. nothing |
| schema.org + 10k instance triples | 27949 | 54275 | 9.2 s | |
| schema.org + 40k instance triples | 57949 | 129275 | 23.6 s | |

Two conclusions, both uncomfortable for the plan as originally written.

**1. Phase 1a bought almost nothing on real data.** schema.org is wide
and shallow — 17949 triples with no deep `subClassOf` chain — so there is
no deep transitive closure to skip. The 33× is real, and it applies to a
shape our vocabularies do not exhibit. It remains worth having (it fixes
a genuine pathology, and deep hierarchies do exist — SKOS thesauri, GO)
but it is not the win the chain number suggests.

**2. On the shape that actually matters we are already near-linear.**
Doubling instance volume costs 2.57× — about **n¹·²⁹**, not n³. The
problem on real data is **not asymptotic**. It is throughput:

> **~2,500 input triples/second, ~5,500 output triples/second.**

That is the number to beat, and it is a constant-factor number. Mature
engines are one to three orders of magnitude above it.

### What this does to the ordering

* **Phase 2 (dictionary encoding) is promoted to the top of the
  remaining work.** Every comparison currently materialises two fresh
  strings (`triple_cmp` → `String.compare (triple_to_key t1) …`).
  Integer term IDs attack exactly the constant that dominates the
  near-linear regime.
* **Phase 1 (semi-naive) is demoted.** It attacks recursive
  re-derivation, which is the chain pathology — largely addressed by
  Phase 1a. It remains correct and worth landing, but it is no longer
  the biggest lever. The agent working it should not be stopped; the
  result is still wanted, with expectations set accordingly.
* **Phase 3 (persistent indexes) rises with Phase 2** — same target,
  the per-round rebuild and the O(n) membership test.

⚠️ This is the second time today measurement has overturned a confident
ordering. The first was believing the round count was O(n). The
discipline that caught both is the same: state the acceptance criterion
as a number, then measure it, and let the number rewrite the plan.

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

⚠️ Revised 2026-07-31: Phase 1a (schema/data separation) was added after
the fact and outranks the rest for real-world data. The original ordering
below was written before that idea was on the table.

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

### Phase 1a — separate the schema from the data. **Probably the biggest win.**

Added 2026-07-31 after the owner asked what the field's baselines are.
This outranks semi-naive for real data and was missing from the first
draft of this plan.

Real vocabularies have hundreds to a few thousand classes. Real *data*
has millions of statements. Production reasoners exploit that: compute
the class/property hierarchy closure **once, on the schema alone** — a
small graph, with proper algorithms available — then push results to the
instance data in a single pass. The expensive recursive part never
touches the big data.

We do the opposite: one generic fixed-point loop over everything, so
instance triples are dragged through every round of the transitive
computation. The tell is that our chain benchmark is **pure schema**, a
few hundred triples, and takes minutes.

The RDFS rules divide cleanly on paper:

* **Recursive, schema-only:** rdfs5 and rdfs11 (transitivity of
  `subPropertyOf` / `subClassOf`). This is the only real recursion.
* **One-pass, given the schema closure:** rdfs2, rdfs3, rdfs7, rdfs9,
  rdfs4a, rdfs4b, rdfs1, rdfs8, rdfs13 — each a lookup against the
  closed hierarchy.

🔴 **The trap, and why this is not the trivial change it looks like.**
RDFS is *reflective*: the vocabulary can describe itself. A graph may
assert `:p rdfs:subPropertyOf rdfs:subClassOf`, after which an ordinary
instance triple `:A :p :B` **injects a new schema edge** `:A
rdfs:subClassOf :B`. A stratification that computes the schema closure
first and then never revisits it is **unsound** on such a graph. The
same reflectivity is what the metamodeling discussion around RS-1 and
the OWL range-iff correction was circling.

So the deliverable is not "stratify". It is:

1. a **checkable side condition** on the input graph under which the
   fast path is provably equivalent to the general fixed point;
2. the fast path, proved equivalent under that condition;
3. a **detector** for the condition, with fallback to the existing
   general loop when it does not hold;
4. evidence about how often real vocabularies violate it — measure SKOS,
   schema.org, FOAF, Dublin Core rather than assuming.

That shape — a fast path with a proved side condition and an honest
fallback — is the same one `graph_exact` and `closure_chain_wf` already
use elsewhere in this tree.

#### Phase 1a as landed — `RDFS.SchemaSplit.fst`

**The complete set of schema-injection routes.** Derived row by row from
the rule table in `RDF.Entailment.RDFS.Spec.fst`, by reading each row's
conclusion TEMPLATE rather than judging the row's appearance. Eleven of
the twelve conclusion predicates are constants; only rdfs7's is read out
of the data (the object of a `rdfs:subPropertyOf` declaration). So the
question "can this row emit a schema edge?" is decided syntactically,
with no semantic argument.

| # | Route | Premise that is not a schema edge |
|---|---|---|
| R1 | rdfs7 with a `subPropertyOf` object of `rdfs:subClassOf` / `rdfs:subPropertyOf` | any data triple |
| R2 | rdfs8 | `xxx rdf:type rdfs:Class` |
| R3 | rdfs13 | `xxx rdf:type rdfs:Datatype` |
| R4 | container axioms | none — constant |
| R5 | reflexivity harvest (rdfs6/rdfs10 approximation) | `rdf:type rdfs:Class` / `rdf:Property`; emits SELF-LOOPS only |

R2, R3 and R5 read `rdf:type`, so the enumeration continues into the
rows that can mint a NEW `rdf:type rdfs:Class` / `rdfs:Datatype` /
`rdf:Property`:

| # | Route | Needs |
|---|---|---|
| R2a | rdfs2 | `ppp rdfs:domain rdfs:Class` (or Datatype / Property) |
| R2b | rdfs3 | `ppp rdfs:range rdfs:Class` (or …) |
| R2c | rdfs9 | `xxx rdfs:subClassOf rdfs:Class` (or …) |
| R2d | rdfs7 with a `subPropertyOf` object of `rdf:type` | any data triple |
| R2e | rdfs4a / rdfs4b | — conclusion object is always `rdfs:Resource`; SAFE |
| R2f | rdfs1 | — subject ranges over the fixed set D; CONSTANT |
| R3a | rdfs7 with a `subPropertyOf` object of `rdfs:domain` / `rdfs:range` | any data triple — re-enables R2a / R2b |

The descent terminates: a new `subPropertyOf` declaration would
re-enable R1 / R2d / R3a, and the only rows that mint one are rdfs5
(whose conclusion object is drawn from `subPropertyOf` objects already
present, so the object SET never grows), R1 itself, the constant
container axioms, and the reflexivity harvest, which emits self-loops
and a self-loop composes with any edge to reproduce that edge.

**The side condition.** `RDFS.SchemaSplit.schema_stable` — three
per-triple clauses, each naming what it blocks:

* **A** no `rdfs:subPropertyOf` declaration targets the rho-df control
  vocabulary `{subClassOf, subPropertyOf, domain, range, type}` — blocks
  R1, R2d, R3a;
* **B** no `rdfs:domain` / `rdfs:range` declaration names
  `rdfs:Class` / `rdfs:Datatype` / `rdf:Property` — blocks R2a, R2b;
* **C** no `rdfs:subClassOf` edge points AT those three — blocks R2c.

`schema_stable_check` decides it in one linear pass, and is proved SOUND
and COMPLETE against the declarative prop.

**What is proved and what is not.** Proved, machine-checked, no `admit`
and no `--admit_smt_queries`: detector soundness and completeness; that
emitted closure edges carry the walked predicate and source; that the
reachability walk's visited set only grows; that every seed edge carries
a schema predicate; and an anti-vacuity witness pair. NOT proved — and
this is the gap, stated rather than papered over — full extensional
equivalence of the fast path with the general fixed point under the side
condition. That rests on the enumeration above plus "the walk computes
the transitive closure", and is checked by measurement, not by the SMT
solver.

**Why the enumeration is not load-bearing at runtime.** Section 3 of
this document records that this rule set has already defeated confident
reasoning twice in one day. So the dispatcher does not trust the
enumeration. It runs the fast path and then CHECKS the property the
enumeration exists to establish — that no schema edge appeared during
the loop that the pre-computed closure did not already carry — and
discards the result for the general loop if the check fails. The check
is one linear filter and holds unconditionally. If the enumeration has a
hole, the output is still right; only the speedup is lost.

**Evidence: how often real vocabularies violate the condition.** Eight
vocabularies, checked against clauses A / B / C:

| Vocabulary | triples | verdict | violating triple |
|---|---:|---|---|
| SKOS (`skos.rdf`) | 252 | satisfies | — |
| FOAF | 633 | satisfies | — |
| PROV-O | 1145 | satisfies | — |
| GO slim (generic) | 4604 | satisfies | — |
| SKOS axioms (`skills/skos-integrity`) | 35 | satisfies | — |
| **Dublin Core Terms** | 700 | **violates C** | `dcterms:AgentClass rdfs:subClassOf rdfs:Class` |
| **schema.org** | 17949 | **violates A and C** | `schema:additionalType rdfs:subPropertyOf rdf:type`; `schema:DataType rdfs:subClassOf rdfs:Class` |
| **W3C Organization Ontology** | 747 | **violates B** | `org:roleProperty rdfs:range rdf:Property` |

📊 3 of 8 violate (5 satisfy). That is the finding, and it is not a
detail: metamodelling is ordinary practice in shipped vocabularies, and
schema.org's `additionalType` is the reflective-aliasing trap itself,
deployed on millions of sites.

Two of the three violations have live instances, so they are not merely
syntactic: `dcterms:Agent rdf:type dcterms:AgentClass` fires R2c, and
schema.org has seven `rdf:type schema:DataType` triples that do the
same. `schema:additionalType` is never used as a predicate inside the
schema.org vocabulary file, and `org:roleProperty` reaches only the
reflexivity harvest, which runs outside the checked loop.

⚠️ **The consequence.** Gating the fast path on the a-priori condition
alone would surrender Dublin Core Terms and schema.org — two of the most
widely deployed vocabularies there are. That is why the dispatcher gates
on the POST-HOC check instead and keeps `schema_stable` as the stated
hypothesis of the equivalence claim. Anyone reading Phase 1a as "close
the schema first" should read this row of the table first.

**Measured.** Chain benchmark, same machine, same tree, `factoidal
entail --regime RDFS`. "before" is the committed binary at the branch
point; "after" is the same binary rebuilt with the split. Output
compared with `cmp`, not by triple count:

| n | before | after | speedup | output triples | identical? |
|---:|---:|---:|---:|---:|---|
| 20 | 0.054 s | 0.021 s | 2.6× | 309 | byte-identical |
| 40 | 0.203 s | 0.052 s | 3.9× | 979 | byte-identical |
| 80 | 1.601 s | 0.195 s | 8.2× | 3519 | byte-identical |
| 160 | 14.137 s | 0.918 s | 15.4× | 13399 | byte-identical |
| 300 | 109.383 s | 3.953 s | 27.7× | 46089 | byte-identical |

📊 Fitted exponent over n = 80…300: **3.20 before, 2.28 after**. The
output itself is quadratic (46089 ≈ n²/2 at n = 300), so the after-curve
is close to output-optimal. The residual above 2.0 is the reachability
walk's visited-set membership test, which is a list scan; a
logarithmic-time set would take it to n² log n.

Real vocabularies: all eight produce **byte-identical** closures before
and after, with wall time unchanged (they are wide and shallow, so
there was never a deep transitive closure to save on — schema.org
5.09 s → 4.81 s, the rest under 0.4 s either way). The win is specific
to deep hierarchies, which is what the benchmark measures and what the
Gene Ontology-shaped workloads in §0 care about.

Gates, all unmoved: rdf-mt 39 pass, 0 fail (of 39) · rdf11 1031 pass,
0 fail (of 1031) · rdf-semantics 41 pass, 3 fail, 3 skip (of 47) ·
SPARQL 631 pass, 0 fail (of 631) · OWL profile-RL PE 30 of 30, NE 6 of
6, Consistency 76 of 76, Inconsistency 14 of 14 ·
`tools/negative-test-vacuity.py` 11 worked, 14 weak, 3 vacuous (of 42) ·
`rdfs_emit_once_regressions.sh` 8 pass, 0 fail ·
`rdfs_entailment_regime_regressions.sh` 16 pass, 0 fail ·
`rdfs_schema_split_regressions.sh` 9 pass, 0 fail.

**The follow-up this points at.** The post-hoc check turns out to be
strictly more valuable than the a-priori condition, which suggests
removing the condition from the design entirely: replace rdfs11 / rdfs5
INSIDE `rdfs_closure_step` with the reachability-based schema closure,
so the loop keeps its own fixed point and no side condition is needed
for correctness at all. The cost is that a round over an already-closed
hierarchy is expensive for the walk, which is what `schema_dense`
guards against here. Worth doing before Phase 4.

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
