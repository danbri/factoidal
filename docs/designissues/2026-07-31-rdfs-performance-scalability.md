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

### ⚠️ Calibration: how much can dictionary encoding actually buy?

I promoted Phase 2 from **reading** `triple_cmp`, not from profiling —
exactly the move `skills/measuring-inference` rule 1 forbids. Measured
2026-08-01, holding graph shape and output constant (17737 triples) and
varying only IRI length:

| IRI length | wall | vs 20-char |
|---:|---:|---:|
| 20 chars | 4.55 s | 1.00× |
| 100 chars | 4.98 s | **1.09×** |
| 400 chars | 8.35 s | 1.84× |

At **realistic** IRI lengths — schema.org's are ~30 chars — string
*length* accounts for well under 10% of the time. At absurd lengths it
reaches 84%.

⚠️ **What this does and does not settle.** It measures the *marginal*
cost of longer strings. It does **not** measure the cost of using
strings at all: even a 20-char comparison costs a pointer chase, a
length check and a byte loop where an integer compare is one
instruction, and it says nothing about the allocation `triple_to_key`
does on every comparison. So this is a **lower bound** on what Phase 2
can recover, not an estimate of it.

**Expectation setting, so the result is judged honestly when it lands:**
a 1.3–2× improvement is a good outcome. A 10× would be surprising and
should be re-measured before it is believed. If the measured gain is
small, that is a finding about where the time really goes, not a failed
phase — and it would promote Phase 3 (persistent indexes, killing the
per-round rebuild and the O(n) membership test) above it.

### 🔴 The blowup nobody had measured: hierarchy depth × instance count

While calibrating the above, a probe with a 200-deep chain and 4000
instances **exceeded a 10-minute cap** — on 4200 input triples, where
schema.org's 17949 close in 4.8 s.

The cause is the product, not either factor. Every instance of the
chain's root acquires a `rdf:type` triple for **every** ancestor:
4000 × 200 = 800,000 derived triples. Neither of our existing benchmarks
sees this — a chain alone has no instances, and schema.org is too shallow
for it to bite.

This is the shape that real deployments hit: Gene Ontology annotations
are exactly deep hierarchy × many instances. **Phase 0's benchmark must
include it**, and it is a stronger argument for Phase 4 (specialised
transitive closure / reachability labelling) than the chain ever was —
with a reachability index, an instance's ancestor set is answered without
materialising one triple per ancestor.

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

#### ✅ Landed 2026-08-02 — `tools/bench-closure.sh`

`tools/bench_closure.py` (measurement) behind `tools/bench-closure.sh`
(binary check, `.claude-runs/` logging). Five synthetic shapes and five
real vocabularies, pinned in
[`third_party/vocabularies/PROVENANCE.md`](../../third_party/vocabularies/PROVENANCE.md)
with URL, retrieval date, SHA-256 and licence. Wall time and CPU time
are reported separately, because the OWL cap-escape family is budgeted
in CPU seconds. `--check` gates against a committed baseline;
`--update-baseline` moves it. The dashboard fragment lands in the
public report through `generate-report.sh`.

📊 **Frozen baseline** — `docs/test-results/closure-bench-baseline.json`,
median of 3 runs per case, `--regime RDFS`:

| real vocabulary | in | out | ratio | wall | out-triples/s |
|---|---:|---:|---:|---:|---:|
| SKOS | 254 | 422 | 1.7× | 0.029 s | 14,552 |
| FOAF | 635 | 863 | 1.4× | 0.051 s | 16,922 |
| Dublin Core terms | 700 | 1272 | 1.8× | 0.085 s | 14,965 |
| schema.org 30.0 | 17949 | 29275 | 1.6× | 4.686 s | 6,247 |
| QUDT 3.4.0 | 130404 | 508139 | **3.9×** | **270.9 s** | **1,876** |

Fitted exponents on the synthetic shapes (log-log least squares, wall):

| shape | n range | wall ~ n^k | output ~ n^k |
|---|---|---:|---:|
| chain | 20–160 | **1.96** | 1.82 |
| tree | 128–1024 | 1.40 | 1.15 |
| diamond | 32–192 | **2.26** | 2.01 |
| wide-flat | 500–4000 | 1.06 | 0.99 |
| dense | 250–2000 | 1.35 | 0.99 |

Run-to-run spread over the 25 repeated cases: median 3.3% wall, max
8.0%. That is what sets `--check`'s 20% default tolerance — a gate
tighter than the noise fires on the noise.

⚠️ **The chain exponent is 1.96, not the 1.29 first reported.** The
first figure came from a three-point fit stopping at n=80; adding n=160
nearly doubled it. Three points do not fit an exponent, and a fit is
only as honest as its range — the range is now printed beside every
exponent for exactly this reason. The n≤80 chain looks near-linear
because it fits inside `fuel=100` comfortably; the curve is elsewhere.

#### 🔴 QUDT — the number Phase 0 was built to find

QUDT tripped the original 120 s cap. It is **not a hang**: measured
separately with a 900 s cap it completes in **272.5 s**, producing
**508,139 triples from 130,404** — a 3.9× expansion, more than twice
schema.org's 1.6×. Peak resident memory was **1.1 GB**.

The cap was therefore raised to 400 s for vocabularies (120 s stays for
synthetic shapes, and under `--quick`). A cap trip can only ever flip a
status; a measured 272.5 s can regress or improve by a percentage that
`--check` can see. Size a cap to measure the largest real input shipped,
and no larger.

**The phase split, measured before naming a culprit** (rule 1). On the
same file: `factoidal count` takes 2.20 s and `factoidal dump`
(parse + serialize) takes 2.32 s. So parsing and serialization together
are **under 1%** of the 272.5 s. The remaining 270 s is closure. This is
the one case so far where the closure really is where the time is —
worth stating explicitly, because the last two times that was assumed it
was false (§0.5, and #341).

**Throughput degrades with size, on real data:**

Baseline medians (3 runs each; the 272.5 s quoted above was the separate
single run under the 900 s cap, 0.6% off the median — inside the 3.3%
run-to-run spread):

| | schema.org | QUDT | ratio |
|---|---:|---:|---:|
| input triples | 17,949 | 130,404 | 7.3× |
| output triples | 29,275 | 508,139 | 17.4× |
| wall | 4.686 s | 270.9 s | **58×** |
| out-triples/s | 6,247 | 1,876 | **0.30×** |

⚠️ Two vocabularies are two points, not a scaling curve — they differ in
shape as well as size, and the expansion ratio differs (1.6× vs 3.9×), so
some of the 57× is simply that QUDT derives far more. Per *output*
triple the engine is 3.3× slower on the larger graph. That per-triple
degradation is the part not explained by output volume, and it is the
part an optimisation can take back. At schema.org's own observed rate,
508,139 triples would take 81 s rather than 271 s.

⚠️ **The 400 s cap is now sized to one vocabulary.** A vocabulary
appreciably larger than QUDT would trip it, and that trip would be
correct behaviour, not a bug in the cap.

#### ⚠️ The diamond shape, and what it does not license

The diamond shape has the worst synthetic exponent at 2.26 — but on the
full sweep the chain is 1.96, not the 1.29 the three-point fit showed, so
the gap between "duplicate derivation routes" and "depth" is much smaller
than it first appeared. Both are super-linear *in the synthetic set*.

This does **not** reorder the plan on its own. Rule 2 of
`skills/measuring-inference` says a synthetic shape does not speak for
real vocabularies, and the diamond's 32× expansion at n=128 is nothing
like the 1.4–3.9× the real ones show. What it does say is where to look:
**measure how much diamond structure QUDT actually contains** before
concluding that semi-naive evaluation is what QUDT needs. QUDT is now
the concrete target, and any Phase 1 or Phase 2 claim should be measured
against its 272.5 s before it is believed.

⚠️ The `--check` regression gate is **not yet wired into
`w3c-tests.sh`**; the baseline exists but nothing fails when it moves.
That wiring is the remaining part of this phase's acceptance criterion.

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

#### 🟡 Landed 2026-08-02 — `RDFS.Closure.SemiNaive.fst`

⚠️ The proof burden above was **not discharged, and deliberately so.**
The design instead makes the delta loop *unable* to be wrong in a way
that matters, which is a different and cheaper guarantee.

**Soundness is free.** Every row in the module applies a rule body
copied from `RDFS.Closure` to a *subset* of its inputs. It can therefore
only derive triples the naive loop also derives. The only possible
error is deriving too **few**.

**Completeness is checked, not proved.** `rdfs_closure_checked` runs the
delta loop, then applies one full naive `rdfs_closure_step` to the
answer:

* adds nothing → the answer is a fixed point of the naive step
  containing the input. The naive closure is the *least* such fixed
  point, so naive ⊆ ours; soundness gives ours ⊆ naive. Equal — return
  the fast answer.
* adds something → the delta loop missed a derivation on this graph.
  Discard it and run the untouched `rdfs_closure`.

A hole in the delta reasoning costs one wasted fast pass, never a lost
derivation. Same discipline as Phase 1a's post-hoc check, and for the
same reason recorded as rule 6 of `skills/measuring-inference`:
confident reasoning about this rule set has been wrong repeatedly — #340
item 4 proposed hoisting five rows out of the loop and all five turned
out to be recursive.

**The twelve rows split four ways**, and only the first three needed
delta variants:

| form | rows | why | delta treatment |
|---|---|---|---|
| A | rdfs4a, rdfs4b, rdfs8, rdfs13 | index is a duplicate filter, not a premise | drive off the delta; full index kept for `emit_once` |
| B | rdfs1, container membership | premise list is a **constant** — no graph read | round 1 only |
| C | rdfs9, rdfs11, rdfs5 | walk graph, probe index | two terms: (Δ driver × full index), (full driver × Δ index) |
| D | rdfs7, rdfs2, rdfs3 | index on both sides | two terms: (Δ decls × full data), (full decls × Δ data) |

Form B *is* a hoist, and is safe only because those two rows read no
graph at all — unlike the five rows #340 targeted. The final check would
catch it regardless.

Both join terms are required for forms C and D; dropping either loses
derivations. The cross term (Δ × Δ) is covered twice, harmlessly, since
the full graph contains the delta.

`sorted_diff` computes the round delta as one linear merge, relying on
`graph_dedup_sort` leaving each round key-sorted and duplicate-free.

**Zero diff to `RDFS.Closure.fsti`.** The naive loop remains the
reference implementation and the fallback. `RDFS.SchemaSplit`'s dispatch
— which already owns every call site — had its three general-path
fallbacks redirected, so no consumer code changed.

Verified under z3 4.13.3 with no `--lax`, no `admit`, no
`--admit_smt_queries`. One `--z3rlimit 30` on the loop, matching the
budget `RDFS.Closure.rdfs_closure` already carries for the same
termination obligation.

#### 🔴 Measured: semi-naive gained exactly nothing, because it never runs

| | baseline | semi-naive | change |
|---|---:|---:|---:|
| QUDT | 270.9 s | 270.839 s | none |
| schema.org | 4.686 s | 4.6875 s | none |

Output byte-for-byte identical, so the delta loop is correct. It simply
is not reached.

`RDFS.SchemaSplit`'s dispatch enters the general path only when
`schema_dense base` holds, and that test is
`edges > 8 * srcs + 64`. QUDT has **709 schema edges over 295 sources**,
so it needs `709 > 2424` — false. QUDT takes the schema-split **fast**
path, that path succeeds, and the three fallbacks Phase 1 redirected are
never entered. The 270.9 s belongs to `rdfs_closure_no_trans` inside the
fast path.

⚠️ This is rule 1 of `skills/measuring-inference`, broken by the person
who wrote rule 1: an acceptance criterion was set against a 270.9 s
number **without first establishing which code path produced it.** The
rule says measure the phase you intend to change. A dispatch branch is a
phase.

The module is kept: it is correct, verified, byte-exact, and it is the
general-path evaluator whenever `schema_dense` does hold. It is not a
measured win and is not presented as one.

#### The profile, and what it bought

`callgrind` on schema.org `entail`, 38.7 G instructions retired:

| family | share |
|---|---:|
| garbage collection (marking, oldify, allocate, modify) | ~31% |
| string build and compare (concat, blits, `string_equal`) | ~19% |
| `mem_triple` / `triple_eq` / `subject_eq` | ~8% |

`mem_triple` has exactly one caller: `graph_add`, which is
`if mem_triple t g then g else g @ [t]` — a linear scan **and** a linear
append, per triple. `add_triples_if_new` folds that, so adding k triples
to a graph of n costs O(n·k) comparisons and O(n·k) freshly allocated
cons cells. Those cells are why GC is the largest single family.

`add_triples_if_new_bulk` replaces the k scans with one sorted merge, at
the two reflexivity-harvest sites where `g` is the whole closed graph.
`add_triples_if_new` itself is unchanged —
`lemma_add_triples_if_new_memP` is proved about that exact definition.

📊 **Criterion stated before the work: QUDT under 150 s. Result:**

| | baseline | bulk union | change |
|---|---:|---:|---:|
| QUDT | 270.9 s | 264.3 s | 1.02× ❌ |
| schema.org | 4.686 s | **2.558 s** | **1.83×** ✅ |

❌ **The criterion is missed.** The hypothesis that this quadratic
dominates QUDT is wrong. The fix is real and large on the graph that was
*profiled*, and almost nothing on the graph it was aimed at — because
callgrind on QUDT costs about four hours, so schema.org was profiled
instead, and rule 2 duly applied.

#### 📊 The scaling curve, on one vocabulary

An earlier "n^2.03" in this note came from comparing schema.org with
QUDT — two different vocabularies, so not a curve at all. On QUDT alone,
by prefix:

| input | output | wall | out-triples/s |
|---:|---:|---:|---:|
| 16,000 | 70,214 | 15.94 s | 4,405 |
| 32,000 | 211,850 | 72.11 s | 2,938 |
| 64,000 | 328,364 | 147.46 s | 2,227 |
| 128,000 | 479,057 | 246.01 s | 1,947 |
| 139,552 | 508,139 | 264.30 s | 1,922 |

Against **output** this is **n^1.42**, not n². Throughput falls smoothly
from 4,405 to 1,922 output triples per second.

⚠️ Prefixes of an N-Triples dump are a biased sample — the subject order
is whatever the serializer emitted, not a random draw. Good enough for a
scaling exponent, not for absolute claims about a 16k-triple vocabulary.

The 16k prefix costs 15.9 s, so callgrind on it is ~13 minutes rather
than four hours: same vocabulary, same code path, tractable. That is the
profile the next fix should come from — not another one taken on
schema.org.

#### ✅ The profile taken on the right vocabulary, and the fix it bought

`callgrind` on the 16,000-triple QUDT prefix, 151 G instructions
retired — a completely different shape from schema.org's:

| family | share |
|---|---:|
| **string construction** (`unsafe_blits` 15.9%, `blit_string` 8.8%, `memcpy` 8.8%, `sum_lengths` 8.2%, `alloc_string` 4.2%, `String.concat` 3.3%) | **~49%** |
| garbage collection | ~17% |
| string comparison | ~5% |
| the key functions (`triple_to_key`, `term_to_key_total`, `subject_to_key`) | ~4% |

About **half the program was building triple key strings.** `triple_cmp`
calls `triple_to_key`, a `String.concat` over the subject, predicate and
object IRIs in full, and `sortWith` calls that comparator O(N log N)
times — two key builds per comparison. At N = 500,000 that is ~38× more
string building than the job needs, and most of the GC share was
collecting those same keys.

**The fix:** `graph_dedup_sort` becomes decorate-sort-undecorate (the
Schwartzian transform) — build each key once, sort `(key, triple)` pairs
on the precomputed key, strip. `RDF.Indexed.build_bucket` already does
exactly this for its six index buckets, so this follows an established
pattern in the tree; it also already demonstrates `List.Tot.map` survives
a half-million triples here.

📊 **Criterion was QUDT under 150 s. Result: 143.87 s.** ✅

| | before | after | change |
|---|---:|---:|---:|
| QUDT | 264.3 s | **143.87 s** | **1.84×** |
| schema.org | 2.558 s | **1.622 s** | 1.58× |

Byte-for-byte identical output on both (508,139 and 29,275 triples).

**Cumulative over the session:**

| | opening baseline | now | change |
|---|---:|---:|---:|
| QUDT | 270.9 s | 143.87 s | **1.88×** |
| schema.org | 4.686 s | 1.622 s | **2.89×** |
| QUDT out-triples/s | 1,876 | 3,532 | 1.88× |
| schema.org out-triples/s | 6,247 | 18,048 | 2.89× |

⚠️ **The proof cost is real and was paid.** The change broke
`lemma_graph_dedup_sort_memP` — every triple the dedup returns came from
the input — and the build caught it: layer 9 failed, later layers never
started, the binary stayed at the previous commit. Re-established with a
walk lemma for the decorated dedup plus a four-step chain
(walk lemma → `memP_map_elim` → `lemma_sortWith_memP`, which was already
generic over the element type → `memP_map_elim`). No `--lax`, no
`admit`. The proof got longer because the data structure got one level
deeper.

#### What this says about the plan

Phase 2 was "dictionary encoding", calibrated in §0.5 at 1.3–2× with
"10× should be disbelieved". The measured 1.84× on QUDT lands inside that
band — but it came from *not* encoding anything. Building each key once
instead of 2·log N times is the cheap part of what dictionary encoding
would buy, obtained without changing a single data type.

Whether full dictionary encoding is still worth it is now an open
question with a new baseline: string construction was ~49% of the
program and this removes the bulk of it, so the remaining headroom is
smaller than §0.5 assumed. Re-profile the 16k prefix before starting
Phase 2.

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
