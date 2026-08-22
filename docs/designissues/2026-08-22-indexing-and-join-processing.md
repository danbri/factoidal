# Indexing and join processing: literature → plan

Owner steer, 2026-08-22, verbatim:

> "Both Lean and F\* come with strengths and weaknesses but with
> careful indexing and study of the literature and other sources, we
> ought to he able to scale and be v v fast."

Read against the founding view recorded at the top of CLAUDE.md the
same day: implementations may be fast and tunable, the spec they
satisfy stays fixed, and the relation between them is a proof.

Tracking: https://github.com/danbri/factoidal/issues/484 (open
question on indexed joins) and
https://github.com/danbri/factoidal/issues/466 (Lean tree).

## 1. Where we actually are (inspected 2026-08-22, not recalled)

- **F\* tree, in-memory:** `RDF.Indexed.fst` is a generic association-
  list **bucket map** (`bucket_map`, `bucket_lookup`, `bucket_push`,
  `build_bucket`) instantiated at `triple`, giving
  `find_objects_indexed` / `find_subjects_indexed`. That is a hash
  bucket per key position — NOT a permutation-index family, NOT
  ordered, NOT a trie. `RDF.Indexed.KeyInjectivity.fst` proves the
  U+001F-joined key is injective on separator-free strings (#338).
- **F\* tree, on disk:** the COTTAS/Parquet base plus sidecars, and an
  HDT reader (`HDT.Triples.fst`, `HDT.Dictionary.fst`). Planning
  modules exist: `SPARQL.Plan.AccessPath.fst`,
  `SPARQL.Plan.Pruning.fst`, `SPARQL.Plan.Streamable.fst`.
- **Joins:** binary joins — hash join with the key-vs-compatibility
  fix from #337.
- **Lean tree:** plain nested-loop scan, no index. Measured quadratic
  (2,891 ms at 8k triples vs the F\* engine's 205 ms).

So today BOTH trees run **binary join plans**. That is the fact that
matters for what follows.

## 2. The literature that is load-bearing

Verified against sources (URLs below), not quoted from memory.

**(a) Binary join plans are asymptotically suboptimal — this is a
theorem, not an opinion.** Atserias, Grohe and Marx (2008) proved a
tight bound (the **AGM bound**) on the maximum result size of a full
conjunctive query given input relation sizes. Ngo, Porat, Ré and Rudra
(2012) gave the first join algorithm running within that bound. The
standard illustration: the triangle query has AGM bound N^1.5, while
every binary-join plan is Ω(N²) — so no join ordering, no matter how
clever the planner, fixes it. Cyclic patterns are common in real
SPARQL.

**(b) Worst-case optimal joins are implementable with ordinary
structures.** Veldhuizen's **Leapfrog Triejoin** (ICDT 2014, LogicBlox)
achieves the NPRR bound with a much simpler algorithm and proof, works
over conventional B-trees/tries, and is optimal for finer-grained
instance classes than NPRR. It is a multi-way, variable-at-a-time
intersection of sorted iterators — a shape that suits a functional
spec unusually well.

**(c) RDF-specific index layouts.** RDF-3X (Neumann & Weikum, 2008)
established the "RISC-style" design: exhaustive permutation indexes
over a dictionary-encoded triple table, with merge joins over sorted
runs. The cost is six index orders.

**(d) The Ring: WCOJ over triples in almost no extra space.**
Arroyuelo, Gómez-Brandón, Hogan, Navarro, Reutter, Rojas-Ledesma and
Soto (ACM TODS, 2024). Each triple is treated as a **cyclic string of
length 3**; rotations are sorted and columns stored as **wavelet
trees**, so stable re-sorting moves between columns without pointers.
The headline: where B-trees or tries need **six** index orders to
support all WCOJ variable orders, **one ring indexes them all**.

**(e) Cardinality estimation for RDF specifically.** Neumann &
Moerkotte, **characteristic sets** (ICDE 2011): group triples by the
property set of their subject, which recovers the implicit schema and
estimates multi-join RDF queries far better than generic DBMS
estimators. RDF's many self-joins are exactly where generic estimators
fail.

**(f) Prior art on verified query processing.** Q\*cert (Auerbach,
Hirzel, Mandel, Shinnar, Siméon) is a Coq platform for implementing
and verifying query compilers; DBCert is described as the first
mechanically verified compiler from canonical SQL to imperative code,
via the Nested Relational Algebra. Both are compiler-correctness
efforts over relational sources.

## 3. What this means for Factoidal

1. **The ceiling on our current design is asymptotic, not
   constant-factor.** Tuning the hash join cannot reach WCOJ on cyclic
   patterns; that needs a different algorithm. Any "make it v v fast"
   programme that stops at better binary joins stops below the known
   optimum.
2. **The Ring is an unusually good fit for a VERIFIED engine**, beyond
   its space win. Six B-tree orders mean six structures, six
   maintenance paths and six invariants to state; one ring is a single
   mathematical object (rotations + stable sort + rank/select) whose
   spec is small enough to write cleanly and whose invariants are
   about strings, which is territory both trees already handle.
3. **Optimality here is PROVABLE, not merely measurable.** The AGM
   bound is a theorem about output size; WCOJ running time is stated
   against it. So the performance claim can live in the same currency
   as the compliance claims — a machine-checked runtime bound rather
   than a benchmark chart. ⚠️ I have not found prior work
   machine-checking a WCOJ bound tied to a running engine; the
   verified-DB literature above is compiler correctness, not
   complexity. If that gap is real it is the distinctive contribution
   available to this project, and it needs a proper survey before
   anyone claims novelty in public.
4. **Characteristic sets are the cheap win** and are orthogonal to the
   join algorithm: a better estimator improves the existing planner
   immediately, with a small spec (a grouping and a counting argument).

## 4. Proposed programme (sequencing, not a schedule)

Each step names what ships AND what gets proved. Nothing starts
without owner go on https://github.com/danbri/factoidal/issues/484.

- **Step 0 — measure the real shape.** Benchmark cyclic (triangle,
  square) vs acyclic patterns on both trees. Cost of the current
  binary plans on cyclic queries is currently ASSUMED, not measured
  here. Per skills/measuring-inference: measure before optimising.
- **Step 1 — spec the index seam.** One F\*/Lean interface: an ordered
  triple iterator with `seek`/`next` (the leapfrog primitive), stated
  against the existing plain evaluator. Proof: the iterator enumerates
  exactly the matching triples, in order, no duplicates.
- **Step 2 — leapfrog triejoin against that seam.** Proof, in
  increasing strength: (a) result-set equality with the plain
  nested-loop evaluator — the refinement theorem that makes the
  optimisation safe; (b) the WCOJ bound itself, which is the research
  contribution and should be scoped separately.
- **Step 3 — characteristic-set estimation** feeding the existing
  planner. Proof: the estimate is exact on the characteristic-set
  abstraction, plus measured accuracy on real vocabularies.
- **Step 4 — Ring/wavelet-tree layout** as the compact index, once the
  iterator seam is proved and the join sits above it. This is the
  largest piece and is deliberately last: the seam makes it a
  substitution, not a rewrite.

Both trees can take Step 1–2; whether Lean gets them is
https://github.com/danbri/factoidal/issues/484, and the founding view
says the answer is not "no, it is the spec tree".

## Sources

- Leapfrog Triejoin (Veldhuizen, ICDT 2014): https://www.openproceedings.org/2014/conf/icdt/Veldhuizen14.pdf and https://arxiv.org/abs/1210.0481
- Worst-Case Optimal Join Algorithms (Ngo, Ré, Rudra, survey): https://dl.acm.org/doi/pdf/10.1145/3180143 and https://arxiv.org/pdf/1803.09930
- The Ring (Arroyuelo et al., ACM TODS 2024): https://dl.acm.org/doi/10.1145/3644824 and https://aidanhogan.com/docs/ring-graph-wco.pdf
- Characteristic sets (Neumann & Moerkotte, ICDE 2011): https://www.csd.uoc.gr/~hy561/papers/storageaccess/optimization/Characteristic%20Sets.pdf
- Q\*cert: https://querycert.github.io/
- DBCert / canonical SQL to imperative code in Coq: https://arxiv.org/abs/2203.08941
