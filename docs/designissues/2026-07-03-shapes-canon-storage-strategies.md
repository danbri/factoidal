# Shapes + canonicalization as storage and scaling strategies — research notes

**Date:** 2026-07-03.
**Status:** design research only. No code changes, no format changes,
no commitments. The recommendations in §5 are ranked experiments.
**Research question (project owner):** "RDFC (canonicalization) + the
notion of shapes could help us design modern high-performance storage
and scaling strategies."

Source-marking convention: claims labelled **[web]** were checked
against the cited source during this session; claims labelled
**[memory]** are from the author-model's training knowledge (the
GitHub-hosted sources were partly unreachable through the proxy) and
should be re-verified before anything load-bearing is built on them.
Claims about this repo cite files directly.

## 0. Where the tree is (grounding)

- **On-disk format.** COTTAS-on-Parquet v1
  ([`docs/cottas-format-v1.md`](../cottas-format-v1.md)): four string
  columns `s,p,o,g` holding N-Quads tokens, ZSTD, DLBA or
  RLE_DICTIONARY encodings, 122,880-row row groups, row order
  producer-chosen (`index=spog` KV key is advisory only, §3 of that
  doc). Files are written by pycottas; factoidal has no F\*-side
  writer yet.
- **Prune/sidecar layer.** Per-column presence bitmaps (Yod6
  predicate prune, Tet3 subject/object prune), per-(p,o) compound
  presence
  ([`2026-04-26-nun4-compound-po-bitmap-design.md`](2026-04-26-nun4-compound-po-bitmap-design.md)),
  per-rg predicate offsets (Lamed3), per-graph predicate Bloom
  sidecars ([`graph-bloom-sidecars.md`](graph-bloom-sidecars.md)) with
  an F\* Bloom core
  ([`ballyhoo-bloom-fstar.md`](ballyhoo-bloom-fstar.md)). All of these
  prune at row-group or graph granularity; none change what is stored
  or in what order.
- **Constraint from #118.** The query path must be F\*; OCaml glue is
  shrinking, not growing
  ([`2026-05-13-issue-118-cottas-ondisk-runtime-retirement-plan.md`](2026-05-13-issue-118-cottas-ondisk-runtime-retirement-plan.md),
  [`2026-07-03-issue-118-first-slice-plan.md`](2026-07-03-issue-118-first-slice-plan.md)).
  Any new companion-file byte layout must be specified in F\* per rule
  #11 and the hash-witness pattern in
  [`2026-05-07-io-verification-and-third-party.md`](2026-05-07-io-verification-and-third-party.md);
  large-buffer serialisation follows the Option-B shape agreed in
  [`2026-05-09-large-writer-byte-format-options.md`](2026-05-09-large-writer-byte-format-options.md).
- **Canonicalization.** RDFC-1.0 exists in F\*
  ([`RDF.Canonical.fst`](../../formal/fstar/RDF.Canonical.fst), 1142
  lines): HFDQ phase + canonical N-Quads rendering are implemented;
  HNDQ (the recursive tie-breaking phase) is not. Suite score: 62
  pass, 23 fail, 1 skip (out of 86 rdf-canon tests) per
  [`docs/claude-rules/current-state.md`](../claude-rules/current-state.md)
  §6. The CLI does not expose it yet (standing priority #6).
- **Shapes.** [`SHACL.Validation.fst`](../../formal/fstar/SHACL.Validation.fst)
  is a Phase-1 AST skeleton (340 lines, validator stubbed, #181). The
  W3C SHACL suite is vendored but unwired.
- **Scale today.** In-memory: ~25k quads/s end-to-end and ~1.2 KB RAM
  per quad, linear
  ([`docs/claude-rules/performance.md`](../claude-rules/performance.md):30-36).
  On-disk: COTTAS serves the 3,143,406-quad ukparliament corpus. The
  goal is corpora one to two orders of magnitude beyond that without
  giving up the verified query path.

The common thread of this note: the sidecars built so far treat row
groups as arbitrary slices and recover selectivity after the fact
with bitmaps. Both "shapes" (declared or discovered structure) and
"canonical form" (deterministic identity) are levers on **what gets
stored where and under what name**, which is where the larger wins in
the literature come from.

## 1. Characteristic sets: discovered shapes as the physical schema

### 1.1 The idea

A subject's *characteristic set* (CS) is the exact set of predicates
it has. Neumann and Moerkotte, "Characteristic Sets: Accurate
Cardinality Estimation for RDF Queries with Multiple Joins" (ICDE
2011) observed that real RDF corpora have few distinct CSs relative
to subjects, and that storing `(CS, count, per-predicate occurrence
counts)` gives near-exact cardinality estimates for star joins —
the query shape SPARQL BGPs are dominated by. **[web:
[paper PDF](https://www.csd.uoc.gr/~hy561/papers/storageaccess/optimization/Characteristic%20Sets.pdf)]**

Follow-on work turned CSs from an estimation device into a physical
design device:

- Meimaris, Papastefanatos, Mamoulis, Anagnostopoulos, "Extended
  Characteristic Sets: Graph Indexing for SPARQL Query Optimization"
  (ICDE 2017) — *extended* CSs (ECS) additionally type the
  object-subject links between CSs, and axonDB stores and indexes
  triples grouped by CS/ECS, so a star query resolves to "scan these
  few CS partitions" and a path query to "scan these ECS link
  partitions". **[web:
  [survey confirmation](https://arxiv.org/pdf/2102.13027)]**
- Meimaris and Papastefanatos, "Hierarchical Characteristic Set
  Merging for Optimizing SPARQL Queries in Heterogeneous RDF" (arXiv
  1809.02345, 2018) — heterogeneous corpora can have CS explosion
  (tens of thousands of near-duplicate CSs); merging CSs along their
  subset lattice bounds partition count while keeping estimates
  tight. **[web: [arXiv](https://arxiv.org/abs/1809.02345)]**
- Bornea et al., "Building an Efficient RDF Store Over a Relational
  Database" (SIGMOD 2013, the DB2 RDF store) used entity-oriented
  rows (subject + hashed predicate columns) — CS-like clustering
  inside a relational engine. **[memory]**

### 1.2 SHACL shapes ≈ declared characteristic sets

A SHACL node shape with `sh:property` constraints (minCount ≥ 1)
declares a predicate set every conforming focus node must have —
i.e. a lower bound on the CS of every instance. The two notions
compose in both directions:

- **Discovered → declared:** mining CSs from a corpus is a cheap
  one-pass job and yields candidate shapes (this is how several shape
  induction tools work, e.g. SheXer-style approaches **[memory]**).
- **Declared → physical:** where shapes exist, they are a
  *partitioning oracle* that is stable under data growth — new
  conforming instances land in an existing partition, whereas raw CS
  partitioning can fragment when instances have optional extras.
  The hierarchical-merge result above says the practical answer is
  "declared shape = merge target; exact CS = refinement within it".

For factoidal the attraction is that
[`SHACL.Validation.fst`](../../formal/fstar/SHACL.Validation.fst)'s
AST already carries exactly the vocabulary needed (`minCount`,
`class`, `datatype`, paths); a `shape → predicate-set lower bound`
function is a small `Tot` function over that AST, and "row belongs to
shape partition" is checkable in F\*.

### 1.3 What CS clustering does to COTTAS

COTTAS v1 row order is producer-chosen and semantically free
([`docs/cottas-format-v1.md`](../cottas-format-v1.md) §3). Today
pycottas emits SPOG order, so a 122,880-row row group at
parliament scale contains a lexicographic slice of subjects — which
mixes many CSs, so almost every row group contains almost every
frequent predicate. Consequences, visible in the existing design
docs:

- Yod6's predicate-presence bitmap prunes only for *rare* predicates
  (frequent predicates are present in every rg).
- The compound (p,o) bitmap
  ([`2026-04-26-nun4-compound-po-bitmap-design.md`](2026-04-26-nun4-compound-po-bitmap-design.md))
  was needed precisely because per-column presence saturates:
  parliament has ~60–100k distinct (p,o) pairs *per row group*.

If rows are instead sorted by `(CS-id, s, p, o)` — group subjects by
their characteristic set, then SPO within the group — then:

- **Row groups become predicate-sparse.** A row group covering one CS
  contains only that CS's predicates (parliament has 232 predicate
  dict tokens total; typical CS sizes are single-digit to low tens
  **[memory, needs measurement]**). Yod6 goes from "passes almost
  everything" to "kills most row groups for any bound predicate".
  The same presence-bitmap *code* becomes far more selective with no
  reader change — the sidecars' effectiveness is a function of row
  order.
- **Sparse (p,o) pair lists shrink** per rg (fewer predicates ⇒ fewer
  distinct pairs), so the compound bitmap gets smaller and more
  selective simultaneously.
- **DLBA/dictionary compression improves.** Long runs of identical
  `p` values and clustered `o` datatypes compress better under both
  supported encodings; RLE_DICTIONARY on `p` becomes near-free.
- **Star joins localise.** `?s p1 ?a . ?s p2 ?b` touches only row
  groups of CSs containing {p1,p2} — the axonDB effect, obtained here
  purely by row placement plus the existing prune cascade.
- **Cardinality estimation upgrades.** A per-CS `(count, per-pred
  counts)` table is a few KB and gives Neumann–Moerkotte-quality
  star-join estimates; Mem5's estimate path currently extrapolates
  from presence bits, which cannot distinguish "1 row matches in rg"
  from "122,880 rows match".

Cost side: CS clustering is a *write-time* sort. COTTAS files are
currently write-once (produced by
[`tools/corpus_pipeline.py`](../../tools/corpus_pipeline.py)), so
update-cost concerns (§2.3) do not bite yet. The failure mode to
watch is CS explosion on heterogeneous corpora — mitigation is
lattice merging (Meimaris 2018) or shape-anchored merging (§1.2),
plus a residual "no dominant CS" partition.

## 2. Shape/type-partitioned storage: what history says

### 2.1 Property tables and vertical partitioning

- Wilkinson, "Jena Property Table Implementation" (SSWS 2006): rows =
  subjects, columns = properties, for *frequent patterns*; the rest
  stays in a triple table. Wins on star access, loses on schema drift
  and multi-valued properties. **[web:
  [Semantic Scholar entry](https://www.semanticscholar.org/paper/Jena-Property-Table-Implementation-Wilkinson/8762ac09383eebaae04bd64af885678cb58821fb)]**
- Abadi, Marcus, Madden, Hollenbach, "Scalable Semantic Web Data
  Management Using Vertical Partitioning" (VLDB 2007) and the
  follow-up SW-Store (VLDB Journal 2009): one two-column `(s,o)`
  table per predicate in a column store. Measured to match property
  tables while being simpler — the property-table benefit largely
  reduces to columnar layout + clustering. **[web:
  [paper](https://www.cs.umd.edu/~abadi/papers/abadirdf.pdf)]**
- Later systems folded both into general columnar/permuted-index
  designs (RDF-3X §4; Virtuoso's column store **[memory]**), and the
  "A Survey of RDF Stores & SPARQL Engines for Querying Knowledge
  Graphs" (Ali, Saleem, Yao, Hogan et al., VLDB Journal 2022)
  taxonomy treats CS-based layouts as the modern descendant of
  property tables. **[web: [arXiv](https://arxiv.org/pdf/2102.13027)]**

Reading for factoidal: COTTAS-on-Parquet is *already* the
vertically-partitioned columnar layout Abadi argued for — what it
lacks is the **clustering** dimension (which subjects share a row
group). That is exactly the cheap-to-change axis (§1.3), and it does
not require wide-table-per-shape schemas, which would break the fixed
four-column v1 contract and the F\* reader.

### 2.2 When shape partitioning wins

Consensus across the property-table/CS literature **[web+memory]**:

- Wins: star-shaped BGPs (most of SPARQL), scans restricted to one
  type/shape, compression, cardinality estimation.
- Neutral: single-pattern lookups with bound predicate (permutation
  indexes already handle these).
- Loses: queries with unbound predicates crossing all partitions;
  corpora where subjects are structurally unique (CS explosion);
  update-heavy workloads (a subject gaining a predicate *changes its
  CS* ⇒ row migration).

### 2.3 SHACL as oracle vs. discovered CSs

Use both, in this order: discovered exact CSs are the ground truth of
the corpus and cost one pass; declared SHACL shapes (when present)
name merge targets and make partition identity stable across corpus
versions. A shape that the data does not satisfy is detected by the
same machinery (a CS missing a required predicate) — i.e. the
partitioner and a future
[`SHACL.Validation.fst`](../../formal/fstar/SHACL.Validation.fst)
validator share their core scan. That shared scan is an argument for
implementing CS extraction in F\* even before the validator lands.

## 3. Canonicalization as a storage primitive

### 3.1 Canonical form ⇒ content-addressed identity

RDFC-1.0 (W3C Recommendation, "RDF Dataset Canonicalization",
<https://www.w3.org/TR/rdf-canon/>) yields a canonical N-Quads
serialisation that is invariant under blank-node relabelling; its
hash is therefore an identity for the *graph*, not the file. **[web]**
Prior art on using that as a storage primitive:

- Carroll, "Signing RDF Graphs" (ISWC 2003) — the original
  canonical-N-Triples-for-signatures construction. **[memory]**
- Kuhn and Dumontier, "Trusty URIs: Verifiable, Immutable, and
  Permanent Digital Artifacts for Linked Data" (ESWC 2014) — hash of
  canonicalised RDF content embedded in the IRI; nanopublications
  ecosystem runs on this at millions-of-graphs scale. **[web:
  [arXiv](https://arxiv.org/pdf/1401.5775)]**
- IPLD (IPFS's data model) — Merkle-DAG content addressing for
  arbitrary linked data; hash-linked blocks give dedup, integrity,
  and incremental sync for free. **[web:
  [ProtoSchool lesson](https://proto.school/merkle-dags/08/)]**
- Hogan, "Canonical Forms for Isomorphic and Equivalent RDF Graphs:
  Algorithms for Leaning and Labelling Blank Nodes" (ACM TWEB 2017) —
  the algorithmics behind canonical labelling, including the hard
  cases. **[web:
  [author PDF](https://aidanhogan.com/docs/rdf-canonicalisation.pdf)]**

What a per-graph canonical hash buys factoidal concretely:

1. **Dedup / idempotent ingest.** The corpus pipeline can skip
   re-converting and re-indexing a graph whose canonical hash is
   unchanged — cheap incremental corpus rebuilds. Today's pipeline
   has no change detection at all.
2. **Cache keys.** `(canonical dataset hash, canonical query text)`
   keys a sound query-result cache, including across blank-node
   relabelings that byte-level file hashes miss.
3. **Blank-node-stable diffs.** Diffing two canonical N-Quads files
   is line-set difference; this is the substrate the RDF versioning
   literature builds on — OSTRICH (Taelman, Vander Sande, Verborgh,
   "Triple Storage for Random-Access Versioned Querying of RDF
   Archives", JWS 2019) stores an HDT snapshot + aggregated
   changesets; COBRA (Taelman et al., SWJ 2022) makes the delta chain
   bidirectional; Quit Store (Arndt et al., JWS 2019) and R43ples
   (Graube et al. 2014) do git-style graph versioning.
   **[web for OSTRICH/COBRA:
   [journal article](https://rdfostrich.github.io/article-jws2018-ostrich/);
   memory for Quit/R43ples]** A canonical-hash sidecar is the
   zero-cost first rung of that ladder.
4. **Merkle roll-ups.** Per-graph hashes compose upward (hash of
   sorted child hashes) into corpus- and bundle-level identities —
   the same TOC/bundle structure the Bloom roll-ups already use
   ([`graph-bloom-sidecars.md`](graph-bloom-sidecars.md)) gains a
   verification/dedup key alongside its prune key. This also gives
   the io-verification hash-witness pattern
   ([`2026-05-07-io-verification-and-third-party.md`](2026-05-07-io-verification-and-third-party.md))
   a semantic (graph-level) counterpart to its byte-level witnesses.

### 3.2 Cost, and the shapes interplay

RDFC-1.0's worst case is exponential: canonical labelling embeds
graph-isomorphism-hard instances when blank nodes form large
automorphic structures (the HNDQ recursion). The spec and Hogan 2017
both note real-world data essentially never exhibits this, and
implementations ship work limits. **[web: W3C rdf-canon security
considerations; Hogan 2017]**

The interplay claim — and the reason "RDFC + shapes" is one research
question, not two: **shape-bounded blank-node structures make
canonicalization cheap.** If shapes constrain bnodes to trees or
bounded-degree, non-automorphic structures (RDF lists, typical
description bnodes — what SHACL property paths reach), then
first-degree hashes are already discriminating, HNDQ never recurses
deeply, and canonicalization is O(n log n) in practice. **[memory /
analytical — worth an empirical check on our suites]** Conversely, a
corpus that validates against known shapes can carry a *certified
canonicalization budget*: validate once, then canonicalize with a
hard work cap knowing the cap is unreachable. That is a claim an F\*
codebase is unusually well placed to make precise later (a lemma
relating a bnode-structure predicate to HFDQ-uniqueness), though
nothing in §5 depends on proving it.

Practical status note: [`RDF.Canonical.fst`](../../formal/fstar/RDF.Canonical.fst)
lacks HNDQ (23 of 86 suite failures), which is precisely the
symmetric-bnode branch. For shape-bounded data — including, likely,
all of ukparliament — HFDQ-only already yields correct canonical
hashes; the hash-sidecar experiment (§5, E3) does not need to wait
for HNDQ, but must record "HFDQ tie encountered" and decline to emit
a hash in that case rather than emit a wrong one.

## 4. Sort orders, dictionaries, and what one more permutation buys

Reference points:

- RDF-3X (Neumann and Weikum, "RDF-3X: a RISC-style Engine for RDF",
  PVLDB 2008; VLDB Journal 2010): all 6 SPO permutations + aggregate
  indexes, byte-level delta compression over sorted triples; every
  triple pattern becomes one range scan. **[web:
  [VLDB-J page](https://dl.acm.org/doi/10.1007/s00778-009-0165-y)]**
- HDT (Fernández, Martínez-Prieto, Gutiérrez, Polleres, Arias,
  "Binary RDF Representation for Publication and Exchange (HDT)", JWS
  2013): global term dictionary + bitmap-tree triples in one
  permutation; HDT-FoQ adds indexes for the other access patterns;
  HDTQ extends to quads. Factoidal already reads HDT
  ([`2026-04-19-hdt-fstar-status.md`](2026-04-19-hdt-fstar-status.md)).
  **[web: [rdfhdt.org internals](https://www.rdfhdt.org/hdt-internals/)]**
- Oxigraph stores quads under multiple key permutations (SPOG-family
  orderings) in RocksDB, following the RDF-3X recipe on an LSM tree.
  **[memory — github.com unreachable through proxy this session]**

COTTAS v1 sits at "one permutation, string cells, per-file". The
realistic upgrades, in increasing invasiveness:

1. **Better row order within the existing format** (free): §1.3. Any
   producer-side sort is v1-conformant. This includes CS clustering
   or plain POS ordering for a predicate-scan-heavy workload — but CS
   clustering subsumes most of POS's benefit for star queries while
   keeping subject locality.
2. **A second permutation file** (moderate): a sibling `data.posg.cottas`
   would give bound-`p`/bound-`o` patterns a scan instead of a prune
   cascade. v1 anticipated per-permutation files (§10 "Index columns
   and secondary indexes"). Cost: 2× storage, writer changes, and
   planner logic in F\* to pick a permutation — a real but
   well-trodden design (RDF-3X). Given that presence bitmaps + Lamed3
   offsets already approximate this, measure §5-E1 first; a second
   permutation is the fallback if prune rates stay poor.
3. **A dictionary-ID layer** (larger): replace repeated string cells
   with u32 IDs + a `.dict` companion — the direction
   [`RDF.CottasStore.OnDiskIndex.fst`](../../formal/fstar/RDF.CottasStore.OnDiskIndex.fst)
   already establishes (`dict_encode_token`/`dict_decode_token` are
   byte-specified in F\*). This is the HDT/RDF-3X move that cuts both
   size and decode cost, and it aligns with the #118 second slice
   ("realising the four `mmap_companion_*` primitives against the
   `.dict` companions",
   [`2026-07-03-issue-118-first-slice-plan.md`](2026-07-03-issue-118-first-slice-plan.md)
   closing section). It amounts to a COTTAS v2 and should be its own
   design doc; CS clustering makes it *more* effective (ID runs get
   longer) so the ordering experiment is not wasted work if v2
   happens.

Rule-#11 note for all three: sort order is producer-side and
semantics-free (reader must not rely on order per v1 §3), so
experiment 1 needs no F\* changes at all; options 2–3 put byte layout
in F\* with hash-witness CI per the Option-B pattern in
[`2026-05-09-large-writer-byte-format-options.md`](2026-05-09-large-writer-byte-format-options.md).

## 5. Recommended experiments (ranked by expected win / cost)

These are experiments with measurement plans, not commitments. All
three are independent; E1 and E3 can run in parallel sessions.

### E1 — Characteristic-set row clustering (no format change, no F\* change)

**Hypothesis:** re-ordering COTTAS rows by `(CS(s), s, p, o)` before
the pycottas write raises the existing Yod6/Tet3/compound-(p,o)
prune cascade's kill rate on bound-predicate patterns from
near-zero (frequent predicates appear in every rg today) to
most-rgs-killed, and improves ZSTD/DLBA
compression, at zero reader cost.

**Build:** a corpus-pipeline variant (producer-side Python is
in-policy per [`docs/cottas-format-v1.md`](../cottas-format-v1.md)
§1) that (a) computes each subject's CS in one pass, (b) merges CSs
above a partition-count cap along the subset lattice, (c) emits the
re-sorted N-Quads into `pycottas.rdf2cottas`, then rebuilds the
companion sidecars.

**Measure:** on the ukparliament corpus, before vs. after —
(1) per-query wall time via
[`tools/bench_ukpar_queries.py`](../../tools/bench_ukpar_queries.py) /
[`tools/bench_ukpar_modern.py`](../../tools/bench_ukpar_modern.py);
(2) row groups pruned vs. scanned per query (the prune counters the
cascade already logs); (3) `.cottas` + sidecar file sizes; (4)
distinct (p,o) pairs per rg (compound-bitmap payload size as proxy);
(5) correctness witness:
[`tests/local/cottas_corpus_regressions.sh`](../../tests/local/cottas_corpus_regressions.sh)
and
[`tests/local/backend_parity_regressions.sh`](../../tests/local/backend_parity_regressions.sh)
must be unchanged, since row order is semantically free. Also record
CS statistics (distinct CSs, size distribution) — input for E2 and
for the SHACL work.

**Cost:** small (one Python producer variant + one bench session).
**Risk:** CS explosion on heterogeneous corpora — bounded by the
merge cap; parliament data is schema-regular so the ceiling case is
likely favourable, which is also a threat to external validity (add
one heterogeneous corpus, e.g. a DBpedia slice, before believing the
numbers generalise).

### E2 — Per-CS statistics sidecar for cardinality estimation (F\*, one companion file)

**Hypothesis:** a `.cs` companion file holding `(CS-id → predicate
set, subject count, per-predicate triple counts, rg span)` gives
Neumann–Moerkotte star-join estimates that beat the current
presence-bit extrapolation in Mem5's estimate path, improving join
ordering on multi-pattern queries.

**Build:** F\* module `RDF.CottasStore.CharSetIndex.fst` mirroring
the PresenceBitmap pattern (header + payload byte layout specified in
F\*; writer under the Option-B hash-witness discipline; reader is the
only load-bearing path). Wire `cottas_ondisk_estimate` to consult it
when the pattern is a star on one subject variable. Depends on E1's
row order for the `rg span` field to be tight, but the estimate
quality claim is testable even on unsorted corpora.

**Measure:** (1) estimate error: predicted vs. true cardinality for
the bench query set (labelled per query); (2) end-to-end wall time on
multi-BGP ukparliament queries; (3) sidecar size; (4) suite scores
unchanged (`w3c_runner --all`: currently SPARQL 631 pass, 0 fail;
RDF 1031 pass, 0 fail — must stay).
**Cost:** medium (one F\* module + writer + one estimate-path
redirect; the Psi3/compound designs are the template).
**Risk:** the planner may not yet exploit better estimates — measure
estimate error separately from wall time so a null wall-time result
is still informative.

### E3 — Canonical-hash sidecar: RDFC as ingest/dedup/cache primitive (mostly consumer wiring)

**Hypothesis:** exposing the existing
[`RDF.Canonical.fst`](../../formal/fstar/RDF.Canonical.fst) as
`factoidal canonicalize` (standing priority #6) and writing a
`graph.c14n.sha256` sidecar per graph folder makes corpus rebuilds
incremental (skip unchanged graphs), gives sound query-cache keys,
and provides bnode-stable diffs — at a canonicalization cost that is
near-linear on shape-regular data.

**Build:** (a) CLI subcommand (consumer wiring in `bin/`, no new
F\*); (b) sidecar writer in the corpus pipeline next to the Bloom
sidecars, with Merkle roll-up per bundle mirroring
[`tools/graph_bloom_rollup.py`](../../tools/graph_bloom_rollup.py);
(c) skip-if-hash-unchanged logic in
[`tools/corpus_pipeline.py`](../../tools/corpus_pipeline.py). Emit
no hash (and say so) when HFDQ ties are detected, until HNDQ lands.

**Measure:** (1) canonicalization throughput (quads/s) on ukparliament
graphs and on
[`formal/fstar/bench-turtle-metrics.sh`](../../formal/fstar/bench-turtle-metrics.sh)-sized
synthetic files — this doubles as the empirical check of the
"shape-bounded bnodes ⇒ cheap canonicalization" claim in §3.2, by
recording HFDQ-tie frequency per corpus; (2) pipeline wall time for a
1-graph-changed rebuild, before vs. after; (3) rdf-canon suite must
not regress (62 pass, 23 fail, 1 skip of 86 is the baseline).
**Cost:** small-to-medium, and most of it is already a standing
priority; the experiment adds only the sidecar + skip logic.
**Risk:** HFDQ-only coverage — mitigated by the decline-to-hash rule;
per-graph canonicalization cost on very large single graphs (measure
before relying on it in the pipeline's hot path).

### Deferred (flagged, not recommended now)

- **Second permutation file** (§4 option 2) — decide after E1's prune
  numbers.
- **Dictionary-ID COTTAS v2** (§4 option 3) — its own design doc;
  sequence behind the #118 second slice, and behind E1 (clustering
  changes the payoff calculus in v2's favour).
- **Shape-partitioned wide tables** — rejected for now: breaks the
  four-column v1 contract and the F\* reader for a benefit E1 largely
  captures (§2.1).

## 6. Web sources consulted

- Neumann, Moerkotte 2011, Characteristic Sets (ICDE):
  <https://www.csd.uoc.gr/~hy561/papers/storageaccess/optimization/Characteristic%20Sets.pdf>
- Meimaris, Papastefanatos 2018, Hierarchical CS Merging:
  <https://arxiv.org/abs/1809.02345>
- Ali, Saleem, Yao, Hogan et al. 2022, RDF stores survey (VLDB-J):
  <https://arxiv.org/pdf/2102.13027>
- Wilkinson 2006, Jena Property Table Implementation:
  <https://www.semanticscholar.org/paper/Jena-Property-Table-Implementation-Wilkinson/8762ac09383eebaae04bd64af885678cb58821fb>
- Abadi et al. 2007, Vertical Partitioning (VLDB):
  <https://www.cs.umd.edu/~abadi/papers/abadirdf.pdf>
- Abadi et al. 2009, SW-Store (VLDB-J):
  <https://link.springer.com/article/10.1007/s00778-008-0125-y>
- Neumann, Weikum 2010, RDF-3X (VLDB-J):
  <https://dl.acm.org/doi/10.1007/s00778-009-0165-y>
- Fernández et al. 2013, HDT; internals page:
  <https://www.rdfhdt.org/hdt-internals/>
- Hogan 2017, Canonical Forms for Isomorphic and Equivalent RDF
  Graphs (ACM TWEB):
  <https://aidanhogan.com/docs/rdf-canonicalisation.pdf>
- W3C RDF Dataset Canonicalization (RDFC-1.0):
  <https://www.w3.org/TR/rdf-canon/>
- Taelman et al. 2019, OSTRICH (JWS):
  <https://rdfostrich.github.io/article-jws2018-ostrich/>
- Taelman et al. 2022, COBRA bidirectional delta chains (SWJ):
  <https://content.iospress.com/articles/semantic-web/sw210449>
- Kuhn, Dumontier 2014, Trusty URIs (ESWC):
  <https://arxiv.org/pdf/1401.5775>
- IPLD Merkle-DAG tutorial: <https://proto.school/merkle-dags/08/>

From-memory citations needing verification when GitHub/ACM access is
available: Carroll 2003 "Signing RDF Graphs" (ISWC); Bornea et al.
2013 DB2-RDF (SIGMOD); Arndt et al. 2019 Quit Store (JWS); Graube et
al. 2014 R43ples; Oxigraph storage permutations; Meimaris et al. 2017
ECS/axonDB (ICDE — the 2018 arXiv follow-up above is web-verified).
