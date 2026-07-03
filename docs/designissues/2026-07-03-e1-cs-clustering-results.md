# E1 results — characteristic-set row clustering for COTTAS (prototype measurement)

**Date:** 2026-07-03.
**Status:** experiment report. Prototype + measurements for experiment
E1 of
[`2026-07-03-shapes-canon-storage-strategies.md`](2026-07-03-shapes-canon-storage-strategies.md)
§5. No production pipeline changes; nothing here is wired into
[`tools/corpus_pipeline.py`](../../tools/corpus_pipeline.py) yet.
The UK Parliament corpus is absent from this clone, so this run uses a
synthetic shape-varied corpus; §7 says what the parliament re-run
must measure.

## 1. Method

- **Clustering tool:**
  [`tools/cs_cluster_nq.py`](../../tools/cs_cluster_nq.py) (new,
  Python stdlib only). Reads N-Quads from stdin or a file, computes
  each subject's characteristic set CS(s) — the set of predicates the
  subject has anywhere in the input — hashes the sorted predicate set
  to a 64-bit key (SHA-256 truncated to 16 hex chars), and emits the
  same quads sorted by `(CS(s), s, p, o, g)`. `--stats` prints
  distinct-CS count, a subjects-per-CS min/median/max summary, and
  input/output quad counts. The transform is a pure permutation
  (input and output quad counts are checked equal; re-clustering its
  own output is byte-identical, i.e. idempotent).
- **Writer:** `pycottas.rdf2cottas` cannot preserve a producer-chosen
  row order — it sets DuckDB `preserve_insertion_order = false` and
  always applies `ORDER BY <index permutation>` (pycottas 1.1.0,
  `__init__.py:23-87` in the venv at `_tmp.junk/pycottas-venv`).
  Since E1's experimental variable *is* the row order, both artifacts
  were written by a scratchpad script that mirrors rdf2cottas exactly
  (pyoxigraph term rendering incl. the `DEFAULT` sentinel; DuckDB
  `COPY ... (FORMAT PARQUET, COMPRESSION ZSTD, COMPRESSION_LEVEL 22,
  PARQUET_VERSION v2, KV_METADATA {index: ...})`; default 122,880-row
  row groups) with two deviations:
  1. `ORDER BY seq` (input order) instead of the index permutation,
     so row order is exactly the .nq line order; and
  2. `DICTIONARY_SIZE_LIMIT 1`, which forces
     `DELTA_LENGTH_BYTE_ARRAY` on all four columns — the encoding
     [`docs/cottas-format-v1.md`](../cottas-format-v1.md) §3 says
     producers SHOULD use, and the shape of the last-tested pycottas
     compatibility line ("DLBA across all 4"). This was forced
     because of a reader bug found en route (§6.1).
- **Artifacts compared** (identical quad multiset, identical writer,
  row order is the only variable):
  - `baseline` — input order (generation order, subjects interleaved
    across shapes);
  - `clustered` — output of `cs_cluster_nq.py`;
  - `spog` — `ORDER BY s, p, o, g`, i.e. the order today's pipeline
    (`rdf2cottas(index="spog")`) produces, included as the
    production-relevant reference point.
- **Binary:** committed `bin/linux-x86_64/factoidal`
  (`query --data-cottas FILE --query Q.rq`). Every command ran under
  `timeout 600`; all completed far below the cap.

## 2. Corpus

195,305 quads total = 195,300 synthetic + the 5-quad
[`tests/local/data/cottas_sample.nq`](../../tests/local/data/cottas_sample.nq)
appended. The synthetic part has 62,000 subjects in 4 shapes, emitted
round-robin so input order interleaves shapes:

| shape (¼ of subjects each) | predicates | optional extra |
|---|---|---|
| person | name, knows, age | email (30% of persons) |
| document | title, author, date | license (20% of documents) |
| measurement | value, unit, timestamp | — |
| event | label, location, date (shared with document) | — |

Graphs: 139,501 quads in the default graph, 18,600 in each of 3
synthetic named graphs, 4 in the sample file's 2 named graphs.
17 distinct predicate tokens overall.

CS statistics from `cs_cluster_nq.py --stats`: 10 distinct
characteristic sets over 62,004 subjects; subjects per CS min 1,
median 4,650, max 15,500. Input quads 195,305, output quads 195,305
(equal, as required).

## 3. File sizes

Same 21,643,744-byte N-Quads input in all three cases.

| artifact | bytes | vs baseline | vs spog |
|---|---:|---:|---:|
| `baseline` (input order) | 639,300 | — | +59.8% |
| `spog` (today's pipeline order) | 399,964 | −37.4% | — |
| `clustered` (CS order, this experiment) | **386,664** | **−39.5%** | **−3.3%** |

Reading: most of the compression win over raw arrival order comes
from *any* subject-grouping sort (SPOG already delivers −37.4%); CS
clustering adds 3.3% on top of SPOG here. The margin over SPOG is
small on this corpus for an identifiable reason: the synthetic
subject IRIs encode their shape in the IRI prefix
(`/person/`, `/document/`, …), so plain subject order already
co-locates shapes almost perfectly. Corpora whose subject IRIs do
not correlate with structure should show a larger clustered-vs-spog
gap; corpora like parliament (typed IRI paths) sit in between. This
is the main external-validity caveat.

## 4. Row-group locality (prune-selectivity proxy)

Row groups are 122,880 rows, so this 195,305-row corpus has 2 per
file (row group 1 has 72,425 rows). Distinct values per row group,
measured with DuckDB `read_parquet(..., file_row_number=true)`:

| artifact | distinct p (rg0, rg1) | distinct (p,o) pairs (rg0, rg1) | rows with p=`vocab:unit` (rg0, rg1) |
|---|---|---|---|
| baseline | 13, 17 | 56,339, 34,722 | 9,752, 5,748 |
| spog | 9, 11 | 43,567, 43,856 | 8,927, 6,573 |
| clustered | 12, 9 | 53,196, 34,197 | **15,500, 0** |

The bound-predicate row is the E1 mechanism in miniature: the
`vocab:unit` predicate (measurement shape only) spans both row groups
under baseline and spog order but is confined to row group 0 under CS
order, so a Yod6-style presence bitmap would kill 1 of 2 row groups
(50%) for that predicate — versus 0 of 2 for the other orders. With
2 row groups the effect is necessarily coarse; at parliament scale
(26 row groups) a single-CS predicate would be confined to the few
row groups its CS partition occupies.

Caveat: no presence-bitmap/compound sidecars were built for these
artifacts, and the committed binary's timings below therefore do
**not** include prune wins — the table above is a structural proxy
only. End-to-end prune measurement needs the parliament pipeline
(§7).

## 5. Query wall-times

`bin/linux-x86_64/factoidal query --data-cottas FILE --query Q.rq`,
3 runs per cell, wall-clock seconds, single otherwise-idle container.
Values are median (min–max) of the 3 runs.

Queries:

- (a) predicate-bound:
  `SELECT ?s ?o WHERE { ?s <http://example.org/vocab/unit> ?o } LIMIT 100`
- (b) subject-bound:
  `SELECT ?p ?o WHERE { <http://example.org/person/40000> ?p ?o }`
- (c) count by graph:
  `SELECT ?g (COUNT(*) AS ?n) WHERE { GRAPH ?g { ?s ?p ?o } } GROUP BY ?g`

| query | baseline | spog | clustered | clustered vs baseline | clustered vs spog |
|---|---|---|---|---:|---:|
| (a) predicate-bound | 9.729 (9.708–9.900) | 9.169 (9.131–9.480) | 8.934 (8.844–9.008) | −8.2% | −2.6% |
| (b) subject-bound | 11.948 (11.901–11.971) | 11.493 (11.427–11.503) | 11.119 (11.086–11.155) | −6.9% | −3.3% |
| (c) count by graph | 1.122 (1.115–1.135) | 1.142 (1.127–1.145) | 1.032 (1.027–1.048) | −8.0% | −9.6% |

The deltas track file size almost exactly, which is the expected
mechanism here: with no sidecars in play, the reader decodes full
column chunks, so smaller ZSTD payloads decode faster. The absolute
9–12 s level for (a)/(b) is the on-disk path's full-scan cost at
195k rows and is unrelated to row order.

## 6. Correctness

All three artifacts pass `pycottas.verify`. Result counts are
identical across the three artifacts for all three queries: query (a)
returns 100 rows on all three (LIMIT-capped), query (b) returns 4
rows on all three, query (c) returns 5 rows on all three, and the
query-(c) result rows match row-for-row after sorting. In-memory
ground truth (`factoidal query --data base.nq`) agrees for (a)
(100 rows) and (b) (4 rows, same bindings).

Two pre-existing reader bugs surfaced; both are row-order-independent
and reproduce identically on all three artifacts:

### 6.1 RLE_DICTIONARY pages in row groups after the first fail to decode

With duckdb 1.5.4 (the version in `_tmp.junk/pycottas-venv`), default
Parquet writes pick `RLE_DICTIONARY` for low-cardinality columns
(`p`, `g`). The committed `bin/linux-x86_64/factoidal` then fails
with `Failure("COTTAS on-disk: could not decode column 3")` — on
files produced by plain `pycottas.rdf2cottas` too, not just this
experiment's writer. Bisection: files of 122,880 and 122,881 rows
decode (at 122,881 the second row group's g-chunk is a 1-value PLAIN
chunk with no dictionary page); files of 130,000+ rows fail (the
second row group carries its own dictionary page). Row group 0's
dictionary decodes fine, so the defect is specific to dictionary
pages in row groups ≥ 1.
[`docs/cottas-format-v1.md`](../cottas-format-v1.md) §3 says v1
readers MUST support RLE_DICTIONARY on any column, so this is a
conformance bug, and it means the current pipeline + committed binary
combination breaks for any corpus chunk over 122,880 rows once the
venv's DuckDB chooses dictionary encoding. Workaround used here (and
available to the pipeline): write with `DICTIONARY_SIZE_LIMIT 1` to
force all-DLBA, which is also the spec's SHOULD encoding. Needs a
GitHub issue + a fix in the F\* RLE_DICTIONARY decoder path.

### 6.2 On-disk `GROUP BY ?g` returns wrong counts

Query (c) returns `?n = 195304` for every one of the 5 graphs on the
on-disk path (all three artifacts identically), while the in-memory
path on the same data returns the correct 18,600 / 18,600 / 18,600 /
3 / 1 — which matches a direct scan of the .nq. The on-disk path gets
the ungrouped variants right: `COUNT(*)` over `GRAPH ?g { ?s ?p ?o }`
returns the correct 55,804, and `COUNT(*)` with a bound graph IRI
returns the correct 18,600. So grouping by the graph variable is
what's broken in the on-disk evaluator, not GRAPH matching or
counting. Row-order-independent (identical wrong numbers on all
three artifacts), so it does not affect E1's comparison — but it
needs its own issue; the cross-artifact equality check in this
experiment would have masked it without the in-memory ground-truth
run.

## 7. Verdict and parliament follow-up

**Verdict: qualified yes — worth wiring into the corpus pipeline as
an option, with the decision to make it the default deferred to the
parliament measurement.** The experiment confirms the E1 mechanism
end-to-end at zero reader cost: CS clustering is a pure producer-side
permutation (correctness checks pass unchanged), it compresses better
than both arrival order (−39.5%) and today's SPOG order (−3.3%), it
speeds up the committed binary's queries by 7–8% versus arrival order
purely through decode volume, and it demonstrably confines a
shape-specific predicate to a subset of row groups where SPOG order
does not — which is the property the Yod6/Tet3/compound-(p,o) prune
cascade needs to become selective. What this run cannot show is the
prune-cascade payoff itself (no sidecars here, and only 2 row groups)
or the clustered-vs-spog margin on a corpus whose subject IRIs don't
already encode shape — on this synthetic corpus SPOG order captures
most of the compression win, so the case for CS clustering rests on
the prune/locality effects, not the extra 3.3% of size.

The parliament re-run (corpus absent from this clone) should measure,
per E1's plan: (1) `.cottas` + sidecar sizes for spog-order vs
CS-order builds; (2) row groups pruned vs scanned per query from the
existing prune counters, with the Yod6/Tet3/compound sidecars rebuilt
for the CS-order file — this is the number that decides the default;
(3) per-query wall time via
[`tools/bench_ukpar_queries.py`](../../tools/bench_ukpar_queries.py) /
[`tools/bench_ukpar_modern.py`](../../tools/bench_ukpar_modern.py),
medians with min/max, 3+ runs; (4) distinct (p,o) pairs per row group
before/after (compound-bitmap payload proxy — expect the ~60–100k
per-rg pair count to drop); (5) parliament CS statistics (distinct CS
count, subjects-per-CS histogram, and whether a merge cap is needed —
232 predicates suggests low CS explosion risk); (6)
[`tests/local/cottas_corpus_regressions.sh`](../../tests/local/cottas_corpus_regressions.sh)
and
[`tests/local/backend_parity_regressions.sh`](../../tests/local/backend_parity_regressions.sh)
unchanged; (7) one heterogeneous corpus (e.g. a DBpedia slice) before
believing the numbers generalise. Wiring plan: add a
`--row-order {spog,cs}` option to `materialize_nq_cottas_corpus` that
pipes the normalised .nq through `cs_cluster_nq.py` and writes via a
direct DuckDB COPY preserving that order (rdf2cottas cannot; §1),
with `DICTIONARY_SIZE_LIMIT 1` until §6.1 is fixed. Prerequisites to
file as issues first: the §6.1 RLE_DICTIONARY decoder bug (blocks
any >122,880-row rebuild with current DuckDB defaults) and the §6.2
GROUP-BY-graph bug (blocks trusting on-disk aggregate results).

## Appendix: raw timing runs

Wall-clock seconds per run (3 runs each, `timeout 600`, all rc=0):

| artifact | query | run 1 | run 2 | run 3 |
|---|---|---:|---:|---:|
| baseline | (a) predicate-bound | 9.729 | 9.900 | 9.708 |
| baseline | (b) subject-bound | 11.971 | 11.948 | 11.901 |
| baseline | (c) count by graph | 1.135 | 1.122 | 1.115 |
| clustered | (a) predicate-bound | 9.008 | 8.844 | 8.934 |
| clustered | (b) subject-bound | 11.119 | 11.086 | 11.155 |
| clustered | (c) count by graph | 1.032 | 1.027 | 1.048 |
| spog | (a) predicate-bound | 9.169 | 9.131 | 9.480 |
| spog | (b) subject-bound | 11.427 | 11.493 | 11.503 |
| spog | (c) count by graph | 1.145 | 1.127 | 1.142 |
