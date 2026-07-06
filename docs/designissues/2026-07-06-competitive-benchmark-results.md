# Competitive benchmark: factoidal vs Apache Jena vs pyoxigraph vs rdflib

**Date:** 2026-07-06. **Author context:** measurement + harness-build
only; no `.fst`/OCaml changes. Harness: `tools/bench-competitive.sh`
(entry point) + `tools/bench_competitive.py` (orchestration) +
`tools/bench_competitive_driver_{pyoxigraph,rdflib}.py` (persistent-
process drivers) + `tools/bench_rusage_run.py` (peak-RSS wrapper,
`/usr/bin/time -v` is not installed in this sandbox). Raw JSON:
`docs/test-results/competitive-bench.json`. Table generator:
`tools/bench_competitive_report.py`.

**Why this doc exists.** The owner's goal is a "world class offering,"
which needs a measuring stick against engines other than ourselves.
`docs/designissues/2026-07-05-disk-backed-db-perf-review.md` measured
factoidal in isolation; this benchmark puts factoidal alongside at
least one established RDF store on the *same* data and the *same*
SPARQL text, cross-checks that the answers actually agree, and reports
wins and losses without sandbagging or cherry-picking (per
`skills/perf-benchmarking/SKILL.md` and anti-pattern #25 — every
number below is labelled with what it counts and out of what).

**Binary provenance (read before quoting any number).** `bin/linux-x86_64`
had uncommitted changes throughout this session (a sibling session was
actively rebuilding it — exactly the scenario the task brief warned
about). The harness detected this and refused to run against the dirty
working tree; every measurement instead used `git show
HEAD:bin/linux-x86_64/<binary>` into a scratch dir, per its
`--allow-dirty-bin` path. Because siblings kept landing commits during
this session, **the LOAD numbers (§3) and QUERY numbers (§4) were
measured against two different HEAD commits**, about 40 minutes apart:
LOAD against `232288a`, QUERY against `a3ef63c` (the QUERY phase was
rerun once after a harness bug fix — see the note at the end of §4).
Both are stated explicitly rather than presented as one snapshot.
`docs/test-results/competitive-bench.json`'s `engines.factoidal.provenance`
field carries the exact commit and scratch path for the run that
produced its contents (`a3ef63c`, the QUERY-phase run).

---

## 1. Engines: what installed, through the proxy

| Engine | Installed? | How | Version |
|---|---|---|---|
| Apache Jena (`arq`, `tdb2.tdbloader`, `tdb2.tdbquery`) | yes | binary distribution `org.apache.jena:apache-jena:5.2.0` fetched from Maven Central (`repo1.maven.org`, reachable through the agent proxy with the session's CA bundle) — **no build**, this is Jena's own published tarball, cached at `~/.cache/factoidal-bench/apache-jena-5.2.0` by `tools/bench-competitive.sh` so reruns don't re-download | Apache Jena 5.2.0 |
| pyoxigraph | yes | `pip install pyoxigraph` (pypi.org is in this sandbox's direct-allow list, no proxy needed) | 0.5.9 |
| rdflib | yes (already present) | pip | 7.6.0 |
| factoidal | n/a (subject under test) | `git show HEAD:bin/linux-x86_64/factoidal` (see provenance note above) | commit `232288a` (LOAD), `a3ef63c` (QUERY) |

Preference order from the task brief was Jena, then Oxigraph, then
rdflib as the floor. All three installed cleanly; this is **at least
one real store beyond rdflib** (Jena, plus pyoxigraph as a second) —
the task's minimum bar is cleared with room to spare. Nothing was
substituted or skipped for lack of proxy access.

A note on `/tmp/jena`: the repo's existing Jena ARQ probes
(`tools/jena_arq_*probe.sh`, see `skills/test-suites/SKILL.md`) expect
a **source checkout** of `jena-arq`'s test corpus at
`/tmp/jena/jena-arq/testing/DAWG-Final` — that tree has no built jars
and was not usable as a runnable store. This benchmark instead fetches
Jena's own published binary distribution, independent of that probe
setup.

## 2. Data: in-tree only, no fabricated corpora

| Corpus | Source | Triples | Bytes |
|---|---|---:|---:|
| `gene` | `examples/wikidata/subsets/lifesci-kgx/data/gene.ttl` (the exact file `2026-07-05-disk-backed-db-perf-review.md` measured) | 888,949 | 17,363,312 |
| `lifesci-all` | concatenation of all 21 `.ttl` files in that same directory (produced by the harness into a scratch dir at run time, not committed — concatenation is valid Turtle here because none of the files declare `@base` and prefix re-declaration mid-stream is legal Turtle) | 1,258,752 | 29,008,189 |

The query workload (§4) runs on `gene` only, the corpus the perf
review already characterised — so this benchmark's factoidal numbers
are directly cross-checkable against that doc's §2.c/§2.e. `lifesci-all`
is a second, larger LOAD-only scaling point (§3), not run through the
query matrix, to keep the harness's wall-clock bounded; this scoping
choice is stated here rather than left implicit.

## 3. LOAD: wall time + peak RSS to a queryable state

| Engine | Corpus | Wall (median of 3 runs) | Peak RSS (median) | Runs ok | Note |
|---|---|---:|---:|---:|---|
| factoidal-cli-fast-path | gene | 26.31 s | 744 MiB | 3/3 | fresh-process point-lookup query (materializing, non-fast-path-eligible) |
| factoidal-cli-forced-slow-path (kill switch) | gene | 25.17 s | 744 MiB | 3/3 | same, `FACTOIDAL_DISABLE_STREAM_FASTPATH=1` |
| jena-arq-inmemory | gene | 9.93 s | 1,492 MiB | 3/3 | arq reparses the file every invocation |
| jena-tdb2 (on-disk) | gene | 9.59 s | 2,005 MiB | 3/3 | fresh `tdb2.tdbloader` run into a fresh dir each time |
| pyoxigraph (in-memory) | gene | **2.33 s** | **315 MiB** | 3/3 | `Store().load()` |
| rdflib (in-memory, floor baseline) | gene | 24.38 s | 727 MiB | 3/3 | `Graph().parse()` |
| factoidal cottas-import (on-disk build) | gene | 129.08 s | 1,717 MiB | 1/1 | `corpus_pipeline.py materialize-nq-cottas-corpus --build-sidecars`; single run (~2 min cost, not median-of-3 — disclosed) |
| factoidal-cli-fast-path | lifesci-all | 40.22 s | 1,183 MiB | 3/3 | same proxy query, 1.26M-triple corpus |
| factoidal-cli-forced-slow-path (kill switch) | lifesci-all | 40.08 s | 1,183 MiB | 3/3 | " |
| jena-arq-inmemory | lifesci-all | 14.24 s | 1,734 MiB | 3/3 | " |
| jena-tdb2 (on-disk) | lifesci-all | 14.36 s | 2,440 MiB | 3/3 | " |
| pyoxigraph (in-memory) | lifesci-all | **4.42 s** | **452 MiB** | 3/3 | " |
| rdflib (in-memory, floor baseline) | lifesci-all | 38.81 s | 1,103 MiB | 3/3 | " |

Methodology notes (load-bearing, not boilerplate):

- **factoidal has no load-only CLI op** — the CLI parses, indexes, and
  answers a query in one process. The LOAD proxy used here is the
  **subject point-lookup query** (`q3`, confirmed in §4 to be *not*
  fast-path-eligible), run 3 fresh times; this is the actual wall/RSS
  cost of reaching a state where an arbitrary query can be answered,
  not the (much cheaper, aggregate-only) fast path. Using `q1`
  (`COUNT(*)`) instead would have understated this cost by roughly 4×
  (see §4) — the choice matters and is stated.
- **Jena arq (in-memory)** reparses the Turtle file on every
  invocation — its "load" cost IS its per-query cost, shown here via
  the same point-lookup proxy for an apples-to-apples row against
  factoidal's CLI.
- **Jena tdb2.tdbloader** builds a real persistent on-disk store (the
  direct analog of factoidal's COTTAS path) — 3 fresh loader runs into
  3 fresh target directories.
- **pyoxigraph / rdflib** load once per fresh Python process (3
  processes), `resource.getrusage(RUSAGE_SELF)` sampled immediately
  after `load()`/`parse()`, before any query.

**Read on LOAD:** pyoxigraph is the fastest and leanest load path by a
wide margin (2.3 s / 315 MiB vs. everyone else's 9-40 s / 700 MiB-2 GB).
Jena's `tdb2.tdbloader` carries the heaviest RSS of any engine (2.0-2.4 GiB
for an 888,949-1,258,752-triple corpus) despite building the smallest
number of in-process data structures — that cost is JVM/TDB2 index
construction overhead, not something comparable to factoidal's
in-memory footprint. factoidal's own two in-memory rows (~744 MiB /
~1.18 GiB) sit in the middle of the pack; its COTTAS import is the
single most expensive LOAD step measured (129 s), but that cost is
paid once at corpus-build time, not per server boot (see the cited
2026-07-05 review's own finding that eager sidecars + the 'COTD' magic
fix already collapsed the *reopen* cost to ~0.3 s — this benchmark did
not re-verify that reopen number, it is cited from that doc).

## 4. QUERY latency, cold and warm (gene corpus)

The 6 queries (identical SPARQL text sent to every engine; see
`tools/bench_competitive_queries.py` for the exact strings and why
each was chosen):

1. `q1_count_star` — `COUNT(*)` over the whole default graph.
2. `q2_bound_predicate_count` — `COUNT(*)` on `wdt:P684` (759,263 of
   888,949 triples, the dominant predicate).
3. `q3_subject_point_lookup` — all `(p, o)` for one fixed subject IRI
   (3 result rows).
4. `q4_two_pattern_join` — same-subject join between the dominant
   predicate and the rarest one (14 result rows).
5. `q5_group_by` — `GROUP BY` predicate (6 groups).
6. `q6_optional_filter` — required pattern + `OPTIONAL` + `FILTER`
   (25,083 rows, 9,117 with the optional variable bound).

Cold = first invocation (fresh process for the five CLI-based
rows per query; first `query()` call in an already-loaded process for
pyoxigraph/rdflib). Warm = median of 3 further invocations/calls (see
`cold_warm_methodology` in the JSON for the full disclosure of this
asymmetry between process-per-query and persistent-process engines).

| Engine | Query | Cold | Warm (median of 3) | Rows | Answer hash |
|---|---|---:|---:|---:|---|
| factoidal-cli-fast-path | q1_count_star | 6.65 s | 6.57 s | 1 | `03379de5` |
| factoidal-cli-forced-slow-path | q1_count_star | 26.28 s | 25.87 s | 1 | `03379de5` |
| factoidal-cottas (on-disk) | q1_count_star | **0.74 s** | 0.72 s | 1 | `03379de5` |
| jena-arq-inmemory | q1_count_star | 11.06 s | 10.56 s | 1 | `03379de5` |
| jena-tdb2 (on-disk) | q1_count_star | 1.91 s | 1.83 s | 1 | `03379de5` |
| pyoxigraph (in-memory) | q1_count_star | **0.22 s** | 0.21 s | 1 | `03379de5` |
| rdflib (floor) | q1_count_star | 8.78 s | 8.40 s | 1 | `03379de5` |
| factoidal-cli-fast-path | q2_bound_predicate_count | 6.55 s | 6.53 s | 1 | `fe789892` |
| factoidal-cli-forced-slow-path | q2_bound_predicate_count | 26.75 s | 26.52 s | 1 | `fe789892` |
| factoidal-cottas (on-disk) | q2_bound_predicate_count | 2.89 s | 2.88 s | 1 | `fe789892` |
| jena-arq-inmemory | q2_bound_predicate_count | 11.04 s | 10.78 s | 1 | `fe789892` |
| jena-tdb2 (on-disk) | q2_bound_predicate_count | 2.00 s | 1.79 s | 1 | `fe789892` |
| pyoxigraph (in-memory) | q2_bound_predicate_count | **0.18 s** | 0.17 s | 1 | `fe789892` |
| rdflib (floor) | q2_bound_predicate_count | 6.25 s | 6.21 s | 1 | `fe789892` |
| factoidal-cli-fast-path | q3_subject_point_lookup | 26.31 s | 26.38 s | 3 | `fe19111a` |
| factoidal-cli-forced-slow-path | q3_subject_point_lookup | 26.20 s | 26.68 s | 3 | `fe19111a` |
| factoidal-cottas (on-disk) | q3_subject_point_lookup | **62.17 s** | 61.64 s | 3 | `fe19111a` |
| jena-arq-inmemory | q3_subject_point_lookup | 9.94 s | 10.05 s | 3 | `fe19111a` |
| jena-tdb2 (on-disk) | q3_subject_point_lookup | 1.16 s | 1.18 s | 3 | `fe19111a` |
| pyoxigraph (in-memory) | q3_subject_point_lookup | **~0 ms** | ~0 ms | 3 | `fe19111a` |
| rdflib (floor) | q3_subject_point_lookup | **3 ms** | 2 ms | 3 | `fe19111a` |
| factoidal-cli-fast-path | q4_two_pattern_join | 25.95 s | 26.22 s | 14 | `ae7167c4` |
| factoidal-cli-forced-slow-path | q4_two_pattern_join | 26.31 s | 26.21 s | 14 | `ae7167c4` |
| factoidal-cottas (on-disk) | q4_two_pattern_join | **92.11 s** | 91.59 s | 14 | `ae7167c4` |
| jena-arq-inmemory | q4_two_pattern_join | 11.40 s | 11.48 s | 14 | `ae7167c4` |
| jena-tdb2 (on-disk) | q4_two_pattern_join | 3.88 s | 3.88 s | 14 | `ae7167c4` |
| pyoxigraph (in-memory) | q4_two_pattern_join | 0.58 s | 0.56 s | 14 | `ae7167c4` |
| rdflib (floor) | q4_two_pattern_join | **3 ms** | 3 ms | 14 | `ae7167c4` |
| factoidal-cli-fast-path | q5_group_by | **SKIP (timeout >600 s)** | SKIP | SKIP | — |
| factoidal-cli-forced-slow-path | q5_group_by | **SKIP (timeout >600 s)** | SKIP | SKIP | — |
| factoidal-cottas (on-disk) | q5_group_by | **SKIP (timeout >600 s)** | SKIP | SKIP | — |
| jena-arq-inmemory | q5_group_by | 11.68 s | 10.89 s | 6 | `e709bd9c` |
| jena-tdb2 (on-disk) | q5_group_by | 2.15 s | 2.05 s | 6 | `e709bd9c` |
| pyoxigraph (in-memory) | q5_group_by | **0.23 s** | 0.23 s | 6 | `e709bd9c` |
| rdflib (floor) | q5_group_by | 11.71 s | 11.48 s | 6 | `e709bd9c` |
| factoidal-cli-fast-path | q6_optional_filter | 68.78 s | 69.11 s | 25,083 | `e30f57b5` |
| factoidal-cli-forced-slow-path | q6_optional_filter | 69.40 s | 69.28 s | 25,083 | `e30f57b5` |
| factoidal-cottas (on-disk) | q6_optional_filter | **159.51 s** | 159.57 s | 25,083 | `e30f57b5` |
| jena-arq-inmemory | q6_optional_filter | 10.36 s | 10.74 s | 25,083 | `e30f57b5` |
| jena-tdb2 (on-disk) | q6_optional_filter | 2.57 s | 2.62 s | 25,083 | `e30f57b5` |
| pyoxigraph (in-memory) | q6_optional_filter | **0.22 s** | 0.22 s | 25,083 | `e30f57b5` |
| rdflib (floor) | q6_optional_filter | 2.83 s | 2.71 s | 25,083 | `e30f57b5` |

(Answer hashes truncated to 8 hex chars for table width; full 16-char
SHA-256-derived hashes are in `docs/test-results/competitive-bench.json`'s
`query_results[].answer_sha256`. Every engine's hash for a given query
is identical — see the agreement table below.)

### Cross-engine answer agreement

| Query | Engines compared | Agree? |
|---|---|---|
| q1_count_star | factoidal-fast, factoidal-slow, factoidal-cottas, jena-arq, jena-tdb2, pyoxigraph, rdflib | **yes** |
| q2_bound_predicate_count | " | **yes** |
| q3_subject_point_lookup | " | **yes** |
| q4_two_pattern_join | " | **yes** |
| q5_group_by | jena-arq, jena-tdb2, pyoxigraph, rdflib (factoidal's 3 rows SKIP, not compared — see above) | **yes** |
| q6_optional_filter | factoidal-fast, factoidal-slow, factoidal-cottas, jena-arq, jena-tdb2, pyoxigraph, rdflib | **yes** |

**Zero VOID rows.** Every query where every engine actually produced an
answer, all engines agree exactly (order-insensitive row-set
comparison, bare-lexical value comparison — see `canonicalize_term`'s
docstring in `tools/bench_competitive.py` for the one disclosed
limitation: literal datatype/language-tag distinctions are not
compared, which is safe for this specific query set's all-URI/
all-integer results but would need strengthening for a query set with
typed-literal columns). `q5_group_by` has 3 fewer engines in its
comparison set because factoidal's own three query paths (in-memory
fast, in-memory slow, on-disk COTTAS) all timed out before producing
an answer at all — that is reported as a SKIP, not folded into a false
"disagreement," and not hidden either.

**Harness bug found and fixed during this run, disclosed:** the first
full run crashed partway through `q6_optional_filter`'s answer
comparison (`TypeError: '<' not supported between instances of 'str'
and 'NoneType'`, sorting rows where the `OPTIONAL` variable is
legitimately unbound in most rows). Fixed in
`tools/bench_competitive.py`'s `normalize_rows` (commit message: sort
by an explicit `(is_none, value-or-placeholder)` key instead of
comparing `None` and `str` directly), verified with a standalone unit
check before rerunning, then the QUERY phase was rerun with
`--only-phase query --reuse-gene-tdb2-dir ... --reuse-gene-cottas-artifact
...` to reuse the already-built on-disk artifacts rather than repeat
the ~16-minute LOAD phase. This is why LOAD (§3) and QUERY (§4) were
measured against different HEAD commits (see the provenance note at
the top of this doc).

## 5. The honest read

**Where factoidal wins:** the COTTAS on-disk path's `COUNT(*)` (0.74 s)
and bound-predicate `COUNT` (2.89 s) are competitive with or faster
than Jena's TDB2 (1.91 s / 2.00 s) on the same corpus, and both clear
factoidal's own in-memory CLI by 9-36×. This is the intended shape of
the COTTAS format (columnar, ZSTD-compressed, presence-bitmap-pruned
full-graph aggregates) working as designed — a real, reproducible win
on the query type it was built for.

**Where factoidal loses, ranked by how much it should worry the "world
class" claim:**

1. **`GROUP BY` does not finish in under 10 minutes on any of
   factoidal's three own paths (in-memory fast, in-memory slow,
   on-disk COTTAS), on a corpus of 888,949 triples grouping into just
   6 buckets.** Every competitor — Jena's 2005-era ARQ engine, Jena's
   TDB2 index, pyoxigraph, and even pure-Python rdflib — answers the
   identical query in under 12 seconds (rdflib: 11.7 s; jena-tdb2:
   2.15 s; pyoxigraph: 0.23 s). This is not a "some queries are slower"
   gap; it is a missing capability at this scale, on every storage
   backend factoidal has, including the one (COTTAS) that was
   otherwise the star performer in this benchmark. It should be
   treated as a correctness-adjacent severity bug (a query that never
   returns is operationally indistinguishable from one that returns
   wrong data) and filed as its own GitHub issue with this benchmark's
   JSON as the reproduction case, not folded into the general
   "GROUP BY is slow" prior art already in the codebase.
2. **The streaming "fast path" only accelerates two of the six query
   shapes tested (`COUNT(*)` and bound-predicate `COUNT`), and the
   speedup it buys (6.6 s vs 26-27 s, ~4×) evaporates for every other
   shape** — point lookup, join, and optional-filter all cost the
   identical ~26-27 s whether the kill switch is set or not, because
   none of them are eligible for the fast path at all; they pay full
   in-memory materialization regardless. A user who reaches for
   "factoidal is fast" based on a demo `COUNT(*)` query will hit the
   *un*-accelerated cost on their very next query. The practical
   consequence: **a 3-row point lookup on an 888,949-triple graph
   costs 26 seconds** in factoidal's in-memory CLI — 8,700× slower
   than rdflib's 3 ms for the identical query and identical answer on
   the identical data, and roughly a million times slower than
   pyoxigraph's sub-millisecond response. rdflib is the "floor
   baseline" by the task brief's own framing, and it beats factoidal
   here by four orders of magnitude.
3. **COTTAS (the on-disk path) gets slower, not faster, as query
   selectivity/row-count increases** — 0.74 s for `COUNT(*)` (1 row
   out), 62.17 s for the 3-row point lookup, 92.11 s for the 14-row
   join, 159.51 s for the 25,083-row optional-filter. This is the
   *inverse* of the shape an index-backed on-disk store should have
   (point lookups and small joins ought to be the *cheap* case, full
   aggregates the *expensive* one). Jena's TDB2, built on the same
   underlying gene.ttl corpus, shows the opposite and expected shape
   (1.16-3.88 s across every query type, roughly flat). This is
   consistent with — and adds a fourth, previously-unmeasured data
   point to — the query-shape sensitivity findings already logged in
   `docs/designissues/2026-07-05-disk-backed-db-perf-review.md` (the
   row-group-count/quadratic-locate findings): COTTAS's prune cascade
   evidently only pays off for the full-scan aggregate case exercised
   there, not for point lookups or small joins, on this corpus's row
   layout.

**What this benchmark does not settle:** it exercises one mid-sized
corpus (888,949 triples) and 6 query shapes chosen to span
aggregate/point-lookup/join/group-by/optional categories, not the full
SPARQL 1.1 surface, and it runs on shared cloud-sandbox hardware (not
isolated benchmark iron) — the *absolute* numbers should not be quoted
outside this doc without re-measurement, but the *relative* shapes
(COUNT-only fast path, GROUP BY non-termination, COTTAS's inverted
selectivity curve) are large enough (10×-1000×+) that sandbox noise
does not explain them away.

## 6. Reproducing this benchmark

```bash
tools/bench-competitive.sh                       # full run, both corpora, all engines detected
tools/bench-competitive.sh --skip-lifesci-all-load  # gene only (faster)
tools/bench-competitive.sh --only-phase query    # query matrix only (needs a prior `load`/`all` run
                                                  # in the same --scratch dir for the on-disk artifacts,
                                                  # or --reuse-gene-tdb2-dir/--reuse-gene-cottas-artifact)
JENA_HOME=/path/to/apache-jena-5.2.0 tools/bench-competitive.sh   # use an existing Jena instead of fetching
python3 tools/bench_competitive_report.py        # regenerate the markdown tables from the committed JSON
```

Every engine is detected, not assumed: if Jena/pyoxigraph/rdflib is
unavailable, its rows are marked SKIP with a stated reason rather than
silently omitted or faked. If `bin/linux-x86_64` has uncommitted
changes (a sibling session mid-rebuild), the harness refuses to run
against a moving target unless `--allow-dirty-bin` is passed, in which
case it uses `git show HEAD:bin/linux-x86_64/<binary>` into a scratch
dir and records that provenance in the JSON's `engines.factoidal`
entry — this happened twice during this session's own run (see the
provenance note at the top of this doc).

Every per-invocation timeout is capped at 600 s (anti-pattern #17); a
cold run that hits the cap skips its warm runs rather than repeating a
proven-hanging combination 3 more times, and is reported as SKIP with
the reason stated, never silently dropped.
