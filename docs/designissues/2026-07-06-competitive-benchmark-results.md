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
   **Update 2026-07-06: fixed — see §7.** The O(n²) list-append
   accumulation in `SPARQL11.Algebra.fst`'s `add_to_groups` is gone;
   all three factoidal paths now finish (27.17 s / 26.74 s / 109.93 s
   vs. Jena's 2.05 s — order-of-magnitude, not literal, parity).
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

## 7. Update, 2026-07-06: the GROUP BY cliff (§4/§5 item 1) is fixed

**Mechanism, named with file:line.** `formal/fstar/SPARQL11.Algebra.fst`'s
`add_to_groups` (the per-row group-accumulation step inside `group_by`,
~line 3115) grew the matched group's solution list with
`Lh.append_tr g.g_solutions [mu]`. `append_tr xs ys` (`RDF.List.Helpers.fst`)
walks its **entire first argument** to build a reversed accumulator before
splicing `ys` on — it is O(len xs), not O(1). Since `g.g_solutions` is
exactly the list being appended onto, every one of the 888,949 rows in
`q5_group_by` paid a cost proportional to how many rows had already
landed in its group. `GROUP BY ?p` over `gene.ttl` produces 6 groups, one
of which (`wdt:P684`) holds 759,263 rows — so the append chain for that
one group alone cost 1+2+...+759,263 ≈ 2.9×10^11 operations, which is
exactly the >600 s timeout recorded in §4 on **all three** factoidal
paths (in-memory fast path, in-memory forced-slow-path, COTTAS on-disk):
the cliff is in the shared `SPARQL11.Algebra.fst` grouping code, not in
any one storage backend.

**Fix.** `add_to_groups` now conses the new solution onto the front of
the matched group (`mu :: g.g_solutions`, O(1)) instead of appending to
the back; `group_by` reverses each group's solution list exactly once,
after its fold over all rows completes, restoring the original row
order in one O(n) pass total (rather than paying an implicit O(n)
reversal on every single row, as the old repeated-append code did).
Group lookup itself (scanning the small number of *distinct* keys seen
so far) is unchanged — still O(g) per row, g = distinct group count;
that remains fine for this benchmark's g=6 and is flagged in the code
comment as a separate perf track if a future workload has very many
distinct GROUP BY keys. Verified clean under F* 2025.12.15 / z3 4.13.3,
no `--lax`, no `--admit_smt_queries`.

**Growth curve, before and after** (same query, subsets of `gene.ttl`
by line-prefix, same CLI invocation pattern as `bench_competitive.py`):

| Subset | Unfixed (committed `bin/linux-x86_64/factoidal`, commit `5e8399a`) | Fixed |
|---|---:|---:|
| ~10k lines | 0.18 s | 0.13 s |
| ~50k lines | 2.61 s | 0.70 s |
| ~100k lines | 16.11 s | 1.50 s |
| ~200k lines | 112.48 s | 3.21 s |

Unfixed: exponent trending from ~1.7 (10k→50k) to ~2.8 (100k→200k) —
consistent with an O(n²) mechanism whose relative overhead grows as the
dominant group's list gets larger (plus additional GC pressure from the
ever-larger repeated copies). Fixed: exponent ~1.1 across the same
range — linear, as expected once the accumulation is O(1) per row.

**Full 888,949-triple corpus, fixed, all three factoidal paths** (measured
in an isolated git worktree built from HEAD `94df5d3` plus only the
`SPARQL11.Algebra.fst` patch — see provenance note below):

| Path | Time | Answer |
|---|---:|---|
| in-memory (fast path) | 27.17 s | `e709bd9ceadd3c45` |
| in-memory (forced slow path) | 26.74 s | `e709bd9ceadd3c45` |
| COTTAS on-disk | 109.93 s | `e709bd9ceadd3c45` |

All three now finish (down from >600 s / indeterminate) and all three
produce `e709bd9ceadd3c45` — byte-identical to Jena's, pyoxigraph's, and
rdflib's answer for this query (§4 table above). This is
**order-of-magnitude, not literal, parity** with Jena's in-memory 2.05 s
warm figure (27.17/2.05 ≈ 13×) — the quadratic cliff that made the query
never finish is gone, but the remaining linear-time constant factor of
GROUP BY partitioning (per-row key evaluation, alias binding, and the
O(g) group-list scan) is a separate, smaller optimization opportunity
this fix does not address.

**Provenance and isolation.** At measurement time, `bin/factoidal-cli/factoidal_cli.ml`,
`formal/fstar/RDF.Store.Columnar.DeltaLog.fst`, and
`formal/fstar/SPARQL11.Store.fst` had uncommitted, unrelated, in-flight
changes from a concurrent session (a durable-update/compaction feature,
`docs/designissues/2026-07-06-durable-update-design.md`) that briefly left
the main tree's `bin/factoidal-cli` consumer binary in a non-compiling
state. The `SPARQL11.Algebra.fst` GROUP BY fix was verified, extracted,
compiled, benchmarked, and floor-tested in an isolated `git worktree`
checked out from `HEAD` (commit `94df5d3`) with **only** the
`SPARQL11.Algebra.fst` diff applied on top — not the concurrent session's
WIP — so none of the numbers or floor results above are affected by that
unrelated, still-in-progress work. Floors checked in that isolated
worktree: SPARQL 631 pass/0 fail (out of 631, includes the aggregates
suite that exercises GROUP BY), RDF 1031 pass/0 fail (out of 1031),
RDFC-1.0 86 pass/0 fail (out of 86), `tests/unit/` 30 file(s) pass/0
fail (out of 30), `cottas_row_order_regressions.sh` 27 pass/0 fail (out
of 27), `cottas_corpus_regressions.sh` 4 pass/0 fail (out of 4),
`dict_global_cache_parity.sh` 6 pass/0 fail (out of 6),
`streamable_fastpath_regressions.sh` 13 pass/0 fail (out of 13).
`tests/local/durable_update_stage3.sh` showed 6 pass, 9 fail (out of 15)
in this same isolated worktree — this is the concurrent session's
in-progress durability feature at its last-committed state (every
failing check touches `--delta-log`, which this patch does not), not a
regression caused by this fix; it is called out here rather than
silently omitted. The raw numbers above are also recorded in
`docs/test-results/competitive-bench.json`'s `group_by_fix_2026_07_06`
key and the three updated `q5_group_by` rows in `query_results`.

## 8. Update, 2026-07-06: SEARCH selectivity — loss 3's inverted curve, partially flattened

§5's loss 3 ("COTTAS gets slower, not faster, as selectivity/row-count
increases") was profiled and partially fixed this session. **Profile
attribution first, with file:line** (strace + the stderr trace already
compiled into the binary — no new instrumentation needed): the SELECT
path's 62.17 s / 92.11 s / 159.51 s costs for `q3`/`q4`/`q6` were NOT
dominated by `RDF.CottasStore.fst`'s row-group walk decoding all four
columns of every row group (the mechanism the task brief assumed, by
analogy with the 2026-07-06 COUNT fix, §7's sibling item recorded
elsewhere in this doc's companion perf-review doc) — every one of
those three queries binds or projects every one of `s`/`p`/`o`, so
skipping a column's decode the way the COUNT fix does buys nothing
here. The real cost, found by adding a timestamped wrapper around the
binary's own `[bet7-trace]`/`[qof3-trace]` stderr lines: `build_qp_row`
(`RDF.CottasStore.fst:503-508`) converts every matched row's
already-decoded column TOKEN into an id via
`ondisk_lookup_*_id_global`, which on first touch of a column
triggers the OCaml Bet7 lazy loader's `collect_distinct`
(`experimental_ocaml_glue/cottas_ondisk_runtime.sh:213-238`) —
decoding and deduping **the entire column across every row group of
the whole corpus**, ignoring `plan_candidate_rgs`'s row-group pruning
entirely, just to hand back a value the row-group decode already had
as a string. Measured on gene.ttl (888,949 rows, 8 row groups):
subject `collect_distinct` ~9-10 s (91,871 distinct values), object
`collect_distinct` ~43 s (75,142 distinct values) — a fixed,
corpus-wide tax paid once per column per process, independent of how
selective the query is.

**Crossover policy** (the task's own framing asked for one): there
isn't a useful column-skip crossover on this corpus — every SEARCH
query here needs every column's value, so "decode only the bound
columns" has nothing to skip. The crossover that matters is a
different axis: stop resolving a corpus-wide id at all for output
construction, and parse the raw token directly instead. That is what
this fix does.

**Fix, in F\*** (verified, z3 4.13.3, no `--lax`; no
`experimental_ocaml_glue/` changes — this fix REMOVES a code path's
dependence on that glue, it adds none): `RDF.CottasStore.fst` gained
`cottas_qp_row_tok` (a row shape holding the four raw column strings a
matched row already decoded, instead of ids), `token_to_subject` /
`_predicate` / `_object` / `_graph_name` (parse a raw COTTAS cell
directly into its typed RDF term via `Parser.NTriples`'s existing
verified N-Triples term grammar — `docs/cottas-format-v1.md` §4
defines the COTTAS cell grammar as literally a subset of that grammar,
confirmed against the real gene.cottas artifact via
`SELECT s FROM parquet_scan(...)`, which returns bracket-wrapped IRI
tokens exactly as the format spec requires), `filter_zipped_rows_tok_seq`
/ `_limited_tok_seq`, and tok-shaped siblings of every row-group walk
(`walk_row_groups_search_tok_global`, `walk_candidate_rgs_search_tok_
global`, and their `_limited` variants), plus `cottas_ondisk_row_tok_
to_quad` / `cottas_ondisk_rows_tok_to_triples`. `cottas_ondisk_search`
and `cottas_ondisk_search_limited` now return `cottas_qp_row_tok`
instead of the id-based `cottas_qp_row` (`Parser.BallyhooCOTTAS.fst`);
`RDF.Store.Capabilities.Cottas.fst`'s `sc_solve`/`sc_solve_limited` —
the only call site of either function — updated to match. The
BOUND-side resolution (a query's own literal subject/predicate/object
→ id, via `cottas_ondisk_encode_subject`/`_predicate`/`_object`) is
**unchanged** and still goes through Bet7; see "not fixed" below.

**Measured** (gene.ttl, 888,949 quads, CS-clustered + eager sidecars,
8 row groups; "before" = binary `a3ef63c`, the numbers in §4 above;
"after" = this fix, measured in an isolated git worktree from HEAD
`2030fb2` with only the `RDF.CottasStore.fst` /
`RDF.Store.Capabilities.Cottas.fst` /
`tests/unit/parquet_rle_dictionary_multi_row_group.ml` diff applied —
same isolation discipline §7 used, for the same reason: a concurrent
sibling session was mid-rebuild in the main tree throughout):

| Query | Before | After | Ratio | Why |
|---|---:|---:|---:|---|
| `q1_count_star` | 0.74 s | 0.76 s | ~flat | unbound `COUNT(*)`, never calls `cottas_ondisk_search` — untouched by design |
| `q2_bound_predicate_count` | 2.89 s | 2.92 s | ~flat | bound-predicate `COUNT`, uses `cottas_ondisk_count_exact` — untouched by design |
| `q3_subject_point_lookup` | 62.17 s | **17.7 s** | **~3.5×** | object's Bet7 tax (~43 s) gone; subject's Bet7 tax (~9-10 s, bound-side, not fixed) remains |
| `q4_two_pattern_join` | 92.11 s | **31.1 s** | **~3.0×** | same as q3 — the join executor binds subject mid-plan even though the SPARQL text never does, re-triggering the unfixed bound-side resolution |
| `q6_optional_filter` | 159.51 s | **100.7 s** | **~1.6×** | Bet7 fully eliminated (no `collect_distinct` call appears in the trace at all); the remaining ~100 s is genuinely proportional to the 25,083-row match set (row-group decode + per-row term parsing), not a corpus-wide constant |

This is **not** the full flattening the task asked for — `q3`/`q4`
still cost an order of magnitude more than Jena TDB2's 1.16-3.88 s
flat curve (§4), because the bound-side Bet7 tax (documented below)
survives this round, and `q6`'s residual cost reflects real per-row
work on a genuinely large (25,083-row) result set, which even a flat
index-scan engine pays something for. What the fix does establish:
the selectivity curve's *inversion* — the specific finding that a
1-row aggregate government cost less than a 3-row lookup which cost
less than a 14-row join which cost less than a 25,083-row scan, in
that exact backwards order — is gone for the two point/join queries,
and materially reduced for the large scan; every "after" number is now
closer to (though still above) TDB2's order of magnitude than to the
"before" column.

**Correctness.** All 5 queries' output is byte-identical before vs
after (row counts, bindings, and content unchanged) — confirmed by
diffing the CLI's table output. Regression pins:
`tests/unit/parquet_rle_dictionary_multi_row_group.ml` grew a tenth
section (116 assertions in the file now, 0 fail, up from 102): 14 new
pins on `token_to_subject`/`_predicate`/`_object`/`_graph_name`
against hand-written, format-conformant tokens (this file's own
fixture data is not bracket-wrapped and so is deliberately not reused
for term-level parsing pins — see the section's own comment for why)
plus `cottas_ondisk_row_tok_to_quad`'s `DEFAULT`-sentinel and
named-graph handling. `tests/unit/store_capabilities_unit.ml`'s
`raw_solve`/`raw_solve_limited` (which call `cottas_ondisk_search`
directly, cross-checking the `store_caps` wrapper against the raw
entry point) were updated to the tok-shaped consumer — this file's
381 assertions all pass, and would have caught a mismatch between the
wrapper and the raw path had one existed.

**Not fixed this round.** The bound-side term→id resolution
(`cottas_ondisk_encode_subject`/`_predicate`/`_object`/`_graph_name`,
`RDF.CottasStore.fst`:152-170) still goes through the same Bet7
corpus-wide revmap — any query (or join/optional execution step) that
BINDS a subject still pays that column's one-time `collect_distinct`.
Closing this means serializing the query's own literal term directly
to its raw column-token form (a local, O(1) computation — the
symmetric operation to this fix's `token_to_subject`/etc) instead of
resolving an id, and touches `cottas_bound_qp` (shared with the dead
in-memory `GB_COTTAS` path in `Parser.BallyhooCOTTAS.fst`) — a wider
change than this one, not attempted here to keep this fix
commit-sized. Filed as the natural next item. A second, smaller,
unconfirmed hypothesis about `q6`'s residual cost (the `OPTIONAL`
pattern's join strategy may re-issue a bound on-disk search per outer
row rather than a single batched pass) is noted but not investigated
further this round.

**Floors after the change** (measured in the isolated worktree
described above — repo root only, per this doc's own convention):
SPARQL suite 631 pass, 0 fail (of 631); RDF suite 1,031 pass, 0 fail
(of 1,031); `tests/unit/run-all.sh` 30 file(s) pass, 0 file(s) fail
(of 30); `tests/local/cottas_row_order_regressions.sh` 26 pass, 0 fail
(of 26); `tests/local/cottas_corpus_regressions.sh` 4 pass, 0 fail (of
4); `tests/local/dict_global_cache_parity.sh` 6 pass, 0 fail (of 6);
`tests/local/streamable_fastpath_regressions.sh` 13 pass, 0 fail (of
13); `tests/local/durable_update_stage3.sh` 15 pass, 0 fail (of 15);
`tests/local/durable_update_stage4_compaction.sh` 29 pass, 0 fail (of
29). The raw numbers above are also recorded in
`docs/test-results/competitive-bench.json`'s
`search_selective_decode_2026_07_06` key.

## 9. Update, 2026-07-06: BOUND-side token-direct — §8's "not fixed this round" residual, closed

§8 left the bound-side term→id resolution in place: any query that
BINDS a subject/predicate/object still paid that column's one-time
corpus-wide `collect_distinct` populate (subject ~9-10 s / 91,871
distinct; the mechanism §8 named as the surviving residual). This
round mirrors the output-side fix on the bound side.

**Fix, in F\*** (verified, F\* 2025.12.15 / z3 4.13.3, no `--lax`; no
`experimental_ocaml_glue/` changes — this removes the live query
path's LAST dependence on the Bet7 term-dictionary glue, it adds
none): `RDF.CottasStore.fst` gained `bound_subject_to_token` /
`bound_predicate_to_token` / `bound_object_to_token` /
`bound_graph_iri_to_token` (serialize the query's own typed bound term
directly to its COTTAS cell token via the existing verified N-Quads
serializer `RDF.NQuads.Serialize` — `docs/cottas-format-v1.md` §4
defines the cell grammar as exactly that token form), the
`cottas_bound_qp_tok` record (bounds as raw token strings, the
bound-side sibling of §8's `cottas_qp_row_tok`),
`cottas_ondisk_build_bound_qp_tok` (no dictionary lookup, never
`None` — an absent term still yields zero rows cheaply via the
dict-page candidate prune), and `_tok` siblings of all four entry
points (`cottas_ondisk_search_tok` / `_search_limited_tok` /
`_estimate_tok` / `_count_exact_tok`).
`RDF.Store.Capabilities.Cottas.fst`'s `sc_solve` / `sc_solve_limited`
/ `sc_estimate` / `sc_count_exact` now use the tok pairing; the
id-based functions remain defined (verification spec + compat) with
no live caller.

**What still legitimately needs ids, kept as-is per structure:**

| Structure | Needs an id? | How it gets one |
|---|---|---|
| compound (p,o) presence bitmap prefilter | yes (sorted-rank pair-code) | `compound_po_dict_encode` reads `.p.dict`/`.o.dict` headers directly (1576873 path) — cheap, never the Bet7 revmap; unchanged |
| row-group pruning (`plan_candidate_rgs`) | no | dict-PAGE membership test compares the bound TOKEN string against per-rg dictionary pages — already token-shaped, unchanged |
| row matching (`cell_match` in the walks) | no | bound token vs decoded cell, string equality — now fed by direct serialization instead of id→token |
| output construction | no | token-direct since 9750eb7 (§8) |
| graph scope | no | `COS_DefaultOnly` → `"DEFAULT"` sentinel, `COS_NamedGraph` → `"<iri>"` — serialized directly, no graph-dict encode |

**Measured** (gene corpus, 888,949 quads, artifact
`.claude-runs/repro/corpus-gene/gene/v1/data.cottas`, one-shot
`factoidal query --data-cottas`, `tools/bench_rusage_run.py`, 3 runs
each, median wall / max RSS; "before" = committed HEAD binary
`f30bc52`, "after" = working-tree binary carrying this fix — see the
provenance caveat below):

| Query | Before wall | After wall | Before peak RSS | After peak RSS | Bound-side populate removed |
|---|---:|---:|---:|---:|---|
| q1 `COUNT(*)` | 0.37 s | 0.39 s | 56,004 KB (54.7 MiB) | 60,368 KB (59.0 MiB) | none bound — untouched by design |
| q2 bound-predicate COUNT | 1.77 s | 1.11 s | 91,500 KB (89.4 MiB) | 92,880 KB (90.7 MiB) | predicate `collect_distinct` (6 distinct, full 888,949-row walk) |
| q3 subject point lookup (3 rows) | 12.06 s | 2.17 s (**5.6×**) | 139,724 KB (136.4 MiB) | 94,264 KB (**92.1 MiB**) | subject `collect_distinct` (91,871 distinct) |
| q4 two-pattern join (14 rows) | 31.08 s | 4.07 s (**7.6×**) | 191,112 KB (186.6 MiB) | 146,788 KB (143.3 MiB) | predicate + subject populates |
| q6 optional-filter (25,083 rows) | 73.94 s | 44.88 s (**1.65×**) | 210,888 KB (205.9 MiB) | 209,900 KB (205.0 MiB) | predicate populate; residual is real per-row work on the 25,083-row match set |
| stage-4 point lookup `LIMIT 1` | 11.67 s | 1.75 s | 139,664 KB (136.4 MiB) | 94,052 KB (**91.8 MiB**) | subject populate |
| buffer mode (`--data-cottas-mem`) point lookup | — | 1.79 s | — | 94,052 KB — identical to file mode | " |

The stage-4 target ("subject-bound point lookup under 100 MiB, from
136.4") is met: 94,052-94,264 KB across every point-lookup variant,
file and buffer mode alike. `tests/local/cottas_lazy_dictionary_stage4.sh`'s
interim <150 MiB pin is tightened to <100 MiB, and its per-column
trace expectations inverted (a bound query now populates NO term
dictionary; only the named-graph enumeration at dataset construction
still fires, by design) — 12 pass, 0 fail (out of 12) post-change.

Attribution is trace-pinned, not inferred: in every "before" stderr
the removed cost appears as `ensure_subjects_loaded` /
`ensure_predicates_loaded` + `collect_distinct` lines; in every
"after" stderr those lines are absent (`ensure_graphs_loaded` alone
remains). Outputs are byte-identical before vs after on all of
q1/q2/q3/q4/q6 (`diff` on the CLI table output; q6's 25,083 rows
included), and stable across repeat runs.

**Provenance caveat.** The "after" binary also carries a concurrent
sibling session's uncommitted BaseWriter-v2 work
(`Parquet.Footer.fst`: dictionary-page codec plumbing + a
position-indexed dictionary lookup tree; `bin/factoidal-cli/
factoidal_cli.ml`: import/compact call `serialize_cottas_v2`), which
touches the read path's dictionary decode. The wall-clock wins above
are attributable to THIS fix via the trace pins (the removed
`collect_distinct` walks are the removed seconds), but the small RSS
deltas outside the point-lookup shape — q1's +4.4 MiB and q2's
+1.4 MiB — are NOT explained by this fix (identical traces, identical
walks, structurally identical extracted code for the id/tok
`count_exact` pair; process baseline on a 1-quad fixture is 124 KB
SMALLER in the after binary) and are consistent with the sibling's
in-flight dictionary-lookup tree. Disclosed rather than untangled:
isolating it would need a third binary built from HEAD plus only this
diff, which the landing coordinator can do if the delta matters.

**Floors after the change** (working tree, repo root): SPARQL 631
pass, 0 fail (of 631); RDF 1,031 pass, 0 fail (of 1,031);
`tests/unit/run-all.sh` 32 file(s) pass, 0 fail (of 32) — includes
`store_capabilities_unit` 521 pass, 0 fail (the wrapper-vs-raw
equivalence net, its raw side updated to the tok pairing) and
`parquet_rle_dictionary_multi_row_group` 116 pass, 0 fail (the
multi-row-group pins); `cottas_row_order_regressions.sh` 27 pass, 0
fail (the three-way agreement matrix); `cottas_corpus_regressions.sh`
4 pass, 0 fail; `cottas_native_import_regressions.sh` 17 pass, 0
fail; `dict_global_cache_parity.sh` 6 pass, 0 fail;
`streamable_fastpath_regressions.sh` 13 pass, 0 fail;
`inmemory_bytes_store_stage3.sh` 23 pass, 0 fail;
`durable_update_stage3.sh` 15 pass, 0 fail;
`durable_update_stage4_compaction.sh` 29 pass, 0 fail;
`cottas_lazy_dictionary_stage4.sh` 12 pass, 0 fail.
(A first unit-suite run showed 3 build-stage failures that
disappeared on re-run — link races against the sibling session's
concurrent compile, each file green when rerun alone and the full
suite 32/32 on the quiet rerun. `cottas_ask_decode_failure_
regressions.sh` reports its single check as SKIP — "fixture no longer
reproduces the undecodable-column shape" — with the HEAD binary too;
pre-existing, not this change.)
