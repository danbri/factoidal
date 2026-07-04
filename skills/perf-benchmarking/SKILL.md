---
name: perf-benchmarking
description: Measure, record, and gate Factoidal performance — parser throughput benchmarks, UK Parliament query bench, query observability (Server-Timing, /admin/recent.json, --explain), profiling policy, and the history of why things were slow. Use when the user asks "is it faster", "benchmark the parser", "why is this query slow", before claiming any speed win, or when a perf number in docs looks stale. Speed is measured separately from correctness; never claim a perf improvement inside a compliance change without its own measurement.
---

# Performance measurement and benchmarking

Correctness is measured with `w3c_runner` and the dashboard (see
`test-suites`). Speed is measured with the harnesses below. The rule
that binds them: **never claim a speed win unless it was measured
separately from a compliance change** — one commit's number must be
attributable to that commit.

## Harnesses

### Turtle/parser throughput — `formal/fstar/bench-turtle-metrics.sh`

Generates four fixtures in `/tmp/factoidal-metrics` (`prefixed-1000`,
`fulliri-1000`, `unicode-1000`, plus `berlin-1000` when
`examples/data/third_party/Berlin.ttl` is present), rebuilds `factoidal` from
`ocaml-output/`, and runs `factoidal --count` under `/usr/bin/time`
with `RUNS=5` reporting median/min/max seconds and peak RSS. Requires
the F\* opam switch (it recompiles). To measure a **committed binary**
without a toolchain, generate the same fixtures and time
`bin/<platform>/factoidal --count` directly — keep the median-of-N
discipline.

### Parse + serialize throughput — `tools/bench-parse-serialize.sh`

Runs against the **committed** `bin/<platform>/factoidal` /
`factoidal-dump-nq` binaries only — no F\* toolchain, no rebuild.
Measures `factoidal count` (parse: N-Triples, Turtle, RDF/XML),
`factoidal-dump-nq` (serialize: parse + sorted N-Quads dump), and
`factoidal canonicalize` (RDFC-1.0; capped at 100k triples) at
10k/100k/1M triples on deterministic synthetic fixtures, plus the UK
Parliament TriG corpus if present (skipped gracefully if not). Each
measurement is a median of 3 runs, each run capped at 120s
(`timeout`); a cap trip is recorded as a **documented skip**, not a
silent omission. `serialize_nq` and `canonicalize` numbers are
end-to-end (parse included) — the CLI has no parse-once/format-many
entry point.

Outputs `docs/test-results/perf-parse-serialize.json` (machine-
readable) and `.../perf-parse-serialize.fragment.html` (included
fail-soft by `formal/fstar/generate-report.sh` into the public
dashboard). CI: the `parse-serialize-bench` job in
`.github/workflows/ukparliament-bench.yml`.

**Known anomaly (measured 2026-07-04, committed `bin/linux-x86_64`):**
`factoidal count` scales as expected (~80-90k triples/s through 1M,
consistent with the baselines above), but `factoidal-dump-nq` and
`factoidal canonicalize` are severely superlinear on the *same*
triple-only (no-bnode) fixtures — e.g. `dump-nq` on 1,000 triples
takes ~0.65s but on 2,000 triples takes ~12.9s (should be ~1.3s if
linear). `canonicalize` shows the same shape (1,000: ~0.46s; 2,000:
~8.6s). Both hit the 120s/run cap well before 100k triples. RDF/XML
parsing separately crashes with `Stack overflow` above ~10k triples
(likely non-tail-recursive descent in the XML/RDF-XML parser). None
of these are fixed by this benchmarking work — they are flagged here
per the "perf opportunism" standing order below; a GitHub issue
should be filed before anyone relies on `dump-nq`/`canonicalize`/
RDF-XML at scale.

### Query latency — UK Parliament bench

`tools/bench_ukpar_modern.py` (and the older `bench_ukpar_queries.py`)
POST the 24 queries in `third_party/data/ukparliament/sparql/` to a
running endpoint, wall-clock each with a per-query timeout, and emit
CSV+JSON. The checked-in baselines live at
`docs/test-results/ukparliament-bench-modern.{csv,json}`.

CI gate: `.github/workflows/ukparliament-bench.yml` boots the daemon
on the checked-in corpus, runs the bench, and diffs against the
baseline via `.github/scripts/ukparliament_bench_diff.py` (zero
successful queries = hard regression). It runs on push, PR, and a
daily cron. If your change legitimately shifts the baseline, update
the baseline JSON in the same PR and say why.

### Other tools

- `tools/backend_benchmark.py` — backend comparisons.
- `tools/compare_rdf_parser_counts.py` — parse-speed and count parity
  vs pyoxigraph.
- `tests/unit/` perf repros (`rdfxml_parser_perf.ml`,
  `owl_direct_pipeline_timing.ml`) — keep perf repros as unit tests so
  regressions are one command away.

## Current baselines (measure, don't trust)

Measured 2026-07-03 against the committed `bin/linux-x86_64/factoidal`
(cloud container, bash wall-clock, median of 3):

| Fixture | Time | Rate |
|---|---:|---:|
| prefixed 1,000 triples | 0.02s | ~50k triples/s |
| full-IRI 1,000 triples | 0.04s | ~25k triples/s |
| unicode 1,000 triples | 0.02s | ~50k triples/s |
| prefixed 100,000 triples | 0.93s | ~108k triples/s |
| prefixed 1,000,000 triples | 9.66s | ~104k triples/s |

Scaling is near-linear through 1M triples. Any doc still quoting
"~40 triples/s", "25s per 1,000 triples", or "35MB never finishes"
(e.g. old tables in `docs/claude-rules/performance.md`) describes the
pre-fix engine — see the history below. When you see such a number,
re-measure and update the doc rather than propagating it.

## Scaling status: where the walls are (2026-07)

Parse throughput is no longer the bottleneck. The current walls:

- **In-memory store**: fully W3C-compliant and, since the #259
  sort-and-group fix in `build_indexed`
  (`RDF.Graph.Executable.fst`), linear in time and memory. Measured
  2026-07-03 (committed linux binary, N-Quads → GRAPH-count query,
  end-to-end incl. parse + index + eval): 43k quads 2.2s / 115 MB at
  100k / 1M quads in 41s at ~1.2 GB. So the walls are a ~25k quads/s
  end-to-end constant and ~1.2 KB of RAM per quad — the 3.1M-quad
  Parliament corpus would need ~4 GB, more than the 2 GB Fly VM.
  Historical note: before #259 the same lifesci query took 137s
  (~135s of Θ(N·B) `bucket_replace_acc` index build; see
  `docs/designissues/2026-05-01-perf-fast-path-vs-load.md`) — if you
  see numbers like that quoted, they predate the fix. Compliance
  numbers say nothing about scale either way: the suites run on tiny
  fixtures.
- **On-disk (COTTAS)**: opens and serves the 3,143,406-quad UK
  Parliament corpus (the Fly.io endpoint + ukparliament demo), but
  the performant search/estimate path is the 718-line unverified
  OCaml override (`cottas_ondisk_runtime.sh`); the extracted F\*
  path is not yet fast enough to replace it. Retirement is scoped in
  `docs/designissues/2026-05-13-issue-118-cottas-ondisk-runtime-retirement-plan.md`
  (#118) with ukparliament-bench gating each step. History of
  soundness bugs in this layer (silent literal-bound-object drops,
  #261, fixed) is exactly why the glue must shrink.
- **HDT**: interface-only in F\*; shells out to the external
  `hdtSearch` CLI per query (#253 retirement plan).
- **OWL-RL closure**: blows up on sameAs clusters
  (`owl_rl_closure_step`, #262, characterised not fixed).

The 2026-05-01 lesson generalises and is worth restating: **a correct
fast path on the wrong layer saves nothing** — profile which *phase*
(read, parse, index-build, eval, format) the time is in before
optimising anything.

## The slowness history (why we care about boundaries)

The Turtle path was once ~40 triples/s with super-linear scaling. The
diagnosis took two passes, and the lesson generalises:

1. **First pass** (`docs/designissues/2026-04-19-turtle-parser-speed.md`)
   blamed the syntactic parser: `nat` positions extracting to `Z.t`
   GMP bignums, eager `span_to_string` materialising a substring per
   token, O(n) list `append` in per-statement folders.
   All real, all fixed (byte-indexed `Parser.FastString`,
   `Parser.TurtleScanner` deferred materialisation).
2. **Second pass** (`docs/designissues/2026-04-24-turtle-parser-perf-diagnosis.md`)
   found the dominant cost was **not in the parser at all**:
   `graph_add`/`mem_triple` dedup-scanned and tail-appended per triple
   — Θ(N²) in `RDF.Graph.Executable`. Bulk-parse prepend +
   one-shot canonicalise fixed it.

Durable lessons: profile before assuming the tokenizer; F\* data
structure and extraction choices (bignum `nat`, list append,
dedup-on-insert) dominate at scale; and the fix belongs in the F\*
architecture, not in OCaml-side patches (see `ocaml-boundary`).
On-disk backends (HDT triples, COTTAS quads) exist because re-parsing
text at scale is the wrong plan regardless of parser speed.

## Observability (per-query timing that's always on)

Every SPARQL query emits three layers (see `docs/observability.md`):

- a fixed-field `[timing]` line on stderr;
- a standards-compatible `Server-Timing` HTTP header
  (with `Timing-Allow-Origin: *`) — "one curl says where the time
  went";
- `/admin/recent.json` — last 50 queries with counters.

Plus `factoidal --explain` dumps the query plan without executing
(`SPARQL.Explain`, `SPARQL.Plan.Explain`). Reach for these before any
ad-hoc profiling.

## Profiling policy

OCaml-level profiling (the `Profile_runtime.ml` pattern, env-gated by
`FACTOIDAL_PROFILE`) is a **temporary post-extraction step only**: it
lives outside the F\* source of truth, must be manually reinserted
after each extraction, and changes the extracted surface. Use it to
locate a hotspot, record findings in a design doc, then remove it
(`docs/ocaml-profiling.md`). Performance fixes land as F\* changes.

## Perf opportunism (standing order)

Every session watches for optimisation opportunities regardless of
its task: a lopsided `Server-Timing` phase, a super-linear loop shape
in code you happen to read, a linear scan where a presence bitmap or
offset index already exists, repeated re-parsing where a canonical
hash (RDFC-1.0) could key a cache. The protocol: don't chase it
mid-task — capture the observation with just enough measurement to be
actionable (one timing, one file:line) in
`docs/claude-rules/current-state.md` § Standing priorities or a
GitHub issue, then finish what you were doing. The wins so far
(#70 byte-indexed parsing, #259 sort-and-group, Lamed3 offset index)
all started as noticed smells, not scheduled work.

## Time discipline for perf work

- Cap every ad-hoc parse/query at 10 minutes (`timeout 600`); if the
  cap trips, kill and shrink the input — don't rerun and hope
  (anti-pattern #17).
- Long benches run in the background, logging to `.claude-runs/` with
  a hard wall-clock cap (#19); checkpoint state to `.claude-worklog.md`
  (#18).
- Don't burn clock on a known-slow path — background it and continue
  (#20, #21).

## Recording results

- Repeatable-fixture numbers → update
  `docs/designissues/turtle-parser-metrics.md` /
  `parser-speed-status.md` with date, binary provenance, and machine.
- Endpoint numbers → the ukparliament baseline files (via the bench,
  not by hand).
- Public-facing perf claims (README, demo pages) must carry a date and
  match a recorded measurement — see `site-and-dashboard`.
- Report in full sentences with units; no unlabelled ratios
  (anti-pattern #25).

## What this skill does NOT cover

- Conformance scores — `test-suites` skill.
- Building binaries — `build-and-test` skill.
- Publishing metrics on the site — `site-and-dashboard` skill.
- Background-job wall-clock discipline in depth —
  `autonomous-time-discipline` skill.
