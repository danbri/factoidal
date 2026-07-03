# Performance status and history

Operational guidance for measuring and recording performance lives in
[`skills/perf-benchmarking/SKILL.md`](../../skills/perf-benchmarking/SKILL.md).
This file records where the engine stands and how it got here.

## Current status (measured 2026-07-03)

The Turtle path is no longer the bottleneck it was. Against the
committed `bin/linux-x86_64/factoidal` (`--count`, median of 3, cloud
container):

| N triples | Time | Rate |
|-----------|------|------|
| 1,000 (prefixed) | 0.02 s | ~50k triples/s |
| 1,000 (full-IRI) | 0.04 s | ~25k triples/s |
| 100,000 | 0.93 s | ~108k triples/s |
| 1,000,000 | 9.66 s | ~104k triples/s |

Scaling is near-linear through 1M triples. Re-measure with
`formal/fstar/bench-turtle-metrics.sh` (or the committed binary + the
same fixtures) before quoting these; update this table when you do.

For data at rest, still prefer the binary backends (HDT triples,
COTTAS quads) over re-parsing text — see the caveats in
`docs/designissues/2026-04-19-hdt-fstar-status.md` (the HDT path is
interface-only in F\* and shells out to `hdtSearch`; COTTAS has the
substantial verified `Parquet.Footer` reader).

The walls have moved, not vanished. In-memory: compliant but
RAM-bound, with `indexed_dataset_backend` construction dominating
load time (see `2026-05-01-perf-fast-path-vs-load.md` — ~135s of a
137s demo query was index build). On-disk COTTAS: serves the 3.14M-quad
UK Parliament corpus, but only via the unverified OCaml runtime
override whose retirement is scoped in
`2026-05-13-issue-118-cottas-ondisk-runtime-retirement-plan.md`.
The current-walls summary lives in
[`skills/perf-benchmarking/SKILL.md`](../../skills/perf-benchmarking/SKILL.md)
§ "Scaling status".

## History: the slow-Turtle era (2026-04, fixed)

Measured 2026-04-17, same fixtures: 1,000 triples took 25 s
(~40 triples/s), 10,000 took >8 minutes (killed), 35.8 MB never
finished — super-linear scaling. Two root-cause passes were needed:

1. Parser-side taxes
   (`docs/designissues/2026-04-19-turtle-parser-speed.md`):
   `nat` positions extracting to GMP `Z.t`, eager `span_to_string`
   per token, O(n) list append in the grammar folders.
2. The dominant cost, found later
   (`docs/designissues/2026-04-24-turtle-parser-perf-diagnosis.md`):
   Θ(N²) dedup-scan + tail-append in `graph_add`/`mem_triple` in
   `RDF.Graph.Executable` — not in the parser at all.

Both were fixed in F\* (byte-indexed `Parser.FastString` hot paths,
deferred span materialisation, bulk prepend + one-shot
canonicalisation). The durable lessons — profile before blaming the
tokenizer; F\* data-structure and extraction choices dominate at
scale; fixes land in F\*, not OCaml patches — are captured in the
`perf-benchmarking` skill.

## Standing rules

- Ad-hoc parse/query tests MUST be capped at 10 minutes per rule #17
  (see `anti-patterns.md`).
- Never claim a speed win unless it was measured separately from a
  compliance change.
- Never leave a perf claim in a doc without a date and a binary
  provenance.
