## Turtle Parser Metrics

> **Related plan (2026-04-19):**
> [`2026-04-19-turtle-parser-speed.md`](2026-04-19-turtle-parser-speed.md) —
> audit of the three structural bottlenecks (`nat`→`Z.t` positions,
> eager `span_to_string` extraction, O(n) list appends in the grammar)
> and a phased plan to close the ~250× gap to usable rates. These
> metrics are the baseline that plan benchmarks against.

This note records the current repeatable benchmark path for Turtle parser work that is being driven from F* changes rather than OCaml-only experiments.

### Fixture Set

The current baseline uses four small fixtures generated or sliced by `formal/fstar/bench-turtle-metrics.sh`:

- `prefixed-1000.ttl`
  prefixed-name-heavy ASCII triples
- `fulliri-1000.ttl`
  full `<http://...>` IRI triples
- `unicode-1000.ttl`
  prefixed triples with non-ASCII literal text
- `berlin-1000.ttl`
  first 1000 lines of `examples/data/third_party/Berlin.ttl` when present

The point of this set is not standards coverage. It is to separate the measured performance regimes that have already shown up in investigation:

- prefixed-name-heavy Turtle
- full-IRI-heavy Turtle
- non-ASCII content
- a more realistic Berlin slice

### How To Run

From `formal/fstar/`:

```bash
./bench-turtle-metrics.sh
```

This script:

1. regenerates the benchmark fixtures in `/tmp/factoidal-metrics`
2. rebuilds `ocaml-output/factoidal` directly from the extracted OCaml
3. runs `factoidal --count` on each fixture under `/usr/bin/time`
4. repeats each fixture `RUNS` times and reports median/min/max wall time

Example:

```bash
RUNS=5 ./bench-turtle-metrics.sh
```

It avoids the current `w3c_runner` build issue in `build-ocaml.sh compile`, which is unrelated to Turtle benchmarking.

### Current Baseline

After the scanner-first Turtle changes plus the F* change that replaced `string_contains_colon` list allocation with indexed traversal, representative single-run timings were:

- `prefixed-1000.ttl`: `4.11s`, `7200 KB`
- `fulliri-1000.ttl`: `19.35s`, `7360 KB`
- `unicode-1000.ttl`: `8.19s`, `7200 KB`
- `berlin-1000.ttl`: `14.37s`, `7360 KB`, `993 triples`

An earlier baseline from the same measurement path was:

- `prefixed-1000.ttl`: `4.67s`
- `fulliri-1000.ttl`: `23.31s`
- `unicode-1000.ttl`: `9.33s`
- `berlin-1000.ttl`: `16.15s`

Those numbers were enough to confirm direction, but there is visible run-to-run noise. The benchmark script now supports repeated runs and should be used for any claim stronger than "roughly better" or "roughly worse".

### Interpretation

The current measurements still show two distinct expensive regimes:

- full-IRI-heavy input is worst
- Berlin-like data remains substantially more expensive than the simple prefixed case

That keeps the architectural conclusion unchanged:

- scanner-first refactoring in F* is the right direction
- full-IRI handling still needs more work
- non-ASCII handling is slower than pure ASCII, but currently not exploding disproportionately on this small benchmark
