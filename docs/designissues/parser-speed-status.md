# Parser Speed Status

Current status: correctness and measurement have improved, but Turtle-family parsing is still too slow for large ingestion workloads.

## Current parser timing baseline

Measured from the F*-derived CLI path after restoring a clean measurement setup:

- prefixed synthetic Turtle: `4.75s`
- full-IRI synthetic Turtle: `20.97s`
- unicode-heavy synthetic Turtle: `10.25s`
- Berlin slice: `15.93s`

These numbers are good enough to identify the performance regimes, but not good enough for large real-world ingestion.

## Main observations

- Full `<http://...>` IRI parsing is still much worse than prefixed-name-heavy input.
- Berlin-like Turtle remains expensive.
- Unicode-heavy content is slower than ASCII-heavy input, but the main problem is still repeated text scanning and string handling, not Unicode alone.
- The F* scanner-first migration is architecturally correct, but has not yet produced a decisive speed win.

## Current priority order

1. Full-IRI path in Turtle/TriG
2. String scanning and escape handling
3. Reducing substring creation and repeated validation
4. Explicit streaming scanner state and chunk carry
5. Fast ingestion path for N-Quads

## Measurement discipline

- Use `w3c_runner` and `docs/test-results/` for correctness and compliance.
- Use `formal/fstar/bench-turtle-metrics.sh` for parser-speed tracking.
- Do not claim speed wins unless they are measured separately from compliance improvements.
