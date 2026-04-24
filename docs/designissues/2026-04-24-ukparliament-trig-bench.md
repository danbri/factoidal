# 2026-04-24 UK Parliament TriG benchmark (Agent Alpha)

## Goal

Benchmark the F\*-extracted Turtle/TriG parser against
`third_party/data/ukparliament/ukparliament-rdf-2019-07-27.trig`
(331 MB, single large TriG file) to establish whether the file is
tractable today and, if not, locate the bottleneck.

## Constraints

- Rule #17: 10-min hard cap per run, enforced with `perl -e 'alarm N; exec @ARGV'`
  since macOS lacks `timeout`.
- Rule #20: TriG is the known-slow path — do NOT hold the main loop on it.
- No edits to `.fst` / `ocaml-output/*.ml`.
- No `./build-ocaml.sh extract` / `compile` (main thread is rebuilding).
- Total wall-clock budget 30 min.

## Pre-check (done)

- File: 331 MB (`ukparliament-rdf-2019-07-27.trig`), header is conventional
  `@prefix` Turtle syntax (schema.org, parliament schema, wgs84, owl, ...).
- External RDF tools available on this mac:
  - `rapper`: NOT FOUND
  - `serd` / `serdi`: NOT FOUND
  - `riot` (Jena): NOT FOUND
  - `arq`: NOT FOUND
  - `raptor`: NOT FOUND
  - ==> N-Quads conversion fallback via external tool is **unavailable**.
  - `timeout`: NOT FOUND (expected on macOS); use `perl -e 'alarm N; exec'`.
  - `perl`, `/usr/bin/time -lp`: available.
- Binary: `./bin/darwin-arm64/factoidal` supports `--count --data FILE`
  with auto-detected TriG format from `.trig` extension.

## Plan

1. Slice the file with `head -c` at 1M, 10M, 50M. For each slice:
   - `/usr/bin/time -lp perl -e 'alarm 300; exec @ARGV' -- \
      ./bin/darwin-arm64/factoidal --count --data /tmp/uk-slice-XXM.trig`
   - Capture wallclock, RSS, triple count.
2. Fit the scaling curve. If linear and cheap (< 2 min for 50M) attempt
   the full file once with a 300 s cap. If obviously super-linear, stop
   and report.
3. `head -c` can cut mid-statement; this still measures parser throughput
   on representative prefixes. For the 1M slice we'll also try a
   line-boundary cut via `head -n` to rule out cut-artifact anomalies.

## Expected outcomes

Based on `2026-04-20-turtle-parser-profile.md` + `2026-04-23-tail-recursion-audit.md`,
the current Turtle/TriG path is suspected O(n²) or worse due to non-tail-rec
accumulation. If so, 50 M chunk will already blow past 5 min and the full
331 M file is untractable without the planned tail-rec rewrite.

## Scratch slot for results

Filled in after runs complete. If tractable, note triple count + memory.
If not, report the scaling curve and fall-through recommendation.
