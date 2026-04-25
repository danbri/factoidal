# 2026-04-25 — UK Parliament SPARQL Query Bench Harness

Agent: Vau
Date: 2026-04-25
Branch: claude/main

## Goal

Build a lightweight benchmark harness that runs the 24 vendored UK Parliament
sample SPARQL queries (`third_party/data/ukparliament/sparql/{main,detail}/*.rq`)
against the factoidal-http endpoint at `http://100.107.116.70:3030/sparql`,
records wallclock + result-row counts, and emits both CSV and JSON reports.

Per CLAUDE.md rules #1, #5, #15: this is *pure tooling*. No semantic logic in
the harness; we are only timing HTTP round-trips against an existing endpoint.

## Inputs

- `third_party/data/ukparliament/sparql/main/*.rq` (11 files)
- `third_party/data/ukparliament/sparql/detail/*.rq` (13 files)
- Endpoint: `http://100.107.116.70:3030/sparql` (read-only, CORS open).
  Loading started ~06:25; expected ready ~06:35.

Note: the original task description said "14 + 10 = 24". On disk it is
"11 + 13 = 24". Same total.

## Plan

1. `tools/bench_ukpar_queries.py` — Python 3 stdlib only (no deps).
2. Discover every `.rq` recursively under the sparql dir.
3. For each query:
   - HTTP POST `Content-Type: application/sparql-query`,
     `Accept: application/sparql-results+json`.
   - Wallclock time the request (`time.perf_counter`).
   - Parse JSON response: count `results.bindings` for SELECT,
     `boolean` for ASK. Capture HTTP status, error body on non-200.
   - Per-query timeout cap: 60s. Mark as TIMEOUT and continue.
4. Endpoint health-check loop at start: GET `?query=ASK%20%7B%7D` (or POST
   `ASK {}`). Retry every 10s up to 5 minutes. If still down, write a doc
   note and exit non-zero — don't waste budget.
5. Writes:
   - `docs/test-results/ukparliament-bench.csv`
   - `docs/test-results/ukparliament-bench.json`
6. Print summary: `24 queries: N OK, M error, total wallclock X seconds, slowest = Q`.

## Out of scope

- No SPARQL UPDATE — endpoint is read-only.
- No mutation of `formal/fstar/*.fst`, no edits to `w3c_runner.ml`.
- Optional integration into `generate-report.sh` is a stretch; main
  deliverable is the harness + CSV/JSON.

## Hard limits

- 60 min wall-clock total budget.
- Per-query timeout 60s.
- Endpoint unreachable for 5 min ⇒ doc + abort.
