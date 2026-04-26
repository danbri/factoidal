# Tav5 — SIGBUS circuit breaker + tail-rec hunt (2026-04-26)

## Context

Daemon `factoidal-http` SIGBUSes (signal 10 / EXC_BAD_ACCESS at thread 1
stack guard) when SPARQL queries materialise the full ~3.14M-quad UK
parliament corpus before joining/filtering. Three crash dumps today
(08:32:55, 08:59:22, ...) all show 544 KB pthread default stack
exhausted by deeply recursive list walks in the response/marshalling
path. Het3's commit `b5396fc` already fixed the first offender
(`Parquet.Footer.sum_nat_list`); other non-tail-rec list walks remain.

## Plan (2-hour box)

1. **Circuit breaker (must-ship)** — Add a per-query result-cardinality
   cap in `formal/fstar/ocaml-output/factoidal_http.ml`. Default 50 000
   rows, configurable via `--max-rows N` CLI flag, `--max-rows 0`
   disables. When exceeded, return HTTP 413 with JSON error body and
   stderr trace `[tav5-trace] result-cap exceeded ...`. Check happens
   right after the BGP/algebra evaluator returns its solution sequence
   and before the JSON serialiser sees it (since the serialiser is
   where the stack overflow tips).

2. **Tail-rec offender hunt (best-effort)** — Disable cap, re-run the
   geosparql trigger, grep for the same `let rec ... | hd :: tl -> hd OP f tl`
   pattern in the SPARQL solution-sequence / JSON marshalling path.
   If a clear offender appears, rewrite to accumulator-pattern in F\*.
   `make verify` only — do NOT run `./build-ocaml.sh extract` (8-10 min,
   stalls watchdog). Main thread will re-extract.

## Smoke checks

- Demo path (`?s rdf:type ?o LIMIT 5`) returns 200 in <2 s.
- Trigger query returns 413 with the JSON body, daemon stays alive.
- W3C `--all` stays 1657/1/0/4.

## Hard rules

- No `build-ocaml.sh extract`. `./build-ocaml.sh compile` only (no dune;
  the script invokes `ocamlfind ocamlopt` directly per
  `formal/fstar/build-ocaml.sh`).
- No push. Commit on `claude/main` locally; main thread pushes.
- F\*-first: tail-rec rewrite goes in `.fst`, not OCaml patches.
