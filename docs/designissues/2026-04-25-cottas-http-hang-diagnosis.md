# 2026-04-25 — factoidal-http --data-cottas hang diagnosis (Agent Zayin2)

## Symptom

`factoidal-http --data-cottas <file>` hangs forever (2:38 CPU, 44 KB RSS,
never reaches `LISTEN`), while `factoidal --data-cottas <file>` works
(after Cottas-Perf's bulk decode landed in 9378d52).

## Investigation in flight

1. Confirm CLI fast on the 3.14 M-quad UK Parliament corpus (62 MB
   COTTAS).
2. Reproduce HTTP hang with a fresh `factoidal-http` invocation on
   port 3033 (avoid 3030 which has the working N-Quads endpoint).
3. Compare argv parsing, `load_dataset`, and `load_cottas_dataset` in
   both binaries — both call `Parser_BallyhooCOTTAS.cottas_open_dataset_store`
   which (after Cottas-Perf) goes through the bulk per-column decode
   path in `experimental_ocaml_glue/cottas_runtime.sh:271-320`.

## First obvious finding

`bin/darwin-arm64/factoidal-http` is locally modified (uncommitted)
relative to `2465c11`. The local change may be Daleth2's `--data-cottas`
wiring (also rolled into 2465c11). Need to confirm both binaries were
linked against the same Cottas-Perf-fixed `Parquet_Footer.ml` and
`Parser_BallyhooCOTTAS.ml`.

## Plan

- Time the CLI: `factoidal --data-cottas data.cottas --count` with
  `/usr/bin/time -l`. Confirm < 60 s.
- Launch HTTP on port 3033, watch process RSS and check if it reaches
  LISTEN.
- If HTTP hangs, run `sample` against the OCaml process to compare hot
  frames against CLI.
- Diff the two `load_cottas_dataset` definitions textually.

## Hard limits

- ≤ 100 LoC change (per session brief).
- Don't touch the F\* COTTAS reader.
- Don't kill the live `factoidal-http` on port 3030 (only working
  endpoint).
