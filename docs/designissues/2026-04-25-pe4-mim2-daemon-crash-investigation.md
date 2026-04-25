# Pe4 — Mim2 cottas-ondisk daemon mid-walk crash investigation

**Date:** 2026-04-25
**Branch:** `claude/main`
**Parent commit:** `87e9dda` (Mim2 — Phases B+C)
**Time-box:** 45 min
**Scope:** OCaml/glue diagnostics only. **NO F\* changes** — Phase D agent
needs `RDF.CottasStore.fst` untouched.

## Symptom (from Mim2 report)

`factoidal serve --data-cottas <parliament>`:

- `cottas_ondisk_open` completes in ~106s with correct distinct counts
  (s=908,630 / p=232 / o=956,144 / 26 row groups).
- First SPARQL `SELECT (COUNT(*) AS ?n)` triggers `search_fast`, which
  walks the 26 row groups via
  `Parquet_Footer.probe_parquet_column_decode_in_row_group`.
- The daemon process **disappears mid-walk** — no `[qof3-FATAL]`, no
  parse error, no HTTP error reply.

## Hypotheses (ranked)

1. **OOM during `Array.of_list`** of 122k strings × 4 columns, 26 row
   groups in `search_fast` (lines 488–499 of cottas_ondisk_runtime.sh).
   `arr_of_col` materialises every column in every row group as an OCaml
   `string array`. For a 26-rg corpus that is ≥ 12.7M strings live at
   peak. macOS may reap.
2. **Stack overflow** in `Array.of_list` on 122k-element list — but
   `Array.of_list` is implemented iteratively in stdlib, so unlikely.
3. **`failwith` from a parquet probe** (`assume val` body) on some
   row-group-specific malformed encoding. Would print backtrace via
   `Printexc.record_backtrace true` only if the exception escapes —
   `search_fast` has no try/catch around the inner loop.
4. **SIGSEGV / SIGABRT** from the C zstd / parquet stub
   (`parquet_zstd_stubs.c`). No signal handler today.
5. **Cohttp/Lwt worker thread died** with an uncaught exception that
   wasn't logged because flushing was buffered.

## Plan

### A. Verify Qof3's instrumentation is alive in the binary

- `Printexc.record_backtrace true` already at top of
  `factoidal_http_main.ml` (verified line 16).
- `[qof3]` traces around `eval_select_query_backend_dataset` in
  `factoidal_http.ml:932-944` (verified).
- `[qof3-trace] search_fast: rg_count=N` already logs entry; per-rg
  trace is missing — only emits start + total at end.

### B. Add per-row-group instrumentation (Pe4)

Edits to `cottas_ondisk_runtime.sh` AND `RDF_CottasStore.ml` (kept in
sync — `compile` does not re-run patches, so the generated .ml is the
binary's source of truth, but the .sh stays the canonical template per
rule #13).

In `Cottas_ondisk_runtime.search_fast` and `estimate_fast`:

- `[pe4-trace] search_fast rg=N start rss=NN_MB` before each row group.
- `[pe4-trace] search_fast rg=N s_arr=N` after each column decode.
- `[pe4-trace] search_fast rg=N done matches_so_far=N` after inner
  filter loop.
- Wrap the per-rg block in `try ... with e -> [pe4-FATAL] ...` so a
  thrown `failwith` from a probe stub is captured with backtrace
  before the process dies.

Add an RSS helper (shells out to `ps -o rss=` on Unix; cheap, runs
26 times max).

### C. Add SIGSEGV / SIGABRT handler in `factoidal_http_main.ml`

- `Sys.set_signal Sys.sigsegv (Sys.Signal_handle ...)` that prints
  `[pe4-SIGNAL] signo=N` + best-effort `Printexc.print_raw_backtrace`
  and re-raises. macOS won't reliably let us catch SIGSEGV but it is
  cheap to try.

### D. Re-build with `compile` only

Per Mim2 instructions: `./build-ocaml.sh compile` (no `extract`).
~3 min on macOS.

### E. Restart daemon, send one query, capture the LAST trace

```bash
./bin/darwin-arm64/factoidal serve --port 3032 --host 100.107.116.70 \
  --data-cottas tmp/ukparliament/CorpusCOTTAS/ukparliament/v1/data.cottas \
  --web-demo ukparliament --read-only --cors='*' \
  > /tmp/pe4-3032-instrumented.log 2>&1 &
disown
# wait ~106s
curl -sS -m 600 \
  "http://100.107.116.70:3032/sparql?query=SELECT%20%28COUNT%28%2A%29%20AS%20%3Fn%29%20WHERE%20%7B%20%3Fs%20%3Fp%20%3Fo%20%7D"
tail -200 /tmp/pe4-3032-instrumented.log
```

## Findings

(Filled in after instrumentation runs.)

## Recommendation for Phase D

(Filled in after diagnosis.)
