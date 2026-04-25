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

### Diagnosis: STACK OVERFLOW in worker thread on `sum_nat_list`

The daemon dies via **SIGBUS** (`KERN_PROTECTION_FAILURE`) hitting the
**stack guard page** of the cohttp accept-loop worker thread, not main.

**Evidence — macOS crash report**
`~/Library/Logs/DiagnosticReports/factoidal-2026-04-25-233112.ips`:

```
exception:
  type    = EXC_BAD_ACCESS
  signal  = SIGBUS
  subtype = KERN_PROTECTION_FAILURE at 0x000000016b293ff8
  rawCodes = [2, 6092832760]   (code 2 = KERN_PROTECTION_FAILURE)

vmRegionInfo:
  0x16b293ff8 is in 0x16b290000-0x16b294000;
  STACK GUARD 16b290000-16b294000 [16K] ---/rwx for thread 1
  Stack       16b294000-16b31c000 [544K] rw-/rwx thread 1

faultingThread: 1 (NOT main; main was sleeping in unix_sleep)
faultingFrames (deepest first):
  camlParquet_Footer__sum_nat_list_3087   imageOffset 945028  symLoc 4
  camlParquet_Footer__sum_nat_list_3087   imageOffset 945100  symLoc 76
  caml_callback_exn                        callback.c:111
  caml_thread_start                        st_stubs.c:549
  _pthread_start
```

The two adjacent `sum_nat_list_3087` frames (symLoc 4 and 76) are the
recursion frame and its return-PC entry — i.e. the symbol writes into
its caller frame's slot just past the live stack and trips the
**stack guard page**. Classic non-tail-rec stack overflow.

**The bug.** `Parquet_Footer.ml` line 2886:

```ocaml
let rec sum_nat_list (xs : Prims.nat Prims.list) : Prims.nat =
  match xs with
  | [] -> Prims.int_zero
  | hd :: tl -> hd + (sum_nat_list tl)
```

The `hd + (sum_nat_list tl)` form is **NOT tail-recursive** — Z.add
is called on the result of the recursive call, so each level
allocates a stack frame. The `lengths` list passed to `sum_nat_list`
in `probe_parquet_column_delta_length_byte_array_decode_all_in_row_group`
is the per-row-group string-length list. For the parliament corpus
each row group has ~120,894 entries (3,143,406 ÷ 26). That's
~120k frames × ~128 bytes = ~15 MB of stack — well past the macOS
**worker pthread stack of 544 KB**.

The crash trace `[pe4-trace] search_fast rg=0 enter rss=1481MB`
followed by silence is consistent: the very first call to
`probe_parquet_column_decode_in_row_group path 0 0` dispatches into
the DLBA path which runs `sum_nat_list lengths`, recursing 120k deep
and blowing the guard page mid-recursion.

**Why open() succeeds but query() dies.** `cottas_ondisk_open` runs
on the **main thread** (default 8 MB stack on macOS arm64), so the
same `sum_nat_list` recursion fits. The accept-loop worker (created
in `factoidal_http.ml run_server` via `Thread.create accept_loop ()`)
inherits the macOS pthread default of 512 KB + a 16 KB guard. That's
where `search_fast` runs — and it dies on the very first row group.

**Why the SIGNAL handler did not fire.** `Sys.set_signal Sys.sigabrt`
etc. installs OCaml runtime handlers, but SIGBUS / SIGSEGV from a
stack-guard hit on a worker pthread is delivered to the offending
thread; the OCaml runtime cannot reliably dispatch it through the
masked-signal queue and the thread is killed by the kernel before
the handler can flush. Hence the silent disappearance.

### Last trace line + system state

- **Last [qof3-trace]**: `search_fast: rg_count=26`
- **Last [pe4-trace]**: `search_fast rg=0 enter rss=1481MB heap=1501MB matches=0`
- **Iteration**: row-group 0, column 0 (subject), inside the first
  `probe_parquet_column_decode_in_row_group` call, depth ~120k inside
  `sum_nat_list` over the per-rg DLBA length list.
- **RSS at death**: ~1.4–1.5 GB (mostly `coh_subjects/_predicates/_objects`
  parsed term lists + `__mim2_file_bytes_cache` 63 MB byte slurp).
- **Stack region at fault**: thread 1 (worker) stack guard page
  (16K guard + 544K live stack).

## Recommendation for Phase D

Phase D should **NOT** rely on column-prune alone to dodge this.
Even reading just one column still triggers `sum_nat_list` over the
column's per-row-group lengths list. The daemon will die identically.

**Real fix** (F\* change, ineligible for Pe4 scope):

In `Parquet.Footer.fst`, rewrite `sum_nat_list` with an explicit
accumulator so OCaml extracts a tail call:

```fstar
let rec sum_nat_list_acc (xs : list nat) (acc : nat) : Tot nat (decreases xs) =
  match xs with
  | [] -> acc
  | hd :: tl -> sum_nat_list_acc tl (hd + acc)

let sum_nat_list (xs : list nat) : nat = sum_nat_list_acc xs 0
```

This is the same pattern as patch #95 (`stack_safe_list_ops`) that
already covers `concatMap` / `op_At` etc. in `SPARQL11.Algebra.fst`.
Either:

1. Land this directly in `Parquet.Footer.fst` (1-line spec change,
   verifies the same — `sum_nat_list xs == fold_left (+) 0 xs`).
2. OR temporarily extend patch #95's stack-safe rewriter to also
   transform `Parquet_Footer__sum_nat_list_3087` post-extraction
   (less preferred — F\* is the source of truth).

The Phase D agent (tsade2) should grep `Parquet_Footer.ml` for any
other `let rec` doing `f hd (recurse tl)` patterns — especially
`build_dlba_length_list` (line 2795) and `decode_plain_dictionary_entries`
(3301) and `map_indices_to_dict` (3433). These are all candidates for
the same overflow if Phase D moves any of them onto the worker thread.

**Workaround for the immediate daemon while F\* fix lands**: bump the
worker-thread pthread stack size in `factoidal_http.ml run_server`:

```ocaml
(* before Thread.create accept_loop *)
let _ = Thread.create
  ~stacksize:(8 * 1024 * 1024)   (* match main thread *)
  accept_loop () in
```

OCaml's `Thread.create` does not expose `~stacksize`, so the workaround
needs `pthread_attr_setstacksize` in a tiny C stub. Or simpler: do the
COTTAS query work synchronously on the main thread (8MB stack already)
by moving `search_fast` invocation to the request thread that also
calls `accept`. This conflicts with the existing
"single accept loop, work on accept thread" design but both paths
already share the request handler.

## Pe4 deliverables

1. Per-row-group `[pe4-trace]` instrumentation in `search_fast` and
   `estimate_fast` (RSS / heap / fd / matches at every column decode +
   filter-loop boundary). Lives in
   `experimental_ocaml_glue/cottas_ondisk_runtime.sh` (canonical
   template) and the patched `ocaml-output/RDF_CottasStore.ml`.
2. SIGABRT/SIGPIPE/SIGTERM handlers in `factoidal_http_main.ml` AND
   `factoidal_cli.ml` (the `serve` subcommand path missed Qof3's
   handlers — addressed here).
3. This diagnosis doc.

The `[pe4-FATAL]` try/with around each row-group also did not fire,
confirming the kill was uncatchable kernel-delivered SIGBUS, not an
OCaml exception.
