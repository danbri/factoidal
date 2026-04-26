# Heth3 — per-query wall-clock timeout in factoidal-http

**Date**: 2026-04-26  **Agent**: Heth3  **Scope**: `formal/fstar/ocaml-output/factoidal_http.ml`

## Problem

A single slow query (e.g. unbound BGP `SELECT * WHERE { ?s ?p ?o }` against the
COTTAS on-disk parliament corpus walking 26 row groups) blocks the
single-threaded HTTP accept loop for minutes, queuing every subsequent
request behind it. Observed: 24 modern parliament queries stacked and
timed out at curl level.

## Approach chosen: `Unix.alarm` + `Sys.sigalrm`

The prompt suggested Lwt.pick / Lwt_preemptive.detach as the primary
option. **Inspecting the code, factoidal_http.ml is NOT Lwt/cohttp** — it
is a vanilla `Unix.accept` loop driving synchronous OCaml. Linking
against Lwt would mean a substantial rewrite (and a new opam dep) for a
modest feature. The prompt explicitly allows the simpler alternative:
"run the query inside a `Unix.alarm` with a SIGALRM handler that raises
an exception. Less Lwt-y but kills the synchronous OCaml."

Mechanics:
- `Sys.set_signal Sys.sigalrm` to a handler that raises `Query_timeout`.
- `Unix.alarm cfg.query_timeout` immediately before `parse_and_run`.
- `Unix.alarm 0` in a `Fun.protect ~finally` to guarantee the timer is
  cancelled on every exit path (success, parse error, evaluator
  exception).
- `try ... with Query_timeout -> { rb_status = 504; ... }` builds the
  HTTP 504 response. The accept loop then closes the socket and loops
  back to `Unix.accept`, freeing the worker.
- `cfg.query_timeout = 0` skips both `set_signal` and `alarm` entirely
  (infinite, matches the user-facing "0 = disabled" semantics).

## Caveats / known trade-offs

- `Unix.alarm` is **process-global**. The HTTP server is single-threaded
  (or one accept-thread when COTTAS is loading) so this is fine today.
  When we eventually move to a worker pool, this becomes per-process
  rather than per-request and we'll need to revisit (probably with a
  per-thread polling abort flag wired into the BGP loop).
- The signal handler raises out of whatever OCaml stack frame happened
  to be running. The F\*-extracted evaluator is mostly pure functional
  code, but a few patches (e.g. cottas-ondisk readers) hold mmap
  resources via `Bigarray`/`Unix.LargeFile` — these clean up via GC
  finalisers, not `try/finally`, so a SIGALRM mid-read leaks no
  filesystem state. Cohttp/Lwt-style "leaked detached thread" is not a
  concern here because we genuinely *do* unwind the stack.
- SIGALRM races with our SIGTERM/SIGINT handlers are benign: those use
  `Sys.Signal_handle` and OCaml serialises signal delivery between
  safepoints.
- `--query-timeout 0` (disabled) is a foot-gun — documented in
  `--help`.

## CLI surface

```
--query-timeout SECS   Per-query wall-clock budget. SIGALRM raises Query_timeout
                       in the evaluator; the handler returns HTTP 504.
                       0 = disabled (infinite). Default: 30.
```

## 504 response body

```json
{"error":"query_timeout","seconds":30,"hint":"Add LIMIT or bind more triple-pattern terms."}
```

Mirrors the existing 413 result-cap response shape.

## Smoke plan

1. `dune build` (or `ocamlopt` per `build-ocaml.sh`) factoidal-http.
2. Start with `--query-timeout 5` against parliament corpus.
3. `curl 'http://127.0.0.1:3030/query?query=SELECT+*+WHERE+{?s+?p+?o}'`
   → expect HTTP 504 in ~5s.
4. Immediately `curl '...query=SELECT+(COUNT(*)+AS+?n)+WHERE+{...}'`
   → expect 200 in <100ms.
5. Verify W3C suite still 1657/1/0/4 (alarm semantics shouldn't affect
   tests that complete sub-second).
