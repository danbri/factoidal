# Qof3 — Defensive instrumentation for cottas-ondisk first-query crash

Date: 2026-04-25
Agent: Qof3
Scope: diagnostic only — no semantic changes

## The bug being hunted

`./bin/darwin-arm64/factoidal serve --port 3032 --data-cottas
tmp/ukparliament/CorpusCOTTAS/ukparliament/v1/data.cottas` binds the
port (Mim's #99 fix), opens COTTAS in ~5.5s, then dies silently on the
first SPARQL query. Empty reply, no stderr trace, no exception logged.

Likely path: `factoidal_http.ml:run_query → eval_select_query_backend_dataset`
(Kaph2 commit `b958e50`/`e4ea3ca`) → into the cottas-ondisk runtime
(Bet4 PR #101). Some `assume val` body or a runtime helper raises
unhandled.

## Goal

Get a stack trace + first-FATAL line on stderr after the next probe,
so a follow-up agent can plan the F*-first fix.

## Instrumentation plan

1. `factoidal_http_main.ml` — `Printexc.record_backtrace true` at very
   start of `let () = ...` so backtraces are populated for every uncaught
   exception in `run_server`.
2. `factoidal_http.ml`
   - `run_query`: wrap each branch's `S.eval_*_backend_dataset` call in
     `try`, log "calling eval_X" before / "eval_X returned ok N rows"
     after / "eval_X raised: ..." with backtrace on raise, then re-raise.
   - `parse_and_run`: existing `try/with` already exists at line 934 —
     extend it to also log `Printexc.get_backtrace ()` before serialising
     the 500.
   - `handle_connection`: existing `with e -> ...` at line 1986 — add
     `Printexc.get_backtrace ()` to its log line.
   - `run_server`: in the accept loop at ~2129, log every accepted
     connection (peer addr, fd) before handing off to handle_connection
     so we can confirm whether the daemon dies before/during/after.
3. `experimental_ocaml_glue/cottas_ondisk_runtime.sh`
   - Wrap every entry of `search_rows`, `count_rows`, `predicate_present`,
     `encode_*`, `decode_*`, `named_graphs` with a `[trace]` Printf.eprintf.
   - At every `failwith` site in the runtime body, prefix with
     `Printf.eprintf "[FATAL] cottas_ondisk_X: ...\n%!"`.
   - The 13 wrapper functions (`cottas_ondisk_search`, etc.) — log
     `[trace] cottas_ondisk_X invoked` on entry. None of them currently
     have failwith stubs (all 13 are wired by the python dict
     replacements), so no prefix needed there.
4. `build-ocaml.sh` — add `-g` to ocamlopt for `factoidal-http` and
   `factoidal` so backtraces include source line numbers.

## Expected output after redeploy

```
factoidal-http listening on http://127.0.0.1:3032/query
  COTTAS open complete: 1 on-disk file(s), 0 in-memory triple(s) in 5.5s
[accept] 127.0.0.1:NNNNN fd=N
[2026-04-25 ...] POST /query (body=N, accept=...)
[trace] cottas_ondisk_search invoked
[trace] search_rows bound={s=...; p=...; o=...; g=...}
[FATAL] cottas_ondisk_X: ...   <-- this is what we want
  connection error: Failure(...)
  backtrace:
   Raised at ...
   Called from ...
```

Or — if a wrapper like `cottas_ondisk_summary` is the one being hit:

```
[trace] cottas_ondisk_summary invoked
```

Then we know which assume-val site has incorrect runtime behaviour.

## Constraints honoured

- Diagnostic only (no semantic logic).
- No F\* edits.
- Single commit on `claude/main`.
- Final commit message:
  `factoidal-http: defensive instrumentation for cottas-ondisk query crash`
