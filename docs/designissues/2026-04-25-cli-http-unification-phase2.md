# Phase 2: collapse `factoidal-http` into `factoidal serve` (Tet3)

Date: 2026-04-25
Owner: Agent Tet3
Predecessor: `42759c5` (Bet3 Phase 0/1 plan + exec-shim).
Coordination: Heth2 is concurrently refactoring the landing-page area of
`factoidal_http.ml` (web_demo flag, removal of inline HTML). Tet3's edits
must NOT touch `landing_page_html`, `try_static_route`, the `web_demo`
config field, or the request-handling logic. Scope: argv parsing + module
boundary + `let () = ...` only.

## Problem

After Bet3 Phase 1, `factoidal serve …` is a thin shim that does
`Unix.execvp "factoidal-http" …`. That works, but:

1. Two binaries on disk; users still see `factoidal-http` as a
   separate first-class entry point.
2. Argv-parser duplication: `factoidal_http.ml :: parse_args ()` reads
   `Sys.argv` directly, so the CLI can't share or pre-process the args.
3. The user explicitly asked for `factoidal-http` to be "just an alias for
   factoidal plus some args" — the exec shim doesn't get there.

## Target shape

```
factoidal_http.ml
  ├── argv parser (parse_args ?args () : config)   ← same code, now takes optional args
  ├── load_dataset, load_rdf_dataset, load_cottas_dataset
  ├── handle_connection, run_server cfg            ← unchanged
  └── (no top-level `let () = ...`)

factoidal_http_main.ml   ← new, ~5 lines
  let () =
    let cfg = Factoidal_http.parse_args () in
    if cfg.help_mode then (Factoidal_http.usage (); exit 0);
    Factoidal_http.run_server cfg

factoidal_cli.ml
  serve handler:
    let cfg = Factoidal_http.parse_args ~args:rest () in
    if cfg.help_mode then (Factoidal_http.usage (); exit 0);
    Factoidal_http.run_server cfg
  (no exec, in-process)

build-ocaml.sh
  factoidal-http binary  = COMMON_MODULES + factoidal_http.ml + factoidal_http_main.ml
  factoidal binary       = COMMON_MODULES + factoidal_http.ml + factoidal_cli.ml
```

`factoidal-http` stays as a 5-line wrapper for backward compat with
anything that scripts the binary path (Bet3 plan option (b)).

## What changes

1. `factoidal_http.ml`:
   - `parse_args ()` → `parse_args ?args ()`. Default `args` resolves
     to `Array.to_list Sys.argv |> List.tl` (same as today). Caller in
     `factoidal_cli.ml` passes the post-`serve` argv tail.
   - Remove the trailing `let () = ...` block (4 lines). Move it into
     a new file.
2. New file `factoidal_http_main.ml` (~5 lines) — calls
   `Factoidal_http.parse_args () |> ... |> run_server`.
3. `factoidal_cli.ml`:
   - Replace `exec_sibling "factoidal-http" rest` in the `serve`
     handler with `let cfg = Factoidal_http.parse_args ~args:rest ()
     in Factoidal_http.run_server cfg`. Exit 0 not needed — run_server
     loops forever.
   - Implement `cottas-info FILE`: open via `Parser_BallyhooCOTTAS`,
     print `{file, triples, distinct subjects, distinct predicates,
     distinct objects, named graphs}`. Reuse the cache walk from
     `load_cottas_dataset` already in factoidal_cli.ml.
4. `build-ocaml.sh`:
   - Compile `factoidal-http` from
     `COMMON_MODULES factoidal_http.ml factoidal_http_main.ml`.
   - Compile `factoidal` from
     `COMMON_MODULES factoidal_http.ml factoidal_cli.ml`.
   - Order matters (ocamlfind needs the dependency first).

## Risks

- **Build failure on Heth2's diff.** If Heth2 commits parse_args edits
  with a clashing signature, fix forward — they're additive flag
  handlers, not signature touches.
- **Browser bundle.** factoidal_cli is also js_of_ocaml-built. Linking
  factoidal_http.ml in would drag Unix.* into the JS build, which fails.
  **Decision: factoidal_cli serve subcommand is gated on a build-time
  module presence check; the JS bundle keeps the old exec shim
  (no-op-on-Web).** Simpler fix for now: only link factoidal_http.ml
  into the *native* factoidal binary, leave the JS bundle's serve
  handler as a stub that prints "serve is native-only".
- **Running 3030 endpoint.** Don't take it down. After rebuild, the
  user can ctrl-c + relaunch.
- **Heth2 conflict on parse_args.** The optional ?args parameter
  doesn't move existing code, just adds a default arg before the
  body. Heth2's pattern-match additions land cleanly.

## Hard limits

- ≤ 200 LoC net change.
- No `.fst` edits.
- Don't break the running 3030 endpoint.
- Both `factoidal serve …` and `factoidal-http …` must work after.

## Out of scope (Phase 3)

- Drop `factoidal-http` binary entirely; replace with argv[0]-dispatch
  symlink (busybox style).
- Same for `w3c_runner`, `owl_runner`, `rdfc10_runner`.
- Move `factoidal_http`'s argv parsing into a shared dispatcher with
  the CLI's parse_args (subcommand-aware).
