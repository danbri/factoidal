# bin/factoidal-http — SPARQL 1.1 Protocol HTTP server

Hand-written OCaml module implementing the `Factoidal_http` module
plus its `factoidal-http` standalone-binary entry point.

## Files

- `factoidal_http.ml` (2598 LoC) — main library: bind/listen,
  request parsing, dispatch into the F\*-extracted SPARQL engine
  (`SPARQL11_Algebra` / `SPARQL_Protocol` / `SPARQL_HTTP*` /
  `SPARQL_Query_Analysis` / `SPARQL_Update_Analysis` /
  `SPARQL_Eval_TimeBudget` / `SPARQL_Eval_Limits` / etc.),
  response framing, threading, error handling, signal handlers.
  Linked into both the `factoidal` CLI binary (called via
  `Factoidal_serve.start_with_args`) and the `factoidal-http`
  stand-alone binary.
- `factoidal_http_main.ml` — 5-line `let () = ...` wrapper around
  `Factoidal_http.run_server` for the stand-alone
  `bin/<platform>/factoidal-http` binary. Kept as a separate
  binary for backward compat with anything that scripts the path.

## Why the source lives here, not in `formal/fstar/ocaml-output/`

Per CLAUDE.md iron rule #11, hand-written consumer-side OCaml does
not belong in `formal/fstar/ocaml-output/` — that directory is
reserved for F\*-extracted output and `assume val` glue patches.
This is the HTTP I/O layer; per rule #11(c) "pure I/O (file/clock/
socket)" is acceptable consumer-side glue.

## Future semantic split (#200 D follow-up)

The 2598 LoC includes some logic that *could* migrate further into
F\* — request URL parsing, query-string decoding, response-format
selection. That migration is a follow-up — moving the file out of
the verified library boundary is a strict improvement either way
(per rule #11), and any subsequent F\* migration just shrinks this
module further.

The Heth3 timeout work (#211, `SPARQL.Eval.TimeBudget.fst` +
`202_now_ms.sh` glue) already moved the per-query
cooperative-cancellation core into F\*; this module just calls it.
The bs_json / tp_explain / kind_label work (#170 / #173) similarly
moved response-rendering helpers into F\*-extracted code.

## Build

`build-ocaml.sh compile` for native (links into `bin/<platform>/
factoidal` and `bin/<platform>/factoidal-http`); `build-ocaml-
debug.sh factoidal-http` for the debug bytecode build.

`-I ../../../bin/factoidal-http` is passed at compile time so
ocamlfind can resolve `Factoidal_http.<x>` cmi from later modules
(factoidal_serve / factoidal_cli call into it).

## Cross-references

- Migration epic: [#200](https://github.com/danbri/factoidal/issues/200) Section D
- Heth3 retirement: #211 (TimeBudget moved to F\*)
- bs_json / tp_explain / tpx_json: #170 (response renderers moved
  to F\*)
- kind_label / is_test_type_iri: #173 (label rendering moved to F\*)
- Pattern reference: `bin/factoidal-cli/README.md`,
  `bin/factoidal-serve/README.md`, `bin/factoidal-explain/README.md`
