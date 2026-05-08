# bin/factoidal-serve — `factoidal serve` subcommand glue

Three OCaml source files implementing the `Factoidal_serve` module —
the consumer-side glue that the `factoidal` CLI calls when invoked
as `factoidal serve …`. All three files compile to the same OCaml
module name (`Factoidal_serve`); the build picks one at compile time
depending on the target.

## Files

- `factoidal_serve.ml` (20 LoC) — production native build. Forks an
  in-process HTTP server via `Factoidal_http.run_server`. Linked by
  the native `factoidal` CLI build.
- `factoidal_serve_debug.ml` (17 LoC) — debug bytecode build
  (`build-ocaml-debug.sh factoidal`). Same surface, with
  diagnostic logging instrumented for the
  `factoidal.byte` debug binary.
- `factoidal_serve_jsoo.ml` — JS bundle build. Errors at runtime if
  `serve` is invoked under js_of_ocaml (the JS bundle has no
  Unix.bind). Same module signature as the native variant so the
  rest of the CLI compiles.

## Why the source lives here, not in `formal/fstar/ocaml-output/`

Per CLAUDE.md iron rule #11, hand-written consumer-side OCaml does
not belong in `formal/fstar/ocaml-output/` — that directory is
reserved for F\*-extracted output and `assume val` glue patches.
This module is a consumer of `Factoidal_http`, so it lives under
`bin/<consumer>/` per the migration epic
[#200](https://github.com/danbri/factoidal/issues/200) Section D.

The built binaries still land at `bin/<platform>/factoidal` (and
`factoidal.byte`, `factoidal.js`) — same paths as before; only the
sources moved.

## Build

The native `factoidal` binary build (`build-ocaml.sh compile`) and
the JS build reference these files via the relative path
`../../../bin/factoidal-serve/...` from `formal/fstar/ocaml-output/`.

The debug build (`build-ocaml-debug.sh factoidal`) and the JS build
both stage one of the variants as `factoidal_serve.ml` in cwd at
build time (so the OCaml module name resolves correctly), then
clean up. See the inline `Phase 8 (#200 D)` comments in each script
for details.

## Cross-references

- Migration epic: [#200](https://github.com/danbri/factoidal/issues/200) Section D
- Pattern reference: `bin/cottas-ondisk-smoketest/README.md`,
  `bin/factoidal-dump-nq/README.md`
