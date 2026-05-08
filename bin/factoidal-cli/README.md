# bin/factoidal-cli — `factoidal` CLI entry point

Hand-written OCaml entry point (`let () = ...`) for the
`factoidal` command-line tool. Parses argv, dispatches to
subcommand modules:

- `factoidal query` — SPARQL query execution
- `factoidal parse` — RDF format → N-Quads dump
- `factoidal --explain` — plan-tree rendering (via `Factoidal_explain`)
- `factoidal serve` — start the HTTP server (via `Factoidal_serve`)
- `factoidal validate` — RDFC-1.0 canonicalisation smoke (via
  `RDF_Canonical`)

Output: `bin/<platform>/factoidal` (native) and `bin/<platform>/
factoidal.byte` (debug bytecode); `factoidal.js` (browser).

## Why the source lives here, not in `formal/fstar/ocaml-output/`

Per CLAUDE.md iron rule #11, hand-written consumer-side OCaml does
not belong in `formal/fstar/ocaml-output/` — that directory is
reserved for F\*-extracted output and `assume val` glue patches.
This is the entry-point module of a CLI consumer, so it lives
under `bin/<consumer>/` per the migration epic
[#200](https://github.com/danbri/factoidal/issues/200) Section D.

The built binary still lands at `bin/<platform>/factoidal` — same
path as before; only the source moved.

## Build

`build-ocaml.sh compile` for native, `build-ocaml.sh js` for the
JS bundle, `build-ocaml-debug.sh factoidal` for the debug
bytecode. All three reference this file via the relative path
`../../../bin/factoidal-cli/factoidal_cli.ml` from the
`formal/fstar/ocaml-output/` cwd.

This module is the LAST in the link order (entry point), so no
`-I` flag is needed — nothing imports it.

## Cross-references

- Migration epic: [#200](https://github.com/danbri/factoidal/issues/200) Section D
- Pattern reference: `bin/factoidal-explain/README.md`,
  `bin/factoidal-serve/README.md`
