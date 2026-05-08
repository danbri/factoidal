# bin/factoidal-explain — `factoidal explain` subcommand

OCaml module implementing the `Factoidal_explain` module — provides
the SPARQL plan-explanation rendering used by `factoidal --explain`
and the `/explain` HTTP endpoint.

## Why the source lives here, not in `formal/fstar/ocaml-output/`

Per CLAUDE.md iron rule #11, hand-written consumer-side OCaml does
not belong in `formal/fstar/ocaml-output/` — that directory is
reserved for F\*-extracted output and `assume val` glue patches.
This module is a consumer of the F\*-extracted SPARQL plan
infrastructure, so it lives under `bin/<consumer>/` per the
migration epic [#200](https://github.com/danbri/factoidal/issues/200)
Section D.

The built binary still lands at `bin/<platform>/factoidal` (and
`factoidal.byte`, `factoidal.js`) — same paths as before; only the
source moved.

## Build

The native `factoidal` binary build (`build-ocaml.sh compile`), the
JS bundle build, and the debug-bytecode build (`build-ocaml-debug.sh
factoidal`) reference this file via the relative path
`../../../bin/factoidal-explain/...` from `formal/fstar/ocaml-output/`,
plus `-I ../../../bin/factoidal-explain` so ocamlfind can resolve
the cmi when later modules call into `Factoidal_explain.<x>`.

## Cross-references

- Migration epic: [#200](https://github.com/danbri/factoidal/issues/200) Section D
- Pattern reference: `bin/factoidal-serve/README.md`,
  `bin/cottas-ondisk-smoketest/README.md`
