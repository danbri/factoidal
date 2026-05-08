# bin/w3c-runner — W3C SPARQL 1.1 + RDF 1.1 + RIF entailment test runner

Hand-written OCaml entry point for the load-bearing W3C test harness:

```
w3c_runner [--all | --rdf <suite> | <suite>]
```

Reads test manifests under `third_party/testing/w3c/`, dispatches to
F\*-extracted parsers / SPARQL evaluator / OWL closure, prints
per-test outcomes + aggregate scores. Source for the public
dashboard at https://danbri.github.io/factoidal/test-results/.

## Rule #15 sniff

This runner contains the `RIF.Core` saturation dispatch + RIF
imports resolution (`rif_resolve_import_local_path`,
`rif_load_imports`) that landed in #232 / #225. That's
test-harness convention (loading W3C-vendored RIF rule files +
companion data graphs) plus pure I/O — defensible at the harness
boundary. Per CLAUDE.md iron rule #15 ("no semantic logic in test
runners") this is on the line. Migration into a verified library
boundary is a future refactor; for now it stays consumer-side.

## Why the source lives here, not in `formal/fstar/ocaml-output/`

Per CLAUDE.md iron rule #11, hand-written consumer-side OCaml does
not belong in `formal/fstar/ocaml-output/` — that directory is
reserved for F\*-extracted output and `assume val` glue patches.
This runner is a consumer of the F\*-extracted parsers + SPARQL
engine + OWL closure, so it lives under `bin/<consumer>/` per the
migration epic [#200](https://github.com/danbri/factoidal/issues/200)
Section D.

The built binary still lands at `bin/<platform>/w3c_runner` —
same path as before; only the source moved.

## Build

`build-ocaml.sh compile` for native; `build-ocaml.sh js` for the
browser bundle (`docs/fstar-extracted/w3c-runner.js`); `build-
ocaml.sh wasm` for wasm (experimental).

Source path: `../../../bin/w3c-runner/w3c_runner.ml` from the
`formal/fstar/ocaml-output/` cwd. No `-I` flag needed: this is
the entry-point module.

## Cross-references

- Migration epic: [#200](https://github.com/danbri/factoidal/issues/200) Section D
- Dashboard: `formal/fstar/generate-report.sh` consumes the
  `*_results.log` outputs of this runner.
- Pattern reference: `bin/owl-runner/README.md`,
  `bin/rdfc10-runner/README.md`
