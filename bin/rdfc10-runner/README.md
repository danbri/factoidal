# bin/rdfc10-runner — W3C RDFC-1.0 canonicalization test runner

Stand-alone CLI that drives the W3C RDF Dataset Canonicalization 1.0
(RDFC-1.0) test suite against the F\*-extracted `RDF.Canonical`
implementation.

```
rdfc10_runner <manifest.ttl>
```

Reads `third_party/testing/rdf-canon/tests/manifest.ttl` via the
F\*-extracted `Parser_Turtle`, dispatches per test type
(`rdfc:RDFC10EvalTest`, `rdfc:RDFC10MapTest`,
`rdfc:RDFC10NegativeEvalTest`), and runs each through
`RDF_Canonical.canonicalize_to_nquads` (Phase 1 HFDQ + Phase 2 HNDQ
permutation enumeration), comparing byte-for-byte against the
expected output.

## Why the source lives here, not in `formal/fstar/ocaml-output/`

Per CLAUDE.md iron rule #11, hand-written consumer-side OCaml does
not belong in `formal/fstar/ocaml-output/` — that directory is
reserved for F\*-extracted output and `assume val` glue patches.
This binary is a consumer of the F\*-extracted RDF / Canonical /
parser modules, so it lives under `bin/<consumer>/` per the
migration epic [#200](https://github.com/danbri/factoidal/issues/200)
Section D.

The built binary still lands at `bin/<platform>/rdfc10_runner` —
same path as before; only the source moved.

## Build

Built automatically by `formal/fstar/build-ocaml.sh compile`. Source
path is referenced via `../../../bin/rdfc10-runner/rdfc10_runner.ml`
from the `formal/fstar/ocaml-output/` cwd.

## Cross-references

- Migration epic: [#200](https://github.com/danbri/factoidal/issues/200) Section D
- Pattern reference: `bin/cottas-ondisk-smoketest/README.md`,
  `bin/factoidal-dump-nq/README.md`
- RDFC-1.0 plan: `docs/designissues/2026-04-25-rdfc10-algo-plan.md`
