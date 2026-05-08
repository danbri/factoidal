# bin/cottas-ondisk-smoketest — COTTAS on-disk store smoketest harness

Phase 2 acceptance harness for issue #100 (COTTAS on-disk store).

## What this binary does

Stand-alone CLI:

```
cottas_ondisk_smoketest <path-to-data.cottas>
```

1. Opens the COTTAS file via the F\*-extracted on-disk store
   (`cottas_ondisk_open`).
2. Reports startup RSS in MB.
3. Runs the universal-bound triple pattern `(None, None, None, None)`
   = `SELECT (COUNT-* AS ?n) WHERE { ?s ?p ?o }` via
   `cottas_ondisk_estimate`.
4. Reports query wall-clock + post-query RSS.
5. Verifies that `backend_search` through `GB_CottasOnDisk` returns
   the same triple count for an unbound BGP `{?s ?p ?o}`.

## Why the source lives here, not in `formal/fstar/ocaml-output/`

Per CLAUDE.md iron rule #11, hand-written consumer-side OCaml does
not belong in `formal/fstar/ocaml-output/` — that directory is
reserved for F\*-extracted output and `assume val` glue patches.
This binary is a consumer of the F\*-extracted COTTAS API, so it
lives under `bin/<consumer>/` per the migration epic
[#200](https://github.com/danbri/factoidal/issues/200) Section D.

The built binary still lands at
`bin/<platform>/cottas_ondisk_smoketest` — same path as before; only
the source moved.

## Build

Built automatically by `formal/fstar/build-ocaml.sh compile`. Source
path is referenced relative from `formal/fstar/`:

```
../../bin/cottas-ondisk-smoketest/cottas_ondisk_smoketest.ml
```

Failure to compile is non-blocking (per the original Phase 2
harness contract); main binaries proceed.

## Cross-references

- Original tracking issue: [#100](https://github.com/danbri/factoidal/issues/100)
- Migration epic: [#200](https://github.com/danbri/factoidal/issues/200) Section D
- Pattern reference: `bin/xml-runner/README.md`
