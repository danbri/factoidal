# SPARQL Parser Regressions

This note records local parser regressions that deserve direct coverage outside
the W3C suite.

## Why

The W3C SPARQL syntax suite is necessary, but it does not replace a small set
of repo-local regression cases triggered by real usage of the `factoidal` CLI.

## Current local parser check

`tests/local/sparql/prefix_a_semicolon.rq`

This query uses normal SPARQL shorthand:

- prefixed names
- `a` for `rdf:type`
- `;` predicate-object chaining

This query now parses and executes successfully through the local CLI and the
experimental HDT-backed query path. It stays as a repo-local smoke test because
it exercises a small, human-written query shape that is easy to rerun while the
SPARQL frontend and HDT path are still moving.

## Test runner

Use:

```bash
tests/local/sparql_parser_regressions.sh
```

Current semantics:

- `PASS` means the local shorthand query still parses and runs
- `FAIL` means the frontend has regressed and needs investigation
