# tests/web-demos — parity tests for the browser demos

This directory asserts that the SPARQL queries and RDF data bundled with the
`docs/fstar-extracted/*.html` demo pages produce the *same* results across all
three engines we ship:

| Engine | Driver |
|---|---|
| Native OCaml | `bin/<platform>/factoidal` |
| js_of_ocaml | `node docs/fstar-extracted/factoidal.js` |
| wasm_of_ocaml | `node docs/fstar-extracted/factoidal.wasm.js` |

The demo pages (`demo-lifesci.html`, `demo-cottas.html`, `demo-dev.html`,
`index.html`) load these bundles in-browser and run queries over data fetched
same-origin from `docs/fstar-extracted/lifesci/`, `docs/fstar-extracted/
cottas-examples/`, etc. If a browser user sees different results from the
native CLI, that's a regression we want to catch before it ships.

## Harnesses

### `lifesci_parity.sh`

Runs every query from `demo-lifesci.html` through all three engines against
the three lifesci named graphs, comparing row counts to a JSON-encoded
expectation.

```sh
tests/web-demos/lifesci_parity.sh          # all three engines
tests/web-demos/lifesci_parity.sh --skip-wasm   # skip wasm (faster)
```

Exit code is 0 iff every engine produces the expected row count for every
query that isn't on the `known_failures` allowlist.

### `lifesci_queries.json`

The test definition: dataset mapping + per-query `{name, file, expected_rows,
note}` objects. `expected_rows_min` is accepted in place of `expected_rows`
for data-dependent queries.

`known_failures.<engine>.<query>` marks a query as expected to error on a
specific engine. The entry's value is a human-readable note explaining the
root cause and linking to the tracking issue (open one before landing).

## Current status (2026-04-23)

Five lifesci queries × three engines. All five pass on native. Two JS and
two WASM queries currently error with stack overflows — the non-tail-rec
cross-graph BGP + UNION + GROUP BY combinations blow v8's default stack.
Tracked under `known_failures`; native parity still verified.

## Adding a demo

When you add or change a demo under `docs/fstar-extracted/*.html`:

1. If the demo introduces new queries, add them to `lifesci_queries.json`
   (or create a new `<demo>_queries.json` + `<demo>_parity.sh`).
2. Run the parity script against a freshly-built native binary to get the
   expected row counts.
3. Bundle regeneration commits (`./build-ocaml.sh js wasm wasm-factoidal`)
   should re-run the parity script as part of the verification loop so no
   regression ships.

## Why not just Playwright against the live page?

The page load pulls in js_of_ocaml and wasm_of_ocaml bundles that are
identical to what the Node driver loads — there's no browser-only codepath
for the engine itself. Node-driven parity catches engine regressions without
the flakiness of a headless-browser harness. Separate Playwright smoke
tests for the UI live under `.playwright-mcp/` (not in this directory).
