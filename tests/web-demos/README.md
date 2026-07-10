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

### `hub_browser_all.sh`

Headless-Chromium regression harness for EVERY documentation-hub post
(`docs/web/hub/NN-*.md`, 30 of them as of this writing) -- distinct from
the two demo-page harnesses above, this one covers the docs hub
(`docs/web/hub/`), whose `observable-js` cells run the F*-extracted
engine in-browser and where a cell regression is often invisible to
any node-side test (it depends on real DOM/layout/GC/browser-tab
behavior). Sibling to `hub_smoke.sh` (the hub scaffold's own smoke
cell) and `hub_posts_smoke.sh` (posts 01-18, mounted-cell + mobile-
viewport checks); this one is broader (every post, enumerated from the
built site rather than hardcoded) but shallower (pageerror/REJECTED-
cell detection only, no interaction/viewport checks).

```sh
tests/web-demos/hub_browser_all.sh
HUB_BROWSER_ALL_PORT=8940 tests/web-demos/hub_browser_all.sh   # different port
```

Builds the site, serves it under `/factoidal/`, and drives ONE headless
Chromium instance (a fresh page per post) over every post, checking for
`pageerror` events and cells left in the vendored Observable Inspector's
own REJECTED state (`observablehq--error`, the class
`third_party/observable/dist/inspector.esm.js`'s `Inspector.rejected()`
adds to the cell's container node -- see `docs/_includes/hub.njk`'s
`createOutput()`, which mirrors it as `observable-cell-error` on the
same node). A page with zero live cells (e.g. post 22) passes trivially.

**Allowlist policy**: some pages may legitimately end a cell in a
rejected state (an intentional demo of the engine correctly rejecting
something) or carry an already-diagnosed bug out of this script's scope
(test-infra only -- it must not touch F\*/npm-package internals). Both
cases go through the same per-post `ALLOWLIST` object inside the Node
driver (`grep -n ALLOWLIST tests/web-demos/hub_browser_all.sh`), each
entry with an explicit, non-generic reason -- never a blanket
suppression. An allowlisted page still fails on any pageerror or
rejected cell the entry doesn't specifically cover. As of this writing
a full survey of all 30 posts found no cell that intentionally ends up
REJECTED (post 18's IndexedDB torn-write demo, post 21's WKT parser,
and post 28's MathML-to-Presentation converter all wrap their throwing
code in the cell's own try/catch and return a normal value describing
the failure), so the allowlist carries exactly one entry: post 24
(`24-hdt-header-dictionary-triples`), `KNOWN-BUG` -- `fn.queryHdt()` in
the js_of_ocaml bundle takes several seconds per call even against its
tiny 9KB/343-triple HDT fixture (measured directly against the npm
package's own JS-engine path: ~5.7s/20.5s/17.2s for the post's three
queries), which fully blocks the tab's main thread long enough that
headless Chromium can kill the unresponsive renderer -- a genuine,
reproducible performance bug in the HDT reader's js_of_ocaml path, not
a flake, and not something a test-infra-only change can fix. Needs an
HDT reader performance fix in F\* (`HDT.Triples.fst` /
`HDT.Dictionary.fst`).

Playwright's own `{timeout}` option on `waitForFunction`/`evaluate` is
NOT reliable once a page's JS main thread is fully blocked by a long
synchronous computation (confirmed empirically against post 24 -- a
declared 30000ms timeout didn't actually reject until ~44s of real
wall-clock time). The driver instead races every such call against its
own plain `setTimeout` deadline (`ownRace()` in the driver) so control
always comes back on schedule and the page can be force-closed cleanly
before anything at the browser-process level goes wrong -- verified
that a force-close mid-computation doesn't affect the SAME browser
instance's ability to serve subsequent posts.

Output is one `PASS <slug>` / `FAIL <slug>: <reason>` line per post
plus a final `hub-browser: X pass, Y fail (out of N posts)` summary.
Exit 0 iff Y=0. Total wall-clock is capped at 15 minutes; a full run
currently takes about a minute.

### `hub_post21_geo_check.sh`

Dedicated headless-Chromium checks for the GeoSPARQL post's Leaflet
choropleth map (task #105) — the assertions the two broader hub
harnesses above don't make. Builds the site, serves it under
`/factoidal/`, and drives Playwright over BOTH the strict page
(`web/hub/21-geosparql-geometry-and-topology/`) and its auto-generated
live-mode twin (`web/hub-live/21-.../`, produced by
`docs/web/hub-live.11ty.js`).

Strict page: zero pageerror/console.error, zero rejected cells, more
than 20 SVG paths inside `.hub-leaflet-map` (the 33-borough choropleth
+ Thames line actually rendered from the vendored GeoJSON under
`docs/web/hub/assets/geo/`), the custom fullscreen control present,
and — via Playwright request interception, so it can't pass just
because the sandbox happens to be offline — zero requests to any
non-localhost host across the whole page lifecycle.

Live twin: page loads with zero pageerrors, the "Live mode" banner is
present, `data-hub-mode="live"` is on `<body>`, and the cell's
live-only branch created its `L.tileLayer` object
(`window.__hubLiveTileLayer`) — deliberately WITHOUT asserting any
tile was fetched (CI has no network guarantee; non-local requests are
intercepted and answered with an empty 204).

```sh
tests/web-demos/hub_post21_geo_check.sh
HUB_POST21_GEO_CHECK_PORT=8942 tests/web-demos/hub_post21_geo_check.sh
```

Exit 0 iff all 12 checks pass. Wall-clock capped at 10 minutes.

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
