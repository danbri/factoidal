# tests/beyond-w3c — demanding parity tests for the public demo surface

This directory is the regression net for the demo queries the public site
exposes (`docs/fstar-extracted/*.html`). It runs every demo query through
every runtime we ship and asserts they all agree.

Tracking issue: #241 (umbrella). Sub-issues #242–#248 cover the six phases.

## What this suite covers

| Layer | What it asserts | Sub-issue |
|---|---|---|
| Phase 1 — Fixtures | every `<factoidal-query>` has a manifest entry; CI lint catches drift | #242 |
| Phase 2a — JS-in-node | every fixture runs in `node factoidal.js`; row-set parity vs native | #243 |
| Phase 2b — Wasm-in-node | every fixture runs in `node factoidal.wasm.js`; row-set parity vs native | #244 |
| Phase 3 — Headless browser | Playwright drives the live demo page in real Chromium; catches frontend render bugs (see #240) | #245 |
| Phase 4 — Dashboard | per-runtime per-query pass/fail grid on the public test-results page | #246 |
| Phase 5 — Perf | parse-time / eval-time / total-ms per (query, runtime), history-tracked; anchors #95 | #247 |
| Phase 6 — Persistence | COTTAS persistent backend cold-load + repeated-query parity vs in-memory | #248 |

Each phase produces a checkpoint that the next phase consumes; running the
whole suite is one shell entry point (TBD as phases land).

## Layout

```
tests/beyond-w3c/
  README.md                    — this file
  fixtures/                    — per-page manifest + queries
    <page-name>.json           — manifest: datasets + queries + expected
    queries/                   — .rq files referenced from manifests
    expected/                  — reference SPARQL-Results JSON / CSV (Phase 1)
  runners/                     — per-runtime adapters
    run-native.sh              — bin/<plat>/factoidal
    run-js-node.sh             — node docs/fstar-extracted/factoidal.js
    run-wasm-node.sh           — node docs/fstar-extracted/factoidal.wasm.js  (Phase 2b)
    run-browser.{ts,js}        — Playwright/Puppeteer driver  (Phase 3)
    run-cottas.sh              — persistent backend           (Phase 6)
  bin/
    run-parity.py              — orchestrator: walks a manifest, calls runners, computes the grid
```

## Manifest schema

```json
{
  "page": "docs/fstar-extracted/index.html",
  "datasets": [
    { "name": "people",  "file": "docs/fstar-extracted/samples/people.ttl",  "format": "turtle" }
  ],
  "queries": [
    {
      "name": "bind-upper",
      "label": "BIND + string functions",
      "dataset": "people",
      "file": "tests/beyond-w3c/fixtures/queries/bind-upper.rq",
      "expected": { "kind": "row-count", "rows": 5 },
      "known_failures": {
        "js-node":   { "issue": 240, "note": "BatUChar.Out_of_range mid-stream" },
        "wasm-node": { "issue": 240, "note": "Likely same root cause as js-node" }
      }
    }
  ]
}
```

`expected.kind` ∈ `row-count` | `row-set-csv` | `row-set-srx` | `boolean`.
`known_failures` is the only escape hatch — every entry carries an issue
number so the failure has a tracker. Removing the entry must be the same
PR that fixes the bug.

Adding a `<factoidal-query>` to a demo page without a fixture entry is a
CI failure (Phase 1 lint).

## Why not just extend tests/web-demos/lifesci_parity.sh?

`tests/web-demos/` is currently 5 lifesci queries × 3 runtimes via a bash
script. It serves its purpose but doesn't scale to:

- 40+ demo queries across 6 demo pages
- Headless-browser drivers (Playwright)
- Per-(query, runtime) cell on the public dashboard
- Perf history tracking
- Persistent-backend cold-load tests

The fixture migration in #242 absorbs `lifesci_queries.json` into the new
schema; the old script can either redirect to the new runner or be retired.

## Status

The scaffold (this file + `fixtures/queries/bind-upper.rq` + a stub manifest
for `index.html`) lands first so subsequent phase PRs each ship one moving
part. The bind-upper query is the canonical failing case from #240 — every
runner that lands gets a real test from day one.
