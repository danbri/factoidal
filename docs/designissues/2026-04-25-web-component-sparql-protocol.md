# Web component: remote SPARQL Protocol endpoint mode

**Date:** 2026-04-25
**Agent:** Aleph3
**Status:** in-progress

## Goal

Add `endpoint=` attribute to `<factoidal-sparql-client>` so the same component
can target either:

1. **Local mode** (existing) — `src-data` attribute; queries run via the
   in-browser F* engine (JS or WASM).
2. **Remote mode** (new) — `endpoint` attribute; queries POST to a SPARQL
   1.1 Protocol endpoint, parse JSON response, render in the same UI.

## Why

- Sade2's landing page wants a hosted-endpoint demo against `/sparql`.
- The component already has the result-rendering UI (table/JSON/CSV/TSV
  views, column hide, downloads, timing summary). Reusing it costs ≤200 LoC
  of fetch+POST glue.
- The result schema produced by the F* engine is W3C SPARQL Results JSON
  — exactly what a Protocol endpoint returns. `_renderResultsJSON` accepts
  it directly.

## Scope (what changes)

- File: `docs/fstar-extracted/factoidal-sparql-client.js` (the wrapper, NOT
  the bundles `factoidal.js` / `factoidal.wasm.js`).
- New observed attribute: `endpoint`.
- New getter: `get endpoint()`.
- Dispatch in `_onRunClick`: if `endpoint` is set, take the remote path and
  skip `_getFilePayloads` + engine-source loading entirely.
- Engine-toggle UI suppressed (or replaced with endpoint URL pill) when in
  remote mode — local-mode JS/WASM toggle is meaningless against a remote
  server.
- Logic toggle hidden in remote mode (entailment regime is the server's job;
  not ours to set).
- `_warm()` skips engine prefetch in remote mode.

## Out of scope (deferred)

- HTTP GET form of the protocol (`?query=...`). POST is required by the
  spec for any query that exceeds URL length; we use POST unconditionally.
- Authentication / CORS configuration. If the endpoint requires auth or
  doesn't allow the page's origin, that's a server-side concern.
- Update / Graph Store Protocol. SELECT/ASK/CONSTRUCT/DESCRIBE only.
- CONSTRUCT / DESCRIBE result rendering (Turtle response). The component
  currently renders SPARQL Results JSON; serving Turtle from `/sparql`
  with `Accept: application/sparql-results+json` is the server's
  responsibility per the protocol.
- Remote-mode timing breakdown that distinguishes server time from network
  RTT. We surface total wall-clock only.

## Hard limits (per task brief)

- ≤ 200 LoC of new JS in the wrapper.
- No edits to the bundles (`factoidal.js`, `factoidal.wasm.js`).
- Backward compatibility: existing demos (`demo-cottas.html`,
  `demo-lifesci.html`, `demo-lifesci-v2.html`, `demo-notebook.html`) keep
  working without modification.

## API surface (after edit)

```html
<!-- Existing local mode (unchanged): -->
<factoidal-sparql-client
    src-data='[{"url":"./data.ttl"}]'
    engines="js,wasm" default-engine="js">
  <factoidal-query name="q1" label="Count">SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }</factoidal-query>
</factoidal-sparql-client>

<!-- New remote mode: -->
<factoidal-sparql-client endpoint="http://example.org/sparql">
  <factoidal-query name="q1" label="Count">SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }</factoidal-query>
</factoidal-sparql-client>
```

When both `endpoint` and `src-data` are set, `endpoint` wins.

## Test plan

1. Local server from `docs/fstar-extracted/` — open `demo-lifesci-v2.html`,
   verify in-browser engine still works (regression check).
2. Add a small smoke HTML that points at `http://100.107.116.70:3030/sparql`
   with a `SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }` query — verify it
   returns 3143406 (current live count).
3. Custom events still fire: `factoidal:query-start`,
   `factoidal:query-done`, `factoidal:query-error`.

## Coordination

Sade2's landing page will use `<factoidal-sparql-client endpoint="...">`
with no `src-data`. The component must not error if `src-data` is missing
when `endpoint` is set.
