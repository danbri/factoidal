# 2026-04-25 — factoidal-http landing page: web component + Parliament menu

**Agent:** Gamma2
**Branch:** claude/main (HEAD ~ 04808f7)
**Builds on:**
- Sade2 `cd5dc90` — landing page + bundled web component at `/`
- Aleph3 `56ab457` — `<factoidal-sparql-client>` remote-endpoint mode

## Why

User-stated requirement (verbatim):

> MUST be web component and w3c sparql protocol client

The current landing page (`landing_page_html ()` in
`formal/fstar/ocaml-output/factoidal_http.ml` lines ~1102–1164) inlines a
raw `fetch()` console. That predates Aleph3's remote-endpoint support and
needs to be swapped for `<factoidal-sparql-client endpoint="/sparql">`.

Plus: the user wants the 24 vendored UK Parliament queries
(`third_party/data/ukparliament/sparql/{main,detail}/*.rq`) selectable
from the landing page, so a person hitting `/` can click through real
queries against the running endpoint without copy-pasting from disk.

## Design

### Routes

1. `GET /` — already exists. Replace `landing_page_html ()` body with a
   page that mounts `<factoidal-sparql-client endpoint="/sparql">`, then
   on `DOMContentLoaded` fetches `/parliament-queries.json` and assigns
   the result to the component via the `queries` attribute (which the
   component already supports — see line ~663 of
   `docs/fstar-extracted/factoidal-sparql-client.js`,
   `_syncFromAttributes`).

2. `GET /parliament-queries.json` — new. Walks
   `third_party/data/ukparliament/sparql/{main,detail}/*.rq` at request
   time (no caching — He2 may modernise queries; updates surface
   naturally) and emits `[{key, label, body}, ...]`. Resolved via the
   same `argv[0]/CWD`-relative candidate list as the JS bundle.

   Sort key embeds the directory ("main — …", "detail — …") and the
   filename so the dropdown stays grouped + alphabetical.

### Why the JSON route, not an inline bake-in

Total `.rq` size is ~15 KB. The hard limit is 8 KB landing-page HTML
(excluding component bundle), so inlining 24 multi-line SPARQL bodies
plus JSON-escaping busts the budget twice over. A 100-byte fetch +
JSON parse is the obvious answer.

### Component API used

The web component already supports three ways to populate its query
dropdown — JS property, `queries` attribute (JSON), and
`<factoidal-query>` light-DOM children. We use the JS property
(`comp.queries = arr`) after fetch — cleanest, no JSON-in-attribute
escaping, and triggers re-render via the existing setter
(line ~570 of the component).

### Endpoint visibility

The component already shows an "endpoint pill" with the endpoint host
when in remote mode (line ~836). The landing page additionally renders
the endpoint URL as a `<code>` link in its `<p class="lede">` so a user
arriving fresh sees both the protocol-level URL and the human console.

### Out of scope (this commit)

- "Compare endpoints" link — would need a config-time list of sibling
  ports; defer until factoidal-http supports a registry.
- Per-query timing UI — already provided by the component's "Details"
  pane (line ~778). No work needed here.

## Iron-rule check

- Rule #15 (no semantic logic in OCaml glue): pure I/O — directory
  walk, file read, JSON formatting. No SPARQL/RDF decisions.
- Rule #1 (F* is the source of truth): unchanged — SPARQL.HTTP.fst
  is untouched, the protocol path is unchanged.
- ≤ 250 LoC of OCaml budget; landing HTML < 8 KB.

## Coordination

- Daleth2 may be wiring `--data-cottas` into factoidal-http. If their
  edits land first and conflict, rebase on top.
- He2 may be modernising the .rq files. We re-read on every JSON
  request, so their changes surface without restart.
- Aleph3 owns `factoidal-sparql-client.js` — we do not touch it.
