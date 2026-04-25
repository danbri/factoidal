# Landing-page backend selector + modernised query menu (Vau2)

Date: 2026-04-25
Agent: Vau2
Branch: claude/main
Scope: pure I/O glue in `formal/fstar/ocaml-output/factoidal_http.ml`
(rule #15 — landing page is HTTP routing, not RDF/SPARQL semantics).

## Problem

`landing_page_html ()` mounts `<factoidal-sparql-client endpoint="/sparql">`
and fetches `/parliament-queries.json` (24 vendored UK Parliament queries).
Two limitations:

1. The endpoint is hard-wired to `/sparql` on the same host. To compare the
   in-memory N-Quads loader vs. the binary COTTAS loader running on a
   different port (e.g. `100.107.116.70:3032`), the user has to edit the
   page or rewrite the URL. We want a runtime switch.

2. He2's modernised queries (commit cf22aad) live in
   `tools/sample-queries/ukparliament/{main,detail}/*_modern.rq` and are
   not surfaced in the dropdown.

3. The page never tells the user which backend is currently loaded or how
   many triples it contains.

## Design

### `GET /backend-info.json`

Returns a small JSON record describing the backend served on this port:

```json
{ "kind": "in-memory" | "binary" | "mixed" | "empty",
  "triples": 3143406,
  "default_graph_triples": 3143406,
  "named_graphs": 0,
  "named_graph_triples": 0,
  "source": "data.nq" }
```

- `kind`:
  - `binary`     — server was started with `--data-cottas` only.
  - `in-memory`  — server was started with `--dataset` only.
  - `mixed`      — both.
  - `empty`      — neither.
- `triples`: total triple count across default + named graphs (computed
  by `List.length`; cheap on an immutable in-memory store, OK for a UI
  pill, no need to cache).
- `source`: basename of the primary input file (or "(none)" if empty).

Implementation lives next to `serve_parliament_queries_json` and dispatches
from `try_static_route`. Reads `dataset_ref` so the count reflects the
current state (post-UPDATE).

### Two dropdowns in the landing page

A small `<header class="controls">` strip sits above the
`<factoidal-sparql-client>`:

- **Backend select** (`#backend-select`):
  - "Auto (this server)" → `endpoint = "/sparql"` (default).
  - "in-memory (N-Quads)" → `endpoint = location.origin + "/sparql"` (same
    behaviour today; explicit option reserved for future cross-host use).
  - "binary (COTTAS)" → `endpoint = ?cottas=` query-string value, falling
    back to `http://100.107.116.70:3032/sparql`.
  - On change: sets `clientEl.endpoint = newUrl` and re-fetches
    `<chosen>/backend-info.json` (CORS permitting; falls back to the
    local one with a "(remote pill unavailable)" note).

- **Query select** is the existing `<factoidal-sparql-client>`'s built-in
  dropdown — we just hand it a longer `queries` array. The JSON is
  augmented to carry a `group` string so we can later upgrade the
  component to render `<optgroup>`s; for now the labels are prefixed with
  "Vendored — " / "Modernised — " so the existing flat list is still
  readable.

### Backend-status pill

Plain `<span id="backend-pill">` styled as a pill:

```
Backend: in-memory (3,143,406 triples · data.nq)
```

Updated on:
- page load (fetch `/backend-info.json`),
- backend-select change (re-fetch from new origin).

### Modernised queries

New helper `parliament_modern_dir ()` resolves
`tools/sample-queries/ukparliament` (sibling of `third_party/data/...`).
For each `*_modern.rq` file it emits a JSON entry with key prefix
`modern/<group>/...` and label `"Modernised — <group> / <stem>"`. The
existing 24 vendored queries are emitted with label `"Vendored — ..."`.
Total: ~48 queries.

## Non-goals

- **Do not** change the web component bundle (`factoidal-sparql-client.js`).
  The component already supports `endpoint` as a reflected attribute and
  `queries` as a settable property; nothing else is needed.
- **Do not** touch any `.fst` files. This is pure HTTP routing glue.
- **Do not** add a discovery mechanism that auto-probes other ports.
  The user picks; the server reports its own state.

## Files touched

- `formal/fstar/ocaml-output/factoidal_http.ml`
  - new helper: `count_dataset_triples`
  - new helper: `resolve_modern_queries_dir`, `modern_entries_for_group`
  - extend: `build_parliament_queries_json` (add modernised entries)
  - new route: `/backend-info.json` in `try_static_route` + helper
    `serve_backend_info_json`
  - extend: `landing_page_html ()` HTML + JS

## Coordination

- Zayin2 is fixing the `--data-cottas` startup hang; that work is in
  argv parsing / `load_dataset`. Disjoint from this task (we only read
  `dataset_ref` and `cfg.dataset_file` / `cfg.data_cottas_files`).
- Gamma2 wrote the original landing page. We extend, not replace.

## Commit

`factoidal-http: backend selector + modernised query menu`
