# Per-dataset web demos via static files

Date: 2026-04-25
Author: Heth2 (agent)
Status: in-progress

## Why

Currently `factoidal_http.ml` inlines a ~150-line HTML/JS landing page as a
single OCaml string literal (`landing_page_html ()`). That is fine for a
single hard-coded UI but it has three growing-pain problems:

1. **UI changes require a rebuild.** Tweaking a CSS rule means
   re-extract → recompile → relaunch the binary. We want web designers
   (or at least the human at the keyboard) to iterate without touching
   F* / OCaml.
2. **The HTML is Parliament-specific.** The lede paragraph mentions UK
   Parliament queries; the page hard-codes a Parliament queries dropdown.
   When we point factoidal-http at a different dataset (`simple.ttl`,
   life-sciences KGX, etc.) the framing is wrong.
3. **No room for per-demo assets.** A future life-sciences demo will want
   its own JS/CSS/data files; today there's no place to drop them.

## What

- `docs/web/landing/index.html` — generic SPARQL playground (default when
  no `--web-demo` flag is passed). Plain textarea + Run + the
  `<factoidal-sparql-client>` web component.
- `docs/web/demos/<demo-id>/index.html` — per-dataset demo UI. Seeded
  with three:
  - `ukparliament/` — the current Vau2 page, made dataset-specific
    (Parliament lede + queries dropdown stays).
  - `simple-entailment/` — small demo for `simple.ttl` exercising entailment.
  - `lifesci/` — placeholder/stub.
- `factoidal-http --web-demo DEMO_ID_OR_PATH`
  - Bare id (`ukparliament`) → resolves to `docs/web/demos/ukparliament/`
  - Absolute path → served directly
  - Default → serves `docs/web/landing/`
- factoidal-http serves the chosen directory recursively as static files
  (HTML/JS/CSS/JSON/PNG) at `/<path>`. Demos can ship their own assets.
- `/sparql` is unchanged — strict W3C SPARQL 1.1 Protocol endpoint.
- `/parliament-queries.json` and `/backend-info.json` continue to live in
  the OCaml glue (they're data, not UI). The demo HTML fetches them.
- If the resolved demo directory doesn't exist, return a 1-line plaintext
  message pointing the user at `--web-demo` (no 500).

## Iron rules touched

- Rule #15: keeping semantic logic out. The static-file serving is pure
  I/O glue — no SPARQL semantics involved.
- Rule #13: never edit extracted `.ml` from `ocaml-output/`. Wait — that
  applies to F*-extracted files. `factoidal_http.ml` is hand-written
  glue, not extracted, so editing it is allowed.

## Coordination

Zayin2 may be touching argv parsing for `--data-cottas` (data load path).
This change adds `--web-demo` (UI path). Both are key=value flags;
collision risk is low and we keep `parse_args ()` as a single
function with both branches added in compatible style.

## Sample invocation

```
./bin/darwin-arm64/factoidal-http \
  --port 3030 \
  --data-cottas third_party/data/ukparliament-2019.cottas \
  --web-demo ukparliament
```

Future demos: just drop `docs/web/demos/<id>/` with an `index.html`. No
recompile.
