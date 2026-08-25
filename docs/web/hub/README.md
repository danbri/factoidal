# Documentation hub — cell-authoring contract

This is the implementation reference for writing a hub post. The
reader-facing explanation lives in [the hub index](../)'s "How the
interactive cells work" section; this file is the fuller contract for
whoever writes the next post.

<!-- Linked as `../` (the directory), not `index.md` -- `index.md`
     is the one page in this directory Eleventy does NOT give its own
     pretty-URL subdirectory, so docs/.eleventy.js's mdlink-to-slug
     transform's blanket "prepend ../, drop .md, append /" rewrite
     turns a `.md`-suffixed link to it into a nonexistent `index/`
     path. See the equivalent note in index.md. -->

## Front matter

```yaml
---
title: "Post title"
description: "One-sentence description."
layout: hub.njk
series: docs-hub
series_order: N
vocab: foaf | wikidata | schema.org | skos | none
status: draft | published
tests: tests/hub/postNN_test.mjs
---
```

`layout: hub.njk` is required — it's what wires in the Observable
runtime and the fenced-block cell convention. The rest of the fields
are read by nothing at build time today; they're bookkeeping (the
series plan doc, `docs/designissues/2026-07-05-docs-hub-plan.md`, is
the source of truth for the series map) but keep them, since the next
post's author will grep for them.

## Fence conventions

- ` ```observable-js ` — a **live cell**. `docs/_includes/hub.njk`'s
  runtime script finds every `pre > code.language-observable-js`,
  wraps its text content in an async function body, and runs it
  through the vendored Observable Runtime + Inspector. Write a
  `return` statement to produce the value the Inspector renders.

### Cell chrome: Edit + Run

Every mounted cell auto-runs on page load exactly as before, but now
also gets a small toolbar (an Edit toggle and a Run button) inserted
between the code and the output box. DOM order after `mountCell()`
runs is:

```
<pre><code class="language-observable-js">...</code></pre>   <!-- original source, static view -->
<textarea class="observable-cell-editor" hidden>...</textarea>  <!-- editable view, seeded from the pre -->
<div class="observable-cell-toolbar">
  <button class="observable-cell-edit-btn">Edit</button>
  <button class="observable-cell-run-btn">Run</button>
  <!-- + a one-line hint span, first cell of the page only -->
</div>
<div class="observable-cell" data-hub-cell="N">...</div>   <!-- Inspector output -->
```

- **Edit toggle** swaps the static `<pre>` for a `<textarea>` seeded
  with the current source (`hidden` attribute flips both ways; the
  button label flips "Edit" / "Done"). The textarea is a deliberate
  choice over `contenteditable`: iOS Safari's contenteditable caret
  placement and undo stack are unreliable (cursor jumps on
  re-render, inconsistent Enter-key node splitting), whereas a plain
  `<textarea>` gets the native mobile keyboard, native undo/redo, and
  reliable `autocorrect`/`autocapitalize`/`spellcheck` suppression via
  ordinary attributes — the properties code entry on a phone actually
  needs. It autogrows via an `input` listener (`scrollHeight` resize
  trick) instead of a fixed row count.
- **Run** re-executes whatever the *current* source is (the textarea's
  value if editing, otherwise the unedited source) using the vendored
  Observable runtime's `module.redefine(name, inputs, definition)` —
  confirmed present on the vendored bundle
  (`third_party/observable/dist/runtime.esm.js`'s `module_redefine`,
  exported on `Module.prototype.redefine`). `redefine` looks up the
  already-`define()`d variable by name and re-runs `variable.define`
  on it, so the *same* `Variable` (and therefore the same attached
  `Inspector`/output node) recomputes in place — no delete+recreate,
  no new output box. `hub.njk` names each cell's variable `"hubCell" +
  index`, matching the name it was originally `define()`d with, so
  `main.redefine("hubCell" + index, CELL_BINDINGS, newFn)` always finds
  it.
- **Errors don't kill the cell.** `hub.njk` wraps the `Inspector`
  instance passed to `main.variable()` so a runtime rejection (thrown
  inside the cell's async body, on the initial run or any subsequent
  Run) adds the existing `.observable-cell-error` class to the output
  box, and a later successful Run removes it again — the same styling
  every static-render error already used, now also applied to
  redefine-triggered errors. A synchronous compile error (bad syntax in
  the edited source) is caught before `redefine` is even called and
  reported the same way. Either way the cell stays mounted: fixing the
  source and tapping Run again works.
- **Output-format toggle.** Each cell's toolbar carries a small
  radio-style segmented control, `Output: [Auto] [Table]`. `Auto`
  (the default, so nothing regresses) renders the cell's returned
  value with the Observable Inspector's js/json widget; `Table` wraps
  the same value in the existing `pretty()` helper. `hub.njk`'s
  `createOutput()` caches the last computed value and re-renders it on
  toggle, so flipping the control does **not** re-run the cell's
  computation. Because `pretty()` returns non-table shapes unchanged
  (DOM nodes, `null`, empty arrays, …), `Table` on a cell that already
  returns a DOM node (e.g. `Plot.plot(...)`) is a no-op — the Inspector
  renders it identically either way.
- **Keyboard:** Cmd/Ctrl+Enter inside the textarea runs the cell
  without touching the Run button — the desktop equivalent of the
  mobile tap target.
- **Discoverability:** a `title` attribute on the toolbar documents the
  Edit/Run affordance for desktop hover, but a phone has no hover — so
  the first cell on each page also gets a small, visible, italic hint
  ("Edit & re-run — computed in your browser.") next to its toolbar.
  Only the first cell gets it, to avoid cluttering every cell on the
  page with the same sentence.
- **Tap targets** (`.observable-cell-btn`) are >= 44px in both
  dimensions and wrap in a flex row, so the toolbar never forces
  page-level horizontal scroll at a 390px viewport; the textarea is
  `width: 100%` / `box-sizing: border-box` for the same reason.
- ` ```js `, ` ```turtle `, ` ```fstar `, etc. — static, inert code
  samples. Use these for pure notation (Turtle syntax being
  introduced, an F\* type definition being quoted) where there is
  nothing to *compute*, only something to *read*.

Only convert a code sample to a live cell when it actually computes
something a reader benefits from seeing run (a parse, a query, an
entailment closure) — not every fenced block needs to be live.

## Named cells: declare once, reference everywhere

This is the default authoring style for every post in the series, not
an optional extra. A cell of the form `name = <expression>` or `name =
{ ...statements...; return v; }` declares a **named** reactive
variable; any later cell that mentions `name` becomes a dependent, and
the vendored [Observable runtime](https://github.com/observablehq/runtime)
topologically orders the cells and re-runs whatever needs re-running
when an upstream value changes. A cell without a leading `name =`
(starting with `const`, `return`, a bare expression, …) stays
**anonymous**, exactly as before — naming is additive, not a
requirement on every cell.

The rule this replaces: earlier drafts of several posts had each live
cell redeclare its own copy of the same Turtle/JSON text (`const ttl =
\`…\`` pasted into every cell that needed it), so editing the data
meant editing it N times and no cell could build on another's parsed
result. That redundancy is the defect, not a style choice — when two or
more cells in a post need the *same* data (byte-identical, not just
similar), declare it once in a named cell — usually the first cell
that introduces it, or a small dedicated cell right where the data
first appears in the prose — and have every other cell reference the
bare name instead of repeating the literal. Name an intermediate
computed value (a parsed `Dataset`, a shared helper function) the same
way, but only where a later cell actually reuses it — don't introduce a
name nobody reads. Where two cells' data genuinely differs (even if
structurally similar), leave them independent; forcing a shared name
onto deliberately-different examples is the wrong direction.

[Post 26](../26-reactive-cells-declare-once-use-everywhere/) is the
worked example of the whole chain: `ttl = \`…\`` names the source text,
`graph = fn.parse(ttl)` names the parsed dataset (a promise-valued
cell — the runtime awaits it before any dependent reads it), `results
= fn.query(graph, …)` names the query result, `table = pretty(results)`
and a final anonymous chart cell both read `results`/further-derived
names. Tap **Edit** on the `ttl` cell there and change the data: only
the cells that actually depend on it re-run, not the whole page.

The compiler that infers each cell's name and its cross-cell inputs is
[`reactive-cells.mjs`](https://github.com/danbri/factoidal/blob/claude/main/docs/web/hub/reactive-cells.mjs) — shared, byte-for-byte,
between `docs/_includes/hub.njk` (the browser) and
`tests/hub/_helpers.mjs`'s `runReactivePost()` (the Node pinning
harness), so a post's tests exercise the identical dependency inference
the page runs. Read its header comment before writing a named cell —
it documents the exact traps:

- **`name = { … }` is a block body**, not an object literal — write
  `return` inside it. Use `name = ({ … })` (parens around the braces)
  when the value actually is an object.
- **A cell must never shadow a KNOWN name** — a builtin (`fn`,
  `Factoidal`, `Plot`, `d3`, `html`, `md`, `pretty`) or another cell's
  declared name. Local-binding detection is coarse (regex-based, not a
  real scope analysis), so a shadowed name can resolve unpredictably.
- **A `return /regex/` right after a keyword can misparse** as
  division — assign the regex to a `const` first, where detection is
  reliable.

A post's `tests/hub/postNN_test.mjs` pins the cross-cell wiring
directly: `runReactivePost(cells, bindings)` builds the same headless
Observable-runtime module the browser builds, and
`post.value(post.names[i])` reads a named (or anonymously-indexed)
cell's resolved value through its full dependency chain — proving the
references actually resolve, not merely that each cell happens to run
in isolation.

## Cell bindings (`CELL_BINDINGS`)

Every live cell's function body receives these bindings by parameter
name. This list and the `new Function(...)` parameter list in
`hub.njk` are mirrored deliberately — extend both together if a future
post needs a new binding.

| Name | What it is |
|---|---|
| `Factoidal` | the raw npm package entry (`npm/factoidal/browser.js`) — `query(dataString, sparqlString, {dataFormat, entail, output})` returns a raw SPARQL-JSON results object (or a raw string for non-JSON `output`), `toRdf()`/`canonicalize()` dump N-Quads text, `queryDataset()` handles multi-named-graph/multi-engine queries. No `Dataset`, no typed bindings — this is the CLI's own shape, one call in, one string/JSON out. |
| `fn` | the **typed** cell-facing API: `fn.parse(text, {format}) -> Promise<Dataset>`, `fn.query(dataset, sparql, {entail}) -> Promise<Bindings[] \| boolean \| Dataset>` — the same external contract `npm/factoidal/index.js`'s Node-side typed API exposes (`parse()`/`query()`/`Dataset.size`/iteration/`toNQuads()`), reshaped from `Factoidal`'s raw calls by a small adapter defined inline in `hub.njk` (see "Why `fn` is an adapter, not an import" below). Use this for any cell that parses a document or runs SELECT/ASK/CONSTRUCT and wants to work with terms/bindings rather than raw JSON. |
| `d3` | vendored `d3` 7.9.0, for hand-rolled charts. |
| `Plot` | vendored `@observablehq/plot` 0.6.17, for declarative charts. |
| `html` | vendored `@observablehq/stdlib`'s tagged-template HTML helper. |
| `md` | vendored `@observablehq/stdlib`'s tagged-template Markdown helper. |
| `pretty` | opt-in prettier rendering for a cell's return value — see "The `pretty()` rendering option" below. Returns a DOM node in the browser; nothing else in the contract changes if a cell never calls it. |
| `L` | vendored Leaflet 1.9.4 (`third_party/leaflet/`, BSD-2-Clause, no CDN) — `window.L` as set by the classic `<script>` load in `hub.njk`'s head. Use `L.map()`/`L.circleMarker()`/`L.geoJSON()` for vector map cells (no default marker-icon PNGs are vendored, so `L.marker()` with the stock icon will 404 — use `L.circleMarker` instead; a vendored GeoJSON basemap lives under `web/hub/assets/geo/`). `L.tileLayer()` against an external tile host is live-mode only (task #105): gate it on `data-hub-mode === "live"` — the strict page's CSP blocks the tile request, and `hub.njk` styles the layers-control toggle with a text glyph so the un-vendored `images/layers.png` is never requested either. |

### The `fn` typed surface in full

```
fn.parse(text: string, options?: {format?: string, baseIRI?: string}) -> Promise<Dataset>

fn.query(dataset: Dataset, sparql: string, options?: {entail?: 'none'|'RDFS'|'OWL-RL'})
  -> Promise<Map<string, Term>[]>   // SELECT
   | Promise<boolean>               // ASK
   | Promise<Dataset>                // CONSTRUCT / DESCRIBE

fn.shaclValidate(data: Dataset|string, shapes: Dataset|string, options?: {format?: string})
  -> Promise<{conforms: boolean, report: Dataset}>
  // report is SHACL_Validation.validation_report_to_graph's graph: one
  // sh:ValidationResult per violation (sh:focusNode, sh:resultPath,
  // sh:resultMessage, sh:sourceConstraintComponent). Throws if the
  // loaded bundle predates the SHACL export -- see "Capability checks"
  // below for the try/catch pattern a cell should use instead of
  // assuming this always resolves.

// Dataset:
dataset.size                        // number of quads
[...dataset]                        // iterate {subject, predicate, object} quads
dataset.toNQuads()                  // N-Quads/N-Triples text

// Term (subject/predicate/object, and Map values from query() rows):
term.termType                       // 'NamedNode' | 'BlankNode' | 'Literal'
term.value                          // IRI, blank-node label, or literal lexical form
term.language                       // '' unless termType === 'Literal' and it has a language tag
term.datatype.value                 // datatype IRI, Literal terms only
```

This is intentionally the same shape `npm/factoidal/index.js`'s
`parse()`/`query()` expose — a post's code sample is written once
against that typed API (and pinned by a `node:test` file importing the
real `npm/factoidal` module directly), then dropped into an
` ```observable-js ` fence with `factoidal.` renamed to `fn.` and any
`import` statement removed (cell bodies are plain function bodies, not
ES modules — no `import`/`export` inside a fence).

### Capability checks

Not every `fn` method is guaranteed to work against every loaded
engine bundle — `fn.shaclValidate` (and the raw `Factoidal.shaclValidate`/
`shexValidate`/`owlClosure`/etc. it's built on) needs the npm-entry ABI
bundle, which an older or stale build might not expose. A cell that
calls one of these should try/catch it and produce an explanatory
value on failure rather than let the whole cell render as a hard
`.observable-cell-error`:

```js
try {
  const result = await fn.shaclValidate(data, shapes);
  return { available: true, conforms: result.conforms };
} catch (err) {
  return { available: false, note: err.message };
}
```

This is the same pattern `npm/factoidal/lib/api.js`'s own `capabilities()`
probe uses server-side (per-function `typeof` checks); a cell doesn't
have access to `capabilities()` directly (it's Node-only, `npm/factoidal`'s
typed API, not exposed on `browser.js`), so try/catch around the call
itself is the client-side equivalent.

### Why `fn` is an adapter, not an import

`npm/factoidal/index.js` (and `fn.js`, the FP dataset wrapper it in
turn wraps) is CommonJS and uses `node:fs`/`node:crypto`/`require()` —
none of which exist in a browser. `npm/factoidal/browser.js` is the
one browser-safe ESM entry point; its raw, CLI-shaped calls (`query`,
`toRdf`, `canonicalize`, and the per-engine wrappers such as
`xsltTransform`/`queryHdt`) are the primitives `fn` is built on, not
what a hub cell calls directly. Rather than fork the engine, re-mirror
a browser build of the whole typed API, or change `npm/factoidal`
itself wholesale (out of this wave's territory — `npm/factoidal` and
`lib/api.js` are verified-library-adjacent surfaces with their own
test suite), `fn` is a small reshaping layer defined directly in
`docs/_includes/hub.njk`: for `parse`/`query` it feeds the browser
entry's `toRdf()`/`query()` results through a short N-Quads/SPARQL-JSON
parser to produce Dataset/Map-shaped values; for the engine wrappers
(XSLT, MathML, XForms, JSON Schema, Schematron, TOAN, matrix, HDT,
SHACL, canonicalize, update, capabilities) it delegates straight
through to the matching browser-entry function, unwrapped. It does not
import `npm/factoidal`/`lib/api.js` directly — the browser entry
(`browser.js`/`fn.js`/`index.d.ts` under `npm/factoidal/`, mirrored to
`docs/npm/factoidal/`) is the only shared surface.

### Trap: `*/` inside a `fn`-wrapper JSDoc comment breaks EVERY post

`hub.njk`'s `fn` object and its supporting functions live inside ONE
inline `<script type="module">` block that every hub post's page
shares. A JS block comment (`/** ... */`) closes at the FIRST `*/` it
contains — same trap as F*'s nesting `(* ... *)` comments (CLAUDE.md's
"F\* Syntax Traps"), except a JS block comment does not nest at all,
so it is even easier to trip. Writing a glob-ish name like `rhoDf*/
sigmoid` inside a doc comment (post 42's `toCottas`/`openCottas`
wrapper, 2026-08-25) closes the comment right there; every line after
it becomes literal top-level code, and the whole shared script fails
to parse with a generic `Unexpected token '*'` — on EVERY post's page,
not just the one being edited, since they all load the same script.
Two fixes, either is enough: write the name without the slash
(`rhoDf-family`, not `rhoDf*/`), or use `//` line comments instead of
`/** */` for prose that might contain `*/`. Verify a hub.njk edit by
extracting the ACTUAL rendered `<script type="module">…</script>`
block from a built page (anchor on the line that is exactly
`<script type="module">`, not a textual mention of that string inside
the CSP `<!-- -->` comment near the top of the file — an easy
false-negative) and running `node --check` on it.

### The `pretty()` rendering option

Every cell can return raw arrays/objects and let the Inspector render
its default collapsed-JS-tree view — that's still the default, and
most cells (posts 03-05, and any cell not explicitly converted) do
exactly that. `pretty(value)` is an **opt-in** alternative for the
common shapes a query cell tends to produce: wrap the cell's return
value in `pretty(...)` and get a small styled HTML table instead of a
JS-tree the reader has to expand.

Shape dispatch (checked in this order):

| Input shape | Rendering |
|---|---|
| Array of `Map` (SPARQL bindings rows — Map keys are variable names) | table, one column per variable, in first-seen order across all rows |
| Dataset-like (has `.size` and is `Symbol.iterator`-able over quads) | a triples/quads table: `s`/`p`/`o` columns, plus `g` if any quad has a graph |
| Array of plain objects | table from the union of keys across all objects, in first-seen order |
| Plain object | a two-column key/value table |
| Scalar (`string`/`number`/`boolean`/`bigint`) | a small styled value span |
| Anything else (`null`, `undefined`, an empty array, a DOM node, a lone `Map` not inside an array, ...) | returned **unchanged** — the Inspector's own renderer handles it exactly as if `pretty()` had never been called |

Term values (`NamedNode`/`BlankNode`/`Literal`) inside a table cell are
shortened for display: an IRI compacts to its trailing path/fragment
segment with the full IRI in a `title` tooltip (hover on desktop; the
raw value is still there for anyone who needs it); a blank node is
shown `_:`-prefixed; a literal is quoted, with an `@lang` or
`^^datatype` suffix when present (datatype/language also folded into
the tooltip). Tables sit inside a scrollable wrapper — both axes, so a
wide table doesn't force the page to scroll horizontally at a 390px
viewport (same `overflow-x` pattern `.observable-cell` already uses)
and a tall table scrolls internally instead of pushing the rest of the
page down — with a small caption line above the grid giving the row
(or field) count, e.g. "12 rows".

**Browser vs. test duality.** `hub.njk`'s `pretty()` returns an actual
DOM node — the Inspector's contract for a DOM-Node return value is to
insert it as-is, so this composes with the existing Inspector
machinery with no special-casing. `tests/hub/_helpers.mjs` exports a
`pretty` stub with the *same shape dispatch* but no DOM dependency: it
returns a plain, JSON-serializable structure instead —
`{kind: 'table', columns: [...], rows: [[...], ...]}` or
`{kind: 'value', value}` — so a pinned `node:test` can assert on table
shape (`result.columns`, `result.rows.length`, cell contents) without a
browser. Both implementations satisfy the same shape-dispatch contract
above; a cell written against `pretty()` runs unchanged against either.

## Reader-added cells

Below the pinned cells, `hub.njk`'s `initUserCells()` appends a "Your
own cells" section with an `+ Add a cell` button. Clicking it mounts a
fresh live cell — an editable `<textarea>` plus a `Run`, `Remove` and
the same `Output: [Auto] [Table]` toggle — that evaluates through the
**same** `compileCell()` / `CELL_BINDINGS` path the pinned cells use,
so `fn`, `Factoidal`, `Plot`, `d3`, `html`, `md` and `pretty` are all
in scope. Each user cell gets its own Observable runtime `Variable`
(`userCell<seq>`); `Run` (re-)defines it in place, `Remove` calls
`variable.delete()` to tear it out of the runtime and drops the DOM
block. The pinned cells are never touched — this only adds cells on
top. Nothing a reader types is persisted or sent anywhere; it runs in
their browser and disappears on reload.

## Testing discipline

Every live cell's source must also be pinned in that post's test file
under `tests/hub/postNN_test.mjs`. The pinning tests extract the exact
fenced source out of the shipped post file
(`extractObservableCells()` in `tests/hub/_helpers.mjs`) and execute it.
A post whose cells are all anonymous (no cross-cell references) can
run each cell standalone via `runObservableCell()` — the same `new
Function(...CELL_BINDINGS, body)` construction `hub.njk`'s
`mountCell()` uses. A post with named, cross-referencing cells (the
norm — see "Named cells" above) instead uses `runReactivePost(cells,
bindings)`, which builds the same headless Observable-runtime module
`hub.njk` builds in the browser, wiring each cell's inputs through the
identical `reactive-cells.mjs` compiler; `post.value(post.names[i])`
then reads a cell's resolved value through its full dependency chain,
so the test proves the cross-cell references actually resolve rather
than merely that each cell runs alone. Either way, the test runs the
literal string that ships on the page, not a hand-copied approximation
that can drift. The Node-side `fn` binding used in tests is the *real*
`npm/factoidal` typed API (imported the same way
`npm/factoidal/test/*.js` does), not the browser adapter — since both
implementations satisfy the same external contract above, one cell
source works correctly executed against either.

The browser-side correctness check (does `fn`'s adapter actually work
against the real F\*-extracted engine in a real browser) is
`tests/web-demos/hub_posts_smoke.sh`, which drives headless Chromium
over each built post page and asserts every `.observable-cell` on the
page computes without `.observable-cell-error` and produces a value.
It also drives one interaction pass, on the first post's first cell:
click the Edit toggle, overwrite the textarea with a trivially
different deterministic expression (`return 6 * 7;`), click Run, and
assert the output box updates to `42` with no
`.observable-cell-error` — i.e. that the toolbar's Edit/Run chrome and
`module.redefine()` re-run path actually work end to end, not just
that the auto-run-on-load path does. The 390px no-horizontal-overflow
check (`document.documentElement.scrollWidth <= clientWidth`) runs on
every page after the toolbar has mounted, so it also covers the
toolbar/editor chrome added by this change.

## Constraints every cell must respect

- **Same-origin only (strict pages).** Every import in `hub.njk` is a
  same-origin Pages path (`{{ '...' | url }}`) — never a CDN URL. Cell
  bodies inherit this: don't `fetch()` an external URL from inside a
  cell — the strict hub's Content-Security-Policy (`img-src`/
  `connect-src 'self'`, stated in `hub.njk`'s `<meta http-equiv>` tag)
  blocks it anyway. **Live-mode caveat (task #105):** every post also
  gets an auto-generated twin at `/web/hub-live/<slug>/`
  (`docs/web/hub-live.11ty.js`) whose CSP additionally allows
  `https:` on `img-src`/`connect-src` only — external *data* (map
  tiles, remote SPARQL endpoints), never external *scripts*. A cell
  that wants live-only behavior must feature-detect via the
  `data-hub-mode` attribute `hub.njk` sets on `<body>` (`"strict"` or
  `"live"`) and degrade cleanly when it reads `"strict"` — the same
  cell source runs on both pages. See post 21's map cell for the
  worked example.
- **js engine only.** The wasm_of_ocaml build
  (`docs/npm/factoidal/browser-wasm.js`) is stale for newer CLI
  surfaces cells rely on (`--dump-nq` byte-for-byte parity, etc.);
  cells use the default js_of_ocaml path (`Factoidal`/`fn`'s default
  engine), not `queryDataset(..., {engine: 'wasm'})`.
- **No engine/npm/lib changes.** If a cell genuinely cannot be
  expressed against `Factoidal`/`fn` as they stand, don't extend
  `npm/factoidal` or `docs/npm/factoidal/` to make it work — write the
  cell against the raw `Factoidal` API instead and note the gap in
  the post's prose.
