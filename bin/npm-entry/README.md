# bin/npm-entry — js_of_ocaml / wasm_of_ocaml entry for the npm package

Two profiles, one ABI (https://github.com/danbri/factoidal/issues/684):

| file | module split | links |
|---|---|---|
| `entry_core.ml` | `Entry_core` | parse/query/update/serialize/dataset-handle surface; only F* modules on the allowed-list in its own header comment |
| `entry_extras.ml` | `Entry_extras` | RIF, JSON-LD, XML/XPath, SHACL, ShEx, closures + tableau, OWL DL, RML, CSVW, delta log, COTTAS, VC/DID crypto, XSLT, MathML, XForms, JSON Schema, Schematron, TOAN, matrix, sigmoid |
| `entry_jsoo.ml` | full export table | `entry_core.ml` + `entry_extras.ml` → `factoidal-npm-entry.js` / `.wasm.js`, `profile: "full"` |
| `entry_lite_jsoo.ml` | lite export table | `entry_core.ml` ALONE → `factoidal-npm-entry-lite.js` / `.wasm.js`, `profile: "lite"` |

Both export tables use the SAME JS global `factoidalNpmEntry` (design
record decision 5), so `npm/factoidal/lib/api.js`, `browser.js` and
`createApi` work unchanged against either bundle — a caller picks the
bundle file, not a different API shape. `entry_core.ml`'s
`extra_parsers` hook is how RDF/XML and JSON-LD parsing reach
`parseToDatasetJson`/`parseDocument`/`datasetOpen` when
`entry_extras.ml` is linked (the full bundle); in the lite bundle the
hook stays `None` and those two formats answer a routing error naming
the full bundle instead of a missing-function crash.

All four are CONSUMERS (rule #11): hand-written OCaml glue that
exposes the F*-extracted engine to JavaScript via a small, stable,
string/JSON ABI. No RDF or SPARQL semantics live here — every semantic
operation delegates to an F*-extracted module, named in each file's
own header/section comments:

  parse (strict, with position + prefixes) -> Parser.Diagnostics.fst's
                  turtle_document / trig_document / ntriples_diagnostic /
                  nquads_diagnostic (extracted as Parser_Diagnostics.ml),
                  RDF_Format dispatch, RDF_Dataset_Merge.rename_dataset_bnodes
                  for per-document blank-node scoping
  query         -> SPARQL11_Parser.parse_sparql, OWL_QueryRewrite,
                  SPARQL11_Store.run_select_query_backend_dataset /
                  run_ask_query_backend_dataset (fallback:
                  SPARQL11_Algebra.eval_select_query / eval_ask_query),
                  SPARQL11_Algebra.eval_construct_query
  update        -> SPARQL11_Parser.parse_sparql_update,
                  SPARQL11_Algebra.apply_update
  serialize     -> RDF_Canonical.canonical_nquads (sorted N-Quads)
  canonicalize  -> RDF_Canonical.canonicalize_to_nquads (RDFC-1.0)
  serialize (turtle) -> RDF_Turtle_Serialize.turtle_of_graph_opts /
                  turtle_of_graph_auto (prefix-compacted,
                  subject-grouped pretty-print; caller prefixes win
                  when given)
  SRJ terms     -> SPARQL_Protocol.json_term, SPARQL_JSON_Escape

The full ABI contract (every exported function, its JSON envelope
shape, and which bundle carries it) is documented in the header
comment of [`entry_jsoo.ml`](entry_jsoo.ml). The JavaScript consumer
is [`npm/factoidal/lib/api.js`](../../npm/factoidal/lib/api.js).

## abiVersion "2" — strict-by-default parsing, dataset handles, prefixes

Bumped from "1" for three landings, all in `entry_core.ml`:

- **Strict parsing**
  (https://github.com/danbri/factoidal/issues/344). `parseToDatasetJson`
  and `datasetOpen` reject the WHOLE parse on any syntax error, any
  undeclared prefix, or any relative IRI that cannot resolve (no
  `baseIri` in effect) — nothing is silently dropped any more. The
  error envelope carries a byte offset plus 1-based line/column
  (`Parser_Diagnostics.position_of_offset`) for every syntax the
  parser can report a position for (Turtle, TriG, N-Triples,
  N-Quads); RDF/XML and JSON-LD failures carry a message only. New
  `parseDocument(text, format, baseIri, optionsJson)` adds an opt-in
  `{"lenient":true}` mode that answers `ok:true` with whatever the
  parser recovered plus a `diagnostics` array, for a caller that wants
  the old best-effort behaviour with the drop count made visible
  instead of invisible.
- **Dataset handles**
  (https://github.com/danbri/factoidal/issues/680, mirroring
  `formal/lean4/Wasm/Ops/Handles.lean`'s op names and envelopes).
  `datasetOpen`/`datasetQuery`/`datasetQuery12`/`datasetUpdate`/
  `datasetSerialize`/`datasetSerializeWith`/`datasetClose` parse and
  index a dataset ONCE and let a caller query/update/serialize it many
  times by handle string (`"h1"`, `"h2"`, ... never reused), instead of
  re-parsing N-Quads text and rebuilding the SPARQL index on every
  call. `entry_core.ml`'s `eval_query_over_backend` is the one
  evaluator both the stateless `queryDataset` and the handle-based
  `datasetQuery` call, so query semantics are identical either way.
- **Prefix-aware, shorthand-aware Turtle output**
  (https://github.com/danbri/factoidal/issues/681).
  `parseToDatasetJson`/`parseDocument`/`datasetOpen` report the
  prefixes the parser read (`"prefixes":{"ex":"http://example.org/"}`,
  labels without their trailing colon, in declaration order with a
  later redeclaration of the same label winning); new
  `serializeTurtleWith`/`datasetSerializeWith` take an `optionsJson`
  of `{"prefixes":{label:iri},"literalShorthand":true|false}` — caller
  prefix pairs win in the caller's order, unused caller namespaces are
  not emitted, and auto `nsN:` labels skip caller labels
  (`RDF_Turtle_Serialize.turtle_of_graph_opts`).

Every ABI member from `abiVersion "1"` keeps its name and its
envelope's existing members; nothing that used to work has changed
shape.

## Type-checking the four files standalone

```sh
eval $(opam env --switch=fstar)
cd formal/fstar/ocaml-output
ocamlfind ocamlc -c -package fstar.lib,str,zarith,sha,digestif.c,js_of_ocaml \
  -I . -w -8-14-26 ../../../bin/npm-entry/entry_core.ml
ocamlfind ocamlc -c -package fstar.lib,str,zarith,sha,digestif.c,js_of_ocaml \
  -I . -I ../../../bin/npm-entry -w -8-14-26 ../../../bin/npm-entry/entry_extras.ml
```

(run from a scratch dir with `-I ocaml-output` to avoid dropping
artifacts into the build tree; `bin/npm-entry/.gitignore` already
excludes `*.cmi`/`*.cmo`/`*.cmx`/`*.o`/`*.byte` for the artifacts that
DO land next to the source here, which they do for any cross-directory
`../../../bin/npm-entry/*.ml` argument — see the build wiring note
below).

## Build wiring in formal/fstar/build-ocaml.sh

### 1. `js` step — full + lite `npm_entry*.byte` and their `.js`

The full build links `entry_core.ml entry_extras.ml entry_jsoo.ml` (in
that order — `entry_extras.ml` `open`s `Entry_core`, `entry_jsoo.ml`
references both) into `npm_entry.byte`, alongside `FSTAR_MODULES`, with
`-I ../../../bin/npm-entry` added so the cross-directory `.cmi` files
(ocamlc writes each source's `.cmi`/`.cmo` next to ITS OWN file, not
into `cwd`) resolve. `js_of_ocaml` emits
`docs/fstar-extracted/factoidal-npm-entry.js`.

The lite build runs after: every `FSTAR_MODULES` unit is compiled to a
scratch bytecode object in `_lite_cmo/` (gitignored) and archived into
one `.cma`; the final link (`entry_core.ml` + `entry_lite_jsoo.ml`)
runs WITHOUT `-linkall`, so only the units those two files transitively
reference get pulled from the archive — that module-level omission is
the lite bundle's size lever (js_of_ocaml's own function-level
dead-code elimination runs on top of it). `js_of_ocaml` emits
`docs/fstar-extracted/factoidal-npm-entry-lite.js`.

### 2. `wasm-factoidal` step — wasm mirrors

After the existing npm-entry wasm block (guarded on `npm_entry.byte`
existing), a second block (guarded on `npm_entry_lite.byte` existing)
mirrors it for the lite bytecode: same `wasm_of_ocaml compile`
arguments, same `wasm_stub_shims.py` patch, output
`docs/fstar-extracted/factoidal-npm-entry-lite.wasm.js` +
`.wasm.assets/`.

### 3. `npm` step — stage into npm/factoidal/

Next to the existing full-bundle copy block, an optional-if-present
block copies `factoidal-npm-entry-lite.js`, `.wasm.js` and
`.wasm.assets/` into `npm/factoidal/`, same pattern, same messages.
`npm/factoidal/package.json`'s `files` list, `lib/api.js` and the
typed wrapper for the lite profile are a later task (owned by a
parallel change — this split's job stops at the OCaml entries, the
build wiring, and the rebuilt bundles).

## What flips on after the build

- `npm/factoidal/test/api.test.js` — the three tests currently skipped
  with reason "pending npm-entry build": CONSTRUCT -> Dataset, UPDATE,
  and RDFC-1.0 canonicalize (canonicalize alternatively flips on when
  the plain CLI bundle is rebuilt, since `--canonicalize` is already in
  `factoidal_cli.ml`, commit 42c7fd3 — the committed
  `docs/fstar-extracted/factoidal.js` predates it).
- The API stops argv-driving the CLI bundle for query/parse and uses
  the persistent ABI (one bundle eval per process instead of one per
  call).
- Dataset handles let a caller amortise parse + index cost across many
  queries against the same data (`bin/npm-entry/smoke.mjs`'s item 8
  measures the stateless-vs-handle timing difference).

## Smoke checks

`bin/npm-entry/smoke.mjs` (`node bin/npm-entry/smoke.mjs
[bundle-path]`, default the full bundle) runs the behavioral checks
for strict parsing, lenient `parseDocument`, dataset handles, prefix/
shorthand-aware Turtle serialization, and (against the full bundle
only) a diff against the previously committed bundle's `queryDataset`/
`updateDataset` answers. Run it against BOTH
`docs/fstar-extracted/factoidal-npm-entry.js` and
`factoidal-npm-entry-lite.js` after any rebuild — profile-specific
checks (full has `shaclValidate`, lite routes `rdfxml`/`jsonld` to a
"load the full bundle" error) branch on the bundle's own
`e.profile`.
