# bin/npm-entry-core — parse/serialize-only js_of_ocaml entry (pilot)

`entry_core_jsoo.ml` is the measured pilot for
[`docs/designissues/2026-07-05-bundle-modularity.md`](../../docs/designissues/2026-07-05-bundle-modularity.md):
a consumer entry point (rule #11) exposing ONLY the parse/serialize
surface — `factoidalNpmEntryCore.{parseToDatasetJson,
serializeNQuads, serializeTurtle}` — so js_of_ocaml's whole-program
dead-code elimination strips SPARQL/OWL/SHACL/ShEx/RIF/RDF-XML/
JSON-LD/COTTAS out of the bundle.

**Not yet wired into `formal/fstar/build-ocaml.sh`.** The wiring
(an `ENTRY_POINTS` loop in the `js` step) lands with the
bundle-modularity implementation wave — see §8 of the design doc.
Until then the bundle is built manually as below.

Measured 2026-07-05: 190,367 B raw / 59,318 B gzip -9, vs the full
`factoidal-npm-entry.js` at 476,558 B raw / 144,265 B gzip -9
(40% raw, 41% gzipped). wasm_of_ocaml asset: 162,521 B vs 503,790 B.

## Manual build (scratch dir; matches build-ocaml.sh's js step)

Copy the module subset below plus this entry into a scratch dir
(never compile ad hoc inside `ocaml-output/` — it drops `.cmo`/`.cmi`
that poison the shared tree), then:

```sh
eval $(opam env --switch=fstar)
ocamlfind ocamlc -package fstar.lib,str,zarith,sha,digestif.c,unix,js_of_ocaml \
  -linkpkg -w -8-14-26 \
  RDF_Format.ml \
  RDF_Graph_Executable.ml RDF_List_Helpers.ml RDF_Bytes.ml \
  Parser_FastString.ml SPARQL11_IRI_Resolve.ml Parser_IRI.ml \
  RDF_NQuads_Serialize.ml \
  Parser_Combinators.ml Parser_TurtleScanner.ml Parser_NTriples.ml Parser_Turtle.ml \
  RDF_Turtle_Serialize.ml \
  Parser_NQuads.ml Parser_TriG.ml \
  SPARQL_JSON_Escape.ml \
  fstar_pure_hashes.ml \
  RDF_Dataset_Graphs.ml \
  RDF_Canonical.ml \
  RDF_Dataset_Merge.ml \
  entry_core_jsoo.ml \
  -o npm_entry_core.byte

js_of_ocaml \
  +zarith_stubs_js/biginteger.js \
  +zarith_stubs_js/runtime.js \
  fstar_int_stubs.js \
  fstar_hash_stubs.js \
  fstar_utf8_output_stubs.js \
  npm_entry_core.byte \
  -o factoidal-npm-entry-core.js
```

Differences from the full-entry invocation, both because
`Parquet_Footer` is not linked: no `-custom
parquet_zstd_stubs_jsoo.c`, and no `vendor/fzstd.umd.js` /
`parquet_zstd_stubs.js` shims. The three `fstar_*_stubs.js` files
live in `formal/fstar/ocaml-output/`.

Smoke test (Node): `require('./factoidal-npm-entry-core.js')`
returns `{ factoidalNpmEntryCore }` (also set on `globalThis` in
browsers); parse Turtle/N-Triples/N-Quads/TriG, re-serialize, and
confirm `parseToDatasetJson(x, "rdfxml", "")` returns the
`{"ok":false,...}` routing error, not a crash.
