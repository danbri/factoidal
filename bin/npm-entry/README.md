# bin/npm-entry — js_of_ocaml / wasm_of_ocaml entry for the npm package

`entry_jsoo.ml` is a consumer entry point (rule #11: hand-written
OCaml consumers live in `bin/<consumer>/`) that exposes the
F\*-extracted engine to JavaScript as a persistent string/JSON ABI —
`factoidalNpmEntry.{parseToDatasetJson, queryDataset, askDataset,
updateDataset, serializeNQuads, canonicalizeToNQuads}`. The ABI
contract is documented in the header comment of
[`entry_jsoo.ml`](entry_jsoo.ml); the JavaScript consumer is
[`npm/factoidal/lib/api.js`](../../npm/factoidal/lib/api.js), which
falls back to argv-driving the CLI bundle until the entry bundle is
built.

The file type-checks against the current extraction output:

```sh
eval $(opam env --switch=fstar)
cd formal/fstar/ocaml-output
ocamlfind ocamlc -c -package fstar.lib,str,zarith,sha,digestif.c,js_of_ocaml \
  -I . -w -8-14-26 ../../../bin/npm-entry/entry_jsoo.ml
```

(verified clean on 2026-07-04 against the committed `.cmi` set; run
from a scratch dir with `-I ocaml-output` to avoid dropping artifacts
into the build tree).

## Build wiring for formal/fstar/build-ocaml.sh

Three edits, all inside existing steps. Line numbers refer to the
2026-07-04 state of the script.

### 1. `js` step — build `npm_entry.byte` + `factoidal-npm-entry.js`

Add to `JS_TARGETS` (line 816) so the freshness check covers the new
artifacts:

```sh
    npm_entry.byte
    ../../../docs/fstar-extracted/factoidal-npm-entry.js
```

Add to `JS_SOURCES` (line 822):

```sh
    ../../../bin/npm-entry/entry_jsoo.ml
```

After the `factoidal.byte` block (i.e. after `rm -f factoidal_serve.ml`
/ its error check, around line 883–890), add the bytecode build — note
the extra `js_of_ocaml` ocamlfind package, which is the only difference
from the factoidal.byte invocation, and that no serve stub is needed
(the entry links no `Factoidal_serve`):

```sh
    # Build npm-entry bytecode (bin/npm-entry/entry_jsoo.ml): the
    # persistent string/JSON ABI for the npm package. Needs the
    # js_of_ocaml library for Js.export / Js.wrap_callback.
    run_with_heartbeat "ocamlc npm_entry.byte" "_ocamlc_npm_entry.log" -- \
      ocamlfind ocamlc -package fstar.lib,str,zarith,sha,digestif.c,unix,js_of_ocaml -linkpkg -w -8-14-26 \
      -custom parquet_zstd_stubs_jsoo.c \
      "${FSTAR_MODULES[@]}" \
      ../../../bin/npm-entry/entry_jsoo.ml \
      -o npm_entry.byte
    grep -i error _ocamlc_npm_entry.log || true
```

After the `js_of_ocaml factoidal` block (line 911–921), add:

```sh
    run_with_heartbeat "js_of_ocaml npm-entry" "_jsoo_npm_entry.log" -- \
      js_of_ocaml \
      +zarith_stubs_js/biginteger.js \
      +zarith_stubs_js/runtime.js \
      fstar_int_stubs.js \
      fstar_hash_stubs.js \
      fstar_utf8_output_stubs.js \
      vendor/fzstd.umd.js \
      parquet_zstd_stubs.js \
      npm_entry.byte \
      -o ../../../docs/fstar-extracted/factoidal-npm-entry.js
    grep -v "Warning \[deprecated" _jsoo_npm_entry.log | grep -v "^$" || true
    echo "  Built: docs/fstar-extracted/factoidal-npm-entry.js ($(wc -c < ../../../docs/fstar-extracted/factoidal-npm-entry.js) bytes)"
```

### 2. `wasm-factoidal` step (line 985+) — wasm entry bundle

After the existing `wasm_of_ocaml factoidal` block (line 1009+), mirror
it for the entry (guarded on `npm_entry.byte` existing, same shims):

```sh
  if [[ -f npm_entry.byte ]]; then
    run_with_heartbeat "wasm_of_ocaml npm-entry" "_waoc_npm_entry.log" -- \
      wasm_of_ocaml compile \
      +zarith_stubs_js/biginteger.js \
      +zarith_stubs_js/runtime.js \
      wasm_runtime/zarith_runtime_wasm.js \
      wasm_runtime/zarith_runtime.wat \
      fstar_int_stubs.js \
      npm_entry.byte \
      -o ../../../docs/fstar-extracted/factoidal-npm-entry.wasm.js
    python3 wasm_stub_shims.py ../../../docs/fstar-extracted/factoidal-npm-entry.wasm.js
  fi
```

### 3. `npm` step (Step 6, line 1038+) — stage into npm/factoidal/

Next to the existing wasm copy block (line 1082 area), add
optional-if-present copies:

```sh
  if [[ -f "$JSDIR/factoidal-npm-entry.js" ]]; then
    cp "$JSDIR/factoidal-npm-entry.js" "$NPMDIR/factoidal-npm-entry.js"
  fi
  if [[ -f "$JSDIR/factoidal-npm-entry.wasm.js" ]]; then
    cp "$JSDIR/factoidal-npm-entry.wasm.js" "$NPMDIR/factoidal-npm-entry.wasm.js"
  fi
  if [[ -d "$JSDIR/factoidal-npm-entry.wasm.assets" ]]; then
    rm -rf "$NPMDIR/factoidal-npm-entry.wasm.assets"
    cp -R "$JSDIR/factoidal-npm-entry.wasm.assets" "$NPMDIR/factoidal-npm-entry.wasm.assets"
  fi
```

`npm/factoidal/package.json` already lists the three staged names in
`files`, and `npm/factoidal/lib/api.js` + `test/helpers.js` pick them
up automatically (env overrides `FACTOIDAL_NPM_ENTRY` /
`FACTOIDAL_NPM_ENTRY_WASM` exist for ad-hoc testing).

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
