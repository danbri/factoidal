# Vendored: wikifn-fstar compiled engine

- `wikifn_engine.js` — the js_of_ocaml build of
  [danbri/wikifn-fstar](https://github.com/danbri/wikifn-fstar): the
  Wikifunctions corpus translated to F\*, checked by F\*, extracted to
  OCaml, compiled to JavaScript. Loaded by hub post 35
  (`35-wikifunctions-extension-functions.md`) via the
  `fn.loadWikifunctions()` wrapper; exposes
  `globalThis.wikifnCompiledCall(zid, argsJson)` (compiled F\*
  functions by ZID) and `globalThis.wikifnEngineCall(zid, fuel,
  argsJson)` (the interpreter fallback).
- Snapshot: 2026-08-22 from
  https://danbri.github.io/wikifn-fstar/generated/wikifn_engine.js
  sha256 1e0b7f79b64857f51715… (`shasum -a 256` the file for the full
  digest).
- Licence: Apache-2.0 (`LICENSE` alongside; owner-confirmed
  2026-08-22 — wikifn-fstar is the same author's work, apart from
  wikifunctions.org corpus content and its own third_party).
- Refresh: re-download the URL above, update the sha256 here, re-run
  `node --test tests/hub/post35_test.mjs` and the browser sweep.
