# Changelog

## 0.1.0-alpha.0 — Initial scaffold, unpublished

Directory layout committed to the main repo under `npm/factoidal/`.
Not yet published to the npm registry.

- `package.json` with dual CJS (`index.js`) / ESM (`index.mjs`)
  entry points, a `browser` condition, and a TypeScript declaration
  file (`index.d.ts`).
- `index.js` wraps the js_of_ocaml-compiled `factoidal.js` bundle in
  an `async` `query(data, query, options)` API with `dataFormat`,
  `entail`, and `output` options.
- `browser.js` mirrors the same API for browsers, fetching
  `factoidal.js` via `fetch()` relative to the module URL.
- `build-ocaml.sh npm` target (in the repo root's
  `formal/fstar/build-ocaml.sh`) populates this directory from the
  existing extraction output.
