// Shared test setup: pin the engine bundles to the build of record.
//
// In the repo tree the package-local factoidal.js may be stale (it is
// refreshed by `build-ocaml.sh npm` at packaging time — and is itself
// always a copy of docs/fstar-extracted/), while docs/fstar-extracted/
// holds the latest `build-ocaml.sh js` output. Prefer the docs copy
// whenever it exists; in a published tarball it doesn't and the
// package-local copy is used. (Mtime comparison is useless here: a
// fresh clone stamps every file with the same checkout time.)

'use strict';

const fs = require('node:fs');
const path = require('node:path');

const PKG_ROOT = path.resolve(__dirname, '..');
const DOCS = path.resolve(PKG_ROOT, '..', '..', 'docs', 'fstar-extracted');

function preferFresh(envName, filename) {
  if (process.env[envName]) return;
  const docsCopy = path.join(DOCS, filename);
  if (fs.existsSync(docsCopy)) process.env[envName] = docsCopy;
}

preferFresh('FACTOIDAL_JS_BUNDLE', 'factoidal.js');
preferFresh('FACTOIDAL_WASM_BUNDLE', 'factoidal.wasm.js');
preferFresh('FACTOIDAL_NPM_ENTRY', 'factoidal-npm-entry.js');
preferFresh('FACTOIDAL_NPM_ENTRY_WASM', 'factoidal-npm-entry.wasm.js');

const PENDING = 'pending npm-entry build';

module.exports = { PENDING };
