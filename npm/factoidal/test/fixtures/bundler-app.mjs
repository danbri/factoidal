// Fixture bundled by test/bundler-esbuild.test.mjs and by
// tests/web-demos/bundler_csp_smoke.sh (issue #682). Imports ONLY
// through the bundler-friendly, statically-importable subpaths -- no
// fetch, no `new Function(src)` eval anywhere in this file or in what
// it imports -- so the esbuild output runs under a page whose
// Content-Security-Policy has no `unsafe-eval`.
//
// Both callers bundle this exact file with esbuild
// (bundle: true, platform: 'browser', format: 'esm') and then run the
// output: the Node test captures stdout for the `ROW_COUNT:N` line
// this prints; the browser CSP smoke script reads `document.title`
// (set below when `document` exists) since a plain
// `<script type="module">` page has no module consumer to read an
// export from.

import { createApi } from '@factoidal/core/api';
import * as entryMod from '@factoidal/core/factoidal-npm-entry.js';

// factoidal-npm-entry.js is js_of_ocaml-generated CommonJS (no
// import/export syntax of its own): esbuild detects that and wraps it
// with its CJS-interop machinery, so the exact shape `import * as`
// produces depends on that interop layer's namespace-vs-default
// handling. Try the two shapes esbuild's `format: 'esm'` output is
// known to produce (the namespace object itself, and its `.default`)
// before falling back to the classic-script registration
// (globalThis.factoidalNpmEntry) documented in browser.js.
const abi = entryMod.factoidalNpmEntry
  ?? entryMod.default?.factoidalNpmEntry
  ?? globalThis.factoidalNpmEntry;

if (!abi) {
  throw new Error(
    'bundler-app fixture: could not find factoidalNpmEntry on the ' +
    'bundled factoidal-npm-entry.js import (checked entryMod, ' +
    'entryMod.default, globalThis) -- esbuild CJS-interop shape ' +
    'changed; see this file\'s comment.');
}

const factoidal = createApi(abi);

const TTL = `
  @prefix ex:   <http://example.org/> .
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:knows ex:bob .
  ex:bob   a foaf:Person ; foaf:name "Bob" .
  ex:carol a foaf:Person ; foaf:name "Carol" .
`;

export const EXPECTED_ROW_COUNT = 3;

const ds = await factoidal.parse(TTL, { format: 'turtle' });
const rows = await factoidal.query(ds,
  'PREFIX foaf: <http://xmlns.com/foaf/0.1/> SELECT ?p WHERE { ?p a foaf:Person }');

export const rowCount = rows.length;

// eslint-disable-next-line no-console -- the Node driver's assertion surface
console.log('ROW_COUNT:' + rowCount);

if (typeof document !== 'undefined') {
  document.title = String(rowCount);
}
