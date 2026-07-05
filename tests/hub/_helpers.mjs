// Shared test setup for docs-hub post tests.
//
// Mirrors npm/factoidal/test/helpers.js's bundle-selection logic (prefer
// docs/fstar-extracted/'s freshly-built bundles over the package-local
// copies, which are only refreshed by build-ocaml.sh npm at packaging
// time) rather than duplicating it. Import this module FIRST, before
// importing npm/factoidal's index.mjs, so the FACTOIDAL_*_BUNDLE env
// vars are set before the engine loader reads them.
//
// Usage:
//   import '../_helpers.mjs';
//   import factoidal from '../../npm/factoidal/index.mjs';

import { createRequire } from 'node:module';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const require = createRequire(import.meta.url);

require(path.join(__dirname, '..', '..', 'npm', 'factoidal', 'test', 'helpers.js'));

export const NPM_FACTOIDAL_INDEX =
  path.join(__dirname, '..', '..', 'npm', 'factoidal', 'index.mjs');

// Root a hub post's shipped Markdown file, for pinning tests that
// extract and execute its live cells' exact source.
export const HUB_POST_DIR = path.join(__dirname, '..', '..', 'docs', 'web', 'hub');

/**
 * Extract every ```observable-js fenced code block's source, in
 * document order, from a hub post's Markdown file. Mirrors
 * docs/_includes/hub.njk's `code.language-observable-js` selector at
 * the source level (before Eleventy/Markdown-it render it to HTML).
 *
 * @param {string} postFilename e.g. '01-triples-rdf-from-first-principles.md'
 * @returns {string[]} cell source bodies, in order
 */
export function extractObservableCells(postFilename) {
  const text = fs.readFileSync(path.join(HUB_POST_DIR, postFilename), 'utf8');
  const re = /```observable-js\n([\s\S]*?)```/g;
  const cells = [];
  let m;
  while ((m = re.exec(text)) !== null) cells.push(m[1]);
  return cells;
}

/**
 * Execute one cell's source exactly the way docs/_includes/hub.njk's
 * mountCell() does in the browser: wrap the body in an async IIFE and
 * invoke it via `new Function(...bindingNames, body)`. This pins the
 * literal string that ships on the page -- not a hand-copied
 * approximation that can drift from it.
 *
 * @param {string} source   a cell body, as returned by extractObservableCells()
 * @param {Record<string, unknown>} bindings   e.g. { fn: factoidal }
 * @returns {Promise<unknown>} whatever the cell's `return` produces
 */
export async function runObservableCell(source, bindings) {
  const names = Object.keys(bindings);
  const values = names.map((n) => bindings[n]);
  const cellFn = new Function(
    ...names,
    'return (async () => {\n' + source + '\n})();'
  );
  return cellFn(...values);
}
