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

/**
 * Node-side stub for docs/_includes/hub.njk's `pretty()` cell binding.
 *
 * The browser-side `pretty()` returns a DOM node (a styled <table>
 * wrapped for scrolling, or a styled <span> for scalars) so it can be
 * handed straight to the Observable Inspector. There is no DOM here,
 * so this stub implements the *same shape dispatch* (array of Map ->
 * bindings table; Dataset-like -> triples/quads table; array of plain
 * objects -> table from the union of keys; plain object -> key/value
 * table; scalar -> value; anything else -> unchanged) but returns a
 * plain, JSON-serializable structure instead of a node, so a pinned
 * `node:test` can assert on table shape without a browser:
 *
 *   { kind: 'table', columns: string[], rows: unknown[][] }
 *   { kind: 'value', value: string | number | boolean | bigint }
 *
 * See docs/web/hub/README.md's "The `pretty()` rendering option"
 * section for the full contract both implementations satisfy.
 *
 * @param {unknown} value
 * @returns {{kind: 'table', columns: string[], rows: unknown[][]} | {kind: 'value', value: unknown} | unknown}
 */
export function pretty(value) {
  function isPlainObject(v) {
    if (typeof v !== 'object' || v === null) return false;
    if (Array.isArray(v)) return false;
    if (v instanceof Map || v instanceof Set) return false;
    const proto = Object.getPrototypeOf(v);
    return proto === Object.prototype || proto === null;
  }
  function isDatasetLike(v) {
    return (
      typeof v === 'object' && v !== null && !Array.isArray(v) &&
      !(v instanceof Map) && !(v instanceof Set) &&
      typeof v.size === 'number' && typeof v[Symbol.iterator] === 'function'
    );
  }
  function termCell(t) {
    if (t && typeof t === 'object' && typeof t.termType === 'string') {
      if (t.termType === 'BlankNode') return '_:' + t.value;
      if (t.termType === 'Literal') {
        let text = '"' + t.value + '"';
        if (t.language) text += '@' + t.language;
        else if (t.datatype && t.datatype.value && t.datatype.value !== 'http://www.w3.org/2001/XMLSchema#string') {
          text += '^^' + t.datatype.value;
        }
        return text;
      }
      return t.value; // NamedNode
    }
    return t;
  }

  // (a) array of Map -- SPARQL bindings rows.
  if (Array.isArray(value) && value.length > 0 && value.every((r) => r instanceof Map)) {
    const columns = [];
    for (const row of value) {
      for (const k of row.keys()) if (!columns.includes(k)) columns.push(k);
    }
    const rows = value.map((row) => columns.map((c) => (row.has(c) ? termCell(row.get(c)) : '')));
    return { kind: 'table', columns, rows };
  }

  // (c) Dataset-like -- checked ahead of the plain-object-array case.
  if (isDatasetLike(value)) {
    const quads = [...value];
    const hasGraph = quads.some((q) => q && q.graph && q.graph.value);
    const columns = hasGraph ? ['s', 'p', 'o', 'g'] : ['s', 'p', 'o'];
    const rows = quads.map((q) => {
      const row = [termCell(q.subject), termCell(q.predicate), termCell(q.object)];
      if (hasGraph) row.push(q.graph ? termCell(q.graph) : '');
      return row;
    });
    return { kind: 'table', columns, rows };
  }

  // (b) array of plain objects -- table from the union of keys.
  if (Array.isArray(value) && value.length > 0 && value.every(isPlainObject)) {
    const columns = [];
    for (const obj of value) {
      for (const k of Object.keys(obj)) if (!columns.includes(k)) columns.push(k);
    }
    const rows = value.map((obj) => columns.map((k) => (k in obj ? obj[k] : '')));
    return { kind: 'table', columns, rows };
  }

  // (d) plain object -- two-column key/value table.
  if (isPlainObject(value)) {
    return { kind: 'table', columns: ['key', 'value'], rows: Object.entries(value) };
  }

  // (e) scalars/strings.
  if (
    typeof value === 'string' || typeof value === 'number' ||
    typeof value === 'boolean' || typeof value === 'bigint'
  ) {
    return { kind: 'value', value };
  }

  // (f) anything else -- unchanged.
  return value;
}
