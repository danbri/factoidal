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

// The SAME vendored Observable runtime the browser hub loads, and the
// SAME project-owned reactive-cell compiler docs/_includes/hub.njk
// imports. Node can load both headless: the runtime's window_global
// falls back to globalThis and its animation-frame scheduler falls back
// to setImmediate, and the compiler is DOM-free. Importing them here
// lets a pinning test exercise the REAL reactive dataflow path (declare
// `ttl` in one cell, reference it from `graph = parse(ttl)` in the next)
// rather than only the standalone runObservableCell() path below.
import { Runtime } from '../../third_party/observable/dist/runtime.esm.js';
import { analyzeCell, cellInputs, makeDefinition } from '../../docs/web/hub/reactive-cells.mjs';

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
 * Build a headless reactive runtime module from a post's cell sequence,
 * exactly the way docs/_includes/hub.njk wires the browser: each cell
 * becomes a named Observable-runtime variable, its inputs inferred from
 * the SAME analyzeCell()/cellInputs() compiler the page uses. This is
 * the cross-cell path -- a cell `graph = fn.parse(ttl)` references the
 * `ttl` cell's value, the runtime topologically orders them, and
 * promise-valued cells resolve before their dependents run.
 *
 * `bindings` are the module-scope builtins (e.g. { fn, pretty, Plot }),
 * defined as named variables so cells can reference them by name.
 *
 * Returns `{ names, infos, value }` where `value(name)` resolves to a
 * named cell's (or an anonymous cell's fallback-named) current value --
 * `module.value()` computes the transitive dependency graph and awaits
 * any promise-valued variable, so a `SELECT` that depends on a parsed
 * graph that depends on Turtle text resolves through the whole chain.
 *
 * Anonymous cells (no `name =`) get a stable fallback name `cell<index>`
 * in document order, so a test can still read one by index if needed.
 *
 * @param {string[]} cells   cell bodies, as from extractObservableCells()
 * @param {Record<string, unknown>} bindings  builtins in scope, by name
 * @returns {{names: string[], infos: object[], value: (name: string) => Promise<unknown>}}
 */
export function runReactivePost(cells, bindings) {
  const runtime = new Runtime();
  const main = runtime.module();

  const knownNames = new Set(Object.keys(bindings));
  for (const [k, v] of Object.entries(bindings)) {
    main.variable().define(k, [], () => v);
  }

  const infos = cells.map((src) => analyzeCell(src));
  for (const info of infos) if (info.name) knownNames.add(info.name);

  let anon = 0;
  const names = infos.map((info) => {
    const runtimeName = info.name || `cell${anon++}`;
    const inputs = cellInputs(info, knownNames);
    main.variable().define(runtimeName, inputs, makeDefinition(inputs, info.body));
    return runtimeName;
  });

  return {
    names,
    infos,
    value: (name) => main.value(name),
    // Re-define a named cell in place (the Edit+Run path the page takes):
    // the runtime re-runs it AND every dependent that references its name.
    // Reading a downstream value afterward proves the propagation.
    redefine: (name, newSource) => {
      const info = analyzeCell(newSource);
      const inputs = cellInputs(info, knownNames);
      main.redefine(name, inputs, makeDefinition(inputs, info.body));
    },
  };
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
