// Pins every live cell in docs/web/hub/24-hdt-header-dictionary-triples.md.
//
// The post's three cells fetch the in-repo RML-Core HDT fixture and
// hand its bytes to `fn.queryHdt(bytes, sparql)`, which encapsulates
// the `--data-hdt` argv+files primitive entirely -- the cell never
// builds a virtual path or fake-filesystem entry itself. In the
// browser `fn.queryHdt` (docs/_includes/hub.njk's adapter) is built on
// `Factoidal.runFactoidalCli` (browser.js), which drives the
// js_of_ocaml CLI bundle; a hub cell has no js bundle here, so this
// test provides a Node-side `fn.queryHdt` that materializes the bytes
// to a temp file and shells out to the SAME CLI via the committed
// native binary (bin/<platform>/factoidal) -- mirroring the adapter's
// own logic (byte-pack, run --data-hdt, reshape SRJ bindings into
// Map<string,Term> rows) one layer down. `fetch` is stubbed to serve
// the local fixture bytes (the cell's page-relative URL is ignored).
// `Plot` is an echo stub capturing marks/data so the histogram cell's
// derived data can be asserted (same browser-vs-test duality
// documented for pretty()/Plot in hub/README.md and post23_test.mjs).

import { createRequire } from 'node:module';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { execFileSync } from 'node:child_process';
import { extractObservableCells, runObservableCell, pretty } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const require = createRequire(import.meta.url);
const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = path.join(__dirname, '..', '..');
const POST_FILE = '24-hdt-header-dictionary-triples.md';

const HDT_FIXTURE = path.join(
  REPO_ROOT, 'third_party', 'testing', 'hdt', 'rml-core-ontology.hdt');

// Locate the committed native binary for this platform (same layout
// bin/<platform>/ the CLAUDE.md rule-#9 committed binaries use).
function nativeBinary() {
  const candidates = [
    path.join(REPO_ROOT, 'bin', 'linux-x86_64', 'factoidal'),
    path.join(REPO_ROOT, 'ocaml-output', 'factoidal'),
  ];
  for (const c of candidates) if (fs.existsSync(c)) return c;
  throw new Error('native factoidal binary not found (build it first)');
}

// Node-side stand-in for browser.js's runFactoidalCli(args, files):
// write each virtual file to a real temp path, rewrite any arg equal to
// the virtual name, run the native CLI, and return {stdout,stderr,exitCode}.
async function runFactoidalCli(args, files) {
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'hub-hdt-'));
  let realArgs = args.slice();
  for (const f of files || []) {
    const real = path.join(tmpDir, path.basename(f.name));
    fs.writeFileSync(real, Buffer.from(f.content, 'latin1'));
    realArgs = realArgs.map((a) => (a === f.name ? real : a));
  }
  let stdout = '', stderr = '', exitCode = 0;
  try {
    stdout = execFileSync(nativeBinary(), realArgs,
      { encoding: 'utf8', maxBuffer: 1 << 26 });
  } catch (e) {
    stdout = e.stdout ? e.stdout.toString() : '';
    stderr = e.stderr ? e.stderr.toString() : '';
    exitCode = typeof e.status === 'number' ? e.status : 1;
  } finally {
    fs.rmSync(tmpDir, { recursive: true, force: true });
  }
  return { stdout, stderr, exitCode };
}

// Mirrors docs/_includes/hub.njk's `fn` adapter's srjTermToFn(): SRJ
// term -> RDF/JS-shaped term ({termType, value, [language], [datatype]}).
const XSD_STRING = 'http://www.w3.org/2001/XMLSchema#string';
const RDF_LANGSTRING = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#langString';
function srjTermToFn(t) {
  if (t.type === 'uri') return { termType: 'NamedNode', value: t.value };
  if (t.type === 'bnode') return { termType: 'BlankNode', value: t.value };
  const language = t['xml:lang'] || '';
  const datatype = t.datatype || (language ? RDF_LANGSTRING : XSD_STRING);
  return { termType: 'Literal', value: t.value, language, datatype: { termType: 'NamedNode', value: datatype } };
}

let _queryHdtSeq = 0;

// Node-side stand-in for docs/_includes/hub.njk's `fn.queryHdt(bytes,
// sparql)`: byte-pack, drive `--data-hdt` through runFactoidalCli()
// (the native-binary primitive above), and reshape the SPARQL Results
// JSON into Bindings[]/boolean -- the exact same two-step the real
// adapter performs over `Factoidal.queryHdt`/`Factoidal.runFactoidalCli`.
async function queryHdt(bytes, sparql) {
  const u8 = bytes instanceof Uint8Array ? bytes : new Uint8Array(bytes);
  let content = '';
  for (let i = 0; i < u8.length; i++) content += String.fromCharCode(u8[i]);
  const virtPath = `/static/fn-queryhdt-test-${_queryHdtSeq++}.hdt`;
  const res = await runFactoidalCli(
    ['--data-hdt', virtPath, '-e', sparql, '-o', 'json'],
    [{ name: virtPath, content }]);
  if (res.exitCode !== 0) {
    throw new Error('queryHdt failed: ' + (res.stderr || res.stdout));
  }
  const json = JSON.parse(res.stdout.slice(res.stdout.indexOf('{'), res.stdout.lastIndexOf('}') + 1));
  if (typeof json.boolean === 'boolean') return json.boolean;
  const rows = (json.results && json.results.bindings) || [];
  return rows.map((row) => {
    const map = new Map();
    for (const [name, term] of Object.entries(row)) map.set(name, srjTermToFn(term));
    return map;
  });
}

const fn = { queryHdt };

// Echo stub for the vendored Observable Plot (as in post23_test.mjs).
const Plot = {
  plot: (spec) => ({ isPlot: true, ...spec }),
  barX: (data, options) => ({ mark: 'barX', data, options }),
  text: (data, options) => ({ mark: 'text', data, options }),
  ruleX: (data, options) => ({ mark: 'ruleX', data, options }),
};

// Serve the local HDT fixture for the cells' page-relative fetch().
const realFetch = globalThis.fetch;
globalThis.fetch = async () => {
  const buf = fs.readFileSync(HDT_FIXTURE);
  const ab = buf.buffer.slice(buf.byteOffset, buf.byteOffset + buf.byteLength);
  return { ok: true, async arrayBuffer() { return ab; } };
};
test.after(() => { globalThis.fetch = realFetch; });

const cells = extractObservableCells(POST_FILE);
const B = { fn, pretty, Plot };

test('post24: post has 3 live cells', () => {
  assert.equal(cells.length, 3, `expected 3 live cells, found ${cells.length}`);
});

test('post24 cell 1 (count triples): 343', async () => {
  const result = await runObservableCell(cells[0], B);
  assert.equal(result, 343);
});

test('post24 cell 2 (owl:Class labels): pretty table including RML classes', async () => {
  const result = await runObservableCell(cells[1], B);
  assert.equal(result.kind, 'table');
  assert.deepEqual(result.columns, ['class', 'label']);
  assert.ok(result.rows.length >= 20, `expected >= 20 class rows, got ${result.rows.length}`);
  const labels = result.rows.map((r) => r[1]);
  for (const expected of ['Triples Map', 'Subject Map', 'Object Map']) {
    assert.ok(labels.includes(expected), `missing class label ${expected}`);
  }
});

test('post24 cell 3 (predicate histogram): rdf:type bar at 84', async () => {
  const result = await runObservableCell(cells[2], B);
  assert.equal(result.isPlot, true);
  const bar = result.marks.find((m) => m.mark === 'barX');
  assert.ok(bar, 'expected a barX mark');
  assert.ok(bar.data.length >= 1 && bar.data.length <= 8, 'top-8 predicate bars');
  const typeBar = bar.data.find((d) => d.predicate === 'type');
  assert.ok(typeBar, 'expected an rdf:type bar');
  assert.equal(typeBar.count, 84);
  // Bars are sorted descending, so rdf:type is the tallest (first).
  assert.equal(bar.data[0].predicate, 'type');
});

// Coverage gap this closes: the three cell tests above shell out to the
// committed NATIVE binary (runFactoidalCli -> execFileSync). The browser
// hub runs the js_of_ocaml BUNDLE instead, and the bundle diverges from
// native exactly where an F* value extracts through stdint's Uint32,
// whose C externals (uint32_xor, ...) have no js_of_ocaml realisation.
// HDT.Container's CRC16 (and HDT.Dictionary's CRC8/CRC32C) used
// FStar.UInt32, so opening any HDT file aborted in-browser with
// Failure("uint32_xor not implemented") -> empty stdout -> the cell's
// JSON.parse threw "Unexpected EOF", while every native test stayed
// green. This case drives the ACTUAL bundle the way browser.js does
// (engine-js.js runCli over the '/static/' fake device) so a
// native-only regression can never hide here again.
test('post24: HDT count is 343 through the js_of_ocaml bundle (not just native)', () => {
  const ejs = require(
    path.join(REPO_ROOT, 'npm', 'factoidal', 'lib', 'engine-js.js'));
  const buf = fs.readFileSync(HDT_FIXTURE);
  // Bundle fake-filesystem content is a byte-per-charCode string (latin1),
  // matching how browser.js hands fetched bytes to runFactoidalCli.
  let content = '';
  for (let i = 0; i < buf.length; i++) content += String.fromCharCode(buf[i]);

  const res = ejs.runCli(
    ['--data-hdt', '/static/h.hdt',
     '-e', 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }',
     '-o', 'json'],
    [{ name: '/static/h.hdt', content }]);

  assert.equal(res.exitCode, 0,
    `bundle HDT query failed (exit ${res.exitCode}): ${res.stdout}${res.stderr}`);
  // Regression pin: the pre-fix bundle emitted "uint32_xor not implemented".
  assert.ok(!/not implemented/.test(res.stdout + res.stderr),
    `bundle hit an unrealised external: ${res.stdout}${res.stderr}`);
  const json = JSON.parse(res.stdout);
  assert.equal(json.results.bindings[0].n.value, '343');
});
