// Pins every live cell in docs/web/hub/24-hdt-header-dictionary-triples.md.
//
// The post's three cells fetch the in-repo RML-Core HDT fixture, hand
// its bytes to `Factoidal.runFactoidalCli(['--data-hdt', ...])`, and
// render the results (a count, a pretty() class table, an Observable
// Plot predicate histogram). In the browser `Factoidal` is browser.js's
// namespace and `runFactoidalCli` drives the js_of_ocaml CLI bundle; a
// hub cell has no js bundle here, so this test provides a Node-side
// `Factoidal.runFactoidalCli` that materializes the virtual files to a
// temp dir and shells out to the SAME CLI via the committed native
// binary (bin/<platform>/factoidal). `fetch` is stubbed to serve the
// local fixture bytes (the cell's page-relative URL is ignored). `Plot`
// is an echo stub capturing marks/data so the histogram cell's derived
// data can be asserted (same browser-vs-test duality documented for
// pretty()/Plot in hub/README.md and post23_test.mjs).

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

const Factoidal = { runFactoidalCli };

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
const B = { Factoidal, pretty, Plot };

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
