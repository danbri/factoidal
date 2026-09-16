// Pins every live cell in docs/web/hub/55-valis-a-drum-machine-in-rdf.md.
//
// The post fetches two vendored Valis Turtle files (third_party/valis/)
// relative to a `valisBase` cell that, in the browser, resolves from
// `location.href`. Node has no `location`, so this file redefines
// `valisBase` to a `file:` URL over the real vendored directory right
// after building the reactive post -- before reading any value -- and
// installs a `fetch` shim that answers `file:` URLs from disk and falls
// through to the real fetch() for anything else, per
// docs/web/hub/README.md's testing-discipline section.

import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import { NPM_FACTOIDAL_INDEX, extractObservableCells, extractObservableCellsWithFlags, runReactivePost, pretty } from './_helpers.mjs';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = path.join(__dirname, '..', '..');
const VALIS_DIR = path.join(REPO_ROOT, 'third_party', 'valis');

const POST_FILE = '55-valis-a-drum-machine-in-rdf.md';
const cells = extractObservableCells(POST_FILE);
const cellsWithFlags = extractObservableCellsWithFlags(POST_FILE);

const EXPECTED = JSON.parse(
  fs.readFileSync(path.join(__dirname, 'post55_expected.json'), 'utf8'));

// `valisBase` (a directory URL, trailing slash) over the vendored Turtle
// files, so the post's string-concatenation fetches ("vocabs/valis.ttl")
// resolve exactly as they do under the real "../assets/valis/" passthrough.
const VALIS_DIR_URL = pathToFileURL(VALIS_DIR).href.replace(/\/?$/, '/');

function installFetchShim() {
  const previousFetch = globalThis.fetch;
  globalThis.fetch = async (url) => {
    const u = String(url);
    if (u.startsWith('file:')) {
      const buf = await fs.promises.readFile(fileURLToPath(u));
      return new Response(buf);
    }
    return previousFetch(url);
  };
  return () => { globalThis.fetch = previousFetch; };
}

function buildPost() {
  const post = runReactivePost(cells, { fn: factoidal, pretty, html: (s) => s, md: (s) => s });
  // Before reading any value: redefine valisBase to the file: directory
  // URL. redefine() re-runs the named variable AND every cell that
  // references it, so ontologyText/circuitText's fetch() calls -- and
  // everything downstream -- see the vendored files on disk.
  post.redefine('valisBase', 'valisBase = ' + JSON.stringify(VALIS_DIR_URL));
  return post;
}

test('post55: post has 27 live cells', () => {
  assert.equal(cells.length, 27, `expected 27 live cells, found ${cells.length}`);
});

test('post55: the last cell is the closed, titled library cell (fence flags)', () => {
  const last = cellsWithFlags[cellsWithFlags.length - 1];
  assert.deepEqual(last.flags, { closed: true, title: 'Library: DAW helpers' });
  assert.match(last.source, /daw\s*=\s*\(\{/);
});

test('post55: ontology and circuit parse to the engine\'s own triple counts', async () => {
  const restoreFetch = installFetchShim();
  try {
    const post = buildPost();
    const ontology = await post.value('ontology');
    const circuit = await post.value('circuit');
    assert.equal(ontology.size, EXPECTED.ontologySize,
      `ontology.size is ${ontology.size}, expected pinned ${EXPECTED.ontologySize}`);
    assert.equal(circuit.size, EXPECTED.circuitSize,
      `circuit.size is ${circuit.size}, expected pinned ${EXPECTED.circuitSize}`);
  } finally {
    restoreFetch();
  }
});

test('post55: the port query returns rows, and Oscillator folds to a class with a 440 Hz frequency default', async () => {
  const restoreFetch = installFetchShim();
  try {
    const post = buildPost();
    const portRows = await post.value('portRows');
    assert.ok(portRows.length > 0, 'portRows should not be empty');
    assert.equal(portRows.length, EXPECTED.portRowsLength);

    const elementClasses = await post.value('elementClasses');
    const osc = elementClasses.classes.Oscillator;
    assert.ok(osc, 'elementClasses.classes.Oscillator should exist');
    const freq = osc.ports.find((p) => p.sym === 'frequency');
    assert.ok(freq, 'Oscillator should have a frequency port');
    assert.equal(freq.def, 440);
  } finally {
    restoreFetch();
  }
});

test('post55: the arc query returns rows, and circuitModel assembles elements and arcs', async () => {
  const restoreFetch = installFetchShim();
  try {
    const post = buildPost();
    const arcRows = await post.value('arcRows');
    assert.ok(arcRows.length > 0, 'arcRows should not be empty');
    assert.equal(arcRows.length, EXPECTED.arcRowsLength);

    const model = await post.value('model');
    assert.equal(model.elements.length, EXPECTED.modelElementsLength);
    assert.equal(model.arcs.length, EXPECTED.modelArcsLength);
  } finally {
    restoreFetch();
  }
});

test('post55: the UPDATE keeps the triple count fixed, and the Turtle output re-parses to the same canonical graph', async () => {
  const restoreFetch = installFetchShim();
  try {
    const post = buildPost();
    const circuit = await post.value('circuit');
    const edited = await post.value('edited');
    assert.equal(edited.size, circuit.size,
      'edited.size should equal circuit.size -- the UPDATE deletes one triple and inserts one');

    const turtleOut = await post.value('turtleOut');
    assert.match(turtleOut, /440\.0/);

    const reparsed = await factoidal.parse(turtleOut, { format: 'turtle' });
    const canonReparsed = await factoidal.canonicalize(reparsed);
    const canonEdited = await factoidal.canonicalize(edited);
    assert.equal(canonReparsed, canonEdited,
      'turtleOut should re-parse to a dataset canonically identical to edited');
  } finally {
    restoreFetch();
  }
});

test('post55: the audio cell returns {skipped: "no AudioContext"} under Node', async () => {
  const restoreFetch = installFetchShim();
  try {
    const post = buildPost();
    const audioCellName = post.names[post.names.length - 2]; // last cell before the closed daw library cell
    const result = await post.value(audioCellName);
    assert.deepEqual(result, { skipped: 'no AudioContext' });
  } finally {
    restoreFetch();
  }
});

test('post55: apiItems matches the pinned probe (edit post55_expected.json deliberately when an engine improvement lands)', async () => {
  const restoreFetch = installFetchShim();
  try {
    const post = buildPost();
    const apiItems = await post.value('apiItems');
    assert.deepEqual(apiItems, EXPECTED.apiItems);
  } finally {
    restoreFetch();
  }
});

test('post55: timings covers all six measured steps', async () => {
  const restoreFetch = installFetchShim();
  try {
    const post = buildPost();
    const timings = await post.value('timings');
    assert.equal(timings.kind, 'table');
    const steps = timings.rows.map((row) => row[0]).sort();
    assert.deepEqual(steps, [
      'ontology parse', 'circuit parse', 'port query', 'arc query', 'update', 'serialize',
    ].sort(), 'timings should name exactly the six measured steps (order not asserted)');
  } finally {
    restoreFetch();
  }
});
