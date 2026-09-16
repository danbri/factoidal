// Strict parsing (issue #344): every function that parses text input
// rejects with a positioned ParseError instead of silently dropping
// data. See README.md's "Parsing is strict by default" section and
// lib/api.js's entryResult()/ParseError.

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');

const factoidal = require('../index.js');
const wasmEngine = require('../wasm.js');

function assertParseError(err, who) {
  assert.equal(err.name, 'ParseError', `${who}: err.name`);
  assert.ok(err instanceof Error, `${who}: ParseError extends Error`);
  assert.equal(err instanceof factoidal.ParseError, true,
    `${who}: err instanceof the exported ParseError class`);
  assert.equal(typeof err.line, 'number', `${who}: err.line is a number`);
  assert.equal(typeof err.column, 'number', `${who}: err.column is a number`);
  assert.equal(typeof err.offset, 'number', `${who}: err.offset is a number`);
}

test('parse("this is not turtle") rejects with a positioned ParseError', async () => {
  await assert.rejects(
    factoidal.parse('this is not turtle', { format: 'turtle' }),
    (err) => { assertParseError(err, 'parse'); return true; });
});

test('a Turtle document missing one "." rejects with a positioned ParseError', async () => {
  const text =
    '@prefix ex: <http://example.org/> .\n' +
    'ex:a ex:p ex:o\n' +        // missing '.' here
    'ex:b ex:p ex:o2 .\n';
  await assert.rejects(
    factoidal.parse(text, { format: 'turtle' }),
    (err) => {
      assertParseError(err, 'missing-dot');
      assert.equal(err.line, 3, 'the parser reports the failure on the FOLLOWING line');
      return true;
    });
});

test('a relative IRI with no baseIRI rejects with a message mentioning IRI', async () => {
  await assert.rejects(
    factoidal.parse('<a> <b> <c> .', { format: 'turtle' }),
    /IRI/i);
});

test('N-Triples syntax errors reject with a positioned ParseError', async () => {
  await assert.rejects(
    factoidal.parse('<http://x/s> <http://x/p> .', { format: 'ntriples' }),
    (err) => { assertParseError(err, 'ntriples'); return true; });
});

test('N-Quads syntax errors reject with a positioned ParseError', async () => {
  await assert.rejects(
    factoidal.parse('<http://x/s> <http://x/p> .', { format: 'nquads' }),
    (err) => { assertParseError(err, 'nquads'); return true; });
});

test('TriG syntax errors reject with a positioned ParseError', async () => {
  await assert.rejects(
    factoidal.parse('@prefix ex: <http://x/> . GRAPH ex:g { ex:s ex:p', { format: 'trig' }),
    (err) => { assertParseError(err, 'trig'); return true; });
});

test('RDF/XML syntax errors reject (a message only, no position -- issue #344)', async () => {
  // From the W3C rdfms-syntax-incomplete negative suite (error002.rdf):
  // an rdf:nodeID value must match the XML Name production.
  const bad =
    '<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#">' +
    '<rdf:Description rdf:nodeID="333-555-666" /></rdf:RDF>';
  await assert.rejects(
    factoidal.parse(bad, { format: 'rdfxml' }),
    (err) => {
      assert.notEqual(err.name, 'ParseError',
        'RDF/XML failures carry a message only, so they stay a plain Error');
      assert.match(err.message, /nodeID/);
      return true;
    });
});

test('{lenient:true} returns the recoverable statements and one diagnostic', async () => {
  const text =
    '@prefix ex: <http://example.org/> .\n' +
    'ex:a ex:p ex:o .\n' +
    'BOGUS\n' +
    'ex:b ex:p ex:o2 .\n';
  const ds = await factoidal.parse(text, { format: 'turtle', lenient: true });
  assert.equal(ds.size, 2, 'both statements around the bad line recover');
  assert.equal(ds.diagnostics.length, 1);
  assert.equal(typeof ds.diagnostics[0].message, 'string');
  assert.equal(typeof ds.diagnostics[0].line, 'number');
  assert.equal(typeof ds.diagnostics[0].column, 'number');
  assert.equal(typeof ds.diagnostics[0].offset, 'number');
  // Strict parsing of the SAME text rejects outright.
  await assert.rejects(factoidal.parse(text, { format: 'turtle' }));
});

test("query('bad text', sparql) rejects the same way", async () => {
  await assert.rejects(
    factoidal.query('this is not turtle', 'SELECT * WHERE { ?s ?p ?o }', { format: 'turtle' }),
    (err) => { assertParseError(err, 'query'); return true; });
});

// ---------------------------------------------------------------------
// wasm parity: the same line/column. Skips cleanly (same pattern as
// wasm-parity.test.js) when Node < 22 or the wasm bundle is absent.
// ---------------------------------------------------------------------

const NODE_MAJOR = Number(process.versions.node.split('.')[0]);

function wasmSkipReason() {
  if (NODE_MAJOR < 22) {
    return `Node ${process.versions.node} < 22 (WasmGC needed)`;
  }
  if (!wasmEngine.wasmAvailable()) {
    return 'factoidal.wasm.js / .wasm asset not present ' +
      "(run 'build-ocaml.sh wasm-factoidal', then 'build-ocaml.sh npm')";
  }
  return null;
}

test('wasm engine: parse("this is not turtle") gives the same line/column as the js engine', async (t) => {
  const reason = wasmSkipReason();
  if (reason) { t.skip(reason); return; }

  let jsErr;
  try {
    await factoidal.parse('this is not turtle', { format: 'turtle' });
  } catch (e) {
    jsErr = e;
  }
  assert.ok(jsErr, 'js engine must have rejected');

  await assert.rejects(
    wasmEngine.parse('this is not turtle', { format: 'turtle' }),
    (err) => {
      assertParseError(err, 'wasm');
      assert.equal(err.line, jsErr.line);
      assert.equal(err.column, jsErr.column);
      assert.equal(err.offset, jsErr.offset);
      // Same class, since lib/api.js's ParseError is a module-level
      // singleton every buildApi() instance shares.
      assert.equal(wasmEngine.ParseError, factoidal.ParseError);
      return true;
    });
});
