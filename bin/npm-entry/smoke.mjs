#!/usr/bin/env node
// bin/npm-entry/smoke.mjs — behavioral smoke checks for the npm-entry
// bundles (https://github.com/danbri/factoidal/issues/344,
// https://github.com/danbri/factoidal/issues/680,
// https://github.com/danbri/factoidal/issues/681,
// https://github.com/danbri/factoidal/issues/684).
//
// Runs directly against a built js_of_ocaml bundle (no npm package
// wrapper involved) — the ABI entry_jsoo.ml / entry_lite_jsoo.ml
// export as the JS global `factoidalNpmEntry`.
//
// Usage:
//   node bin/npm-entry/smoke.mjs [bundle-path]
//
// bundle-path defaults to docs/fstar-extracted/factoidal-npm-entry.js
// (the full bundle) relative to the repository root. Pass
// docs/fstar-extracted/factoidal-npm-entry-lite.js (or any other path)
// to run the same suite against the lite bundle; profile-specific
// checks (see below) branch on `e.profile` so ONE script covers both.
//
// Exits 0 when every check passes, 1 otherwise (each failure is
// printed with FAIL and the mismatch).

import { createRequire } from 'node:module';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
import { performance } from 'node:perf_hooks';

const require = createRequire(import.meta.url);
const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, '..', '..');

const bundlePathArg = process.argv[2];
const bundlePath = bundlePathArg
  ? path.resolve(process.cwd(), bundlePathArg)
  : path.join(repoRoot, 'docs', 'fstar-extracted', 'factoidal-npm-entry.js');

function loadBundle(p) {
  const mod = require(p);
  const e = (mod && mod.factoidalNpmEntry) || globalThis.factoidalNpmEntry;
  if (!e) {
    throw new Error(`${p}: module did not export factoidalNpmEntry`);
  }
  return e;
}

const e = loadBundle(bundlePath);

let passCount = 0;
let failCount = 0;

function check(name, cond, detail) {
  if (cond) {
    passCount += 1;
    console.log(`ok   - ${name}`);
  } else {
    failCount += 1;
    console.log(`FAIL - ${name}`);
    if (detail !== undefined) {
      console.log(`       ${detail}`);
    }
  }
}

function parseEnvelope(text) {
  try {
    return JSON.parse(text);
  } catch (err) {
    throw new Error(`could not JSON.parse envelope: ${text}\n${err}`);
  }
}

console.log(`=== bin/npm-entry/smoke.mjs against ${bundlePath} ===`);
console.log(`abiVersion=${e.abiVersion} profile=${e.profile}`);

// ---------------------------------------------------------------------
// 1. Garbage input rejects at line 1, column 1, offset 0.
// ---------------------------------------------------------------------
{
  const r = parseEnvelope(e.parseToDatasetJson('this is not turtle', 'turtle', ''));
  check('1. garbage input: ok:false', r.ok === false, JSON.stringify(r));
  check('1. garbage input: line 1', r.line === 1, JSON.stringify(r));
  check('1. garbage input: column 1', r.column === 1, JSON.stringify(r));
  check('1. garbage input: offset 0', r.offset === 0, JSON.stringify(r));
}

// ---------------------------------------------------------------------
// 2. A missing "." on line 2 rejects at line 3 (the parser cannot know
//    the statement was unterminated until it fails to find one).
// ---------------------------------------------------------------------
const missingDotTurtle =
  '@prefix ex: <http://example.org/> .\nex:a ex:p ex:b\nex:c ex:p ex:d .\n';
{
  const r = parseEnvelope(e.parseToDatasetJson(missingDotTurtle, 'turtle', ''));
  check('2. missing dot: ok:false', r.ok === false, JSON.stringify(r));
  check('2. missing dot: line 3', r.line === 3, JSON.stringify(r));
}

// ---------------------------------------------------------------------
// 3. The same input, lenient: recovers the one well-formed triple, one
//    diagnostic, and the declared prefix.
// ---------------------------------------------------------------------
{
  const r = parseEnvelope(
    e.parseDocument(missingDotTurtle, 'turtle', '', '{"lenient":true}')
  );
  check('3. lenient: ok:true', r.ok === true, JSON.stringify(r));
  check('3. lenient: count 1', r.count === 1, JSON.stringify(r));
  check(
    '3. lenient: diagnostics.length === 1',
    Array.isArray(r.diagnostics) && r.diagnostics.length === 1,
    JSON.stringify(r)
  );
  check(
    '3. lenient: prefixes.ex',
    r.prefixes && r.prefixes.ex === 'http://example.org/',
    JSON.stringify(r)
  );
}

// ---------------------------------------------------------------------
// 4. Relative IRI, no base, rejects with a message mentioning IRI
//    (https://github.com/danbri/factoidal/issues/344's acceptance case).
// ---------------------------------------------------------------------
{
  const r = parseEnvelope(e.parseToDatasetJson('<a> <b> <c> .\n', 'turtle', ''));
  check('4. relative IRI, no base: ok:false', r.ok === false, JSON.stringify(r));
  check(
    '4. relative IRI, no base: message mentions IRI',
    typeof r.error === 'string' && /IRI/.test(r.error),
    JSON.stringify(r)
  );
}

// ---------------------------------------------------------------------
// 5. Valid Turtle with two prefixes: both labels reported, without
//    their trailing colon.
// ---------------------------------------------------------------------
const twoPrefixTurtle =
  '@prefix ex: <http://example.org/> .\n' +
  '@prefix foaf: <http://xmlns.com/foaf/0.1/> .\n' +
  'ex:alice foaf:knows ex:bob .\n';
{
  const r = parseEnvelope(e.parseToDatasetJson(twoPrefixTurtle, 'turtle', ''));
  check('5. two prefixes: ok:true', r.ok === true, JSON.stringify(r));
  check(
    '5. two prefixes: ex present, no colon',
    r.prefixes && r.prefixes.ex === 'http://example.org/',
    JSON.stringify(r)
  );
  check(
    '5. two prefixes: foaf present, no colon',
    r.prefixes && r.prefixes.foaf === 'http://xmlns.com/foaf/0.1/',
    JSON.stringify(r)
  );
}

// ---------------------------------------------------------------------
// 6. Dataset handles: open, query (join + ask), update, serialize
//    (plain + with options), close, then a post-close query fails.
// ---------------------------------------------------------------------
function makeTurtleFixture(n) {
  const lines = ['@prefix ex: <http://example.org/> .'];
  for (let i = 0; i < n; i += 1) {
    lines.push(`ex:s${i} ex:p ex:o${i} .`);
    lines.push(`ex:s${i} ex:knows ex:s${(i + 1) % n} .`);
  }
  return lines.join('\n') + '\n';
}

{
  const fixture = makeTurtleFixture(200);
  const openR = parseEnvelope(e.datasetOpen(fixture, 'turtle', ''));
  check('6. datasetOpen: ok:true', openR.ok === true, JSON.stringify(openR).slice(0, 200));
  check('6. datasetOpen: count 400', openR.count === 400, JSON.stringify(openR).slice(0, 200));
  const handle = openR.handle;

  const joinQuery =
    'PREFIX ex: <http://example.org/> ' +
    'SELECT ?s ?o ?friend WHERE { ?s ex:p ?o . ?s ex:knows ?friend }';
  const qR = parseEnvelope(e.datasetQuery(handle, joinQuery));
  check('6. datasetQuery join: ok:true, kind select', qR.ok === true && qR.kind === 'select',
    JSON.stringify(qR).slice(0, 200));
  check('6. datasetQuery join: 200 bindings',
    qR.srj && qR.srj.results && qR.srj.results.bindings.length === 200,
    JSON.stringify(qR).slice(0, 200));

  const askQuery = 'PREFIX ex: <http://example.org/> ASK { ex:s0 ex:p ex:o0 }';
  const askR = parseEnvelope(e.datasetQuery(handle, askQuery));
  check('6. datasetQuery ask: ok:true, kind ask, boolean true',
    askR.ok === true && askR.kind === 'ask' && askR.boolean === true,
    JSON.stringify(askR));

  const updR = parseEnvelope(
    e.datasetUpdate(handle, 'PREFIX ex: <http://example.org/> INSERT DATA { ex:extra ex:p ex:extra }')
  );
  check('6. datasetUpdate: ok:true, count 401', updR.ok === true && updR.count === 401,
    JSON.stringify(updR));

  const serR = parseEnvelope(e.datasetSerialize(handle, 'turtle'));
  check('6. datasetSerialize turtle: ok:true, uses ex: prefix',
    serR.ok === true && typeof serR.turtle === 'string' && /@prefix ex:/.test(serR.turtle),
    JSON.stringify(serR).slice(0, 200));

  const serWithR = parseEnvelope(
    e.datasetSerializeWith(
      handle,
      'turtle',
      '{"prefixes":{"zz":"http://example.org/"},"literalShorthand":false}'
    )
  );
  check(
    '6. datasetSerializeWith: uses zz: label',
    serWithR.ok === true && /@prefix zz:/.test(serWithR.turtle),
    JSON.stringify(serWithR).slice(0, 200)
  );

  const closeR = parseEnvelope(e.datasetClose(handle));
  check('6. datasetClose: ok:true', closeR.ok === true, JSON.stringify(closeR));

  const postCloseR = parseEnvelope(e.datasetQuery(handle, askQuery));
  check(
    '6. post-close datasetQuery: unknown dataset handle',
    postCloseR.ok === false && /unknown dataset handle/.test(postCloseR.error),
    JSON.stringify(postCloseR)
  );
}

// ---------------------------------------------------------------------
// 7. serializeTurtleWith: caller prefix used, no auto ns1: for the
//    same namespace.
// ---------------------------------------------------------------------
{
  const nq = '<http://example.org/s> <http://example.org/p> <http://example.org/o> .\n';
  const r = parseEnvelope(
    e.serializeTurtleWith(nq, '{"prefixes":{"ex":"http://example.org/"}}')
  );
  check('7. serializeTurtleWith: ok:true', r.ok === true, JSON.stringify(r));
  check('7. serializeTurtleWith: @prefix ex: present', /@prefix ex:/.test(r.turtle), r.turtle);
  check('7. serializeTurtleWith: no ns1: label', !/\bns1:/.test(r.turtle), r.turtle);
}

// ---------------------------------------------------------------------
// 8. Timing: stateless queryDataset (re-parse + rebuild index every
//    call) vs. datasetQuery on a handle (cached backend). Medians are
//    printed for the report / design record, not asserted (a timing
//    number is a measurement, never a pass/fail gate).
// ---------------------------------------------------------------------
function median(xs) {
  const sorted = [...xs].sort((a, b) => a - b);
  const mid = Math.floor(sorted.length / 2);
  return sorted.length % 2 === 0 ? (sorted[mid - 1] + sorted[mid]) / 2 : sorted[mid];
}

{
  const bigFixture = makeTurtleFixture(1000); // 1000 * 2 = 2000 triples
  const parsed = parseEnvelope(e.parseToDatasetJson(bigFixture, 'turtle', ''));
  check('8. 2000-triple fixture parses: ok:true, count 2000',
    parsed.ok === true && parsed.count === 2000, JSON.stringify(parsed).slice(0, 200));
  const nquads = parsed.nquads;

  const joinQuery =
    'PREFIX ex: <http://example.org/> ' +
    'SELECT ?s ?o ?friend WHERE { ?s ex:p ?o . ?s ex:knows ?friend }';

  const statelessTimes = [];
  for (let i = 0; i < 20; i += 1) {
    const t0 = performance.now();
    const r = parseEnvelope(e.queryDataset(nquads, joinQuery));
    const t1 = performance.now();
    if (r.ok !== true) throw new Error(`stateless queryDataset failed: ${JSON.stringify(r)}`);
    statelessTimes.push(t1 - t0);
  }

  const openR = parseEnvelope(e.datasetOpen(bigFixture, 'turtle', ''));
  const handle = openR.handle;
  const handleTimes = [];
  for (let i = 0; i < 20; i += 1) {
    const t0 = performance.now();
    const r = parseEnvelope(e.datasetQuery(handle, joinQuery));
    const t1 = performance.now();
    if (r.ok !== true) throw new Error(`datasetQuery failed: ${JSON.stringify(r)}`);
    handleTimes.push(t1 - t0);
  }
  e.datasetClose(handle);

  const statelessMedian = median(statelessTimes);
  const handleMedian = median(handleTimes);
  console.log(
    `8. timing (2000-triple two-pattern join, 20 runs each): ` +
      `stateless queryDataset median ${statelessMedian.toFixed(3)} ms, ` +
      `handle datasetQuery median ${handleMedian.toFixed(3)} ms`
  );
}

// ---------------------------------------------------------------------
// 9. Profile-specific: lite has no entry_extras.ml surface and routes
//    rdfxml/jsonld to the "load the full bundle" error; full has both.
// ---------------------------------------------------------------------
if (e.profile === 'lite') {
  const r = parseEnvelope(e.parseToDatasetJson('<rdf:RDF/>', 'rdfxml', ''));
  check('9. lite: rdfxml routing error', r.ok === false, JSON.stringify(r));
  check(
    '9. lite: rdfxml routing error names full bundle',
    typeof r.error === 'string' && /factoidal-npm-entry\.js/.test(r.error),
    JSON.stringify(r)
  );
  check('9. lite: shaclValidate absent', typeof e.shaclValidate === 'undefined');
  check('9. lite: profile === "lite"', e.profile === 'lite');
} else if (e.profile === 'full') {
  check('9. full: profile === "full"', e.profile === 'full');
  check('9. full: shaclValidate is a function', typeof e.shaclValidate === 'function');
} else {
  check('9. profile is "lite" or "full"', false, `profile=${e.profile}`);
}

// ---------------------------------------------------------------------
// 10. Stateless queryDataset/updateDataset answer exactly as before
//     (full bundle only — compared against the previously committed
//     bundle at the fixed main-worktree path).
// ---------------------------------------------------------------------
if (e.profile === 'full') {
  const oldBundlePath = '/home/user/factoidal/npm/factoidal/factoidal-npm-entry.js';
  try {
    const oldE = loadBundle(oldBundlePath);
    const nq =
      '<http://example.org/a> <http://example.org/p> <http://example.org/b> .\n' +
      '<http://example.org/b> <http://example.org/p> <http://example.org/c> .\n';
    const query =
      'PREFIX ex: <http://example.org/> SELECT ?x ?y ?z WHERE { ?x ex:p ?y . ?y ex:p ?z }';
    const oldR = parseEnvelope(oldE.queryDataset(nq, query));
    const newR = parseEnvelope(e.queryDataset(nq, query));
    check(
      '10. queryDataset srj matches the previously committed bundle',
      JSON.stringify(oldR.srj) === JSON.stringify(newR.srj),
      `old=${JSON.stringify(oldR.srj)}\n       new=${JSON.stringify(newR.srj)}`
    );

    const updateText = 'PREFIX ex: <http://example.org/> INSERT DATA { ex:a ex:p ex:z }';
    const oldU = parseEnvelope(oldE.updateDataset(nq, updateText));
    const newU = parseEnvelope(e.updateDataset(nq, updateText));
    check(
      '10. updateDataset nquads matches the previously committed bundle',
      oldU.nquads === newU.nquads,
      `old=${JSON.stringify(oldU.nquads)}\n       new=${JSON.stringify(newU.nquads)}`
    );
  } catch (err) {
    check('10. old-bundle comparison', false, String(err));
  }
}

console.log(`=== ${passCount} pass, ${failCount} fail (out of ${passCount + failCount}) ===`);
process.exitCode = failCount === 0 ? 0 : 1;
