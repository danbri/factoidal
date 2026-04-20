// Node-side smoke test for ../browser-wasm.js.
//
// We can't spin up a real browser here; instead we:
//   - feed the wasm.js source from docs/fstar-extracted/ (or the
//     npm package copy if build-ocaml.sh npm has run) via the
//     _setFactoidalWasmSource() test hook,
//   - inject an fs.readFileSync-based reader for the .wasm asset
//     via _setWasmAssetFallback().
//
// Both hooks are documented as test-only. A real browser uses fetch()
// and doesn't need them. Where possible we still exercise the full
// eval-the-IIFE path so this test catches regressions in argv/stdout
// plumbing, exit-sentinel handling, console hijack/restore, etc.
//
// Run: node test/smoke-wasm.js
// Exit code: 0 on all pass, 1 on any failure.

import { readFileSync, existsSync } from 'node:fs';
import { fileURLToPath }            from 'node:url';
import { dirname, join, resolve }   from 'node:path';
import { strict as assert }         from 'node:assert';

const here    = dirname(fileURLToPath(import.meta.url));
const pkgRoot = resolve(here, '..');
const repoRoot = resolve(pkgRoot, '..', '..');

// Source of truth for the wasm bundle. Prefer the in-package copy
// (what a downstream user would get); fall back to the repo-level
// build artifact.
function resolveWasmBundle() {
  const pkgCopy = join(pkgRoot, 'factoidal.wasm.js');
  if (existsSync(pkgCopy)) {
    return {
      jsPath:     pkgCopy,
      assetsDir:  join(pkgRoot, 'factoidal.wasm.assets'),
      source:    'npm/factoidal/',
    };
  }
  const docsCopy = join(repoRoot, 'docs', 'fstar-extracted', 'factoidal.wasm.js');
  return {
    jsPath:     docsCopy,
    assetsDir:  join(repoRoot, 'docs', 'fstar-extracted', 'factoidal.wasm.assets'),
    source:    'docs/fstar-extracted/',
  };
}

const bundle = resolveWasmBundle();
if (!existsSync(bundle.jsPath)) {
  console.error(`FATAL: cannot find factoidal.wasm.js at ${bundle.jsPath}`);
  console.error('  Run ./build-ocaml.sh wasm-factoidal to produce it, or');
  console.error('  ./build-ocaml.sh npm to copy it into npm/factoidal/.');
  process.exit(1);
}
if (!existsSync(bundle.assetsDir)) {
  console.error(`FATAL: cannot find factoidal.wasm.assets/ at ${bundle.assetsDir}`);
  process.exit(1);
}

console.log(`factoidal browser-wasm smoke test`);
console.log(`  bundle: ${bundle.source}factoidal.wasm.js`);

const wasmJsSource = readFileSync(bundle.jsPath, 'utf8');

// Read the .wasm asset by the filename the bundle requests. The
// loader currently passes something like
// "factoidal.wasm.assets/code-<hash>.wasm" — we strip back to just
// the basename and read from our known assets directory.
function readWasmAsset(assetSubPath) {
  // assetSubPath looks like "factoidal.wasm.assets/code-XXXX.wasm"
  const basename = assetSubPath.split('/').pop();
  const abs      = join(bundle.assetsDir, basename);
  if (!existsSync(abs)) {
    throw new Error(`wasm asset not found: ${abs}`);
  }
  return readFileSync(abs); // Buffer — Response accepts Buffer fine.
}

const mod = await import(new URL('../browser-wasm.js', import.meta.url));
const { query, _setFactoidalWasmSource, _setWasmAssetFallback } = mod;
_setFactoidalWasmSource(wasmJsSource);
_setWasmAssetFallback(readWasmAsset);

const TTL = `
  @prefix ex:   <http://example.org/> .
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:knows ex:bob .
  ex:bob   a foaf:Person ; foaf:name "Bob"   .
  ex:carol a foaf:Person ; foaf:name "Carol"@en .
`;

const RDFS_TTL = `
  @prefix schema: <http://schema.org/> .
  @prefix rdfs:   <http://www.w3.org/2000/01/rdf-schema#> .
  @prefix ex:     <http://example.org/> .
  schema:Place   a rdfs:Class .
  schema:Hotel   rdfs:subClassOf schema:Place .
  ex:motel6      a schema:Hotel ; schema:name "Motel 6" .
`;

let pass = 0, fail = 0;

async function check(label, fn) {
  try {
    await fn();
    console.log(`  PASS  ${label}`);
    pass++;
  } catch (e) {
    console.log(`  FAIL  ${label}: ${e && e.message}`);
    if (e && e.stdout) console.log(`        stdout: ${e.stdout.slice(0, 200)}`);
    if (e && e.stderr) console.log(`        stderr: ${e.stderr.slice(0, 200)}`);
    if (e && e.stack)  console.log(`        ${e.stack.split('\n').slice(0, 4).join('\n        ')}`);
    fail++;
  }
}

// 1. Basic SELECT, default options.
await check('SELECT returns bindings', async () => {
  const r = await query(TTL, `
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    SELECT ?name WHERE { ?p foaf:name ?name }
  `);
  assert.ok(r && r.head,                'head present');
  assert.ok(Array.isArray(r.head.vars), 'head.vars array');
  assert.deepEqual(r.head.vars, ['name']);
  assert.equal(r.results.bindings.length, 3, 'three name bindings');
  const names = r.results.bindings.map(b => b.name.value).sort();
  assert.deepEqual(names, ['Alice', 'Bob', 'Carol']);
});

// 2. ASK — just assert shape + boolean type. Engine-correctness is
//    exercised by the main smoke test.
await check('ASK returns {head, boolean}', async () => {
  const r = await query(TTL, `
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    PREFIX ex:   <http://example.org/>
    ASK { ex:alice foaf:knows ex:bob }
  `);
  assert.ok(r && r.head,            'head present');
  assert.equal(typeof r.boolean, 'boolean', 'boolean field present');
  console.log(`        (engine returned boolean=${r.boolean})`);
});

// 3. RDFS entailment — should infer motel6 as schema:Place.
await check('entail=RDFS infers subclass', async () => {
  const q = `
    PREFIX schema: <http://schema.org/>
    SELECT ?s WHERE { ?s a schema:Place }
  `;
  const none = await query(RDFS_TTL, q);
  const rdfs = await query(RDFS_TTL, q, { entail: 'RDFS' });
  assert.equal(none.results.bindings.length, 0,
    'without RDFS, no direct schema:Place instances');
  assert.ok(rdfs.results.bindings.length >= 1,
    `RDFS should infer >=1 place, got ${rdfs.results.bindings.length}`);
});

console.log('');
console.log(`Results: ${pass} pass, ${fail} fail`);
process.exit(fail === 0 ? 0 : 1);
