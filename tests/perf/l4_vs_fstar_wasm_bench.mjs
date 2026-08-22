// Benchmark: the Lean 4 wasm engine (docs/web/hub/assets/l4/) vs the
// F*-extracted engines from the npm package — wasm_of_ocaml
// (factoidal/wasm, WasmGC) and js_of_ocaml (factoidal, plain JS).
//
// Workload: K people, each with a :name and an :age triple (2K triples
// total); the query is the two-pattern join from hub post 36
// (?s :name ?n . ?s :age ?a) — the same shape on all three engines.
//
// Measurement discipline (skills/perf-benchmarking):
// - each engine runs in its OWN child process, so RSS deltas are not
//   contaminated by a sibling engine's heap;
// - init, data ingestion, and query are timed separately;
// - query time is the median of 5 runs after 1 warmup;
// - the known asymmetry is REPORTED, not hidden: the Lean ABI takes
//   pre-built JSON triples (marshal cost inside the call, measured
//   separately as stringifyMs), while the F* engines parse Turtle
//   (parseMs). Neither number is comparable to the other's ingest —
//   only queryMs is like-for-like once both sides hold the data.
//
// Usage:
//   node tests/perf/l4_vs_fstar_wasm_bench.mjs            # driver: all engines, K=100,1000,4000
//   node tests/perf/l4_vs_fstar_wasm_bench.mjs <engine> <K>   # one engine, one size (child mode)
// Engines: l4 | fstar-wasm | fstar-js

import { spawnSync } from 'node:child_process';
import { statSync } from 'node:fs';
import { fileURLToPath } from 'node:url';

const HERE = fileURLToPath(new URL('.', import.meta.url));
const ROOT = new URL('../../', import.meta.url);
const p = (rel) => fileURLToPath(new URL(rel, ROOT));

const EX = 'http://example.org/';
const XSD_INT = 'http://www.w3.org/2001/XMLSchema#integer';

function makeData(K) {
  const triples = [];
  const ttlLines = [`@prefix : <${EX}> .`];
  for (let i = 0; i < K; i++) {
    const s = { type: 'uri', value: `${EX}p${i}` };
    triples.push({ subject: s, predicate: { type: 'uri', value: EX + 'name' },
      object: { type: 'literal', value: `Person ${i}` } });
    triples.push({ subject: s, predicate: { type: 'uri', value: EX + 'age' },
      object: { type: 'literal', value: String(18 + (i % 60)), datatype: XSD_INT } });
    ttlLines.push(`:p${i} :name "Person ${i}" ; :age ${18 + (i % 60)} .`);
  }
  return { triples, ttl: ttlLines.join('\n') };
}

const BGP = [
  { subject: { type: 'var', value: 's' }, predicate: { type: 'uri', value: EX + 'name' }, object: { type: 'var', value: 'n' } },
  { subject: { type: 'var', value: 's' }, predicate: { type: 'uri', value: EX + 'age' }, object: { type: 'var', value: 'a' } },
];
const SPARQL = `PREFIX : <${EX}> SELECT ?s ?n ?a WHERE { ?s :name ?n ; :age ?a }`;

const median = (xs) => [...xs].sort((a, b) => a - b)[Math.floor(xs.length / 2)];
const now = () => performance.now();
const mem = () => { const m = process.memoryUsage(); return { rss: m.rss, heapUsed: m.heapUsed }; };

async function runChild(engine, K) {
  const { triples, ttl } = makeData(K);
  const out = { engine, people: K, triples: 2 * K, node: process.version };
  const m0 = mem();

  let queryOnce; // () => Promise<number of rows>
  if (engine === 'l4') {
    const t0 = now();
    const { loadL4 } = await import(new URL('docs/web/hub/assets/l4/l4factoidal.js', ROOT).href);
    const l4 = await loadL4();
    out.initMs = +(now() - t0).toFixed(1);
    const ts = now();
    JSON.stringify(triples); // marshal share of each call, measured alone
    out.stringifyMs = +(now() - ts).toFixed(1);
    queryOnce = async () => {
      const doc = await l4.bgpQuery(triples, BGP);
      return doc.results.bindings.length;
    };
  } else {
    const t0 = now();
    const { createRequire } = await import('node:module');
    const require = createRequire(import.meta.url);
    const factoidal = require(p(engine === 'fstar-wasm' ? 'npm/factoidal/wasm.js' : 'npm/factoidal/index.js'));
    // First parse forces engine init; time it apart from data size by
    // parsing one triple first.
    await factoidal.parse(`<${EX}a> <${EX}b> "c" .`, { format: 'ntriples', baseIRI: EX });
    out.initMs = +(now() - t0).toFixed(1);
    const tp = now();
    const dataset = await factoidal.parse(ttl, { format: 'turtle', baseIRI: EX });
    out.parseMs = +(now() - tp).toFixed(1);
    queryOnce = async () => {
      const rows = await factoidal.query(dataset, SPARQL);
      return Array.isArray(rows) ? rows.length : rows.results.bindings.length;
    };
  }

  const m1 = mem();
  out.rows = await queryOnce(); // warmup + sanity
  const times = [];
  for (let i = 0; i < 5; i++) { const t = now(); await queryOnce(); times.push(now() - t); }
  out.queryMsMedian = +median(times).toFixed(1);
  out.queryMsAll = times.map((t) => +t.toFixed(1));
  const m2 = mem();
  out.rssAfterInitMB = +((m1.rss - m0.rss) / 1048576).toFixed(1);
  out.rssAfterQueriesMB = +((m2.rss - m0.rss) / 1048576).toFixed(1);
  out.heapAfterQueriesMB = +((m2.heapUsed - m0.heapUsed) / 1048576).toFixed(1);
  console.log(JSON.stringify(out));
}

function driver() {
  const sizes = process.env.BENCH_SIZES ? process.env.BENCH_SIZES.split(',').map(Number) : [100, 1000, 4000];
  const engines = ['l4', 'fstar-wasm', 'fstar-js'];
  const artifacts = {
    'l4 wasm': ['docs/web/hub/assets/l4/l4factoidal.wasm', 'docs/web/hub/assets/l4/l4factoidal.mjs', 'docs/web/hub/assets/l4/l4factoidal.js'],
    'fstar wasm_of_ocaml': ['npm/factoidal/factoidal-npm-entry.wasm.js', 'npm/factoidal/factoidal-npm-entry.wasm.assets'],
    'fstar js_of_ocaml': ['npm/factoidal/factoidal.js'],
  };
  console.log('# artifact sizes (bytes)');
  for (const [name, files] of Object.entries(artifacts)) {
    let total = 0;
    for (const f of files) {
      try {
        const st = statSync(p(f));
        if (st.isDirectory()) {
          const { readdirSync } = require('node:fs');
        }
        total += st.size;
      } catch { /* directory: measured below via du in the report */ }
    }
    console.log(JSON.stringify({ artifact: name, files, knownFileBytes: total }));
  }
  for (const K of sizes) for (const e of engines) {
    const r = spawnSync(process.execPath, [fileURLToPath(import.meta.url), e, String(K)], { encoding: 'utf8', timeout: 600000 });
    process.stdout.write(r.stdout || '');
    if (r.status !== 0) console.log(JSON.stringify({ engine: e, people: K, error: (r.stderr || 'nonzero exit').slice(0, 300) }));
  }
}

const [, , engineArg, kArg] = process.argv;
if (engineArg) await runChild(engineArg, Number(kArg ?? 1000));
else driver();
