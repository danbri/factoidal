// Perf comparison: stateless query() (parse + index per call, via the
// npm-entry ABI's queryDataset) vs handle.query() (parse + index ONCE
// via openDataset(), issue #680) on the F* engine (npm/factoidal).
//
// Workload: the same 2,000-triple two-pattern join shape as
// tests/perf/l4_vs_fstar_wasm_bench.mjs's makeData(1000)/BGP/SPARQL
// (K=1000 people, each with a :name and an :age triple) -- duplicated
// here rather than imported, since that file runs its own driver as a
// side effect of module evaluation (spawning child processes) and is
// not itself a reusable module.
//
// Prints medians of 5 runs (after 1 warmup) for each path; does not
// assert -- this is an observability script, not a gate. Follows the
// same measurement discipline as l4_vs_fstar_wasm_bench.mjs (init/
// parse timed apart from query; median of 5 runs after 1 warmup).
//
// Usage: node tests/perf/npm_handle_vs_stateless.mjs

import { createRequire } from 'node:module';
import { fileURLToPath } from 'node:url';

const require = createRequire(import.meta.url);
const factoidal = require(fileURLToPath(new URL('../../npm/factoidal/index.js', import.meta.url)));

const EX = 'http://example.org/';
const K = 1000; // 2 * K = 2,000 triples

function makeTtl(k) {
  const lines = [`@prefix : <${EX}> .`];
  for (let i = 0; i < k; i++) {
    lines.push(`:p${i} :name "Person ${i}" ; :age ${18 + (i % 60)} .`);
  }
  return lines.join('\n');
}

const SPARQL = `PREFIX : <${EX}> SELECT ?s ?n ?a WHERE { ?s :name ?n ; :age ?a }`;

const now = () => performance.now();
const median = (xs) => [...xs].sort((a, b) => a - b)[Math.floor(xs.length / 2)];

async function main() {
  const ttl = makeTtl(K);
  const tp = now();
  const dataset = await factoidal.parse(ttl, { format: 'turtle', baseIRI: EX });
  const parseMs = now() - tp;
  console.log(`fixture: ${dataset.size} triples (K=${K} people), parse ${parseMs.toFixed(1)} ms`);

  const to = now();
  const handle = await factoidal.openDataset(dataset);
  const openMs = now() - to;
  console.log(`openDataset(): ${openMs.toFixed(1)} ms (handle ${handle.handle}, size ${handle.size})`);

  // Warmup + sanity for both paths -- same row count either way.
  const statelessRows = await factoidal.query(dataset, SPARQL);
  const handleRows = await handle.query(SPARQL);
  if (statelessRows.length !== handleRows.length) {
    throw new Error(
      `row count mismatch: stateless=${statelessRows.length} handle=${handleRows.length}`);
  }
  console.log(`rows per query: ${statelessRows.length}`);

  const statelessTimes = [];
  for (let i = 0; i < 5; i++) {
    const t = now();
    await factoidal.query(dataset, SPARQL);
    statelessTimes.push(now() - t);
  }
  const handleTimes = [];
  for (let i = 0; i < 5; i++) {
    const t = now();
    await handle.query(SPARQL);
    handleTimes.push(now() - t);
  }
  await handle.close();

  const statelessMedian = median(statelessTimes);
  const handleMedian = median(handleTimes);
  console.log(`stateless query() median (5 runs): ${statelessMedian.toFixed(2)} ms  [${statelessTimes.map((t) => t.toFixed(1)).join(', ')}]`);
  console.log(`handle.query() median (5 runs):    ${handleMedian.toFixed(2)} ms  [${handleTimes.map((t) => t.toFixed(1)).join(', ')}]`);
  console.log(`speedup (stateless / handle): ${(statelessMedian / handleMedian).toFixed(2)}x`);
}

main().catch((e) => { console.error(e.stack); process.exit(1); });
