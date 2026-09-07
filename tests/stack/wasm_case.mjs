// Run ONE deep-input case through the shipped WebAssembly module in Node.
//
// The wasm module carries the smallest stack we ship, so it is the route
// that fails first when a recursion is proportional to an input. Each case
// runs in its OWN node process: a stack overflow inside wasm aborts the
// instance, and a shared process would report every later case as broken.
//
//   node tests/stack/wasm_case.mjs <case-name> <fixture-dir>
//
// Prints one JSON line: {case, route:"wasm", ok, ms, detail}.
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';

const [, , caseName, dir] = process.argv;
const ROOT = new URL('../../', import.meta.url);
const read = (f) => readFileSync(`${dir}/${f}`, 'utf8');
const readArgs = (f) => JSON.parse(read(f));

const CASES = {
  'xml-entities': () => ['parseToDatasetJson', readArgs('args-xml.json')],
  'turtle-literal': () => ['parseToDatasetJson', readArgs('args-turtle-literal.json')],
  'turtle-collection': () => ['parseToDatasetJson', readArgs('args-turtle-collection.json')],
  'nquads-one-subject': () => ['parseToDatasetJson', readArgs('args-nquads.json')],
  'sparql-union': () => ['queryDataset', readArgs('args-sparql-union.json')],
  'sparql-nested': () => ['queryDataset', readArgs('args-sparql-nested.json')],
  'manifest': () => ['storeManifestInspect', readArgs('manifest-args.json')],
};

const out = { case: caseName, route: 'wasm' };
try {
  const build = CASES[caseName];
  if (!build) throw new Error(`no wasm route for case '${caseName}'`);
  const [op, args] = build();
  const { loadL4 } = await import(new URL('docs/web/hub/assets/l4/l4factoidal.js', ROOT).href);
  const l4 = await loadL4();
  const t0 = performance.now();
  const res = l4.call(op, args);
  out.ms = Math.round(performance.now() - t0);
  out.ok = true;
  out.detail = JSON.stringify(res).slice(0, 120);
} catch (e) {
  out.ok = false;
  out.detail = String(e && e.message ? e.message : e).slice(0, 300);
}
console.log(JSON.stringify(out));
