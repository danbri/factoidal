// The JavaScript half of tools/wasm-store-query-smoke.sh.
//
// The WASM module has no file system, so this host does the file reads. It
// does NOTHING else: it never parses a manifest, never verifies a digest and
// never interprets a block. It reads `manifest.sbm2` by name, hands the bytes
// to `storeManifestInspect` and `storeQueryPlan`, reads exactly the artifact
// keys the plan named, and hands those bytes to `storeQuery`. Every decision
// — which blocks a query needs, whether their digests match, what the query
// answers — is made in Lean (iron rule 7 of CLAUDE.md).
//
// The artifact bytes go across RAW: they are concatenated into one buffer
// written straight into the wasm heap by `l4.callBlob`, with no hexadecimal
// and no base64 anywhere. Each artifact is a {"key","offset","len"} window
// into that buffer, and Lean bounds-checks every window.
//
//   node tools/wasm-store-query-smoke.mjs <generation-dir> <sparql> [--tamper]
//
// Prints one JSON line on success. With `--tamper` it flips one byte of the
// first artifact and expects `storeQuery` to refuse.
import { readFileSync } from 'node:fs';
import { join } from 'node:path';

const [directory, query, ...flags] = process.argv.slice(2);
if (!directory || !query) {
  console.error('usage: wasm-store-query-smoke.mjs <generation-dir> <sparql> [--tamper]');
  process.exit(2);
}
const tamper = flags.includes('--tamper');

const loaderUrl = new URL('../docs/web/hub/assets/l4/l4factoidal.js', import.meta.url);
const { loadL4 } = await import(loaderUrl.href);
const l4 = await loadL4();

const manifestHex = readFileSync(join(directory, 'manifest.sbm2')).toString('hex');

const inspect = l4.call('storeManifestInspect', [manifestHex]);
const plan = l4.call('storeQueryPlan', [manifestHex, query]);

// One buffer, the artifacts back to back, and a window per artifact.
const chunks = plan.keys.map((key) => readFileSync(join(directory, key)));
if (tamper) {
  if (chunks.length === 0) {
    console.error('--tamper needs a plan that selects at least one artifact');
    process.exit(1);
  }
  chunks[0][Math.floor(chunks[0].length / 2)] ^= 0xff;
}
const blob = Buffer.concat(chunks);
let offset = 0;
const artifacts = plan.keys.map((key, i) => {
  const descriptor = { key, offset, len: chunks[i].length };
  offset += chunks[i].length;
  return descriptor;
});

if (tamper) {
  try {
    l4.callBlob('storeQuery', [manifestHex, query, JSON.stringify(artifacts)], blob);
  } catch (error) {
    console.log(JSON.stringify({ refused: String(error.message) }));
    process.exit(0);
  }
  console.error('storeQuery accepted an artifact whose SHA-256 does not match');
  process.exit(1);
}

const result = l4.callBlob('storeQuery',
  [manifestHex, query, JSON.stringify(artifacts)], blob);

let rows;
if (result.kind === 'select') rows = result.srj.results.bindings.length;
else if (result.kind === 'ask') rows = result.boolean ? 1 : 0;
else if (result.kind === 'construct') rows = result.nquads.split('\n').filter((l) => l.length > 0).length;
else rows = -1;

console.log(JSON.stringify({
  wireVersion: inspect.wireVersion,
  layout: inspect.layout,
  manifestEntries: inspect.entries.length,
  mode: plan.mode,
  shards: plan.shards,
  keys: plan.keys.length,
  planBytes: plan.bytes,
  planRows: plan.rows,
  blobBytes: blob.length,
  resultMode: result.mode,
  resultShards: result.shards,
  kind: result.kind,
  rows,
}));
