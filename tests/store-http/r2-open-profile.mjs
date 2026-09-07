// Where the seconds go when a store over HTTP is opened, phase by phase.
// https://github.com/danbri/factoidal/issues/670
//
//   node tests/store-http/r2-open-profile.mjs
//   R2_BASE=https://example.invalid/coll/ node tests/store-http/r2-open-profile.mjs
//
// This one DOES reach the network, so it is not part of any suite. It
// exists because the four costs of opening a store — the pointer, the
// manifest download, the hexadecimal encoding the ABI takes, and the
// engine's decode — are wildly unequal at scale, and a single wall-clock
// figure hides which one to repair. Measured 2026-09-07 against the
// skosall generation (25,533,404-byte manifest, 36,106 entries): 316 ms,
// 4,325 ms, 4,552 ms, and 537,868 ms respectively. The design note is
// docs/designissues/2026-09-07-store-over-http.md.
//
// It runs on a WORKER THREAD with a 64 MB stack, the route
// npm/factoidal/bin/store-worker-host.mjs takes, because decoding a
// manifest of this size overflows the default frame budget. `node
// --stack-size=N` on the main thread does not substitute for it on
// macOS: the main thread's stack is fixed by the operating system, so a
// large value gives a segmentation fault rather than a bigger stack.

import { Worker, isMainThread, parentPort } from 'node:worker_threads'

const BASE = process.env.R2_BASE ??
  'https://pub-ce682919a85f481f9864add9d9a66737.r2.dev/skosall/'

if (isMainThread) {
  const worker = new Worker(new URL(import.meta.url), {
    resourceLimits: { stackSizeMb: 64, maxOldGenerationSizeMb: 8192 }
  })
  worker.on('message', (line) => process.stdout.write(line))
  worker.on('error', (error) => {
    process.stderr.write(`worker: ${error.message}\n`)
    process.exit(1)
  })
} else {
  const say = (line) => parentPort.postMessage(line + '\n')
  const { hexOfBytes } = await import('../../npm/factoidal/store-http/index.mjs')
  const { loadEngine } = await import('../../npm/factoidal/bin/engine.mjs')
  const engine = await loadEngine()
  const base = BASE.endsWith('/') ? BASE : BASE + '/'

  const timed = async (label, work) => {
    const started = Date.now()
    const value = await work()
    say(`${label.padEnd(34)} ${String(Date.now() - started).padStart(8)} ms`)
    return value
  }

  say(`base ${base}`)
  const generation = (await timed('GET CURRENT',
    async () => (await (await fetch(base + 'CURRENT')).text()))).trim()
  say(`generation ${generation}`)

  const generationUrl = `${base}${generation}/`
  const manifest = await timed('GET manifest', async () => new Uint8Array(
    await (await fetch(generationUrl + 'manifest.sbm2')).arrayBuffer()))
  say(`manifest ${manifest.length} bytes`)

  await timed('GET manifest again (cache check)', async () => new Uint8Array(
    await (await fetch(generationUrl + 'manifest.sbm2')).arrayBuffer()))

  const hex = await timed('hexOfBytes', async () => hexOfBytes(manifest))
  say(`hex ${hex.length} characters`)

  const inspection = await timed('storeManifestInspect',
    async () => engine.call('storeManifestInspect', [hex]))
  const graphs = new Set()
  for (const entry of inspection.entries) {
    for (const graph of entry.graphs ?? []) {
      graphs.add(typeof graph === 'string' ? graph : graph.value)
    }
  }
  say(`entries ${inspection.entries.length}, rows ${inspection.totalRows}, ` +
      `bytes ${inspection.totalBytes}, wire ${inspection.wireVersion}, ` +
      `layout ${inspection.layout}, graphs ${graphs.size}`)
  process.exit(0)
}
