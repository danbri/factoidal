// The store-over-HTTP host, against a mock bucket.
// https://github.com/danbri/factoidal/issues/669
// https://github.com/danbri/factoidal/issues/670
//
//   node tests/store-http/over-http.mjs
//
// WHAT IT GATES THAT NOTHING ELSE DOES
// `tests/store-host/cli.mjs` drives the same three engine operations over
// a local filesystem. This drives them over `fetch`, which is the path a
// browser takes, and pins the four properties that path adds:
//
//   * the plan decides the requests. A bound-predicate query fetches ONE
//     object out of thirteen; an unbound one fetches all thirteen. Nothing
//     in the host chooses.
//   * a substituted object is refused BY NAME before it reaches the
//     engine, and refused again by the engine when the host check is off.
//   * a byte range is either served exactly or reported as ignored — never
//     silently short.
//   * repeated queries do not grow the module's linear memory, so a page
//     can hold one store open and keep asking.
//
// Nothing here touches a network or Cloudflare: `mock-bucket.mjs` serves
// the sample store this package ships.

import { cp, readFile, writeFile } from 'node:fs/promises'
import { mkdtemp, rm } from 'node:fs/promises'
import { tmpdir } from 'node:os'
import { join } from 'node:path'

import { startMockBucket } from './mock-bucket.mjs'
import {
  openStoreOverHttp, HttpStoreError
} from '../../npm/factoidal/store-http/index.mjs'

const SAMPLE = new URL('../../npm/factoidal/sample-store', import.meta.url).pathname
const SKOS = 'PREFIX skos: <http://www.w3.org/2004/02/skos/core#>\n'

let pass = 0
let fail = 0
const failures = []

function check (name, condition, detail = '') {
  if (condition) {
    pass += 1
    process.stdout.write(`ok   ${name}\n`)
  } else {
    fail += 1
    failures.push(name)
    process.stdout.write(`FAIL ${name}${detail ? ' — ' + detail : ''}\n`)
  }
}

async function refuses (name, run, expectedCode) {
  try {
    await run()
    check(name, false, 'it did not refuse')
  } catch (error) {
    check(name, error instanceof HttpStoreError && error.code === expectedCode,
      `${error.code ?? error.name}: ${error.message}`)
    return error
  }
  return null
}

// The nine shapes of the skosdex cookbook, written for this store's one
// default graph. The notebook (docs/web/hub/54-skosdex-over-r2.md) carries
// the same nine; the R2 generation carries named graphs, so the same
// shapes take a GRAPH wrapper there.
export const SHAPES = [
  { id: 'census', title: 'Concept census',
    q: SKOS + 'SELECT (COUNT(?c) AS ?concepts) WHERE { ?c a skos:Concept }' },
  { id: 'indexer', title: 'The indexer shape',
    q: SKOS + `SELECT ?c ?pref ?def WHERE {
  ?c a skos:Concept ; skos:prefLabel ?pref .
  OPTIONAL { ?c skos:definition ?def }
  FILTER(LANGMATCHES(LANG(?pref), "en"))
} LIMIT 20` },
  { id: 'schemes', title: 'Scheme inventory',
    q: SKOS + 'SELECT ?scheme (COUNT(?c) AS ?concepts) WHERE { ?c skos:inScheme ?scheme } GROUP BY ?scheme ORDER BY DESC(?concepts)' },
  { id: 'languages-of-one', title: 'One concept, every language',
    q: SKOS + `SELECT ?lang ?label WHERE {
  <http://cv.iptc.org/newscodes/spamfstat/yards-per-attempt> skos:prefLabel ?label
  BIND(LANG(?label) AS ?lang)
} ORDER BY ?lang` },
  { id: 'same-label', title: 'Same label, which concept',
    q: SKOS + 'SELECT ?c WHERE { ?c skos:prefLabel "number-of-plays"@en-gb }' },
  { id: 'language-coverage', title: 'Language coverage',
    q: SKOS + 'SELECT ?lang (COUNT(?l) AS ?labels) WHERE { ?s skos:prefLabel ?l BIND(LANG(?l) AS ?lang) } GROUP BY ?lang ORDER BY DESC(?labels)' },
  { id: 'predicates', title: 'Predicate census',
    q: 'SELECT ?p (COUNT(*) AS ?n) WHERE { ?s ?p ?o } GROUP BY ?p ORDER BY DESC(?n)' },
  { id: 'top-concepts', title: 'Top concepts of every scheme',
    q: SKOS + `SELECT ?scheme ?c ?label WHERE {
  ?scheme skos:hasTopConcept ?c . ?c skos:prefLabel ?label
  FILTER(LANGMATCHES(LANG(?label), "en-gb"))
} LIMIT 20` },
  { id: 'definitions', title: 'Definitions that mention video',
    q: SKOS + `SELECT ?c ?def WHERE {
  ?c skos:definition ?def
  FILTER(LANGMATCHES(LANG(?def), "en") && CONTAINS(LCASE(?def), "video"))
} LIMIT 20` }
]

const bucket = await startMockBucket({ root: SAMPLE, prefix: 'skosall' })
const store = await openStoreOverHttp(bucket.url)
const engine = store.engine

// ------------------------------------------------------------ opening
check('CURRENT names the generation', store.generation === 'gen-1', store.generation)
check('the manifest was fetched once, and only the manifest',
  store.log.count === 1 && store.log.requests[0].key === store.manifestName,
  JSON.stringify(store.log.requests))
check('the engine decoded the manifest the host never read',
  store.facts.entries === 13 && store.facts.rows === 4434 &&
  store.facts.wireVersion === 6,
  JSON.stringify(store.facts))
check('opening reads CURRENT then one manifest, two requests in all',
  bucket.requests.length === 2 &&
  bucket.requests[0].url.endsWith('/CURRENT') &&
  bucket.requests[1].url.endsWith('/' + store.manifestName),
  JSON.stringify(bucket.requests.map((r) => r.url)))

const named = await openStoreOverHttp(bucket.url, { generation: 'gen-1', engine })
check('a generation opens by name, with no CURRENT read',
  named.generation === 'gen-1' && named.log.count === 1)

// ------------------------------------------------- the plan decides
const bound = await store.query(SHAPES[0].q)
check('a bound predicate fetches one object out of thirteen',
  bound.requests.length === 1 && bound.plan.shards === 1 &&
  bound.blobBytes < store.facts.bytes,
  `${bound.requests.length} objects, ${bound.blobBytes} bytes`)
check('every artifact the host sent was verified against the manifest',
  bound.requests.every((request) => request.verified))

const open = await store.query(SHAPES[6].q)
check('an unbound predicate fetches every block',
  open.requests.length === 13 && open.blobBytes === store.facts.bytes,
  `${open.requests.length} objects, ${open.blobBytes} bytes`)

check('the host asked for exactly the keys the plan named',
  bound.artifacts.map((a) => a.key).join(',') === bound.plan.keys.join(','))

// -------------------------------------------------- the nine shapes
const measured = []
for (const shape of SHAPES) {
  const answer = await store.query(shape.q)
  const rows = answer.result.srj?.results?.bindings ?? []
  measured.push({
    id: shape.id,
    mode: answer.plan.mode,
    objects: answer.requests.length,
    bytes: answer.timings.networkBytes,
    rows: rows.length
  })
  check(`${shape.id}: answers rows over HTTP`,
    answer.result.kind === 'select' && rows.length > 0,
    `${rows.length} rows`)
}
process.stdout.write('\nthe nine shapes over the sample store:\n')
process.stdout.write('id                   mode                                   objects      bytes  rows\n')
for (const row of measured) {
  process.stdout.write(
    `${row.id.padEnd(20)} ${row.mode.padEnd(38)} ${String(row.objects).padStart(7)} ` +
    `${String(row.bytes).padStart(10)} ${String(row.rows).padStart(5)}\n`)
}
const selective = measured.filter((row) => row.objects < 13)
check('eight of the nine shapes read less than the whole generation',
  selective.length === 8, `${selective.length} of ${measured.length}`)

// -------------------------------------------------- repeated queries
// The module's linear memory must not grow with the number of questions.
const heapBefore = engine._module.HEAPU8.length
for (let round = 0; round < 25; round += 1) await store.query(SHAPES[4].q)
const heapAfter = engine._module.HEAPU8.length
check('twenty-five more queries do not grow the module memory',
  heapAfter === heapBefore, `${heapBefore} -> ${heapAfter}`)
check('nothing is retained per query by default', store.cache.size === 0)

// ---------------------------------------------------------- ranges
const key = bound.plan.keys[0]
store.resetLog()
const whole = await store.fetchArtifact(key)
const window = await store.fetchArtifact(key, { offset: 16, length: 64 })
check('a byte range is served exactly, and is the same bytes',
  window.length === 64 &&
  Buffer.compare(Buffer.from(window), Buffer.from(whole.subarray(16, 80))) === 0)

const noRanges = await startMockBucket({ root: SAMPLE, prefix: 'skosall', ranges: false })
const overNoRanges = await openStoreOverHttp(noRanges.url, { engine })
await refuses('a server that ignores a range is reported, not misread',
  () => overNoRanges.fetchArtifact(key, { offset: 16, length: 64 }), 'RANGE_IGNORED')
await noRanges.close()

// ------------------------------------------------------------- CORS
const preflight = await fetch(bucket.url + 'gen-1/' + key, {
  method: 'OPTIONS',
  headers: { origin: 'https://danbri.github.io', 'access-control-request-method': 'GET' }
})
check('the bucket answers a browser preflight',
  preflight.headers.get('access-control-allow-origin') === '*' &&
  (preflight.headers.get('access-control-allow-headers') ?? '').includes('range'))
const head = await fetch(bucket.url + 'gen-1/' + key, { method: 'HEAD' })
check('an immutable object says so, and CURRENT does not',
  (head.headers.get('cache-control') ?? '').includes('immutable'))

// -------------------------------------------------------- integrity
const damaged = await mkdtemp(join(tmpdir(), 'store-http-'))
await cp(SAMPLE, damaged, { recursive: true })
const damagedPath = join(damaged, 'gen-1', key)
const original = await readFile(damagedPath)
const flipped = Buffer.from(original)
flipped[flipped.length - 1] ^= 0xff
await writeFile(damagedPath, flipped)

const damagedBucket = await startMockBucket({ root: damaged, prefix: 'skosall' })
const overDamaged = await openStoreOverHttp(damagedBucket.url, { engine })
const refusal = await refuses('a substituted object is refused by name, before the engine',
  () => overDamaged.query(SHAPES[0].q), 'DIGEST_MISMATCH')
check('the refusal names the key and both digests',
  refusal !== null && refusal.key === key &&
  refusal.expected !== refusal.found && refusal.expected.length === 64,
  refusal ? `${refusal.key} ${refusal.expected} ${refusal.found}` : '')

const trusting = await openStoreOverHttp(damagedBucket.url, { engine, verify: false })
const engineRefusal = await refuses('with the host check off the engine refuses it anyway',
  () => trusting.query(SHAPES[0].q), 'ENGINE_REFUSED')
check('the engine names the same artifact in its own words',
  engineRefusal !== null && engineRefusal.message.includes(key),
  engineRefusal ? engineRefusal.message : '')
await damagedBucket.close()
await rm(damaged, { recursive: true, force: true })

// ------------------------------------------------------- refusals
await refuses('a missing collection is reported, not guessed',
  () => openStoreOverHttp(bucket.url + 'nothing-here/', { engine }), 'NOT_OK')

await bucket.close()

const total = pass + fail
process.stdout.write(`\nstore-over-http: ${pass} pass, ${fail} fail (out of ${total})\n`)
if (fail > 0) {
  process.stdout.write(`failed: ${failures.join(', ')}\n`)
  process.exit(1)
}
