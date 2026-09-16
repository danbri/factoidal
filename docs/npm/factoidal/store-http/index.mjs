// Reading a Shardborough generation over HTTP, from a browser or from a
// server runtime, with `fetch` as the only I/O primitive.
// https://github.com/danbri/factoidal/issues/669
// https://github.com/danbri/factoidal/issues/670
//
// WHAT THIS FILE IS ALLOWED TO DO
// Fetch CURRENT, fetch a manifest file by name, fetch the artifact objects
// the ENGINE's plan named, concatenate their bytes, and hand them over. It
// computes SHA-256 of the bytes it fetched and compares it against the
// digest the engine read out of the manifest, so a substituted object is
// refused before it reaches the module; the comparison uses a digest this
// file never derives itself.
//
// It never parses a manifest, never decides which artifact answers a
// query, never decodes a block and knows no field offset, magic number or
// artifact role. Every one of those is a format decision and it lives in
// `formal/lean4/Wasm/Ops/Store.lean` (iron rule 7 of CLAUDE.md). A
// reviewer who finds a byte offset or an artifact suffix in this file has
// found a rule violation; `tools/host-purity-lint.sh` scans for both.
//
// WHAT IT IS THE HTTP COUNTERPART OF
// `npm/factoidal/bin/store.mjs` drives the same operations over a local
// filesystem through `npm/factoidal/store-host`. The sequence is identical
// and the engine cannot tell the two apart:
//
//   openStore    ->  openStoreOverHttp    CURRENT and the manifest
//   readWhole    ->  fetchArtifact        one GET per artifact the plan named
//   queryStore   ->  HttpStore#query      storeQueryPlan, then storeQuery
//
// The design note is `docs/designissues/2026-09-07-store-over-http.md`.

/** A failure of the transport or of the host's own digest check. */
export class HttpStoreError extends Error {
  constructor (code, message, detail = {}) {
    super(message)
    this.name = 'HttpStoreError'
    this.code = code
    this.url = detail.url ?? null
    this.key = detail.key ?? null
    this.expected = detail.expected ?? null
    this.found = detail.found ?? null
    if (detail.cause !== undefined) this.cause = detail.cause
  }
}

// The manifest file names a generation directory can carry, in the order
// `Harness.ShardMerklePread.readManifest` tries them, and the pointer file
// that names the activated generation. These three strings are the whole
// of this module's knowledge of the layout: it reads whichever manifest
// name exists and passes the bytes on without looking inside either one.
// The same names appear in `store-host/index.mjs` for the same reason.
const MANIFEST_NAMES = ['manifest.sbm2', 'manifest.sbm1']
const POINTER_NAME = 'CURRENT'

const HEX = (() => {
  const table = new Array(256)
  for (let byte = 0; byte < 256; byte += 1) {
    table[byte] = byte.toString(16).padStart(2, '0')
  }
  return table
})()

/**
 * Lowercase hexadecimal of a byte array. A transport encoding for the
 * manifest argument two of the operations take, and for a digest, not an
 * interpretation of the bytes. Artifact bytes never take this path: they
 * cross raw through `callBlobIO`.
 */
export function hexOfBytes (bytes) {
  let out = ''
  for (let index = 0; index < bytes.length; index += 1) out += HEX[bytes[index]]
  return out
}

/** SHA-256 of a byte array, as lowercase hexadecimal. */
async function sha256Hex (bytes) {
  const subtle = globalThis.crypto && globalThis.crypto.subtle
  if (!subtle) {
    throw new HttpStoreError('NO_WEB_CRYPTO',
      'this runtime exposes no crypto.subtle, so the host cannot check a ' +
      'digest before the bytes reach the engine. Pass {verify: false} to ' +
      'rely on the engine, which checks every artifact it opens either way.')
  }
  // A fresh buffer: the caller's array may be a view onto a larger one.
  const digest = await subtle.digest('SHA-256', bytes.slice().buffer)
  return hexOfBytes(new Uint8Array(digest))
}

/** Join a base URL that names a directory with one child name. */
function childUrl (base, name) {
  return base.endsWith('/') ? base + name : base + '/' + name
}

function now () {
  return (globalThis.performance && globalThis.performance.now)
    ? globalThis.performance.now()
    : Date.now()
}

/**
 * One GET. `range`, when given, asks for the half-open byte window
 * [offset, offset+length) and the result is checked to be exactly that
 * long, so a server that ignored the request is caught here rather than
 * misread downstream. The query path passes none: today the engine's plan
 * names whole artifacts, and a whole-object GET is what it asked for.
 */
async function get (url, options = {}) {
  const headers = {}
  const range = options.range
  if (range) {
    headers.range = `bytes=${range.offset}-${range.offset + range.length - 1}`
  }
  const started = now()
  let response
  try {
    response = await fetch(url, { headers, ...(options.init ?? {}) })
  } catch (cause) {
    // fetch throws before any response exists: the host is unreachable, the
    // connection dropped, the page's connect-src forbids the origin, or a
    // cross-origin server did not answer the preflight. The browser does not
    // say which, so the message names the possibilities and carries the
    // cause instead of asserting one of them.
    const why = cause && cause.message ? ` (${cause.message})` : ''
    throw new HttpStoreError('FETCH_FAILED',
      `${url} could not be fetched${why}: no response arrived. Either the ` +
      'server is unreachable, the page forbids that origin (connect-src), or ' +
      'a cross-origin server did not answer the preflight; see the design note.',
      { url, cause })
  }
  if (!response.ok) {
    throw new HttpStoreError('NOT_OK',
      `${url} was refused by the server (${response.status})`, { url })
  }
  const bytes = new Uint8Array(await response.arrayBuffer())
  if (range && bytes.length !== range.length) {
    throw new HttpStoreError('RANGE_IGNORED',
      `${url} answered ${bytes.length} bytes for a ${range.length}-byte ` +
      'window: the server does not serve ranges',
      { url, expected: range.length, found: bytes.length })
  }
  return { bytes, ms: now() - started }
}

/** Run `worker` over `items` with at most `limit` in flight. */
async function mapBounded (items, limit, worker) {
  const out = new Array(items.length)
  let next = 0
  const runners = new Array(Math.min(limit, items.length)).fill(null).map(async () => {
    for (;;) {
      const index = next
      next += 1
      if (index >= items.length) return
      out[index] = await worker(items[index], index)
    }
  })
  await Promise.all(runners)
  return out
}

/**
 * The engine's refusals arrive as `Error: l4factoidal: <its own text>`.
 * The text a caller sees is always the engine's, never a rewrite of it.
 */
function engineText (error) {
  const raw = error && error.message ? String(error.message) : String(error)
  return raw.replace(/^l4factoidal:\s*/, '')
}

/**
 * An open generation, reachable over HTTP.
 *
 * Hold one of these for as long as questions are asked about the
 * generation. It retains the manifest bytes and their hexadecimal form, so
 * a query does not re-encode a large manifest per question, and, when
 * `cacheArtifacts` is on, the artifact bytes already fetched. Nothing else
 * accumulates: the region built for one query is dropped when the query
 * returns.
 */
export class HttpStore {
  constructor (engine, detail) {
    this.engine = engine
    /** The collection root that holds CURRENT, with a trailing slash. */
    this.baseUrl = detail.baseUrl
    /** The generation name CURRENT held, or the one the caller named. */
    this.generation = detail.generation
    /** The generation directory URL, with a trailing slash. */
    this.generationUrl = detail.generationUrl
    this.manifestName = detail.manifestName
    this.manifest = detail.manifest
    this.manifestHex = hexOfBytes(detail.manifest)
    this.verify = detail.verify
    this.concurrency = detail.concurrency
    this.cacheArtifacts = detail.cacheArtifacts
    /** key -> bytes, only when `cacheArtifacts` is on. */
    this.cache = new Map()
    /** Every request this store made, oldest first. */
    this.requests = []
    /**
     * The manifest as the ENGINE decoded it. The host reads two fields of
     * it — an artifact's name, and the digest the manifest commits for
     * that name — and interprets neither.
     */
    this.inspection = detail.inspection
    this.digests = new Map()
    for (const entry of detail.inspection.entries ?? []) {
      if (typeof entry.sha256 === 'string') this.digests.set(entry.key, entry.sha256)
    }
    for (const blob of detail.inspection.blobs ?? []) {
      if (typeof blob.sha256 === 'string') this.digests.set(blob.key, blob.sha256)
    }
  }

  /** What the engine says the generation is. */
  get facts () {
    const inspection = this.inspection
    return {
      generation: this.generation,
      wireVersion: inspection.wireVersion,
      layout: inspection.layout,
      entries: (inspection.entries ?? []).length,
      rows: inspection.totalRows,
      bytes: inspection.totalBytes,
      manifestBytes: this.manifest.length
    }
  }

  /** The request log since the last `resetLog()`, and its totals. */
  get log () {
    let bytes = 0
    let ms = 0
    for (const request of this.requests) {
      bytes += request.bytes
      if (request.from === 'network') ms += request.ms
    }
    return { requests: this.requests.slice(), count: this.requests.length, bytes, ms }
  }

  resetLog () {
    this.requests = []
  }

  /** Drop the artifact cache. The manifest is kept. */
  clearCache () {
    this.cache.clear()
  }

  /**
   * Fetch one artifact by the name the engine's plan gave, and check it
   * against the digest the manifest commits for that name.
   *
   * A mismatch throws DIGEST_MISMATCH naming the key, and the bytes are
   * discarded: they never reach the engine and are never cached. This is
   * an early refusal, not the authority — `storeQuery` checks every
   * artifact it opens against the same commitment, so switching the check
   * off changes when a substituted object is caught, not whether it is.
   */
  async fetchArtifact (key, range = null) {
    if (this.cacheArtifacts && range === null && this.cache.has(key)) {
      const bytes = this.cache.get(key)
      this.requests.push({ key, bytes: bytes.length, ms: 0, from: 'cache', verified: false })
      return bytes
    }
    const url = childUrl(this.generationUrl, key)
    const { bytes, ms } = await get(url, { range })
    let verified = false
    if (this.verify && range === null) {
      const expected = this.digests.get(key)
      if (typeof expected === 'string') {
        const found = await sha256Hex(bytes)
        if (found !== expected) {
          this.requests.push({ key, bytes: bytes.length, ms, from: 'network', verified: false })
          throw new HttpStoreError('DIGEST_MISMATCH',
            `artifact '${key}' does not match the SHA-256 the manifest ` +
            'commits for it; the bytes were discarded',
            { url, key, expected, found })
        }
        verified = true
      }
    }
    this.requests.push({ key, bytes: bytes.length, ms, from: 'network', verified })
    if (this.cacheArtifacts && range === null) this.cache.set(key, bytes)
    return bytes
  }

  /** `storeQueryPlan` — which artifacts this query needs, before any GET. */
  plan (sparql) {
    try {
      return this.engine.call('storeQueryPlan', [this.manifestHex, sparql])
    } catch (error) {
      throw new HttpStoreError('ENGINE_REFUSED', engineText(error))
    }
  }

  /**
   * Evaluate one SPARQL query.
   *
   * Plan, GET exactly the artifacts the plan named (bounded parallel),
   * concatenate them into one region, and call `storeQuery` with a
   * {"key","offset","len"} window per artifact. The region is written
   * straight into the wasm heap with no encoding, and the engine
   * bounds-checks every window.
   *
   * @returns {{plan: object, result: object, artifacts: object[],
   *            blobBytes: number, requests: object[], timings: object}}
   */
  async query (sparql) {
    const startedAll = now()
    const plan = this.plan(sparql)
    const plannedAt = now()
    const before = this.requests.length
    const keys = (plan.keys ?? []).concat(plan.blobKeys ?? [])
    const chunks = await mapBounded(keys, this.concurrency, (key) => this.fetchArtifact(key))
    const fetchedAt = now()

    let total = 0
    for (const chunk of chunks) total += chunk.length
    const blob = new Uint8Array(total)
    const artifacts = []
    let offset = 0
    for (let index = 0; index < chunks.length; index += 1) {
      blob.set(chunks[index], offset)
      artifacts.push({ key: keys[index], offset, len: chunks[index].length })
      offset += chunks[index].length
    }

    let result
    try {
      result = this.engine.callBlobIO('storeQuery',
        [this.manifestHex, sparql, JSON.stringify(artifacts)], blob).envelope
    } catch (error) {
      throw new HttpStoreError('ENGINE_REFUSED', engineText(error))
    }
    const done = now()
    const requests = this.requests.slice(before)
    let networkBytes = 0
    for (const request of requests) networkBytes += request.bytes
    return {
      plan,
      result,
      artifacts,
      blobBytes: total,
      requests,
      timings: {
        planMs: plannedAt - startedAll,
        fetchMs: fetchedAt - plannedAt,
        answerMs: done - fetchedAt,
        totalMs: done - startedAll,
        networkBytes
      }
    }
  }
}

/**
 * Open a generation that lives under an HTTP base URL.
 *
 * With no `generation` option the activated generation is opened through
 * CURRENT, exactly as the filesystem host does. With one, that generation
 * is opened directly, which is how a published generation with no
 * activation pointer is read.
 *
 * @param {string} baseUrl the collection root, the URL that holds CURRENT
 * @param {{engine?: object, generation?: string, verify?: boolean,
 *          concurrency?: number, cacheArtifacts?: boolean}} options
 *   `engine` is a loaded engine — the object loadL4() resolves to, with
 *   `call` and `callBlobIO`. In Node or Deno it is loaded for you when
 *   absent; a browser must pass one, because finding the module's files is
 *   the page's business and not this module's.
 * @returns {Promise<HttpStore>}
 */
export async function openStoreOverHttp (baseUrl, options = {}) {
  if (typeof baseUrl !== 'string' || baseUrl.length === 0) {
    throw new HttpStoreError('BAD_ARGUMENT', 'baseUrl must be a non-empty string')
  }
  const base = baseUrl.endsWith('/') ? baseUrl : baseUrl + '/'
  const engine = options.engine ?? await loadEngineHere()

  let generation = options.generation
  if (typeof generation !== 'string') {
    const pointer = await get(childUrl(base, POINTER_NAME))
    // CURRENT holds a UTF-8 generation name. Trailing ASCII whitespace is
    // tolerated so a pointer written by hand still opens. Refusing a name
    // that would leave the collection root is a URL-safety guard on a
    // string about to be joined, not a check of the pointer's format.
    generation = new TextDecoder('utf-8', { fatal: true })
      .decode(pointer.bytes).replace(/[\r\n\t ]+$/, '')
    if (generation.length === 0 || generation === '.' || generation === '..' ||
        /[/\\?# ]/.test(generation)) {
      throw new HttpStoreError('BAD_GENERATION_NAME',
        `${POINTER_NAME} does not hold a usable child name`,
        { url: childUrl(base, POINTER_NAME) })
    }
  }
  const generationUrl = childUrl(base, generation) + '/'

  let manifest = null
  let manifestName = null
  let lastError = null
  for (const name of MANIFEST_NAMES) {
    try {
      manifest = (await get(childUrl(generationUrl, name))).bytes
      manifestName = name
      break
    } catch (error) {
      lastError = error
    }
  }
  if (manifest === null) {
    throw new HttpStoreError('NO_MANIFEST',
      `${generationUrl} serves none of ${MANIFEST_NAMES.join(', ')}`,
      { url: generationUrl, cause: lastError })
  }

  let inspection
  try {
    inspection = engine.call('storeManifestInspect', [hexOfBytes(manifest)])
  } catch (error) {
    throw new HttpStoreError('ENGINE_REFUSED', engineText(error))
  }

  const store = new HttpStore(engine, {
    baseUrl: base,
    generation,
    generationUrl,
    manifestName,
    manifest,
    inspection,
    verify: options.verify !== false,
    concurrency: Math.max(1, options.concurrency ?? 6),
    cacheArtifacts: options.cacheArtifacts === true
  })
  store.requests.push({
    key: manifestName, bytes: manifest.length, ms: 0, from: 'network', verified: false
  })
  return store
}

/**
 * Load the engine the way the command-line tools do. Node and Deno only:
 * `bin/engine.mjs` resolves the module's files through the filesystem
 * host, which a browser has none of. Imported dynamically so a browser
 * bundle of this file never pulls in `node:fs`.
 */
async function loadEngineHere () {
  const isServerRuntime =
    (globalThis.process && globalThis.process.versions && globalThis.process.versions.node) ||
    typeof globalThis.Deno !== 'undefined'
  if (!isServerRuntime) {
    throw new HttpStoreError('NO_ENGINE',
      'pass {engine} — a browser page loads the engine itself, with ' +
      "loadL4() from the module's own loader")
  }
  const module = await import('../bin/engine.mjs')
  return module.loadEngine()
}

export default openStoreOverHttp
