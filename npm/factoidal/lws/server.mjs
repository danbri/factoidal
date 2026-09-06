// A Node HTTP host for the Linked Web Storage Protocol 1.0 core.
// https://github.com/danbri/factoidal/issues/659
// Design record: docs/designissues/2026-09-06-lws-and-solid-protocols.md
//
// WHAT THIS FILE IS ALLOWED TO DO
// Accept a socket, turn one HTTP request into the JSON request record,
// call the engine's `lwsStep` on a handle, and write the JSON response
// record back onto the socket. That is the whole contract.
//
// It makes NO protocol decision. It does not choose a status code, does
// not build a `Link` header, does not read or write a resource, does not
// decide whether a PATCH is refused, and does not know what a container
// is. Every one of those lives in `formal/lean4/L4Factoidal/LWS/`
// (iron rule 7 of CLAUDE.md). A reviewer who finds a status code, a
// media type decision or an RDF term in this file has found a rule
// violation. The one status code written here is 500, and only for a
// failure of this host itself.
//
// THE WASM CONTRACT
//   lwsOpen  [configJson]            -> { ok, handle }
//   lwsStep  [handle, requestJson]   -> { ok, response }
//   lwsClose [handle]                -> { ok }
//
//   request  { method, target, headers: [[name, value]], body }
//   response { status, headers: [[name, value]], body }
//
// `headers` is a list of pairs rather than an object because HTTP allows
// a field name to repeat and the order of repeated fields is
// significant; an object would lose both.
//
// The reader of the response envelope accepts the response record either
// under `response` or spread onto the envelope itself, and the handle
// either as `handle` or as `id`. This is deliberate tolerance while the
// Lean side of the contract lands, not two supported shapes: when
// `docs/lws-solid-conformance.md` fixes one, the other stops being
// produced and this code keeps working unchanged.

import { loadEngine } from '../bin/engine.mjs'

/** The ops this host needs from the engine. */
export const LWS_OPS = ['lwsOpen', 'lwsStep', 'lwsClose']

/** An error raised by the LWS host, as opposed to one the engine
 *  reported. `unknownOp` is set when the loaded WebAssembly module does
 *  not carry the operation at all, which is what a test skips on. */
export class LwsHostError extends Error {
  constructor (message, detail = {}) {
    super(message)
    this.name = 'LwsHostError'
    this.unknownOp = detail.unknownOp === true
  }
}

function isUnknownOp (error) {
  const text = error && error.message ? String(error.message) : String(error)
  return text.indexOf('unknown op') >= 0
}

/**
 * Whether the loaded engine carries the LWS operations.
 *
 * One call is made and its refusal read. A module built before the LWS
 * ops landed answers "unknown op"; anything else -- including an engine
 * complaint about the configuration -- means the op is present.
 *
 * @param {object} engine the handle from `loadEngine()`
 * @returns {Promise<{available: boolean, reason: string}>}
 */
export async function lwsOpsAvailable (engine) {
  try {
    const opened = engine.call('lwsOpen', [JSON.stringify({ probe: true })])
    const handle = handleOf(opened)
    if (handle !== null) {
      try { engine.call('lwsClose', [handle]) } catch (_error) { /* probe only */ }
    }
    return { available: true, reason: 'lwsOpen answered' }
  } catch (error) {
    if (isUnknownOp(error)) {
      return {
        available: false,
        reason: 'the loaded l4factoidal WebAssembly module does not carry ' +
          'the lws ops (rebuild formal/lean4/Wasm)'
      }
    }
    return { available: true, reason: 'lwsOpen answered with an engine error' }
  }
}

function handleOf (envelope) {
  if (envelope === null || typeof envelope !== 'object') return null
  for (const name of ['handle', 'id']) {
    const value = envelope[name]
    if (typeof value === 'string' && value.length > 0) return value
    if (typeof value === 'number') return String(value)
  }
  return null
}

function responseOf (envelope) {
  if (envelope === null || typeof envelope !== 'object') {
    throw new LwsHostError('lwsStep answered with no envelope')
  }
  const record = (envelope.response !== null && typeof envelope.response === 'object')
    ? envelope.response
    : envelope
  if (typeof record.status !== 'number') {
    throw new LwsHostError('lwsStep answered with no status in its response record')
  }
  const headers = Array.isArray(record.headers) ? record.headers : []
  const body = typeof record.body === 'string' ? record.body : ''
  return { status: record.status, headers, body }
}

/**
 * Open one LWS storage on the engine and return the handle plus the two
 * calls a host makes against it.
 *
 * `configJson` is passed to the engine unread. The storage root
 * directory, if the engine takes one, goes in it.
 *
 * @param {object} options
 * @param {string} [options.root] a directory the engine may use for state
 * @param {string} [options.baseUrl] the origin the storage is served at
 * @param {object} [options.engine] an engine handle to reuse
 * @returns {Promise<{step: Function, close: Function, handle: string, engine: object}>}
 */
export async function openLwsStorage (options = {}) {
  const engine = options.engine !== undefined ? options.engine : await loadEngine()
  const config = {}
  if (typeof options.root === 'string') config.root = options.root
  if (typeof options.baseUrl === 'string') config.baseUrl = options.baseUrl
  let opened
  try {
    opened = engine.call('lwsOpen', [JSON.stringify(config)])
  } catch (error) {
    if (isUnknownOp(error)) {
      throw new LwsHostError(
        'the loaded l4factoidal WebAssembly module does not carry lwsOpen',
        { unknownOp: true })
    }
    throw error
  }
  const handle = handleOf(opened)
  if (handle === null) {
    throw new LwsHostError('lwsOpen answered with no handle')
  }
  return {
    engine,
    handle,
    /**
     * One protocol step.
     * @param {{method: string, target: string,
     *          headers: Array<[string, string]>, body: string}} request
     * @returns {{status: number, headers: Array<[string, string]>, body: string}}
     */
    step (request) {
      return responseOf(engine.call('lwsStep', [handle, JSON.stringify(request)]))
    },
    close () {
      try { engine.call('lwsClose', [handle]) } catch (_error) { /* already gone */ }
    }
  }
}

/** Read a Node request body as one UTF-8 string. */
function readBody (request) {
  return new Promise((resolve, reject) => {
    const chunks = []
    request.on('data', (chunk) => chunks.push(chunk))
    request.on('error', reject)
    request.on('end', () => resolve(Buffer.concat(chunks).toString('utf8')))
  })
}

/** Node's flat `rawHeaders` array as the pairs the contract wants. */
function headerPairs (raw) {
  const pairs = []
  for (let index = 0; index + 1 < raw.length; index += 2) {
    pairs.push([raw[index], raw[index + 1]])
  }
  return pairs
}

/**
 * A Node `http.Server` that answers every request through `lwsStep`.
 *
 * The server is returned unlistened: the caller chooses the port, which
 * is what lets a test take an ephemeral one.
 *
 * @param {object} options as `openLwsStorage`, plus `onError`
 * @returns {Promise<{server: import('node:http').Server,
 *                    storage: object, close: Function}>}
 */
export async function createLwsServer (options = {}) {
  const http = await import('node:http')
  const storage = await openLwsStorage(options)
  const onError = typeof options.onError === 'function'
    ? options.onError
    : (error) => { console.error(`lws-serve: ${error.message}`) }

  const server = http.createServer(async (request, response) => {
    let record
    try {
      record = {
        method: request.method,
        target: request.url,
        headers: headerPairs(request.rawHeaders),
        body: await readBody(request)
      }
    } catch (error) {
      onError(error)
      response.writeHead(500, { 'content-type': 'text/plain' })
      response.end('lws-serve: could not read the request body\n')
      return
    }
    let answer
    try {
      answer = storage.step(record)
    } catch (error) {
      // A failure of this host or of the engine, not a protocol answer.
      // The engine's own words are kept; nothing is invented.
      onError(error)
      response.writeHead(500, { 'content-type': 'text/plain' })
      response.end(`lws-serve: ${error.message}\n`)
      return
    }
    for (const pair of answer.headers) {
      if (!Array.isArray(pair) || pair.length < 2) continue
      const existing = response.getHeader(pair[0])
      if (existing === undefined) {
        response.setHeader(pair[0], String(pair[1]))
      } else if (Array.isArray(existing)) {
        response.setHeader(pair[0], existing.concat([String(pair[1])]))
      } else {
        response.setHeader(pair[0], [String(existing), String(pair[1])])
      }
    }
    response.statusCode = answer.status
    response.end(answer.body)
  })

  return {
    server,
    storage,
    close () {
      return new Promise((resolve) => {
        server.close(() => { storage.close(); resolve() })
      })
    }
  }
}

/**
 * Start a server and resolve once it is listening.
 *
 * @param {object} options as `createLwsServer`, plus `port` and `host`
 * @returns {Promise<{server: object, storage: object, port: number,
 *                    origin: string, close: Function}>}
 */
export async function listen (options = {}) {
  const port = typeof options.port === 'number' ? options.port : 0
  const host = typeof options.host === 'string' ? options.host : '127.0.0.1'
  const created = await createLwsServer(options)
  await new Promise((resolve, reject) => {
    created.server.once('error', reject)
    created.server.listen(port, host, resolve)
  })
  const bound = created.server.address()
  return {
    ...created,
    port: bound.port,
    origin: `http://${host}:${bound.port}`
  }
}
