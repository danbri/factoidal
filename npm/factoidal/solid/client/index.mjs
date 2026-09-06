// A `fetch` host for the Solid Protocol v0.11.0 client conformance class.
// https://github.com/danbri/factoidal/issues/659
// Design record: docs/designissues/2026-09-06-lws-and-solid-protocols.md
// Specification: https://solidproject.org/TR/protocol
//
// WHAT THIS FILE IS ALLOWED TO DO
// Call `solidClientRequest` to get a request record, put that record on
// the wire with `fetch`, and give the reply to `solidClientResponse` to
// be interpreted. It is a socket and nothing else.
//
// It composes no URL, sets no `Content-Type`, adds no `Slug`, reads no
// `Link` header and parses no body. Discovery, request construction,
// response interpretation and the WebID profile read are in
// `formal/lean4/L4Factoidal/Solid/Client/` (iron rule 7 of CLAUDE.md).
// A reviewer who finds a header name, a media type or a link relation
// in this file has found a rule violation.
//
// THE WASM CONTRACT
//   solidClientRequest  [kind, argsJson]     -> { ok, request }
//   solidClientResponse [kind, responseJson] -> { ok, ... }
//
//   request  { method, target, headers: [[name, value]], body }
//   response { status, headers: [[name, value]], body }
//
// `kind` names the client operation: "discover", "get", "put", "post",
// "delete", "patch", "profile". The interpretation `solidClientResponse`
// answers is the operation's own shape and this file passes it through
// unread, so a new kind needs no change here.
//
// A multi-step operation is a loop, not a special case: `solidClientRequest`
// may answer `{ ok, done: true, ... }` instead of a request, or answer a
// request together with a `state` that the next call is given. Discovery
// walking from a resource up to its storage root is the case that needs
// it. When the Lean side answers a single request with no `state`, the
// loop runs once.
//
// This file shares no code with `../server/index.mjs` beyond the engine
// loader.

import { loadEngine } from '../../bin/engine.mjs'

/** The ops this host needs from the engine. */
export const SOLID_CLIENT_OPS = ['solidClientRequest', 'solidClientResponse']

/** An error raised by the Solid client host. `unknownOp` is set when the
 *  loaded WebAssembly module does not carry the operation at all. */
export class SolidClientHostError extends Error {
  constructor (message, detail = {}) {
    super(message)
    this.name = 'SolidClientHostError'
    this.unknownOp = detail.unknownOp === true
  }
}

function isUnknownOp (error) {
  const text = error && error.message ? String(error.message) : String(error)
  return text.indexOf('unknown op') >= 0
}

/**
 * Whether the loaded engine carries the Solid client operations.
 *
 * @param {object} engine the handle from `loadEngine()`
 * @returns {Promise<{available: boolean, reason: string}>}
 */
export async function solidClientOpsAvailable (engine) {
  try {
    engine.call('solidClientRequest', ['get', JSON.stringify({ probe: true })])
    return { available: true, reason: 'solidClientRequest answered' }
  } catch (error) {
    if (isUnknownOp(error)) {
      return {
        available: false,
        reason: 'the loaded l4factoidal WebAssembly module does not carry ' +
          'the solid client ops (rebuild formal/lean4/Wasm)'
      }
    }
    return { available: true, reason: 'solidClientRequest answered with an engine error' }
  }
}

function requestOf (envelope) {
  if (envelope === null || typeof envelope !== 'object') {
    throw new SolidClientHostError('solidClientRequest answered with no envelope')
  }
  if (envelope.done === true) return null
  const record = (envelope.request !== null && typeof envelope.request === 'object')
    ? envelope.request
    : envelope
  if (typeof record.method !== 'string' || typeof record.target !== 'string') {
    throw new SolidClientHostError(
      'solidClientRequest answered with no method and target')
  }
  return {
    method: record.method,
    target: record.target,
    headers: Array.isArray(record.headers) ? record.headers : [],
    body: typeof record.body === 'string' ? record.body : null
  }
}

/** The reply as the JSON response record the contract states. */
async function recordOfReply (reply) {
  const headers = []
  reply.headers.forEach((value, name) => { headers.push([name, value]) })
  return {
    status: reply.status,
    headers,
    body: await reply.text()
  }
}

/**
 * A Solid client bound to one engine and one `fetch`.
 *
 * @param {object} [options]
 * @param {object} [options.engine] an engine handle to reuse
 * @param {Function} [options.fetch] the fetch to use (default `globalThis.fetch`)
 * @param {number} [options.maxSteps] the loop cap for a multi-step operation
 * @returns {Promise<{run: Function, get: Function, put: Function,
 *                    post: Function, delete: Function, discover: Function,
 *                    engine: object}>}
 */
export async function createSolidClient (options = {}) {
  const engine = options.engine !== undefined ? options.engine : await loadEngine()
  const wire = typeof options.fetch === 'function' ? options.fetch : globalThis.fetch
  if (typeof wire !== 'function') {
    throw new SolidClientHostError('no fetch is available in this runtime')
  }
  const maxSteps = typeof options.maxSteps === 'number' ? options.maxSteps : 16

  /**
   * Run one client operation to its end.
   *
   * @param {string} kind the operation name the engine dispatches on
   * @param {object} args the operation's arguments, passed unread
   * @returns {Promise<object>} whatever `solidClientResponse` answered
   */
  async function run (kind, args) {
    let state = null
    let interpretation = null
    for (let step = 0; step < maxSteps; step += 1) {
      const call = state === null ? { ...args } : { ...args, state }
      let built
      try {
        built = engine.call('solidClientRequest', [kind, JSON.stringify(call)])
      } catch (error) {
        if (isUnknownOp(error)) {
          throw new SolidClientHostError(
            'the loaded l4factoidal WebAssembly module does not carry ' +
            'solidClientRequest', { unknownOp: true })
        }
        throw error
      }
      const request = requestOf(built)
      if (request === null) return built
      const headers = {}
      for (const pair of request.headers) {
        if (!Array.isArray(pair) || pair.length < 2) continue
        headers[pair[0]] = headers[pair[0]] === undefined
          ? String(pair[1])
          : `${headers[pair[0]]}, ${String(pair[1])}`
      }
      const reply = await wire(request.target, {
        method: request.method,
        headers,
        body: request.body === null ? undefined : request.body,
        redirect: 'manual'
      })
      const record = await recordOfReply(reply)
      record.target = request.target
      record.method = request.method
      if (built.state !== undefined) record.state = built.state
      try {
        interpretation = engine.call('solidClientResponse', [kind, JSON.stringify(record)])
      } catch (error) {
        if (isUnknownOp(error)) {
          throw new SolidClientHostError(
            'the loaded l4factoidal WebAssembly module does not carry ' +
            'solidClientResponse', { unknownOp: true })
        }
        throw error
      }
      if (interpretation === null || typeof interpretation !== 'object') {
        throw new SolidClientHostError('solidClientResponse answered with no envelope')
      }
      if (interpretation.continue !== true) return interpretation
      state = interpretation.state === undefined ? null : interpretation.state
    }
    throw new SolidClientHostError(
      `the "${kind}" operation did not finish within ${maxSteps} requests`)
  }

  return {
    engine,
    run,
    discover: (url, extra = {}) => run('discover', { url, ...extra }),
    get: (url, extra = {}) => run('get', { url, ...extra }),
    put: (url, body, extra = {}) => run('put', { url, body, ...extra }),
    post: (url, body, extra = {}) => run('post', { url, body, ...extra }),
    delete: (url, extra = {}) => run('delete', { url, ...extra }),
    patch: (url, body, extra = {}) => run('patch', { url, body, ...extra }),
    profile: (webid, extra = {}) => run('profile', { url: webid, ...extra })
  }
}
