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
// Fixed in docs/lws-solid-conformance.md, section "wasm ABI".
//   solidClientRequest  [kind, argsJson]     -> { ok, request }
//   solidClientResponse [kind, responseJson] -> { ok, interpretation }
//
//   request  { method, target, headers: [[name, value]], body }
//   response { status, headers: [[name, value]], body }
//
// The two operations take DIFFERENT kind vocabularies, and this host
// keeps them apart rather than deriving one from the other.
//
//   request kinds:        read, create, replace, patch, delete,
//                         discoverStorage, readProfile
//   interpretation kinds: storage, containment, auxiliaries, profile,
//                         wacAllow
//
// Which interpretation a reply wants is a protocol decision, so this
// file never picks one. It uses, in order: the `interpret` member the
// request envelope named, then the `interpret` the caller passed. With
// neither, the reply is returned uninterpreted and `interpretation` is
// null -- the raw record, never a host reading of it.
//
// A multi-step operation is a loop, not a special case: an
// interpretation that answers `{ continue: true, state }` sends the
// state back into the next `solidClientRequest`. Walking from a resource
// up to its storage root is the case that needs it. A single-request
// operation runs the loop once, and the loop is capped so a state that
// never settles is a reported failure rather than a hang.
//
// This file shares no code with `../server/index.mjs` beyond the engine
// loader.

import { loadEngine } from '../../bin/engine.mjs'

/** The ops this host needs from the engine. */
export const SOLID_CLIENT_OPS = ['solidClientRequest', 'solidClientResponse']

/** The request kinds the ABI names. Listed so a caller can be checked
 *  against the contract; this host attaches no meaning to any of them. */
export const SOLID_REQUEST_KINDS = [
  'read', 'create', 'replace', 'patch', 'delete', 'discoverStorage', 'readProfile'
]

/** The interpretation kinds the ABI names. */
export const SOLID_INTERPRETATION_KINDS = [
  'storage', 'containment', 'auxiliaries', 'profile', 'wacAllow'
]

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
    engine.call('solidClientRequest', ['read', JSON.stringify({ target: '/' })])
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

function interpretationOf (envelope) {
  if (envelope === null || typeof envelope !== 'object') {
    throw new SolidClientHostError('solidClientResponse answered with no envelope')
  }
  return (envelope.interpretation !== null && typeof envelope.interpretation === 'object')
    ? envelope.interpretation
    : envelope
}

/** The reply as the JSON response record the contract states. */
async function recordOfReply (reply) {
  const headers = []
  reply.headers.forEach((value, name) => { headers.push([name, value]) })
  return { status: reply.status, headers, body: await reply.text() }
}

/**
 * A Solid client bound to one engine and one `fetch`.
 *
 * @param {object} [options]
 * @param {object} [options.engine] an engine handle to reuse
 * @param {Function} [options.fetch] the fetch to use (default `globalThis.fetch`)
 * @param {string} [options.baseIri] prefixed to a request target that is a path
 * @param {number} [options.maxSteps] the loop cap for a multi-step operation
 * @returns {Promise<object>} the client
 */
export async function createSolidClient (options = {}) {
  const engine = options.engine !== undefined ? options.engine : await loadEngine()
  const wire = typeof options.fetch === 'function' ? options.fetch : globalThis.fetch
  if (typeof wire !== 'function') {
    throw new SolidClientHostError('no fetch is available in this runtime')
  }
  const maxSteps = typeof options.maxSteps === 'number' ? options.maxSteps : 16
  const baseIri = typeof options.baseIri === 'string' ? options.baseIri : null

  /** Where to send a request whose target the engine wrote as a path.
   *  This is address resolution, not IRI construction: the engine's
   *  target is used verbatim when it is already absolute. */
  function endpoint (target) {
    if (/^[a-zA-Z][a-zA-Z0-9+.-]*:/.test(target)) return target
    if (baseIri === null) {
      throw new SolidClientHostError(
        `the engine answered the path "${target}" and this client has no ` +
        'baseIri to send it to; pass baseIri to createSolidClient')
    }
    return baseIri.replace(/\/$/, '') + target
  }

  function callRequest (kind, args) {
    try {
      return engine.call('solidClientRequest', [kind, JSON.stringify(args)])
    } catch (error) {
      if (isUnknownOp(error)) {
        throw new SolidClientHostError(
          'the loaded l4factoidal WebAssembly module does not carry ' +
          'solidClientRequest', { unknownOp: true })
      }
      throw error
    }
  }

  function callResponse (kind, record) {
    try {
      return engine.call('solidClientResponse', [kind, JSON.stringify(record)])
    } catch (error) {
      if (isUnknownOp(error)) {
        throw new SolidClientHostError(
          'the loaded l4factoidal WebAssembly module does not carry ' +
          'solidClientResponse', { unknownOp: true })
      }
      throw error
    }
  }

  /**
   * Run one client operation to its end.
   *
   * @param {string} kind a request kind from `SOLID_REQUEST_KINDS`
   * @param {object} args the operation's arguments, passed unread
   * @param {object} [extra] `interpret`: an interpretation kind to use
   *   when the request envelope names none
   * @returns {Promise<{kind: string, request: object, response: object,
   *                    interpret: string|null, interpretation: object|null,
   *                    steps: number}>}
   */
  async function run (kind, args, extra = {}) {
    let state = null
    for (let step = 1; step <= maxSteps; step += 1) {
      const built = callRequest(kind, state === null ? args : { ...args, state })
      const request = requestOf(built)
      const headers = {}
      for (const pair of request.headers) {
        if (!Array.isArray(pair) || pair.length < 2) continue
        headers[pair[0]] = headers[pair[0]] === undefined
          ? String(pair[1])
          : `${headers[pair[0]]}, ${String(pair[1])}`
      }
      const reply = await wire(endpoint(request.target), {
        method: request.method,
        headers,
        body: request.body === null ? undefined : request.body,
        redirect: 'manual'
      })
      const record = await recordOfReply(reply)
      const interpretKind = typeof built.interpret === 'string'
        ? built.interpret
        : (typeof extra.interpret === 'string' ? extra.interpret : null)
      const answer = {
        kind,
        request,
        response: record,
        interpret: interpretKind,
        interpretation: null,
        steps: step
      }
      if (interpretKind === null) return answer
      const interpretation = interpretationOf(callResponse(interpretKind, record))
      answer.interpretation = interpretation
      if (interpretation.continue !== true) return answer
      state = interpretation.state === undefined ? null : interpretation.state
    }
    throw new SolidClientHostError(
      `the "${kind}" operation did not finish within ${maxSteps} requests`)
  }

  return {
    engine,
    run,
    /** Named wrappers over `run`. Each one passes its arguments through;
     *  none of them adds a header, a media type or a URL. */
    read: (target, extra = {}) => run('read', { target, ...extra }),
    create: (target, body, contentType, extra = {}) =>
      run('create', { target, body, contentType, ...extra }),
    replace: (target, body, contentType, extra = {}) =>
      run('replace', { target, body, contentType, ...extra }),
    patch: (target, body, contentType, extra = {}) =>
      run('patch', { target, body, contentType, ...extra }),
    delete: (target, extra = {}) => run('delete', { target, ...extra }),
    discoverStorage: (target, extra = {}) =>
      run('discoverStorage', { target, interpret: 'storage', ...extra },
        { interpret: 'storage' }),
    readProfile: (target, extra = {}) =>
      run('readProfile', { target, ...extra }, { interpret: 'profile' })
  }
}
