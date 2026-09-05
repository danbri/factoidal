// Caller-registered SPARQL 1.1 §17.6 extension functions for the Lean
// engine. https://github.com/danbri/factoidal/issues/463 (the F* side),
// docs/designissues/2026-09-04-lean-extension-functions.md (this side).
//
// WHAT THIS FILE IS ALLOWED TO DO
// Hold the caller's functions, carry values across the boundary, and
// memoise. It makes NO semantic decision: which IRIs may reach a
// registered function, what an absent answer means, and how a §17.6
// error behaves are all decided in Lean (Wasm/Ops/ExtFns.lean and the
// evaluator). A JavaScript answer this file cannot encode becomes the
// empty string, which Lean reads as the §17.6 error — the same outcome
// as a function that is not registered at all.
//
// THE BRIDGE
// One function, globalThis.__factoidalExtCall(iri, argsJson), which the
// EM_JS body in formal/lean4/ffi/l4_ext.c calls SYNCHRONOUSLY from
// inside the evaluator. `argsJson` is a JSON array of SPARQL Query
// Results JSON binding-value objects; the answer is one such object as
// a JSON string, or the empty string for "no value".
//
// ASYNC
// The evaluator is synchronous and inside WebAssembly, so it cannot wait
// for a promise. The F* engine's answer is reused verbatim
// (npm/factoidal/browser.js, withExtensionRounds): the bridge starts the
// promise, records it, and answers "no value" for this round; the host
// awaits every pending promise, writes the answers into the memo table,
// and runs the WHOLE query again, until a round adds no new pending
// call.
//
// DETERMINISM
// The memo table is keyed on iri + ' ' + argsJson and lives for one
// top-level query, so the same call answers the same way however many
// times the physical plan evaluates the expression, and across
// re-evaluation rounds.

const XSD = 'http://www.w3.org/2001/XMLSchema#'

/** How many evaluation rounds an async resolution may take. */
export const EXT_MAX_ROUNDS = 25

const extFunctions = new Map()
const extRegistered = new Set()
let extCache = new Map()
let extPending = []
let bridgeInstalled = false

/**
 * Encode one JavaScript answer as an SRJ binding-value object, as a JSON
 * string. `''` means "no value" — the §17.6 error.
 */
function encodeAnswer (out) {
  if (out === null || out === undefined) return ''
  if (typeof out === 'boolean') {
    return JSON.stringify({ type: 'literal', value: out ? 'true' : 'false', datatype: XSD + 'boolean' })
  }
  if (typeof out === 'number') {
    if (!Number.isFinite(out)) return ''
    return Number.isInteger(out)
      ? JSON.stringify({ type: 'literal', value: String(out), datatype: XSD + 'integer' })
      : JSON.stringify({ type: 'literal', value: String(out), datatype: XSD + 'double' })
  }
  if (typeof out === 'string') {
    return JSON.stringify({ type: 'literal', value: out })
  }
  if (typeof out === 'object' && typeof out.type === 'string') {
    // Already an SRJ binding-value object (or an RDF/JS-shaped term the
    // caller built): pass it through and let the Lean decoder judge it.
    return JSON.stringify(out)
  }
  return ''
}

/** The synchronous bridge the wasm module calls. */
function extBridge (iri, argsJson) {
  const key = iri + ' ' + argsJson
  if (extCache.has(key)) return extCache.get(key)
  const fn = extFunctions.get(iri)
  if (typeof fn !== 'function') return ''
  let out
  try {
    out = fn(JSON.parse(argsJson))
  } catch (_error) {
    extCache.set(key, '')
    return ''
  }
  if (out !== null && typeof out === 'object' && typeof out.then === 'function') {
    extPending.push({ key, promise: out })
    return ''
  }
  const encoded = encodeAnswer(out)
  extCache.set(key, encoded)
  return encoded
}

function installBridge () {
  if (bridgeInstalled) return
  globalThis.__factoidalExtCall = extBridge
  bridgeInstalled = true
}

/**
 * Register one function under an absolute IRI.
 *
 * `fn` receives the evaluated arguments as an array of SRJ
 * binding-value objects and returns a term object, a JavaScript
 * string/number/boolean, `null`/`undefined` (the §17.6 error), or a
 * promise of any of those.
 *
 * Scope: per loaded engine (one wasm module instance). A server that
 * serves more than one caller uses `withExtensionFunctions` instead, or
 * loads one engine per caller.
 */
export function registerExtensionFunction (engine, iri, fn) {
  if (typeof iri !== 'string' || !/^[A-Za-z][A-Za-z0-9+.-]*:/.test(iri)) {
    throw new TypeError('registerExtensionFunction: iri must be an absolute IRI string')
  }
  if (typeof fn !== 'function') {
    throw new TypeError('registerExtensionFunction: fn must be a function')
  }
  installBridge()
  extFunctions.set(iri, fn)
  engine.call('extRegister', [iri])
  extRegistered.add(iri)
}

/** Remove one registered function. */
export function unregisterExtensionFunction (engine, iri) {
  extFunctions.delete(iri)
  extRegistered.delete(iri)
  engine.call('extUnregister', [iri])
}

/** Return the engine to the built-in table (`geof:` and the built-ins). */
export function clearExtensionFunctions (engine) {
  extFunctions.clear()
  extRegistered.clear()
  engine.call('extClear', [])
}

/** The IRIs the engine will ask the host about. */
export function listExtensionFunctions (engine) {
  return engine.call('extList', []).iris
}

/**
 * Run `body` with a fresh per-query memo table, resolving async answers
 * by re-evaluation. `body` is called once per round and must be the
 * WHOLE query, because a later round re-evaluates it with more answers
 * known.
 */
export async function withExtensionRounds (body) {
  extCache = new Map()
  for (let round = 0; ; round += 1) {
    extPending = []
    const result = body()
    if (extPending.length === 0) return result
    if (round >= EXT_MAX_ROUNDS) {
      throw new Error(
        'extension functions: async resolution did not converge within ' +
        `${EXT_MAX_ROUNDS} evaluation rounds`)
    }
    const pending = extPending
    extPending = []
    await Promise.all(pending.map(async ({ key, promise }) => {
      try {
        extCache.set(key, encodeAnswer(await promise))
      } catch (_error) {
        extCache.set(key, '')
      }
    }))
  }
}

/**
 * Run one query with a fresh memo table. Use this for a synchronous
 * function set; use `withExtensionRounds` when any function is async.
 */
export function withFreshMemo (body) {
  extCache = new Map()
  extPending = []
  return body()
}

/**
 * Register `map` (IRI -> function), run `body`, and clear in a
 * `finally`. This is the scope a long-lived server wants: one caller's
 * registrations are never visible to the next.
 */
export async function withExtensionFunctions (engine, map, body) {
  for (const [iri, fn] of Object.entries(map)) {
    registerExtensionFunction(engine, iri, fn)
  }
  try {
    return await withExtensionRounds(body)
  } finally {
    clearExtensionFunctions(engine)
  }
}
