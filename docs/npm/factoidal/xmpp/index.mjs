// factoidal/xmpp — a functional-programming-style API over
// `L4Factoidal.XMPP` (formal/lean4/L4Factoidal/XMPP/README.md), the
// GC3-targeting XMPP implementation in Lean 4, served through the same
// wasm dispatch ABI as the rest of the Lean engine
// (formal/lean4/Wasm/Dispatch.lean, formal/lean4/Wasm/Ops/Xmpp.lean).
//
// Design record: formal/lean4/L4Factoidal/XMPP/README.md
//
// WHAT "FUNCTIONAL-PROGRAMMING-STYLE" MEANS HERE, CONCRETELY
//   - Every exported function is pure data in, pure data out: plain
//     strings/objects/arrays, no classes, no mutable instances to hold.
//   - No exceptions for an EXPECTED outcome. A malformed JID, a stanza
//     that isn't message/presence/iq, an unknown negotiation stage —
//     these are ordinary answers, not exceptional control flow, so
//     every function returns a `{ok: true, value}` or
//     `{ok: false, error, unknownOp}` result (a Result/Either shape),
//     never throws for them. The one thing that still throws is a
//     genuine host/environment failure (the wasm module won't load at
//     all) — see `loadXmppEngine()`.
//   - Immutable results: nothing returned here is later mutated by this
//     module. Build a new value; don't hand back something to poke at.
//
// WHAT THIS COVERS (matches exactly what `L4Factoidal.XMPP` implements
// today, 2026-09-07 — see the design record's "Status" section):
//   - RFC 7622 JID parsing/rendering (`parseJid`, `renderJid`)
//   - RFC 6120 stream header parsing/rendering (`parseStreamHeader`,
//     `renderStreamHeader`) — tolerates the leading `<?xml ...?>`
//     declaration real servers send (caught testing against a live
//     ejabberd instance; see the design record)
//   - RFC 6120 `<stream:features>` negotiation (`featuresFor`) — the
//     TLS-then-SASL-then-bind ordering is a proved Lean theorem, not
//     just this JS wrapper's behaviour
//   - stanza parsing (`parseStanza`) for message/presence/iq
//
// WHAT THIS DOES NOT COVER YET, ON PURPOSE (ask for the op with
// `xmppOpsAvailable()`'s companion `ops` reflection before relying on
// it; an absent op means the resolved wasm predates it, not that this
// wrapper forgot it):
//   - stanza construction FROM JSON (payload reconstruction needs a
//     sibling-node XML parser the Lean side doesn't have yet)
//   - GC3 itself (still an unfinished upstream XSF spec)
//   - SASL/SCRAM computation (message FORMAT only exists so far; no
//     HACL* HMAC-SHA-256 binding yet — see the design record's crypto
//     section)
//   - MUC/MIX interop modules

import { loadEngine } from '../bin/engine.mjs'

/** The XMPP op names this module calls. */
export const XMPP_OPS = [
  'xmppJidParse',
  'xmppJidRender',
  'xmppStreamHeaderParse',
  'xmppStreamHeaderRender',
  'xmppFeaturesFor',
  'xmppStanzaParse'
]

function isUnknownOp (error) {
  const text = error && error.message ? String(error.message) : String(error)
  return text.indexOf('unknown op') >= 0
}

/**
 * Load the engine handle this module's functions need. Exposed so a
 * caller can load it once and pass it to every call via `options.engine`
 * instead of paying the load cost per call — the one place in this
 * module where "just call the function" isn't free, so it isn't hidden.
 *
 * @returns {Promise<object>} an engine handle with a `.call(op, args)` method
 * @throws if the wasm module cannot be resolved or loaded at all — a
 *   host/environment failure, not a protocol-level outcome, so this is
 *   the one thing in this module that DOES throw
 */
export async function loadXmppEngine () {
  return loadEngine()
}

/**
 * Whether the loaded engine carries the XMPP ops at all — protects
 * against a resolved wasm bundle built before they existed.
 *
 * @param {object} [options]
 * @param {object} [options.engine] an engine handle to reuse
 * @returns {Promise<{available: boolean, missing: string[]}>}
 */
export async function xmppOpsAvailable (options = {}) {
  const engine = options.engine !== undefined ? options.engine : await loadXmppEngine()
  let names
  try {
    names = engine.call('ops', []).ops
  } catch (_error) {
    return { available: false, missing: XMPP_OPS.slice() }
  }
  const missing = XMPP_OPS.filter((op) => !names.includes(op))
  return { available: missing.length === 0, missing }
}

/** Call one op, converting the engine's throw-on-`{ok:false}` convention
 * into a Result value instead — the point of this module's shape. */
function callOp (engine, op, args) {
  try {
    return engine.call(op, args)
  } catch (error) {
    return { ok: false, error: String((error && error.message) || error), unknownOp: isUnknownOp(error) }
  }
}

/**
 * Parse an RFC 7622 JID string.
 *
 * Structural + length well-formedness only (per RFC 7622 §3.1); PRECIS
 * enforcement (RFC 8264/8265 — Unicode normalisation, case folding,
 * disallowed codepoints) is not implemented on the Lean side yet, so a
 * string with disallowed characters but the right shape parses as
 * `wellFormed: true`. This is a stated engine gap, not a wrapper bug.
 *
 * @param {string} jid
 * @param {object} [options]
 * @param {object} [options.engine] an engine handle to reuse
 * @returns {Promise<{ok: true, value: {localpart: string|null,
 *   domainpart: string, resourcepart: string|null, wellFormed: boolean}}
 *   | {ok: false, error: string, unknownOp: boolean}>}
 */
export async function parseJid (jid, options = {}) {
  const engine = options.engine !== undefined ? options.engine : await loadXmppEngine()
  const result = callOp(engine, 'xmppJidParse', [String(jid)])
  if (result.ok === false) return result
  const { ok, ...value } = result
  return { ok: true, value }
}

/**
 * Render a JID from its parts back to a string.
 *
 * @param {{localpart?: string|null, domainpart: string, resourcepart?: string|null}} parts
 * @param {object} [options]
 * @param {object} [options.engine] an engine handle to reuse
 * @returns {Promise<{ok: true, value: string} | {ok: false, error: string, unknownOp: boolean}>}
 */
export async function renderJid (parts, options = {}) {
  const engine = options.engine !== undefined ? options.engine : await loadXmppEngine()
  const result = callOp(engine, 'xmppJidRender', [JSON.stringify(parts)])
  if (result.ok === false) return result
  return { ok: true, value: result.jid }
}

/**
 * Parse an RFC 6120 `<stream:stream ...>` opening tag. Unlike an
 * ordinary stanza this element is never closed until the connection
 * ends, so `rest` is the unconsumed remainder of the input (features,
 * stanzas, and eventually `</stream:stream>`) for the caller to parse
 * separately.
 *
 * @param {string} xml
 * @param {object} [options]
 * @param {object} [options.engine] an engine handle to reuse
 * @returns {Promise<{ok: true, value: {from: string|null, to: string|null,
 *   id: string|null, version: string|null, lang: string|null, rest: string}}
 *   | {ok: false, error: string, unknownOp: boolean}>}
 */
export async function parseStreamHeader (xml, options = {}) {
  const engine = options.engine !== undefined ? options.engine : await loadXmppEngine()
  const result = callOp(engine, 'xmppStreamHeaderParse', [String(xml)])
  if (result.ok === false) return result
  const { ok, ...value } = result
  return { ok: true, value }
}

/**
 * Render an RFC 6120 stream header back to its opening-tag XML.
 *
 * @param {{from?: string|null, to?: string|null, id?: string|null,
 *   version?: string|null, lang?: string|null}} header
 * @param {object} [options]
 * @param {object} [options.engine] an engine handle to reuse
 * @returns {Promise<{ok: true, value: string} | {ok: false, error: string, unknownOp: boolean}>}
 */
export async function renderStreamHeader (header, options = {}) {
  const engine = options.engine !== undefined ? options.engine : await loadXmppEngine()
  const result = callOp(engine, 'xmppStreamHeaderRender', [JSON.stringify(header)])
  if (result.ok === false) return result
  return { ok: true, value: result.xml }
}

/**
 * What to advertise in `<stream:features>` at a given negotiation stage.
 * The RFC 6120 ordering (STARTTLS only pre-TLS, SASL mechanisms only
 * post-TLS, bind/session only once authenticated) is a proved theorem
 * on the Lean side (`Core.featuresFor_startTls_iff_preTls` etc.) — this
 * function cannot be called into producing a value that violates it,
 * because no such value exists to return.
 *
 * @param {'preTls'|'postTls'|'authenticated'|'bound'} stage
 * @param {string[]} [mechanisms] SASL mechanism names to offer at `postTls`
 * @param {object} [options]
 * @param {object} [options.engine] an engine handle to reuse
 * @returns {Promise<{ok: true, value: {startTlsRequired: 'required'|'optional'|null,
 *   saslMechanisms: string[], canBind: boolean, canSession: boolean, xml: string}}
 *   | {ok: false, error: string, unknownOp: boolean}>}
 */
export async function featuresFor (stage, mechanisms = [], options = {}) {
  const engine = options.engine !== undefined ? options.engine : await loadXmppEngine()
  const result = callOp(engine, 'xmppFeaturesFor', [JSON.stringify({ stage, mechanisms })])
  if (result.ok === false) return result
  const { ok, ...value } = result
  return { ok: true, value }
}

/**
 * Parse a complete `message`/`presence`/`iq` stanza. Payload children
 * are returned as their serialized XML fragment (`payloadXml`), not a
 * structured tree — see the module header for why stanza construction
 * from JSON isn't offered yet.
 *
 * @param {string} xml
 * @param {object} [options]
 * @param {object} [options.engine] an engine handle to reuse
 * @returns {Promise<{ok: true, value: {kind: 'message'|'presence'|'iq',
 *   id: string|null, from: string|null, to: string|null, type: string|null,
 *   payloadXml: string}} | {ok: false, error: string, unknownOp: boolean}>}
 */
export async function parseStanza (xml, options = {}) {
  const engine = options.engine !== undefined ? options.engine : await loadXmppEngine()
  const result = callOp(engine, 'xmppStanzaParse', [String(xml)])
  if (result.ok === false) return result
  const { ok, ...value } = result
  return { ok: true, value }
}
