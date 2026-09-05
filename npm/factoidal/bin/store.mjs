// Driving the three WebAssembly store operations from a JavaScript host.
// https://github.com/danbri/factoidal/issues/641
//
// WHAT THIS FILE IS ALLOWED TO DO
// Read CURRENT, read a manifest file by name, read the artifact files the
// engine's plan named, concatenate their bytes, and hand them over. It
// never parses a manifest, never verifies a digest, never decodes a block
// and never decides which artifact answers a query. Every one of those is
// a format decision and it lives in `formal/lean4/Wasm/Ops/Store.lean`
// (iron rule 7 of CLAUDE.md). A reviewer who finds a magic number, a
// field offset or a hash in this file has found a rule violation.
//
// The operations and their envelopes are described in
// `docs/designissues/2026-09-03-wasm-shardborough-store-ops.md`.

import { openCollection, readWhole } from '../store-host/index.mjs'
import { joinPath } from '../store-host/paths.mjs'
import { hexOfBytes } from './engine.mjs'

/** The manifest file names a generation directory can carry, in the order
 *  `Harness.ShardMerklePread.readManifest` tries them. */
const MANIFEST_NAMES = ['manifest.sbm2', 'manifest.sbm1']

/**
 * An error the store operations reported. `capName` is set when the
 * refusal was one of the operation's caps; `message` is always the
 * engine's own words.
 */
export class StoreOperationError extends Error {
  constructor (message, detail = {}) {
    super(message)
    this.name = 'StoreOperationError'
    this.capValue = detail.capValue === undefined ? null : detail.capValue
    this.capLimit = detail.capLimit === undefined ? null : detail.capLimit
    this.digestKey = detail.digestKey === undefined ? null : detail.digestKey
    this.stackLimit = detail.stackLimit === true
  }
}

// The engine's refusals arrive as an Error whose message is
// "l4factoidal: <the operation's own text>". These two patterns say only
// WHICH refusal it was, so the command can add a next step; the text the
// user sees is always the engine's, never a rewrite of it.
const CAP_PATTERN = /the plan selects (\d+) (?:artifacts|artifact bytes|rows), the cap is (\d+)/
const DIGEST_PATTERN = /artifact '([^']*)' does not match the SHA-256/

function asStoreError (error) {
  const raw = error && error.message ? String(error.message) : String(error)
  const message = raw.replace(/^l4factoidal:\s*/, '')
  // Not a refusal by the engine: the host runtime ran out of call stack
  // inside the wasm module. Some evaluator paths recurse once per row.
  // Measured 2026-09-03 against the committed wasm, on a 6455-row
  // generation: `SELECT ?s ?p ?o WHERE { ?s ?p ?o }` and the same query
  // with `ORDER BY` overflow under Node's default WebAssembly frame
  // budget, while `SELECT *`, and either query with a LIMIT, do not.
  // `node --stack-size=4000` clears all of them, and Deno clears them at
  // its own default.
  if (error instanceof RangeError || message.indexOf('call stack size exceeded') >= 0) {
    return new StoreOperationError(message, { stackLimit: true })
  }
  const cap = CAP_PATTERN.exec(message)
  if (cap !== null) {
    return new StoreOperationError(message,
      { capValue: Number(cap[1]), capLimit: Number(cap[2]) })
  }
  const digest = DIGEST_PATTERN.exec(message)
  if (digest !== null) {
    return new StoreOperationError(message, { digestKey: digest[1] })
  }
  return new StoreOperationError(message)
}

/**
 * What to print when the runtime, not the engine, ran out of call stack.
 *
 * One copy of this text, used by every command that can hit the frame
 * budget. `remedy` is the one line that differs: a query can be made
 * smaller with a LIMIT, a pack cannot.
 *
 * The pack path normally never reaches this, because it runs on a worker
 * thread with a raised stack (`bin/pack-host.mjs`,
 * https://github.com/danbri/factoidal/issues/649). It is what a reader
 * sees when the worker route is refused with --no-worker, is unavailable
 * on their platform, or is not enough.
 *
 * @param {string} remedy
 * @returns {string[]} the lines, in order, for stderr
 */
export function stackLimitAdvice (remedy) {
  return [
    'The runtime ran out of call stack inside the engine, not the store.',
    'Some engine paths recurse once per row or per input chunk, and enough',
    "of them exceed the runtime's default WebAssembly frame budget.",
    remedy
  ]
}

/** The remedies for each command that can run out of frames. */
export const STACK_REMEDY = {
  query: 'Raise it with node --stack-size=4000, add a LIMIT, or use Deno.',
  pack: 'Raise it with node --stack-size=8000, or ' +
    'deno run --v8-flags=--stack-size=8000.'
}

/**
 * Open a store and return its manifest bytes.
 *
 * With no `generationName` the activated generation is opened through
 * CURRENT. With one, that generation is opened directly, which is how a
 * generation that has not been activated is inspected.
 *
 * @param {string} root the collection root that holds CURRENT
 * @param {string|null} generationName
 * @returns {{root: string, generation: string, generationDir: string,
 *            manifestName: string, manifest: Uint8Array,
 *            manifestHex: string, activated: boolean}}
 */
export function openStore (root, generationName = null) {
  if (typeof generationName !== 'string') {
    const opened = openCollection(root)
    return { ...opened, manifestHex: hexOfBytes(opened.manifest), activated: true }
  }
  const generationDir = joinPath(root, generationName)
  for (const manifestName of MANIFEST_NAMES) {
    let manifest
    try {
      manifest = readWhole(joinPath(generationDir, manifestName))
    } catch (_error) {
      continue
    }
    return {
      root,
      generation: generationName,
      generationDir,
      manifestName,
      manifest,
      manifestHex: hexOfBytes(manifest),
      activated: false
    }
  }
  throw new StoreOperationError(
    `${generationDir} has none of ${MANIFEST_NAMES.join(', ')}`)
}

/** `storeManifestInspect` — decode one manifest. */
export function inspectManifest (engine, store) {
  try {
    return engine.call('storeManifestInspect', [store.manifestHex])
  } catch (error) {
    throw asStoreError(error)
  }
}

/** `storeQueryPlan` — the artifact keys this query needs, and the mode. */
export function planQuery (engine, store, sparql) {
  try {
    return engine.call('storeQueryPlan', [store.manifestHex, sparql])
  } catch (error) {
    throw asStoreError(error)
  }
}

/**
 * Ask the engine to decide the caps before any file is read.
 *
 * `storeQuery` checks its three caps against the manifest's own
 * declarations BEFORE it looks at the artifact descriptors, so a call
 * carrying an empty descriptor list gets the cap decision without moving
 * a byte. The caps themselves stay where they are defined
 * (`Wasm/Ops/Store.lean`); this host holds none of their values.
 *
 * @returns the envelope when the plan needs no artifact at all, else null
 * @throws {StoreOperationError} when a cap refused the plan
 */
function capDecision (engine, store, sparql) {
  try {
    // callBlobIO, not callBlob: the blob-IO entry is the one that reaches
    // the SPARQL 1.1 section 17.6 extension registry (Wasm/Dispatch.lean's
    // callBlobIO), so a caller registration is in scope on the stateless
    // store path too. The envelope is identical.
    return engine.callBlobIO('storeQuery',
      [store.manifestHex, sparql, '[]'], new Uint8Array(0)).envelope
  } catch (error) {
    const refusal = asStoreError(error)
    if (refusal.message.indexOf('no bytes were supplied for artifact') >= 0) {
      return null
    }
    throw refusal
  }
}

/**
 * Evaluate one SPARQL query against one generation.
 *
 * The sequence is: plan, cap decision, read exactly the artifacts the
 * plan named, concatenate them into one buffer, and call `storeQuery`
 * with a `{"key","offset","len"}` window per artifact. The buffer is
 * written straight into the wasm heap by `engine.callBlobIO` with no
 * encoding, and the engine bounds-checks every window.
 *
 * @returns {{plan: object, result: object, blobBytes: number,
 *            artifacts: {key: string, offset: number, len: number}[]}}
 */
export function queryStore (engine, store, sparql) {
  const plan = planQuery(engine, store, sparql)
  const empty = capDecision(engine, store, sparql)
  if (empty !== null) {
    return { plan, result: empty, blobBytes: 0, artifacts: [] }
  }
  const chunks = plan.keys.map((key) => readWhole(joinPath(store.generationDir, key)))
  let total = 0
  for (const chunk of chunks) total += chunk.length
  const blob = new Uint8Array(total)
  const artifacts = []
  let offset = 0
  for (let index = 0; index < chunks.length; index += 1) {
    blob.set(chunks[index], offset)
    artifacts.push({ key: plan.keys[index], offset, len: chunks[index].length })
    offset += chunks[index].length
  }
  let result
  try {
    result = engine.callBlobIO('storeQuery',
      [store.manifestHex, sparql, JSON.stringify(artifacts)], blob).envelope
  } catch (error) {
    throw asStoreError(error)
  }
  return { plan, result, blobBytes: total, artifacts }
}

/**
 * `serializeTurtle` — the engine's own Turtle writer, over the N-Quads a
 * CONSTRUCT answered. Named graphs are flattened into the default graph
 * on this path; `--format nquads` is the fidelity-preserving one.
 */
export function turtleOfNQuads (engine, nquads) {
  try {
    return engine.call('serializeTurtle', [nquads]).turtle
  } catch (error) {
    throw asStoreError(error)
  }
}

// ---------------------------------------------------------------- handles
//
// `queryStore` above is stateless: every call transfers the artifacts again,
// and the engine hashes, decodes and indexes them again. A process that
// answers many questions against one generation — a chat bot, an MCP server,
// a SPARQL endpoint — pays that per question, and none of it depends on the
// question.
//
// A handle holds the verified, decoded, indexed form inside the engine.
// `storeOpen` verifies every artifact against the SHA-256 the manifest
// commits, once; `storeHandleQuery` then answers from what it retained. The
// engine refuses a query whose plan needs a block the handle does not retain,
// so a handle answer is never a partial generation.
//
// What a handle does NOT change: a query still scans every retained row, so
// its cost is still proportional to the row count. A handle removes the
// per-query decode; it is not a text index.
//
// The stateless path above stays exactly as it was. A one-shot CLI query
// should not pay to build a handle it will drop.

/**
 * The artifact keys a manifest declares, in manifest order: every block, and
 * every index sidecar the entry names. The KEYS come from the engine; this
 * function chooses none of them. A sidecar is what lets a literal search skip
 * the scan (SBM8's LGI1); a generation that declares none is unaffected.
 */
function manifestKeys (engine, store) {
  const keys = []
  for (const entry of inspectManifest(engine, store).entries) {
    keys.push(entry.key)
    for (const key of Object.values(entry.sidecars ?? {})) keys.push(key)
  }
  return keys
}

/** Read the named artifacts and concatenate them into one region. */
function regionOf (store, keys) {
  const chunks = keys.map((key) => readWhole(joinPath(store.generationDir, key)))
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
  return { blob, artifacts }
}

/**
 * An open store held inside the engine. Hold this object for as long as the
 * process answers questions about the generation, then `close()` it.
 *
 * The wasm module is single-threaded: two `query()` calls cannot overlap. A
 * server awaits one before it starts the next.
 */
export class StoreHandle {
  constructor (engine, store, envelope) {
    this.engine = engine
    this.store = store
    this.handle = envelope.handle
    this.identity = envelope.identity
    this.layout = envelope.layout
    this.wireVersion = envelope.wireVersion
    this.artifacts = envelope.artifacts
    this.bytes = envelope.bytes
    this.rows = envelope.rows
    this.closed = false
  }

  /**
   * One SPARQL query against the retained blocks. The envelope is the one
   * `queryStore` answers with — `kind`, `srj`/`boolean`/`nquads`, plus
   * `shards` and `mode` — so a caller handles both paths alike.
   */
  query (sparql) {
    if (this.closed) {
      throw new StoreOperationError(`store handle ${this.handle} is closed`)
    }
    try {
      return this.engine.call('storeHandleQuery', [this.handle, sparql])
    } catch (error) {
      throw asStoreError(error)
    }
  }

  /** Drop the handle and everything it retained. Idempotent on this object. */
  close () {
    if (this.closed) return
    this.closed = true
    try {
      this.engine.call('storeHandleClose', [this.handle])
    } catch (error) {
      throw asStoreError(error)
    }
  }
}

/**
 * `storeOpen` — verify, decode and index a generation once.
 *
 * With no options every artifact the manifest declares is opened, so any
 * query the generation can answer works. With `sparql` only the artifacts
 * that query's plan names are opened, which is what a process asking one
 * query shape wants. With `keys` exactly those artifacts are opened.
 *
 * @param {object} engine the loaded engine (bin/engine.mjs)
 * @param {object} store  the result of `openStore`
 * @param {{keys?: string[], sparql?: string}} options
 * @returns {StoreHandle}
 */
export function openStoreHandle (engine, store, options = {}) {
  let keys
  if (Array.isArray(options.keys)) {
    keys = options.keys
  } else if (typeof options.sparql === 'string') {
    const plan = planQuery(engine, store, options.sparql)
    keys = plan.keys.concat(plan.sidecarKeys ?? [])
  } else {
    keys = manifestKeys(engine, store)
  }
  const { blob, artifacts } = regionOf(store, keys)
  let envelope
  try {
    envelope = engine.callBlobIO('storeOpen',
      [store.manifestHex, JSON.stringify(artifacts)], blob).envelope
  } catch (error) {
    throw asStoreError(error)
  }
  return new StoreHandle(engine, store, envelope)
}

/** `storeHandleQuery` — the loose form, for a caller holding only the id. */
export function queryStoreHandle (engine, handle, sparql) {
  const id = typeof handle === 'string' ? handle : handle.handle
  try {
    return engine.call('storeHandleQuery', [id, sparql])
  } catch (error) {
    throw asStoreError(error)
  }
}

/** `storeHandleClose` — the loose form. */
export function closeStoreHandle (engine, handle) {
  if (handle instanceof StoreHandle) return handle.close()
  try {
    return engine.call('storeHandleClose', [handle])
  } catch (error) {
    throw asStoreError(error)
  }
}

/**
 * `storeHandleList` — what this process holds open, with the retained bytes
 * and rows and the two residency caps. A server that cannot see its own
 * residency cannot be operated.
 */
export function listStoreHandles (engine) {
  try {
    return engine.call('storeHandleList', [])
  } catch (error) {
    throw asStoreError(error)
  }
}
