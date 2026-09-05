// Giving the store operations a call stack big enough to finish, without
// asking the reader for a runtime flag.
// https://github.com/danbri/factoidal/issues/653
//
// THE DEFECT THIS FILE EXISTS FOR
// Several engine paths recurse once per manifest entry or once per row.
// On a large generation that exceeds the default call stack of Node and
// of Deno, and the failure is `Maximum call stack size exceeded` rather
// than an engine refusal. MEASURED 2026-09-05 against the committed
// module, on a 7,315,251-quad collection of 3,286 blocks in 204 graphs
// (`/Users/danbri/working/factoidal-skosfull`): `storeQueryPlan` alone
// overflows on plain `node`, before a single artifact byte is read, and
// `node --stack-size=60000` clears the plan, the open and every query.
// Earlier the same limit was narrowed to any query that materialises
// about 14,576 rows or more, whatever it returns.
//
// `factoidal pack` had the same defect and it was solved host-side, on a
// worker thread with a raised stack (`bin/pack-host.mjs`,
// https://github.com/danbri/factoidal/issues/649). This file carries that
// route to the store operations.
//
// WHY THE HANDLE ITSELF LIVES IN THE WORKER
// A handle is STATE INSIDE THE WASM INSTANCE -- the verified, decoded,
// indexed blocks that `storeOpen` retained. A WebAssembly instance does
// not cross a thread boundary, so a handle opened on the main thread
// cannot be queried from a worker, and the reverse. Only two designs are
// available:
//
//   (a) the handle lives in the worker, and `query()` and `close()` are
//       messages to it;
//   (b) each query spawns a worker, which re-reads and re-decodes every
//       artifact.
//
// (b) destroys the reason a handle exists: `storeOpen` is the expensive
// call (5.4 s against the collection above, where a query is 0.6 s), and
// paying it per query is worse than the stateless `queryStore` path. So
// (a) is what this file implements.
//
// THE COST OF (a), STATED
//   - One worker thread per SESSION, not per handle. A session holds one
//     engine and as many handles as the engine's own handle cap allows,
//     so a caller that opens several stores pays for one thread and one
//     copy of the module. `openStoreHandleOnWorker` uses a shared session
//     by default; `{ownWorker: true}` gives a handle its own thread, and
//     its own copy of the 5.6 MB module, when a caller wants failure
//     isolation between stores.
//   - Every call is ASYNCHRONOUS, where the in-process handle is
//     synchronous. A message round trip is the price of the bigger stack.
//   - An extension function registered on the MAIN thread's engine
//     (`bin/ext.mjs`) is not visible to the worker's engine. Register it
//     inside the worker, or use the in-process handle.
//   - The worker keeps the process alive until `close()` or
//     `terminate()`. `unref()` is not used: a server that dropped its
//     last reference would otherwise lose its store silently.
//
// WHAT A ONE-SHOT QUERY DOES INSTEAD
// A single `factoidal query` builds no handle and drops whatever it
// loads, so a worker is measured overhead it cannot amortise. It runs
// IN PROCESS, and only when the runtime runs out of frames does it retry
// once on a worker (`queryStoreOnWorker`). The normal case pays nothing.

import {
  WORKER_STACK_MB, isStackOverflow, reviveError, workerRefused, workerStackMb
} from './pack-host.mjs'
import { StoreOperationError } from './store.mjs'

const isDeno = typeof globalThis.Deno !== 'undefined'

export { WORKER_STACK_MB, isStackOverflow, workerRefused, workerStackMb }

/** Whether this runtime has the `worker_threads` route at all. Deno's
 *  `Worker` takes no stack size, so Deno takes the re-exec route in
 *  `bin/pack-host.mjs` instead. */
export function workerRouteAvailable () {
  return !isDeno
}

// ------------------------------------------------------------- a session
//
// One worker thread, one engine, many handles.

let nextRequestId = 1

/**
 * A worker thread holding one engine and the handles opened through it.
 *
 * Hold one of these for as long as a process answers questions about a
 * store. `terminate()` drops the thread and everything in it.
 */
export class StoreWorkerSession {
  constructor (worker) {
    this.worker = worker
    this.pending = new Map()
    this.dead = null
    this.handles = new Set()
    worker.on('message', (message) => {
      const waiting = this.pending.get(message.id)
      if (waiting === undefined) return
      this.pending.delete(message.id)
      if (message.kind === 'error') waiting.reject(reviveError(message.error))
      else waiting.resolve(message.answer)
    })
    worker.on('error', (error) => { this.fail(error) })
    worker.on('exit', (code) => {
      this.fail(new StoreOperationError(
        `the store worker exited with code ${code}`))
    })
  }

  /** Fail every outstanding request and refuse every later one. */
  fail (error) {
    if (this.dead === null) this.dead = error
    for (const waiting of this.pending.values()) waiting.reject(error)
    this.pending.clear()
  }

  /** Send one request and await its answer. */
  send (request) {
    if (this.dead !== null) return Promise.reject(this.dead)
    const id = nextRequestId
    nextRequestId += 1
    return new Promise((resolve, reject) => {
      this.pending.set(id, { resolve, reject })
      this.worker.postMessage({ ...request, id })
    })
  }

  /**
   * Open one store handle inside this session's worker.
   *
   * @param {string} root the collection root that holds CURRENT
   * @param {{generation?: string, keys?: string[], sparql?: string}} options
   *   the same options `openStoreHandle` takes, plus `generation` to open
   *   a generation that has not been activated
   * @returns {Promise<WorkerStoreHandle>}
   */
  async open (root, options = {}) {
    const envelope = await this.send({
      kind: 'open',
      root,
      generation: typeof options.generation === 'string' ? options.generation : null,
      keys: Array.isArray(options.keys) ? options.keys : null,
      sparql: typeof options.sparql === 'string' ? options.sparql : null
    })
    const handle = new WorkerStoreHandle(this, envelope)
    this.handles.add(handle)
    return handle
  }

  /** `storeHandleList` from inside the worker: what this session holds. */
  async list () {
    return (await this.send({ kind: 'list' })).list
  }

  /** Stop the thread. Every handle it held is gone with it. */
  async terminate () {
    if (this.dead === null) this.dead = new StoreOperationError(
      'this store worker session is terminated')
    for (const handle of this.handles) handle.closed = true
    this.handles.clear()
    await this.worker.terminate()
  }
}

/**
 * A store handle held inside a worker thread.
 *
 * The same envelope fields as the in-process `StoreHandle`, and the same
 * two methods, except that both are asynchronous. The wasm module is
 * single-threaded, so two `query()` calls on one session are served in
 * the order they were sent.
 */
export class WorkerStoreHandle {
  constructor (session, envelope) {
    this.session = session
    this.handle = envelope.handle
    this.identity = envelope.identity
    this.layout = envelope.layout
    this.wireVersion = envelope.wireVersion
    this.artifacts = envelope.artifacts
    this.bytes = envelope.bytes
    this.rows = envelope.rows
    this.closed = false
    // Set when this handle owns its session, so `close()` stops the thread.
    this.ownSession = false
  }

  /** One SPARQL query against the retained blocks. The envelope is the
   *  one the in-process handle answers with. */
  async query (sparql) {
    if (this.closed) {
      throw new StoreOperationError(`store handle ${this.handle} is closed`)
    }
    return (await this.session.send({
      kind: 'query', handle: this.handle, sparql
    })).result
  }

  /** Drop the handle and everything it retained. Idempotent. */
  async close () {
    if (this.closed) return
    this.closed = true
    this.session.handles.delete(this)
    if (this.ownSession) {
      await this.session.terminate()
      return
    }
    if (this.session.dead !== null) return
    await this.session.send({ kind: 'close', handle: this.handle })
  }
}

// ------------------------------------------------------- starting one

/** Start a worker thread with a stack big enough for the store paths. */
async function startWorker () {
  if (!workerRouteAvailable()) {
    throw new StoreOperationError(
      'this runtime has no worker_threads route for the store operations; ' +
      'raise the call stack itself instead')
  }
  const { Worker } = await import('node:worker_threads')
  const entry = new URL('./store-worker.mjs', import.meta.url)
  const worker = new Worker(entry, {
    resourceLimits: { stackSizeMb: workerStackMb() }
  })
  const session = new StoreWorkerSession(worker)
  // Load the engine now, so the first query measures the query.
  await session.send({ kind: 'warm' })
  return session
}

/** Start a session of this session's own. */
export async function openStoreWorkerSession () {
  return await startWorker()
}

let sharedSession = null

/** The session `openStoreHandleOnWorker` uses when the caller names none:
 *  one thread, one engine, shared by every handle in the process. */
export async function sharedStoreWorkerSession () {
  if (sharedSession === null) sharedSession = startWorker()
  try {
    return await sharedSession
  } catch (error) {
    sharedSession = null
    throw error
  }
}

/** Stop the shared session, if one was started. */
export async function closeSharedStoreWorkerSession () {
  if (sharedSession === null) return
  const session = sharedSession
  sharedSession = null
  await (await session).terminate()
}

/**
 * Open one store handle on a worker thread with a raised call stack.
 *
 * This is the handle a long-lived process wants against a large store: an
 * MCP server, a chat tool loop, a SPARQL endpoint. It is asynchronous
 * where `openStoreHandle` is synchronous, and it needs no runtime flag.
 *
 * @param {string} root the collection root that holds CURRENT
 * @param {{generation?: string, keys?: string[], sparql?: string,
 *          session?: StoreWorkerSession, ownWorker?: boolean}} options
 * @returns {Promise<WorkerStoreHandle>}
 */
export async function openStoreHandleOnWorker (root, options = {}) {
  if (options.session instanceof StoreWorkerSession) {
    return await options.session.open(root, options)
  }
  if (options.ownWorker === true) {
    const session = await startWorker()
    const handle = await session.open(root, options)
    handle.ownSession = true
    return handle
  }
  const session = await sharedStoreWorkerSession()
  return await session.open(root, options)
}

// ------------------------------------------------- the one-shot retry

/**
 * Run one stateless query on a worker thread, then stop the thread.
 *
 * What `factoidal query` retries with after the in-process attempt ran
 * out of frames. It answers exactly what `queryStore` answers.
 *
 * @returns {Promise<{plan: object, result: object, blobBytes: number}>}
 */
export async function queryStoreOnWorker (root, generation, sparql) {
  const session = await startWorker()
  try {
    return await session.send({
      kind: 'query-once', root, generation: generation ?? null, sparql
    })
  } finally {
    await session.terminate()
  }
}
