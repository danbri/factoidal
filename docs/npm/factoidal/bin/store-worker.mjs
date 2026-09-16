// The thread the store operations run on under Node, so that a query
// against a large generation has a call stack big enough to finish.
// https://github.com/danbri/factoidal/issues/653
//
// WHAT THIS FILE IS ALLOWED TO DO
// Load the engine, open a store, hold store handles, run the same store
// operations the in-process path runs, and post the answers back. It
// reads no manifest field, verifies no digest, decodes no block and
// chooses no artifact: `bin/store.mjs` drives the engine here exactly as
// it does on the main thread (iron rule 7 of CLAUDE.md).
//
// THE ENGINE AND THE HANDLES LIVE HERE, NOT ON THE MAIN THREAD.
// A loaded WebAssembly instance does not cross a thread boundary, and a
// store handle is state inside that instance: the verified, decoded,
// indexed blocks. So a handle opened here can only be queried from here.
// That is why the protocol below carries `query` and `close` as messages
// rather than returning a handle object. One worker holds many handles,
// up to the engine's own handle cap.

import { parentPort } from 'node:worker_threads'
import { loadEngine } from './engine.mjs'
import { describeError } from './pack-host.mjs'
import {
  listStoreHandles, openStore, openStoreHandle, planQuery, queryStore
} from './store.mjs'

const port = parentPort

/** The handles this worker holds, by the id the engine gave them. */
const handles = new Map()

let engine = null
async function theEngine () {
  if (engine === null) engine = await loadEngine()
  return engine
}

/** One request. Every branch answers with a plain object, so nothing
 *  that crosses the boundary is an engine reference. */
async function serve (request) {
  const active = await theEngine()
  if (request.kind === 'open') {
    const store = openStore(request.root, request.generation ?? null)
    const options = {}
    if (Array.isArray(request.keys)) options.keys = request.keys
    else if (typeof request.sparql === 'string') options.sparql = request.sparql
    const handle = openStoreHandle(active, store, options)
    handles.set(handle.handle, handle)
    return {
      handle: handle.handle,
      identity: handle.identity,
      layout: handle.layout,
      wireVersion: handle.wireVersion,
      artifacts: handle.artifacts,
      bytes: handle.bytes,
      rows: handle.rows
    }
  }
  if (request.kind === 'query') {
    const handle = handles.get(request.handle)
    if (handle === undefined) {
      throw new Error(`this worker holds no store handle ${request.handle}`)
    }
    return { result: handle.query(request.sparql) }
  }
  if (request.kind === 'close') {
    const handle = handles.get(request.handle)
    if (handle === undefined) return { closed: false }
    handle.close()
    handles.delete(request.handle)
    return { closed: true }
  }
  if (request.kind === 'list') {
    return { list: listStoreHandles(active) }
  }
  if (request.kind === 'plan') {
    const store = openStore(request.root, request.generation ?? null)
    return { plan: planQuery(active, store, request.sparql) }
  }
  if (request.kind === 'query-once') {
    // The stateless path: read the artifacts the plan names, hand them
    // over, drop them. Used by the one-shot `factoidal query` after an
    // in-process attempt ran out of frames.
    const store = openStore(request.root, request.generation ?? null)
    const answer = queryStore(active, store, request.sparql)
    return {
      plan: answer.plan,
      result: answer.result,
      blobBytes: answer.blobBytes
    }
  }
  if (request.kind === 'warm') return { warm: true }
  throw new Error(`the store worker was sent an unknown request "${request.kind}"`)
}

port.on('message', (request) => {
  serve(request).then(
    (answer) => port.postMessage({ id: request.id, kind: 'ok', answer }),
    (error) => port.postMessage({ id: request.id, kind: 'error', error: describeError(error) }))
})
