// The thread `factoidal pack` runs on under Node, so that the pack has a
// call stack big enough to finish.
// https://github.com/danbri/factoidal/issues/649
//
// WHAT THIS FILE IS ALLOWED TO DO
// Load the engine, run the same pack the in-process path runs, post the
// progress reports back, and post the failure back. It reads no RDF,
// names no artifact and encodes nothing: `pack.mjs` drives the engine
// and `store-host` writes the bytes, here exactly as they do on the
// main thread (iron rule 7 of CLAUDE.md).
//
// The engine loads HERE, not on the main thread: a loaded WebAssembly
// instance does not cross a thread boundary. The artifacts are written
// HERE too, where they arrive, so no artifact byte crosses it either.

import { parentPort, workerData } from 'node:worker_threads'
import { describeError, packHere } from './pack-host.mjs'

const port = parentPort
const task = workerData

packHere(task, task.progress
  ? (progress) => port.postMessage({ kind: 'progress', progress })
  : undefined)
  .then((answer) => {
    if (answer.notWired === true) port.postMessage({ kind: 'notWired' })
    else port.postMessage({ kind: 'report', report: answer.report })
  })
  .catch((error) => {
    port.postMessage({ kind: 'error', error: describeError(error) })
  })
