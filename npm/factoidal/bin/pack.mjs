// Building a Shardborough generation from a JavaScript host, with the
// Lean engine running as WebAssembly.
// https://github.com/danbri/factoidal/issues/641 stage 3.
// Design record: docs/designissues/2026-09-03-npm-pack-in-wasm.md.
//
// WHAT THIS FILE IS ALLOWED TO DO
// Read the input file in chunks, hand each chunk to the engine, take back
// whatever artifacts the engine says are ready, and write each one under
// the name the engine gave it. It decides no artifact name, computes no
// digest, encodes no block and writes no manifest field. Every one of
// those is a format decision and it lives in the Lean source (iron rule
// 7 of CLAUDE.md). A reviewer who finds a magic number, a field offset,
// a file-name pattern or a hash in this file has found a violation.
//
// There is no file I/O inside the wasm module -- libuv is left out of the
// Emscripten build by design -- so the engine cannot write the generation
// itself. That is the whole reason this file exists.
//
// WHY IT STREAMS
// wasm32 addresses 4 GiB. The native packer's own second pass is already
// bounded: it publishes a batch of blocks every 64 input chunks and then
// drops the triples. This host drives that same fold one chunk at a time
// and writes each artifact as it appears, so neither side ever holds the
// whole input or the whole generation.

import { StoreHostError, readChunk, writeNew } from '../store-host/index.mjs'
import { joinPath } from '../store-host/paths.mjs'

/** The chunk the host feeds per call. The native packer reads 65,536
 *  bytes at a time; matching it keeps the two folds in step, which is
 *  what makes the byte-identity gate meaningful. */
export const FEED_BYTES = 65536

/** An error the pack operations reported, with the engine's own words. */
export class PackError extends Error {
  constructor (message, detail = {}) {
    super(message)
    this.name = 'PackError'
    this.handle = detail.handle === undefined ? null : detail.handle
    this.notWired = detail.notWired === true
  }
}

/**
 * Whether the loaded engine carries the pack operations.
 *
 * The engine reports its own operation lists in the `abiVersion`
 * envelope, so the command asks it rather than guessing from a package
 * version. An engine built before stage 3 answers a package that has the
 * subcommand, and this is how that pairing is detected.
 */
export function packSupported (engine) {
  let envelope
  try {
    envelope = engine.call('abiVersion', [])
  } catch (_error) {
    return false
  }
  const named = (list) => Array.isArray(list) && list.indexOf('packBegin') >= 0
  return named(envelope.ops) || named(envelope.blobOps) || named(envelope.blobIoOps)
}

/**
 * Take every artifact the engine has ready and write it into `output`.
 *
 * `packNext` answers one artifact per call and reports when the queue is
 * empty. The bytes come back in the module's out region, raw; nothing on
 * this path encodes them.
 *
 * @returns {{names: string[], bytes: number}} what was written
 */
function drain (engine, handle, output) {
  const names = []
  let total = 0
  for (;;) {
    const answer = engine.callBlobIO('packNext', [handle], new Uint8Array(0))
    const envelope = answer.envelope
    if (envelope.done === true) break
    if (typeof envelope.name !== 'string') {
      throw new PackError('packNext answered no artifact name', { handle })
    }
    writeNew(joinPath(output, envelope.name), answer.bytes)
    names.push(envelope.name)
    total += answer.bytes.length
  }
  return { names, bytes: total }
}

/**
 * Build one immutable generation from one RDF file.
 *
 * @param {object} engine the loaded engine
 * @param {string} input the RDF file to read
 * @param {string} output the generation directory to fill; it must exist
 * @param {object} options
 * @param {string} options.layout `ibk3` or `ibk4`
 * @param {string} options.syntax `turtle`, `trig` or `nquads`
 * @param {(progress: object) => void} [options.onProgress]
 * @returns {object} the engine's own finish envelope, plus what was written
 */
export function packFile (engine, input, output, options) {
  const begun = engine.call('packBegin', [options.syntax, options.layout])
  const handle = begun.handle
  if (typeof handle !== 'string') {
    throw new PackError('packBegin answered no handle')
  }
  const written = []
  let bytesWritten = 0
  let bytesRead = 0
  try {
    // The prepass the native packer runs first -- the source digest and
    // the generated-blank-node prefix -- is the engine's business, so the
    // host simply feeds the file twice and lets the engine say when it
    // has moved from one pass to the next.
    for (let pass = 0; pass < 2; pass += 1) {
      const passName = pass === 0 ? 'prepass' : 'ingest'
      let offset = 0
      for (;;) {
        const chunk = readChunk(input, offset, FEED_BYTES)
        if (chunk.length === 0) break
        offset += chunk.length
        bytesRead += chunk.length
        engine.callBlobIO('packFeed', [handle, passName], chunk)
        const drained = drain(engine, handle, output)
        written.push(...drained.names)
        bytesWritten += drained.bytes
        if (typeof options.onProgress === 'function') {
          options.onProgress({ pass: passName, bytesRead, artifacts: written.length })
        }
      }
      engine.call('packEndPass', [handle, passName])
      const drained = drain(engine, handle, output)
      written.push(...drained.names)
      bytesWritten += drained.bytes
    }
    const finished = engine.call('packFinish', [handle])
    const last = drain(engine, handle, output)
    written.push(...last.names)
    bytesWritten += last.bytes
    return { ...finished, written, bytesWritten, bytesRead }
  } finally {
    try { engine.call('packClose', [handle]) } catch (_error) { /* already gone */ }
  }
}

/**
 * Verify one generation and report the engine's verdict.
 *
 * The host reads the manifest and every artifact the engine asks for; the
 * engine checks each one against the digest the manifest commits and
 * every cross-artifact relation. Replacing CURRENT is the host's step,
 * and it happens only on a verdict of ok.
 */
export function verifyGeneration (engine, manifestHex, artifacts) {
  const windows = []
  let offset = 0
  for (const artifact of artifacts) {
    windows.push({ key: artifact.key, offset, len: artifact.bytes.length })
    offset += artifact.bytes.length
  }
  const blob = new Uint8Array(offset)
  let cursor = 0
  for (const artifact of artifacts) {
    blob.set(artifact.bytes, cursor)
    cursor += artifact.bytes.length
  }
  return engine.callBlob('activateVerify',
    [manifestHex, JSON.stringify(windows)], blob)
}

export { StoreHostError }
