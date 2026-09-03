// The store host: the byte-moving half of the persisted Shardborough store
// when the engine runs as WebAssembly instead of a native binary.
// https://github.com/danbri/factoidal/issues/641
//
// WHAT THIS FILE IS ALLOWED TO DO
// Open a file by name, move its bytes, sync, rename, list a directory.
// Nothing else. It never parses a manifest, checks a digest, decodes a
// block, or decides which artifact answers a query. Those are format
// decisions and they live in the Lean source (iron rule 7). A reviewer
// who finds a magic number, a field offset or a hash in this directory
// has found a rule violation.
//
// WHAT IT CORRESPONDS TO
// `formal/lean4/Harness/PosixRangeIO.lean` declares three `@[extern]`
// primitives, realised in `formal/lean4/ffi/block_pread.c`:
//
//   l4_block_pread                    -> readRange
//   l4_delta_log_append_sync_at_size  -> appendSyncAtSize
//   l4_atomic_replace_file_sync       -> atomicReplace
//
// `readWhole`, `openCollection` and `listGeneration` have no extern of
// their own; the native tools use Lean's own `IO.FS` for them.
//
// WHERE THE HOST DIFFERS FROM THE C EXTERNS
//
// 1. No advisory lock on the append. `l4_delta_log_append_sync_at_size`
//    holds `flock(fd, LOCK_EX)` across the size check, the write loop and
//    the fsync, so exactly one of two concurrent writers appends and the
//    loser gets `false` and retries. Neither Node nor Deno has `flock` in
//    its standard library, and this module takes no dependency, so the
//    sequence here is fstat, then append, then fsync, with no lock. Two
//    writers that observe the same size therefore both append, and the
//    delta log gets two batches where the protocol expects one. Use this
//    function only where a single writer is guaranteed. This is the one
//    divergence that can corrupt a store; see issue 641 stage 4.
//
// 2. Failures raise instead of returning false. Every C extern collapses
//    an open, write or fsync failure into an empty result or `false`. A
//    `false` there is therefore ambiguous: it can mean the size did not
//    match, or that the disk is full. Here `false` from
//    `appendSyncAtSize` means only that the file size was not the
//    expected one; an I/O failure throws a `StoreHostError`. A caller
//    that wants the extern's exact shape catches and maps to false.
//
// 3. `readRange` raises on a short read. The extern returns an empty
//    array on any failure and `Harness.PosixRangeIO.readRange?` turns a
//    wrong size into `none`. Here a short read throws with code
//    SHORT_READ, which carries the same refusal and says why.
//
// 4. `atomicReplace` returning false does not mean nothing changed. The C
//    version returns false when the parent-directory fsync fails, after
//    the rename has already succeeded. This module reports it the same
//    way: false means the new bytes may be in place but their directory
//    entry is not known to be durable.
//
// 5. Deno has no positional read. `readRange` opens its own handle, seeks
//    and reads. The handle is private to the call, so there is no cursor
//    to race, but it is a seek plus a read and not one `pread`.
//
// 6. Offsets and lengths are JavaScript numbers. The externs take
//    `UInt64`. Anything at or above 2^53 is rejected with BAD_ARGUMENT
//    rather than silently rounded.
//
// 7. Directory fsync is not portable. `atomicReplace` opens the parent
//    directory and fsyncs it, which works on Linux and macOS under both
//    runtimes. Windows refuses to open a directory as a file; the call
//    returns false there and the rename still happened (point 4).

import { StoreHostError, requireBytes, requireCount, requirePath } from './errors.mjs'
import { joinPath, requireChildName } from './paths.mjs'

const isDeno = typeof globalThis.Deno !== 'undefined' &&
  typeof globalThis.Deno.openSync === 'function'

const impl = isDeno ? await import('./deno.mjs') : await import('./node.mjs')

/** 'node' or 'deno' — which implementation load-time selection chose. */
export const runtime = impl.runtime

export { StoreHostError }

/**
 * Read a whole file.
 * @param {string} path
 * @returns {Uint8Array} a fresh array of exactly the file's bytes
 */
export function readWhole (path) {
  requirePath(path, 'path')
  return impl.readWhole(path)
}

/**
 * Read exactly `length` bytes starting at `offset`, without touching any
 * shared file cursor. The counterpart of `l4_block_pread`.
 * @param {string} path
 * @param {number} offset
 * @param {number} length
 * @returns {Uint8Array} exactly `length` bytes
 * @throws {StoreHostError} code SHORT_READ when the file has fewer bytes
 */
export function readRange (path, offset, length) {
  requirePath(path, 'path')
  requireCount(offset, 'offset')
  requireCount(length, 'length')
  return impl.readRange(path, offset, length)
}

/**
 * Append `bytes` only if the file currently has exactly `expectedSize`
 * bytes, then fsync it. The counterpart of
 * `l4_delta_log_append_sync_at_size`, minus its advisory lock
 * (divergence 1 above). Creates the file when absent, in which case the
 * only size that matches is 0.
 * @param {string} path
 * @param {Uint8Array} bytes
 * @param {number} expectedSize
 * @returns {boolean} true when the append happened and was synced;
 *   false when the file's size was not `expectedSize`
 */
export function appendSyncAtSize (path, bytes, expectedSize) {
  requirePath(path, 'path')
  requireBytes(bytes, 'bytes')
  requireCount(expectedSize, 'expectedSize')
  return impl.appendSyncAtSize(path, bytes, expectedSize)
}

/**
 * Replace a file's whole contents so that a reader sees either the old
 * bytes or the new bytes and never a mixture: write a temporary file in
 * the same directory, fsync it, rename it over the target, fsync the
 * directory. The counterpart of `l4_atomic_replace_file_sync`.
 * @param {string} path
 * @param {Uint8Array} bytes
 * @returns {boolean} true when the replacement is durable; false when the
 *   rename succeeded but the directory fsync did not (divergence 4)
 */
export function atomicReplace (path, bytes) {
  requirePath(path, 'path')
  requireBytes(bytes, 'bytes')
  return impl.atomicReplace(path, bytes)
}

/**
 * List the regular files of one directory with their sizes, sorted by
 * name. Subdirectories and symbolic links to directories are left out.
 * @param {string} directory
 * @returns {{name: string, size: number}[]}
 */
export function listGeneration (directory) {
  requirePath(directory, 'directory')
  return impl.listGeneration(directory)
}

// The manifest file names a generation directory can carry, in the order
// `Harness.ShardMerklePread.readManifest` tries them. This module reads
// whichever exists and returns its bytes untouched; it does not look
// inside either one.
const MANIFEST_NAMES = ['manifest.sbm2', 'manifest.sbm1']

/**
 * Open an activated collection: read `CURRENT`, and return the generation
 * name it holds together with the raw manifest bytes of that generation.
 *
 * The returned `manifest` is bytes. Deciding what those bytes mean —
 * which wire version, which artifacts, which digests — is the engine's
 * job, not this module's.
 *
 * @param {string} root the collection root that holds CURRENT
 * @returns {{root: string, generation: string, generationDir: string,
 *            manifestName: string, manifest: Uint8Array}}
 * @throws {StoreHostError} code NO_CURRENT when the root has no CURRENT,
 *   NO_MANIFEST when the generation carries none of the manifest names
 */
export function openCollection (root) {
  requirePath(root, 'root')
  const pointerPath = joinPath(root, 'CURRENT')
  let pointerBytes
  try {
    pointerBytes = impl.readWhole(pointerPath)
  } catch (cause) {
    throw new StoreHostError(
      'NO_CURRENT',
      `${root} has no readable CURRENT pointer`,
      { path: pointerPath, cause }
    )
  }
  // CURRENT holds a UTF-8 child-generation name (spec section 6.4). Trailing
  // ASCII whitespace is tolerated so a pointer written by hand still opens.
  const generation = requireChildName(
    new TextDecoder('utf-8', { fatal: true }).decode(pointerBytes).replace(/[\r\n\t ]+$/, ''),
    'CURRENT'
  )
  const generationDir = joinPath(root, generation)
  for (const manifestName of MANIFEST_NAMES) {
    try {
      const manifest = impl.readWhole(joinPath(generationDir, manifestName))
      return { root, generation, generationDir, manifestName, manifest }
    } catch (error) {
      if (error instanceof StoreHostError && error.code === 'OPEN_FAILED') continue
      throw error
    }
  }
  throw new StoreHostError(
    'NO_MANIFEST',
    `${generationDir} has none of ${MANIFEST_NAMES.join(', ')}`,
    { path: generationDir }
  )
}
