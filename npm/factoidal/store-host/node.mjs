// Node implementation of the four host primitives the Lean persisted store
// needs (Harness/PosixRangeIO.lean). See ./index.mjs for the contract and
// for the places where Node's semantics differ from the C externs.
//
// Nothing here parses, verifies or interprets a byte. It opens files,
// moves bytes, and syncs.

import {
  closeSync, fstatSync, fsyncSync, openSync, readSync, readdirSync,
  renameSync, statSync, unlinkSync, writeSync
} from 'node:fs'

import { StoreHostError } from './errors.mjs'
import { baseName, dirName, joinPath } from './paths.mjs'

export const runtime = 'node'

function wrap (code, message, path, cause) {
  return new StoreHostError(code, `${message}: ${String(cause && cause.message ? cause.message : cause)}`, { path, cause })
}

function isInterrupt (error) {
  return error && (error.code === 'EINTR' || error.code === 'EAGAIN')
}

function openRead (path) {
  try {
    return openSync(path, 'r')
  } catch (cause) {
    throw wrap('OPEN_FAILED', `cannot open ${path} for reading`, path, cause)
  }
}

/** Read `length` bytes at `offset` into `out` at `outOffset`. Returns how many. */
function preadInto (fd, out, outOffset, length, offset, path) {
  let done = 0
  while (done < length) {
    let read
    try {
      read = readSync(fd, out, outOffset + done, length - done, offset + done)
    } catch (cause) {
      if (isInterrupt(cause)) continue
      throw wrap('READ_FAILED', `read failed on ${path}`, path, cause)
    }
    if (read === 0) break
    done += read
  }
  return done
}

export function readWhole (path) {
  const fd = openRead(path)
  try {
    const size = fstatSync(fd).size
    if (!Number.isSafeInteger(size)) {
      throw new StoreHostError('FILE_TOO_LARGE', `${path} is larger than 2^53 - 1 bytes`, { path })
    }
    const out = new Uint8Array(size)
    const done = preadInto(fd, out, 0, size, 0, path)
    if (done !== size) {
      throw new StoreHostError('SHORT_READ', `${path} shrank during the read (${done} of ${size} bytes)`, { path })
    }
    return out
  } finally {
    closeSync(fd)
  }
}

export function readRange (path, offset, length) {
  if (length === 0) return new Uint8Array(0)
  const fd = openRead(path)
  try {
    const out = new Uint8Array(length)
    const done = preadInto(fd, out, 0, length, offset, path)
    if (done !== length) {
      throw new StoreHostError(
        'SHORT_READ',
        `${path} returned ${done} of ${length} bytes at offset ${offset}`,
        { path }
      )
    }
    return out
  } finally {
    closeSync(fd)
  }
}

export function appendSyncAtSize (path, bytes, expectedSize) {
  let fd
  try {
    // 'a' is O_WRONLY | O_CREAT | O_APPEND, matching the C extern's open.
    fd = openSync(path, 'a')
  } catch (cause) {
    throw wrap('OPEN_FAILED', `cannot open ${path} for append`, path, cause)
  }
  try {
    const size = fstatSync(fd).size
    if (size !== expectedSize) return false
    let done = 0
    while (done < bytes.length) {
      let written
      try {
        // position null keeps the O_APPEND placement the C extern relies on.
        written = writeSync(fd, bytes, done, bytes.length - done, null)
      } catch (cause) {
        if (isInterrupt(cause)) continue
        throw wrap('WRITE_FAILED', `append failed on ${path}`, path, cause)
      }
      done += written
    }
    try {
      fsyncSync(fd)
    } catch (cause) {
      throw wrap('FSYNC_FAILED', `fsync failed on ${path}`, path, cause)
    }
    return true
  } finally {
    closeSync(fd)
  }
}

function temporaryName (path) {
  const suffix = Math.floor(Math.random() * 0xffffff).toString(16).padStart(6, '0')
  return joinPath(dirName(path), baseName(path) + '.tmp.' + suffix)
}

function fsyncDirectory (directory) {
  let fd
  try {
    fd = openSync(directory, 'r')
  } catch (cause) {
    throw wrap('DIR_OPEN_FAILED', `cannot open ${directory} to sync it`, directory, cause)
  }
  try {
    fsyncSync(fd)
  } finally {
    closeSync(fd)
  }
}

export function atomicReplace (path, bytes) {
  const directory = dirName(path)
  let temporary = null
  let fd = null
  try {
    for (let attempt = 0; attempt < 8 && fd === null; attempt += 1) {
      temporary = temporaryName(path)
      try {
        // 'wx' is O_WRONLY | O_CREAT | O_EXCL, the exclusive create that
        // makes the name ours the way mkstemp does in the C extern.
        fd = openSync(temporary, 'wx')
      } catch (cause) {
        if (cause && cause.code === 'EEXIST') continue
        throw wrap('OPEN_FAILED', `cannot create ${temporary}`, temporary, cause)
      }
    }
    if (fd === null) {
      throw new StoreHostError('TEMP_NAME_EXHAUSTED', `no free temporary name beside ${path}`, { path })
    }
    let done = 0
    while (done < bytes.length) {
      let written
      try {
        written = writeSync(fd, bytes, done, bytes.length - done, null)
      } catch (cause) {
        if (isInterrupt(cause)) continue
        throw wrap('WRITE_FAILED', `write failed on ${temporary}`, temporary, cause)
      }
      done += written
    }
    fsyncSync(fd)
    closeSync(fd)
    fd = null
    renameSync(temporary, path)
    temporary = null
    try {
      fsyncDirectory(directory)
    } catch (_error) {
      // The C extern also returns false here, with the replacement already
      // done. Reported the same way; see ./index.mjs for what false means.
      return false
    }
    return true
  } catch (error) {
    if (fd !== null) closeSync(fd)
    if (temporary !== null) {
      try { unlinkSync(temporary) } catch (_ignored) { /* the temporary may not exist */ }
    }
    throw error
  }
}

export function listGeneration (directory) {
  let names
  try {
    names = readdirSync(directory)
  } catch (cause) {
    throw wrap('DIR_READ_FAILED', `cannot list ${directory}`, directory, cause)
  }
  const out = []
  for (const name of names.sort()) {
    let info
    try {
      info = statSync(joinPath(directory, name))
    } catch (_cause) {
      continue // a name that vanished between readdir and stat
    }
    if (!info.isFile()) continue
    out.push({ name, size: info.size })
  }
  return out
}
