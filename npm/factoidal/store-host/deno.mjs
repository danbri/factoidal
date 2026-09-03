// Deno implementation of the same four host primitives. Uses only Deno
// globals, so it never loads Deno's Node compatibility layer.
//
// Deno 2 removed the resource-id fsync entry points (`Deno.fsyncSync`);
// the file-handle method `FsFile.syncSync()` is the one that exists.

import { StoreHostError } from './errors.mjs'
import { baseName, dirName, joinPath } from './paths.mjs'

export const runtime = 'deno'

function wrap (code, message, path, cause) {
  return new StoreHostError(code, `${message}: ${String(cause && cause.message ? cause.message : cause)}`, { path, cause })
}

function openRead (path) {
  try {
    return Deno.openSync(path, { read: true })
  } catch (cause) {
    throw wrap('OPEN_FAILED', `cannot open ${path} for reading`, path, cause)
  }
}

/**
 * Deno has no positional read. Each call here opens its own handle, so the
 * seek belongs to that handle alone and no other reader can move it. That
 * is what `pread` buys the C extern; it is not the same instruction.
 */
function readInto (file, out, length, offset, path) {
  if (offset > 0) file.seekSync(offset, Deno.SeekMode.Start)
  let done = 0
  while (done < length) {
    let read
    try {
      read = file.readSync(out.subarray(done, length))
    } catch (cause) {
      throw wrap('READ_FAILED', `read failed on ${path}`, path, cause)
    }
    if (read === null || read === 0) break
    done += read
  }
  return done
}

export function readWhole (path) {
  const file = openRead(path)
  try {
    const size = file.statSync().size
    if (!Number.isSafeInteger(size)) {
      throw new StoreHostError('FILE_TOO_LARGE', `${path} is larger than 2^53 - 1 bytes`, { path })
    }
    const out = new Uint8Array(size)
    const done = readInto(file, out, size, 0, path)
    if (done !== size) {
      throw new StoreHostError('SHORT_READ', `${path} shrank during the read (${done} of ${size} bytes)`, { path })
    }
    return out
  } finally {
    file.close()
  }
}

export function readRange (path, offset, length) {
  if (length === 0) return new Uint8Array(0)
  const file = openRead(path)
  try {
    const out = new Uint8Array(length)
    const done = readInto(file, out, length, offset, path)
    if (done !== length) {
      throw new StoreHostError(
        'SHORT_READ',
        `${path} returned ${done} of ${length} bytes at offset ${offset}`,
        { path }
      )
    }
    return out
  } finally {
    file.close()
  }
}

export function appendSyncAtSize (path, bytes, expectedSize) {
  let file
  try {
    file = Deno.openSync(path, { write: true, create: true, append: true })
  } catch (cause) {
    throw wrap('OPEN_FAILED', `cannot open ${path} for append`, path, cause)
  }
  try {
    const size = file.statSync().size
    if (size !== expectedSize) return false
    let done = 0
    while (done < bytes.length) {
      let written
      try {
        written = file.writeSync(bytes.subarray(done))
      } catch (cause) {
        throw wrap('WRITE_FAILED', `append failed on ${path}`, path, cause)
      }
      done += written
    }
    try {
      file.syncSync()
    } catch (cause) {
      throw wrap('FSYNC_FAILED', `fsync failed on ${path}`, path, cause)
    }
    return true
  } finally {
    file.close()
  }
}

function temporaryName (path) {
  const suffix = Math.floor(Math.random() * 0xffffff).toString(16).padStart(6, '0')
  return joinPath(dirName(path), baseName(path) + '.tmp.' + suffix)
}

function fsyncDirectory (directory) {
  let handle
  try {
    handle = Deno.openSync(directory, { read: true })
  } catch (cause) {
    throw wrap('DIR_OPEN_FAILED', `cannot open ${directory} to sync it`, directory, cause)
  }
  try {
    handle.syncSync()
  } finally {
    handle.close()
  }
}

export function atomicReplace (path, bytes) {
  const directory = dirName(path)
  let temporary = null
  let file = null
  try {
    for (let attempt = 0; attempt < 8 && file === null; attempt += 1) {
      temporary = temporaryName(path)
      try {
        file = Deno.openSync(temporary, { write: true, createNew: true })
      } catch (cause) {
        if (cause instanceof Deno.errors.AlreadyExists) continue
        throw wrap('OPEN_FAILED', `cannot create ${temporary}`, temporary, cause)
      }
    }
    if (file === null) {
      throw new StoreHostError('TEMP_NAME_EXHAUSTED', `no free temporary name beside ${path}`, { path })
    }
    let done = 0
    while (done < bytes.length) {
      let written
      try {
        written = file.writeSync(bytes.subarray(done))
      } catch (cause) {
        throw wrap('WRITE_FAILED', `write failed on ${temporary}`, temporary, cause)
      }
      done += written
    }
    file.syncSync()
    file.close()
    file = null
    Deno.renameSync(temporary, path)
    temporary = null
    try {
      fsyncDirectory(directory)
    } catch (_error) {
      return false
    }
    return true
  } catch (error) {
    if (file !== null) file.close()
    if (temporary !== null) {
      try { Deno.removeSync(temporary) } catch (_ignored) { /* the temporary may not exist */ }
    }
    throw error
  }
}

export function listGeneration (directory) {
  const out = []
  let entries
  try {
    entries = [...Deno.readDirSync(directory)]
  } catch (cause) {
    throw wrap('DIR_READ_FAILED', `cannot list ${directory}`, directory, cause)
  }
  entries.sort((left, right) => (left.name < right.name ? -1 : left.name > right.name ? 1 : 0))
  for (const entry of entries) {
    if (!entry.isFile) continue
    let info
    try {
      info = Deno.statSync(joinPath(directory, entry.name))
    } catch (_cause) {
      continue
    }
    out.push({ name: entry.name, size: info.size })
  }
  return out
}
