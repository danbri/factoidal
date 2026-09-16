// Path plumbing for the store host. No dependency on `node:path`, so the
// same file loads under Deno without the Node compatibility layer.
//
// These functions join and split path strings. They make no decision about
// what a Shardborough generation contains.

import { StoreHostError } from './errors.mjs'

const SEPARATORS = ['/', '\\']

function isSeparator (character) {
  return SEPARATORS.indexOf(character) >= 0
}

/** Join with '/'. Every runtime this module targets accepts '/'. */
export function joinPath (base, child) {
  if (base.length === 0) return child
  const last = base[base.length - 1]
  return isSeparator(last) ? base + child : base + '/' + child
}

/** The directory part of a path, or '.' when the path has no separator. */
export function dirName (path) {
  let end = path.length
  while (end > 1 && isSeparator(path[end - 1])) end -= 1
  let index = end - 1
  while (index >= 0 && !isSeparator(path[index])) index -= 1
  if (index < 0) return '.'
  if (index === 0) return path[0]
  return path.slice(0, index)
}

/** The final component of a path. */
export function baseName (path) {
  let end = path.length
  while (end > 1 && isSeparator(path[end - 1])) end -= 1
  let index = end - 1
  while (index >= 0 && !isSeparator(path[index])) index -= 1
  return path.slice(index + 1, end)
}

/**
 * A single child name that may be appended to a directory path.
 *
 * `CURRENT` holds a generation name written by the Lean activation path;
 * this module still refuses a value that would leave the collection root
 * when joined. That is a filesystem-safety guard on a string the host is
 * about to turn into a path, not a check of the pointer's format.
 */
export function requireChildName (name, label) {
  if (typeof name !== 'string' || name.length === 0) {
    throw new StoreHostError('BAD_CHILD_NAME', `${label} is empty`)
  }
  if (name === '.' || name === '..') {
    throw new StoreHostError('BAD_CHILD_NAME', `${label} is "${name}"`)
  }
  for (const character of name) {
    if (isSeparator(character) || character === '\u0000') {
      throw new StoreHostError(
        'BAD_CHILD_NAME',
        `${label} contains a path separator or NUL byte`
      )
    }
  }
  return name
}

/** Convert a `file:` URL string to a filesystem path. */
export function fileUrlToPath (url) {
  const text = typeof url === 'string' ? url : String(url)
  if (!text.startsWith('file://')) return text
  let path = decodeURIComponent(text.slice('file://'.length))
  const host = path.indexOf('/')
  if (host > 0) path = path.slice(host)
  if (/^\/[A-Za-z]:/.test(path)) path = path.slice(1)
  return path
}
