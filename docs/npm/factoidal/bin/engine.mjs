// Loading the Lean engine (L4Factoidal compiled to WebAssembly) for the
// `factoidal` command, under Node and under Deno.
// https://github.com/danbri/factoidal/issues/641
//
// This file resolves three files that must stay together and keep their
// names -- l4factoidal.js, l4factoidal.mjs and l4factoidal.wasm -- and
// imports the loader. The Emscripten glue resolves the .wasm sidecar from
// its own basename, so a rename breaks the load on every runtime
// (skills/lean4-wasm-export, "the naming trap").
//
// `npm/factoidal/l4.js` does the same resolution for the CommonJS API. It
// is not reused here because it is CommonJS and this command must load
// under Deno without the require() compatibility path.
//
// WHAT THIS FILE IS ALLOWED TO DO
// Find the engine, load it, and turn bytes into the hexadecimal string
// two of the three store operations take as their small argument. It
// makes no format decision: it never parses a manifest, verifies a
// digest, decodes a block, or chooses an artifact.

import { readWhole } from '../store-host/index.mjs'
import { fileUrlToPath, joinPath } from '../store-host/paths.mjs'

/** Read one environment variable, or null where reading it is refused. */
function environment (name) {
  try {
    if (typeof globalThis.Deno !== 'undefined' && globalThis.Deno.env) {
      const value = globalThis.Deno.env.get(name)
      return typeof value === 'string' && value.length > 0 ? value : null
    }
  } catch (_error) {
    // Deno without --allow-env. An absent override is the normal case.
    return null
  }
  const value = globalThis.process && globalThis.process.env
    ? globalThis.process.env[name]
    : undefined
  return typeof value === 'string' && value.length > 0 ? value : null
}

function readable (path) {
  try {
    readWhole(path)
    return true
  } catch (_error) {
    return false
  }
}

/** The package directory that holds this command. */
export function packageDirectory () {
  return fileUrlToPath(new URL('..', import.meta.url).href).replace(/\/$/, '')
}

/**
 * The loader file of the first engine source that exists, or null.
 *
 * Order, first hit wins:
 *   1. this package's own l4-assets/ (what `npm install` gives);
 *   2. $FACTOIDAL_L4_ASSETS (a custom deployment);
 *   3. the repository checkout layout, docs/web/hub/assets/l4/.
 */
export function resolveEngine () {
  const inPackage = joinPath(packageDirectory(), 'l4-assets/l4factoidal.js')
  if (readable(inPackage)) return inPackage
  const override = environment('FACTOIDAL_L4_ASSETS')
  if (override !== null) {
    const path = joinPath(override, 'l4factoidal.js')
    if (readable(path)) return path
    throw new Error(`FACTOIDAL_L4_ASSETS=${override} holds no l4factoidal.js`)
  }
  const inCheckout = joinPath(packageDirectory(),
    '../../docs/web/hub/assets/l4/l4factoidal.js')
  if (readable(inCheckout)) return inCheckout
  return null
}

let enginePromise = null

/**
 * Load the engine once and return its handle: `call(op, args)` and
 * `callBlob(op, args, bytes)`.
 */
export function loadEngine () {
  if (enginePromise !== null) return enginePromise
  enginePromise = (async () => {
    const loaderPath = resolveEngine()
    if (loaderPath === null) {
      throw new Error(
        'the Lean engine assets are missing. They normally ship in this ' +
        "package's own l4-assets/ directory; if it is absent this install " +
        'is incomplete. Otherwise set FACTOIDAL_L4_ASSETS to a directory ' +
        'holding l4factoidal.js, l4factoidal.mjs and l4factoidal.wasm.')
    }
    const url = loaderPath.startsWith('file://')
      ? loaderPath
      : 'file://' + encodeURI(loaderPath).replace(/#/g, '%23')
    const module = await import(url)
    return module.loadL4()
  })()
  return enginePromise
}

const HEX = (() => {
  const table = new Array(256)
  for (let byte = 0; byte < 256; byte += 1) {
    table[byte] = byte.toString(16).padStart(2, '0')
  }
  return table
})()

/**
 * Lowercase hexadecimal of a byte array. This is a transport encoding for
 * the manifest argument of `storeManifestInspect` and `storeQueryPlan`,
 * not an interpretation of the bytes. Artifact bytes never take this
 * path: they cross raw through `callBlob`.
 * @param {Uint8Array} bytes
 * @returns {string}
 */
export function hexOfBytes (bytes) {
  const parts = new Array(bytes.length)
  for (let index = 0; index < bytes.length; index += 1) parts[index] = HEX[bytes[index]]
  return parts.join('')
}
