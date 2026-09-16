// Error type shared by the Node and Deno host-I/O implementations.
//
// The store host moves bytes. It never reports a FORMAT decision, so no
// error code here names a manifest, a digest, a block or a generation
// layout: those decisions belong to the Lean source
// (https://github.com/danbri/factoidal/issues/641, iron rule 7).

export class StoreHostError extends Error {
  /**
   * @param {string} code   stable machine-readable code
   * @param {string} message
   * @param {{cause?: unknown, path?: string}} [detail]
   */
  constructor (code, message, detail = {}) {
    super(message, detail.cause === undefined ? undefined : { cause: detail.cause })
    this.name = 'StoreHostError'
    this.code = code
    if (detail.path !== undefined) this.path = detail.path
  }
}

/** Reject an argument that is not a usable filesystem path. */
export function requirePath (value, label) {
  if (typeof value !== 'string' || value.length === 0) {
    throw new StoreHostError('BAD_ARGUMENT', `${label} must be a non-empty string`)
  }
  if (value.indexOf('\u0000') >= 0) {
    throw new StoreHostError('BAD_ARGUMENT', `${label} must not contain a NUL byte`)
  }
  return value
}

/**
 * Reject an offset or length that a 64-bit host accepts and JavaScript
 * cannot represent exactly. The C extern refuses `offset > INT64_MAX`;
 * a JavaScript number stops being exact at 2^53 - 1, so that is the
 * limit this module enforces.
 */
export function requireCount (value, label) {
  if (typeof value !== 'number' || !Number.isSafeInteger(value) || value < 0) {
    throw new StoreHostError(
      'BAD_ARGUMENT',
      `${label} must be a non-negative integer below 2^53`
    )
  }
  return value
}

/** Reject a payload that is not raw bytes. */
export function requireBytes (value, label) {
  if (!(value instanceof Uint8Array)) {
    throw new StoreHostError('BAD_ARGUMENT', `${label} must be a Uint8Array`)
  }
  return value
}
