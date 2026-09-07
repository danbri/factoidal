// A mock object store, so nothing in the store-over-HTTP tests depends on
// Cloudflare, on a network, or on credentials.
// https://github.com/danbri/factoidal/issues/670
//
// It serves one directory tree read-only under the same key layout a
// bucket does — `<prefix>/CURRENT` and `<prefix>/<generation>/<key>` — and
// answers the two things a browser needs of a public bucket that this
// project's own static hosting does not give for free: a permissive
// cross-origin policy, and byte ranges.
//
// It is a TEST FIXTURE and is not a bucket. What it deliberately does not
// do: authentication, writes, listings, conditional requests, multi-range
// requests, or compression. What it deliberately does do: refuse to serve
// anything outside the root it was given, so a mistaken key cannot read
// the checkout.
//
// Usage:
//   const bucket = await startMockBucket({ root, prefix: 'skosall' })
//   bucket.url          // http://127.0.0.1:PORT/skosall/
//   bucket.requests     // every request it answered
//   await bucket.close()
//
// Standalone, to point a browser at it:
//   node tests/store-http/mock-bucket.mjs --root npm/factoidal/sample-store \
//        --prefix skosall --port 8787

import { createServer } from 'node:http'
import { createReadStream } from 'node:fs'
import { stat } from 'node:fs/promises'
import { resolve, join, sep } from 'node:path'
import { pipeline } from 'node:stream/promises'

const RANGE = /^bytes=(\d+)-(\d*)$/

// One year. A generation directory never changes after it is published, so
// its objects are immutable; CURRENT is the one mutable name and gets no
// freshness lifetime at all.
const IMMUTABLE = 'public, max-age=31536000, immutable'

/**
 * Start the mock bucket.
 *
 * @param {{root: string, prefix?: string, port?: number,
 *          host?: string, corsOrigin?: string, ranges?: boolean}} options
 *   `root` is the collection root on disk: the directory holding CURRENT.
 *   `prefix` is the key prefix the objects appear under, so the URL layout
 *   matches a bucket that holds more than one collection. `ranges: false`
 *   makes the server ignore a range request, which is how a test proves
 *   the host notices.
 * @returns {Promise<{url: string, origin: string, port: number,
 *                    requests: object[], close: () => Promise<void>}>}
 */
export async function startMockBucket (options) {
  const root = resolve(options.root)
  const prefix = (options.prefix ?? '').replace(/^\/+|\/+$/g, '')
  const host = options.host ?? '127.0.0.1'
  const corsOrigin = options.corsOrigin ?? '*'
  const ranges = options.ranges !== false
  const requests = []

  const server = createServer((request, response) => {
    const record = { method: request.method, url: request.url, range: request.headers.range ?? null }
    requests.push(record)

    const cors = {
      'access-control-allow-origin': corsOrigin,
      'access-control-allow-methods': 'GET, HEAD, OPTIONS',
      'access-control-allow-headers': 'range, content-type',
      'access-control-expose-headers': 'content-length, content-range, etag, accept-ranges',
      'access-control-max-age': '86400'
    }

    if (request.method === 'OPTIONS') {
      record.status = 204
      response.writeHead(204, cors)
      response.end()
      return
    }
    if (request.method !== 'GET' && request.method !== 'HEAD') {
      record.status = 405
      response.writeHead(405, { ...cors, allow: 'GET, HEAD, OPTIONS' })
      response.end()
      return
    }

    let pathname
    try {
      pathname = decodeURIComponent(new URL(request.url, 'http://localhost').pathname)
    } catch {
      record.status = 400
      response.writeHead(400, cors)
      response.end()
      return
    }
    let key = pathname.replace(/^\/+/, '')
    if (prefix.length > 0) {
      if (key !== prefix && !key.startsWith(prefix + '/')) {
        record.status = 404
        response.writeHead(404, cors)
        response.end()
        return
      }
      key = key.slice(prefix.length).replace(/^\/+/, '')
    }

    const target = resolve(join(root, key))
    if (target !== root && !target.startsWith(root + sep)) {
      record.status = 403
      response.writeHead(403, cors)
      response.end()
      return
    }

    stat(target).then(async (info) => {
      if (!info.isFile()) {
        record.status = 404
        response.writeHead(404, cors)
        response.end()
        return
      }
      const headers = {
        ...cors,
        'content-type': 'application/octet-stream',
        'accept-ranges': ranges ? 'bytes' : 'none',
        etag: `"${info.size}-${Math.trunc(info.mtimeMs)}"`,
        'cache-control': key === 'CURRENT' ? 'no-cache' : IMMUTABLE
      }

      const asked = ranges ? RANGE.exec(request.headers.range ?? '') : null
      let start = 0
      let end = info.size - 1
      let status = 200
      if (asked !== null) {
        start = Number(asked[1])
        end = asked[2].length > 0 ? Number(asked[2]) : info.size - 1
        if (start >= info.size || end < start) {
          record.status = 416
          response.writeHead(416, { ...cors, 'content-range': `bytes */${info.size}` })
          response.end()
          return
        }
        if (end > info.size - 1) end = info.size - 1
        status = 206
        headers['content-range'] = `bytes ${start}-${end}/${info.size}`
      }
      headers['content-length'] = String(end - start + 1)
      record.status = status
      record.bytes = end - start + 1
      response.writeHead(status, headers)
      if (request.method === 'HEAD') {
        response.end()
        return
      }
      await pipeline(createReadStream(target, { start, end }), response)
    }).catch(() => {
      record.status = 404
      if (!response.headersSent) response.writeHead(404, cors)
      response.end()
    })
  })

  await new Promise((ok, fail) => {
    server.once('error', fail)
    server.listen(options.port ?? 0, host, ok)
  })
  const port = server.address().port
  const origin = `http://${host}:${port}`
  return {
    origin,
    port,
    url: prefix.length > 0 ? `${origin}/${prefix}/` : `${origin}/`,
    requests,
    async close () {
      await new Promise((ok) => server.close(ok))
    }
  }
}

// Standalone: serve a store so a real browser can be pointed at it.
if (import.meta.url === `file://${process.argv[1]}`) {
  const argument = (name, fallback) => {
    const at = process.argv.indexOf(`--${name}`)
    return at >= 0 && at + 1 < process.argv.length ? process.argv[at + 1] : fallback
  }
  const bucket = await startMockBucket({
    root: argument('root', 'npm/factoidal/sample-store'),
    prefix: argument('prefix', 'skosall'),
    port: Number(argument('port', '8787'))
  })
  process.stdout.write(`mock bucket: ${bucket.url}\n`)
}
