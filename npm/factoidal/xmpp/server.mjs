// factoidal/xmpp/server.mjs — a Node host for the Lean XMPP server
// (`formal/lean4/L4Factoidal/XMPP/`), through the wasm session ops of
// `formal/lean4/Wasm/Ops/XmppSession.lean`.
//
// This file is a socket, a UTF-8 decoder and a routing table. Every
// protocol decision — what answers a stream header, whether a password
// is right, where a stanza goes, what a roster looks like as bytes —
// is made by `L4Factoidal.XMPP.Server.step` inside the engine and
// reaches this file as the `send`/`route`/`presence`/`close` members of
// one `xmppSessionFeed` answer. Iron rule 7 of `CLAUDE.md`: no protocol
// logic in a host. What this host does instead, and the native harness
// (`formal/lean4/Harness/XmppServe.lean`) does with files:
//
//   * one engine session per TCP (or direct-TLS, XEP-0368) connection;
//   * `route` → find the sessions bound to that bare JID and call
//     `xmppSessionDeliver` on each; none bound → hold the stanza in
//     memory until one binds (`xmppSessionDeliver` itself refuses an
//     unbound session, so nothing is destroyed on the way);
//   * `rostersSaved` → fetch the roster bytes with `xmppRosterGet` and
//     write them under DIR/roster/, unread, so a restart gets them back
//     through `xmppRosterSet`;
//   * DIR/spool/<bare jid>/<file> → the harness's mailbox layout, polled
//     for bound sessions and delivered, so a process that is not an XMPP
//     client (a web application, say) can hand a stanza to a user by
//     writing a file, exactly as it can with the native carrier.
//
// The wasm contract (`xmppOpen`, `xmppSessionOpen`, `xmppSessionFeed`,
// `xmppSessionDeliver`, `xmppSessionClose`, `xmppRosterGet`,
// `xmppRosterSet`, `xmppClose`) is stated in the Lean module's header.
//
// Not implemented, said here rather than left to be discovered: STARTTLS
// (RFC 6120 section 5 — give `cert` and `key` for direct TLS on 5223
// instead), server-to-server federation, and any limit on how many bytes
// a client may send without completing a unit beyond `maxBuffered`,
// which is a transport limit this host applies by closing the socket.

import { randomBytes } from 'node:crypto'
import { StringDecoder } from 'node:string_decoder'
import { mkdir, readFile, writeFile, readdir, unlink } from 'node:fs/promises'
import { join } from 'node:path'
import { loadEngine } from '../bin/engine.mjs'

/** The ops this host needs from the engine. */
export const XMPP_SERVER_OPS = [
  'xmppOpen', 'xmppClose',
  'xmppSessionOpen', 'xmppSessionFeed', 'xmppSessionDeliver', 'xmppSessionClose',
  'xmppRosterGet', 'xmppRosterSet'
]

/** An error raised by this host, as opposed to one the engine reported.
 *  `unknownOp` is set when the loaded WebAssembly module does not carry
 *  the operation at all, which is what a test skips on and what the CLI
 *  reports as "not yet wired". */
export class XmppHostError extends Error {
  constructor (message, detail = {}) {
    super(message)
    this.name = 'XmppHostError'
    this.unknownOp = detail.unknownOp === true
  }
}

function isUnknownOp (error) {
  const text = error && error.message ? String(error.message) : String(error)
  return text.indexOf('unknown op') >= 0
}

/**
 * Whether the loaded engine carries the XMPP server operations.
 *
 * @param {object} [options]
 * @param {object} [options.engine] an engine handle to reuse
 * @returns {Promise<{available: boolean, missing: string[]}>}
 */
export async function xmppServerOpsAvailable (options = {}) {
  const engine = options.engine !== undefined ? options.engine : await loadEngine()
  let names
  try {
    names = engine.call('ops', []).ops
  } catch (_error) {
    return { available: false, missing: XMPP_SERVER_OPS.slice() }
  }
  const missing = XMPP_SERVER_OPS.filter((op) => !names.includes(op))
  return { available: missing.length === 0, missing }
}

/** A bare JID as one path segment: the harness's `pathSafe`
 *  (`Harness/XmppServe.lean`), so the two hosts share a state directory.
 *  Every byte that is not a letter, a digit, `.`, `-` or `_` is written
 *  as `%` and two lowercase hex digits. */
export function pathSafe (s) {
  let out = ''
  for (const byte of Buffer.from(s, 'utf8')) {
    const ch = String.fromCharCode(byte)
    if (byte < 0x80 && /[A-Za-z0-9._-]/.test(ch)) out += ch
    else out += '%' + byte.toString(16).padStart(2, '0')
  }
  return out
}

/** Unpredictable values for the stream id and the SCRAM server nonce
 *  (RFC 6120 section 4.7.3, RFC 5802 section 5.1). The engine has no
 *  random source and asks the host for both. */
function randomToken (bytes = 18) {
  return randomBytes(bytes).toString('base64url')
}

/**
 * Open one XMPP server on the engine and return the handle plus the
 * calls a host makes against it.
 *
 * @param {object} options
 * @param {string} [options.domain] the domain the server is authoritative for (default `localhost`)
 * @param {Array<{username: string, password: string}>} [options.accounts]
 * @param {string} [options.accountsText] `user:password` lines, the harness's accounts-file format
 * @param {string} [options.saltB64] the SCRAM salt, base64
 * @param {number} [options.iterationCount] the SCRAM iteration count
 * @param {boolean} [options.tlsCarrier] whether the carrier terminates TLS
 * @param {object} [options.engine] an engine handle to reuse
 * @returns {Promise<{engine: object, handle: string, domain: string,
 *   openSession: Function, roster: Function, setRoster: Function, close: Function}>}
 */
export async function openXmppServer (options = {}) {
  const engine = options.engine !== undefined ? options.engine : await loadEngine()
  const config = {}
  if (typeof options.domain === 'string') config.domain = options.domain
  if (Array.isArray(options.accounts)) config.accounts = options.accounts
  if (typeof options.accountsText === 'string') config.accountsText = options.accountsText
  if (typeof options.saltB64 === 'string') config.saltB64 = options.saltB64
  if (typeof options.iterationCount === 'number') config.iterationCount = options.iterationCount
  if (typeof options.tlsCarrier === 'boolean') config.tlsCarrier = options.tlsCarrier
  let opened
  try {
    opened = engine.call('xmppOpen', [JSON.stringify(config)])
  } catch (error) {
    if (isUnknownOp(error)) {
      throw new XmppHostError(
        'the loaded l4factoidal WebAssembly module does not carry xmppOpen',
        { unknownOp: true })
    }
    throw error
  }
  if (typeof opened.handle !== 'string' || opened.handle.length === 0) {
    throw new XmppHostError('xmppOpen answered with no handle')
  }
  const handle = opened.handle
  return {
    engine,
    handle,
    domain: typeof opened.domain === 'string' ? opened.domain : (config.domain || 'localhost'),
    accounts: typeof opened.accounts === 'number' ? opened.accounts : undefined,
    /**
     * One client connection.
     * @param {{streamId?: string, nonce?: string, tlsCarrier?: boolean, maxUnits?: number}} [sessionOptions]
     */
    openSession (sessionOptions = {}) {
      const record = {
        streamId: typeof sessionOptions.streamId === 'string' ? sessionOptions.streamId : randomToken(),
        nonce: typeof sessionOptions.nonce === 'string' ? sessionOptions.nonce : randomToken()
      }
      if (typeof sessionOptions.tlsCarrier === 'boolean') record.tlsCarrier = sessionOptions.tlsCarrier
      if (typeof sessionOptions.maxUnits === 'number') record.maxUnits = sessionOptions.maxUnits
      const answer = engine.call('xmppSessionOpen', [handle, JSON.stringify(record)])
      if (typeof answer.handle !== 'string') throw new XmppHostError('xmppSessionOpen answered with no handle')
      const session = answer.handle
      let open = true
      return {
        handle: session,
        /** Feed received text; returns the engine's answer document. */
        feed (text) {
          return engine.call('xmppSessionFeed', [session, text])
        },
        /** Hand this session a stanza another session routed to it. */
        deliver (text) {
          return engine.call('xmppSessionDeliver', [session, text])
        },
        /** End of input: returns `{send: string[]}` and releases the handle. */
        close () {
          if (!open) return { send: [] }
          open = false
          try {
            return engine.call('xmppSessionClose', [session])
          } catch (_error) {
            return { send: [] }
          }
        }
      }
    },
    /** The roster of a bare JID: `{encoded, items}`. */
    roster (bare) {
      return engine.call('xmppRosterGet', [handle, bare])
    },
    /** Load a roster the host persisted (the `encoded` of `roster()`). */
    setRoster (bare, encoded) {
      engine.call('xmppRosterSet', [handle, bare, encoded])
    },
    close () {
      try { engine.call('xmppClose', [handle]) } catch (_error) { /* already gone */ }
    }
  }
}

/** Load `DIR/accounts` (one `user:password` per line) if it exists. */
async function readAccountsFile (path) {
  try {
    return await readFile(path, 'utf8')
  } catch (error) {
    if (error && error.code === 'ENOENT') return null
    throw error
  }
}

/**
 * A `net.Server` (or `tls.Server`, when `cert` and `key` are given —
 * XEP-0368 direct TLS) that runs one engine session per connection.
 *
 * The server is returned unlistened: the caller chooses the port.
 *
 * @param {object} options as `openXmppServer`, plus:
 * @param {string} [options.dir] state directory: `accounts` is read from it when
 *   no accounts are given; rosters are persisted under `roster/`; `spool/` is
 *   polled for stanzas written by other processes
 * @param {string|Buffer} [options.cert] PEM certificate chain for direct TLS
 * @param {string|Buffer} [options.key] PEM private key for direct TLS
 * @param {number} [options.pollMs] spool poll interval (default 250; 0 disables)
 * @param {number} [options.maxBuffered] bytes a connection may hold without
 *   completing a unit before the socket is closed (default 1 MiB)
 * @param {Function} [options.onError]
 * @param {Function} [options.onLog]
 * @returns {Promise<{server: object, xmpp: object, close: Function, sessions: Function}>}
 */
export async function createXmppServer (options = {}) {
  const onError = typeof options.onError === 'function'
    ? options.onError
    : (error) => { console.error(`xmpp-serve: ${error.message}`) }
  const onLog = typeof options.onLog === 'function' ? options.onLog : () => {}
  const dir = typeof options.dir === 'string' ? options.dir : null
  const pollMs = typeof options.pollMs === 'number' ? options.pollMs : 250
  const maxBuffered = typeof options.maxBuffered === 'number' ? options.maxBuffered : 1024 * 1024

  const serverOptions = { ...options }
  if (dir !== null && !Array.isArray(options.accounts) && typeof options.accountsText !== 'string') {
    const text = await readAccountsFile(join(dir, 'accounts'))
    if (text !== null) serverOptions.accountsText = text
  }
  const useTls = options.cert !== undefined && options.key !== undefined
  if (typeof serverOptions.tlsCarrier !== 'boolean') serverOptions.tlsCarrier = useTls
  const xmpp = await openXmppServer(serverOptions)

  // Rosters the previous run persisted.
  if (dir !== null) {
    await mkdir(join(dir, 'roster'), { recursive: true })
    await mkdir(join(dir, 'spool'), { recursive: true })
    for (const name of await readdir(join(dir, 'roster'))) {
      if (!name.endsWith('.tsv')) continue
      const bare = decodeURIComponent(name.slice(0, -4))
      try {
        xmpp.setRoster(bare, await readFile(join(dir, 'roster', name), 'utf8'))
      } catch (error) {
        onError(new XmppHostError(`roster ${name}: ${error.message}`))
      }
    }
  }

  /** Every live connection: socket, engine session, and the last `bare`/`full` the engine reported. */
  const connections = new Set()
  /** bare JID → stanzas routed to it while no session was bound. */
  const pending = new Map()

  function boundTo (bare) {
    const found = []
    for (const c of connections) if (c.full !== null && c.bare === bare) found.push(c)
    return found
  }

  function writeAll (c, lines) {
    for (const line of lines) if (!c.socket.destroyed) c.socket.write(line)
  }

  /** Deliver one stanza to every session bound to `bare`, or hold it. */
  function routeStanza (bare, text) {
    const targets = boundTo(bare)
    if (targets.length === 0) {
      if (!pending.has(bare)) pending.set(bare, [])
      pending.get(bare).push(text)
      return
    }
    for (const t of targets) {
      let answer
      try { answer = t.session.deliver(text) } catch (error) { onError(error); continue }
      if (answer.delivered === true) writeAll(t, answer.send)
      else {
        if (!pending.has(bare)) pending.set(bare, [])
        pending.get(bare).push(text)
      }
    }
  }

  /** A session just bound: hand it what was waiting. */
  function flushPending (c) {
    const queue = pending.get(c.bare)
    if (!queue || queue.length === 0) return
    pending.delete(c.bare)
    for (const text of queue) routeStanza(c.bare, text)
  }

  async function persistRosters (bares) {
    if (dir === null) return
    for (const bare of bares) {
      try {
        const { encoded } = xmpp.roster(bare)
        await writeFile(join(dir, 'roster', pathSafe(bare) + '.tsv'), encoded)
      } catch (error) {
        onError(new XmppHostError(`persisting roster of ${bare}: ${error.message}`))
      }
    }
  }

  /** Perform one feed answer. */
  function perform (c, answer) {
    writeAll(c, answer.send)
    const wasBound = c.full !== null
    c.bare = typeof answer.bare === 'string' ? answer.bare : null
    c.full = typeof answer.full === 'string' ? answer.full : null
    for (const r of answer.route) routeStanza(r.to, r.text)
    if (Array.isArray(answer.rostersSaved) && answer.rostersSaved.length > 0) {
      persistRosters(answer.rostersSaved)
    }
    if (!wasBound && c.full !== null) flushPending(c)
    if (answer.close === true) {
      c.closing = true
      c.socket.end()
    }
  }

  function endSession (c) {
    if (!connections.has(c)) return
    connections.delete(c)
    let answer
    try { answer = c.session.close() } catch (error) { onError(error); answer = { send: [] } }
    if (!c.closing && !c.socket.destroyed) {
      writeAll(c, answer.send)
      c.socket.end()
    }
  }

  function onConnection (socket) {
    let session
    try {
      session = xmpp.openSession({ tlsCarrier: useTls })
    } catch (error) {
      onError(error)
      socket.destroy()
      return
    }
    const c = {
      socket,
      session,
      bare: null,
      full: null,
      closing: false,
      decoder: new StringDecoder('utf8'),
      buffered: 0
    }
    connections.add(c)
    onLog(`connection from ${socket.remoteAddress}:${socket.remotePort}`)
    socket.on('data', (chunk) => {
      if (!connections.has(c)) return
      const text = c.decoder.write(chunk)
      if (text.length === 0) return
      let answer
      try {
        answer = session.feed(text)
      } catch (error) {
        onError(error)
        socket.destroy()
        connections.delete(c)
        return
      }
      // A transport limit, not a protocol one: a client that sends this
      // much without completing a unit is cut off.
      c.buffered = answer.send.length > 0 || answer.route.length > 0 ? 0 : c.buffered + chunk.length
      perform(c, answer)
      if (c.buffered > maxBuffered) {
        onError(new XmppHostError(`connection exceeded ${maxBuffered} buffered bytes`))
        socket.destroy()
        connections.delete(c)
        try { session.close() } catch (_error) { /* gone */ }
      }
    })
    socket.on('end', () => endSession(c))
    socket.on('close', () => endSession(c))
    socket.on('error', (error) => {
      if (error && error.code !== 'ECONNRESET') onError(error)
      endSession(c)
    })
  }

  let server
  if (useTls) {
    const tls = await import('node:tls')
    server = tls.createServer({ cert: options.cert, key: options.key }, onConnection)
  } else {
    const net = await import('node:net')
    server = net.createServer(onConnection)
  }

  // The harness's mailbox: `<dir>/spool/<bare jid>/<name>` holds one
  // stanza's bytes for that account. Polled for every bound session,
  // delivered in name order, unlinked once the engine accepted it.
  let poller = null
  let polling = false
  async function pollSpool () {
    if (polling || dir === null) return
    polling = true
    try {
      const bares = new Set()
      for (const c of connections) if (c.full !== null) bares.add(c.bare)
      for (const bare of bares) {
        const box = join(dir, 'spool', pathSafe(bare))
        let names
        try { names = (await readdir(box)).sort() } catch (_error) { continue }
        for (const name of names) {
          const path = join(box, name)
          let text
          try { text = await readFile(path, 'utf8') } catch (_error) { continue }
          const targets = boundTo(bare)
          if (targets.length === 0) break
          let accepted = false
          for (const t of targets) {
            try {
              const answer = t.session.deliver(text)
              if (answer.delivered === true) { writeAll(t, answer.send); accepted = true }
            } catch (error) { onError(error) }
          }
          if (accepted) await unlink(path).catch(() => {})
        }
      }
    } finally {
      polling = false
    }
  }
  if (dir !== null && pollMs > 0) {
    poller = setInterval(() => { pollSpool().catch(onError) }, pollMs)
    if (typeof poller.unref === 'function') poller.unref()
  }

  return {
    server,
    xmpp,
    /** The live connections' `{bare, full}` pairs, for a host's own view. */
    sessions () {
      return Array.from(connections, (c) => ({ bare: c.bare, full: c.full }))
    },
    /** Stanzas held for accounts with no bound session. */
    pending () {
      return new Map(pending)
    },
    close () {
      return new Promise((resolve) => {
        if (poller !== null) clearInterval(poller)
        for (const c of Array.from(connections)) {
          endSession(c)
          c.socket.destroy()
        }
        server.close(() => {
          xmpp.close()
          resolve()
        })
      })
    }
  }
}

/**
 * Start a server and resolve once it is listening.
 *
 * @param {object} options as `createXmppServer`, plus `port` and `host`
 * @returns {Promise<{server: object, xmpp: object, port: number, host: string,
 *   origin: string, close: Function, sessions: Function}>}
 */
export async function listen (options = {}) {
  const port = typeof options.port === 'number' ? options.port : 0
  const host = typeof options.host === 'string' ? options.host : '127.0.0.1'
  const created = await createXmppServer(options)
  try {
    await new Promise((resolve, reject) => {
      created.server.once('error', reject)
      created.server.listen(port, host, resolve)
    })
  } catch (error) {
    created.xmpp.close()
    throw error
  }
  const bound = created.server.address()
  const scheme = options.cert !== undefined && options.key !== undefined ? 'xmpps' : 'xmpp'
  return { ...created, port: bound.port, host, origin: `${scheme}://${host}:${bound.port}` }
}
