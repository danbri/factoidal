// test/xmpp-serve.test.mjs — the Node XMPP host (`xmpp/server.mjs`) over
// REAL sockets, against the Lean engine in wasm.
//
// Nothing here implements XMPP: each case writes bytes to a TCP socket
// and asserts on the bytes that come back, the same sequences
// `tests/xmpp/server.mjs` replays through the native `l4xmpp-serve`
// binary. A pass means the wasm build of `L4Factoidal.XMPP.Server` did
// it, through this host's sockets and routing table.
//
// Skips wholesale when the Lean wasm assets are not resolvable, and
// when the resolved bundle predates the session ops (`xmppOpen` …) —
// the same pattern `test/xmpp.test.mjs` uses.

import { test } from 'node:test'
import assert from 'node:assert/strict'
import net from 'node:net'
import { mkdtemp, readFile, writeFile, mkdir, readdir, rm } from 'node:fs/promises'
import { tmpdir } from 'node:os'
import { join } from 'node:path'

const DOMAIN = 'example.com'
const NS_SASL = 'urn:ietf:params:xml:ns:xmpp-sasl'
const NS_BIND = 'urn:ietf:params:xml:ns:xmpp-bind'
const NS_ROSTER = 'jabber:iq:roster'
const ACCOUNTS = 'juliet:r0m30\nromeo:juli3t\n'

const streamOpen = (to = DOMAIN) =>
  `<?xml version='1.0'?><stream:stream to='${to}' xmlns='jabber:client'` +
  ` xmlns:stream='http://etherx.jabber.org/streams' version='1.0'>`
const plainAuth = (user, pw) =>
  `<auth xmlns='${NS_SASL}' mechanism='PLAIN'>` +
  Buffer.from(`\0${user}\0${pw}`, 'utf8').toString('base64') + '</auth>'
const bindIq = (id, resource) =>
  `<iq type='set' id='${id}'><bind xmlns='${NS_BIND}'>` +
  (resource ? `<resource>${resource}</resource>` : '') + '</bind></iq>'

let serverModule = null
let available = false
let skipReason = ''
try {
  serverModule = await import('../xmpp/server.mjs')
  const probe = await serverModule.xmppServerOpsAvailable()
  available = probe.available
  if (!available) skipReason = `the resolved wasm bundle lacks ${probe.missing.join(', ')}`
} catch (error) {
  skipReason = `the Lean wasm assets are not resolvable: ${error.message}`
}

/** A raw client: write text, wait for a needle in everything received. */
function connect (port) {
  const socket = net.connect(port, '127.0.0.1')
  let buffer = ''
  const waiters = []
  socket.setEncoding('utf8')
  socket.on('data', (chunk) => {
    buffer += chunk
    for (const w of waiters.splice(0)) w()
  })
  return {
    socket,
    get received () { return buffer },
    reset () { buffer = '' },
    /** Drop everything up to and including the first `needle`, keeping
     *  what arrived after it in the same TCP read. */
    consumeThrough (needle) {
      const at = buffer.indexOf(needle)
      buffer = at < 0 ? '' : buffer.slice(at + needle.length)
    },
    write (text) { socket.write(text) },
    ready () { return new Promise((resolve, reject) => { socket.once('connect', resolve); socket.once('error', reject) }) },
    waitFor (needle, ms = 15000) {
      return new Promise((resolve, reject) => {
        const t0 = Date.now()
        const tick = () => {
          if (buffer.includes(needle)) return resolve(buffer)
          if (Date.now() - t0 > ms) return reject(new Error(`timed out waiting for ${needle}\ngot: ${buffer}`))
          waiters.push(tick)
          setTimeout(tick, 50)
        }
        tick()
      })
    },
    closed () { return new Promise((resolve) => socket.once('close', resolve)) },
    end () { socket.end() }
  }
}

/** Negotiate to a bound session and return the client. */
async function bound (port, user, pw, resource) {
  const c = connect(port)
  await c.ready()
  c.write(streamOpen())
  await c.waitFor('</stream:features>')
  c.reset()
  c.write(plainAuth(user, pw))
  await c.waitFor('<success')
  c.reset()
  c.write(streamOpen())
  await c.waitFor('</stream:features>')
  c.reset()
  c.write(bindIq('b1', resource))
  await c.waitFor('</iq>')
  const jid = c.received.match(/<jid>([^<]*)<\/jid>/)[1]
  // A stanza held for this account is delivered the moment it binds and
  // can share the TCP read with the bind result: keep it.
  c.consumeThrough('</iq>')
  return { client: c, jid }
}

test('xmpp-serve: a full session over a TCP socket, through wasm', { skip: available ? false : skipReason }, async (t) => {
  const dir = await mkdtemp(join(tmpdir(), 'l4xmpp-wasm-'))
  await writeFile(join(dir, 'accounts'), ACCOUNTS)
  const errors = []
  const running = await serverModule.listen({
    dir, domain: DOMAIN, port: 0, pollMs: 50, onError: (e) => errors.push(e.message)
  })
  t.after(async () => { await running.close(); await rm(dir, { recursive: true, force: true }) })

  await t.test('RFC 6120 4.2/4.3: the stream header is answered with features offering SASL, not bind', async () => {
    const c = connect(running.port)
    await c.ready()
    c.write(streamOpen())
    const got = await c.waitFor('</stream:features>')
    assert.ok(got.includes(`from='${DOMAIN}'`), got)
    assert.ok(got.includes('<mechanism>SCRAM-SHA-256</mechanism>'), got)
    assert.ok(got.includes('<mechanism>PLAIN</mechanism>'), got)
    assert.ok(!got.includes(`<bind xmlns="${NS_BIND}"`), got)
    c.end()
  })

  await t.test('RFC 6120 4.9.3.6: a stream for another domain is host-unknown and the socket closes', async () => {
    const c = connect(running.port)
    await c.ready()
    c.write(streamOpen('elsewhere.example'))
    const got = await c.waitFor('</stream:stream>')
    assert.ok(got.includes('<host-unknown'), got)
    await c.closed()
  })

  await t.test('RFC 6120 6.5: a wrong password is not-authorized', async () => {
    const c = connect(running.port)
    await c.ready()
    c.write(streamOpen() + plainAuth('juliet', 'wrong'))
    const got = await c.waitFor('</failure>')
    assert.ok(got.includes('<not-authorized/>'), got)
    assert.ok(!got.includes('<success'), got)
    c.end()
  })

  await t.test('RFC 7677: SCRAM-SHA-256 computed independently with node:crypto authenticates', async () => {
    const crypto = await import('node:crypto')
    const clientNonce = 'fyko+d2lbbFgONRv9qkxdawL'
    const clientFirstBare = `n=juliet,r=${clientNonce}`
    const c = connect(running.port)
    await c.ready()
    c.write(streamOpen())
    await c.waitFor('</stream:features>')
    c.reset()
    c.write(`<auth xmlns='${NS_SASL}' mechanism='SCRAM-SHA-256'>` +
      Buffer.from(`n,,${clientFirstBare}`, 'utf8').toString('base64') + '</auth>')
    await c.waitFor('</challenge>')
    const serverFirst = Buffer.from(
      c.received.match(/<challenge[^>]*>([^<]*)<\/challenge>/)[1], 'base64').toString('utf8')
    const [, nonce, saltB64, iter] = serverFirst.match(/^r=(.*),s=(.*),i=(\d+)$/)
    assert.ok(nonce.startsWith(clientNonce), serverFirst)
    const salted = crypto.pbkdf2Sync('r0m30', Buffer.from(saltB64, 'base64'), parseInt(iter, 10), 32, 'sha256')
    const hmac = (k, msg) => crypto.createHmac('sha256', k).update(msg).digest()
    const clientKey = hmac(salted, 'Client Key')
    const storedKey = crypto.createHash('sha256').update(clientKey).digest()
    const clientFinalNoProof = `c=biws,r=${nonce}`
    const authMessage = `${clientFirstBare},${serverFirst},${clientFinalNoProof}`
    const clientSig = hmac(storedKey, authMessage)
    const proof = Buffer.alloc(32)
    for (let i = 0; i < 32; i++) proof[i] = clientKey[i] ^ clientSig[i]
    const serverKey = hmac(salted, 'Server Key')
    const expectedServerSig = hmac(serverKey, authMessage).toString('base64')
    c.reset()
    c.write(`<response xmlns='${NS_SASL}'>` +
      Buffer.from(`${clientFinalNoProof},p=${proof.toString('base64')}`, 'utf8').toString('base64') +
      '</response>')
    const got = await c.waitFor('<success')
    const verifier = Buffer.from(got.match(/<success[^>]*>([^<]*)<\/success>/)[1], 'base64').toString('utf8')
    assert.equal(verifier, `v=${expectedServerSig}`)
    c.end()
  })

  await t.test('RFC 6120 7: binding returns the full JID; a message reaches the other session with the server-stamped from', async () => {
    const juliet = await bound(running.port, 'juliet', 'r0m30', 'balcony')
    assert.equal(juliet.jid, `juliet@${DOMAIN}/balcony`)
    const romeo = await bound(running.port, 'romeo', 'juli3t', '')
    assert.ok(romeo.jid.startsWith(`romeo@${DOMAIN}/`), romeo.jid)
    assert.equal(running.sessions().filter((s) => s.full !== null).length, 2)

    // The stanza arrives in two TCP writes with a spoofed from.
    const message = `<message to='romeo@${DOMAIN}' from='mercutio@${DOMAIN}/x' type='chat'><body>Wilt thou be gone?</body></message>`
    juliet.client.write(message.slice(0, 40))
    await new Promise((resolve) => setTimeout(resolve, 100))
    assert.equal(romeo.client.received, '', 'nothing is delivered before the stanza is complete')
    juliet.client.write(message.slice(40))
    const got = await romeo.client.waitFor('</message>')
    assert.ok(got.includes(`from="juliet@${DOMAIN}/balcony"`), got)
    assert.ok(!got.includes('mercutio'), got)
    assert.ok(got.includes('<body>Wilt thou be gone?</body>'), got)
    juliet.client.end()
    romeo.client.end()
  })

  await t.test('a message to an account with no bound session is held, then delivered once it binds', async () => {
    const juliet = await bound(running.port, 'juliet', 'r0m30', 'balcony')
    juliet.client.write(`<message to='romeo@${DOMAIN}'><body>later</body></message>`)
    await new Promise((resolve) => setTimeout(resolve, 100))
    assert.equal(running.pending().get(`romeo@${DOMAIN}`)?.length, 1)
    const romeo = await bound(running.port, 'romeo', 'juli3t', 'orchard')
    const got = await romeo.client.waitFor('</message>')
    assert.ok(got.includes('<body>later</body>'), got)
    assert.equal(running.pending().has(`romeo@${DOMAIN}`), false)
    juliet.client.end()
    romeo.client.end()
  })

  await t.test('RFC 6121 2: a roster set is pushed back and persisted under DIR/roster as the engine encodes it', async () => {
    const juliet = await bound(running.port, 'juliet', 'r0m30', 'balcony')
    juliet.client.write(`<iq type='set' id='r1'><query xmlns='${NS_ROSTER}'><item jid='romeo@${DOMAIN}' name='Romeo'/></query></iq>`)
    const got = await juliet.client.waitFor('push-r1')
    assert.ok(got.includes(`<iq type="result" id="r1"/>`), got)
    assert.ok(got.includes(`jid="romeo@${DOMAIN}" name="Romeo" subscription="none"`), got)
    await new Promise((resolve) => setTimeout(resolve, 150))
    const files = await readdir(join(dir, 'roster'))
    assert.deepEqual(files, [`juliet%40${DOMAIN}.tsv`])
    const encoded = await readFile(join(dir, 'roster', files[0]), 'utf8')
    assert.equal(encoded, `romeo@${DOMAIN}\tRomeo\tnone\t0`)
    juliet.client.reset()
    juliet.client.write(`<iq type='get' id='r2'><query xmlns='${NS_ROSTER}'/></iq>`)
    const again = await juliet.client.waitFor('</iq>')
    assert.ok(again.includes(`jid="romeo@${DOMAIN}"`), again)
    juliet.client.end()
  })

  await t.test('a stanza written as a file under DIR/spool/<bare jid>/ is delivered to the bound session and unlinked', async () => {
    const romeo = await bound(running.port, 'romeo', 'juli3t', 'orchard')
    const box = join(dir, 'spool', `romeo%40${DOMAIN}`)
    await mkdir(box, { recursive: true })
    await writeFile(join(box, '1-1'), `<message from='${DOMAIN}' to='romeo@${DOMAIN}'><body>from a file</body></message>`)
    const got = await romeo.client.waitFor('</message>')
    assert.ok(got.includes('<body>from a file</body>'), got)
    await new Promise((resolve) => setTimeout(resolve, 150))
    assert.deepEqual(await readdir(box), [])
    romeo.client.end()
  })

  await t.test('RFC 6120 4.4: a client that half-closes gets the stream close', async () => {
    const c = connect(running.port)
    await c.ready()
    c.write(streamOpen())
    await c.waitFor('</stream:features>')
    c.socket.end()
    const got = await c.waitFor('</stream:stream>')
    assert.ok(got.endsWith('</stream:stream>'), got)
  })

  await t.test('RFC 6120 4.9: a complete but not-well-formed stanza is a stream error, not a crash', async () => {
    const juliet = await bound(running.port, 'juliet', 'r0m30', 'balcony')
    // An undefined entity: the framer cuts a complete unit (depth returns
    // to zero), the XML parser refuses it. `<message><body>x</message>`
    // would instead wait for the unit to complete, as it does natively.
    juliet.client.write('<message><body>&bogus;</body></message>')
    const got = await juliet.client.waitFor('</stream:stream>')
    assert.ok(got.includes('<stream:error'), got)
    await juliet.client.closed()
    const after = await bound(running.port, 'juliet', 'r0m30', 'balcony')
    assert.equal(after.jid, `juliet@${DOMAIN}/balcony`)
    after.client.end()
  })

  assert.deepEqual(errors, [])
})

test('xmpp-serve: rosters persisted by one run are loaded by the next', { skip: available ? false : skipReason }, async (t) => {
  const dir = await mkdtemp(join(tmpdir(), 'l4xmpp-wasm-'))
  await writeFile(join(dir, 'accounts'), ACCOUNTS)
  t.after(async () => { await rm(dir, { recursive: true, force: true }) })
  const first = await serverModule.listen({ dir, domain: DOMAIN, port: 0, pollMs: 0 })
  {
    const juliet = await bound(first.port, 'juliet', 'r0m30', 'balcony')
    juliet.client.write(`<iq type='set' id='r1'><query xmlns='${NS_ROSTER}'><item jid='romeo@${DOMAIN}' name='Romeo'/></query></iq>`)
    await juliet.client.waitFor('push-r1')
    await new Promise((resolve) => setTimeout(resolve, 150))
    juliet.client.end()
  }
  await first.close()
  const second = await serverModule.listen({ dir, domain: DOMAIN, port: 0, pollMs: 0 })
  t.after(() => second.close())
  const juliet = await bound(second.port, 'juliet', 'r0m30', 'balcony')
  juliet.client.write(`<iq type='get' id='r2'><query xmlns='${NS_ROSTER}'/></iq>`)
  const got = await juliet.client.waitFor('</iq>')
  assert.ok(got.includes(`jid="romeo@${DOMAIN}" name="Romeo"`), got)
  juliet.client.end()
})
