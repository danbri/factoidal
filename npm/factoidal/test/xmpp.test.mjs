// factoidal/xmpp — unit tests for npm/factoidal/xmpp/index.mjs.
//
// Skips wholesale when the Lean wasm assets are not resolvable, and
// skips per-op when the resolved wasm predates the XMPP ops (protects
// against a stale committed bundle — see l4-core.test.js for the same
// pattern this file follows).
//
// Run: node --test test/xmpp.test.mjs

import test from 'node:test'
import assert from 'node:assert/strict'
import {
  loadXmppEngine,
  xmppOpsAvailable,
  parseJid,
  renderJid,
  parseStreamHeader,
  renderStreamHeader,
  featuresFor,
  parseStanza
} from '../xmpp/index.mjs'

let enginePromise = null
function engine () {
  if (!enginePromise) enginePromise = loadXmppEngine().catch(() => null)
  return enginePromise
}

async function skipUnlessAvailable (t) {
  const eng = await engine()
  if (eng === null) {
    t.skip('Lean wasm assets not resolvable')
    return true
  }
  const { available, missing } = await xmppOpsAvailable({ engine: eng })
  if (!available) {
    t.skip(`resolved Lean wasm predates XMPP ops: ${missing.join(', ')} ` +
      '(rebuild formal/lean4/Wasm/build-wasm.sh to unskip)')
    return true
  }
  return false
}

// ---- parseJid / renderJid --------------------------------------------

test('parseJid: bare domain', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  const result = await parseJid('example.com', { engine: eng })
  assert.equal(result.ok, true)
  assert.deepEqual(result.value, {
    localpart: null, domainpart: 'example.com', resourcepart: null, wellFormed: true
  })
})

test('parseJid: localpart + domain + resource', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  const result = await parseJid('romeo@example.net/orchard', { engine: eng })
  assert.equal(result.ok, true)
  assert.deepEqual(result.value, {
    localpart: 'romeo', domainpart: 'example.net', resourcepart: 'orchard', wellFormed: true
  })
})

test('parseJid: a resourcepart containing "@" and "/" round-trips', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  const result = await parseJid('example.com/res@ource/with/slashes', { engine: eng })
  assert.equal(result.ok, true)
  assert.equal(result.value.resourcepart, 'res@ource/with/slashes')
})

test('parseJid: empty localpart ("@example.com") is rejected, not silently dropped', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  const result = await parseJid('@example.com', { engine: eng })
  assert.equal(result.ok, false)
  assert.equal(result.unknownOp, false)
})

test('parseJid: empty domainpart ("juliet@") is rejected', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  const result = await parseJid('juliet@', { engine: eng })
  assert.equal(result.ok, false)
})

test('parseJid: empty resourcepart ("juliet@example.com/") is rejected', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  const result = await parseJid('juliet@example.com/', { engine: eng })
  assert.equal(result.ok, false)
})

test('parseJid: the empty string is rejected', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  const result = await parseJid('', { engine: eng })
  assert.equal(result.ok, false)
})

test('renderJid: round-trips a parsed JID back to the same string', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  const parsed = await parseJid('romeo@example.net/orchard', { engine: eng })
  assert.equal(parsed.ok, true)
  const rendered = await renderJid(parsed.value, { engine: eng })
  assert.equal(rendered.ok, true)
  assert.equal(rendered.value, 'romeo@example.net/orchard')
})

test('renderJid: missing required domainpart is rejected', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  const result = await renderJid({ localpart: 'romeo' }, { engine: eng })
  assert.equal(result.ok, false)
})

// ---- parseStreamHeader / renderStreamHeader ---------------------------

test('parseStreamHeader: a real captured ejabberd stream-open tag ' +
  '(2026-09-07, foafmixer pilot container), leading <?xml?> declaration included', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  const xml = "<?xml version='1.0'?><stream:stream id='6532308259630420668' " +
    "version='1.0' xml:lang='en' xmlns:stream='http://etherx.jabber.org/streams' " +
    "from='foafmixer.test' xmlns='jabber:client'>"
  const result = await parseStreamHeader(xml, { engine: eng })
  assert.equal(result.ok, true)
  assert.equal(result.value.from, 'foafmixer.test')
  assert.equal(result.value.to, null)
  assert.equal(result.value.id, '6532308259630420668')
  assert.equal(result.value.version, '1.0')
  assert.equal(result.value.lang, 'en')
  assert.equal(result.value.rest, '')
})

test('parseStreamHeader: a non-stream tag is rejected', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  const result = await parseStreamHeader('<message/>', { engine: eng })
  assert.equal(result.ok, false)
})

test('parseStreamHeader: a stream header with a structurally bad "to" JID is rejected', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  const result = await parseStreamHeader("<stream:stream to='@bad'>", { engine: eng })
  assert.equal(result.ok, false)
})

test('renderStreamHeader: round-trips through parseStreamHeader', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  const header = { from: 'juliet@im.example.com', to: 'im.example.com', id: 'abc', version: '1.0', lang: 'en' }
  const rendered = await renderStreamHeader(header, { engine: eng })
  assert.equal(rendered.ok, true)
  const reparsed = await parseStreamHeader(rendered.value, { engine: eng })
  assert.equal(reparsed.ok, true)
  assert.equal(reparsed.value.from, header.from)
  assert.equal(reparsed.value.to, header.to)
  assert.equal(reparsed.value.id, header.id)
  assert.equal(reparsed.value.version, header.version)
  assert.equal(reparsed.value.lang, header.lang)
})

// ---- featuresFor: the RFC 6120 ordering, as observable behaviour ------

test('featuresFor(preTls): required STARTTLS, no SASL, no bind', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  const result = await featuresFor('preTls', ['SCRAM-SHA-256'], { engine: eng })
  assert.equal(result.ok, true)
  assert.equal(result.value.startTlsRequired, 'required')
  assert.deepEqual(result.value.saslMechanisms, [])
  assert.equal(result.value.canBind, false)
})

test('featuresFor(postTls): the given mechanisms, no STARTTLS, no bind', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  const result = await featuresFor('postTls', ['SCRAM-SHA-256', 'PLAIN'], { engine: eng })
  assert.equal(result.ok, true)
  assert.equal(result.value.startTlsRequired, null)
  assert.deepEqual(result.value.saslMechanisms, ['SCRAM-SHA-256', 'PLAIN'])
  assert.equal(result.value.canBind, false)
  assert.match(result.value.xml, /<mechanism>SCRAM-SHA-256<\/mechanism>/)
})

test('featuresFor(authenticated): bind and session, nothing else', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  const result = await featuresFor('authenticated', [], { engine: eng })
  assert.equal(result.ok, true)
  assert.equal(result.value.startTlsRequired, null)
  assert.deepEqual(result.value.saslMechanisms, [])
  assert.equal(result.value.canBind, true)
  assert.equal(result.value.canSession, true)
})

test('featuresFor: an unknown stage name is rejected, not silently defaulted', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  const result = await featuresFor('notAStage', [], { engine: eng })
  assert.equal(result.ok, false)
})

// ---- parseStanza -------------------------------------------------------

test('parseStanza: a message stanza with a body', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  const xml = '<message from="romeo@example.net/orchard" to="juliet@example.com/balcony" ' +
    'type="chat" id="m1"><body>Art thou not Romeo?</body></message>'
  const result = await parseStanza(xml, { engine: eng })
  assert.equal(result.ok, true)
  assert.deepEqual(result.value, {
    kind: 'message',
    id: 'm1',
    from: 'romeo@example.net/orchard',
    to: 'juliet@example.com/balcony',
    type: 'chat',
    payloadXml: '<body>Art thou not Romeo?</body>'
  })
})

test('parseStanza: bare presence', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  const result = await parseStanza('<presence/>', { engine: eng })
  assert.equal(result.ok, true)
  assert.equal(result.value.kind, 'presence')
  assert.equal(result.value.payloadXml, '')
})

test('parseStanza: an iq with a nested query element preserves its xmlns', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  const xml = '<iq type="get" id="q1" to="example.com"><query xmlns="jabber:iq:roster"/></iq>'
  const result = await parseStanza(xml, { engine: eng })
  assert.equal(result.ok, true)
  assert.equal(result.value.kind, 'iq')
  assert.equal(result.value.payloadXml, '<query xmlns="jabber:iq:roster"/>')
})

test('parseStanza: a stanza with a structurally bad "from" JID is rejected', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  const result = await parseStanza('<message from="a@"><body>hi</body></message>', { engine: eng })
  assert.equal(result.ok, false)
})

test('parseStanza: a non-stanza top-level element (e.g. stream:features) is rejected', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  const result = await parseStanza('<stream:features/>', { engine: eng })
  assert.equal(result.ok, false)
})

// ---- adversarial: none of these should hang or crash the process -----

test('adversarial: a huge run of unmatched "<" fails cleanly and promptly', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  const result = await parseStreamHeader('<'.repeat(100000), { engine: eng })
  assert.equal(result.ok, false)
})

test('adversarial: 1,000 chained "&amp;" entities in a stanza body parse promptly', async (t) => {
  if (await skipUnlessAvailable(t)) return
  const eng = await engine()
  // NOT a round number picked for looks: 1,000 is the last count confirmed
  // to pass. Bisected 2026-09-07: 500 and 1,000 pass; 2,000 and 5,000 throw
  // "Maximum call stack size exceeded" from the SHARED L4Factoidal.XML
  // entity-expansion recursion (not code this package owns), which is
  // apparently not tail-recursive over a run of sequential entity
  // references. Real finding, not swept under the rug — see
  // formal/lean4/L4Factoidal/XMPP/README.md's "known upstream limits" note.
  const body = '&amp;'.repeat(1000)
  const result = await parseStanza(`<message><body>${body}</body></message>`, { engine: eng })
  assert.equal(result.ok, true)
})

// Expected failures (owner rule, 2026-09-07): a stated shortfall is a
// failing test plus an open issue. `xfail` runs the check; if it throws, the
// case is an expected failure naming the issue; if it PASSES, the case FAILS,
// so the flip to a real assertion and the issue closure cannot be forgotten.
function xfail (name, issueUrl, fn) {
  test(`xfail: ${name} (${issueUrl})`, async (t) => {
    let failed = false
    try { await fn(t) } catch (error) { failed = true; t.diagnostic(`expected failure: ${String(error.message).slice(0, 160)}`) }
    assert.ok(failed, `unexpected pass: ${name} now works — flip this xfail to an assertion and close ${issueUrl}`)
  })
}

const PRECIS_ISSUE = 'https://github.com/danbri/factoidal/issues/676'

xfail('parseJid rejects a localpart with a PRECIS-disallowed codepoint (U+00A0 NO-BREAK SPACE, RFC 8265 §3.3)', PRECIS_ISSUE, async () => {
  const r = await parseJid('juliet\u00A0capulet@example.com')
  assert.equal(r.ok, false, 'a disallowed codepoint must be rejected under PRECIS UsernameCaseMapped')
})

xfail('parseJid normalizes a non-NFC localpart (RFC 8265 §3.3 normalization rule)', PRECIS_ISSUE, async () => {
  const r = await parseJid('juli\u0065\u0301t@example.com')
  assert.equal(r.ok, true)
  assert.equal(r.value.localpart, 'juli\u00e9t', 'NFC form expected after PRECIS enforcement')
})
