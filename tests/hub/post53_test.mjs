// Pins every live cell in docs/web/hub/53-xmpp-protocol-logic-in-lean.md.
//
// Harness shape follows tests/hub/post38_test.mjs: `fn` here is the
// node package's `l4Call` layered over the SAME on-disk loader the
// browser imports (docs/web/hub/assets/l4/l4factoidal.js). Skips
// wholesale when the XMPP ops aren't in the resolved wasm bundle, the
// same protection npm/factoidal/test/xmpp.test.mjs uses.

import test from 'node:test';
import assert from 'node:assert/strict';

import { extractObservableCells, runReactivePost, pretty } from './_helpers.mjs';

const L4_LOADER = new URL('../../docs/web/hub/assets/l4/l4factoidal.js', import.meta.url);
const { loadL4 } = await import(L4_LOADER.href);

let l4Promise = null;
const fn = {
  loadL4: () => (l4Promise ??= loadL4()),
  l4Call: async (op, args) => (await fn.loadL4()).call(op, args),
};

const POST_FILE = '53-xmpp-protocol-logic-in-lean.md';
const cells = extractObservableCells(POST_FILE);

async function xmppOpsAvailable() {
  const engine = await fn.loadL4();
  const names = engine.call('ops', []).ops;
  return ['xmppJidParse', 'xmppStreamHeaderParse', 'xmppFeaturesFor', 'xmppStanzaParse']
    .every((op) => names.includes(op));
}

test('post53: JID parsing, stream negotiation, and stanza cells', async (t) => {
  if (!(await xmppOpsAvailable())) {
    t.skip('resolved Lean wasm predates the XMPP ops; rebuild formal/lean4/Wasm/build-wasm.sh to unskip');
    return;
  }

  const post = runReactivePost(cells, { fn, pretty });

  const jidOk = await post.value('jidOk');
  assert.equal(jidOk.localpart, 'romeo');
  assert.equal(jidOk.domainpart, 'example.net');
  assert.equal(jidOk.resourcepart, 'orchard');
  assert.equal(jidOk.wellFormed, true);

  const jidBad = await post.value('jidBad');
  assert.match(jidBad.rejected, /not a structurally valid JID/);

  const streamHeader = await post.value('streamHeader');
  assert.equal(streamHeader.from, 'foafmixer.test');
  assert.equal(streamHeader.id, '6532308259630420668');
  assert.equal(streamHeader.version, '1.0');
  assert.equal(streamHeader.lang, 'en');
  assert.equal(streamHeader.rest, '');

  const featuresPreTls = await post.value('featuresPreTls');
  assert.equal(featuresPreTls.startTlsRequired, 'required');
  assert.deepEqual(featuresPreTls.saslMechanisms, []);
  assert.equal(featuresPreTls.canBind, false);

  const featuresPostTls = await post.value('featuresPostTls');
  assert.equal(featuresPostTls.startTlsRequired, null);
  assert.deepEqual(featuresPostTls.saslMechanisms, ['SCRAM-SHA-256', 'PLAIN']);
  assert.equal(featuresPostTls.canBind, false);

  const stanza = await post.value('stanza');
  assert.equal(stanza.kind, 'message');
  assert.equal(stanza.from, 'romeo@example.net/orchard');
  assert.equal(stanza.to, 'juliet@example.com/balcony');
  assert.equal(stanza.payloadXml, '<body>Art thou not Romeo?</body>');

  const notAStanza = await post.value('notAStanza');
  assert.match(notAStanza.rejected, /not a valid message\/presence\/iq stanza/);
});
