// tests/xmpp/interop-client.mjs — the Factoidal XMPP server driven by
// @xmpp/client, a third-party XMPP client library nobody here wrote.
//
// This is the point of the test: every other check in tests/xmpp/ is our
// bytes checked against our expectations. Here an independent
// implementation of RFC 6120 and RFC 6121 decides whether the server is
// speaking XMPP, and it fails if we have quietly invented a dialect.
//
// Launched by tools/xmpp-interop.sh, which starts the socat carrier and
// passes the port. Not run directly.
//
// Two sessions: juliet connects and authenticates, romeo connects and
// authenticates, juliet sends romeo a message, romeo receives it.

import { client, xml } from '@xmpp/client';

const port = Number(process.argv[2] ?? 15222);
const domain = process.argv[3] ?? 'localhost';
const service = `xmpp://127.0.0.1:${port}`;

let pass = 0, fail = 0;
const failures = [];
function check(name, cond, detail) {
  if (cond) { pass++; console.log(`  ok   ${name}`); }
  else { fail++; failures.push(name); console.log(`  FAIL ${name}${detail ? `\n       ${detail}` : ''}`); }
}

function connect(username, password, resource) {
  const c = client({
    service, domain, username, password, resource,
    // The carrier holds TLS (XEP-0368 direct TLS on 5223). This local
    // listener is plaintext, so STARTTLS must not be demanded.
    credentials: undefined,
  });
  c.on('error', e => { if (process.env.XMPP_DEBUG) console.log(`[${username} error] ${e.message}`); });
  if (process.env.XMPP_DEBUG) {
    c.on('input', d => console.log(`[${username} <<] ${d}`));
    c.on('output', d => console.log(`[${username} >>] ${d}`));
  }
  c.start().catch(e => {
    if (process.env.XMPP_DEBUG) console.log(`[${username} start] ${e.message}`);
  });
  return c;
}

const timeout = (ms, what) =>
  new Promise((_, rej) => setTimeout(() => rej(new Error(`timed out: ${what}`)), ms));

async function main() {
  let juliet, romeo;
  try {
    juliet = connect('juliet', 'r0m30', 'balcony');
    const julietJid = await Promise.race([
      new Promise(res => juliet.on('online', jid => res(jid))),
      timeout(15000, 'juliet online'),
    ]);
    check('@xmpp/client authenticates and binds against the Lean server',
      String(julietJid).startsWith('juliet@' + domain + '/'),
      `bound as ${julietJid}`);
    check('the resource the client asked for is the one it got',
      String(julietJid).endsWith('/balcony'), String(julietJid));

    // RFC 6121 section 2.1.3 — the roster, asked for by the library's
    // own IQ machinery rather than by a string we wrote.
    const rosterResult = await Promise.race([
      juliet.iqCaller.request(
        xml('iq', { type: 'get' }, xml('query', { xmlns: 'jabber:iq:roster' }))),
      timeout(15000, 'roster get'),
    ]);
    check('a roster get through the library returns an IQ result with a query',
      rosterResult.attrs.type === 'result' &&
      !!rosterResult.getChild('query', 'jabber:iq:roster'),
      rosterResult.toString().slice(0, 200));

    // RFC 6121 section 4 — presence.
    await juliet.send(xml('presence'));

    romeo = connect('romeo', 'juli3t', 'orchard');
    const romeoJid = await Promise.race([
      new Promise(res => romeo.on('online', jid => res(jid))),
      timeout(15000, 'romeo online'),
    ]);
    check('a second session authenticates and binds independently',
      String(romeoJid).startsWith('romeo@' + domain + '/'), String(romeoJid));

    const received = new Promise(res => {
      romeo.on('stanza', st => {
        if (st.is('message') && st.getChildText('body')) res(st);
      });
    });
    await romeo.send(xml('presence'));

    await juliet.send(xml('message',
      { to: `romeo@${domain}`, type: 'chat' },
      xml('body', {}, 'Wilt thou be gone? It is not yet near day.')));

    const msg = await Promise.race([received, timeout(20000, 'romeo receives the message')]);
    check('a message sent by one session reaches the other',
      msg.getChildText('body') === 'Wilt thou be gone? It is not yet near day.',
      msg.toString().slice(0, 200));
    check('the from the receiver sees is the sender\'s full JID',
      String(msg.attrs.from).startsWith(`juliet@${domain}/`), String(msg.attrs.from));

    // A wrong password must be refused, through the library's own SASL.
    const bad = connect('juliet', 'not-the-password', 'x');
    const refused = await Promise.race([
      new Promise(res => bad.on('error', () => res(true))),
      new Promise(res => bad.on('online', () => res(false))),
      timeout(15000, 'bad password refused').catch(() => true),
    ]);
    check('the library reports a refusal for the wrong password', refused === true);
    try { await bad.stop(); } catch { /* already down */ }
  } catch (e) {
    fail++; failures.push('exception');
    console.log(`  FAIL an exception ended the run\n       ${e.message}`);
  } finally {
    for (const c of [juliet, romeo]) {
      if (c) { try { await c.stop(); } catch { /* already down */ } }
    }
  }

  const total = pass + fail;
  console.log(`\nxmpp interop (@xmpp/client): ${pass} pass, ${fail} fail (out of ${total})`);
  if (fail) { console.log('failed: ' + failures.join(', ')); process.exit(1); }
  process.exit(0);
}

main();
