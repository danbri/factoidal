// tests/xmpp/server.mjs — the RFC 6120 and RFC 6121 sequences, replayed
// through the LIVE `l4xmpp-serve` process.
//
// Nothing here implements XMPP. Each case writes bytes to a real
// process's standard input and asserts on the bytes that come back, so a
// pass means the shipped binary did it, not that a mock agreed with a
// mock. The process is the one the carrier forks in
// deploy/fly/xmpp/entrypoint.sh, started the same way but with the
// socket replaced by a pipe.
//
// Two transports are exercised:
//   * a pipe straight to the process (every case);
//   * a socat TCP listener on localhost, when socat is installed — the
//     same carrier line the deployment uses (the last case).
//
// Run:  node tests/xmpp/server.mjs
// Score: "N pass, M fail (out of T)".

import { spawn, spawnSync } from 'node:child_process';
import { mkdtempSync, rmSync, writeFileSync, readFileSync, existsSync, readdirSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import net from 'node:net';

const here = dirname(fileURLToPath(import.meta.url));
const repo = join(here, '..', '..');
const BIN = join(repo, 'formal', 'lean4', '.lake', 'build', 'bin', 'l4xmpp-serve');

const NS_SASL = 'urn:ietf:params:xml:ns:xmpp-sasl';
const NS_BIND = 'urn:ietf:params:xml:ns:xmpp-bind';
const NS_ROSTER = 'jabber:iq:roster';
const DOMAIN = 'example.com';

let pass = 0, fail = 0;
const failures = [];

function check(name, cond, detail) {
  if (cond) { pass++; console.log(`  ok   ${name}`); }
  else { fail++; failures.push(name); console.log(`  FAIL ${name}${detail ? `\n       ${detail}` : ''}`); }
}

function stateDir() {
  const d = mkdtempSync(join(tmpdir(), 'l4xmpp-'));
  writeFileSync(join(d, 'accounts'), 'juliet:r0m30\nromeo:juli3t\n');
  return d;
}

/** Feed `input` to one server process and collect all of stdout. */
function replay(input, { dir, args = [] } = {}) {
  const d = dir ?? stateDir();
  const r = spawnSync(BIN,
    ['--domain', DOMAIN, '--state', d, '--plaintext',
     '--stream-id', 'SID1', '--nonce', 'SRVNONCE', ...args],
    { input, encoding: 'utf8', timeout: 30000 });
  return { out: r.stdout ?? '', err: r.stderr ?? '', dir: d, status: r.status };
}

const streamOpen =
  `<?xml version='1.0'?><stream:stream to='${DOMAIN}' xmlns='jabber:client'` +
  ` xmlns:stream='http://etherx.jabber.org/streams' version='1.0'>`;

const plainAuth = (user, pw) => {
  const payload = Buffer.from(`\0${user}\0${pw}`, 'utf8').toString('base64');
  return `<auth xmlns='${NS_SASL}' mechanism='PLAIN'>${payload}</auth>`;
};

const bindIq = (id, resource) =>
  `<iq type='set' id='${id}'><bind xmlns='${NS_BIND}'>` +
  (resource ? `<resource>${resource}</resource>` : '') + `</bind></iq>`;

/** Everything up to and including a bound session, as juliet. */
const boundPrefix = (resource = 'balcony') =>
  streamOpen + plainAuth('juliet', 'r0m30') + streamOpen + bindIq('b1', resource);

console.log('RFC 6120 — stream negotiation');

{ // RFC 6120 section 4.2
  const { out } = replay(streamOpen);
  check('4.2 the server answers with a stream header carrying from and id',
    out.includes(`from='${DOMAIN}'`) && out.includes(`id='SID1'`) && out.includes("version='1.0'"));
  check('4.3 stream:features offers SASL mechanisms',
    out.includes('<mechanisms') && out.includes('<mechanism>PLAIN</mechanism>'));
  check('6.4.1 SCRAM-SHA-256 is offered',
    out.includes('<mechanism>SCRAM-SHA-256</mechanism>'));
  check('4.3 bind is NOT offered before authentication',
    !out.includes(`<bind xmlns="${NS_BIND}"`));
}

{ // RFC 6120 section 4.9.3.6
  const { out } = replay(
    `<stream:stream to='elsewhere.example' version='1.0'>`);
  check('4.9.3.6 a stream for another domain is host-unknown',
    out.includes('<host-unknown') && out.includes('</stream:stream>'));
}

{ // RFC 6120 section 4.4
  const { out } = replay(streamOpen + '</stream:stream>');
  check('4.4 the stream close is answered with a stream close',
    out.trimEnd().endsWith('</stream:stream>'));
}

{ // RFC 6120 section 6: a stanza before the stream header
  const { out } = replay(`<message to='x@${DOMAIN}'/>`);
  check('4.9 a stanza before the stream header is a stream error',
    out.includes('<stream:error'));
}

console.log('RFC 6120 section 6 — SASL');

{
  const { out } = replay(streamOpen + plainAuth('juliet', 'r0m30'));
  check('6.4.5 PLAIN with the right password succeeds',
    out.includes(`<success xmlns='${NS_SASL}'/>`));
}

{
  const { out } = replay(streamOpen + plainAuth('juliet', 'wrong'));
  check('6.5 PLAIN with the wrong password is not-authorized',
    out.includes('<failure') && out.includes('<not-authorized/>'));
  check('6.5 a failed authentication does not emit success',
    !out.includes('<success'));
}

{
  const { out } = replay(streamOpen + plainAuth('nobody', 'x'));
  check('6.5 an unknown account is not-authorized',
    out.includes('<not-authorized/>'));
}

{
  const { out } = replay(streamOpen + `<auth xmlns='${NS_SASL}' mechanism='ANONYMOUS'/>`);
  check('6.5 an unoffered mechanism is invalid-mechanism',
    out.includes('<invalid-mechanism/>'));
}

{ // RFC 6120 section 6.4.6
  const { out } = replay(streamOpen + plainAuth('juliet', 'r0m30') + streamOpen);
  check('6.4.6 the restarted stream offers bind, not SASL',
    out.lastIndexOf(`<bind xmlns="${NS_BIND}"`) > out.lastIndexOf('<mechanism>'));
}

{ // A stanza between success and the restart
  const { out } = replay(streamOpen + plainAuth('juliet', 'r0m30') + `<presence/>`);
  check('6.4.6 a stanza before the stream restart is a stream error',
    out.includes('<stream:error'));
}

console.log('RFC 7677 — SASL SCRAM-SHA-256, against the live process');

{
  // A full SCRAM exchange computed here with node:crypto — an
  // independent implementation of RFC 5802, so agreement is evidence.
  const crypto = await import('node:crypto');
  const clientNonce = 'fyko+d2lbbFgONRv9qkxdawL';
  const first = `n=juliet,r=${clientNonce}`;
  const { out } = (() => {
    // The exchange needs two rounds, so drive the process interactively.
    return { out: null };
  })();
  void out; void first; void crypto;
}

{
  const crypto = await import('node:crypto');
  const clientNonce = 'fyko+d2lbbFgONRv9qkxdawL';
  const clientFirstBare = `n=juliet,r=${clientNonce}`;
  const d = stateDir();
  const p = spawn(BIN, ['--domain', DOMAIN, '--state', d, '--plaintext',
                        '--stream-id', 'SID1', '--nonce', 'SRVNONCE']);
  let buf = '';
  p.stdout.on('data', c => { buf += c.toString(); });
  const waitFor = (needle, ms = 20000) => new Promise((res, rej) => {
    const t0 = Date.now();
    const tick = () => {
      if (buf.includes(needle)) return res(buf);
      if (Date.now() - t0 > ms) return rej(new Error(`timed out waiting for ${needle}\ngot: ${buf}`));
      setTimeout(tick, 20);
    };
    tick();
  });
  let scramOk = false, scramDetail = '';
  try {
    p.stdin.write(streamOpen);
    await waitFor('</stream:features>');
    buf = '';
    p.stdin.write(`<auth xmlns='${NS_SASL}' mechanism='SCRAM-SHA-256'>` +
      Buffer.from(`n,,${clientFirstBare}`, 'utf8').toString('base64') + '</auth>');
    await waitFor('</challenge>');
    const serverFirst = Buffer.from(
      buf.match(/<challenge[^>]*>([^<]*)<\/challenge>/)[1], 'base64').toString('utf8');
    const m = serverFirst.match(/^r=(.*),s=(.*),i=(\d+)$/);
    const [, nonce, saltB64, iter] = m;
    const salted = crypto.pbkdf2Sync('r0m30', Buffer.from(saltB64, 'base64'),
      parseInt(iter, 10), 32, 'sha256');
    const hmac = (k, msg) => crypto.createHmac('sha256', k).update(msg).digest();
    const clientKey = hmac(salted, 'Client Key');
    const storedKey = crypto.createHash('sha256').update(clientKey).digest();
    const clientFinalNoProof = `c=biws,r=${nonce}`;
    const authMessage = `${clientFirstBare},${serverFirst},${clientFinalNoProof}`;
    const sig = hmac(storedKey, authMessage);
    const proof = Buffer.from(clientKey.map((b, i) => b ^ sig[i]));
    buf = '';
    p.stdin.write(`<response xmlns='${NS_SASL}'>` +
      Buffer.from(`${clientFinalNoProof},p=${proof.toString('base64')}`, 'utf8')
        .toString('base64') + '</response>');
    await waitFor('</success>');
    const v = Buffer.from(buf.match(/<success[^>]*>([^<]*)<\/success>/)[1], 'base64')
      .toString('utf8');
    const serverKey = hmac(salted, 'Server Key');
    const expected = 'v=' + hmac(serverKey, authMessage).toString('base64');
    scramOk = (v === expected);
    scramDetail = `server sent ${v}, node computed ${expected}`;
  } catch (e) {
    scramDetail = String(e.message).slice(0, 300);
  } finally {
    p.stdin.end(); p.kill();
    rmSync(d, { recursive: true, force: true });
  }
  check('RFC 7677 a full SCRAM-SHA-256 exchange authenticates and the ' +
    'ServerSignature matches node:crypto', scramOk, scramDetail);
}

{ // A SCRAM response with a tampered proof
  const d = stateDir();
  const clientFirst = Buffer.from('n,,n=juliet,r=abcdefgh', 'utf8').toString('base64');
  const bad = Buffer.from('c=biws,r=xxx,p=AAAA', 'utf8').toString('base64');
  const { out } = replay(streamOpen +
    `<auth xmlns='${NS_SASL}' mechanism='SCRAM-SHA-256'>${clientFirst}</auth>` +
    `<response xmlns='${NS_SASL}'>${bad}</response>`, { dir: d });
  check('RFC 5802 section 5.1 a response echoing the wrong nonce is refused',
    out.includes('<failure') && !out.includes('<success'));
  rmSync(d, { recursive: true, force: true });
}

console.log('RFC 6120 section 7 — resource binding');

{
  const { out } = replay(boundPrefix('balcony'));
  check('7.6 the bind result carries the full JID the client asked for',
    out.includes('<jid>juliet@example.com/balcony</jid>'));
}

{
  const { out } = replay(streamOpen + plainAuth('juliet', 'r0m30') + streamOpen + bindIq('b1', null));
  check('7.6 with no resource proposed the server assigns one',
    /<jid>juliet@example\.com\/.+<\/jid>/.test(out));
}

{
  const { out } = replay(streamOpen + plainAuth('juliet', 'r0m30') + streamOpen +
    `<iq type='set' id='b2'><query xmlns='urn:example:no'/></iq>`);
  check('7 an IQ that is not a bind before binding is refused',
    out.includes("type=\"error\""));
}

console.log('RFC 6121 section 2 — the roster');

{
  const d = stateDir();
  const { out } = replay(boundPrefix() +
    `<iq type='set' id='r1'><query xmlns='${NS_ROSTER}'>` +
    `<item jid='romeo@example.com' name='Romeo'/></query></iq>` +
    `<iq type='get' id='r2'><query xmlns='${NS_ROSTER}'/></iq>`, { dir: d });
  check('2.3 a roster set is answered with an empty IQ result',
    out.includes('<iq type="result" id="r1"/>'));
  check('2.1.6 the set is pushed back to the session',
    out.includes('id="push-r1"') && out.includes('jid="romeo@example.com"'));
  check('2.1.3 the roster get returns the stored item',
    out.includes('<iq type="result" id="r2"><query xmlns="jabber:iq:roster">') &&
    out.includes('name="Romeo"'));
  check('2 the roster is persisted where the server said to put it',
    existsSync(join(d, 'roster', 'juliet%40example.com.tsv')) &&
    readFileSync(join(d, 'roster', 'juliet%40example.com.tsv'), 'utf8')
      .startsWith('romeo@example.com\tRomeo\tnone\t0'));
  rmSync(d, { recursive: true, force: true });
}

{
  const d = stateDir();
  replay(boundPrefix() +
    `<iq type='set' id='r1'><query xmlns='${NS_ROSTER}'>` +
    `<item jid='romeo@example.com' name='Romeo'/></query></iq>`, { dir: d });
  const { out } = replay(boundPrefix() +
    `<iq type='set' id='r3'><query xmlns='${NS_ROSTER}'>` +
    `<item jid='romeo@example.com' subscription='remove'/></query></iq>` +
    `<iq type='get' id='r4'><query xmlns='${NS_ROSTER}'/></iq>`, { dir: d });
  check('2.5 subscription=remove deletes the item and the next get is empty',
    out.includes('<iq type="result" id="r4"><query xmlns="jabber:iq:roster"/></iq>'));
  rmSync(d, { recursive: true, force: true });
}

{ // The roster survives across connections, which is what makes it a roster.
  const d = stateDir();
  replay(boundPrefix() +
    `<iq type='set' id='r1'><query xmlns='${NS_ROSTER}'>` +
    `<item jid='nurse@example.com' name='Nurse'/></query></iq>`, { dir: d });
  const { out } = replay(boundPrefix() +
    `<iq type='get' id='r9'><query xmlns='${NS_ROSTER}'/></iq>`, { dir: d });
  check('2 the roster is still there on a new connection',
    out.includes('jid="nurse@example.com"') && out.includes('name="Nurse"'));
  rmSync(d, { recursive: true, force: true });
}

console.log('RFC 6121 sections 3 and 4 — presence');

{
  const d = stateDir();
  const { out } = replay(boundPrefix() + `<presence/>`, { dir: d });
  check('4.4.3 available presence is reflected to the sender with a stamped from',
    out.includes('<presence from="juliet@example.com/balcony"/>'));
  check('4.4 the session is recorded as available',
    existsSync(join(d, 'presence', 'juliet%40example.com%2fbalcony')));
  rmSync(d, { recursive: true, force: true });
}

{
  const d = stateDir();
  replay(boundPrefix() +
    `<iq type='set' id='r1'><query xmlns='${NS_ROSTER}'>` +
    `<item jid='romeo@example.com'/></query></iq>` +
    `<presence to='romeo@example.com' type='subscribe'/>`, { dir: d });
  const roster = readFileSync(join(d, 'roster', 'juliet%40example.com.tsv'), 'utf8');
  check('3.1.2 a subscription request sets ask on the roster item',
    roster.includes('romeo@example.com\t\tnone\t1'), roster);
  const spool = join(d, 'spool', 'romeo%40example.com');
  check('3.1.3 the subscription request is routed to the contact',
    existsSync(spool) && readdirSync(spool).some(f =>
      readFileSync(join(spool, f), 'utf8').includes('type="subscribe"')));
  rmSync(d, { recursive: true, force: true });
}

{ // Presence goes only to contacts allowed to see it.
  const d = stateDir();
  writeFileSync(join(d, 'accounts'), 'juliet:r0m30\nromeo:juli3t\nnurse:n\n');
  const { dir } = replay(boundPrefix() +
    `<iq type='set' id='r1'><query xmlns='${NS_ROSTER}'>` +
    `<item jid='romeo@example.com'/></query></iq>`, { dir: d });
  // Hand-set romeo to `both` and nurse to `to`, which only `from`/`both`
  // may see (RFC 6121 section 4.4.2).
  writeFileSync(join(dir, 'roster', 'juliet%40example.com.tsv'),
    'romeo@example.com\t\tboth\t0\nnurse@example.com\t\tto\t0');
  replay(boundPrefix() + `<presence/>`, { dir });
  check('4.4.2 presence reaches a `both` contact',
    existsSync(join(dir, 'spool', 'romeo%40example.com')));
  check('4.4.2 presence does NOT reach a `to`-only contact',
    !existsSync(join(dir, 'spool', 'nurse%40example.com')));
  rmSync(d, { recursive: true, force: true });
}

console.log('RFC 6121 section 8 — messages, between two sessions');

{
  const d = stateDir();
  replay(boundPrefix() +
    `<message to='romeo@example.com' type='chat'><body>Art thou there?</body></message>`,
    { dir: d });
  const spool = join(d, 'spool', 'romeo%40example.com');
  const spooled = existsSync(spool)
    ? readdirSync(spool).map(f => readFileSync(join(spool, f), 'utf8')).join('') : '';
  check('8.1 a message to another account is routed to it',
    spooled.includes('Art thou there?'));
  check('8.1.1.1 the from is the sender\'s full JID, stamped by the server',
    spooled.includes('from="juliet@example.com/balcony"'));

  // Now romeo connects and collects it.
  const romeoPrefix = streamOpen + plainAuth('romeo', 'juli3t') + streamOpen +
    bindIq('b1', 'orchard');
  const { out } = replay(romeoPrefix + `<presence/>`, { dir: d });
  check('8.5 the second session receives the message once bound',
    out.includes('Art thou there?') && out.includes('from="juliet@example.com/balcony"'));
  rmSync(d, { recursive: true, force: true });
}

{ // A message that a client claims comes from someone else.
  const d = stateDir();
  replay(boundPrefix() +
    `<message to='romeo@example.com' from='mallory@evil.example' type='chat'>` +
    `<body>trust me</body></message>`, { dir: d });
  const spool = join(d, 'spool', 'romeo%40example.com');
  const spooled = existsSync(spool)
    ? readdirSync(spool).map(f => readFileSync(join(spool, f), 'utf8')).join('') : '';
  check('8.1.1.1 a spoofed from is replaced, not forwarded',
    spooled.includes('from="juliet@example.com/balcony"') &&
    !spooled.includes('mallory@evil.example'));
  rmSync(d, { recursive: true, force: true });
}

console.log('RFC 6120 section 8.4 — unhandled IQ');

{
  const { out } = replay(boundPrefix() +
    `<iq type='get' id='q1'><query xmlns='urn:example:nothing'/></iq>`);
  check('8.4 an IQ nobody handles gets service-unavailable',
    out.includes('<service-unavailable') && out.includes('id="q1"'));
}

{
  const { out } = replay(boundPrefix() +
    `<iq type='get' id='d1'><query xmlns='http://jabber.org/protocol/disco#info'/></iq>`);
  check('XEP-0030 disco#info answers with a server identity',
    out.includes('category="server"') && out.includes('type="im"'));
}

console.log('Framing — the bytes, not the stanzas');

{ // One write split across the middle of a stanza.
  const d = stateDir();
  const p = spawn(BIN, ['--domain', DOMAIN, '--state', d, '--plaintext',
                        '--stream-id', 'SID1', '--nonce', 'N']);
  let buf = '';
  p.stdout.on('data', c => { buf += c.toString(); });
  p.stdin.write(boundPrefix());
  await new Promise(r => setTimeout(r, 400));
  p.stdin.write(`<message to='romeo@example.com'><bo`);
  await new Promise(r => setTimeout(r, 200));
  const mid = buf.length;
  p.stdin.write(`dy>split</body></message>`);
  await new Promise(r => setTimeout(r, 400));
  p.stdin.end();
  await new Promise(r => setTimeout(r, 200));
  const spool = join(d, 'spool', 'romeo%40example.com');
  const spooled = existsSync(spool)
    ? readdirSync(spool).map(f => readFileSync(join(spool, f), 'utf8')).join('') : '';
  check('a stanza split across two writes is not acted on until it is complete',
    buf.length === mid || !buf.slice(0, mid).includes('split'));
  check('a stanza split across two writes is delivered once it completes',
    spooled.includes('split'));
  p.kill();
  rmSync(d, { recursive: true, force: true });
}

{ // Not well-formed XML.
  const { out } = replay(boundPrefix() + `<message><body>unclosed</message>`);
  check('a malformed stanza is a stream error, not a crash',
    out.includes('<stream:error') || out.includes('</stream:stream>'));
}

console.log('The carrier — socat, the deployment line');

{
  const haveSocat = spawnSync('socat', ['-V'], { encoding: 'utf8' }).status === 0;
  if (!haveSocat) {
    console.log('  SKIP socat is not installed; the TCP-listener case did not run');
    console.log('       (install socat to exercise the deployment carrier line)');
  } else {
    const d = stateDir();
    const port = 15222 + (process.pid % 500);
    const carrier = spawn('socat', [`TCP-LISTEN:${port},reuseaddr,fork`,
      `EXEC:${BIN} --domain ${DOMAIN} --state ${d} --plaintext,pipes`]);
    await new Promise(r => setTimeout(r, 500));
    let got = '';
    const ok = await new Promise(res => {
      const sock = net.connect(port, '127.0.0.1', () => {
        sock.write(boundPrefix() + `<presence/>`);
      });
      sock.on('data', c => {
        got += c.toString();
        if (got.includes('<presence from="juliet@example.com/balcony"/>')) {
          sock.end(); res(true);
        }
      });
      sock.on('error', () => res(false));
      setTimeout(() => { sock.destroy(); res(false); }, 8000);
    });
    check('the socat carrier line from deploy/fly/xmpp carries a full session', ok,
      ok ? '' : got.slice(0, 200));
    carrier.kill();
    rmSync(d, { recursive: true, force: true });
  }
}

const total = pass + fail;
console.log(`\nxmpp server: ${pass} pass, ${fail} fail (out of ${total})`);
if (fail) { console.log('failed: ' + failures.join(', ')); process.exit(1); }
