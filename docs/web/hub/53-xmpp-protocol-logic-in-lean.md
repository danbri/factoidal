---
title: "XMPP, verified: JIDs, stream negotiation, and stanzas"
description: "The start of a fresh, GC3-targeting XMPP implementation in Lean 4 (L4Factoidal.XMPP): JID parsing, RFC 6120 stream negotiation with a proved ordering, and stanza parsing, live in the browser through the same dispatch ABI as the rest of the Lean engine."
layout: hub.njk
series: docs-hub
series_order: 53
vocab: none
status: published
tests: tests/hub/post53_test.mjs
---

Every other engine page in this series answers RDF/SPARQL questions.
This one is different: it's the first page for
[`L4Factoidal.XMPP`](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/XMPP/README.md),
a fresh XMPP implementation written to make
[GC3](https://matthewwild.co.uk/uploads/xmpp-gc3-jan-2025.pdf) — the
XMPP Standards Foundation's early-stage MUC/MIX successor — a
first-class, formally-checked citizen rather than a bolt-on. It reuses
the existing `L4Factoidal.XML` parser for the wire format instead of
duplicating it, and it's tested against a live ejabberd instance, not
just hand-written strings.

What's below is what exists **today**: RFC 7622 JID parsing, RFC 6120
stream-header and `<stream:features>` negotiation, and stanza parsing,
all live in the browser — and, since 2026-09-07, a running server that
speaks RFC 6120 and RFC 6121 over a real socket (see "The server"
below). GC3 is still absent — see "What this isn't, yet"
at the end.

## JIDs (RFC 7622)

`fn.l4Call("xmppJidParse", [jid])` parses the
`[ localpart "@" ] domainpart [ "/" resourcepart ]` grammar. Structural
and length well-formedness only — PRECIS enforcement (tracked as
<https://github.com/danbri/factoidal/issues/676> with expected-failure tests; Unicode
normalization, disallowed codepoints) isn't implemented yet, which the
Lean side's own module header states plainly rather than silently.

```observable-js
jidOk = fn.l4Call("xmppJidParse", ["romeo@example.net/orchard"])
```

An empty-but-present part is rejected, not silently dropped — this is a
[proved theorem](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/XMPP/Jid.lean)
on the Lean side (`parse_some_domain_nonempty` and its two companions),
not just this demo's behaviour.

```observable-js
jidBad = fn.l4Call("xmppJidParse", ["@example.com"]).catch((e) => ({ rejected: e.message }))
```

## Stream negotiation (RFC 6120)

`<stream:stream>` is never closed until the connection ends, so it
can't be parsed as an ordinary complete element — `xmppStreamHeaderParse`
handles the open tag on its own, and tolerates the leading
`<?xml version="1.0"?>` declaration real servers send. The example below
is a byte-for-byte capture from a live ejabberd instance (2026-09-07,
the `foafmixer` pilot container), not a hand-written string.

```observable-js
streamHeader = fn.l4Call("xmppStreamHeaderParse", [
  `<?xml version='1.0'?><stream:stream id='6532308259630420668' version='1.0' xml:lang='en' xmlns:stream='http://etherx.jabber.org/streams' from='foafmixer.test' xmlns='jabber:client'>`,
])
```

`xmppFeaturesFor` computes what a server should offer at a given
negotiation stage. The RFC 6120 ordering — STARTTLS only before TLS,
SASL mechanisms only after TLS but before authentication, resource
binding only once authenticated — is a
[proved `iff` theorem](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/XMPP/Core.lean)
on the Lean side for each stage, not a runtime check this demo could
happen to pass:

```observable-js
featuresPreTls = fn.l4Call("xmppFeaturesFor", [
  JSON.stringify({ stage: "preTls", mechanisms: ["SCRAM-SHA-256"] }),
])
```

```observable-js
featuresPostTls = fn.l4Call("xmppFeaturesFor", [
  JSON.stringify({ stage: "postTls", mechanisms: ["SCRAM-SHA-256", "PLAIN"] }),
])
```

Notice `featuresPreTls` never carries `saslMechanisms`, and
`featuresPostTls` never carries a STARTTLS offer — not because this
particular call happened to omit them, but because no value with both
exists to return.

## Stanzas

`xmppStanzaParse` handles `message`/`presence`/`iq`, with `from`/`to`
validated as real JIDs the same way the stream header is.

```observable-js
stanza = fn.l4Call("xmppStanzaParse", [
  `<message from="romeo@example.net/orchard" to="juliet@example.com/balcony" type="chat" id="m1"><body>Art thou not Romeo?</body></message>`,
])
```

A stanza whose top-level tag isn't one of the three is rejected — a
`<stream:features>` element, say, correctly doesn't parse as a stanza,
because stream negotiation is a different layer:

```observable-js
notAStanza = fn.l4Call("xmppStanzaParse", ["<stream:features/>"]).catch((e) => ({ rejected: e.message }))
```

## The server: `l4xmpp-serve`

There **is** a running server now. `lean_exe l4xmpp-serve` speaks
RFC 6120 and RFC 6121 on standard input and output for one connection,
and the carrier forks one process per connection. The whole non-Lean
part of the deployment is this command:

```
socat OPENSSL-LISTEN:5223,reuseaddr,fork,cert=/certs/fullchain.pem,key=/certs/privkey.pem,verify=0 \
  EXEC:/opt/factoidal/bin/l4xmpp-serve,pipes
```

socat accepts the connection and terminates TLS; it never reads the
stream. [XEP-0368](https://xmpp.org/extensions/xep-0368.html) (direct
TLS on port 5223) is what makes that a complete answer rather than a
partial one: with direct TLS there is no STARTTLS step for the
application to perform, so no TLS library is linked into the Lean
binary. No C, no JavaScript, no Erlang is involved in serving a
connection. The build files and the line count are in
[`deploy/fly/xmpp/`](https://github.com/danbri/factoidal/tree/claude/main/deploy/fly/xmpp).

### A real session, captured

This is not a browser simulation. It is the wire log of
[`@xmpp/client`](https://www.npmjs.com/package/@xmpp/client) — a
third-party XMPP library nobody here wrote — talking to `l4xmpp-serve`
through that socat line, captured by
[`tools/xmpp-interop.sh`](https://github.com/danbri/factoidal/blob/claude/main/tools/xmpp-interop.sh).
`C:` is the client, `S:` the server.

```
C: <?xml version='1.0'?><stream:stream version="1.0" xmlns="jabber:client"
     xmlns:stream="http://etherx.jabber.org/streams" to="localhost">

S: <?xml version='1.0'?><stream:stream xmlns='jabber:client'
     xmlns:stream='http://etherx.jabber.org/streams' from='localhost'
     id='s431823914549416' version='1.0' xml:lang='en'>
   <stream:features>
     <mechanisms xmlns="urn:ietf:params:xml:ns:xmpp-sasl">
       <mechanism>SCRAM-SHA-256</mechanism>
       <mechanism>PLAIN</mechanism>
     </mechanisms>
   </stream:features>

C: <auth xmlns="urn:ietf:params:xml:ns:xmpp-sasl"
     mechanism="PLAIN">AGp1bGlldAByMG0zMA==</auth>

S: <success xmlns='urn:ietf:params:xml:ns:xmpp-sasl'/>

C: <?xml version='1.0'?><stream:stream version="1.0" xmlns="jabber:client"
     xmlns:stream="http://etherx.jabber.org/streams" to="localhost">

S: <?xml version='1.0'?><stream:stream ... id='s431823914549416' ...>
   <stream:features>
     <bind xmlns="urn:ietf:params:xml:ns:xmpp-bind"/>
     <session xmlns="urn:ietf:params:xml:ns:xmpp-session"/>
   </stream:features>

C: <iq type="set" id="cuqx6m6v1y"><bind xmlns="urn:ietf:params:xml:ns:xmpp-bind">
     <resource>balcony</resource></bind></iq>

S: <iq type="result" id="cuqx6m6v1y"><bind xmlns="urn:ietf:params:xml:ns:xmpp-bind">
     <jid>juliet@localhost/balcony</jid></bind></iq>

C: <iq type="get" id="d7tkm39mn9"><query xmlns="jabber:iq:roster"/></iq>

S: <iq type="result" id="d7tkm39mn9"><query xmlns="jabber:iq:roster"/></iq>
```

Notice the second `<stream:features>`. It offers `bind` and no
mechanisms, and the first offers mechanisms and no `bind` — that is
`featuresFor` above, the function whose ordering the four theorems in
`Core.lean` pin. The negotiation the browser cells demonstrate is the
same code that produced these bytes.

### What it speaks

RFC 6120 sections 4.2, 4.4, 4.9 (stream errors), 6 (SASL PLAIN per
RFC 4616 and SCRAM-SHA-256 per RFC 7677, with the 6.4.6 stream
restart), 7 (resource binding), 8 and 8.4; RFC 6121 sections 2 (the
roster: get, set, push, remove, persisted across connections), 3
(presence subscription), 4 (presence broadcast to `from`/`both`
contacts) and 8 (message delivery between sessions, with the `from`
stamped by the server rather than trusted from the client); and a
minimal XEP-0030 `disco#info`.

Every one of those decisions is in
[`L4Factoidal/XMPP/Server.lean`](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/XMPP/Server.lean)
as one total function,

```
step : Session → Env → Framing.Unit → Session × Env × List Out
```

and the host that carries the bytes performs the `Out` actions without
deciding any of them. Even "may this session receive a stanza waiting
for it?" is asked of `Session.canDeliver` rather than answered by the
host — because a host that read and unlinked a stanza the server would
refuse has destroyed it, which is exactly what happened once before the
gate moved into Lean.

Scores, measured 2026-09-07: 41 pass, 0 fail (out of 41) for the RFC
sequences replayed through the live binary
([`tests/xmpp/server.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/xmpp/server.mjs)),
and 7 pass, 0 fail (out of 7) for the `@xmpp/client` interop over a
real socket.

## What this isn't, yet

- No GC3 — still an early-stage, unfinished upstream XSF spec.
  Implementing rooms would be inventing a wire format, not
  implementing one.
- No STARTTLS. The carrier holds TLS (XEP-0368 direct TLS), so
  RFC 6120 section 5 is not implemented in Lean, and neither is SCRAM
  channel binding — the process cannot see the TLS layer.
- No SCRAM-SHA-1. `Crypto/SHA1.lean` exists only as a codec for the
  SPARQL `SHA1()` builtin and its own header forbids using it for
  authentication. SCRAM-SHA-256 (RFC 7677) and PLAIN are what is
  offered.
- No server-to-server federation. One process, one client connection.
- Accounts are a plaintext file with one salt for all of them, and a
  SCRAM login therefore runs PBKDF2 per authentication rather than
  reading stored keys. `Scram.StoredCredentials` is already the right
  shape for the fix; the change is an account-file format, not a
  protocol change.
- Routing between connections is a directory of files, polled every
  50 ms. Inspectable, not fast. `Out.route` names a destination and a
  payload rather than a file, so a faster carrier replaces it without
  touching the protocol modules.
- No MUC/MIX interop modules.
- `parseStanza` has no inverse for reconstructing a stanza's payload
  from JSON — payload children come back as one serialized XML string.

Full status, the license policy, and the reasoning behind each design
choice (why GC3 and not MIX, why MLS and not OMEMO for any future
group encryption, why a fresh implementation rather than building on
Prosody/ejabberd/MongooseIM): the
[design record](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/XMPP/README.md).
