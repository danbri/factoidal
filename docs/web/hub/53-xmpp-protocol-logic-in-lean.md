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
stream-header and `<stream:features>` negotiation, and stanza parsing.
There is no socket layer and no GC3 yet — see "What this isn't, yet"
at the end.

## JIDs (RFC 7622)

`fn.l4Call("xmppJidParse", [jid])` parses the
`[ localpart "@" ] domainpart [ "/" resourcepart ]` grammar. Structural
and length well-formedness only — PRECIS enforcement (Unicode
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

## Configuration — the planned shape (not yet implemented)

There is no running server yet: the pieces above are protocol *logic*
— pure functions over strings — with no socket, TLS, or process
lifecycle around them. Marked plainly as planned, dated 2026-09-07, so
it doesn't quietly rot into a claim: the intended shape, per the
[design record](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/XMPP/README.md),
is a fresh Erlang/Elixir (BEAM) supervision tree — chosen for
per-connection process isolation and preemptive scheduling, not
reused from any existing server — calling this Lean-compiled wasm core
through a NIF, with configuration read from **either** a settings
file **or** CLI flags, e.g.:

```toml
# xmpp.toml (planned)
[server]
domain = "example.com"
c2s_port = 5222
s2s_port = 5269

[tls]
cert = "/etc/xmpp/cert.pem"
key = "/etc/xmpp/key.pem"
require_before_auth = true   # STARTTLS before SASL, per RFC 6120 §5.4.1

[sasl]
mechanisms = ["SCRAM-SHA-256"]
```

```
# equivalent CLI flags (planned)
xmpp-lean --domain example.com --c2s-port 5222 --s2s-port 5269 \
          --tls-cert /etc/xmpp/cert.pem --tls-key /etc/xmpp/key.pem \
          --sasl-mechanisms SCRAM-SHA-256
```

Whichever settings surface lands, `xmppFeaturesFor` above is what would
compute the actual `<stream:features>` offered at each stage from these
values — the config format is new work, the negotiation logic it would
drive already exists and is proved, which is why it's demonstrated live
above rather than only described.

## What this isn't, yet

- No socket/TLS layer, no running server (see "Configuration" above).
- No GC3 — still an early-stage, unfinished upstream XSF spec.
- No SASL/SCRAM *computation* — the message format exists on the Lean
  side; the hash/HMAC binding to the project's HACL* FFI doesn't yet.
- No MUC/MIX interop modules.
- `parseStanza` has no inverse for reconstructing a stanza's payload
  from JSON — payload children come back as one serialized XML string.

Full status, the license policy, and the reasoning behind each design
choice (why GC3 and not MIX, why MLS and not OMEMO for any future
group encryption, why a fresh implementation rather than building on
Prosody/ejabberd/MongooseIM): the
[design record](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/XMPP/README.md).
