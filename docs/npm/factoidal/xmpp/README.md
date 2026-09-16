# `@factoidal/core/xmpp`

A functional-programming-style JavaScript API over `L4Factoidal.XMPP`
(Lean 4, compiled to WebAssembly) — the fresh, GC3-targeting XMPP
implementation described in
[`formal/lean4/L4Factoidal/XMPP/README.md`](../../../formal/lean4/L4Factoidal/XMPP/README.md).

```js
import { parseJid, parseStreamHeader, featuresFor, parseStanza } from '@factoidal/core/xmpp'

const jid = await parseJid('romeo@example.net/orchard')
// { ok: true, value: { localpart: 'romeo', domainpart: 'example.net',
//                       resourcepart: 'orchard', wellFormed: true } }

const bad = await parseJid('@example.com')
// { ok: false, error: 'not a structurally valid JID: @example.com', unknownOp: false }

const features = await featuresFor('postTls', ['SCRAM-SHA-256', 'PLAIN'])
// { ok: true, value: { startTlsRequired: null,
//                       saslMechanisms: ['SCRAM-SHA-256', 'PLAIN'],
//                       canBind: false, canSession: false,
//                       xml: '<stream:features>...</stream:features>' } }
```

## Design: functions in, results out, nothing thrown for an expected outcome

Every function here is pure: plain data in, plain data out, no classes,
nothing to construct or hold onto. A malformed JID, a stanza that isn't
`message`/`presence`/`iq`, an unknown negotiation stage — these are
**ordinary answers**, not exceptional control flow, so every function
returns

```ts
{ ok: true, value: T } | { ok: false, error: string, unknownOp: boolean }
```

rather than throwing. The one thing that still throws is a genuine
host/environment failure — the wasm module not being resolvable or
loadable at all (`loadXmppEngine()`), which is not a protocol-level
outcome and has no sensible data shape to return instead.

## API

| Function | Wraps op | Notes |
|---|---|---|
| `parseJid(jid, options?)` | `xmppJidParse` | RFC 7622 structural + length well-formedness; PRECIS not yet enforced (see below) |
| `renderJid(parts, options?)` | `xmppJidRender` | `{localpart?, domainpart, resourcepart?}` → string |
| `parseStreamHeader(xml, options?)` | `xmppStreamHeaderParse` | tolerates a leading `<?xml ...?>` declaration |
| `renderStreamHeader(header, options?)` | `xmppStreamHeaderRender` | inverse |
| `featuresFor(stage, mechanisms?, options?)` | `xmppFeaturesFor` | `stage` is one of `preTls`/`postTls`/`authenticated`/`bound` |
| `parseStanza(xml, options?)` | `xmppStanzaParse` | `message`/`presence`/`iq` only; payload children come back as one serialized `payloadXml` string, not a tree |

Every function accepts an optional `{ engine }` in its last argument to
reuse an already-loaded engine handle (`await loadXmppEngine()`) instead
of paying the load cost per call — see `loadXmppEngine()`'s doc comment.

`xmppOpsAvailable(options?)` reports whether the resolved wasm module
carries these ops at all, so a caller (or a test) can skip gracefully
against an older committed bundle instead of getting a confusing
"unknown op" error.

## What this does not cover yet, on purpose

- **Stanza construction from JSON.** `parseStanza` has no inverse: building
  a stanza's XML back from a JSON payload description needs a
  sibling-node XML constructor the Lean side doesn't have yet.
- **GC3 itself.** Still an unfinished, early-stage upstream XSF spec —
  see the design record.
- **SASL/SCRAM computation.** The message *format* exists on the Lean
  side (`L4Factoidal.XMPP.Sasl`); the actual hash/HMAC computation
  doesn't yet (no HACL* HMAC-SHA-256 binding — see the design record's
  crypto section).
- **MUC/MIX interop modules.**

## Known upstream limit (found via this module's tests, 2026-09-07)

`parseStanza`/`parseStreamHeader` delegate general XML parsing to the
shared `L4Factoidal.XML` module (reused rather than duplicated — see
the design record). Its entity-expansion handling is not tail-recursive
over a run of *sequential* entity references in one text node: a text
body with roughly 2,000+ consecutive entity references (e.g.
`"&amp;".repeat(2000)`) overflows the wasm call stack
(`Maximum call stack size exceeded`), while ~1,000 passes reliably. This
is a limitation of the shared parser, not of this wrapper — filed here
rather than silently worked around by reverting to a bespoke parser,
which would reintroduce the duplication this module was written to
avoid. `test/xmpp.test.mjs`'s adversarial case is pinned at 1,000 for
exactly this reason.

## Testing

```bash
cd npm/factoidal
node --test test/xmpp.test.mjs
```

Skips wholesale when the Lean wasm assets aren't resolvable, and skips
per-op when the resolved bundle predates a given op (see
`xmppOpsAvailable`) — the same pattern `test/l4-core.test.js` uses.
