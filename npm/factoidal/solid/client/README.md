# `@factoidal/core/solid/client` — a `fetch` host for the Solid Protocol

The Solid Protocol v0.11.0 client conformance class
(<https://solidproject.org/TR/protocol>) over the platform `fetch`.

Tracking issue: <https://github.com/danbri/factoidal/issues/659>.
Design record:
[`docs/designissues/2026-09-06-lws-and-solid-protocols.md`](../../../../docs/designissues/2026-09-06-lws-and-solid-protocols.md).
Conformance ledger:
[`docs/lws-solid-conformance.md`](../../../../docs/lws-solid-conformance.md).

## What is here and what is not

`index.mjs` calls `solidClientRequest` to obtain a request record, puts
that record on the wire, and gives the reply to `solidClientResponse` to
be interpreted. Every request the client sends was built by the engine
and every response it reports was read by the engine.

This file composes no URL, sets no `Content-Type`, adds no `Slug`, reads
no `Link` header and parses no body. Discovery, request construction,
response interpretation and the WebID profile read are in
`formal/lean4/L4Factoidal/Solid/Client/`.

It shares no code with the server host beyond the engine loader.

## The wasm contract

| op | arguments | answer |
| --- | --- | --- |
| `solidClientRequest` | `[kind, argsJson]` | `{ ok, request }` |
| `solidClientResponse` | `[kind, responseJson]` | `{ ok, interpretation }` |

The two operations take different kind vocabularies and this host keeps
them apart rather than deriving one from the other:

* request kinds — `read`, `create`, `replace`, `patch`, `delete`,
  `discoverStorage`, `readProfile`;
* interpretation kinds — `storage`, `containment`, `auxiliaries`,
  `profile`, `wacAllow`.

Which interpretation a reply wants is a protocol decision, so this file
never picks one. It uses the `interpret` member the request envelope
named, then the `interpret` the caller passed. With neither, the reply is
returned uninterpreted and `interpretation` is `null` — the raw record,
never a host reading of it.

A multi-step operation is a loop, not a special case. An interpretation
that answers `{ continue: true, state }` sends the state back into the
next `solidClientRequest`; walking from a resource up to its storage root
is the case that needs it. A single-request operation runs the loop once.
The loop is capped (`maxSteps`, default 16) so a state that never settles
is a reported failure rather than a hang.

The full contract is `docs/lws-solid-conformance.md`, section "wasm ABI".

## Use

```js
import { createSolidClient } from '@factoidal/core/solid/client'

const client = await createSolidClient({ baseIri: 'https://pod.example/' })
const storage = await client.discoverStorage('/alice/notes/one')
await client.replace('/alice/notes/one', '<#a> <#b> <#c> .', 'text/turtle')
const read = await client.read('/alice/notes/one')
await client.delete('/alice/notes/one')
```

```
factoidal solid-client get https://pod.example/alice/notes/one
factoidal solid-client put https://pod.example/alice/notes/one \
  --file note.ttl --content-type text/turtle
factoidal solid-client discover https://pod.example/alice/notes/one
```

## Exports

| name | what it is |
| --- | --- |
| `createSolidClient(options)` | a client bound to one engine and one `fetch` |
| `solidClientOpsAvailable(engine)` | probe the loaded module for the ops |
| `SOLID_CLIENT_OPS` | the two op names |
| `SOLID_REQUEST_KINDS` | the seven request kinds the ABI names |
| `SOLID_INTERPRETATION_KINDS` | the five interpretation kinds |
| `SolidClientHostError` | a host failure, with `unknownOp` |

`options.fetch` replaces the platform `fetch`, which is how a test drives
the client at an in-process server without a proxy. `options.baseIri`
says where to send a request whose target the engine wrote as a path;
an absolute target is used verbatim.

The command's five verbs are aliases for the request kinds — `get`→`read`,
`put`→`replace`, `post`→`create`, `delete`→`delete`,
`discover`→`discoverStorage` — and a kind name is accepted directly.

## Tests and interop

```
node tests/solid/client/against-own-server.mjs   # against our own server
bash tools/solid-client-interop.sh               # against Community Solid Server
```
