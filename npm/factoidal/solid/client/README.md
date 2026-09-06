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
| `solidClientRequest` | `[kind, argsJson]` | `{ ok, request }` or `{ ok, done: true, ... }` |
| `solidClientResponse` | `[kind, responseJson]` | `{ ok, ... }`, the operation's own shape |

`kind` is `discover`, `get`, `put`, `post`, `delete`, `patch` or
`profile`. A new kind needs no change to this file: the interpretation
is passed through unread.

A multi-step operation is a loop, not a special case. `solidClientRequest`
may answer a `state` alongside its request, and `solidClientResponse` may
answer `{ continue: true, state }`; the host then asks for the next
request with that state. Walking from a resource up to its storage root
is the case that needs it. A single-request operation runs the loop
once. The loop is capped (`maxSteps`, default 16) so a state that never
settles is a reported failure rather than a hang.

## Use

```js
import { createSolidClient } from '@factoidal/core/solid/client'

const client = await createSolidClient()
const storage = await client.discover('https://pod.example/alice/notes/one')
await client.put('https://pod.example/alice/notes/one', '<#a> <#b> <#c> .')
const read = await client.get('https://pod.example/alice/notes/one')
await client.delete('https://pod.example/alice/notes/one')
```

```
factoidal solid-client get https://pod.example/alice/notes/one
factoidal solid-client put https://pod.example/alice/notes/one --file note.ttl
factoidal solid-client discover https://pod.example/alice/notes/one
```

## Exports

| name | what it is |
| --- | --- |
| `createSolidClient(options)` | a client bound to one engine and one `fetch` |
| `solidClientOpsAvailable(engine)` | probe the loaded module for the ops |
| `SOLID_CLIENT_OPS` | the two op names |
| `SolidClientHostError` | a host failure, with `unknownOp` |

`options.fetch` replaces the platform `fetch`, which is how a test drives
the client at an in-process server without a proxy.

## Tests and interop

```
node tests/solid/client/against-own-server.mjs   # against our own server
bash tools/solid-client-interop.sh               # against Community Solid Server
```
