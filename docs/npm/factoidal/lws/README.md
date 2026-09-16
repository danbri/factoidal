# `@factoidal/core/lws` — a Node host for Linked Web Storage 1.0

The W3C Linked Web Storage Protocol 1.0 core
(<https://w3c.github.io/lws-protocol/lws10-core/>, Linked Web Storage
Working Group editor's draft) served over Node's `http` module.

Tracking issue: <https://github.com/danbri/factoidal/issues/659>.
Design record:
[`docs/designissues/2026-09-06-lws-and-solid-protocols.md`](../../../docs/designissues/2026-09-06-lws-and-solid-protocols.md).
Conformance ledger:
[`docs/lws-solid-conformance.md`](../../../docs/lws-solid-conformance.md).

## What is here and what is not

`server.mjs` is a socket, a body reader and a header writer. Every
protocol decision — status codes, `Link` relations, `Last-Modified`,
containment, the blank-node refusal in PATCH — is made by
`formal/lean4/L4Factoidal/LWS/` and reaches this file only as a
`{status, headers, body}` record. Iron rule 7 of `CLAUDE.md`: no
protocol logic in a host.

The one status code this file writes itself is `500`, and only when the
host or the engine failed rather than answered.

## The wasm contract

| op | arguments | answer |
| --- | --- | --- |
| `lwsOpen` | `[configJson]` | `{ ok, handle, root }` |
| `lwsStep` | `[handle, requestJson]` | `{ ok, response }` |
| `lwsClose` | `[handle]` | `{ ok }` |

```
request  { method, target, headers: [[name, value]], body }
response { status, headers: [[name, value]], body }
```

`headers` is a list of pairs, not an object: HTTP allows a field name to
repeat and the order of repeated fields carries meaning. `target` is a
path within the storage, so Node's `request.url` is passed through
unchanged and this host composes no IRI.

`configJson` members, all optional: `baseIri` (the absolute IRI the
storage root maps to), `now` (the engine clock in seconds, which advances
by one second per mutation so a write sequence has increasing
`Last-Modified` values with no real clock), `owner`, `agent`. A request
may carry `now` and `agent` of its own to override the handle's for one
step; `listen({realClock: true})` is how a server with a real clock feeds
one in, and a test leaves it off to keep the engine's deterministic
clock. The full contract is `docs/lws-solid-conformance.md`, section
"wasm ABI".

A WebAssembly module built before these ops landed answers `unknown op`.
`lwsOpsAvailable(engine)` reports that as `{available: false, reason}`,
and every test in `tests/lws/` skips with the reason printed rather than
passing on an engine that cannot answer.

## Use

```js
import { listen } from '@factoidal/core/lws'

const running = await listen({ port: 3000, baseIri: 'https://storage.example/' })
console.log(running.origin)
await running.close()
```

From the command:

```
factoidal lws-serve /var/lib/lws --port 3000
```

`--port 0` takes an ephemeral port and the command prints the one it got;
`--base IRI` sets `baseIri`, which defaults to the bound origin. `DIR`
names the storage directory, but the first slice keeps the resource tree
in the engine handle, so nothing is read from it or written to it yet
(design record, section 2).

## Exports

| name | what it is |
| --- | --- |
| `listen(options)` | start a server, resolve when it is listening |
| `createLwsServer(options)` | build the server without listening |
| `openLwsStorage(options)` | open a handle and get `step` / `close` |
| `createLwsServer(...).setBaseIri(iri)` | set `baseIri` before the first request |
| `lwsOpsAvailable(engine)` | probe the loaded module for the ops |
| `LWS_OPS` | the three op names |
| `LwsHostError` | a host failure, with `unknownOp` set when the op is absent |

## Tests

```
node tests/lws/server.mjs
deno run --allow-read --allow-net --allow-write --allow-env tests/lws/server.mjs
```
