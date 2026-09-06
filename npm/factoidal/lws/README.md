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
| `lwsOpen` | `[configJson]` | `{ ok, handle }` |
| `lwsStep` | `[handle, requestJson]` | `{ ok, response }` |
| `lwsClose` | `[handle]` | `{ ok }` |

```
request  { method, target, headers: [[name, value]], body }
response { status, headers: [[name, value]], body }
```

`headers` is a list of pairs, not an object: HTTP allows a field name to
repeat and the order of repeated fields carries meaning.

A WebAssembly module built before these ops landed answers `unknown op`.
`lwsOpsAvailable(engine)` reports that as `{available: false, reason}`,
and every test in `tests/lws/` skips with the reason printed rather than
passing on an engine that cannot answer.

## Use

```js
import { listen } from '@factoidal/core/lws'

const running = await listen({ root: '/var/lib/lws', port: 3000 })
console.log(running.origin)
await running.close()
```

From the command:

```
factoidal lws-serve /var/lib/lws --port 3000
```

`DIR` is where the engine keeps its state. `--port 0` takes an ephemeral
port and the command prints the one it got.

## Exports

| name | what it is |
| --- | --- |
| `listen(options)` | start a server, resolve when it is listening |
| `createLwsServer(options)` | build the server without listening |
| `openLwsStorage(options)` | open a handle and get `step` / `close` |
| `lwsOpsAvailable(engine)` | probe the loaded module for the ops |
| `LWS_OPS` | the three op names |
| `LwsHostError` | a host failure, with `unknownOp` set when the op is absent |

## Tests

```
node tests/lws/server.mjs
deno run --allow-read --allow-net --allow-write --allow-env tests/lws/server.mjs
```
