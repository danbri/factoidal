# `@factoidal/core/solid/server` — a Node host for the Solid Protocol

The Solid Protocol v0.11.0 server conformance class
(<https://solidproject.org/TR/protocol>) served over Node's `http`
module.

Tracking issue: <https://github.com/danbri/factoidal/issues/659>.
Design record:
[`docs/designissues/2026-09-06-lws-and-solid-protocols.md`](../../../../docs/designissues/2026-09-06-lws-and-solid-protocols.md).
Conformance ledger:
[`docs/lws-solid-conformance.md`](../../../../docs/lws-solid-conformance.md).

## What is here and what is not

`index.mjs` is a socket, a body reader and a header writer. Storage
discovery (`Link: rel="type"` for `pim:Storage`), containment triples,
slash semantics, `Allow` and the `Accept-*` family, the PUT/POST/PATCH/
DELETE rules with their status codes, the `acl` and `describedby`
auxiliary lifecycle, N3 Patch, Web Access Control, CORS and the LDN
inbox are all in `formal/lean4/L4Factoidal/Solid/Server/` and reach this
file only as a `{status, headers, body}` record.

The CORS preflight is not an exception. An `OPTIONS` request goes to
`solidStep` like any other and the engine's headers are written back
unread. The only status this file writes itself is `500`, for a failure
of the host.

Solid defers to LWS in the engine, not here: `Solid/Server/*`
instantiates `LWS.Store` and refines `LWS.Operations.step`. This host
knows nothing of that layering.

## The wasm contract

| op | arguments | answer |
| --- | --- | --- |
| `solidOpen` | `[configJson]` | `{ ok, handle }` |
| `solidStep` | `[handle, requestJson]` | `{ ok, response }` |
| `solidClose` | `[handle]` | `{ ok }` |

```
request  { method, target, headers: [[name, value]], body, baseUrl }
response { status, headers: [[name, value]], body }
```

`configJson` carries `root` (the directory the engine may keep state
under) and `baseUrl` (the origin the storage is published at). With an
ephemeral port the origin is not known until the socket is bound, so it
also travels on each request record as `baseUrl`; the engine needs it to
write absolute link targets and containment triples, and this host never
builds one itself.

A module built before these ops landed answers `unknown op`.
`solidServerOpsAvailable(engine)` reports that, and `tests/solid/server/`
skips with the reason printed.

## Use

```js
import { listen } from '@factoidal/core/solid/server'

const running = await listen({ root: '/var/lib/solid', port: 3000 })
console.log(running.origin)
await running.close()
```

```
factoidal solid-serve /var/lib/solid --port 3000
```

## Exports

| name | what it is |
| --- | --- |
| `listen(options)` | start a server, resolve when it is listening |
| `createSolidServer(options)` | build the server without listening |
| `openSolidStorage(options)` | open a handle and get `step` / `close` |
| `solidServerOpsAvailable(engine)` | probe the loaded module for the ops |
| `SOLID_SERVER_OPS` | the three op names |
| `SolidServerHostError` | a host failure, with `unknownOp` |

## Tests and interop

```
node tests/solid/server/protocol.mjs
bash tools/solid-server-interop.sh        # solid-crud-tests + WAC tests
bash tools/solid-conformance-harness.sh   # the Gherkin harness, needs Docker
```
