# LWS 1.0 Core and Solid Protocol — conformance ledger

Design record: [`docs/designissues/2026-09-06-lws-and-solid-protocols.md`](designissues/2026-09-06-lws-and-solid-protocols.md).
Tracking issue: <https://github.com/danbri/factoidal/issues/659>.

The Lean modules are `formal/lean4/L4Factoidal/LWS/` and
`formal/lean4/L4Factoidal/Solid/`. Every row below names one normative
statement of a specification, quotes it verbatim, names the Lean module that
decides it, and gives its status.

Status values (`L4Factoidal.LWS.Conformance.Status`):

| value | meaning |
|---|---|
| `proved` | a Lean theorem discharges the statement; the row names the theorem |
| `guarded` | a `#guard` in `Tests.lean` evaluates the statement at build time; the row names the guard |
| `hostVerified` | the decision needs bytes, a socket, a clock or a token the Lean side does not hold; a host test decides it |
| `open` | not decided yet |

Scores are always written "N pass, M fail (out of T)".

## wasm ABI

The host agent codes against this section. The operations are registered in
`formal/lean4/Wasm/Dispatch.lean` and reachable through `L4Wasm.callIO`
(they hold state, so the pure `L4Wasm.call` answers `unknown op` for them).
Arguments arrive as the dispatch ABI's JSON array of strings; every answer is
one envelope, `{"ok":true,…}` or `{"ok":false,"error":"…"}`.

### Request and response documents

A request is a JSON object:

```json
{"method":"PUT",
 "target":"/alice/card",
 "headers":[["content-type","text/turtle"]],
 "body":"<#me> <http://xmlns.com/foaf/0.1/name> \"Alice\" ."}
```

* `method` — an HTTP method token, upper case.
* `target` — the request target as a path within the storage, beginning with
  `/`. A path that ends with `/` names a container (Solid Protocol §3.1).
* `headers` — an array of two-element arrays. Names are compared case
  insensitively; the engine lower-cases them on the way in.
* `body` — a UTF-8 string. Binary bodies are not carried by this ABI yet; a
  host with binary content stores it outside the engine and gives the engine
  the metadata.

Every member is optional except `method` and `target`.

A response is a JSON object with the same shape minus the method:

```json
{"status":201,
 "headers":[["location","/alice/card"],["last-modified","Thu, 01 Jan 1970 00:00:01 GMT"]],
 "body":""}
```

### Operations

| op | arguments | answer |
|---|---|---|
| `lwsOpen` | `[configJson]` | `{"ok":true,"handle":"lws1","root":"/"}` |
| `lwsStep` | `[handle, requestJson]` | `{"ok":true,"response":{…}}` |
| `lwsClose` | `[handle]` | `{"ok":true}` |
| `solidOpen` | `[configJson]` | `{"ok":true,"handle":"solid1","root":"/","storage":"…"}` |
| `solidStep` | `[handle, requestJson]` | `{"ok":true,"response":{…}}` |
| `solidClose` | `[handle]` | `{"ok":true}` |
| `solidClientRequest` | `[kind, argsJson]` | `{"ok":true,"request":{…}}` |
| `solidClientResponse` | `[kind, responseJson]` | `{"ok":true,"interpretation":{…}}` |

`configJson` is a JSON object. Members, all optional:

| member | default | meaning |
|---|---|---|
| `baseIri` | `"http://localhost/"` | the absolute IRI the storage root maps to. A request target `/a/b` denotes `baseIri` + `a/b`. |
| `now` | `0` | the clock, in seconds since the Unix epoch. Every mutation stamps `Last-Modified` from it and then advances it by one second, so a sequence of writes has a strictly increasing modification time with no call to a real clock. |
| `owner` | absent | the WebID the storage advertises through `Link: rel="http://www.w3.org/ns/solid/terms#owner"`. |
| `agent` | absent | the WebID of the requesting agent for every request on this handle. The host verifies the token; the engine only decides access from it. A handle with no `agent` is an unauthenticated agent. |

A request document may override the clock and the agent for one step with the
members `now` and `agent` beside `method`; this is what a host with a real
clock and a real token verifier uses.

`solidClientRequest` kinds: `read`, `create`, `replace`, `patch`, `delete`,
`discoverStorage`, `readProfile`. `argsJson` is a JSON object whose members
depend on the kind; `target` is required by all of them, `body` and
`contentType` by `create`, `replace` and `patch`.

`solidClientResponse` kinds: `storage`, `containment`, `auxiliaries`,
`profile`, `wacAllow`. The interpretation object is documented per kind in
`formal/lean4/L4Factoidal/Solid/Client/Responses.lean`.

### Errors

An operation that cannot answer at all — an unknown handle, a request
document that is not JSON, an unknown client kind — answers
`{"ok":false,"error":"…"}`. A request the protocol REFUSES is not an error:
it answers `{"ok":true,"response":{"status":405,…}}`, because the status code
is the protocol's own answer.

## LWS 1.0 Core

Source: <https://w3c.github.io/lws-protocol/lws10-core/>, W3C Linked Web
Storage Working Group editor's draft, read 2026-09-06.

The draft's `Operations`, `Containers`, `Discovery`, `Authentication` and
`Authorization` sections are headings with no content, and it defines no HTTP
binding, no status codes and no test suite. Where a row needs a binding, the
Solid Protocol's binding is used and the row says so.

(Table generated from `L4Factoidal.LWS.Conformance.registry`; run
`lake exe l4lws-probe`.)

## Solid Protocol

Source: <https://solidproject.org/TR/protocol>, version 0.11.0, modified
2024-05-12, read 2026-09-06. Web Access Control:
<https://solidproject.org/TR/wac>.

(Table generated from `L4Factoidal.Solid.Conformance.registry`; run
`lake exe l4solid-probe`.)

## Host tests

The host side of both protocols is `npm/factoidal/lws/`,
`npm/factoidal/solid/server/` and `npm/factoidal/solid/client/`. Those
files decide nothing: they accept a socket, turn one request into the
JSON record above, call one operation, and write the answer back. What
the suites below gate is therefore the ROUND TRIP — that a request
reaching a socket arrives at the engine as the record this ABI states,
and that the engine's answer reaches the wire with its status, its
repeated headers and its body intact. The engine's decisions in
isolation are the `#guard`s of `Tests.lean`.

Scores are "N pass, M fail, S skipped (out of T)". The WebAssembly module
is rebuilt by whoever owns the Lean side; a module without these
operations answers `unknown op`, and every suite then probes once and
SKIPS each check by name with that reason printed. A skip is never a pass.

| file | runtimes | what it covers |
|---|---|---|
| `tests/lws/server.mjs` | Node, Deno | the server binds an ephemeral port; PUT creates a data resource; GET reads it back with `Last-Modified`; HEAD carries `Last-Modified` and no body; PUT updates it and `Last-Modified` moves; DELETE removes it; GET after DELETE answers 404; a PATCH whose insertion formula holds a blank node is refused with a 4xx |
| `tests/solid/server/protocol.mjs` | Node, Deno | the storage root advertises `pim:Storage` by `Link rel=type` (§4.1); OPTIONS reports `Allow`, `Accept-Post`, `Accept-Patch`, `Accept-Put` (§4.3); PUT creates a resource and its container gains the containment triple (§5.3); POST assigns a name and reports it in `Location` (§5.4); a PUT that edits a containment triple is refused with 409 (§5.3); DELETE on the storage root is refused with 405 (§5.5); a resource advertises its `describedby` auxiliary and the auxiliary dies with its subject (§4.2); PATCH applies an N3 Patch (§5.6); a CORS preflight is answered with the allow headers (§6); the LDN inbox is advertised and accepts a notification (§7) |
| `tests/solid/client/against-own-server.mjs` | Node, Deno | our client at an in-process instance of our server: `discoverStorage`, `replace`, `read`, `create` with a `Location`, `delete`, that a deleted resource is gone while its POSTed sibling survives, and that every request reached the socket through the engine |
| `tests/solid/client/against-community-server.mjs` | Node | the same five operations with the far end replaced by Community Solid Server, so a misreading our own two sides share cannot pass. Driven by `tools/solid-client-interop.sh` |

Interop scripts, all three exiting `0` passed, `1` failed, `2` could not
run here with the reason printed — never a green skip:

| script | suite | condition it needs |
|---|---|---|
| `tools/solid-server-interop.sh` | `solid-crud-tests`, `web-access-control-tests` | the Solid server operations; `npm ci` for each suite; the access-control suite additionally logs in through an external Solid-OIDC issuer before its first request |
| `tools/solid-client-interop.sh` | our client against Community Solid Server | the Solid client operations; `npx`; 2 GB free for the ~250 MB download |
| `tools/solid-conformance-harness.sh` | `solid-specification-tests` | a Docker daemon and a `SOLID_HARNESS_ENV` credentials file |

Measured 2026-09-06 against the committed WebAssembly module, which does
not carry these operations: `tests/lws/server.mjs` 0 pass, 0 fail, 8
skipped (out of 8); `tests/solid/server/protocol.mjs` 0 pass, 0 fail, 12
skipped (out of 12); `tests/solid/client/against-own-server.mjs` 0 pass,
0 fail, 7 skipped (out of 7); all three interop scripts exit 2.
