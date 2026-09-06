---
name: lws-solid
description: Run, test and extend Factoidal's Linked Web Storage 1.0 and Solid Protocol support - the Node hosts, the wasm ABI they call, the host test suites, the three community interop scripts and the conformance ledger. Use when serving a storage, driving a Solid client, adding a protocol rule, or reading a score from one of these suites.
---

# Linked Web Storage 1.0 and the Solid Protocol

Two standards, one engine, four hosts.

* **LWS 1.0 core** — <https://w3c.github.io/lws-protocol/lws10-core/>,
  W3C Linked Web Storage Working Group editor's draft. Its HTTP bindings
  and status codes are still headings with no content, and it defines no
  test suite.
* **Solid Protocol v0.11.0** — <https://solidproject.org/TR/protocol>.
  It has an HTTP binding, two conformance classes (server and client) and
  three community test suites.

Solid defers to LWS **in the engine**: `Solid/Server/*` instantiates
`LWS.Store` and refines `LWS.Operations.step`. Where the LWS draft is
still "todo", the Solid binding is used and the ledger row says so, so
the day LWS fixes its binding the row is the difference.

Read first:

* design record —
  [`docs/designissues/2026-09-06-lws-and-solid-protocols.md`](../../docs/designissues/2026-09-06-lws-and-solid-protocols.md)
* conformance ledger —
  [`docs/lws-solid-conformance.md`](../../docs/lws-solid-conformance.md);
  its "wasm ABI" section is the contract every host codes against, and
  its "host tests" section says what each host test covers
* tracking issue — <https://github.com/danbri/factoidal/issues/659>

## Where each piece lives

| path | what it is |
| --- | --- |
| `formal/lean4/L4Factoidal/LWS/` | the LWS resource model, store, operations, patch, discovery, conformance registry |
| `formal/lean4/L4Factoidal/Solid/Server/` | storage, containment, auxiliaries, methods, N3 Patch, WAC, CORS, LDN |
| `formal/lean4/L4Factoidal/Solid/Client/` | discovery, request building, response interpretation, WebID profile |
| `formal/lean4/Wasm/Ops/Lws.lean`, `Solid.lean` | the handle ops |
| `npm/factoidal/lws/server.mjs` | Node `http` host over `lwsStep` |
| `npm/factoidal/solid/server/index.mjs` | Node `http` host over `solidStep` |
| `npm/factoidal/solid/client/index.mjs` | `fetch` host over `solidClientRequest`/`solidClientResponse` |
| `tests/lws/`, `tests/solid/server/`, `tests/solid/client/` | the host suites |
| `tools/solid-server-interop.sh`, `solid-client-interop.sh`, `solid-conformance-harness.sh` | the three interop scripts |
| `third_party/testing/solid-crud-tests`, `web-access-control-tests`, `solid-specification-tests` | the community suites, as submodules |

**Iron rule 7 applies without exception.** A host accepts a socket, turns
one request into the ABI's JSON record, calls one op, and writes the
answer back. Any status code, `Link` relation, media type, containment
triple or access decision found in a `.mjs` under `npm/factoidal/lws/` or
`npm/factoidal/solid/` is a rule violation. The only status a host writes
is `500`, for a failure of the host itself.

## Run the servers

```
factoidal lws-serve   DIR [--port N] [--host ADDRESS] [--base IRI]
factoidal solid-serve DIR [--port N] [--host ADDRESS] [--base IRI] [--owner WEBID]
```

`--port 0` takes an ephemeral port and the command prints the origin it
got on stdout, which is what the interop scripts read. `--base` sets
`baseIri`, defaulting to the bound origin.

`DIR` names the storage directory and **is not read or written yet**: the
first slice keeps the resource tree in the engine handle (design record,
section 2). Persisting it into the Shardborough store is a later step.

From JavaScript:

```js
import { listen } from '@factoidal/core/lws'
import { listen as solidListen } from '@factoidal/core/solid/server'
```

## Run the client

```
factoidal solid-client <get|put|post|delete|discover> URL [--body TEXT|--file PATH]
                       [--content-type M] [--interpret KIND]
```

The five verbs are aliases for the ABI's request kinds — `get`→`read`,
`put`→`replace`, `post`→`create`, `delete`→`delete`,
`discover`→`discoverStorage` — and a kind name is accepted directly.

```js
import { createSolidClient } from '@factoidal/core/solid/client'
const client = await createSolidClient({ baseIri: 'https://pod.example/' })
```

`solidClientRequest` and `solidClientResponse` take **different** kind
vocabularies and the host never derives one from the other. Which
interpretation a reply wants is a protocol decision: the host uses the
`interpret` kind the request envelope named, then the one the caller
passed, and otherwise returns the reply uninterpreted.

## Run the tests

```
node tests/lws/server.mjs
node tests/solid/server/protocol.mjs
node tests/solid/client/against-own-server.mjs
```

Each also runs under Deno (`deno run --allow-read --allow-net --allow-env
<file>`), and the Node run drives the Deno run when `deno` is on PATH.
`tools/internal-tests.sh` runs all three as `node-tests/...` suites.

Each prints `N pass, M fail, S skipped (out of T)`.

**The wasm module is rebuilt by whoever owns the Lean side, not by these
tests.** A module without the new ops answers `unknown op`; each suite
probes with one call and then SKIPS every check by name with that reason
printed. A skip is never a pass (anti-pattern 3), and the score line
always carries the skip count.

## Run the interop scripts

```
bash tools/solid-server-interop.sh        # solid-crud-tests + WAC vs our server
bash tools/solid-client-interop.sh        # our client vs Community Solid Server
bash tools/solid-conformance-harness.sh   # the Gherkin harness (Docker)
```

Exit codes are the same in all three: `0` passed, `1` something failed,
`2` could not run here with the reason printed. **`2` is never a green
skip** — a suite that could not run reports `0 pass, 0 fail (out of 0) -
not run`.

What makes each one exit 2 today:

| script | why it does not run |
| --- | --- |
| `solid-server-interop.sh` | the module carries no Solid server ops; and `web-access-control-tests` logs in through an external Solid-OIDC issuer before its first request |
| `solid-client-interop.sh` | the module carries no Solid client ops; also refuses to start the ~250 MB Community Solid Server download below 2 GB free |
| `solid-conformance-harness.sh` | no Docker daemon, or no `SOLID_HARNESS_ENV` credentials file |

`tests/solid/client/against-own-server.mjs` puts our client and our
server on two ends of one socket, so a shared misreading of the
specification passes it. That is what
`tests/solid/client/against-community-server.mjs` (driven by
`solid-client-interop.sh`) and the two Jest suites are for.

## What is stubbed, and what is a stated boundary

Not in the first slice, recorded so nobody assumes it: Solid-OIDC token
issuance, Access Control Policy, Solid Notifications channels,
persistence into Shardborough, and the LWS `authn-openid`, `authn-saml`,
`authn-ssi` and `searchindex` drafts.

**Authentication is a boundary, not a gap in the engine.** Solid-OIDC
needs RS256 or ES256 JWT verification and DPoP proofs; HACL\* gives
SHA-256 and Ed25519 and neither RSA nor P-256 is vendored. Token
verification is therefore a host realisation (WebCrypto in Node) behind
one Lean-declared interface, and it is listed in the ledger as
`hostVerified`. Web Access Control decisions stay pure Lean over the
agent the host verified. The first slice serves public resources and
unauthenticated writes to a test-only storage, which is why both
access-control suites cannot run yet.

## Adding a rule

1. Write it in Lean, under `L4Factoidal/LWS/` or
   `L4Factoidal/Solid/Server/`, with its `#guard` in the neighbouring
   `Tests.lean`.
2. Add its row to the conformance registry: statement id, verbatim quote,
   module, status.
3. If it is visible over HTTP, add a check to the matching host suite in
   `tests/`, naming the specification section in the check name.
4. Rebuild the wasm module (`skills/lean4-wasm-export`) so the host
   suites stop skipping.
5. Nothing goes in a host. If a rule seems to need host code, the ABI is
   missing a field — extend the ABI record in the ledger instead.
