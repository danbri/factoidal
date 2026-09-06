# `L4Factoidal.Solid` — the Solid Protocol, server and client

Source specifications:

* <https://solidproject.org/TR/protocol> — Solid Protocol v0.11.0, modified
  2024-05-12, read 2026-09-06.
* <https://solidproject.org/TR/wac> — Web Access Control, read 2026-09-06.

Design record:
[`docs/designissues/2026-09-06-lws-and-solid-protocols.md`](../../../../docs/designissues/2026-09-06-lws-and-solid-protocols.md).
Ledger: [`docs/lws-solid-conformance.md`](../../../../docs/lws-solid-conformance.md).
Tracking issue: <https://github.com/danbri/factoidal/issues/659>.

## Solid defers to LWS

`Solid/Server/*` holds no storage of its own. It instantiates
`L4Factoidal.LWS.Store` and REFINES `L4Factoidal.LWS.Operations.step`, which
decides create, read, update and delete and generates `Last-Modified`,
`Allow` and the `Accept-*` fields. Each file names, in its header, the LWS
function it wraps and what it adds.

| file | wraps | adds |
|---|---|---|
| `Server/Storage.lean` | `LWS.Model`, `LWS.Discovery` | the `pim:Storage` type link, the storage description and owner links, slash semantics and the 301 redirect |
| `Server/Containment.lean` | `LWS.Operations.containedPaths` | the container's RDF representation as LDP Basic Container containment triples, the contained-resource metadata, and the 1-1 correspondence theorems |
| `Server/Auxiliary.lean` | `LWS.Discovery`, `LWS.Store.remove` | the `acl` and `describedby` lifecycle and the theorem that an auxiliary dies with its subject |
| `Server/Methods.lean` | `LWS.Operations.step` | the access decision, the redirect, the container representation, the 409 on a containment edit, N3 Patch, auxiliary deletion, `WAC-Allow`, CORS |
| `Server/N3Patch.lean` | `LWS.Patch`, `Syntax.Turtle.parseTurtle` | the `text/n3` surface syntax of §5.3.1 |
| `Server/WAC.lean` | nothing of LWS — its `Authorization` section is empty | the whole access decision, the effective-ACL walk and `WAC-Allow` |
| `Server/Cors.lean` | `LWS.Operations.step`'s response | the `Access-Control-*` and `Vary` fields |
| `Server/Ldn.lean` | `LWS.Operations.step` | the `ldp:inbox` link and the acceptance rule |

## Server and client are distinct

Different namespaces, different wasm operations, different host packages,
different test directories. The client never calls a server function: it
builds requests (`Client/Requests.lean`), reads what came back
(`Client/Responses.lean`), reads the links (`Client/Discovery.lean`) and
reads a WebID profile (`Client/Profile.lean`).

The separation has a rule behind it. Web Access Control §3.1 says "Clients
MUST NOT derive the URI of the ACL resource through string operations on the
URI of the resource", while the SERVER has to choose that URI somehow. The
server's `aclPathOf` is in `L4Factoidal.LWS.Discovery`; the client side has
no such function, and reads the `acl` link instead.

## Access control in the first slice

`ServerConfig.enforceWac` is `false` by default. With it false the access
decision is computed and reported in `WAC-Allow` but never refuses a
request; the storage serves public resources and unauthenticated writes,
which is what the design record says the first slice does. With it true the
decision is enforced and a target with no effective ACL resource is denied,
as Web Access Control §5.3 requires. Registry row `solid-wac-10` records
that a storage is created without a root ACL, which is a host provisioning
step.

Authentication is a host boundary. Solid-OIDC needs RS256 or ES256, which
HACL\* does not give us, so the host verifies the token and passes the WebID
in the handle configuration. The engine decides access from a WebID it did
not verify, and the ledger row says so.

## Running it

```
cd formal/lean4
lake build L4Factoidal.Solid.Tests    # every #guard runs during the build
lake exe l4solid-probe                # prints the registry counts
```
