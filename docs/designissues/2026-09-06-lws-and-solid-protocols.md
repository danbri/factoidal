# Linked Web Storage Protocol 1.0 and the Solid Protocol in Factoidal

2026-09-06. Owner, verbatim: "Add a new standard to Factoidal for
implementation - set up directories, test suites, READMEs etc and integrate
any test harnesses. This will be the Solid-inspired Linked Web Storage
Protocol 1.0. Also create similar setup for Solid itself - client and server.
Ideally it will use and defer to the W3C LWSP spec for backend, but that is a
development currently underway. Focus on unit tests and likely interop with
existing tools. Feel free to make both server and client, but keep a clear
distinction."

Tracking issue: <https://github.com/danbri/factoidal/issues/659>.

## 1. The two specifications, as read on 2026-09-06

**LWS 1.0 Core** (<https://w3c.github.io/lws-protocol/lws10-core/>, W3C
Linked Web Storage WG editor's draft; repository `w3c/lws-protocol`, with
sibling drafts `lws10-authn-openid`, `lws10-authn-saml`,
`lws10-authn-ssi-cid`, `lws10-authn-ssi-did-key`,
`lws10-notifications-webhook`, `lws10-searchindex`, `lws10-vocab`).
Resource model: LWS Resource, Container, Data Resource, Storage Root,
auxiliary Metadata Resource and Linkset Resource (RFC 9264). Operations:
Create, Read, Update, Delete, with `Last-Modified` REQUIRED on GET/HEAD and
PATCH "?insertions formulae MUST NOT contain blank nodes". Discovery by
RFC 8288 links from the root container. Authentication by OpenID Connect,
SAML 2.0 or controlled identifiers (CID 1.0); authorization by access
requests and grants. Notifications as terms (notification, subscription,
suite). **The HTTP bindings, status codes and conditional-request rules are
marked "todo" in the draft, and it defines no test suite.**

**Solid Protocol v0.11.0** (<https://solidproject.org/TR/protocol>,
Community Group report, modified 2024-05-12). Storage (`pim:Storage`) as
root container advertised by `Link: rel="type"`; LDP Basic Container
containment with a 1-1 correspondence between containment triples and the
path hierarchy; slash semantics; auxiliary resources `acl` and
`describedby`, deleted with their subject; GET/HEAD/OPTIONS with `Allow`,
`Accept-Patch`, `Accept-Post`, `Accept-Put`; PUT creating intermediate
containers and refusing containment-triple edits (409); POST to a container
with server-assigned names; PATCH with N3 Patch (`text/n3`); DELETE refusing
the root and its ACL (405); LDN inbox; Solid Notifications Protocol; CORS;
WebID; Solid-OIDC (WebID-TLS historical); "Servers MUST conform to either or
both Web Access Control and Access Control Policy". Conformance classes:
server and client; no test harness is named by the specification itself.

Interoperability tools that exist (checked 2026-09-06, all active):

| tool | what it is | how we use it |
|---|---|---|
| `solid-contrib/specification-tests` | the Solid specification tests (Gherkin), run by `solid-contrib/conformance-test-harness` (Java, Docker image) | server interop, optional, needs Docker |
| `solid-contrib/solid-crud-tests` | Jest surface tests for CRUD and WebSockets pub-sub against a running pod server | server interop, Node only |
| `solid-contrib/web-access-control-tests` | Jest tests of WAC | server interop, Node only |
| `CommunitySolidServer/CommunitySolidServer` | reference server (`npx @solid/community-server`) | CLIENT interop target |
| `w3c/ldp-testsuite` | archived, unmaintained | not used |

LWS has no test suite; its conformance is our own MUST-statement ledger.

## 2. Where each piece lives

Iron rules 1, 4 and 7 apply: protocol decisions are Lean, hosts carry
bytes. The existing `HTTP/Server.lean` and `HTTP/Client.lean` already frame
requests and responses without a socket, and the store operations already
run behind `Wasm/Ops/*` with all state in `Wasm/Ops/Handles.lean`. The two
new standards follow the same shape.

```
formal/lean4/L4Factoidal/LWS/          the LWS 1.0 core, spec side and engine side
  Model.lean        resource kinds, identifiers, containment, auxiliary links
  Store.lean        the abstract resource store (a structure of operations
                    plus their laws) that any backend instantiates
  Operations.lean   step : Store → Request → Response × Store, one function
                    per MUST statement, no IO
  Patch.lean        the ?insertions / ?deletions formula patch
  Discovery.lean    Link relations the root and containers advertise
  Conformance.lean  the MUST-statement registry: id → statement → theorem
                    or #guard that discharges it
  Tests.lean        #guard unit tests, one per registry row
formal/lean4/L4Factoidal/Solid/        the Solid Protocol AS A LAYER OVER LWS
  Server/           Storage.lean (pim:Storage, slash semantics), Containment.lean
                    (containment triples ↔ path hierarchy), Auxiliary.lean
                    (acl, describedby), Methods.lean (Allow, Accept-*, PUT/POST/
                    PATCH/DELETE rules, status codes), N3Patch.lean, WAC.lean
                    (the access decision as a pure function over ACL graphs),
                    Cors.lean, Ldn.lean
  Client/           Discovery.lean (find the storage, the inbox, auxiliaries),
                    Requests.lean (build conformant requests), Responses.lean
                    (interpret them), Profile.lean (WebID profile)
  Conformance.lean  registry as for LWS
  Tests.lean
formal/lean4/Wasm/Ops/Lws.lean         lwsOpen/lwsStep/lwsClose over a handle
formal/lean4/Wasm/Ops/Solid.lean       solidOpen/solidStep/solidClose, and
                                       solidClientRequest/solidClientResponse
npm/factoidal/lws/                     server host: Node http → lwsStep
npm/factoidal/solid/server/            server host: Node http → solidStep
npm/factoidal/solid/client/            client host: fetch → solidClient*
tests/lws/                             host tests over the wasm ops
tests/solid/server/, tests/solid/client/
third_party/testing/solid-specification-tests, solid-crud-tests,
  web-access-control-tests           submodules, registered in ensure-test-env.sh
tools/solid-server-interop.sh          run solid-crud-tests and WAC tests against our server
tools/solid-client-interop.sh          run our client against Community Solid Server
docs/lws-solid-conformance.md          the ledger: statement → module → test → status
```

**Solid defers to LWS.** `Solid/Server/*` never touches bytes or a
filesystem: it instantiates `LWS.Store` and refines `LWS.Operations.step`
with Solid's additional rules (containment triples, auxiliary resources,
WAC, slash semantics). Where LWS's draft is still "todo" (HTTP bindings),
the Solid rule is used and the registry row says "Solid 0.11 §N, LWS core
§Operations todo", so the day LWS fixes its binding the row is the diff.

**Server and client are distinct.** Different namespaces, different wasm
operations, different host packages, different test directories, different
interop scripts. The only shared code is `LWS.Model` (the vocabulary of
resources and links) and `HTTP/*` (message framing).

**State.** A server's resource tree is a handle in `Wasm/Ops/Handles.lean`
territory: the host feeds bytes, Lean holds the tree and returns responses.
Persistence to the Shardborough store (RDF resources as named graphs, one
graph per resource) is a later step; the first slice keeps the tree in the
handle and the host may snapshot it to disk as bytes it does not interpret.

**Authentication is a boundary, stated.** Solid-OIDC needs JWT verification
with RS256 or ES256 and DPoP proofs. HACL* gives SHA-256 and Ed25519; RSA and
P-256 are not vendored. Token verification is therefore a host realisation
(WebCrypto in Node) behind one Lean-declared interface, listed in the
conformance ledger as "host-verified", and the first slice serves public
resources and unauthenticated writes to a test-only storage. WAC decisions
are pure Lean over the agent the host verified.

## 3. The first slice (what "set up" delivers)

1. Directories, module skeletons with the types above, READMEs in every
   new directory naming the spec section each file implements.
2. LWS: `Model`, `Store` with laws, `Operations.step` for Create/Read/
   Update/Delete on data resources and containers, `Last-Modified`,
   `Patch` with the blank-node refusal, `Discovery` links, and `#guard`s
   for each — the conformance registry populated from the draft's MUST
   statements with their current status.
3. Solid server: storage discovery header, containment triples, slash
   semantics, `Allow`/`Accept-*`, PUT/POST/PATCH(N3 Patch)/DELETE rules with
   their status codes, auxiliary `acl`/`describedby` lifecycle, WAC decision
   function with the WAC spec's examples as `#guard`s, CORS headers, LDN
   inbox discovery and POST; wasm ops; Node host; `tests/solid/server/`
   replaying the specification's own HTTP examples; `solid-crud-tests`
   runnable against it with a labelled score.
4. Solid client: discovery walk, request builders, response interpretation,
   WebID profile read; Node host on `fetch`; `tests/solid/client/` against
   an in-process instance of OUR server, and `tools/solid-client-interop.sh`
   against Community Solid Server with a labelled score.
5. Registration: `Tests.lean` imports, `lakefile.lean` probes
   (`l4lws-probe`, `l4solid-probe`), `tools/ensure-test-env.sh` rows for
   the three submodules, `tools/internal-tests.sh` discovery of the new
   probes and Node suites, `docs/20260903-internal-test-inventory.md` rows,
   `skills/lws-solid/SKILL.md`, the spec-coverage ledger.

Scores are always labelled "N pass, M fail, S skipped (out of T)" and a
suite that cannot run (no Docker, no network) reports that, never a pass.

## 4. Not in the first slice, recorded so nobody assumes it

Solid-OIDC token issuance; ACP; Solid Notifications channels; the
conformance-test-harness Docker run (script written, run needs Docker);
persistence into Shardborough; LWS authn-openid / saml / ssi drafts; the
LWS search index draft. Each becomes an issue when it starts.
