# `L4Factoidal.LWS` — Linked Web Storage Protocol 1.0 Core

Source specification:
<https://w3c.github.io/lws-protocol/lws10-core/> — W3C Linked Web Storage
Working Group editor's draft, read 2026-09-06.

Design record:
[`docs/designissues/2026-09-06-lws-and-solid-protocols.md`](../../../../docs/designissues/2026-09-06-lws-and-solid-protocols.md).
Ledger: [`docs/lws-solid-conformance.md`](../../../../docs/lws-solid-conformance.md).
Tracking issue: <https://github.com/danbri/factoidal/issues/659>.

## What the draft states, and what it does not

The draft defines the resource model (LWS resource, container, data
resource, storage root, metadata resource, linkset resource, auxiliary
resource, containment, storage, storage root, storage description) and names
the four operations. Its `Operations`, `Containers`, `Discovery`,
`Authentication` and `Authorization` sections are headings with empty
bodies. It states two MUST statements about behaviour, both in the
CG-to-ED delta list:

* "HTTP Server MUST generate a Last-Modified header field in response to GET
  and HEAD requests."
* "The PATCH ?insertions formulae MUST NOT contain blank nodes."

It defines no HTTP binding, no status codes and no test suite. Wherever a
binding is needed, this implementation uses the Solid Protocol v0.11.0
binding, which the draft's Acknowledgements name as its source, and the
conformance registry row carries both citations. The day the draft fixes its
own binding, those rows are the difference.

## Files

| file | what it holds |
|---|---|
| `Model.lean` | `ResourceKind`, path and containment functions, `Link`, `Entry`. Identifiers are `RDF.WfIri`. |
| `Store.lean` | `Store σ`, a structure of pure operations over an abstract state; `StoreLaws`, what a backend must satisfy; `MemStore`, the reference instance, with `memStoreLaws` proving it does. |
| `Discovery.lean` | the RFC 8288 links a storage advertises: `type`, `acl`, `describedby`, `storageDescription`, `owner`. |
| `Operations.lean` | `step : Store σ → Config → Request → σ → Response × σ` — create, read, update, delete, `Last-Modified`, `Allow`, `Accept-*`, and the HTTP-date conversion. |
| `Patch.lean` | the `?conditions` / `?insertions` / `?deletions` formula patch, its constraints, and `applyPatch`. Matching is `SPARQL.evalBgp` and instantiation is `SPARQL.instantiateTemplate` — no second matcher. |
| `Conformance.lean` | the registry: id, section, verbatim statement, module, binding, status. |
| `Tests.lean` | one `#guard` per `guarded` row, and the theorems the `proved` rows name. |

## What is pure and what is not

Everything in this directory is a total function. There is no socket, no
file read and no clock: the time comes from `Store.now`, which the host
sets, and every mutation calls `Store.tick`, so the modification times of a
request sequence are strictly increasing and the server-assigned names of
POST are distinct without a counter beside the clock.

The wasm entry layer (`Wasm/Ops/Lws.lean`) holds the state in a handle table
and is the only part that performs `IO`.

## Running it

```
cd formal/lean4
lake build L4Factoidal.LWS.Tests      # every #guard runs during the build
lake exe l4lws-probe                  # prints the registry counts
```
