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

## F* statement list

The F* tree states the same requirement identifiers over an abstract
resource store: [`formal/fstar/LWS.Core.Spec.fsti`](../formal/fstar/LWS.Core.Spec.fsti)
with its model and proofs in `LWS.Core.Spec.fst`, and
[`formal/fstar/Solid.Protocol.Spec.fsti`](../formal/fstar/Solid.Protocol.Spec.fsti)
which imports it and adds the Solid layer, its server statements in Part 8
and its client statements in Part 9. The list below is generated from
[`formal/fstar/LWS.Solid.Registry.fst`](../formal/fstar/LWS.Solid.Registry.fst),
whose rows carry the same identifiers and the same verbatim statements as the
Lean registries, and which proves that no identifier appears twice.

The F* modules are specifications, not an engine: each one declares the
operations over an abstract store and states the requirement as a `val` or a
lemma, and the accompanying `.fst` gives one model that discharges every law.
The engine is the Lean tree. A row with no F* statement is one the F* side
does not state yet; the Lean rows above say how that row is decided.

Verified with z3 4.13.3, no `--lax` and no `--admit_smt_queries`:
`fstar.exe --z3version 4.13.3 --cache_checked_modules <module>`.

51 of the 91 rows carry an F* statement (18 LWS rows: 10 stated;
73 Solid rows: 41 stated).

| requirement | source | section | F* statement |
|---|---|---|---|
| `lws-core-01` | LWS | Resource Access | - |
| `lws-core-02` | LWS | Resource Access | - |
| `lws-core-03` | LWS | For Editors (CG-to-ED delta) | `LWS.Core.Spec.lws_core_03_last_modified_on_get`, `LWS.Core.Spec.lws_core_03_last_modified_on_head` |
| `lws-core-04` | LWS | For Editors (CG-to-ED delta) | `LWS.Core.Spec.lws_core_04_insertions_no_blank_nodes`, `LWS.Core.Spec.lws_core_04_ill_formed_patch_refused` |
| `lws-core-05` | LWS | Terminology | `LWS.Core.Spec.lws_core_05_create_updates_containment`, `LWS.Core.Spec.lws_core_05_delete_updates_containment`, `LWS.Core.Spec.contained_are_children` |
| `lws-core-06` | LWS | Terminology | `LWS.Core.Spec.lws_core_06_root_has_no_parent`, `LWS.Core.Spec.lws_core_06_only_root_has_no_parent`, `LWS.Core.Spec.containment_acyclic`, `LWS.Core.Spec.containment_single_parent`, `LWS.Core.Spec.lws_core_root_not_deleted` |
| `lws-core-07` | LWS | Terminology | `Solid.Protocol.Spec.solid_04_11_auxiliaries_deleted_with_subject` |
| `lws-core-08` | LWS | Terminology | `LWS.Core.Spec.lws_core_08_auxiliary_links_advertised` |
| `lws-core-09` | LWS | Terminology | - |
| `lws-core-10` | LWS | Terminology | - |
| `lws-core-11` | LWS | Resource Access | `LWS.Core.Spec.lws_core_11_four_operations` |
| `lws-core-12` | LWS | Resource Access | `LWS.Core.Spec.lws_core_12_created_is_not_success` |
| `lws-core-13` | LWS | Resource Access | `Solid.Protocol.Spec.solid_wac_01_no_acl_denies` |
| `lws-core-14` | LWS | Resource Access | - |
| `lws-core-15` | LWS | Authentication | - |
| `lws-core-16` | LWS | Notifications | - |
| `lws-core-17` | LWS | Access Requests and Grants | - |
| `lws-core-18` | LWS | Terminology | `LWS.Core.Spec.lws_core_18_storage_description_link` |
| `solid-02-01` | Solid | Solid Protocol §2.1 HTTP Server | - |
| `solid-02-02` | Solid | Solid Protocol §2.1 HTTP Server | `Solid.Protocol.Spec.solid_02_02_content_type_required` |
| `solid-02-03` | Solid | Solid Protocol §2.1 HTTP Server | - |
| `solid-02-04` | Solid | Solid Protocol §2.1 HTTP Server | - |
| `solid-02-05` | Solid | Solid Protocol §2.1 HTTP Server | - |
| `solid-02-06` | Solid | Solid Protocol §2.2 HTTP Client | `Solid.Protocol.Spec.solid_02_06_client_content_type` |
| `solid-03-01` | Solid | Solid Protocol §3.1 URI Slash Semantics | `Solid.Protocol.Spec.solid_03_01_slash_denotes_container` |
| `solid-03-02` | Solid | Solid Protocol §3.1 URI Slash Semantics | `Solid.Protocol.Spec.solid_03_02_slash_pair_distinct` |
| `solid-03-03` | Solid | Solid Protocol §3.1 URI Slash Semantics | - |
| `solid-04-01` | Solid | Solid Protocol §4.1 Storage Resource | - |
| `solid-04-02` | Solid | Solid Protocol §4.1 Storage Resource | - |
| `solid-04-03` | Solid | Solid Protocol §4.1 Storage Resource | `Solid.Protocol.Spec.solid_04_03_storage_type_link` |
| `solid-04-04` | Solid | Solid Protocol §4.1 Storage Resource | `Solid.Protocol.Spec.solid_04_04_storage_description_link` |
| `solid-04-05` | Solid | Solid Protocol §4.1 Storage Resource | - |
| `solid-04-06` | Solid | Solid Protocol §4.1 Storage Resource | - |
| `solid-04-07` | Solid | Solid Protocol §4.1 Storage Resource | `Solid.Protocol.Spec.solid_04_07_owner_link` |
| `solid-04-08` | Solid | Solid Protocol §4.2 Resource Containment | `Solid.Protocol.Spec.solid_04_08_containment_iff_enumerated`, `Solid.Protocol.Spec.solid_04_08_containment_is_hierarchy` |
| `solid-04-09` | Solid | Solid Protocol §4.2 Resource Containment | - |
| `solid-04-10` | Solid | Solid Protocol §4.2.1 Contained Resource Metadata | - |
| `solid-04-11` | Solid | Solid Protocol §4.3 Auxiliary Resources | `Solid.Protocol.Spec.solid_04_11_auxiliaries_deleted_with_subject` |
| `solid-04-12` | Solid | Solid Protocol §4.3 Auxiliary Resources | `Solid.Protocol.Spec.solid_04_12_auxiliary_links_advertised` |
| `solid-04-13` | Solid | Solid Protocol §4.3.2 Description Resource | `Solid.Protocol.Spec.solid_04_13_at_most_one_description` |
| `solid-04-14` | Solid | Solid Protocol §4.3.2 Description Resource | `Solid.Protocol.Spec.solid_04_14_description_authorized_as_subject` |
| `solid-05-01` | Solid | Solid Protocol §5 Reading and Writing Resources | `Solid.Protocol.Spec.solid_05_01_unsupported_method_405` |
| `solid-05-02` | Solid | Solid Protocol §5.1 Resource Type Heuristics | `Solid.Protocol.Spec.solid_05_02_post_assigns_uri` |
| `solid-05-03` | Solid | Solid Protocol §5.2 Reading Resources | - |
| `solid-05-04` | Solid | Solid Protocol §5.2 Reading Resources | `Solid.Protocol.Spec.solid_05_04_allow_header` |
| `solid-05-05` | Solid | Solid Protocol §5.2 Reading Resources | `Solid.Protocol.Spec.solid_05_05_accept_headers` |
| `solid-05-06` | Solid | Solid Protocol §5.3 Writing Resources | - |
| `solid-05-07` | Solid | Solid Protocol §5.3 Writing Resources | `Solid.Protocol.Spec.solid_05_07_intermediate_container` |
| `solid-05-08` | Solid | Solid Protocol §5.3 Writing Resources | `Solid.Protocol.Spec.solid_05_02_post_assigns_uri` |
| `solid-05-09` | Solid | Solid Protocol §5.3 Writing Resources | `Solid.Protocol.Spec.solid_05_09_post_missing_target_404` |
| `solid-05-10` | Solid | Solid Protocol §5.3 Writing Resources | - |
| `solid-05-11` | Solid | Solid Protocol §5.3 Writing Resources | `Solid.Protocol.Spec.solid_05_11_containment_edit_409` |
| `solid-05-12` | Solid | Solid Protocol §5.3 Writing Resources | - |
| `solid-05-13` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | `Solid.Protocol.Spec.solid_05_13_n3_patch_accepted`, `LWS.Core.Spec.lws_patch_not_refused`, `LWS.Core.Spec.lws_patch_applied` |
| `solid-05-14` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | `Solid.Protocol.Spec.solid_05_05_accept_headers` |
| `solid-05-15` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | - |
| `solid-05-16` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | `Solid.Protocol.Spec.solid_05_19_ill_formed_patch_422` |
| `solid-05-17` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | `Solid.Protocol.Spec.solid_05_19_ill_formed_patch_422` |
| `solid-05-18` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | `LWS.Core.Spec.lws_core_04_insertions_no_blank_nodes` |
| `solid-05-19` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | `Solid.Protocol.Spec.solid_05_19_ill_formed_patch_422` |
| `solid-05-20` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | `Solid.Protocol.Spec.solid_05_20_patch_operations` |
| `solid-05-21` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | - |
| `solid-05-22` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | - |
| `solid-05-23` | Solid | Solid Protocol §5.4 Deleting Resources | `Solid.Protocol.Spec.solid_05_25_delete_removes_containment` |
| `solid-05-24` | Solid | Solid Protocol §5.4 Deleting Resources | `Solid.Protocol.Spec.solid_05_24_delete_root_405` |
| `solid-05-25` | Solid | Solid Protocol §5.4 Deleting Resources | `Solid.Protocol.Spec.solid_05_25_delete_removes_containment` |
| `solid-05-26` | Solid | Solid Protocol §5.4 Deleting Resources | `Solid.Protocol.Spec.solid_04_11_auxiliaries_deleted_with_subject` |
| `solid-05-27` | Solid | Solid Protocol §5.4 Deleting Resources | `Solid.Protocol.Spec.solid_05_27_delete_non_empty_container_409` |
| `solid-05-28` | Solid | Solid Protocol §5.5 Resource Representations | - |
| `solid-05-29` | Solid | Solid Protocol §5.5 Resource Representations | - |
| `solid-06-01` | Solid | Solid Protocol §6 Linked Data Notifications | - |
| `solid-06-02` | Solid | Solid Protocol §6 Linked Data Notifications | - |
| `solid-07-01` | Solid | Solid Protocol §7.1 Solid Notifications Protocol | - |
| `solid-08-01` | Solid | Solid Protocol §8.1 CORS Server | - |
| `solid-08-02` | Solid | Solid Protocol §8.1 CORS Server | - |
| `solid-08-03` | Solid | Solid Protocol §8.1 CORS Server | - |
| `solid-08-04` | Solid | Solid Protocol §8.1 CORS Server | - |
| `solid-09-01` | Solid | Solid Protocol §9.1 WebID | - |
| `solid-10-01` | Solid | Solid Protocol §10.1 Solid-OIDC | - |
| `solid-11-01` | Solid | Solid Protocol §11 Authorization | `Solid.Protocol.Spec.solid_wac_01_no_acl_denies` |
| `solid-wac-01` | Solid | Web Access Control §5.3 Authorization Evaluation | `Solid.Protocol.Spec.solid_wac_01_no_acl_denies` |
| `solid-wac-02` | Solid | Web Access Control §5.3.3 Authorization Matching | `Solid.Protocol.Spec.solid_wac_02_match_resource_agent_mode` |
| `solid-wac-03` | Solid | Web Access Control §5.3.3 Authorization Matching | `Solid.Protocol.Spec.solid_wac_03_default_is_inherited` |
| `solid-wac-04` | Solid | Web Access Control §5.3.3 Authorization Matching | `Solid.Protocol.Spec.solid_wac_04_agent_group` |
| `solid-wac-05` | Solid | Web Access Control §5.1 Effective ACL Resource Algorithm | - |
| `solid-wac-06` | Solid | Web Access Control §5.3.2 Web Origin Authorization | - |
| `solid-wac-07` | Solid | Web Access Control §5.3.4 Access Privileges | `Solid.Protocol.Spec.solid_wac_07_wac_allow_header` |
| `solid-wac-08` | Solid | Web Access Control §5.3.4 Access Privileges | `Solid.Protocol.Spec.solid_wac_08_client_reads_wac_allow` |
| `solid-wac-09` | Solid | Web Access Control §3.1 ACL Resource Discovery | `Solid.Protocol.Spec.solid_wac_09_client_acl_from_links` |
| `solid-wac-10` | Solid | Web Access Control §3.2 ACL Resource Representation | - |
| `solid-cl-01` | Solid | Solid Protocol §4.1 Storage Resource | `Solid.Protocol.Spec.solid_cl_01_storage_walk_sound` |
