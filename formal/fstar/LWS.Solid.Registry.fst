module LWS.Solid.Registry

(** ======================================================================= **)
(** The cross-tree statement list for the Linked Web Storage Protocol 1.0   **)
(** Core and the Solid Protocol.                                           **)
(**                                                                         **)
(** One row per normative statement. The identifiers and the statement text **)
(** are those of the Lean registries                                        **)
(** formal/lean4/L4Factoidal/LWS/Conformance.lean and                       **)
(** formal/lean4/L4Factoidal/Solid/Conformance.lean, generated from them so **)
(** the two trees cannot drift apart. The Lean rows name the Lean module    **)
(** that decides each statement; the rows here name the F* val or lemma     **)
(** that STATES it, in LWS.Core.Spec or Solid.Protocol.Spec. An empty       **)
(** `fstar_name` says the F* side does not state that row yet.              **)
(**                                                                         **)
(** Sources, both read 2026-09-06:                                          **)
(**   https://w3c.github.io/lws-protocol/lws10-core/                        **)
(**   https://solidproject.org/TR/protocol  (v0.11.0, 2024-05-12)           **)
(**   https://solidproject.org/TR/wac                                       **)
(**                                                                         **)
(** This module states no protocol rule. It is a list, and the only         **)
(** property proved of it is that the identifiers are unique, so a row      **)
(** cannot be added under an identifier that already has one.               **)
(** ======================================================================= **)

open FStar.List.Tot

type spec_source =
  | Src_Lws
  | Src_Solid

type requirement = {
  req_id      : string;
  req_source  : spec_source;
  req_section : string;
  req_text    : string;
  fstar_name  : string
}

let source_label (s : spec_source) : string =
  match s with
  | Src_Lws   -> "LWS 1.0 Core"
  | Src_Solid -> "Solid Protocol"

let requirements : list requirement =
[ { req_id      = "lws-core-01"
  ; req_source  = Src_Lws
  ; req_section = "Resource Access"
  ; req_text    = "A LWS Server is an HTTP server [RFC9112] that complies with all of the relevant \"MUST\" statements in this specification."
  ; fstar_name  = "" }
; { req_id      = "lws-core-02"
  ; req_source  = Src_Lws
  ; req_section = "Resource Access"
  ; req_text    = "An LWS Client is an HTTP client [RFC9112] that complies with all of the relevant \"MUST\" statements in this specification."
  ; fstar_name  = "" }
; { req_id      = "lws-core-03"
  ; req_source  = Src_Lws
  ; req_section = "For Editors (CG-to-ED delta)"
  ; req_text    = "HTTP Server MUST generate a Last-Modified header field in response to GET and HEAD requests."
  ; fstar_name  = "LWS.Core.Spec.lws_core_03_last_modified_on_get, LWS.Core.Spec.lws_core_03_last_modified_on_head" }
; { req_id      = "lws-core-04"
  ; req_source  = Src_Lws
  ; req_section = "For Editors (CG-to-ED delta)"
  ; req_text    = "The PATCH ?insertions formulae MUST NOT contain blank nodes."
  ; fstar_name  = "LWS.Core.Spec.lws_core_04_insertions_no_blank_nodes, LWS.Core.Spec.lws_core_04_ill_formed_patch_refused" }
; { req_id      = "lws-core-05"
  ; req_source  = Src_Lws
  ; req_section = "Terminology"
  ; req_text    = "container — an LWS resource that is able to enumerate a collection of LWS resources, conforming to the conventions described in Section 8. Containers."
  ; fstar_name  = "LWS.Core.Spec.lws_core_05_create_updates_containment, LWS.Core.Spec.lws_core_05_delete_updates_containment, LWS.Core.Spec.contained_are_children" }
; { req_id      = "lws-core-06"
  ; req_source  = Src_Lws
  ; req_section = "Terminology"
  ; req_text    = "storage root — a container at the root of a containment hierarchy of a storage. The storage root is the only LWS resource that does not have a parent in the LWS containment hierarchy nor a primary resource."
  ; fstar_name  = "LWS.Core.Spec.lws_core_06_root_has_no_parent, LWS.Core.Spec.lws_core_06_only_root_has_no_parent, LWS.Core.Spec.containment_acyclic, LWS.Core.Spec.containment_single_parent, LWS.Core.Spec.lws_core_root_not_deleted" }
; { req_id      = "lws-core-07"
  ; req_source  = Src_Lws
  ; req_section = "Terminology"
  ; req_text    = "auxiliary resource — an LWS resource that plays a particular role with respect to a LWS resource, called its primary resource, and whose lifetime is bound to the primary resource."
  ; fstar_name  = "Solid.Protocol.Spec.solid_04_11_auxiliaries_deleted_with_subject" }
; { req_id      = "lws-core-08"
  ; req_source  = Src_Lws
  ; req_section = "Terminology"
  ; req_text    = "Auxiliary resources are discovered using web links [RFC8288] of a specific type (see Section )."
  ; fstar_name  = "LWS.Core.Spec.lws_core_08_auxiliary_links_advertised" }
; { req_id      = "lws-core-09"
  ; req_source  = Src_Lws
  ; req_section = "Terminology"
  ; req_text    = "linkset resource — a type of auxiliary resource whose representation conforms to [RFC9264]."
  ; fstar_name  = "" }
; { req_id      = "lws-core-10"
  ; req_source  = Src_Lws
  ; req_section = "Terminology"
  ; req_text    = "metadata resource — an auxiliary resource, managed by a storage, that describes an LWS resource and conforms to the conventions described in TBD."
  ; fstar_name  = "" }
; { req_id      = "lws-core-11"
  ; req_source  = Src_Lws
  ; req_section = "Resource Access"
  ; req_text    = "An operation is any of the following actions that can be performed on a served resource: create resource, read resource, update resource, delete resource."
  ; fstar_name  = "LWS.Core.Spec.lws_core_11_four_operations" }
; { req_id      = "lws-core-12"
  ; req_source  = Src_Lws
  ; req_section = "Resource Access"
  ; req_text    = "success - the operation is believed to have completed. This may be accompanied by a resource representation conveying the contents of a served resource. A success response is not defined for the create resource operation. See instead created."
  ; fstar_name  = "LWS.Core.Spec.lws_core_12_created_is_not_success" }
; { req_id      = "lws-core-13"
  ; req_source  = Src_Lws
  ; req_section = "Resource Access"
  ; req_text    = "not permitted"
  ; fstar_name  = "Solid.Protocol.Spec.solid_wac_01_no_acl_denies" }
; { req_id      = "lws-core-14"
  ; req_source  = Src_Lws
  ; req_section = "Resource Access"
  ; req_text    = "unknown requester"
  ; fstar_name  = "" }
; { req_id      = "lws-core-15"
  ; req_source  = Src_Lws
  ; req_section = "Authentication"
  ; req_text    = "LWS makes use of user authentication as defined in specifications for OpenID Connect, SAML 2.0, and self-signed controlled identifiers (CIDs), for example."
  ; fstar_name  = "" }
; { req_id      = "lws-core-16"
  ; req_source  = Src_Lws
  ; req_section = "Notifications"
  ; req_text    = "notification — a message describing an event that has occurred on a resource."
  ; fstar_name  = "" }
; { req_id      = "lws-core-17"
  ; req_source  = Src_Lws
  ; req_section = "Access Requests and Grants"
  ; req_text    = "access grant — a data object created by a storage controller, expressing an ability for an agent to perform specific actions on storage resources within certain defined constraints."
  ; fstar_name  = "" }
; { req_id      = "lws-core-18"
  ; req_source  = Src_Lws
  ; req_section = "Terminology"
  ; req_text    = "storage description — an LWS resource, conforming to the requirements of a W3C Controlled Identifier document [CID-1.0], that describes a storage along with its services and capabilities."
  ; fstar_name  = "LWS.Core.Spec.lws_core_18_storage_description_link" }
; { req_id      = "solid-02-01"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §2.1 HTTP Server"
  ; req_text    = "Servers MUST conform to HTTP Semantics [RFC9110]. […] Servers MUST conform to HTTP/1.1 [RFC9112]."
  ; fstar_name  = "" }
; { req_id      = "solid-02-02"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §2.1 HTTP Server"
  ; req_text    = "Server MUST reject PUT, POST, and PATCH requests that contain content but lack the Content-Type header field, with a status code of 400."
  ; fstar_name  = "Solid.Protocol.Spec.solid_02_02_content_type_required" }
; { req_id      = "solid-02-03"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §2.1 HTTP Server"
  ; req_text    = "When a client does not provide valid credentials when requesting a resource that requires it (see WebID), servers MUST send a response with a 401 status code (unless 404 is preferred for security reasons)."
  ; fstar_name  = "" }
; { req_id      = "solid-02-04"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §2.1 HTTP Server"
  ; req_text    = "When both http and https URI schemes are supported, the server MUST redirect all http URIs to their https counterparts using a response with a 301 status code and a Location header."
  ; fstar_name  = "" }
; { req_id      = "solid-02-05"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §2.1 HTTP Server"
  ; req_text    = "Server MUST generate a Content-Type header field in a message that contains content."
  ; fstar_name  = "" }
; { req_id      = "solid-02-06"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §2.2 HTTP Client"
  ; req_text    = "Clients MUST use the Content-Type HTTP header field in PUT, POST, and PATCH requests that contain content [RFC9110]."
  ; fstar_name  = "Solid.Protocol.Spec.solid_02_06_client_content_type" }
; { req_id      = "solid-03-01"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §3.1 URI Slash Semantics"
  ; req_text    = "Paths ending with a slash denote a container resource."
  ; fstar_name  = "Solid.Protocol.Spec.solid_03_01_slash_denotes_container" }
; { req_id      = "solid-03-02"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §3.1 URI Slash Semantics"
  ; req_text    = "If two URIs differ only in the trailing slash, and the server has associated a resource with one of them, then the other URI MUST NOT correspond to another resource. Instead, the server MAY respond to requests for the latter URI with a 301 redirect to the former."
  ; fstar_name  = "Solid.Protocol.Spec.solid_03_02_slash_pair_distinct" }
; { req_id      = "solid-03-03"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §3.1 URI Slash Semantics"
  ; req_text    = "Servers MUST authorize prior to this optional redirect."
  ; fstar_name  = "" }
; { req_id      = "solid-04-01"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §4.1 Storage Resource"
  ; req_text    = "Servers MUST provide one or more storages."
  ; fstar_name  = "" }
; { req_id      = "solid-04-02"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §4.1 Storage Resource"
  ; req_text    = "When a server supports multiple storages, the URIs MUST be allocated to non-overlapping space."
  ; fstar_name  = "" }
; { req_id      = "solid-04-03"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §4.1 Storage Resource"
  ; req_text    = "Servers MUST advertise the storage resource by including the HTTP Link header field with rel=\"type\" targeting http://www.w3.org/ns/pim/space#Storage when responding to storage's request URI."
  ; fstar_name  = "Solid.Protocol.Spec.solid_04_03_storage_type_link" }
; { req_id      = "solid-04-04"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §4.1 Storage Resource"
  ; req_text    = "Servers MUST include the Link header field with rel=\"http://www.w3.org/ns/solid/terms#storageDescription\" targeting the URI of the storage description resource in the response of HTTP GET, HEAD and OPTIONS requests targeting a resource in a storage."
  ; fstar_name  = "Solid.Protocol.Spec.solid_04_04_storage_description_link" }
; { req_id      = "solid-04-05"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §4.1 Storage Resource"
  ; req_text    = "Servers MUST include statements about the storage as part of the storage description resource."
  ; fstar_name  = "" }
; { req_id      = "solid-04-06"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §4.1 Storage Resource"
  ; req_text    = "Servers MUST keep track of at least one owner of a storage in an implementation defined way."
  ; fstar_name  = "" }
; { req_id      = "solid-04-07"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §4.1 Storage Resource"
  ; req_text    = "When a server wants to advertise the owner of a storage, the server MUST include the Link header field with rel=\"http://www.w3.org/ns/solid/terms#owner\" targeting the URI of the owner in the response of HTTP HEAD or GET requests targeting the root container."
  ; fstar_name  = "Solid.Protocol.Spec.solid_04_07_owner_link" }
; { req_id      = "solid-04-08"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §4.2 Resource Containment"
  ; req_text    = "There is a 1-1 correspondence between containment triples and relative reference within the path name hierarchy."
  ; fstar_name  = "Solid.Protocol.Spec.solid_04_08_containment_iff_enumerated, Solid.Protocol.Spec.solid_04_08_containment_is_hierarchy" }
; { req_id      = "solid-04-09"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §4.2 Resource Containment"
  ; req_text    = "The representation and behaviour of containers in Solid corresponds to LDP Basic Container and MUST be supported by server."
  ; fstar_name  = "" }
; { req_id      = "solid-04-10"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §4.2.1 Contained Resource Metadata"
  ; req_text    = "Servers SHOULD include resource metadata about contained resources as part of the container description, unless that information is inapplicable to the server."
  ; fstar_name  = "" }
; { req_id      = "solid-04-11"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §4.3 Auxiliary Resources"
  ; req_text    = "Servers MUST support auxiliary resources defined by this specification and manage the association between a subject resource and auxiliary resources. When a subject resource is deleted its auxiliary resources are also deleted by the server."
  ; fstar_name  = "Solid.Protocol.Spec.solid_04_11_auxiliaries_deleted_with_subject" }
; { req_id      = "solid-04-12"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §4.3 Auxiliary Resources"
  ; req_text    = "Servers MUST advertise auxiliary resources associated with a subject resource by responding to HEAD and GET requests by including the HTTP Link header field with the rel parameter [RFC8288]."
  ; fstar_name  = "Solid.Protocol.Spec.solid_04_12_auxiliary_links_advertised" }
; { req_id      = "solid-04-13"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §4.3.2 Description Resource"
  ; req_text    = "Servers MUST NOT directly associate more than one description resource to a subject resource."
  ; fstar_name  = "Solid.Protocol.Spec.solid_04_13_at_most_one_description" }
; { req_id      = "solid-04-14"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §4.3.2 Description Resource"
  ; req_text    = "When an HTTP request targets a description resource, the server MUST apply the authorization rule that is used for the subject resource with which the description resource is associated."
  ; fstar_name  = "Solid.Protocol.Spec.solid_04_14_description_authorized_as_subject" }
; { req_id      = "solid-05-01"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5 Reading and Writing Resources"
  ; req_text    = "Servers MUST respond with the 405 status code to requests using HTTP methods that are not supported by the target resource."
  ; fstar_name  = "Solid.Protocol.Spec.solid_05_01_unsupported_method_405" }
; { req_id      = "solid-05-02"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.1 Resource Type Heuristics"
  ; req_text    = "When a successful POST request creates a resource, the server MUST assign a URI to that resource."
  ; fstar_name  = "Solid.Protocol.Spec.solid_05_02_post_assigns_uri" }
; { req_id      = "solid-05-03"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.2 Reading Resources"
  ; req_text    = "Servers MUST support the HTTP GET, HEAD and OPTIONS methods [RFC9110] for clients to read resources or to determine communication options."
  ; fstar_name  = "" }
; { req_id      = "solid-05-04"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.2 Reading Resources"
  ; req_text    = "Servers MUST indicate the HTTP methods supported by the target resource by generating an Allow header field in successful responses."
  ; fstar_name  = "Solid.Protocol.Spec.solid_05_04_allow_header" }
; { req_id      = "solid-05-05"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.2 Reading Resources"
  ; req_text    = "When responding to authorized requests, servers MUST indicate supported media types in the HTTP Accept-Patch [RFC5789], Accept-Post [LDP] and Accept-Put [The Accept-Put Response Header] response header fields that correspond to acceptable HTTP methods listed in Allow header field value in response to HTTP GET, HEAD and OPTIONS requests."
  ; fstar_name  = "Solid.Protocol.Spec.solid_05_05_accept_headers" }
; { req_id      = "solid-05-06"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.3 Writing Resources"
  ; req_text    = "Servers MUST support the HTTP PUT, POST and PATCH methods [RFC9110]."
  ; fstar_name  = "" }
; { req_id      = "solid-05-07"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.3 Writing Resources"
  ; req_text    = "Servers MUST create intermediate containers and include corresponding containment triples in container representations derived from the URI path component of PUT and PATCH requests."
  ; fstar_name  = "Solid.Protocol.Spec.solid_05_07_intermediate_container" }
; { req_id      = "solid-05-08"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.3 Writing Resources"
  ; req_text    = "Servers MUST allow creation of new resources by a POST request to a URI path ending with /. Servers MUST create resources with URI paths ending with /{id} in container /."
  ; fstar_name  = "Solid.Protocol.Spec.solid_05_02_post_assigns_uri" }
; { req_id      = "solid-05-09"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.3 Writing Resources"
  ; req_text    = "When a POST method request targets a resource without an existing representation, the server MUST respond with the 404 status code."
  ; fstar_name  = "Solid.Protocol.Spec.solid_05_09_post_missing_target_404" }
; { req_id      = "solid-05-10"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.3 Writing Resources"
  ; req_text    = "When a PUT or PATCH request targets an auxiliary resource, the server MUST create or update it."
  ; fstar_name  = "" }
; { req_id      = "solid-05-11"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.3 Writing Resources"
  ; req_text    = "Servers MUST NOT allow HTTP PUT or PATCH on a container to update its containment triples; if the server receives such a request, it MUST respond with a 409 status code."
  ; fstar_name  = "Solid.Protocol.Spec.solid_05_11_containment_edit_409" }
; { req_id      = "solid-05-12"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.3 Writing Resources"
  ; req_text    = "Servers MUST NOT allow HTTP POST, PUT and PATCH to update a container's resource metadata statements; if the server receives such a request, it MUST respond with a 409 status code."
  ; fstar_name  = "" }
; { req_id      = "solid-05-13"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.3.1 Modifying Resources Using N3 Patches"
  ; req_text    = "Servers MUST accept a PATCH request with an N3 Patch body when the target of the request is an RDF document [RDF11-CONCEPTS]."
  ; fstar_name  = "Solid.Protocol.Spec.solid_05_13_n3_patch_accepted, LWS.Core.Spec.lws_patch_not_refused, LWS.Core.Spec.lws_patch_applied" }
; { req_id      = "solid-05-14"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.3.1 Modifying Resources Using N3 Patches"
  ; req_text    = "Servers MUST indicate support of N3 Patch by listing text/n3 as a field value of the Accept-Patch header field [RFC5789] of relevant responses."
  ; fstar_name  = "Solid.Protocol.Spec.solid_05_05_accept_headers" }
; { req_id      = "solid-05-15"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.3.1 Modifying Resources Using N3 Patches"
  ; req_text    = "When present, ?deletions, ?insertions, and ?conditions MUST be non-nested cited formulae [N3] consisting only of triples and/or triple patterns [SPARQL11-QUERY]."
  ; fstar_name  = "" }
; { req_id      = "solid-05-16"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.3.1 Modifying Resources Using N3 Patches"
  ; req_text    = "A patch resource MUST contain a triple ?patch rdf:type solid:InsertDeletePatch."
  ; fstar_name  = "Solid.Protocol.Spec.solid_05_19_ill_formed_patch_422" }
; { req_id      = "solid-05-17"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.3.1 Modifying Resources Using N3 Patches"
  ; req_text    = "The ?insertions and ?deletions formulae MUST NOT contain variables that do not occur in the ?conditions formula."
  ; fstar_name  = "Solid.Protocol.Spec.solid_05_19_ill_formed_patch_422" }
; { req_id      = "solid-05-18"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.3.1 Modifying Resources Using N3 Patches"
  ; req_text    = "The ?insertions and ?deletions formulae MUST NOT contain blank nodes."
  ; fstar_name  = "LWS.Core.Spec.lws_core_04_insertions_no_blank_nodes" }
; { req_id      = "solid-05-19"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.3.1 Modifying Resources Using N3 Patches"
  ; req_text    = "Servers MUST respond with a 422 status code [RFC4918] if a patch document does not satisfy all of the above constraints."
  ; fstar_name  = "Solid.Protocol.Spec.solid_05_19_ill_formed_patch_422" }
; { req_id      = "solid-05-20"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.3.1 Modifying Resources Using N3 Patches"
  ; req_text    = "When ?conditions is non-empty, servers MUST treat the request as a Read operation. When ?insertions is non-empty, servers MUST (also) treat the request as an Append operation. When ?deletions is non-empty, servers MUST treat the request as a Read and Write operation."
  ; fstar_name  = "Solid.Protocol.Spec.solid_05_20_patch_operations" }
; { req_id      = "solid-05-21"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.3.1 Modifying Resources Using N3 Patches"
  ; req_text    = "If no such mapping exists, or if multiple mappings exist, the server MUST respond with a 409 status code."
  ; fstar_name  = "" }
; { req_id      = "solid-05-22"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.3.1 Modifying Resources Using N3 Patches"
  ; req_text    = "If the set of triples resulting from ?deletions is non-empty and the dataset does not contain all of these triples, the server MUST respond with a 409 status code."
  ; fstar_name  = "" }
; { req_id      = "solid-05-23"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.4 Deleting Resources"
  ; req_text    = "Servers MUST support the HTTP DELETE method [RFC9110]."
  ; fstar_name  = "Solid.Protocol.Spec.solid_05_25_delete_removes_containment" }
; { req_id      = "solid-05-24"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.4 Deleting Resources"
  ; req_text    = "When a DELETE request targets storage's root container or its associated ACL resource, the server MUST respond with the 405 status code. Server MUST exclude the DELETE method in the field value of the Allow header field, in response to requests to these resources."
  ; fstar_name  = "Solid.Protocol.Spec.solid_05_24_delete_root_405" }
; { req_id      = "solid-05-25"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.4 Deleting Resources"
  ; req_text    = "When a contained resource is deleted, the server MUST also remove the corresponding containment triple."
  ; fstar_name  = "Solid.Protocol.Spec.solid_05_25_delete_removes_containment" }
; { req_id      = "solid-05-26"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.4 Deleting Resources"
  ; req_text    = "When a contained resource is deleted, the server MUST also delete the associated auxiliary resources."
  ; fstar_name  = "Solid.Protocol.Spec.solid_04_11_auxiliaries_deleted_with_subject" }
; { req_id      = "solid-05-27"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.4 Deleting Resources"
  ; req_text    = "When a DELETE request targets a container, the server MUST delete the container if it contains no resources. If the container contains resources, the server MUST respond with the 409 status code."
  ; fstar_name  = "Solid.Protocol.Spec.solid_05_27_delete_non_empty_container_409" }
; { req_id      = "solid-05-28"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.5 Resource Representations"
  ; req_text    = "When a server creates an RDF source on HTTP PUT, POST, or PATCH requests, the server MUST satisfy GET requests on this resource when the Accept header field requests text/turtle or application/ld+json."
  ; fstar_name  = "" }
; { req_id      = "solid-05-29"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §5.5 Resource Representations"
  ; req_text    = "When a PUT, POST, PATCH or DELETE method request targets a representation URL that is different than the resource URL, the server MUST respond with a 307 or 308 status code."
  ; fstar_name  = "" }
; { req_id      = "solid-06-01"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §6 Linked Data Notifications"
  ; req_text    = "A Solid server MUST conform to the LDN specification by implementing the Receiver parts to receive notifications, and MAY implement the Sender or Consumer parts."
  ; fstar_name  = "" }
; { req_id      = "solid-06-02"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §6 Linked Data Notifications"
  ; req_text    = "A Solid client MUST conform to the LDN specification by implementing the Sender or Consumer parts to send or read notifications."
  ; fstar_name  = "" }
; { req_id      = "solid-07-01"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §7.1 Solid Notifications Protocol"
  ; req_text    = "Servers MUST conform to the Solid Notifications Protocol by implementing the Resource Server, Subscription Server, Notification Sender and Notification Receiver."
  ; fstar_name  = "" }
; { req_id      = "solid-08-01"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §8.1 CORS Server"
  ; req_text    = "A server MUST implement the CORS protocol [FETCH] such that browsers allow Solid apps to send any request and combination of request headers to the server, and allow the app to read any response and response headers received from the server."
  ; fstar_name  = "" }
; { req_id      = "solid-08-02"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §8.1 CORS Server"
  ; req_text    = "The server MUST set the Access-Control-Allow-Origin header field value to the valid Origin header field value from the request and list Origin in the Vary header field value."
  ; fstar_name  = "" }
; { req_id      = "solid-08-03"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §8.1 CORS Server"
  ; req_text    = "The server MUST make all used response headers readable for the Solid app through Access-Control-Expose-Headers."
  ; fstar_name  = "" }
; { req_id      = "solid-08-04"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §8.1 CORS Server"
  ; req_text    = "A server MUST also support the HTTP OPTIONS method such that it can respond appropriately to CORS preflight requests."
  ; fstar_name  = "" }
; { req_id      = "solid-09-01"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §9.1 WebID"
  ; req_text    = "When a WebID is dereferenced, server provides a representation of the WebID Profile in an RDF document."
  ; fstar_name  = "" }
; { req_id      = "solid-10-01"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §10.1 Solid-OIDC"
  ; req_text    = "Servers MUST conform to the Solid-OIDC specification."
  ; fstar_name  = "" }
; { req_id      = "solid-11-01"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §11 Authorization"
  ; req_text    = "Servers MUST conform to either or both Web Access Control and Access Control Policy specifications."
  ; fstar_name  = "Solid.Protocol.Spec.solid_wac_01_no_acl_denies" }
; { req_id      = "solid-wac-01"
  ; req_source  = Src_Solid
  ; req_section = "Web Access Control §5.3 Authorization Evaluation"
  ; req_text    = "Access is granted when conforming Authorizations are matched, otherwise access is denied."
  ; fstar_name  = "Solid.Protocol.Spec.solid_wac_01_no_acl_denies" }
; { req_id      = "solid-wac-02"
  ; req_source  = Src_Solid
  ; req_section = "Web Access Control §5.3.3 Authorization Matching"
  ; req_text    = "Match an Authorization with a specific resource, agent and access mode."
  ; fstar_name  = "Solid.Protocol.Spec.solid_wac_02_match_resource_agent_mode" }
; { req_id      = "solid-wac-03"
  ; req_source  = Src_Solid
  ; req_section = "Web Access Control §5.3.3 Authorization Matching"
  ; req_text    = "Match an Authorization with a specific container resource, agent class membership and access mode."
  ; fstar_name  = "Solid.Protocol.Spec.solid_wac_03_default_is_inherited" }
; { req_id      = "solid-wac-04"
  ; req_source  = Src_Solid
  ; req_section = "Web Access Control §5.3.3 Authorization Matching"
  ; req_text    = "Match an Authorization with a specific resource, agent with any group membership, and specific access mode."
  ; fstar_name  = "Solid.Protocol.Spec.solid_wac_04_agent_group" }
; { req_id      = "solid-wac-05"
  ; req_source  = Src_Solid
  ; req_section = "Web Access Control §5.1 Effective ACL Resource Algorithm"
  ; req_text    = "If resource has an associated aclResource with a representation, return aclResource. Otherwise, repeat the steps using the container resource of resource."
  ; fstar_name  = "" }
; { req_id      = "solid-wac-06"
  ; req_source  = Src_Solid
  ; req_section = "Web Access Control §5.3.2 Web Origin Authorization"
  ; req_text    = "When a server participates in the CORS protocol [FETCH] and authorization is granted to an HTTP request including the Origin header, the server MUST include the HTTP Access-Control-Allow-Origin and Access-Control-Allow-Headers headers in the response of the HTTP request."
  ; fstar_name  = "" }
; { req_id      = "solid-wac-07"
  ; req_source  = Src_Solid
  ; req_section = "Web Access Control §5.3.4 Access Privileges"
  ; req_text    = "Servers MUST advertise client's access privileges on a resource by including the WAC-Allow HTTP header in the response of HTTP GET and HEAD requests."
  ; fstar_name  = "Solid.Protocol.Spec.solid_wac_07_wac_allow_header" }
; { req_id      = "solid-wac-08"
  ; req_source  = Src_Solid
  ; req_section = "Web Access Control §5.3.4 Access Privileges"
  ; req_text    = "Clients MUST discover access privileges on a resource by making an HTTP GET or HEAD request on the target resource, and checking the WAC-Allow header value for access parameters listing the allowed access modes per permission group."
  ; fstar_name  = "Solid.Protocol.Spec.solid_wac_08_client_reads_wac_allow" }
; { req_id      = "solid-wac-09"
  ; req_source  = Src_Solid
  ; req_section = "Web Access Control §3.1 ACL Resource Discovery"
  ; req_text    = "Clients MUST discover the ACL resource associated with a resource by making an HTTP request on the target URL, and checking the HTTP Link header with the rel parameter. […] Clients MUST NOT derive the URI of the ACL resource through string operations on the URI of the resource."
  ; fstar_name  = "Solid.Protocol.Spec.solid_wac_09_client_acl_from_links" }
; { req_id      = "solid-wac-10"
  ; req_source  = Src_Solid
  ; req_section = "Web Access Control §3.2 ACL Resource Representation"
  ; req_text    = "Root container ACL resources MUST have representations. The ACL resource of the root container MUST include an Authorization allowing the acl:Control access privilege."
  ; fstar_name  = "" }
; { req_id      = "solid-cl-01"
  ; req_source  = Src_Solid
  ; req_section = "Solid Protocol §4.1 Storage Resource"
  ; req_text    = "Clients can determine the storage of a resource by moving up the URI path hierarchy until the response includes a Link header field with rel=\"type\" targeting http://www.w3.org/ns/pim/space#Storage."
  ; fstar_name  = "Solid.Protocol.Spec.solid_cl_01_storage_walk_sound" }
]
(** ======================================================================= **)
(** Counting                                                                **)
(** ======================================================================= **)

let req_ident (r : requirement) : string = r.req_id

let is_lws   (r : requirement) : bool = Src_Lws?   r.req_source
let is_solid (r : requirement) : bool = Src_Solid? r.req_source
let is_stated (r : requirement) : bool = not (r.fstar_name = "")

let rec ids_unique (l : list string) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | x :: tl -> not (mem x tl) && ids_unique tl

// No identifier appears twice, so a new row cannot silently replace one.
let _ = assert_norm (ids_unique (map req_ident requirements) == true)

// The counts, fixed here so a change to the list shows up as a failure
// rather than as a number nobody read.
let _ = assert_norm (length requirements == 91)
let _ = assert_norm (length (filter is_lws   requirements) == 18)
let _ = assert_norm (length (filter is_solid requirements) == 73)
let _ = assert_norm (length (filter is_stated requirements) == 51)
