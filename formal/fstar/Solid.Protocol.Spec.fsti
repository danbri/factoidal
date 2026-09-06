module Solid.Protocol.Spec

(** ======================================================================= **)
(** The Solid Protocol as a REFINEMENT of the LWS 1.0 Core specification.   **)
(**                                                                         **)
(** Sources: https://solidproject.org/TR/protocol, version 0.11.0, modified **)
(** 2024-05-12, and https://solidproject.org/TR/wac. Both read 2026-09-06.  **)
(**                                                                         **)
(** This module imports LWS.Core.Spec and adds what Solid states on top of  **)
(** it: the storage resource and slash semantics, the correspondence        **)
(** between containment triples and the path hierarchy, auxiliary resources **)
(** and their lifetime, the method table with its status codes, N3 Patch,   **)
(** and the Web Access Control decision as a pure function.                 **)
(**                                                                         **)
(** Requirement identifiers are those of                                    **)
(** formal/lean4/L4Factoidal/Solid/Conformance.lean, so the two trees can   **)
(** be checked against one statement list. LWS.Solid.Registry holds it.     **)
(**                                                                         **)
(** Part 9 holds the CLIENT statements. Server and client are separate      **)
(** conformance classes in the specification and are kept apart here: no    **)
(** client function reads a server state, and no server function builds a   **)
(** client request.                                                         **)
(** ======================================================================= **)

open FStar.List.Tot
open LWS.Core.Spec

(** ======================================================================= **)
(** Part 1: Vocabulary                                                      **)
(** ======================================================================= **)

let iri_ldp_contains        : string = "http://www.w3.org/ns/ldp#contains"
let iri_ldp_basic_container : string = "http://www.w3.org/ns/ldp#BasicContainer"
let iri_rdf_type            : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let iri_insert_delete_patch : string = "http://www.w3.org/ns/solid/terms#InsertDeletePatch"
let iri_solid_inserts       : string = "http://www.w3.org/ns/solid/terms#inserts"
let iri_solid_deletes       : string = "http://www.w3.org/ns/solid/terms#deletes"
let iri_solid_where         : string = "http://www.w3.org/ns/solid/terms#where"
let media_n3                : string = "text/n3"
let media_turtle            : string = "text/turtle"
let media_ldjson            : string = "application/ld+json"

(** ======================================================================= **)
(** Part 2: Targets and auxiliary resources                                 **)
(** ======================================================================= **)

// Solid Protocol section 4.3. An auxiliary resource is a separate resource
// with its own URI whose lifetime is bound to a subject resource. It is not
// a contained resource, so it never appears in a containment triple; that is
// why it is held beside the LWS store rather than in it.
type aux_kind =
  | Aux_Subject
  | Aux_Acl
  | Aux_Describedby

// What a request targets: a subject resource, or one of its auxiliaries.
type target = {
  g_id  : rid;
  g_aux : aux_kind
}

(** Solid Protocol section 4.3.2 Description Resource.
    "When an HTTP request targets a description resource, the server MUST
    apply the authorization rule that is used for the subject resource with
    which the description resource is associated."
    Requirement solid-04-14: the authorization subject of any target is its
    subject resource. **)
let authorization_subject (t : target) : rid = t.g_id

let target_uri (t : target) : string =
  match t.g_aux with
  | Aux_Subject     -> rid_path t.g_id
  | Aux_Acl         -> rid_path t.g_id ^ acl_suffix
  | Aux_Describedby -> rid_path t.g_id ^ describedby_suffix

// Solid Protocol section 3.1 URI Slash Semantics: "Paths ending with a slash
// denote a container resource."
let is_container_id (r : rid) : bool = r.container

(** ======================================================================= **)
(** Part 3: Web Access Control                                              **)
(** ======================================================================= **)

type access_mode =
  | AM_Read
  | AM_Write
  | AM_Append
  | AM_Control

type agent =
  | Ag_Public
  | Ag_WebId of string

// One acl:Authorization, as the subset of Web Access Control section 4 that
// the decision of section 5.3 reads.
type authorization = {
  z_access_to   : list rid;
  z_default     : list rid;
  z_agent       : list string;
  z_agent_class : list string;
  z_agent_group : list string;
  z_mode        : list access_mode
}

// Group membership, which the ACL graph states by vcard:hasMember. The
// decision reads it; it does not compute it.
type group_index = list (string * list string)

let cls_foaf_agent          : string = "http://xmlns.com/foaf/0.1/Agent"
let cls_authenticated_agent : string = "http://www.w3.org/ns/auth/acl#AuthenticatedAgent"

let rec group_members (gi : group_index) (g : string) : Tot (list string) (decreases gi) =
  match gi with
  | [] -> []
  | (k, ms) :: tl -> if k = g then ms else group_members tl g

let agent_in_group (gi : group_index) (w : string) (g : string) : bool =
  mem w (group_members gi g)

let rec agent_in_any_group (gi : group_index) (w : string) (gs : list string) :
  Tot bool (decreases gs) =
  match gs with
  | [] -> false
  | g :: tl -> agent_in_group gi w g || agent_in_any_group gi w tl

// Web Access Control section 5.3.3 Authorization Matching, subject half.
let subject_matches (gi : group_index) (a : agent) (z : authorization) : bool =
  mem cls_foaf_agent z.z_agent_class ||
  (match a with
   | Ag_Public -> false
   | Ag_WebId w ->
     mem w z.z_agent ||
     mem cls_authenticated_agent z.z_agent_class ||
     agent_in_any_group gi w z.z_agent_group)

// Web Access Control section 3.4: acl:Write includes acl:Append.
let mode_matches (m : access_mode) (z : authorization) : bool =
  mem m z.z_mode || (AM_Append? m && mem AM_Write z.z_mode)

(** ======================================================================= **)
(** Part 4: The server state                                                **)
(** ======================================================================= **)

// The LWS store, plus what Solid adds: the ACL and description auxiliary
// resources, the group memberships the ACL decision reads, the WebID the
// host verified for this request, and whether access control is enforced.
noeq type sstate = {
  x_store   : store;
  x_acl     : list (rid * list authorization);
  x_meta    : list (rid * list rdf_triple);
  x_groups  : group_index;
  x_agent   : agent;
  x_enforce : bool
}

let rec acl_lookup (m : list (rid * list authorization)) (r : rid) :
  Tot (option (list authorization)) (decreases m) =
  match m with
  | [] -> None
  | (k, v) :: tl -> if k = r then Some v else acl_lookup tl r

let rec meta_lookup (m : list (rid * list rdf_triple)) (r : rid) :
  Tot (option (list rdf_triple)) (decreases m) =
  match m with
  | [] -> None
  | (k, v) :: tl -> if k = r then Some v else meta_lookup tl r

let acl_not_key  (r : rid) (kv : rid * list authorization) : bool = not (fst kv = r)
let meta_not_key (r : rid) (kv : rid * list rdf_triple)    : bool = not (fst kv = r)

// Web Access Control section 5.1, Effective ACL Resource Algorithm: "If
// resource has an associated aclResource with a representation, return
// aclResource. Otherwise, repeat the steps using the container resource of
// resource." The third component says whether the authorization was
// inherited, which selects acl:default over acl:accessTo.
let rec effective_acl (s : sstate) (r : rid) :
  Tot (option (rid * list authorization * bool)) (decreases (length r.segs)) =
  match acl_lookup s.x_acl r with
  | Some auths -> Some (r, auths, false)
  | None ->
    (match parent_of r with
     | None -> None
     | Some p ->
       containment_acyclic r;
       (match effective_acl s p with
        | None -> None
        | Some (o, a, _) -> Some (o, a, true)))

let authorization_grants
    (gi : group_index) (a : agent) (owner : rid) (inherited : bool)
    (m : access_mode) (z : authorization) : bool =
  (if inherited then mem owner z.z_default else mem owner z.z_access_to) &&
  subject_matches gi a z &&
  mode_matches m z

// Web Access Control section 5.3: "Access is granted when conforming
// Authorizations are matched, otherwise access is denied."
let decide_access (s : sstate) (a : agent) (r : rid) (m : access_mode) : bool =
  match effective_acl s r with
  | None -> false
  | Some (owner, auths, inherited) ->
    existsb (authorization_grants s.x_groups a owner inherited m) auths

let all_modes : list access_mode = [AM_Read; AM_Write; AM_Append; AM_Control]

let mode_token (m : access_mode) : string =
  match m with
  | AM_Read    -> "read"
  | AM_Write   -> "write"
  | AM_Append  -> "append"
  | AM_Control -> "control"

let mode_granted (s : sstate) (a : agent) (r : rid) (m : access_mode) : bool =
  decide_access s a r m

let granted_modes (s : sstate) (a : agent) (r : rid) : list access_mode =
  filter (mode_granted s a r) all_modes

let rec join_tokens (ms : list access_mode) : Tot string (decreases ms) =
  match ms with
  | [] -> ""
  | [m] -> mode_token m
  | m :: tl -> mode_token m ^ " " ^ join_tokens tl

let wac_allow_value (s : sstate) (r : rid) : string =
  "user=\"" ^ join_tokens (granted_modes s s.x_agent r) ^
  "\",public=\"" ^ join_tokens (granted_modes s Ag_Public r) ^ "\""

(** ======================================================================= **)
(** Part 5: Containment                                                     **)
(** ======================================================================= **)

// A containment statement, held over identifiers rather than over rendered
// IRIs so the correspondence of requirement solid-04-08 is a structural
// one. `container_graph` renders it.
type containment = {
  n_container : rid;
  n_child     : rid
}

let mk_containment (c : rid) (r : rid) : containment =
  { n_container = c; n_child = r }

let container_triples (s : sstate) (c : rid) : list containment =
  map (mk_containment c) (contained s.x_store c)

let render_containment (t : containment) : rdf_triple =
  { t_s = rid_path t.n_container; t_p = iri_ldp_contains; t_o = rid_path t.n_child }

let container_graph (s : sstate) (c : rid) : list rdf_triple =
  map render_containment (container_triples s c)

let is_containment_triple (c : rid) (t : rdf_triple) : bool =
  t.t_s = rid_path c && t.t_p = iri_ldp_contains

let containment_part (c : rid) (g : list rdf_triple) : list rdf_triple =
  filter (is_containment_triple c) g

// A submitted representation edits the containment triples exactly when its
// containment part is not the container's own. Solid Protocol section 5.3
// refuses such a request with 409.
let body_edits_containment (s : sstate) (c : rid) (g : list rdf_triple) : bool =
  not (containment_part c g = container_graph s c)

(** ======================================================================= **)
(** Part 6: The method table                                                **)
(** ======================================================================= **)

type http_method =
  | HM_GET
  | HM_HEAD
  | HM_OPTIONS
  | HM_POST
  | HM_PUT
  | HM_PATCH
  | HM_DELETE
  | HM_Other of string

let write_method (m : http_method) : bool = HM_POST? m || HM_PUT? m || HM_PATCH? m

// Solid Protocol section 5.3.1. The N3 Patch document, as the shape the
// specification states: a type triple, and the three cited formulae
// solid:inserts, solid:deletes and solid:where. `d_nested` records that a
// formula was nested, which section 5.3.1 refuses.
type n3_patch_doc = {
  d_type_triple : bool;
  d_inserts     : list patch_triple;
  d_deletes     : list patch_triple;
  d_where       : list patch_triple;
  d_nested      : bool
}

let n3_patch_of (d : n3_patch_doc) : patch =
  { insertions = d.d_inserts; deletions = d.d_deletes; conditions = d.d_where }

let n3_patch_valid (d : n3_patch_doc) : bool =
  d.d_type_triple && not d.d_nested && patch_well_formed (n3_patch_of d)

// Solid Protocol section 5.3.1: the operations a patch request is treated as.
let patch_operations (p : patch) : list access_mode =
  (if Cons? p.conditions then [AM_Read] else []) @
  (if Cons? p.insertions then [AM_Append] else []) @
  (if Cons? p.deletions  then [AM_Read; AM_Write] else [])

type request = {
  q_method  : http_method;
  q_target  : target;
  q_headers : list (string * string);
  q_body    : string;
  q_graph   : list rdf_triple;
  q_patch   : option n3_patch_doc;
  q_acl     : list authorization;
  q_slug    : option string
}

let rec header_value (h : list (string * string)) (n : string) :
  Tot (option string) (decreases h) =
  match h with
  | [] -> None
  | (k, v) :: tl -> if k = n then Some v else header_value tl n

// Solid Protocol section 5.4: DELETE is refused on the storage root and on
// the root's ACL resource, and the Allow field value excludes it there.
let delete_allowed (t : target) : bool =
  not (t.g_id = root && (Aux_Subject? t.g_aux || Aux_Acl? t.g_aux))

let allow_value (t : target) : string =
  if is_container_id t.g_id && Aux_Subject? t.g_aux then
    (if delete_allowed t then "OPTIONS, HEAD, GET, POST, PUT, PATCH, DELETE"
     else                    "OPTIONS, HEAD, GET, POST, PUT, PATCH")
  else
    (if delete_allowed t then "OPTIONS, HEAD, GET, PUT, PATCH, DELETE"
     else                    "OPTIONS, HEAD, GET, PUT, PATCH")

let accept_post_value  : string = "text/turtle, application/ld+json"
let accept_patch_value : string = "text/n3"
let accept_put_value   : string = "text/turtle, application/ld+json"

let post_allowed (t : target) : bool = is_container_id t.g_id && Aux_Subject? t.g_aux

// The header fields a GET, HEAD or OPTIONS response carries beyond the LWS
// ones. Accept-Post appears exactly where Allow lists POST, which is what
// requirement solid-05-05 asks for.
let read_headers (s : sstate) (t : target) : list (string * string) =
  [ ("allow",        allow_value t);
    ("accept-patch", accept_patch_value);
    ("accept-put",   accept_put_value);
    ("wac-allow",    wac_allow_value s (authorization_subject t)) ]
  @ (if post_allowed t then [ ("accept-post", accept_post_value) ] else [])

(** ======================================================================= **)
(** Part 7: The step function                                               **)
(** ======================================================================= **)

let refuse (code : nat) : response = { status = code; headers = []; body = "" }

let container_resource : resource = {
  r_kind         = RK_Container;
  r_content_type = media_turtle;
  r_content      = "";
  r_graph        = [];
  r_modified     = 0
}

let resource_of (q : request) : resource = {
  r_kind         = (if is_container_id q.q_target.g_id then RK_Container else RK_DataResource);
  r_content_type = (match header_value q.q_headers "content-type" with
                    | Some c -> c | None -> media_turtle);
  r_content      = q.q_body;
  r_graph        = q.q_graph;
  r_modified     = 0
}

let target_exists (s : sstate) (t : target) : bool =
  match t.g_aux with
  | Aux_Subject     -> exists_res s.x_store t.g_id
  | Aux_Acl         -> Some? (acl_lookup s.x_acl t.g_id)
  | Aux_Describedby -> Some? (meta_lookup s.x_meta t.g_id)

// Solid Protocol section 5.3: "Servers MUST create intermediate containers
// and include corresponding containment triples in container representations
// derived from the URI path component of PUT and PATCH requests."
let ensure_parent (s : sstate) (r : rid) : sstate =
  match parent_of r with
  | None -> s
  | Some p ->
    if exists_res s.x_store p then s
    else { s with x_store = create_res s.x_store p container_resource }

let put_target (s : sstate) (q : request) : sstate =
  match q.q_target.g_aux with
  | Aux_Subject ->
    if exists_res s.x_store q.q_target.g_id
    then { s with x_store = update_res s.x_store q.q_target.g_id (resource_of q) }
    else { s with x_store = create_res s.x_store q.q_target.g_id (resource_of q) }
  | Aux_Acl ->
    { s with x_acl = (q.q_target.g_id, q.q_acl) :: filter (acl_not_key q.q_target.g_id) s.x_acl }
  | Aux_Describedby ->
    { s with x_meta = (q.q_target.g_id, q.q_graph) :: filter (meta_not_key q.q_target.g_id) s.x_meta }

// Solid Protocol section 4.3: "When a subject resource is deleted its
// auxiliary resources are also deleted by the server."
let delete_target (s : sstate) (t : target) : sstate =
  match t.g_aux with
  | Aux_Subject ->
    { s with x_store = delete_res s.x_store t.g_id;
             x_acl   = filter (acl_not_key t.g_id) s.x_acl;
             x_meta  = filter (meta_not_key t.g_id) s.x_meta }
  | Aux_Acl         -> { s with x_acl  = filter (acl_not_key t.g_id) s.x_acl }
  | Aux_Describedby -> { s with x_meta = filter (meta_not_key t.g_id) s.x_meta }

// Solid Protocol section 5.3: a POST to a container creates a resource with
// a server-assigned name in that container.
let assigned_name (s : sstate) (slug : option string) : string =
  match slug with
  | Some x -> x
  | None -> "r" ^ string_of_int (clock_of s.x_store)

let assigned_rid (s : sstate) (c : rid) (slug : option string) : rid =
  { segs = c.segs @ [ assigned_name s slug ]; container = false }

let step (s : sstate) (q : request) : Tot (response * sstate) =
  // Solid Protocol section 2.1: content without a Content-Type is refused
  // with 400 before anything else is decided.
  if write_method q.q_method && q.q_body <> "" &&
     None? (header_value q.q_headers "content-type")
  then (refuse 400, s)
  else match q.q_method with
  | HM_Other _ ->
    ({ status = 405; headers = [ ("allow", allow_value q.q_target) ]; body = "" }, s)
  | HM_OPTIONS ->
    ({ status = 204; headers = read_headers s q.q_target; body = "" }, s)
  | HM_GET ->
    // The server generated fields come first, so a client reading one of
    // them by name reads this table and not the stored representation's.
    let base = get_res s.x_store q.q_target.g_id in
    ({ base with headers = read_headers s q.q_target @ base.headers }, s)
  | HM_HEAD ->
    let base = head_res s.x_store q.q_target.g_id in
    ({ base with headers = read_headers s q.q_target @ base.headers }, s)
  | HM_DELETE ->
    if not (delete_allowed q.q_target) then
      ({ status = 405; headers = [ ("allow", allow_value q.q_target) ]; body = "" }, s)
    else if not (target_exists s q.q_target) then (refuse 404, s)
    else if is_container_id q.q_target.g_id && Aux_Subject? q.q_target.g_aux &&
            Cons? (contained s.x_store q.q_target.g_id) then (refuse 409, s)
    else (refuse 204, delete_target s q.q_target)
  | HM_POST ->
    if not (post_allowed q.q_target) then
      ({ status = 405; headers = [ ("allow", allow_value q.q_target) ]; body = "" }, s)
    else if not (exists_res s.x_store q.q_target.g_id) then (refuse 404, s)
    else
      let r = assigned_rid s q.q_target.g_id q.q_slug in
      ({ status = 201; headers = [ ("location", rid_path r) ]; body = "" },
       { s with x_store = create_res s.x_store r (resource_of q) })
  | HM_PUT ->
    if is_container_id q.q_target.g_id && Aux_Subject? q.q_target.g_aux &&
       body_edits_containment s q.q_target.g_id q.q_graph
    then (refuse 409, s)
    else
      let existed = target_exists s q.q_target in
      let s2 = put_target (ensure_parent s q.q_target.g_id) q in
      ((if existed then refuse 204
        else { status = 201; headers = [ ("location", target_uri q.q_target) ]; body = "" }), s2)
  | HM_PATCH ->
    (match q.q_patch with
     | None -> (refuse 415, s)
     | Some d ->
       if not (n3_patch_valid d) then (refuse 422, s)
       else if not (exists_res s.x_store q.q_target.g_id) then (refuse 404, s)
       else if is_container_id q.q_target.g_id &&
               body_edits_containment s q.q_target.g_id q.q_graph then (refuse 409, s)
       else
         let (resp, st2) = apply_patch s.x_store q.q_target.g_id (n3_patch_of d) in
         (resp, { s with x_store = st2 }))

(** ======================================================================= **)
(** Part 8: The server statements                                           **)
(** ======================================================================= **)

(** Solid Protocol section 2.1 HTTP Server.
    "Server MUST reject PUT, POST, and PATCH requests that contain content
    but lack the Content-Type header field, with a status code of 400."
    Requirement solid-02-02. **)
val solid_02_02_content_type_required (s : sstate) (q : request) :
  Lemma (requires write_method q.q_method /\ q.q_body =!= "" /\
                  None? (header_value q.q_headers "content-type"))
        (ensures  (fst (step s q)).status == 400 /\ snd (step s q) == s)

(** Solid Protocol section 3.1 URI Slash Semantics.
    "Paths ending with a slash denote a container resource."
    Requirement solid-03-01. Stated as: the slash flag of an identifier and
    its rendered path agree, and a parent is always a container. **)
val solid_03_01_slash_denotes_container (r : rid) :
  Lemma (requires Some? (parent_of r))
        (ensures  is_container_id (Some?.v (parent_of r)))

(** Solid Protocol section 3.1 URI Slash Semantics.
    "If two URIs differ only in the trailing slash, and the server has
    associated a resource with one of them, then the other URI MUST NOT
    correspond to another resource."
    Requirement solid-03-02. Stated as: the two identifiers that differ only
    in the slash flag are distinct identifiers, so a store that holds one and
    a redirect for the other never holds two resources. **)
val solid_03_02_slash_pair_distinct (r : rid) :
  Lemma (r =!= ({ r with container = not r.container }))

(** Solid Protocol section 4.1 Storage Resource.
    "Servers MUST advertise the storage resource by including the HTTP Link
    header field with rel=\"type\" targeting
    http://www.w3.org/ns/pim/space#Storage when responding to storage's
    request URI."
    Requirement solid-04-03. **)
val solid_04_03_storage_type_link (st : store) :
  Lemma (mem ({ l_target = iri_pim_storage; l_rel = rel_type })
             (discovery_links st root))

(** Solid Protocol section 4.1 Storage Resource.
    "When a server wants to advertise the owner of a storage, the server MUST
    include the Link header field with
    rel=\"http://www.w3.org/ns/solid/terms#owner\" targeting the URI of the
    owner in the response of HTTP HEAD or GET requests targeting the root
    container."
    Requirement solid-04-07. **)
val solid_04_07_owner_link (st : store) (o : string) :
  Lemma (requires owner_of st == Some o)
        (ensures  mem ({ l_target = o; l_rel = rel_owner })
                      (discovery_links st root))

(** Solid Protocol section 4.1 Storage Resource.
    "Servers MUST include the Link header field with
    rel=\"http://www.w3.org/ns/solid/terms#storageDescription\" targeting the
    URI of the storage description resource in the response of HTTP GET, HEAD
    and OPTIONS requests targeting a resource in a storage."
    Requirement solid-04-04. **)
val solid_04_04_storage_description_link (st : store) (r : rid) :
  Lemma (requires Some? (lookup st r))
        (ensures  has_rel rel_storage_description (discovery_links st r))

(** Solid Protocol section 4.2 Resource Containment.
    "There is a 1-1 correspondence between containment triples and relative
    reference within the path name hierarchy."
    Requirement solid-04-08, first half: a containment statement holds for a
    container and a child exactly when the child is in the container's
    enumeration. **)
val solid_04_08_containment_iff_enumerated (s : sstate) (c r : rid) :
  Lemma (mem (mk_containment c r) (container_triples s c) <==>
         mem r (contained s.x_store c))

(** Solid Protocol section 4.2 Resource Containment.
    "There is a 1-1 correspondence between containment triples and relative
    reference within the path name hierarchy."
    Requirement solid-04-08, second half: a containment statement holds only
    for a direct child in the path hierarchy. **)
val solid_04_08_containment_is_hierarchy (s : sstate) (c r : rid) :
  Lemma (requires mem (mk_containment c r) (container_triples s c))
        (ensures  parent_of r == Some c)

(** Solid Protocol section 4.3 Auxiliary Resources.
    "Servers MUST support auxiliary resources defined by this specification
    and manage the association between a subject resource and auxiliary
    resources. When a subject resource is deleted its auxiliary resources are
    also deleted by the server."
    Requirements solid-04-11 and solid-05-26. **)
val solid_04_11_auxiliaries_deleted_with_subject (s : sstate) (t : target) :
  Lemma (requires Aux_Subject? t.g_aux)
        (ensures  (let s2 = delete_target s t in
                   None? (acl_lookup s2.x_acl t.g_id) /\
                   None? (meta_lookup s2.x_meta t.g_id)))

(** Solid Protocol section 4.3 Auxiliary Resources.
    "Servers MUST advertise auxiliary resources associated with a subject
    resource by responding to HEAD and GET requests by including the HTTP
    Link header field with the rel parameter [RFC8288]."
    Requirement solid-04-12. **)
val solid_04_12_auxiliary_links_advertised (st : store) (r : rid) :
  Lemma (requires Some? (lookup st r))
        (ensures  has_rel rel_acl (discovery_links st r) /\
                  has_rel rel_describedby (discovery_links st r))

(** Solid Protocol section 4.3.2 Description Resource.
    "Servers MUST NOT directly associate more than one description resource
    to a subject resource."
    Requirement solid-04-13: the description resource of a subject is given
    by a lookup, so a subject has at most one. **)
val solid_04_13_at_most_one_description (s : sstate) (r : rid)
                                        (g1 g2 : list rdf_triple) :
  Lemma (requires meta_lookup s.x_meta r == Some g1 /\
                  meta_lookup s.x_meta r == Some g2)
        (ensures  g1 == g2)

(** Solid Protocol section 4.3.2 Description Resource.
    "When an HTTP request targets a description resource, the server MUST
    apply the authorization rule that is used for the subject resource with
    which the description resource is associated."
    Requirement solid-04-14. **)
val solid_04_14_description_authorized_as_subject (r : rid) :
  Lemma (authorization_subject ({ g_id = r; g_aux = Aux_Describedby }) ==
         authorization_subject ({ g_id = r; g_aux = Aux_Subject }))

(** Solid Protocol section 5 Reading and Writing Resources.
    "Servers MUST respond with the 405 status code to requests using HTTP
    methods that are not supported by the target resource."
    Requirement solid-05-01. **)
val solid_05_01_unsupported_method_405 (s : sstate) (q : request) :
  Lemma (requires HM_Other? q.q_method)
        (ensures  (fst (step s q)).status == 405 /\
                  has_header "allow" (fst (step s q)))

(** Solid Protocol section 5.1 Resource Type Heuristics.
    "When a successful POST request creates a resource, the server MUST
    assign a URI to that resource."
    Requirement solid-05-02, with section 5.3: "Servers MUST create resources
    with URI paths ending with /{id} in container /." (solid-05-08). **)
val solid_05_02_post_assigns_uri (s : sstate) (q : request) :
  Lemma (requires q.q_method == HM_POST /\ post_allowed q.q_target /\
                  exists_res s.x_store q.q_target.g_id /\
                  (q.q_body == "" \/ Some? (header_value q.q_headers "content-type")))
        (ensures  (let (resp, s2) = step s q in
                   let r = assigned_rid s q.q_target.g_id q.q_slug in
                   resp.status == 201 /\ has_header "location" resp /\
                   parent_of r == Some q.q_target.g_id /\
                   exists_res s2.x_store r))

(** Solid Protocol section 5.2 Reading Resources.
    "Servers MUST indicate the HTTP methods supported by the target resource
    by generating an Allow header field in successful responses."
    Requirement solid-05-04. **)
val solid_05_04_allow_header (s : sstate) (q : request) :
  Lemma (requires q.q_method == HM_OPTIONS)
        (ensures  has_header "allow" (fst (step s q)))

(** Solid Protocol section 5.2 Reading Resources.
    "When responding to authorized requests, servers MUST indicate supported
    media types in the HTTP Accept-Patch [RFC5789], Accept-Post [LDP] and
    Accept-Put [The Accept-Put Response Header] response header fields that
    correspond to acceptable HTTP methods listed in Allow header field value
    in response to HTTP GET, HEAD and OPTIONS requests."
    Requirement solid-05-05, with section 5.3.1: "Servers MUST indicate
    support of N3 Patch by listing text/n3 as a field value of the
    Accept-Patch header field" (solid-05-14). **)
val solid_05_05_accept_headers (s : sstate) (q : request) :
  Lemma (requires q.q_method == HM_OPTIONS /\ post_allowed q.q_target)
        (ensures  (let resp = fst (step s q) in
                   has_header "accept-patch" resp /\
                   has_header "accept-put" resp /\
                   has_header "accept-post" resp /\
                   header_value resp.headers "accept-patch" == Some media_n3))

(** Solid Protocol section 5.3 Writing Resources.
    "Servers MUST create intermediate containers and include corresponding
    containment triples in container representations derived from the URI
    path component of PUT and PATCH requests."
    Requirement solid-05-07. Stated for the direct parent of the target. **)
val solid_05_07_intermediate_container (s : sstate) (q : request) :
  Lemma (requires q.q_method == HM_PUT /\ Aux_Subject? q.q_target.g_aux /\
                  Some? (parent_of q.q_target.g_id) /\
                  (q.q_body == "" \/ Some? (header_value q.q_headers "content-type")) /\
                  (is_container_id q.q_target.g_id &&
                   body_edits_containment s q.q_target.g_id q.q_graph) == false)
        (ensures  exists_res (snd (step s q)).x_store
                             (Some?.v (parent_of q.q_target.g_id)))

(** Solid Protocol section 5.3 Writing Resources.
    "When a POST method request targets a resource without an existing
    representation, the server MUST respond with the 404 status code."
    Requirement solid-05-09. **)
val solid_05_09_post_missing_target_404 (s : sstate) (q : request) :
  Lemma (requires q.q_method == HM_POST /\ post_allowed q.q_target /\
                  ~ (exists_res s.x_store q.q_target.g_id) /\
                  (q.q_body == "" \/ Some? (header_value q.q_headers "content-type")))
        (ensures  (fst (step s q)).status == 404 /\ snd (step s q) == s)

(** Solid Protocol section 5.3 Writing Resources.
    "Servers MUST NOT allow HTTP PUT or PATCH on a container to update its
    containment triples; if the server receives such a request, it MUST
    respond with a 409 status code."
    Requirement solid-05-11. **)
val solid_05_11_containment_edit_409 (s : sstate) (q : request) :
  Lemma (requires q.q_method == HM_PUT /\ Aux_Subject? q.q_target.g_aux /\
                  is_container_id q.q_target.g_id /\
                  body_edits_containment s q.q_target.g_id q.q_graph /\
                  (q.q_body == "" \/ Some? (header_value q.q_headers "content-type")))
        (ensures  (fst (step s q)).status == 409 /\ snd (step s q) == s)

(** Solid Protocol section 5.3.1 Modifying Resources Using N3 Patches.
    "Servers MUST accept a PATCH request with an N3 Patch body when the
    target of the request is an RDF document [RDF11-CONCEPTS]."
    Requirement solid-05-13: a valid N3 Patch on an existing resource is
    neither refused as an unsupported media type nor as ill formed. **)
val solid_05_13_n3_patch_accepted (s : sstate) (q : request) (d : n3_patch_doc) :
  Lemma (requires q.q_method == HM_PATCH /\ q.q_patch == Some d /\
                  n3_patch_valid d /\ exists_res s.x_store q.q_target.g_id /\
                  is_container_id q.q_target.g_id == false /\
                  (q.q_body == "" \/ Some? (header_value q.q_headers "content-type")))
        (ensures  (fst (step s q)).status <> 415 /\
                  (fst (step s q)).status <> 422 /\
                  (fst (step s q)).status <> 405)

(** Solid Protocol section 5.3.1 Modifying Resources Using N3 Patches.
    "The ?insertions and ?deletions formulae MUST NOT contain blank nodes."
    Requirement solid-05-18, and "A patch resource MUST contain a triple
    ?patch rdf:type solid:InsertDeletePatch" (solid-05-16), and "Servers MUST
    respond with a 422 status code [RFC4918] if a patch document does not
    satisfy all of the above constraints" (solid-05-19). **)
val solid_05_19_ill_formed_patch_422 (s : sstate) (q : request) (d : n3_patch_doc) :
  Lemma (requires q.q_method == HM_PATCH /\ q.q_patch == Some d /\
                  n3_patch_valid d == false /\
                  (q.q_body == "" \/ Some? (header_value q.q_headers "content-type")))
        (ensures  (fst (step s q)).status == 422 /\ snd (step s q) == s)

(** Solid Protocol section 5.3.1 Modifying Resources Using N3 Patches.
    "When ?conditions is non-empty, servers MUST treat the request as a Read
    operation. When ?insertions is non-empty, servers MUST (also) treat the
    request as an Append operation. When ?deletions is non-empty, servers
    MUST treat the request as a Read and Write operation."
    Requirement solid-05-20. **)
val solid_05_20_patch_operations (p : patch) :
  Lemma (ensures (Cons? p.conditions ==> mem AM_Read   (patch_operations p)) /\
                 (Cons? p.insertions ==> mem AM_Append (patch_operations p)) /\
                 (Cons? p.deletions  ==> mem AM_Read   (patch_operations p) /\
                                         mem AM_Write  (patch_operations p)))

(** Solid Protocol section 5.4 Deleting Resources.
    "When a DELETE request targets storage's root container or its associated
    ACL resource, the server MUST respond with the 405 status code. Server
    MUST exclude the DELETE method in the field value of the Allow header
    field, in response to requests to these resources."
    Requirement solid-05-24. **)
val solid_05_24_delete_root_405 (s : sstate) (q : request) :
  Lemma (requires q.q_method == HM_DELETE /\ q.q_target.g_id == root /\
                  ~ (Aux_Describedby? q.q_target.g_aux))
        (ensures  (fst (step s q)).status == 405 /\ snd (step s q) == s /\
                  has_header "allow" (fst (step s q)) /\
                  delete_allowed q.q_target == false)

(** Solid Protocol section 5.4 Deleting Resources.
    "When a contained resource is deleted, the server MUST also remove the
    corresponding containment triple."
    Requirement solid-05-25. **)
val solid_05_25_delete_removes_containment (s : sstate) (t : target) (c : rid) :
  Lemma (requires Aux_Subject? t.g_aux /\ t.g_id =!= root)
        (ensures  ~ (mem (mk_containment c t.g_id)
                         (container_triples (delete_target s t) c)))

(** Solid Protocol section 5.4 Deleting Resources.
    "When a DELETE request targets a container, the server MUST delete the
    container if it contains no resources. If the container contains
    resources, the server MUST respond with the 409 status code."
    Requirement solid-05-27. **)
val solid_05_27_delete_non_empty_container_409 (s : sstate) (q : request) :
  Lemma (requires q.q_method == HM_DELETE /\ Aux_Subject? q.q_target.g_aux /\
                  is_container_id q.q_target.g_id /\
                  delete_allowed q.q_target /\
                  target_exists s q.q_target /\
                  Cons? (contained s.x_store q.q_target.g_id))
        (ensures  (fst (step s q)).status == 409 /\ snd (step s q) == s)

(** Web Access Control section 5.3 Authorization Evaluation.
    "Access is granted when conforming Authorizations are matched, otherwise
    access is denied."
    Requirement solid-wac-01, denial half: a resource with no effective ACL
    grants nothing. **)
val solid_wac_01_no_acl_denies (s : sstate) (a : agent) (r : rid) (m : access_mode) :
  Lemma (requires None? (effective_acl s r))
        (ensures  decide_access s a r m == false)

(** Web Access Control section 5.3.3 Authorization Matching.
    "Match an Authorization with a specific resource, agent and access mode."
    Requirement solid-wac-02: an authorization grants exactly when it names
    the resource, matches the agent and carries the mode. **)
val solid_wac_02_match_resource_agent_mode
    (gi : group_index) (a : agent) (owner : rid) (m : access_mode) (z : authorization) :
  Lemma (authorization_grants gi a owner false m z <==>
         (mem owner z.z_access_to /\ subject_matches gi a z /\ mode_matches m z))

(** Web Access Control section 5.3.3 Authorization Matching.
    "Match an Authorization with a specific container resource, agent class
    membership and access mode."
    Requirement solid-wac-03: an inherited authorization is read from
    acl:default, not acl:accessTo. **)
val solid_wac_03_default_is_inherited
    (gi : group_index) (a : agent) (owner : rid) (m : access_mode) (z : authorization) :
  Lemma (authorization_grants gi a owner true m z <==>
         (mem owner z.z_default /\ subject_matches gi a z /\ mode_matches m z))

(** Web Access Control section 5.3.3 Authorization Matching.
    "Match an Authorization with a specific resource, agent with any group
    membership, and specific access mode."
    Requirement solid-wac-04. **)
val solid_wac_04_agent_group (gi : group_index) (w g : string) (z : authorization) :
  Lemma (requires mem g z.z_agent_group /\ mem w (group_members gi g))
        (ensures  subject_matches gi (Ag_WebId w) z)

(** Web Access Control section 5.3.4 Access Privileges.
    "Servers MUST advertise client's access privileges on a resource by
    including the WAC-Allow HTTP header in the response of HTTP GET and HEAD
    requests."
    Requirement solid-wac-07. **)
val solid_wac_07_wac_allow_header (s : sstate) (q : request) :
  Lemma (requires (q.q_method == HM_GET \/ q.q_method == HM_HEAD) /\
                  Some? (lookup s.x_store q.q_target.g_id))
        (ensures  has_header "wac-allow" (fst (step s q)))

(** ======================================================================= **)
(** Part 9: The CLIENT statements                                           **)
(**                                                                         **)
(** A separate conformance class. Nothing below reads a server state.       **)
(** ======================================================================= **)

type client_request = {
  k_method  : http_method;
  k_uri     : string;
  k_headers : list (string * string);
  k_body    : string
}

let client_build (m : http_method) (uri : string) (ct : option string) (body : string) :
  Pure client_request
    (requires (write_method m && body <> "") ==> Some? ct)
    (ensures fun r -> r.k_method == m /\ r.k_uri == uri /\ r.k_body == body) =
  { k_method  = m;
    k_uri     = uri;
    k_headers = (match ct with Some c -> [ ("content-type", c) ] | None -> []);
    k_body    = body }

let rec link_target_for (rel : string) (ls : list link) :
  Tot (option string) (decreases ls) =
  match ls with
  | [] -> None
  | l :: tl -> if l.l_rel = rel then Some l.l_target else link_target_for rel tl

// Web Access Control section 3.1: the client reads the ACL URI from the Link
// header field. There is no function here from a resource URI to an ACL URI,
// which is the point of the statement.
let client_acl_uri (ls : list link) : option string = link_target_for rel_acl ls

let client_wac_allow (resp : response) : option string =
  header_value resp.headers "wac-allow"

let is_storage_type_link (l : link) : bool =
  l.l_rel = rel_type && l.l_target = iri_pim_storage

let has_type_storage (ls : list link) : bool = existsb is_storage_type_link ls

// Solid Protocol section 4.1: "Clients can determine the storage of a
// resource by moving up the URI path hierarchy until the response includes a
// Link header field with rel="type" targeting
// http://www.w3.org/ns/pim/space#Storage."
let rec client_storage_walk (probe : rid -> list link) (r : rid) :
  Tot (option rid) (decreases (length r.segs)) =
  if has_type_storage (probe r) then Some r
  else match parent_of r with
       | None -> None
       | Some p -> containment_acyclic r; client_storage_walk probe p

(** Solid Protocol section 2.2 HTTP Client.
    "Clients MUST use the Content-Type HTTP header field in PUT, POST, and
    PATCH requests that contain content [RFC9110]."
    Requirement solid-02-06. **)
val solid_02_06_client_content_type
    (m : http_method) (uri : string) (ct : option string) (body : string) :
  Lemma (requires (write_method m && body <> "") ==> Some? ct)
        (ensures  (write_method m && body <> "") ==>
                  Some? (header_value (client_build m uri ct body).k_headers "content-type"))

(** Web Access Control section 3.1 ACL Resource Discovery.
    "Clients MUST discover the ACL resource associated with a resource by
    making an HTTP request on the target URL, and checking the HTTP Link
    header with the rel parameter. [...] Clients MUST NOT derive the URI of
    the ACL resource through string operations on the URI of the resource."
    Requirement solid-wac-09: the client answers an ACL URI only when the
    links carry one, and the answer is one of those link targets. **)
val solid_wac_09_client_acl_from_links (ls : list link) :
  Lemma (Some? (client_acl_uri ls) <==> has_rel rel_acl ls)

(** Web Access Control section 5.3.4 Access Privileges.
    "Clients MUST discover access privileges on a resource by making an HTTP
    GET or HEAD request on the target resource, and checking the WAC-Allow
    header value for access parameters listing the allowed access modes per
    permission group."
    Requirement solid-wac-08: the value the client reads is the value the
    server wrote for that resource. **)
val solid_wac_08_client_reads_wac_allow (s : sstate) (q : request) :
  Lemma (requires q.q_method == HM_HEAD /\ Some? (lookup s.x_store q.q_target.g_id))
        (ensures  client_wac_allow (fst (step s q)) ==
                  Some (wac_allow_value s (authorization_subject q.q_target)))

(** Solid Protocol section 4.1 Storage Resource.
    "Clients can determine the storage of a resource by moving up the URI
    path hierarchy until the response includes a Link header field with
    rel=\"type\" targeting http://www.w3.org/ns/pim/space#Storage."
    Requirement solid-cl-01: the walk answers an identifier only when that
    identifier itself advertises the storage type link. **)
val solid_cl_01_storage_walk_sound (probe : rid -> list link) (r c : rid) :
  Lemma (requires client_storage_walk probe r == Some c)
        (ensures  has_type_storage (probe c))
