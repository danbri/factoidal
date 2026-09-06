module LWS.Core.Spec

(** ======================================================================= **)
(** Linked Web Storage Protocol 1.0 Core - the SPECIFICATION side.          **)
(**                                                                         **)
(** Source: https://w3c.github.io/lws-protocol/lws10-core/                  **)
(** W3C Linked Web Storage Working Group editor's draft, read 2026-09-06.   **)
(**                                                                         **)
(** This module states the draft's normative statements over an ABSTRACT    **)
(** resource store. The store type is opaque here; LWS.Core.Spec.fst gives  **)
(** one model of it and discharges every law below, so the statements are   **)
(** known to be consistent. A different backend may instantiate the same    **)
(** interface.                                                              **)
(**                                                                         **)
(** The same statement list is carried by the Lean tree in                  **)
(** formal/lean4/L4Factoidal/LWS/Conformance.lean, with the same            **)
(** requirement identifiers "lws-core-NN". LWS.Solid.Registry lists both     **)
(** sides.                                                                  **)
(**                                                                         **)
(** The draft's Operations, Containers, Discovery, Authentication and       **)
(** Authorization sections are headings with empty bodies, so the draft     **)
(** states no HTTP binding and no status codes. Where a statement below     **)
(** needs a binding, the Solid Protocol v0.11.0 binding is used and the     **)
(** doc comment says "LWS todo, Solid section N binding".                   **)
(**                                                                         **)
(** Dependencies are the F* prelude and FStar.List.Tot only, so this        **)
(** module verifies on its own.                                             **)
(** ======================================================================= **)

open FStar.List.Tot

(** ======================================================================= **)
(** Part 1: Resource identifiers and the containment hierarchy              **)
(** ======================================================================= **)

// A resource identifier is a path within one storage: a list of path
// segments, plus the slash flag of Solid Protocol section 3.1 ("Paths
// ending with a slash denote a container resource"). The storage root is
// the empty segment list with the flag set.
type rid = {
  segs      : list string;
  container : bool
}

let root : rid = { segs = []; container = true }

// The parent path: all segments but the last. Total, and always a
// container.
let rec init_segs (l : list string) : list string =
  match l with
  | [] -> []
  | [_] -> []
  | x :: tl -> x :: init_segs tl

let parent_of (r : rid) : option rid =
  match r.segs with
  | [] -> None
  | _  -> Some ({ segs = init_segs r.segs; container = true })

// Containment as a relation. `contains_child c r` holds exactly when r is a
// direct child of c.
let contains_child (c r : rid) : bool = parent_of r = Some c

(** LWS core, Terminology.
    "storage root - a container at the root of a containment hierarchy of a
    storage. The storage root is the only LWS resource that does not have a
    parent in the LWS containment hierarchy nor a primary resource."
    Requirement lws-core-06, first half: the root has no parent. **)
val lws_core_06_root_has_no_parent : unit ->
  Lemma (parent_of root == None)

(** LWS core, Terminology. Requirement lws-core-06, second half: the root is
    the ONLY identifier without a parent. **)
val lws_core_06_only_root_has_no_parent (r : rid) :
  Lemma (requires parent_of r == None)
        (ensures  r.segs == [])

(** The containment hierarchy is acyclic: a parent is strictly shorter than
    its child, so no identifier reaches itself by repeated parent steps.
    Implied by the draft's word "hierarchy" in the lws-core-06 definition. **)
val containment_acyclic (r : rid) :
  Lemma (requires Some? (parent_of r))
        (ensures  length ((Some?.v (parent_of r)).segs) < length r.segs)

(** Single parent: `contains_child` relates each identifier to at most one
    container. Implied by the same definition. **)
val containment_single_parent (c1 c2 r : rid) :
  Lemma (requires contains_child c1 r /\ contains_child c2 r)
        (ensures  c1 == c2)

(** ======================================================================= **)
(** Part 2: Resource kinds, resources, responses                            **)
(** ======================================================================= **)

// LWS core, Terminology: LWS resource, container, data resource, storage
// root, metadata resource (auxiliary), linkset resource (auxiliary,
// RFC 9264).
type resource_kind =
  | RK_StorageRoot
  | RK_Container
  | RK_DataResource
  | RK_MetadataResource
  | RK_LinksetResource

// A ground RDF triple. Subject, predicate and object are held as strings:
// an IRI, or the lexical form of a literal. The LWS statements this module
// carries never inspect a term's structure, so a richer term type would add
// nothing here. RDF.Term is the project's term type for engines that do.
type rdf_triple = {
  t_s : string;
  t_p : string;
  t_o : string
}

// The stored state of one resource. `content` is what the host holds as
// bytes; `graph` is the RDF interpretation used by PATCH. A non-RDF data
// resource has an empty graph.
type resource = {
  r_kind         : resource_kind;
  r_content_type : string;
  r_content      : string;
  r_graph        : list rdf_triple;
  r_modified     : nat
}

// An HTTP response, reduced to what the statements constrain: a status
// code, header fields as name and value pairs with lower-case names, and a
// body.
type response = {
  status  : nat;
  headers : list (string * string);
  body    : string
}

let header_names (resp : response) : list string = map fst resp.headers
let has_header (name : string) (resp : response) : bool = mem name (header_names resp)

// An RFC 8288 web link.
type link = {
  l_target : string;
  l_rel    : string
}

let rel_is (rel : string) (l : link) : bool = l.l_rel = rel
let has_rel (rel : string) (ls : list link) : bool = existsb (rel_is rel) ls

// Link relation names used by the discovery statements. The relations
// themselves are Solid Protocol section 4.1 and 4.3; the LWS draft says
// auxiliary resources are discovered "using web links [RFC8288] of a
// specific type (see Section )" and leaves the section reference empty.
let rel_type                : string = "type"
let rel_acl                 : string = "acl"
let rel_describedby         : string = "describedby"
let rel_storage_description : string = "http://www.w3.org/ns/solid/terms#storageDescription"
let rel_owner               : string = "http://www.w3.org/ns/solid/terms#owner"
let iri_pim_storage         : string = "http://www.w3.org/ns/pim/space#Storage"

(** ======================================================================= **)
(** Part 3: The abstract store                                              **)
(** ======================================================================= **)

// The store is opaque. Its only observers are the four functions below.
val store : Type0

val lookup        : store -> rid -> option resource
val contained     : store -> rid -> list rid
val last_modified : store -> rid -> option nat
val clock_of      : store -> nat
val owner_of      : store -> option string

let exists_res (s : store) (r : rid) : bool = Some? (lookup s r)

// A storage with a root container and nothing else, whose clock starts at
// `t0` and whose owner is `own`.
val empty_store : (t0 : nat) -> (own : option string) -> store

(** ======================================================================= **)
(** Part 4: The four operations                                             **)
(** ======================================================================= **)

// LWS core, Resource Access: "An operation is any of the following actions
// that can be performed on a served resource: create resource, read
// resource, update resource, delete resource."
type operation =
  | Op_Create
  | Op_Read
  | Op_Update
  | Op_Delete

// Create. Post-condition: the resource is stored, it is stamped with the
// store clock, and the clock advances so a later write is strictly later.
val create_res (s : store) (r : rid) (res : resource) :
  Tot (t : store {
    Some? (lookup t r) /\
    last_modified t r == Some (clock_of s) /\
    clock_of t > clock_of s })

// Update. Same post-condition on the modification time; the identifier must
// already exist, which is the caller's obligation.
val update_res (s : store) (r : rid) (res : resource) :
  Tot (t : store {
    Some? (lookup t r) /\
    last_modified t r == Some (clock_of s) /\
    clock_of t > clock_of s })

// Delete. Post-condition: the identifier is gone, unless it is the storage
// root, which this operation never removes (see lws_core_root_not_deleted).
val delete_res (s : store) (r : rid) :
  Tot (t : store { r =!= root ==> None? (lookup t r) })

let rec join_segs (l : list string) : Tot string (decreases l) =
  match l with
  | [] -> ""
  | x :: tl -> "/" ^ x ^ join_segs tl

let rid_path (r : rid) : string =
  let b = join_segs r.segs in
  if r.container then (if b = "" then "/" else b ^ "/") else b

// The suffixes below are this model's choice of auxiliary-resource paths.
// Solid Protocol section 4.3 leaves the URI of an auxiliary resource to the
// server and requires only that it is advertised by a link, which is what
// requirement lws-core-08 and solid-04-12 state; a client that derives the
// path by string operations is refused by requirement solid-wac-09.
let acl_suffix          : string = ".acl"
let describedby_suffix  : string = ".meta"
let storage_description : string = "/.storage-description"

// The links a response advertises for one identifier.
val discovery_links : store -> rid -> list link

// Read. The response of a GET, and of a HEAD, which is the same response
// with an empty body.
val get_res  : store -> rid -> response
val head_res : store -> rid -> response

(** ======================================================================= **)
(** Part 5: The statements                                                  **)
(** ======================================================================= **)

(** LWS core, For Editors (CG-to-ED delta).
    "HTTP Server MUST generate a Last-Modified header field in response to
    GET and HEAD requests."
    Requirement lws-core-03, GET half. No binding is needed: the statement
    names the HTTP header field itself. **)
val lws_core_03_last_modified_on_get (s : store) (r : rid) :
  Lemma (requires Some? (lookup s r))
        (ensures  (get_res s r).status == 200 /\ has_header "last-modified" (get_res s r))

(** LWS core, For Editors (CG-to-ED delta).
    "HTTP Server MUST generate a Last-Modified header field in response to
    GET and HEAD requests."
    Requirement lws-core-03, HEAD half. **)
val lws_core_03_last_modified_on_head (s : store) (r : rid) :
  Lemma (requires Some? (lookup s r))
        (ensures  (head_res s r).status == 200 /\
                  has_header "last-modified" (head_res s r) /\
                  (head_res s r).body == "")

(** LWS core, Terminology.
    "container - an LWS resource that is able to enumerate a collection of
    LWS resources, conforming to the conventions described in Section 8.
    Containers."
    Requirement lws-core-05. LWS todo (the Containers section is empty),
    Solid Protocol v0.11.0 section 4.2 binding: enumeration is by containment
    triples, one per direct child.
    Stated as: creating a resource puts it into its parent's enumeration. **)
val lws_core_05_create_updates_containment (s : store) (r c : rid) (res : resource) :
  Lemma (requires contains_child c r)
        (ensures  mem r (contained (create_res s r res) c))

(** LWS core, Terminology, same statement, delete half. Deleting a resource
    removes it from its parent's enumeration. Solid Protocol v0.11.0 section
    5.4 states the same rule for containment triples (solid-05-25). **)
val lws_core_05_delete_updates_containment (s : store) (r c : rid) :
  Lemma (requires r =!= root)
        (ensures  ~ (mem r (contained (delete_res s r) c)))

(** LWS core, Terminology.
    "The storage root is the only LWS resource that does not have a parent in
    the LWS containment hierarchy nor a primary resource."
    Requirement lws-core-06, operational half: the storage root is never
    deleted. LWS todo, Solid Protocol v0.11.0 section 5.4 binding: "When a
    DELETE request targets storage's root container or its associated ACL
    resource, the server MUST respond with the 405 status code." **)
val lws_core_root_not_deleted (s : store) :
  Lemma (delete_res s root == s)

(** Frame law: creating one resource leaves every other identifier alone.
    Needed by any layer above this one, and by the containment statements. **)
val create_preserves_others (s : store) (r r2 : rid) (res : resource) :
  Lemma (requires r2 =!= r)
        (ensures  lookup (create_res s r res) r2 == lookup s r2)

(** Frame law: updating one resource leaves every other identifier alone. **)
val update_preserves_others (s : store) (r r2 : rid) (res : resource) :
  Lemma (requires r2 =!= r)
        (ensures  lookup (update_res s r res) r2 == lookup s r2)

(** Frame law: deleting one resource leaves every other identifier alone. **)
val delete_preserves_others (s : store) (r r2 : rid) :
  Lemma (requires r2 =!= r)
        (ensures  lookup (delete_res s r) r2 == lookup s r2)

(** Soundness of the enumeration: every member of a container's enumeration
    is a direct child of that container. The other half of requirement
    lws-core-05, and what makes the Solid one-to-one correspondence between
    containment triples and the path hierarchy (solid-04-08) meaningful. **)
val contained_are_children (s : store) (c r : rid) :
  Lemma (requires mem r (contained s c))
        (ensures  contains_child c r)

(** LWS core, Terminology.
    "Auxiliary resources are discovered using web links [RFC8288] of a
    specific type (see Section )."
    Requirement lws-core-08. LWS todo (the draft's section reference is
    empty), Solid Protocol v0.11.0 section 4.3 binding: the relations are
    "acl" and "describedby". **)
val lws_core_08_auxiliary_links_advertised (s : store) (r : rid) :
  Lemma (requires Some? (lookup s r))
        (ensures  has_rel rel_acl (discovery_links s r) /\
                  has_rel rel_describedby (discovery_links s r))

(** LWS core, Terminology.
    "storage description - an LWS resource, conforming to the requirements of
    a W3C Controlled Identifier document [CID-1.0], that describes a storage
    along with its services and capabilities."
    Requirement lws-core-18, discovery half only. LWS todo, Solid Protocol
    v0.11.0 section 4.1 binding: the storageDescription link relation. The
    CID 1.0 conformance of the description document itself is NOT stated
    here and stays open in the registry. **)
val lws_core_18_storage_description_link (s : store) (r : rid) :
  Lemma (requires Some? (lookup s r))
        (ensures  has_rel rel_storage_description (discovery_links s r))

(** LWS core, Discovery, with the Solid Protocol v0.11.0 section 4.1
    binding. The storage root advertises its type, which is what Solid
    requirement solid-04-03 states. **)
val root_storage_type_link (s : store) :
  Lemma (mem ({ l_target = iri_pim_storage; l_rel = rel_type })
             (discovery_links s root))

(** LWS core, Discovery, with the Solid Protocol v0.11.0 section 4.1
    binding: a storage that knows its owner advertises it, which is Solid
    requirement solid-04-07. **)
val root_owner_link (s : store) (o : string) :
  Lemma (requires owner_of s == Some o)
        (ensures  mem ({ l_target = o; l_rel = rel_owner })
                      (discovery_links s root))

(** ======================================================================= **)
(** Part 6: PATCH                                                           **)
(** ======================================================================= **)

// A term of a patch formula.
type patch_term =
  | PT_Iri   of string
  | PT_Lit   of string
  | PT_Var   of string
  | PT_Bnode of string

type patch_triple = {
  p_s : patch_term;
  p_p : patch_term;
  p_o : patch_term
}

// The N3 Patch shape of Solid Protocol section 5.3.1, which the LWS draft
// refers to as ?insertions, ?deletions and ?conditions.
type patch = {
  insertions : list patch_triple;
  deletions  : list patch_triple;
  conditions : list patch_triple
}

let term_is_bnode (t : patch_term) : bool = PT_Bnode? t

let triple_has_bnode (t : patch_triple) : bool =
  term_is_bnode t.p_s || term_is_bnode t.p_p || term_is_bnode t.p_o

let formula_has_bnode (f : list patch_triple) : bool = existsb triple_has_bnode f

let term_var (t : patch_term) : list string =
  match t with
  | PT_Var v -> [v]
  | _ -> []

let triple_vars (t : patch_triple) : list string =
  term_var t.p_s @ term_var t.p_p @ term_var t.p_o

let rec formula_vars (f : list patch_triple) : list string =
  match f with
  | [] -> []
  | t :: tl -> triple_vars t @ formula_vars tl

let var_in (b : list string) (v : string) : bool = mem v b
let vars_within (a b : list string) : bool = for_all (var_in b) a

// A patch is well formed exactly when it satisfies the constraints of
// Solid Protocol section 5.3.1, which are also the LWS draft's PATCH
// constraints.
let patch_well_formed (p : patch) : bool =
  not (formula_has_bnode p.insertions) &&
  not (formula_has_bnode p.deletions) &&
  vars_within (formula_vars p.insertions) (formula_vars p.conditions) &&
  vars_within (formula_vars p.deletions)  (formula_vars p.conditions)

(** LWS core, For Editors (CG-to-ED delta).
    "The PATCH ?insertions formulae MUST NOT contain blank nodes."
    Requirement lws-core-04. LWS todo, Solid Protocol v0.11.0 section 5.3.1
    binding: status code 422. **)
val lws_core_04_insertions_no_blank_nodes (p : patch) :
  Lemma (requires patch_well_formed p)
        (ensures  formula_has_bnode p.insertions == false)

let patch_is_ground (p : patch) : bool =
  Nil? (formula_vars p.insertions) &&
  Nil? (formula_vars p.deletions) &&
  Nil? (formula_vars p.conditions)

let term_string (t : patch_term) : string =
  match t with
  | PT_Iri s -> s
  | PT_Lit s -> s
  | PT_Var v -> v
  | PT_Bnode b -> b

let ground_triple (t : patch_triple) : rdf_triple =
  { t_s = term_string t.p_s; t_p = term_string t.p_p; t_o = term_string t.p_o }

let ground_formula (f : list patch_triple) : list rdf_triple = map ground_triple f

let in_graph (g : list rdf_triple) (t : rdf_triple) : bool = mem t g
let all_present (g : list rdf_triple) (ts : list rdf_triple) : bool = for_all (in_graph g) ts
let not_in (ts : list rdf_triple) (t : rdf_triple) : bool = not (mem t ts)
let remove_triples (g : list rdf_triple) (ts : list rdf_triple) : list rdf_triple =
  filter (not_in ts) g

// Applying a patch. Ground patches only: a patch with variables needs a
// solution mapping over the target graph, which this specification does not
// state (the row stays open in the registry). A patch with variables in its
// conditions is refused as not applicable, never silently applied.
val apply_patch : store -> rid -> patch -> Tot (response * store)

(** LWS core, For Editors (CG-to-ED delta), the refusal half of
    requirement lws-core-04, and Solid Protocol v0.11.0 section 5.3.1:
    "Servers MUST respond with a 422 status code [RFC4918] if a patch
    document does not satisfy all of the above constraints."
    Requirement solid-05-19. **)
val lws_core_04_ill_formed_patch_refused (s : store) (r : rid) (p : patch) :
  Lemma (requires patch_well_formed p == false)
        (ensures  (fst (apply_patch s r p)).status == 422 /\
                  snd (apply_patch s r p) == s)

(** A well formed patch is never refused as ill formed, as an unsupported
    media type, or as an unsupported method. The positive half of
    requirement solid-05-13, "Servers MUST accept a PATCH request with an N3
    Patch body when the target of the request is an RDF document". **)
val lws_patch_not_refused (s : store) (r : rid) (p : patch) :
  Lemma (requires patch_well_formed p)
        (ensures  (fst (apply_patch s r p)).status <> 422 /\
                  (fst (apply_patch s r p)).status <> 415 /\
                  (fst (apply_patch s r p)).status <> 405)

(** What applying a patch does: a well formed ground patch whose conditions
    and whose deletions are all in the target graph is applied, the response
    is 204, and the new graph is the insertions over the graph with the
    deletions removed. The requirement solid-05-20 operations follow from
    the same three formulae. **)
val lws_patch_applied (s : store) (r : rid) (p : patch) (res : resource) :
  Lemma (requires patch_well_formed p /\ patch_is_ground p /\
                  lookup s r == Some res /\
                  all_present res.r_graph (ground_formula p.conditions) /\
                  all_present res.r_graph (ground_formula p.deletions))
        (ensures  (fst (apply_patch s r p)).status == 204 /\
                  Some? (lookup (snd (apply_patch s r p)) r) /\
                  (Some?.v (lookup (snd (apply_patch s r p)) r)).r_graph ==
                    ground_formula p.insertions
                    @ remove_triples res.r_graph (ground_formula p.deletions))

(** ======================================================================= **)
(** Part 7: The operation dispatch and its status codes                     **)
(** ======================================================================= **)

// LWS core, Resource Access, lists the response outcomes: created, success,
// not found, not permitted, unknown requester. The draft binds none of them
// to a status code. The binding below is Solid Protocol v0.11.0 section 5.
val perform : store -> operation -> rid -> resource -> Tot (response * store)

(** LWS core, Resource Access.
    "An operation is any of the following actions that can be performed on a
    served resource: create resource, read resource, update resource, delete
    resource."
    Requirement lws-core-11: all four are answered, none is refused with the
    405 of an unsupported method. LWS todo, Solid Protocol v0.11.0 section 5
    binding. **)
val lws_core_11_four_operations (s : store) (r : rid) (res : resource) :
  Lemma (requires contains_child root r /\ None? (lookup s r))
        (ensures  (
          let (c_resp, s1) = perform s Op_Create r res in
          let (r_resp, _)  = perform s1 Op_Read r res in
          let (u_resp, s2) = perform s1 Op_Update r res in
          let (d_resp, s3) = perform s2 Op_Delete r res in
          c_resp.status == 201 /\ r_resp.status == 200 /\
          u_resp.status == 204 /\ d_resp.status == 204 /\
          None? (lookup s3 r)))

(** LWS core, Resource Access.
    "success - the operation is believed to have completed. This may be
    accompanied by a resource representation conveying the contents of a
    served resource. A success response is not defined for the create
    resource operation. See instead created."
    Requirement lws-core-12: the create outcome is distinct from the success
    outcome. LWS todo, Solid Protocol v0.11.0 section 5 binding: 201 for
    created, 200 or 204 for success. **)
val lws_core_12_created_is_not_success (s : store) (r : rid) (res : resource) :
  Lemma (requires contains_child root r /\ None? (lookup s r))
        (ensures  (fst (perform s Op_Create r res)).status <> 200 /\
                  (fst (perform s Op_Create r res)).status <> 204)
