module Solid.Protocol.Spec

(** ======================================================================= **)
(** Solid.Protocol.Spec - the proofs of the statements the interface makes. **)
(**                                                                         **)
(** Every definition is in the interface; this file holds only the lemma    **)
(** bodies, the induction they need, and the Web Access Control document's  **)
(** worked examples as assert_norm.                                         **)
(** ======================================================================= **)

open FStar.List.Tot
open LWS.Core.Spec

#push-options "--fuel 12 --ifuel 4 --z3rlimit 200"

(** ======================================================================= **)
(** Induction the statements need                                           **)
(** ======================================================================= **)

// Containment statements over a fixed container are in one-to-one
// correspondence with the enumeration they are built from.
let rec mem_map_containment (c : rid) (l : list rid) (r : rid) :
  Lemma (ensures mem (mk_containment c r) (map (mk_containment c) l) == mem r l)
        (decreases l) =
  match l with
  | [] -> ()
  | _ :: tl -> mem_map_containment c tl r

let rec acl_lookup_after_remove (m : list (rid * list authorization)) (r : rid) :
  Lemma (ensures None? (acl_lookup (filter (acl_not_key r) m) r))
        (decreases m) =
  match m with
  | [] -> ()
  | _ :: tl -> acl_lookup_after_remove tl r

let rec meta_lookup_after_remove (m : list (rid * list rdf_triple)) (r : rid) :
  Lemma (ensures None? (meta_lookup (filter (meta_not_key r) m) r))
        (decreases m) =
  match m with
  | [] -> ()
  | _ :: tl -> meta_lookup_after_remove tl r

let rec init_segs_append (l : list string) (x : string) :
  Lemma (ensures init_segs (l @ [x]) == l /\ Cons? (l @ [x]))
        (decreases l) =
  match l with
  | [] -> ()
  | _ :: tl -> init_segs_append tl x

(** ======================================================================= **)
(** Part 8: The server statements                                           **)
(** ======================================================================= **)

let solid_02_02_content_type_required s q = ()

let solid_03_01_slash_denotes_container r = ()

let solid_03_02_slash_pair_distinct r = ()

let solid_04_03_storage_type_link st = root_storage_type_link st

let solid_04_07_owner_link st o = root_owner_link st o

let solid_04_04_storage_description_link st r =
  lws_core_18_storage_description_link st r

let solid_04_08_containment_iff_enumerated s c r =
  mem_map_containment c (contained s.x_store c) r

let solid_04_08_containment_is_hierarchy s c r =
  mem_map_containment c (contained s.x_store c) r;
  contained_are_children s.x_store c r

let solid_04_11_auxiliaries_deleted_with_subject s t =
  acl_lookup_after_remove s.x_acl t.g_id;
  meta_lookup_after_remove s.x_meta t.g_id

let solid_04_12_auxiliary_links_advertised st r =
  lws_core_08_auxiliary_links_advertised st r

let solid_04_13_at_most_one_description s r g1 g2 = ()

let solid_04_14_description_authorized_as_subject r = ()

let solid_05_01_unsupported_method_405 s q = ()

let solid_05_02_post_assigns_uri s q =
  init_segs_append q.q_target.g_id.segs (assigned_name s q.q_slug)

let solid_05_04_allow_header s q = ()

let solid_05_05_accept_headers s q = ()

let solid_05_07_intermediate_container s q =
  let r = q.q_target.g_id in
  containment_acyclic r;
  let p = Some?.v (parent_of r) in
  let s1 = ensure_parent s r in
  create_preserves_others s1.x_store r p (resource_of q);
  update_preserves_others s1.x_store r p (resource_of q)

let solid_05_09_post_missing_target_404 s q = ()

let solid_05_11_containment_edit_409 s q = ()

let solid_05_13_n3_patch_accepted s q d =
  lws_patch_not_refused s.x_store q.q_target.g_id (n3_patch_of d)

let solid_05_19_ill_formed_patch_422 s q d = ()

let solid_05_20_patch_operations p = ()

let solid_05_24_delete_root_405 s q = ()

let solid_05_25_delete_removes_containment s t c =
  mem_map_containment c (contained (delete_res s.x_store t.g_id) c) t.g_id;
  lws_core_05_delete_updates_containment s.x_store t.g_id c

let solid_05_27_delete_non_empty_container_409 s q = ()

let solid_wac_01_no_acl_denies s a r m = ()

let solid_wac_02_match_resource_agent_mode gi a owner m z = ()

let solid_wac_03_default_is_inherited gi a owner m z = ()

let rec agent_in_any_group_intro (gi : group_index) (w g : string) (gs : list string) :
  Lemma (requires mem g gs /\ mem w (group_members gi g))
        (ensures  agent_in_any_group gi w gs)
        (decreases gs) =
  match gs with
  | [] -> ()
  | x :: tl -> if x = g then () else agent_in_any_group_intro gi w g tl

let solid_wac_04_agent_group gi w g z =
  agent_in_any_group_intro gi w g z.z_agent_group

let rec mem_names_append (l1 l2 : list (string * string)) (n : string) :
  Lemma (requires mem n (map fst l1))
        (ensures  mem n (map fst (l1 @ l2)))
        (decreases l1) =
  match l1 with
  | [] -> ()
  | _ :: tl -> if mem n (map fst tl) then mem_names_append tl l2 n else ()

let rec header_value_append (l1 l2 : list (string * string)) (n : string) :
  Lemma (requires Some? (header_value l1 n))
        (ensures  header_value (l1 @ l2) n == header_value l1 n)
        (decreases l1) =
  match l1 with
  | [] -> ()
  | (k, _) :: tl -> if k = n then () else header_value_append tl l2 n

let solid_wac_07_wac_allow_header s q =
  let base = (if HM_GET? q.q_method
              then get_res s.x_store q.q_target.g_id
              else head_res s.x_store q.q_target.g_id) in
  mem_names_append (read_headers s q.q_target) base.headers "wac-allow"

(** ======================================================================= **)
(** Part 9: The client statements                                           **)
(** ======================================================================= **)

let solid_02_06_client_content_type m uri ct body = ()

let rec link_target_present (rel : string) (ls : list link) :
  Lemma (ensures Some? (link_target_for rel ls) == has_rel rel ls)
        (decreases ls) =
  match ls with
  | [] -> ()
  | _ :: tl -> link_target_present rel tl

let solid_wac_09_client_acl_from_links ls = link_target_present rel_acl ls

let solid_wac_08_client_reads_wac_allow s q =
  let base = head_res s.x_store q.q_target.g_id in
  header_value_append (read_headers s q.q_target) base.headers "wac-allow"

let rec storage_walk_sound_aux (probe : rid -> list link) (r c : rid) :
  Lemma (requires client_storage_walk probe r == Some c)
        (ensures  has_type_storage (probe c))
        (decreases (length r.segs)) =
  if has_type_storage (probe r) then ()
  else match parent_of r with
       | None -> ()
       | Some p ->
         containment_acyclic r;
         storage_walk_sound_aux probe p c

let solid_cl_01_storage_walk_sound probe r c = storage_walk_sound_aux probe r c

(** ======================================================================= **)
(** The Web Access Control document's worked examples                       **)
(**                                                                         **)
(** Section 5.3.3 Authorization Matching gives three matching cases. Each   **)
(** is written here as a ground instance and decided by assert_norm, so a   **)
(** change to decide_access that breaks one of them fails the build.        **)
(** ======================================================================= **)

// The example vocabulary of the Web Access Control document.
let ex_alice   : string = "https://alice.example/profile/card#me"
let ex_bob     : string = "https://bob.example/profile/card#me"
let ex_group   : string = "https://alice.example/work-groups#Accounting"
let ex_doc     : rid    = { segs = ["docs"; "note"]; container = false }
let ex_docs    : rid    = { segs = ["docs"]; container = true }

let ex_groups : group_index = [ (ex_group, [ ex_bob ]) ]

// Case 1, section 5.3.3: a specific resource, a specific agent, a specific
// access mode.
let ex_auth_agent : authorization = {
  z_access_to   = [ ex_doc ];
  z_default     = [];
  z_agent       = [ ex_alice ];
  z_agent_class = [];
  z_agent_group = [];
  z_mode        = [ AM_Read; AM_Write ]
}

// Case 2, section 5.3.3: a container, an agent class, an access mode, held
// by acl:default so it is inherited by the contained resources.
let ex_auth_class : authorization = {
  z_access_to   = [];
  z_default     = [ ex_docs ];
  z_agent       = [];
  z_agent_class = [ cls_authenticated_agent ];
  z_agent_group = [];
  z_mode        = [ AM_Read ]
}

// Case 3, section 5.3.3: a specific resource, an agent by group membership,
// a specific access mode.
let ex_auth_group : authorization = {
  z_access_to   = [ ex_doc ];
  z_default     = [];
  z_agent       = [];
  z_agent_class = [];
  z_agent_group = [ ex_group ];
  z_mode        = [ AM_Append ]
}

let ex_state : sstate = {
  x_store   = empty_store 0 None;
  x_acl     = [ (ex_doc,  [ ex_auth_agent; ex_auth_group ]);
                (ex_docs, [ ex_auth_class ]) ];
  x_meta    = [];
  x_groups  = ex_groups;
  x_agent   = Ag_WebId ex_alice;
  x_enforce = true
}

// solid-wac-02: Alice reads and writes the document she is named on.
let _ = assert_norm (decide_access ex_state (Ag_WebId ex_alice) ex_doc AM_Read  == true)
let _ = assert_norm (decide_access ex_state (Ag_WebId ex_alice) ex_doc AM_Write == true)

// solid-wac-01: the public agent matches no authorization, so access is
// denied. acl:Control was granted to nobody, so nobody has it.
let _ = assert_norm (decide_access ex_state Ag_Public ex_doc AM_Read == false)
let _ = assert_norm (decide_access ex_state (Ag_WebId ex_alice) ex_doc AM_Control == false)

// solid-wac-04: Bob appends by his group membership, and does not read.
let _ = assert_norm (decide_access ex_state (Ag_WebId ex_bob) ex_doc AM_Append == true)
let _ = assert_norm (decide_access ex_state (Ag_WebId ex_bob) ex_doc AM_Read   == false)

// Web Access Control section 3.4: acl:Write includes acl:Append, so Alice
// appends without acl:Append being written down.
let _ = assert_norm (decide_access ex_state (Ag_WebId ex_alice) ex_doc AM_Append == true)

// solid-wac-03 with solid-wac-05: a resource with no ACL of its own inherits
// the container's acl:default authorization, and only that one.
let ex_other : rid = { segs = ["docs"; "other"]; container = false }
let _ = assert_norm (decide_access ex_state (Ag_WebId ex_bob)   ex_other AM_Read  == true)
let _ = assert_norm (decide_access ex_state (Ag_WebId ex_alice) ex_other AM_Write == false)
let _ = assert_norm (decide_access ex_state Ag_Public           ex_other AM_Read  == false)

#pop-options
