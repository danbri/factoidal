module LWS.Core.Spec

(** ======================================================================= **)
(** LWS.Core.Spec - one model of the interface, and the proofs of its laws. **)
(**                                                                         **)
(** LWS.Core.Spec.fsti is the specification. This file gives ONE store that **)
(** satisfies it - an association list of identifiers to resources plus a   **)
(** counter that stands for the clock - and discharges every lemma the      **)
(** interface declares. The model exists to show the statements are         **)
(** consistent and to fix their meaning; it is not the engine. The engine   **)
(** is the Lean tree, formal/lean4/L4Factoidal/LWS/.                        **)
(** ======================================================================= **)

open FStar.List.Tot

#push-options "--fuel 8 --ifuel 4 --z3rlimit 100"

(** ======================================================================= **)
(** Part 1: The containment hierarchy                                       **)
(** ======================================================================= **)

let lws_core_06_root_has_no_parent () = ()

let lws_core_06_only_root_has_no_parent r = ()

let rec init_segs_shorter (l : list string) :
  Lemma (requires Cons? l)
        (ensures  length (init_segs l) < length l)
        (decreases l) =
  match l with
  | [_] -> ()
  | _ :: tl -> init_segs_shorter tl

let containment_acyclic r = init_segs_shorter r.segs

let containment_single_parent c1 c2 r = ()

(** ======================================================================= **)
(** Part 2: The store model                                                 **)
(** ======================================================================= **)

type entry = rid * resource

let entry_id (kv : entry) : rid = fst kv

// The predicate that keeps every entry EXCEPT the named one.
let not_id (r : rid) (kv : entry) : bool = not (entry_id kv = r)

// The predicate that keeps the direct children of a container.
let child_of (c : rid) (kv : entry) : bool = contains_child c (entry_id kv)

noeq type store_repr = {
  s_entries : list entry;
  s_clock   : nat;
  s_owner   : option string
}

let store = store_repr

let rec lookup_entries (es : list entry) (r : rid) : Tot (option resource) (decreases es) =
  match es with
  | [] -> None
  | (k, v) :: tl -> if k = r then Some v else lookup_entries tl r

let lookup s r = lookup_entries s.s_entries r

let contained s c = map entry_id (filter (child_of c) s.s_entries)

let last_modified s r =
  match lookup s r with
  | None -> None
  | Some res -> Some res.r_modified

let clock_of s = s.s_clock

let owner_of s = s.s_owner

let root_resource : resource = {
  r_kind         = RK_StorageRoot;
  r_content_type = "text/turtle";
  r_content      = "";
  r_graph        = [];
  r_modified     = 0
}

let empty_store t0 own = {
  s_entries = [ (root, { root_resource with r_modified = t0 }) ];
  s_clock   = t0;
  s_owner   = own
}

// An identifier removed from the entry list cannot be found in it again.
let rec lookup_after_remove (es : list entry) (r : rid) :
  Lemma (ensures None? (lookup_entries (filter (not_id r) es) r))
        (decreases es) =
  match es with
  | [] -> ()
  | (k, _) :: tl -> lookup_after_remove tl r

// Nor can it appear in any container's enumeration.
let rec not_contained_after_remove (es : list entry) (r c : rid) :
  Lemma (ensures ~ (mem r (map entry_id (filter (child_of c) (filter (not_id r) es)))))
        (decreases es) =
  match es with
  | [] -> ()
  | (k, _) :: tl -> not_contained_after_remove tl r c

(** ======================================================================= **)
(** Part 3: The four operations                                             **)
(** ======================================================================= **)

let create_res s r res =
  { s_entries = (r, { res with r_modified = s.s_clock }) :: filter (not_id r) s.s_entries;
    s_clock   = s.s_clock + 1;
    s_owner   = s.s_owner }

let update_res s r res =
  { s_entries = (r, { res with r_modified = s.s_clock }) :: filter (not_id r) s.s_entries;
    s_clock   = s.s_clock + 1;
    s_owner   = s.s_owner }

let delete_res s r =
  if r = root then s
  else begin
    lookup_after_remove s.s_entries r;
    { s_entries = filter (not_id r) s.s_entries;
      s_clock   = s.s_clock + 1;
      s_owner   = s.s_owner }
  end

(** ======================================================================= **)
(** Part 4: Rendering identifiers, links and responses                      **)
(** ======================================================================= **)

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

let discovery_links s r =
  let common = [
    { l_target = rid_path r ^ acl_suffix;         l_rel = rel_acl };
    { l_target = rid_path r ^ describedby_suffix; l_rel = rel_describedby };
    { l_target = storage_description;             l_rel = rel_storage_description }
  ] in
  if r = root then
    let type_link = { l_target = iri_pim_storage; l_rel = rel_type } in
    match s.s_owner with
    | None -> type_link :: common
    | Some o -> type_link :: { l_target = o; l_rel = rel_owner } :: common
  else common

let rec render_links (ls : list link) : Tot string (decreases ls) =
  match ls with
  | [] -> ""
  | [l] -> "<" ^ l.l_target ^ ">; rel=\"" ^ l.l_rel ^ "\""
  | l :: tl -> "<" ^ l.l_target ^ ">; rel=\"" ^ l.l_rel ^ "\", " ^ render_links tl

// The Last-Modified field value. The statement this module carries is about
// the PRESENCE of the field (requirement lws-core-03); rendering the instant
// in the IMF-fixdate form of RFC 9110 section 5.6.7 is the host's, and is a
// separate open row of the registry.
let last_modified_value (t : nat) : string = string_of_int t

let get_res s r =
  match lookup s r with
  | None -> { status = 404; headers = []; body = "" }
  | Some res ->
    { status  = 200;
      headers = [ ("content-type",  res.r_content_type);
                  ("last-modified", last_modified_value res.r_modified);
                  ("link",          render_links (discovery_links s r)) ];
      body    = res.r_content }

let head_res s r = { get_res s r with body = "" }

(** ======================================================================= **)
(** Part 5: The statements over reading, containment and discovery          **)
(** ======================================================================= **)

let lws_core_03_last_modified_on_get s r = ()

let lws_core_03_last_modified_on_head s r = ()

let lws_core_05_create_updates_containment s r c res = ()

let lws_core_05_delete_updates_containment s r c =
  not_contained_after_remove s.s_entries r c

let lws_core_root_not_deleted s = ()

let lws_core_08_auxiliary_links_advertised s r = ()

let lws_core_18_storage_description_link s r = ()

(** ======================================================================= **)
(** Part 6: PATCH                                                           **)
(** ======================================================================= **)

let lws_core_04_insertions_no_blank_nodes p = ()

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

let refusal (code : nat) : response = { status = code; headers = []; body = "" }

let apply_patch s r p =
  if not (patch_well_formed p) then (refusal 422, s)
  else match lookup s r with
  | None -> (refusal 404, s)
  | Some res ->
    // A patch with variables needs a solution mapping over the target graph.
    // This specification does not state that mapping, so such a patch is
    // refused rather than applied. Requirements solid-05-21 and solid-05-22
    // stay open in the registry for the same reason.
    if not (patch_is_ground p) then (refusal 409, s)
    else if not (all_present res.r_graph (ground_formula p.conditions)) then (refusal 409, s)
    else if not (all_present res.r_graph (ground_formula p.deletions)) then (refusal 409, s)
    else
      let g2 = ground_formula p.insertions
               @ remove_triples res.r_graph (ground_formula p.deletions) in
      (refusal 204, update_res s r ({ res with r_graph = g2 }))

let lws_core_04_ill_formed_patch_refused s r p = ()

(** ======================================================================= **)
(** Part 7: The operation dispatch                                          **)
(** ======================================================================= **)

let allow_root : string = "OPTIONS, HEAD, GET, POST, PUT, PATCH"

let perform s op r res =
  match op with
  | Op_Create ->
    if Some? (lookup s r) then (refusal 409, s)
    else ({ status = 201; headers = [ ("location", rid_path r) ]; body = "" },
          create_res s r res)
  | Op_Read -> (get_res s r, s)
  | Op_Update ->
    if None? (lookup s r) then (refusal 404, s)
    else (refusal 204, update_res s r res)
  | Op_Delete ->
    if r = root then ({ status = 405; headers = [ ("allow", allow_root) ]; body = "" }, s)
    else if None? (lookup s r) then (refusal 404, s)
    else (refusal 204, delete_res s r)

let lws_core_11_four_operations s r res =
  lws_core_06_root_has_no_parent ();
  let (_, s1) = perform s Op_Create r res in
  let (_, s2) = perform s1 Op_Update r res in
  lookup_after_remove s2.s_entries r

let lws_core_12_created_is_not_success s r res = ()

#pop-options
