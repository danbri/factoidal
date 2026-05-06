module SPARQL.Update.Sandbox

(* SPARQL 1.1 UPDATE sandbox — pure semantic policy.

   Migrated from formal/fstar/ocaml-output/factoidal_http.ml
   (`expand_user_graph`, `sandbox_op`, `sandbox_update`,
   `check_ggp_graph_target`, `wrap_if_unwrapped`) per CLAUDE.md rule #1
   (F-star is the source of truth) and rule #10/#15 (no semantic logic in
   OCaml glue).

   The sandbox walks an `update_op` AST and:
     - rewrites templates so writes are wrapped in `GRAPH <usergraph>` when
       no outer GRAPH clause is present;
     - rejects ops whose target graph (template wrapper or graph_ref) does
       not equal the user's sandbox graph IRI;
     - rejects LOAD defensively (the HTTP layer already filters LOAD).

   `expand_user_graph` substitutes "{authid}" in a template string with a
   concrete authentication identifier. It is byte-for-byte identical to
   the previous OCaml `string_replace_all ~needle:"{authid}"`.

   Behaviour is byte-for-byte identical to the previous OCaml.
*)

open FStar.String
open FStar.List.Tot
open RDF.Graph.Executable
open SPARQL11.Algebra

(* ========================================================================== *)
(* expand_user_graph: replace all occurrences of "{authid}" in [template].    *)
(* ========================================================================== *)

(* All-occurrence string replacement of a fixed needle. Keep it total.
   We index by character (FStar.String.length / .sub), which matches the
   prior OCaml byte-level implementation only when the haystack is ASCII —
   which is the case for our auth template (it contains literal "{authid}"
   and an IRI body). The previous OCaml version was also byte-level.
   F-star strings are sequences of unicode code points, but for templates
   formed of ASCII this collapses to the same answer. *)
let rec replace_all_aux
  (haystack : string)
  (needle : string)
  (replacement : string)
  (nlen : nat{nlen > 0})
  (pos : nat)
  (acc : list FStar.Char.char)
  : Tot (list FStar.Char.char) (decreases (FStar.String.length haystack - pos))
  =
  let hlen = FStar.String.length haystack in
  if pos >= hlen then acc
  else if pos + nlen > hlen then
    // Tail too short for another match; copy remaining chars verbatim.
    let c = FStar.String.index haystack pos in
    replace_all_aux haystack needle replacement nlen (pos + 1) (c :: acc)
  else
    let candidate = FStar.String.sub haystack pos nlen in
    if candidate = needle then
      let rep_chars = FStar.String.list_of_string replacement in
      let acc' = List.Tot.rev_acc rep_chars acc in
      replace_all_aux haystack needle replacement nlen (pos + nlen) acc'
    else
      let c = FStar.String.index haystack pos in
      replace_all_aux haystack needle replacement nlen (pos + 1) (c :: acc)

val string_replace_all : needle:string -> replacement:string -> haystack:string -> string
let string_replace_all needle replacement haystack =
  let nlen = FStar.String.length needle in
  if nlen = 0 then haystack
  else
    let revc = replace_all_aux haystack needle replacement nlen 0 [] in
    FStar.String.string_of_list (List.Tot.rev revc)

val expand_user_graph : template:string -> authid:string -> string
let expand_user_graph template authid =
  string_replace_all "{authid}" authid template

(* Find the first '{' at or after position [pos] in [s]. Fuel-bounded
   linear scan; returns None if not found within fuel. *)
let rec find_open_brace
    (s : string)
    (pos : nat)
    (fuel : nat)
  : Tot (option nat) (decreases fuel) =
  if fuel = 0 then None
  else
    let len = FStar.String.length s in
    if pos >= len then None
    else
      let c : nat = FStar.Char.int_of_char (FStar.String.index s pos) in
      if c = 0x7B then Some pos  (* '{' *)
      else find_open_brace s (pos + 1) (fuel - 1)

(* Return the fixed prefix of an auth-template up to (but not including)
   "{authid}". If the template contains no "{authid}" placeholder, return
   the whole template. Used by the HTTP server to detect which named
   graphs in the dataset belong to the user-writable sandbox. *)
val template_prefix : template:string -> string
let template_prefix template =
  let len = FStar.String.length template in
  let key = "{authid}" in
  let klen = FStar.String.length key in
  let fuel : nat = len + 1 in
  match find_open_brace template 0 fuel with
  | None -> template
  | Some i ->
    if i + klen <= len && FStar.String.sub template i klen = key
    then FStar.String.sub template 0 i
    else template

(* Smoke tests. *)
let _test_template_prefix_authid =
  template_prefix "https://example.org/users/{authid}/graph" = "https://example.org/users/"

let _test_template_prefix_no_placeholder =
  template_prefix "https://example.org/fixed-graph" = "https://example.org/fixed-graph"

let _test_template_prefix_other_brace =
  // A '{' that is NOT followed by 'authid}' should be passed through.
  template_prefix "https://example.org/{x}/graph" = "https://example.org/{x}/graph"

(* ========================================================================== *)
(* GGP / graph_ref checks                                                     *)
(* ========================================================================== *)

(* Result of inspecting an outer GRAPH wrapper around a template GGP. *)
type ggp_target_status =
  | GTS_Ok                          // no wrapper, or wrapper matches
  | GTS_Mismatch : iri:string -> ggp_target_status
                                    // wrapper targets a specific other IRI
  | GTS_NonIri                      // wrapper uses a variable / non-IRI

val check_ggp_graph_target : group_graph_pattern -> usergraph:wf_iri -> ggp_target_status
let check_ggp_graph_target g usergraph =
  match g with
  | GP_Graph pt _inner ->
    (match pt with
     | PT_IRI iri ->
       if iri = usergraph then GTS_Ok else GTS_Mismatch iri
     | _ -> GTS_NonIri)
  | _ -> GTS_Ok

(* If the ggp has no outer GRAPH wrapper, wrap it with GRAPH <usergraph>{...}.
   If it already has one (matching usergraph — caller has checked), leave as-is. *)
val wrap_if_unwrapped : group_graph_pattern -> usergraph:wf_iri -> group_graph_pattern
let wrap_if_unwrapped g usergraph =
  match g with
  | GP_Graph _ _ -> g
  | _ -> GP_Graph (PT_IRI usergraph) g

(* Internal status when checking / rewriting a template ggp. *)
noeq type ggp_check_result =
  | GCR_Rewrite : group_graph_pattern -> ggp_check_result
  | GCR_Reject  : string -> ggp_check_result

let check_ggp (which:string) (g:group_graph_pattern) (usergraph:wf_iri)
  : ggp_check_result
  =
  match check_ggp_graph_target g usergraph with
  | GTS_Ok -> GCR_Rewrite (wrap_if_unwrapped g usergraph)
  | GTS_Mismatch iri ->
    GCR_Reject (which ^ " targets graph <" ^ iri
                ^ ">; your sandbox is <" ^ usergraph ^ ">")
  | GTS_NonIri ->
    GCR_Reject (which ^ " uses a non-IRI graph target; only GRAPH <"
                ^ usergraph ^ "> is allowed")

(* Internal status when checking a graph_ref. *)
type gref_check_result =
  | GRCR_Ok
  | GRCR_Reject : string -> gref_check_result

let check_gref (which:string) (gr:graph_ref) (usergraph:wf_iri)
  : gref_check_result
  =
  match gr with
  | GR_Graph iri ->
    if iri = usergraph then GRCR_Ok
    else GRCR_Reject (which ^ " targets graph <" ^ iri
                      ^ ">; your sandbox is <" ^ usergraph ^ ">")
  | GR_Default ->
    GRCR_Reject (which ^ " targets the default graph; your sandbox is <"
                 ^ usergraph ^ ">")
  | GR_Named ->
    GRCR_Reject (which ^ " targets NAMED; your sandbox is <"
                 ^ usergraph ^ ">")
  | GR_All ->
    GRCR_Reject (which ^ " targets ALL graphs; your sandbox is <"
                 ^ usergraph ^ ">")

(* ========================================================================== *)
(* sandbox_op                                                                 *)
(* ========================================================================== *)

noeq type sandbox_result =
  | SB_Ok     : update_op -> sandbox_result
  | SB_Reject : string -> sandbox_result

(* check_tpl_opt: option group_graph_pattern -> CGR-shaped option result.
   Local to sandbox_op for U_Modify. *)
noeq type tpl_opt_result =
  | TOR_Rewrite : option group_graph_pattern -> tpl_opt_result
  | TOR_Reject  : string -> tpl_opt_result

let check_tpl_opt (label:string) (t:option group_graph_pattern) (usergraph:wf_iri)
  : tpl_opt_result
  =
  match t with
  | None -> TOR_Rewrite None
  | Some g ->
    (match check_ggp label g usergraph with
     | GCR_Rewrite g' -> TOR_Rewrite (Some g')
     | GCR_Reject msg -> TOR_Reject msg)

val sandbox_op : usergraph:wf_iri -> update_op -> sandbox_result
let sandbox_op usergraph op =
  match op with
  | U_InsertData g ->
    (match check_ggp "INSERT DATA" g usergraph with
     | GCR_Rewrite g' -> SB_Ok (U_InsertData g')
     | GCR_Reject msg -> SB_Reject msg)
  | U_DeleteData g ->
    (match check_ggp "DELETE DATA" g usergraph with
     | GCR_Rewrite g' -> SB_Ok (U_DeleteData g')
     | GCR_Reject msg -> SB_Reject msg)
  | U_DeleteWhere g ->
    (match check_ggp "DELETE WHERE" g usergraph with
     | GCR_Rewrite g' -> SB_Ok (U_DeleteWhere g')
     | GCR_Reject msg -> SB_Reject msg)
  | U_Modify w del_tpl ins_tpl using where ->
    (match check_tpl_opt "INSERT/DELETE: DELETE clause" del_tpl usergraph with
     | TOR_Reject msg -> SB_Reject msg
     | TOR_Rewrite del_tpl' ->
       (match check_tpl_opt "INSERT/DELETE: INSERT clause" ins_tpl usergraph with
        | TOR_Reject msg -> SB_Reject msg
        | TOR_Rewrite ins_tpl' ->
          SB_Ok (U_Modify w del_tpl' ins_tpl' using where)))
  | U_Clear silent gr ->
    (match check_gref "CLEAR" gr usergraph with
     | GRCR_Ok -> SB_Ok (U_Clear silent gr)
     | GRCR_Reject msg -> SB_Reject msg)
  | U_Drop silent gr ->
    (match check_gref "DROP" gr usergraph with
     | GRCR_Ok -> SB_Ok (U_Drop silent gr)
     | GRCR_Reject msg -> SB_Reject msg)
  | U_Create silent iri ->
    if iri = usergraph then SB_Ok (U_Create silent iri)
    else SB_Reject ("CREATE targets graph <" ^ iri
                    ^ ">; your sandbox is <" ^ usergraph ^ ">")
  | U_Add silent src dst ->
    (match check_gref "ADD source" src usergraph with
     | GRCR_Reject msg -> SB_Reject msg
     | GRCR_Ok ->
       (match check_gref "ADD dest" dst usergraph with
        | GRCR_Ok -> SB_Ok (U_Add silent src dst)
        | GRCR_Reject msg -> SB_Reject msg))
  | U_Move silent src dst ->
    (match check_gref "MOVE source" src usergraph with
     | GRCR_Reject msg -> SB_Reject msg
     | GRCR_Ok ->
       (match check_gref "MOVE dest" dst usergraph with
        | GRCR_Ok -> SB_Ok (U_Move silent src dst)
        | GRCR_Reject msg -> SB_Reject msg))
  | U_Copy silent src dst ->
    (match check_gref "COPY source" src usergraph with
     | GRCR_Reject msg -> SB_Reject msg
     | GRCR_Ok ->
       (match check_gref "COPY dest" dst usergraph with
        | GRCR_Ok -> SB_Ok (U_Copy silent src dst)
        | GRCR_Reject msg -> SB_Reject msg))
  | U_Load _ _ _ ->
    SB_Reject "LOAD is not permitted in sandboxed updates"

(* ========================================================================== *)
(* sandbox_update                                                             *)
(* ========================================================================== *)

(* Either monad result for the whole-update sandbox check. *)
noeq type update_sandbox_result =
  | USR_Ok    : sparql_update -> update_sandbox_result
  | USR_Error : string -> update_sandbox_result

let rec sandbox_ops_aux
  (usergraph : wf_iri)
  (acc : list update_op)
  (ops : list update_op)
  : Tot (either string (list update_op)) (decreases ops)
  =
  match ops with
  | [] -> Inr (List.Tot.rev acc)
  | op :: rest ->
    (match sandbox_op usergraph op with
     | SB_Ok op'     -> sandbox_ops_aux usergraph (op' :: acc) rest
     | SB_Reject msg -> Inl msg)

val sandbox_update : usergraph:wf_iri -> sparql_update -> update_sandbox_result
let sandbox_update usergraph u =
  match sandbox_ops_aux usergraph [] u.u_ops with
  | Inl msg -> USR_Error msg
  | Inr ops' -> USR_Ok ({ u with u_ops = ops' })
