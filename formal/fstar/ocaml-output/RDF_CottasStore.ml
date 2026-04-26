open Prims
type cottas_ondisk_handle =
  {
  coh_path: Prims.string ;
  coh_summary:
    Parser_BallyhooCOTTAS.cottas_artifact_summary
      FStar_Pervasives_Native.option
    ;
  coh_subjects: RDF_Graph_Executable.subject Prims.list ;
  coh_predicates: RDF_Graph_Executable.wf_iri Prims.list ;
  coh_objects: RDF_Graph_Executable.rdf_term Prims.list ;
  coh_graphs: RDF_Graph_Executable.iri Prims.list ;
  coh_subj_revmap: (Prims.string * Prims.nat) Prims.list ;
  coh_pred_revmap: (Prims.string * Prims.nat) Prims.list ;
  coh_obj_revmap: (Prims.string * Prims.nat) Prims.list ;
  coh_graph_revmap: (Prims.string * Prims.nat) Prims.list ;
  coh_subjects_raw: Prims.string Prims.list ;
  coh_predicates_raw: Prims.string Prims.list ;
  coh_objects_raw: Prims.string Prims.list ;
  coh_graphs_raw: Prims.string Prims.list ;
  coh_subj_raw_revmap: (Prims.string * Prims.nat) Prims.list ;
  coh_pred_raw_revmap: (Prims.string * Prims.nat) Prims.list ;
  coh_obj_raw_revmap: (Prims.string * Prims.nat) Prims.list ;
  coh_graph_raw_revmap: (Prims.string * Prims.nat) Prims.list }
let __proj__Mkcottas_ondisk_handle__item__coh_path
  (projectee : cottas_ondisk_handle) : Prims.string=
  match projectee with
  | { coh_path; coh_summary; coh_subjects; coh_predicates; coh_objects;
      coh_graphs; coh_subj_revmap; coh_pred_revmap; coh_obj_revmap;
      coh_graph_revmap; coh_subjects_raw; coh_predicates_raw;
      coh_objects_raw; coh_graphs_raw; coh_subj_raw_revmap;
      coh_pred_raw_revmap; coh_obj_raw_revmap; coh_graph_raw_revmap;_} ->
      coh_path
let __proj__Mkcottas_ondisk_handle__item__coh_summary
  (projectee : cottas_ondisk_handle) :
  Parser_BallyhooCOTTAS.cottas_artifact_summary
    FStar_Pervasives_Native.option=
  match projectee with
  | { coh_path; coh_summary; coh_subjects; coh_predicates; coh_objects;
      coh_graphs; coh_subj_revmap; coh_pred_revmap; coh_obj_revmap;
      coh_graph_revmap; coh_subjects_raw; coh_predicates_raw;
      coh_objects_raw; coh_graphs_raw; coh_subj_raw_revmap;
      coh_pred_raw_revmap; coh_obj_raw_revmap; coh_graph_raw_revmap;_} ->
      coh_summary
let __proj__Mkcottas_ondisk_handle__item__coh_subjects
  (projectee : cottas_ondisk_handle) :
  RDF_Graph_Executable.subject Prims.list=
  match projectee with
  | { coh_path; coh_summary; coh_subjects; coh_predicates; coh_objects;
      coh_graphs; coh_subj_revmap; coh_pred_revmap; coh_obj_revmap;
      coh_graph_revmap; coh_subjects_raw; coh_predicates_raw;
      coh_objects_raw; coh_graphs_raw; coh_subj_raw_revmap;
      coh_pred_raw_revmap; coh_obj_raw_revmap; coh_graph_raw_revmap;_} ->
      coh_subjects
let __proj__Mkcottas_ondisk_handle__item__coh_predicates
  (projectee : cottas_ondisk_handle) :
  RDF_Graph_Executable.wf_iri Prims.list=
  match projectee with
  | { coh_path; coh_summary; coh_subjects; coh_predicates; coh_objects;
      coh_graphs; coh_subj_revmap; coh_pred_revmap; coh_obj_revmap;
      coh_graph_revmap; coh_subjects_raw; coh_predicates_raw;
      coh_objects_raw; coh_graphs_raw; coh_subj_raw_revmap;
      coh_pred_raw_revmap; coh_obj_raw_revmap; coh_graph_raw_revmap;_} ->
      coh_predicates
let __proj__Mkcottas_ondisk_handle__item__coh_objects
  (projectee : cottas_ondisk_handle) :
  RDF_Graph_Executable.rdf_term Prims.list=
  match projectee with
  | { coh_path; coh_summary; coh_subjects; coh_predicates; coh_objects;
      coh_graphs; coh_subj_revmap; coh_pred_revmap; coh_obj_revmap;
      coh_graph_revmap; coh_subjects_raw; coh_predicates_raw;
      coh_objects_raw; coh_graphs_raw; coh_subj_raw_revmap;
      coh_pred_raw_revmap; coh_obj_raw_revmap; coh_graph_raw_revmap;_} ->
      coh_objects
let __proj__Mkcottas_ondisk_handle__item__coh_graphs
  (projectee : cottas_ondisk_handle) : RDF_Graph_Executable.iri Prims.list=
  match projectee with
  | { coh_path; coh_summary; coh_subjects; coh_predicates; coh_objects;
      coh_graphs; coh_subj_revmap; coh_pred_revmap; coh_obj_revmap;
      coh_graph_revmap; coh_subjects_raw; coh_predicates_raw;
      coh_objects_raw; coh_graphs_raw; coh_subj_raw_revmap;
      coh_pred_raw_revmap; coh_obj_raw_revmap; coh_graph_raw_revmap;_} ->
      coh_graphs
let __proj__Mkcottas_ondisk_handle__item__coh_subj_revmap
  (projectee : cottas_ondisk_handle) : (Prims.string * Prims.nat) Prims.list=
  match projectee with
  | { coh_path; coh_summary; coh_subjects; coh_predicates; coh_objects;
      coh_graphs; coh_subj_revmap; coh_pred_revmap; coh_obj_revmap;
      coh_graph_revmap; coh_subjects_raw; coh_predicates_raw;
      coh_objects_raw; coh_graphs_raw; coh_subj_raw_revmap;
      coh_pred_raw_revmap; coh_obj_raw_revmap; coh_graph_raw_revmap;_} ->
      coh_subj_revmap
let __proj__Mkcottas_ondisk_handle__item__coh_pred_revmap
  (projectee : cottas_ondisk_handle) : (Prims.string * Prims.nat) Prims.list=
  match projectee with
  | { coh_path; coh_summary; coh_subjects; coh_predicates; coh_objects;
      coh_graphs; coh_subj_revmap; coh_pred_revmap; coh_obj_revmap;
      coh_graph_revmap; coh_subjects_raw; coh_predicates_raw;
      coh_objects_raw; coh_graphs_raw; coh_subj_raw_revmap;
      coh_pred_raw_revmap; coh_obj_raw_revmap; coh_graph_raw_revmap;_} ->
      coh_pred_revmap
let __proj__Mkcottas_ondisk_handle__item__coh_obj_revmap
  (projectee : cottas_ondisk_handle) : (Prims.string * Prims.nat) Prims.list=
  match projectee with
  | { coh_path; coh_summary; coh_subjects; coh_predicates; coh_objects;
      coh_graphs; coh_subj_revmap; coh_pred_revmap; coh_obj_revmap;
      coh_graph_revmap; coh_subjects_raw; coh_predicates_raw;
      coh_objects_raw; coh_graphs_raw; coh_subj_raw_revmap;
      coh_pred_raw_revmap; coh_obj_raw_revmap; coh_graph_raw_revmap;_} ->
      coh_obj_revmap
let __proj__Mkcottas_ondisk_handle__item__coh_graph_revmap
  (projectee : cottas_ondisk_handle) : (Prims.string * Prims.nat) Prims.list=
  match projectee with
  | { coh_path; coh_summary; coh_subjects; coh_predicates; coh_objects;
      coh_graphs; coh_subj_revmap; coh_pred_revmap; coh_obj_revmap;
      coh_graph_revmap; coh_subjects_raw; coh_predicates_raw;
      coh_objects_raw; coh_graphs_raw; coh_subj_raw_revmap;
      coh_pred_raw_revmap; coh_obj_raw_revmap; coh_graph_raw_revmap;_} ->
      coh_graph_revmap
let __proj__Mkcottas_ondisk_handle__item__coh_subjects_raw
  (projectee : cottas_ondisk_handle) : Prims.string Prims.list=
  match projectee with
  | { coh_path; coh_summary; coh_subjects; coh_predicates; coh_objects;
      coh_graphs; coh_subj_revmap; coh_pred_revmap; coh_obj_revmap;
      coh_graph_revmap; coh_subjects_raw; coh_predicates_raw;
      coh_objects_raw; coh_graphs_raw; coh_subj_raw_revmap;
      coh_pred_raw_revmap; coh_obj_raw_revmap; coh_graph_raw_revmap;_} ->
      coh_subjects_raw
let __proj__Mkcottas_ondisk_handle__item__coh_predicates_raw
  (projectee : cottas_ondisk_handle) : Prims.string Prims.list=
  match projectee with
  | { coh_path; coh_summary; coh_subjects; coh_predicates; coh_objects;
      coh_graphs; coh_subj_revmap; coh_pred_revmap; coh_obj_revmap;
      coh_graph_revmap; coh_subjects_raw; coh_predicates_raw;
      coh_objects_raw; coh_graphs_raw; coh_subj_raw_revmap;
      coh_pred_raw_revmap; coh_obj_raw_revmap; coh_graph_raw_revmap;_} ->
      coh_predicates_raw
let __proj__Mkcottas_ondisk_handle__item__coh_objects_raw
  (projectee : cottas_ondisk_handle) : Prims.string Prims.list=
  match projectee with
  | { coh_path; coh_summary; coh_subjects; coh_predicates; coh_objects;
      coh_graphs; coh_subj_revmap; coh_pred_revmap; coh_obj_revmap;
      coh_graph_revmap; coh_subjects_raw; coh_predicates_raw;
      coh_objects_raw; coh_graphs_raw; coh_subj_raw_revmap;
      coh_pred_raw_revmap; coh_obj_raw_revmap; coh_graph_raw_revmap;_} ->
      coh_objects_raw
let __proj__Mkcottas_ondisk_handle__item__coh_graphs_raw
  (projectee : cottas_ondisk_handle) : Prims.string Prims.list=
  match projectee with
  | { coh_path; coh_summary; coh_subjects; coh_predicates; coh_objects;
      coh_graphs; coh_subj_revmap; coh_pred_revmap; coh_obj_revmap;
      coh_graph_revmap; coh_subjects_raw; coh_predicates_raw;
      coh_objects_raw; coh_graphs_raw; coh_subj_raw_revmap;
      coh_pred_raw_revmap; coh_obj_raw_revmap; coh_graph_raw_revmap;_} ->
      coh_graphs_raw
let __proj__Mkcottas_ondisk_handle__item__coh_subj_raw_revmap
  (projectee : cottas_ondisk_handle) : (Prims.string * Prims.nat) Prims.list=
  match projectee with
  | { coh_path; coh_summary; coh_subjects; coh_predicates; coh_objects;
      coh_graphs; coh_subj_revmap; coh_pred_revmap; coh_obj_revmap;
      coh_graph_revmap; coh_subjects_raw; coh_predicates_raw;
      coh_objects_raw; coh_graphs_raw; coh_subj_raw_revmap;
      coh_pred_raw_revmap; coh_obj_raw_revmap; coh_graph_raw_revmap;_} ->
      coh_subj_raw_revmap
let __proj__Mkcottas_ondisk_handle__item__coh_pred_raw_revmap
  (projectee : cottas_ondisk_handle) : (Prims.string * Prims.nat) Prims.list=
  match projectee with
  | { coh_path; coh_summary; coh_subjects; coh_predicates; coh_objects;
      coh_graphs; coh_subj_revmap; coh_pred_revmap; coh_obj_revmap;
      coh_graph_revmap; coh_subjects_raw; coh_predicates_raw;
      coh_objects_raw; coh_graphs_raw; coh_subj_raw_revmap;
      coh_pred_raw_revmap; coh_obj_raw_revmap; coh_graph_raw_revmap;_} ->
      coh_pred_raw_revmap
let __proj__Mkcottas_ondisk_handle__item__coh_obj_raw_revmap
  (projectee : cottas_ondisk_handle) : (Prims.string * Prims.nat) Prims.list=
  match projectee with
  | { coh_path; coh_summary; coh_subjects; coh_predicates; coh_objects;
      coh_graphs; coh_subj_revmap; coh_pred_revmap; coh_obj_revmap;
      coh_graph_revmap; coh_subjects_raw; coh_predicates_raw;
      coh_objects_raw; coh_graphs_raw; coh_subj_raw_revmap;
      coh_pred_raw_revmap; coh_obj_raw_revmap; coh_graph_raw_revmap;_} ->
      coh_obj_raw_revmap
let __proj__Mkcottas_ondisk_handle__item__coh_graph_raw_revmap
  (projectee : cottas_ondisk_handle) : (Prims.string * Prims.nat) Prims.list=
  match projectee with
  | { coh_path; coh_summary; coh_subjects; coh_predicates; coh_objects;
      coh_graphs; coh_subj_revmap; coh_pred_revmap; coh_obj_revmap;
      coh_graph_revmap; coh_subjects_raw; coh_predicates_raw;
      coh_objects_raw; coh_graphs_raw; coh_subj_raw_revmap;
      coh_pred_raw_revmap; coh_obj_raw_revmap; coh_graph_raw_revmap;_} ->
      coh_graph_raw_revmap
type cottas_ondisk_store =
  {
  cods_artifact_path: Prims.string ;
  cods_summary:
    Parser_BallyhooCOTTAS.cottas_artifact_summary
      FStar_Pervasives_Native.option
    ;
  cods_handle: cottas_ondisk_handle }
let __proj__Mkcottas_ondisk_store__item__cods_artifact_path
  (projectee : cottas_ondisk_store) : Prims.string=
  match projectee with
  | { cods_artifact_path; cods_summary; cods_handle;_} -> cods_artifact_path
let __proj__Mkcottas_ondisk_store__item__cods_summary
  (projectee : cottas_ondisk_store) :
  Parser_BallyhooCOTTAS.cottas_artifact_summary
    FStar_Pervasives_Native.option=
  match projectee with
  | { cods_artifact_path; cods_summary; cods_handle;_} -> cods_summary
let __proj__Mkcottas_ondisk_store__item__cods_handle
  (projectee : cottas_ondisk_store) : cottas_ondisk_handle=
  match projectee with
  | { cods_artifact_path; cods_summary; cods_handle;_} -> cods_handle
let rec revmap_lookup (m : (Prims.string * Prims.nat) Prims.list)
  (k : Prims.string) : Prims.nat FStar_Pervasives_Native.option=
  match m with
  | [] -> FStar_Pervasives_Native.None
  | (k', v)::rest ->
      if k = k' then FStar_Pervasives_Native.Some v else revmap_lookup rest k
let rec list_nth :
  'a . 'a Prims.list -> Prims.nat -> 'a FStar_Pervasives_Native.option =
  fun xs i ->
    match xs with
    | [] -> FStar_Pervasives_Native.None
    | hd::tl ->
        if i = Prims.int_zero
        then FStar_Pervasives_Native.Some hd
        else list_nth tl (i - Prims.int_one)
let revmap_unit_sep : Prims.string= "\031"
let subject_to_revmap_key (s : RDF_Graph_Executable.subject) : Prims.string=
  match s with
  | RDF_Graph_Executable.S_IRI i -> FStar_String.concat "" ["I_"; i]
  | RDF_Graph_Executable.S_BNode b -> FStar_String.concat "" ["B_"; b]
let iri_to_revmap_key (i : RDF_Graph_Executable.iri) : Prims.string=
  FStar_String.concat "" ["I_"; i]
let object_to_revmap_key (o : RDF_Graph_Executable.rdf_term) : Prims.string=
  match o with
  | RDF_Graph_Executable.T_IRI i -> FStar_String.concat "" ["I_"; i]
  | RDF_Graph_Executable.T_BNode b -> FStar_String.concat "" ["B_"; b]
  | RDF_Graph_Executable.T_Literal l ->
      let tag =
        match l.RDF_Graph_Executable.lang_tag with
        | FStar_Pervasives_Native.Some t -> t
        | FStar_Pervasives_Native.None -> "" in
      FStar_String.concat ""
        ["L_";
        l.RDF_Graph_Executable.datatype;
        revmap_unit_sep;
        tag;
        revmap_unit_sep;
        l.RDF_Graph_Executable.lexical_form]
module Cottas_ondisk_lazy = struct
  open Stdlib

  (* Per-path "is column N populated yet" flags. Avoid relying on
     Hashtbl size (an empty hashtable on a single-graph corpus is a
     valid populated state). *)
  let subj_loaded  : (string, unit) Hashtbl.t = Hashtbl.create 17
  let pred_loaded  : (string, unit) Hashtbl.t = Hashtbl.create 17
  let obj_loaded   : (string, unit) Hashtbl.t = Hashtbl.create 17
  let graph_loaded : (string, unit) Hashtbl.t = Hashtbl.create 17

  let mark_subj_loaded  path = Hashtbl.replace subj_loaded  path ()
  let mark_pred_loaded  path = Hashtbl.replace pred_loaded  path ()
  let mark_obj_loaded   path = Hashtbl.replace obj_loaded   path ()
  let mark_graph_loaded path = Hashtbl.replace graph_loaded path ()
  let is_subj_loaded    path = Hashtbl.mem subj_loaded  path
  let is_pred_loaded    path = Hashtbl.mem pred_loaded  path
  let is_obj_loaded     path = Hashtbl.mem obj_loaded   path
  let is_graph_loaded   path = Hashtbl.mem graph_loaded path

  (* yod6: pred_presence_by_path installed (issue #100, 2026-04-26).
     For each artifact path, a rg_index -> set-of-predicate-tokens map.
     Populated by ensure_predicates_loaded (replaces the batched
     collect_distinct walk). Consulted by search_fast / estimate_fast /
     search_fast_limited to skip rgs that don't contain the bound
     predicate.

     Mirrors F*-side compute_candidate_rgs_loop (RDF.CottasStore.fst):
     skip rg if `not (list_string_mem dict bound_token)`. Soundness:
     the presence set is built by enumerating every value in the rg's
     predicate column, so a rg marked absent provably contains zero
     matching rows. *)
  (* Use Stdlib.Int.t explicitly: the file's `open Prims` makes `int` mean
     Prims.int = Z.t, even inside this submodule's `open Stdlib`. Bet7
     hit the same issue and aliased `pint = Stdlib.Int.t` in
     Cottas_ondisk_runtime; we mirror that. *)
  let pred_presence_by_path
    : (string, (Stdlib.Int.t, (string, unit) Hashtbl.t) Hashtbl.t) Hashtbl.t
    = Hashtbl.create 17

  let presence_for_path (path : string)
    : (Stdlib.Int.t, (string, unit) Hashtbl.t) Hashtbl.t =
    match Hashtbl.find_opt pred_presence_by_path path with
    | Some t -> t
    | None ->
      let t : (Stdlib.Int.t, (string, unit) Hashtbl.t) Hashtbl.t = Hashtbl.create 32 in
      Hashtbl.add pred_presence_by_path path t;
      t

  (* Returns true iff the rg might contain `pred_tok`, or there's no bound,
     or we have no presence entry for this rg (safe fallback: walk it).
     Returns false ONLY when we have an entry and the predicate is
     definitively absent. *)
  let pred_rg_could_contain (path : string) (rg : Stdlib.Int.t)
    (bound_p : string option) : bool =
    match bound_p with
    | None -> true
    | Some pred_tok ->
      match Hashtbl.find_opt pred_presence_by_path path with
      | None -> true
      | Some by_rg ->
        match Hashtbl.find_opt by_rg rg with
        | None -> true  (* presence not yet recorded for this rg *)
        | Some pred_set -> Hashtbl.mem pred_set pred_tok

  (* tet3: subj_presence_by_path installed (issue #100, 2026-04-26).
     Same shape as pred_presence_by_path. Populated by
     ensure_subjects_loaded; consulted via subj_rg_could_contain from
     search_fast / estimate_fast / search_fast_limited.

     Soundness: built by enumerating every value in the rg's subject
     column, so a rg marked absent provably contains zero matching rows
     for that bound subject. *)
  let subj_presence_by_path
    : (string, (Stdlib.Int.t, (string, unit) Hashtbl.t) Hashtbl.t) Hashtbl.t
    = Hashtbl.create 17

  let obj_presence_by_path
    : (string, (Stdlib.Int.t, (string, unit) Hashtbl.t) Hashtbl.t) Hashtbl.t
    = Hashtbl.create 17

  let subj_presence_for_path (path : string)
    : (Stdlib.Int.t, (string, unit) Hashtbl.t) Hashtbl.t =
    match Hashtbl.find_opt subj_presence_by_path path with
    | Some t -> t
    | None ->
      let t : (Stdlib.Int.t, (string, unit) Hashtbl.t) Hashtbl.t = Hashtbl.create 32 in
      Hashtbl.add subj_presence_by_path path t;
      t

  let obj_presence_for_path (path : string)
    : (Stdlib.Int.t, (string, unit) Hashtbl.t) Hashtbl.t =
    match Hashtbl.find_opt obj_presence_by_path path with
    | Some t -> t
    | None ->
      let t : (Stdlib.Int.t, (string, unit) Hashtbl.t) Hashtbl.t = Hashtbl.create 32 in
      Hashtbl.add obj_presence_by_path path t;
      t

  let subj_rg_could_contain (path : string) (rg : Stdlib.Int.t)
    (bound_s : string option) : bool =
    match bound_s with
    | None -> true
    | Some s_tok ->
      match Hashtbl.find_opt subj_presence_by_path path with
      | None -> true
      | Some by_rg ->
        match Hashtbl.find_opt by_rg rg with
        | None -> true
        | Some s_set -> Hashtbl.mem s_set s_tok

  let obj_rg_could_contain (path : string) (rg : Stdlib.Int.t)
    (bound_o : string option) : bool =
    match bound_o with
    | None -> true
    | Some o_tok ->
      match Hashtbl.find_opt obj_presence_by_path path with
      | None -> true
      | Some by_rg ->
        match Hashtbl.find_opt by_rg rg with
        | None -> true
        | Some o_set -> Hashtbl.mem o_set o_tok
end

module Cottas_ondisk_runtime = struct
  open Stdlib
  (* `int` is shadowed by `open Prims` at the top of the file
     (Prims.int = Z.t).  Provide a local alias for plain OCaml int so
     hashtables and array indices keep the native machine-word type. *)
  type pint = Stdlib.Int.t

  (* Per-handle fast tables (Phase B perf shim). Keyed by artifact path.
     Built at open() time alongside the F* handle. The F* spec lookup
     functions in RDF.CottasStore.fst remain the verification source of
     truth — these tables ARE the same data, just in a hash-indexed
     OCaml shape so cottas_ondisk_search/decode hits don't blow up on
     900k-entry assoc-lists. *)
  type fast_tables = {
    (* token (raw column string) -> nat term-id *)
    ft_subj_tok_to_id  : (string, pint) Hashtbl.t;
    ft_pred_tok_to_id  : (string, pint) Hashtbl.t;
    ft_obj_tok_to_id   : (string, pint) Hashtbl.t;
    ft_graph_tok_to_id : (string, pint) Hashtbl.t;
    (* nat term-id -> typed RDF term (parsed once at open time) *)
    ft_id_to_subject   : (pint, RDF_Graph_Executable.subject) Hashtbl.t;
    ft_id_to_predicate : (pint, RDF_Graph_Executable.wf_iri) Hashtbl.t;
    ft_id_to_object    : (pint, RDF_Graph_Executable.rdf_term) Hashtbl.t;
    ft_id_to_graph     : (pint, RDF_Graph_Executable.iri) Hashtbl.t;
    (* nat term-id -> raw column-token string (for bound -> token
       conversion at search time) *)
    ft_id_to_subj_tok  : (pint, string) Hashtbl.t;
    ft_id_to_pred_tok  : (pint, string) Hashtbl.t;
    ft_id_to_obj_tok   : (pint, string) Hashtbl.t;
    ft_id_to_graph_tok : (pint, string) Hashtbl.t;
  }

  (* Cache by artifact path. *)
  let handles : (string, cottas_ondisk_handle) Hashtbl.t = Hashtbl.create 17
  let fast_table_cache : (string, fast_tables) Hashtbl.t = Hashtbl.create 17

  (* Pe4 instrumentation: cheap per-row-group RSS / fd / GC accounting.
     `ps -o rss=` returns kilobytes on macOS + Linux. fd count from
     /dev/fd. Used by the per-rg [pe4-trace] lines in search_fast and
     estimate_fast.

     Note: `int` is Prims.int (Z.t) inside this file, so all native-int
     scalars must use the `pint` alias declared above. *)
  let pe4_rss_mb () : pint =
    try
      let pid = Unix.getpid () in
      let cmd = Printf.sprintf "ps -o rss= -p %d 2>/dev/null" pid in
      let ic = Unix.open_process_in cmd in
      let line = try input_line ic with End_of_file -> "" in
      let _ = Unix.close_process_in ic in
      let s = String.trim line in
      if String.length s = 0 then (-1)
      else (try (int_of_string s) / 1024 with _ -> (-1))
    with _ -> (-1)

  let pe4_fd_count () : pint =
    let candidates = ["/dev/fd"; "/proc/self/fd"] in
    let rec try_all = function
      | [] -> (-1)
      | d :: rest ->
        (try Array.length (Sys.readdir d) with _ -> try_all rest)
    in try_all candidates

  let pe4_gc_mb () : pint =
    let s = Gc.quick_stat () in
    let words = s.Gc.heap_words in
    (* OCaml word = 8 bytes on 64-bit *)
    (words * 8) / (1024 * 1024)

  (* ---- Token parsing helpers. Convert an N-Triples-style raw column
         token (like "<iri>" / "_:b" / "\"lit\"^^<dt>" / "\"lit\"@en")
         to the matching F* RDF type. ---- *)

  let find_unescaped_quote s =
    let rec loop i escaped =
      if i >= String.length s then None
      else
        match s.[i] with
        | '"' when not escaped -> Some i
        | '\\' when not escaped -> loop (i + 1) true
        | _ -> loop (i + 1) false
    in
    loop 1 false

  let unescape_literal s =
    let b = Buffer.create (String.length s) in
    let rec loop i =
      if i >= String.length s then Buffer.contents b
      else
        match s.[i] with
        | '\\' when i + 1 < String.length s ->
          Buffer.add_char b s.[i + 1];
          loop (i + 2)
        | c ->
          Buffer.add_char b c;
          loop (i + 1)
    in
    loop 0

  let parse_iri_token s =
    let len = String.length s in
    if len >= 2 && s.[0] = '<' && s.[len - 1] = '>' then
      Some (String.sub s 1 (len - 2))
    else
      None

  let parse_literal_token s : RDF_Graph_Executable.wf_literal option =
    if String.length s < 2 || s.[0] <> '"' then None
    else match find_unescaped_quote s with
      | None -> None
      | Some q ->
        let lexical = unescape_literal (String.sub s 1 (q - 1)) in
        let suffix =
          if q + 1 >= String.length s then ""
          else String.sub s (q + 1) (String.length s - q - 1) in
        if suffix = "" then
          Some {
            RDF_Graph_Executable.lexical_form = lexical;
            datatype = RDF_Graph_Executable.xsd_string;
            lang_tag = FStar_Pervasives_Native.None;
          }
        else if String.length suffix >= 1 && suffix.[0] = '@' then
          Some {
            RDF_Graph_Executable.lexical_form = lexical;
            datatype = RDF_Graph_Executable.rdf_lang_string;
            lang_tag = FStar_Pervasives_Native.Some (String.sub suffix 1 (String.length suffix - 1));
          }
        else if String.length suffix >= 4 && String.sub suffix 0 2 = "^^" then
          (match parse_iri_token (String.sub suffix 2 (String.length suffix - 2)) with
           | Some dt ->
             Some {
               RDF_Graph_Executable.lexical_form = lexical;
               datatype = dt;
               lang_tag = FStar_Pervasives_Native.None;
             }
           | None -> None)
        else None

  let parse_subject_str s : RDF_Graph_Executable.subject option =
    match parse_iri_token s with
    | Some iri -> Some (RDF_Graph_Executable.S_IRI iri)
    | None ->
      if String.length s >= 2 && String.sub s 0 2 = "_:" then
        Some (RDF_Graph_Executable.S_BNode (String.sub s 2 (String.length s - 2)))
      else
        None

  let parse_object_str s : RDF_Graph_Executable.rdf_term option =
    match parse_iri_token s with
    | Some iri -> Some (RDF_Graph_Executable.T_IRI iri)
    | None ->
      if String.length s >= 2 && String.sub s 0 2 = "_:" then
        Some (RDF_Graph_Executable.T_BNode (String.sub s 2 (String.length s - 2)))
      else match parse_literal_token s with
        | Some lit -> Some (RDF_Graph_Executable.T_Literal lit)
        | None -> None

  (* ---- Distinct-token collector. We walk all row groups via the F*
         multi-row-group decoder, then dedupe to build the dictionary.
         Phase B drops the per-row int[] columns; we only need the
         distinct token list (indexed by id) + a raw-token-keyed
         revmap. ---- *)

  let collect_distinct (artifact_path : string) (col_idx : pint)
    : (string list * (string, pint) Hashtbl.t * pint) =
    Printf.eprintf "[qof3-trace] collect_distinct col=%d path=%s\n%!" col_idx artifact_path;
    match Parquet_Footer.probe_parquet_column_decode_all_row_groups
            artifact_path (Z.of_int col_idx) with
    | FStar_Pervasives_Native.None ->
      Printf.eprintf "[qof3-FATAL] collect_distinct: could not decode column %d\n%!" col_idx;
      failwith (Printf.sprintf "COTTAS on-disk: could not decode column %d" col_idx)
    | FStar_Pervasives_Native.Some lst ->
      let revmap : (string, pint) Hashtbl.t = Hashtbl.create 257 in
      let strs_rev = ref [] in
      let next_id = ref 0 in
      let row_count = ref 0 in
      List.iter (function
        | FStar_Pervasives_Native.None ->
          Printf.eprintf "[qof3-FATAL] collect_distinct: missing cell in column %d\n%!" col_idx;
          failwith (Printf.sprintf "COTTAS on-disk: missing cell in column %d" col_idx)
        | FStar_Pervasives_Native.Some r ->
          incr row_count;
          if not (Hashtbl.mem revmap r) then begin
            Hashtbl.add revmap r !next_id;
            strs_rev := r :: !strs_rev;
            incr next_id
          end) lst;
      Printf.eprintf "[qof3-trace] collect_distinct col=%d distinct=%d rows=%d\n%!"
        col_idx !next_id !row_count;
      (List.rev !strs_rev, revmap, !row_count)

  (* Same shape as collect_distinct, but for the graph column: skip the
     "DEFAULT" sentinel so it never enters the dictionary. *)
  let collect_distinct_graph (artifact_path : string) (col_idx : pint)
    : (string list * (string, pint) Hashtbl.t * pint) =
    Printf.eprintf "[qof3-trace] collect_distinct_graph col=%d path=%s\n%!" col_idx artifact_path;
    match Parquet_Footer.probe_parquet_column_decode_all_row_groups
            artifact_path (Z.of_int col_idx) with
    | FStar_Pervasives_Native.None ->
      Printf.eprintf "[qof3-FATAL] collect_distinct_graph: could not decode column %d\n%!" col_idx;
      failwith (Printf.sprintf "COTTAS on-disk: could not decode column %d" col_idx)
    | FStar_Pervasives_Native.Some lst ->
      let revmap : (string, pint) Hashtbl.t = Hashtbl.create 17 in
      let strs_rev = ref [] in
      let next_id = ref 0 in
      let row_count = ref 0 in
      List.iter (function
        | FStar_Pervasives_Native.None ->
          Printf.eprintf "[qof3-FATAL] collect_distinct_graph: missing cell in column %d\n%!" col_idx;
          failwith (Printf.sprintf "COTTAS on-disk: missing cell in column %d" col_idx)
        | FStar_Pervasives_Native.Some r ->
          incr row_count;
          if r <> "DEFAULT" && not (Hashtbl.mem revmap r) then begin
            Hashtbl.add revmap r !next_id;
            strs_rev := r :: !strs_rev;
            incr next_id
          end) lst;
      Printf.eprintf "[qof3-trace] collect_distinct_graph col=%d named_graphs=%d rows=%d\n%!"
        col_idx !next_id !row_count;
      (List.rev !strs_rev, revmap, !row_count)

  let build_summary_for_handle artifact_path total_rows graph_count
    : Parser_BallyhooCOTTAS.cottas_artifact_summary FStar_Pervasives_Native.option =
    let row_groups =
      match Parquet_Footer.probe_parquet_row_group_count artifact_path with
      | FStar_Pervasives_Native.None -> Z.one
      | FStar_Pervasives_Native.Some n -> n in
    let mk_col kind : Parser_BallyhooCOTTAS.cottas_column_summary =
      {
        ccs_kind = kind;
        ccs_num_values = Z.of_int total_rows;
        ccs_null_count = Z.zero;
        ccs_encoding = Parser_BallyhooCOTTAS.CE_Delta;
      } in
    FStar_Pervasives_Native.Some {
      Parser_BallyhooCOTTAS.cas_path = artifact_path;
      cas_num_quads = Z.of_int total_rows;
      cas_num_row_groups = row_groups;
      cas_dictionary =
        FStar_Pervasives_Native.Some {
          Parser_BallyhooCOTTAS.cds_num_terms = Z.of_int total_rows;
          cds_num_graphs = Z.of_int graph_count;
          cds_bytes_strings = Z.zero;
        };
      cas_row_groups = [{
        Parser_BallyhooCOTTAS.crgs_index = Z.zero;
        crgs_num_rows = Z.of_int total_rows;
        crgs_columns = [
          mk_col Parser_BallyhooCOTTAS.CC_Subject;
          mk_col Parser_BallyhooCOTTAS.CC_Predicate;
          mk_col Parser_BallyhooCOTTAS.CC_Object;
          mk_col Parser_BallyhooCOTTAS.CC_Graph
        ];
      }];
    }

  (* Tail-recursive mapi-like helpers. Stdlib's List.mapi is not tail-
     recursive and blows the stack on the parliament corpus's 900k-entry
     subject/object lists. *)
  let mapi_tr (f : pint -> 'a -> 'b) (xs : 'a list) : 'b list =
    let rec loop i acc = function
      | [] -> List.rev acc
      | hd :: tl -> loop (i + 1) ((f i hd) :: acc) tl in
    loop 0 [] xs

  let mk_subj_canonical_revmap (xs : RDF_Graph_Executable.subject list)
    : (Prims.string * Prims.nat) Prims.list =
    mapi_tr (fun i s -> (subject_to_revmap_key s, Z.of_int i)) xs

  let mk_iri_canonical_revmap (xs : RDF_Graph_Executable.iri list)
    : (Prims.string * Prims.nat) Prims.list =
    mapi_tr (fun i s -> (iri_to_revmap_key s, Z.of_int i)) xs

  let mk_obj_canonical_revmap (xs : RDF_Graph_Executable.rdf_term list)
    : (Prims.string * Prims.nat) Prims.list =
    mapi_tr (fun i s -> (object_to_revmap_key s, Z.of_int i)) xs

  (* Build the F* handle (Phase B): walk all row groups (every column),
     build distinct-token dictionaries + parallel revmaps, parse each
     dictionary entry to its typed RDF shape. The per-row int[] columns
     of Phase A are GONE — search/estimate work directly via parquet
     row-group probes in F* (or, in practice, via the fast_tables shim
     below). *)
  (* Bet7 lazy-open (issue #100, 2026-04-26): skip eager collection of
     ALL four columns. Each `collect_distinct` decodes every row group's
     data page for that column (~25 s + several hundred MB transient
     allocations on the parliament 3.14M-quad corpus). Total open used
     to be ~106 s + 1.4 GB RSS — far too slow + heavy for an interactive
     demo. After Bet7 the open is footer-only; the per-column
     dictionaries + Hashtbls are populated on demand by
     `Cottas_ondisk_lazy.ensure_*_loaded` from inside the *_fast
     lookup functions (search/estimate/encode/decode/predicate_present).

     Trade-off: the FIRST query that needs a column's dict pays the
     populate cost (~14 s for predicates, ~30 s each for subjects /
     objects on parliament). Subsequent queries are fast. For the
     daemon use case this means the listener comes up + binds the
     port in <1 s; the first SPARQL request takes the populate hit;
     warm requests are fast. cottas_ondisk_named_graphs called
     immediately post-open returns [] until first encode_graph
     populates — acceptable for parliament (which has 0 named
     graphs); for corpora WITH named graphs, snapshot_iris is
     populated after the first query.

     Compatibility with Aleph6's search_fast_limited (added by patch
     cottas_ondisk_zz_aleph6_count_limit.sh, runs after this patch):
     Aleph6's body calls ensure_subjects_loaded / ensure_objects_loaded
     (which are present here) but does NOT call ensure_predicates_loaded
     / ensure_graphs_loaded (because at the time Aleph6 was written
     this patch only deferred s+o). The Aleph6 patch now applies an
     extra fixup further below to add the missing pred+graph hooks. *)
  let build_handle_and_tables artifact_path
    : (cottas_ondisk_handle * fast_tables) =
    Printf.eprintf "[bet7-trace] build_handle path=%s (lazy open: defer all 4 columns)\n%!" artifact_path;
    let n_rows = match Parquet_Footer.probe_parquet_num_rows artifact_path with
      | FStar_Pervasives_Native.Some n -> Z.to_int n
      | FStar_Pervasives_Native.None -> 0 in
    let s_strs = [] in
    let s_tok_to_id : (string, pint) Hashtbl.t = Hashtbl.create 16 in
    let n_rows_s = n_rows in
    let p_strs = [] in
    let p_tok_to_id : (string, pint) Hashtbl.t = Hashtbl.create 16 in
    let n_rows_p = n_rows in
    let o_strs = [] in
    let o_tok_to_id : (string, pint) Hashtbl.t = Hashtbl.create 16 in
    let n_rows_o = n_rows in
    let g_strs = [] in
    let g_tok_to_id : (string, pint) Hashtbl.t = Hashtbl.create 16 in
    let n_rows_g = n_rows in
    let _ = (n_rows_s, n_rows_p, n_rows_o, n_rows_g) in
    if n_rows_s <> n_rows_p || n_rows_s <> n_rows_o || n_rows_s <> n_rows_g then
      Printf.eprintf "[qof3-FATAL] build_handle: row counts disagree s=%d p=%d o=%d g=%d\n%!"
        n_rows_s n_rows_p n_rows_o n_rows_g;
    let n_rows = n_rows_s in
    Printf.eprintf "[qof3-trace] build_handle: distinct s=%d p=%d o=%d g=%d total_rows=%d\n%!"
      (List.length s_strs) (List.length p_strs) (List.length o_strs) (List.length g_strs) n_rows;
    (* Parse each distinct token to its F* RDF shape. *)
    let parse_subjects =
      mapi_tr (fun i raw ->
        match parse_subject_str raw with
        | Some s -> s
        | None ->
          Printf.eprintf "[qof3-FATAL] build_handle: invalid subject token id=%d val=%s\n%!" i raw;
          failwith (Printf.sprintf "COTTAS on-disk: invalid subject token %s" raw)) in
    let parse_predicates =
      mapi_tr (fun i raw ->
        match parse_iri_token raw with
        | Some iri -> (iri : RDF_Graph_Executable.wf_iri)
        | None ->
          Printf.eprintf "[qof3-FATAL] build_handle: invalid predicate token id=%d val=%s\n%!" i raw;
          failwith (Printf.sprintf "COTTAS on-disk: invalid predicate token %s" raw)) in
    let parse_objects =
      mapi_tr (fun i raw ->
        match parse_object_str raw with
        | Some t -> t
        | None ->
          Printf.eprintf "[qof3-FATAL] build_handle: invalid object token id=%d val=%s\n%!" i raw;
          failwith (Printf.sprintf "COTTAS on-disk: invalid object token %s" raw)) in
    let parse_graphs =
      mapi_tr (fun i raw ->
        match parse_iri_token raw with
        | Some iri -> (iri : RDF_Graph_Executable.iri)
        | None ->
          Printf.eprintf "[qof3-FATAL] build_handle: invalid graph token id=%d val=%s\n%!" i raw;
          failwith (Printf.sprintf "COTTAS on-disk: invalid graph token %s" raw)) in
    let coh_subjects   = parse_subjects   s_strs in
    let coh_predicates = parse_predicates p_strs in
    let coh_objects    = parse_objects    o_strs in
    let coh_graphs     = parse_graphs     g_strs in
    (* Build id-to-* hashtables from the parsed lists. *)
    let id_to_subject   : (pint, RDF_Graph_Executable.subject) Hashtbl.t =
      Hashtbl.create (List.length coh_subjects + 17) in
    List.iteri (fun i s -> Hashtbl.add id_to_subject i s) coh_subjects;
    let id_to_predicate : (pint, RDF_Graph_Executable.wf_iri) Hashtbl.t =
      Hashtbl.create (List.length coh_predicates + 17) in
    List.iteri (fun i p -> Hashtbl.add id_to_predicate i p) coh_predicates;
    let id_to_object    : (pint, RDF_Graph_Executable.rdf_term) Hashtbl.t =
      Hashtbl.create (List.length coh_objects + 17) in
    List.iteri (fun i o -> Hashtbl.add id_to_object i o) coh_objects;
    let id_to_graph     : (pint, RDF_Graph_Executable.iri) Hashtbl.t =
      Hashtbl.create (List.length coh_graphs + 17) in
    List.iteri (fun i g -> Hashtbl.add id_to_graph i g) coh_graphs;
    let id_to_subj_tok  : (pint, string) Hashtbl.t = Hashtbl.create (List.length s_strs + 17) in
    List.iteri (fun i s -> Hashtbl.add id_to_subj_tok  i s) s_strs;
    let id_to_pred_tok  : (pint, string) Hashtbl.t = Hashtbl.create (List.length p_strs + 17) in
    List.iteri (fun i s -> Hashtbl.add id_to_pred_tok  i s) p_strs;
    let id_to_obj_tok   : (pint, string) Hashtbl.t = Hashtbl.create (List.length o_strs + 17) in
    List.iteri (fun i s -> Hashtbl.add id_to_obj_tok   i s) o_strs;
    let id_to_graph_tok : (pint, string) Hashtbl.t = Hashtbl.create (List.length g_strs + 17) in
    List.iteri (fun i s -> Hashtbl.add id_to_graph_tok i s) g_strs;
    let tables : fast_tables = {
      ft_subj_tok_to_id  = s_tok_to_id;
      ft_pred_tok_to_id  = p_tok_to_id;
      ft_obj_tok_to_id   = o_tok_to_id;
      ft_graph_tok_to_id = g_tok_to_id;
      ft_id_to_subject   = id_to_subject;
      ft_id_to_predicate = id_to_predicate;
      ft_id_to_object    = id_to_object;
      ft_id_to_graph     = id_to_graph;
      ft_id_to_subj_tok  = id_to_subj_tok;
      ft_id_to_pred_tok  = id_to_pred_tok;
      ft_id_to_obj_tok   = id_to_obj_tok;
      ft_id_to_graph_tok = id_to_graph_tok;
    } in
    let handle : cottas_ondisk_handle = {
      coh_path = artifact_path;
      coh_summary = build_summary_for_handle artifact_path n_rows (List.length g_strs);
      coh_subjects;
      coh_predicates;
      coh_objects;
      coh_graphs;
      coh_subj_revmap  = mk_subj_canonical_revmap coh_subjects;
      coh_pred_revmap  = mk_iri_canonical_revmap  coh_predicates;
      coh_obj_revmap   = mk_obj_canonical_revmap  coh_objects;
      coh_graph_revmap = mk_iri_canonical_revmap  coh_graphs;
      coh_subjects_raw   = s_strs;
      coh_predicates_raw = p_strs;
      coh_objects_raw    = o_strs;
      coh_graphs_raw     = g_strs;
      coh_subj_raw_revmap  = mapi_tr (fun i s -> (s, Z.of_int i)) s_strs;
      coh_pred_raw_revmap  = mapi_tr (fun i s -> (s, Z.of_int i)) p_strs;
      coh_obj_raw_revmap   = mapi_tr (fun i s -> (s, Z.of_int i)) o_strs;
      coh_graph_raw_revmap = mapi_tr (fun i s -> (s, Z.of_int i)) g_strs;
    } in
    (handle, tables)


  (* Bet7 lazy populators (issue #100, 2026-04-26).
     Called from the *_fast functions on first lookup that needs the
     subject or object tables. Idempotent — guarded by
     Cottas_ondisk_lazy.is_*_loaded. *)
  let ensure_subjects_loaded (h : cottas_ondisk_handle) (tables : fast_tables) : unit =
    if not (Cottas_ondisk_lazy.is_subj_loaded h.coh_path) then begin
      Printf.eprintf "[bet7-trace] ensure_subjects_loaded: lazy populate path=%s\n%!" h.coh_path;
      (* tet3: walk subject column per-rg to record per-rg presence
         (vs. the previous batched collect_distinct that lost which rg
         each token came from). *)
      let presence = Cottas_ondisk_lazy.subj_presence_for_path h.coh_path in
      let next_id = ref (Hashtbl.length tables.ft_subj_tok_to_id) in
      let rg_count = match Parquet_Footer.probe_parquet_row_group_count h.coh_path with
        | FStar_Pervasives_Native.None -> 0
        | FStar_Pervasives_Native.Some n -> Z.to_int n in
      for rg = 0 to rg_count - 1 do
        let rg_set : (string, unit) Hashtbl.t = Hashtbl.create 4096 in
        (match Parquet_Footer.probe_parquet_column_decode_in_row_group
                 h.coh_path (Z.of_int rg) Z.zero with
         | FStar_Pervasives_Native.None ->
           Printf.eprintf "[tet3-WARN] ensure_subjects_loaded: rg=%d decode failed\n%!" rg
         | FStar_Pervasives_Native.Some lst ->
           List.iter (function
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some raw ->
               (* Record presence for this rg. *)
               if not (Hashtbl.mem rg_set raw) then
                 Hashtbl.add rg_set raw ();
               (* Build global tok_to_id / id_to_subject / id_to_subj_tok
                  the same way collect_distinct would have. *)
               if not (Hashtbl.mem tables.ft_subj_tok_to_id raw) then begin
                 let id = !next_id in
                 incr next_id;
                 Hashtbl.add tables.ft_subj_tok_to_id raw id;
                 (match parse_subject_str raw with
                  | Some s ->
                    Hashtbl.replace tables.ft_id_to_subject  id s;
                    Hashtbl.replace tables.ft_id_to_subj_tok id raw
                  | None ->
                    Printf.eprintf "[tet3-WARN] ensure_subjects_loaded: invalid subject token id=%d val=%s\n%!" id raw)
               end) lst);
        Hashtbl.replace presence rg rg_set;
        if rg = 0 || rg = rg_count - 1 || rg mod 5 = 0 then
          Printf.eprintf "[tet3-trace] ensure_subjects_loaded rg=%d/%d distinct_subjs=%d\n%!"
            rg rg_count (Hashtbl.length rg_set)
      done;
      Cottas_ondisk_lazy.mark_subj_loaded h.coh_path;
      Gc.full_major ();
      Printf.eprintf "[bet7-trace] ensure_subjects_loaded: %d distinct subjects (tet3 per-rg presence built for %d rgs)\n%!"
        (Hashtbl.length tables.ft_subj_tok_to_id) rg_count
    end

  let ensure_objects_loaded (h : cottas_ondisk_handle) (tables : fast_tables) : unit =
    if not (Cottas_ondisk_lazy.is_obj_loaded h.coh_path) then begin
      Printf.eprintf "[bet7-trace] ensure_objects_loaded: lazy populate path=%s\n%!" h.coh_path;
      (* tet3: walk object column per-rg to record per-rg presence
         (vs. the previous batched collect_distinct that lost which rg
         each token came from). *)
      let presence = Cottas_ondisk_lazy.obj_presence_for_path h.coh_path in
      let next_id = ref (Hashtbl.length tables.ft_obj_tok_to_id) in
      let rg_count = match Parquet_Footer.probe_parquet_row_group_count h.coh_path with
        | FStar_Pervasives_Native.None -> 0
        | FStar_Pervasives_Native.Some n -> Z.to_int n in
      for rg = 0 to rg_count - 1 do
        let rg_set : (string, unit) Hashtbl.t = Hashtbl.create 4096 in
        (match Parquet_Footer.probe_parquet_column_decode_in_row_group
                 h.coh_path (Z.of_int rg) (Z.of_int 2) with
         | FStar_Pervasives_Native.None ->
           Printf.eprintf "[tet3-WARN] ensure_objects_loaded: rg=%d decode failed\n%!" rg
         | FStar_Pervasives_Native.Some lst ->
           List.iter (function
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some raw ->
               (* Record presence for this rg. *)
               if not (Hashtbl.mem rg_set raw) then
                 Hashtbl.add rg_set raw ();
               (* Build global tok_to_id / id_to_object / id_to_obj_tok
                  the same way collect_distinct would have. *)
               if not (Hashtbl.mem tables.ft_obj_tok_to_id raw) then begin
                 let id = !next_id in
                 incr next_id;
                 Hashtbl.add tables.ft_obj_tok_to_id raw id;
                 (match parse_object_str raw with
                  | Some o ->
                    Hashtbl.replace tables.ft_id_to_object  id o;
                    Hashtbl.replace tables.ft_id_to_obj_tok id raw
                  | None ->
                    Printf.eprintf "[tet3-WARN] ensure_objects_loaded: invalid object token id=%d val=%s\n%!" id raw)
               end) lst);
        Hashtbl.replace presence rg rg_set;
        if rg = 0 || rg = rg_count - 1 || rg mod 5 = 0 then
          Printf.eprintf "[tet3-trace] ensure_objects_loaded rg=%d/%d distinct_objs=%d\n%!"
            rg rg_count (Hashtbl.length rg_set)
      done;
      Cottas_ondisk_lazy.mark_obj_loaded h.coh_path;
      Gc.full_major ();
      Printf.eprintf "[bet7-trace] ensure_objects_loaded: %d distinct objects (tet3 per-rg presence built for %d rgs)\n%!"
        (Hashtbl.length tables.ft_obj_tok_to_id) rg_count
    end

  let ensure_predicates_loaded (h : cottas_ondisk_handle) (tables : fast_tables) : unit =
    if not (Cottas_ondisk_lazy.is_pred_loaded h.coh_path) then begin
      Printf.eprintf "[bet7-trace] ensure_predicates_loaded: lazy populate path=%s\n%!" h.coh_path;
      (* yod6: walk predicate column per-rg to record per-rg presence
         (vs. the previous batched collect_distinct that lost which rg
         each token came from). *)
      let presence = Cottas_ondisk_lazy.presence_for_path h.coh_path in
      let next_id = ref (Hashtbl.length tables.ft_pred_tok_to_id) in
      let rg_count = match Parquet_Footer.probe_parquet_row_group_count h.coh_path with
        | FStar_Pervasives_Native.None -> 0
        | FStar_Pervasives_Native.Some n -> Z.to_int n in
      for rg = 0 to rg_count - 1 do
        let rg_set : (string, unit) Hashtbl.t = Hashtbl.create 16 in
        (match Parquet_Footer.probe_parquet_column_decode_in_row_group
                 h.coh_path (Z.of_int rg) Z.one with
         | FStar_Pervasives_Native.None ->
           Printf.eprintf "[yod6-WARN] ensure_predicates_loaded: rg=%d decode failed\n%!" rg
         | FStar_Pervasives_Native.Some lst ->
           List.iter (function
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some raw ->
               (* Record presence for this rg. *)
               if not (Hashtbl.mem rg_set raw) then
                 Hashtbl.add rg_set raw ();
               (* Build global tok_to_id / id_to_predicate / id_to_pred_tok
                  the same way collect_distinct would have. *)
               if not (Hashtbl.mem tables.ft_pred_tok_to_id raw) then begin
                 let id = !next_id in
                 incr next_id;
                 Hashtbl.add tables.ft_pred_tok_to_id raw id;
                 (match parse_iri_token raw with
                  | Some iri ->
                    Hashtbl.replace tables.ft_id_to_predicate id iri;
                    Hashtbl.replace tables.ft_id_to_pred_tok  id raw
                  | None ->
                    Printf.eprintf "[yod6-WARN] ensure_predicates_loaded: invalid predicate token id=%d val=%s\n%!" id raw)
               end) lst);
        Hashtbl.replace presence rg rg_set;
        if rg = 0 || rg = rg_count - 1 || rg mod 5 = 0 then
          Printf.eprintf "[yod6-trace] ensure_predicates_loaded rg=%d/%d distinct_preds=%d\n%!"
            rg rg_count (Hashtbl.length rg_set)
      done;
      Cottas_ondisk_lazy.mark_pred_loaded h.coh_path;
      Gc.full_major ();
      Printf.eprintf "[bet7-trace] ensure_predicates_loaded: %d distinct predicates (yod6 per-rg presence built for %d rgs)\n%!"
        (Hashtbl.length tables.ft_pred_tok_to_id) rg_count
    end

  let ensure_graphs_loaded (h : cottas_ondisk_handle) (tables : fast_tables) : unit =
    if not (Cottas_ondisk_lazy.is_graph_loaded h.coh_path) then begin
      Printf.eprintf "[bet7-trace] ensure_graphs_loaded: lazy populate path=%s\n%!" h.coh_path;
      let (g_strs, g_tok_to_id, _n) = collect_distinct_graph h.coh_path 3 in
      Hashtbl.iter (fun k v -> Hashtbl.replace tables.ft_graph_tok_to_id k v) g_tok_to_id;
      List.iteri (fun i raw ->
        match parse_iri_token raw with
        | Some iri ->
          Hashtbl.replace tables.ft_id_to_graph     i iri;
          Hashtbl.replace tables.ft_id_to_graph_tok i raw
        | None ->
          Printf.eprintf "[bet7-WARN] ensure_graphs_loaded: invalid graph token id=%d val=%s\n%!" i raw)
        g_strs;
      Cottas_ondisk_lazy.mark_graph_loaded h.coh_path;
      Gc.full_major ();
      Printf.eprintf "[bet7-trace] ensure_graphs_loaded: %d distinct graphs\n%!"
        (Hashtbl.length tables.ft_graph_tok_to_id)
    end

  let load_handle artifact_path : cottas_ondisk_handle =
    Printf.eprintf "[qof3-trace] load_handle path=%s\n%!" artifact_path;
    match Hashtbl.find_opt handles artifact_path with
    | Some h ->
      Printf.eprintf "[qof3-trace] load_handle: cache hit\n%!"; h
    | None ->
      let (h, tables) = build_handle_and_tables artifact_path in
      Hashtbl.add handles artifact_path h;
      Hashtbl.add fast_table_cache artifact_path tables;
      h

  let tables_for handle : fast_tables =
    match Hashtbl.find_opt fast_table_cache handle.coh_path with
    | Some t -> t
    | None ->
      (* Re-build (defensive: shouldn't happen if open() always populates). *)
      let (_h, tables) = build_handle_and_tables handle.coh_path in
      Hashtbl.add fast_table_cache handle.coh_path tables;
      tables

  (* ---- Fast search/estimate (Hashtbl-backed; semantically equivalent
         to the F* spec walk_row_groups_search/estimate but O(1) per
         row instead of O(N) per revmap_lookup). ---- *)

  let bound_id_to_token (id_to_tok : (pint, string) Hashtbl.t)
    (b : Prims.nat FStar_Pervasives_Native.option) : string option =
    match b with
    | FStar_Pervasives_Native.None -> None
    | FStar_Pervasives_Native.Some i ->
      Hashtbl.find_opt id_to_tok (Z.to_int i)

  let cell_match_str expected actual =
    match expected with
    | None -> true
    | Some s -> s = actual

  (* Walk all row groups, decode each column lazily, filter by string
     bound, build cottas_qp_row via Hashtbl lookups. Mirrors
     RDF_CottasStore.walk_row_groups_search but with O(1) revmap
     lookups for build_qp_row. *)
  let search_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp)
    : Parser_BallyhooCOTTAS.cottas_qp_row list =
    let path = h.coh_path in
    let tables = tables_for h in
    (* search needs all four columns: build_qp_row reads every cell
       through the *_tok_to_id Hashtbls, and bound_id_to_token reads
       *_id_to_*_tok. *)
    ensure_subjects_loaded   h tables;
    ensure_predicates_loaded h tables;
    ensure_objects_loaded    h tables;
    ensure_graphs_loaded     h tables;
    let bound_s = bound_id_to_token tables.ft_id_to_subj_tok  bound.Parser_BallyhooCOTTAS.cbqp_s in
    let bound_p = bound_id_to_token tables.ft_id_to_pred_tok  bound.Parser_BallyhooCOTTAS.cbqp_p in
    let bound_o = bound_id_to_token tables.ft_id_to_obj_tok   bound.Parser_BallyhooCOTTAS.cbqp_o in
    let bound_g = bound_id_to_token tables.ft_id_to_graph_tok bound.Parser_BallyhooCOTTAS.cbqp_g in
    Printf.eprintf "[qof3-trace] search_fast: bound s=%s p=%s o=%s g=%s\n%!"
      (match bound_s with None -> "_" | Some s -> "<sub>" ^ s ^ "</sub>")
      (match bound_p with None -> "_" | Some s -> s)
      (match bound_o with None -> "_" | Some s -> "<obj>")
      (match bound_g with None -> "_" | Some s -> s);
    let rg_count = match Parquet_Footer.probe_parquet_row_group_count path with
      | FStar_Pervasives_Native.None -> 0
      | FStar_Pervasives_Native.Some n -> Z.to_int n in
    Printf.eprintf "[qof3-trace] search_fast: rg_count=%d\n%!" rg_count;
    Printf.eprintf "[pe4-trace] search_fast pre-walk rss=%dMB heap=%dMB fd=%d\n%!"
      (pe4_rss_mb ()) (pe4_gc_mb ()) (pe4_fd_count ());
    let acc = ref [] in
    let n_matches = ref 0 in
    let arr_of_col col_opt =
      match col_opt with
      | FStar_Pervasives_Native.None -> [||]
      | FStar_Pervasives_Native.Some lst -> Array.of_list lst in
    let cell_of = function
      | FStar_Pervasives_Native.Some s -> s
      | FStar_Pervasives_Native.None -> "" in
    let walk_rg rg =
      Printf.eprintf "[pe4-trace] search_fast rg=%d enter rss=%dMB heap=%dMB matches=%d\n%!"
        rg (pe4_rss_mb ()) (pe4_gc_mb ()) !n_matches;
      let s_lst = Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int rg) Z.zero in
      Printf.eprintf "[pe4-trace] search_fast rg=%d decoded col=0 (subject) rss=%dMB heap=%dMB\n%!"
        rg (pe4_rss_mb ()) (pe4_gc_mb ());
      let s_arr = arr_of_col s_lst in
      Printf.eprintf "[pe4-trace] search_fast rg=%d arrayified col=0 n=%d rss=%dMB heap=%dMB\n%!"
        rg (Array.length s_arr) (pe4_rss_mb ()) (pe4_gc_mb ());
      let p_lst = Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int rg) Z.one in
      Printf.eprintf "[pe4-trace] search_fast rg=%d decoded col=1 (predicate) rss=%dMB heap=%dMB\n%!"
        rg (pe4_rss_mb ()) (pe4_gc_mb ());
      let p_arr = arr_of_col p_lst in
      let o_lst = Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int rg) (Z.of_int 2) in
      Printf.eprintf "[pe4-trace] search_fast rg=%d decoded col=2 (object) rss=%dMB heap=%dMB\n%!"
        rg (pe4_rss_mb ()) (pe4_gc_mb ());
      let o_arr = arr_of_col o_lst in
      let g_lst = Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int rg) (Z.of_int 3) in
      Printf.eprintf "[pe4-trace] search_fast rg=%d decoded col=3 (graph) rss=%dMB heap=%dMB\n%!"
        rg (pe4_rss_mb ()) (pe4_gc_mb ());
      let g_arr = arr_of_col g_lst in
      let n = Array.length s_arr in
      if Array.length p_arr <> n || Array.length o_arr <> n || Array.length g_arr <> n then
        Printf.eprintf "[qof3-FATAL] search_fast: row-group %d column lengths disagree (s=%d p=%d o=%d g=%d)\n%!"
          rg n (Array.length p_arr) (Array.length o_arr) (Array.length g_arr)
      else begin
        Printf.eprintf "[pe4-trace] search_fast rg=%d filter-loop start n=%d rss=%dMB heap=%dMB\n%!"
          rg n (pe4_rss_mb ()) (pe4_gc_mb ());
        for i = 0 to n - 1 do
          let s_tok = cell_of s_arr.(i) in
          let p_tok = cell_of p_arr.(i) in
          let o_tok = cell_of o_arr.(i) in
          let g_tok = cell_of g_arr.(i) in
          if cell_match_str bound_s s_tok &&
             cell_match_str bound_p p_tok &&
             cell_match_str bound_o o_tok &&
             cell_match_str bound_g g_tok
          then begin
            let s_id = Hashtbl.find_opt tables.ft_subj_tok_to_id  s_tok in
            let p_id = Hashtbl.find_opt tables.ft_pred_tok_to_id  p_tok in
            let o_id = Hashtbl.find_opt tables.ft_obj_tok_to_id   o_tok in
            let g_id =
              if g_tok = "DEFAULT" then None
              else Hashtbl.find_opt tables.ft_graph_tok_to_id g_tok in
            let opt_to_z = function
              | None -> FStar_Pervasives_Native.None
              | Some i -> FStar_Pervasives_Native.Some (Z.of_int i) in
            acc := {
              Parser_BallyhooCOTTAS.cqpr_s = opt_to_z s_id;
              cqpr_p = opt_to_z p_id;
              cqpr_o = opt_to_z o_id;
              cqpr_g = opt_to_z g_id;
            } :: !acc;
            incr n_matches
          end
        done;
        Printf.eprintf "[pe4-trace] search_fast rg=%d done matches_so_far=%d rss=%dMB heap=%dMB\n%!"
          rg !n_matches (pe4_rss_mb ()) (pe4_gc_mb ())
      end
    in
    let n_skipped = ref 0 in
    for rg = 0 to rg_count - 1 do
      let could_p = Cottas_ondisk_lazy.pred_rg_could_contain path rg bound_p in
      let could_s = Cottas_ondisk_lazy.subj_rg_could_contain path rg bound_s in
      let could_o = Cottas_ondisk_lazy.obj_rg_could_contain  path rg bound_o in
      if not (could_p && could_s && could_o) then begin
        incr n_skipped;
        if !n_skipped <= 3 || !n_skipped mod 5 = 0 then
          Printf.eprintf "[tet3-trace] search_fast rg=%d skipped (could_p=%b could_s=%b could_o=%b)\n%!"
            rg could_p could_s could_o
      end else begin
        try walk_rg rg
        with e ->
          let bt = Printexc.get_backtrace () in
          Printf.eprintf "[pe4-FATAL] search_fast rg=%d EXCEPTION: %s\nbacktrace=%s\n%!"
            rg (Printexc.to_string e) bt;
          raise e
      end
    done;
    Printf.eprintf "[tet3-trace] search_fast: skipped %d/%d rg(s) (s=%s p=%s o=%s)\n%!"
      !n_skipped rg_count
      (match bound_s with None -> "_" | Some _ -> "<sub>")
      (match bound_p with None -> "_" | Some s -> s)
      (match bound_o with None -> "_" | Some _ -> "<obj>");
    Printf.eprintf "[qof3-trace] search_fast: matched %d row(s) across %d row group(s)\n%!" !n_matches rg_count;
    Printf.eprintf "[pe4-trace] search_fast post-walk rss=%dMB heap=%dMB matches=%d\n%!"
      (pe4_rss_mb ()) (pe4_gc_mb ()) !n_matches;
    List.rev !acc

  (* aleph6: search_fast_limited installed.
     Same as search_fast but stops once `limit` matches accumulate.
     Used by F*-side cottas_ondisk_search_limited for LIMIT pushdown
     (issue #100, 2026-04-26). Keeps Bet7 lazy-load semantics intact —
     ensure_subjects_loaded / ensure_objects_loaded run on entry, then
     the per-rg walk uses O(1) Hashtbl lookups in build_qp_row.
     Matching predicate is byte-identical to search_fast. *)
  let search_fast_limited (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) (limit : pint)
    : Parser_BallyhooCOTTAS.cottas_qp_row list =
    let path = h.coh_path in
    let tables = tables_for h in
    ensure_subjects_loaded h tables;
    ensure_objects_loaded  h tables;
    let bound_s = bound_id_to_token tables.ft_id_to_subj_tok  bound.Parser_BallyhooCOTTAS.cbqp_s in
    let bound_p = bound_id_to_token tables.ft_id_to_pred_tok  bound.Parser_BallyhooCOTTAS.cbqp_p in
    let bound_o = bound_id_to_token tables.ft_id_to_obj_tok   bound.Parser_BallyhooCOTTAS.cbqp_o in
    let bound_g = bound_id_to_token tables.ft_id_to_graph_tok bound.Parser_BallyhooCOTTAS.cbqp_g in
    Printf.eprintf "[aleph6-trace] search_fast_limited: limit=%d bound s=%s p=%s o=%s g=%s\n%!"
      limit
      (match bound_s with None -> "_" | Some _ -> "<sub>")
      (match bound_p with None -> "_" | Some s -> s)
      (match bound_o with None -> "_" | Some _ -> "<obj>")
      (match bound_g with None -> "_" | Some s -> s);
    let rg_count = match Parquet_Footer.probe_parquet_row_group_count path with
      | FStar_Pervasives_Native.None -> 0
      | FStar_Pervasives_Native.Some n -> Z.to_int n in
    let acc = ref [] in
    let n_matches = ref 0 in
    let arr_of_col col_opt =
      match col_opt with
      | FStar_Pervasives_Native.None -> [||]
      | FStar_Pervasives_Native.Some lst -> Array.of_list lst in
    let cell_of = function
      | FStar_Pervasives_Native.Some s -> s
      | FStar_Pervasives_Native.None -> "" in
    (* yod6: search_fast_limited needs ensure_predicates_loaded too,
       so the presence table is populated before we consult it. *)
    ensure_predicates_loaded h tables;
    let rg = ref 0 in
    let n_skipped = ref 0 in
    (try
      while !rg < rg_count && !n_matches < limit do
        let r = !rg in
        let could_p = Cottas_ondisk_lazy.pred_rg_could_contain path r bound_p in
        let could_s = Cottas_ondisk_lazy.subj_rg_could_contain path r bound_s in
        let could_o = Cottas_ondisk_lazy.obj_rg_could_contain  path r bound_o in
        if not (could_p && could_s && could_o) then begin
          incr n_skipped;
          if !n_skipped <= 3 || !n_skipped mod 5 = 0 then
            Printf.eprintf "[tet3-trace] search_fast_limited rg=%d skipped (could_p=%b could_s=%b could_o=%b)\n%!"
              r could_p could_s could_o;
          incr rg
        end else begin
        let s_lst = Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int r) Z.zero in
        let s_arr = arr_of_col s_lst in
        let p_lst = Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int r) Z.one in
        let p_arr = arr_of_col p_lst in
        let o_lst = Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int r) (Z.of_int 2) in
        let o_arr = arr_of_col o_lst in
        let g_lst = Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int r) (Z.of_int 3) in
        let g_arr = arr_of_col g_lst in
        let n = Array.length s_arr in
        if Array.length p_arr <> n || Array.length o_arr <> n || Array.length g_arr <> n then
          Printf.eprintf "[aleph6-FATAL] search_fast_limited: rg=%d column lengths disagree (s=%d p=%d o=%d g=%d)\n%!"
            r n (Array.length p_arr) (Array.length o_arr) (Array.length g_arr)
        else begin
          let i = ref 0 in
          while !i < n && !n_matches < limit do
            let idx = !i in
            let s_tok = cell_of s_arr.(idx) in
            let p_tok = cell_of p_arr.(idx) in
            let o_tok = cell_of o_arr.(idx) in
            let g_tok = cell_of g_arr.(idx) in
            if cell_match_str bound_s s_tok &&
               cell_match_str bound_p p_tok &&
               cell_match_str bound_o o_tok &&
               cell_match_str bound_g g_tok
            then begin
              let s_id = Hashtbl.find_opt tables.ft_subj_tok_to_id  s_tok in
              let p_id = Hashtbl.find_opt tables.ft_pred_tok_to_id  p_tok in
              let o_id = Hashtbl.find_opt tables.ft_obj_tok_to_id   o_tok in
              let g_id =
                if g_tok = "DEFAULT" then None
                else Hashtbl.find_opt tables.ft_graph_tok_to_id g_tok in
              let opt_to_z = function
                | None -> FStar_Pervasives_Native.None
                | Some i -> FStar_Pervasives_Native.Some (Z.of_int i) in
              acc := {
                Parser_BallyhooCOTTAS.cqpr_s = opt_to_z s_id;
                cqpr_p = opt_to_z p_id;
                cqpr_o = opt_to_z o_id;
                cqpr_g = opt_to_z g_id;
              } :: !acc;
              incr n_matches
            end;
            incr i
          done
        end;
        incr rg
        end (* yod6: close the not-skipped branch *)
      done
    with e ->
      let bt = Printexc.get_backtrace () in
      Printf.eprintf "[aleph6-FATAL] search_fast_limited rg=%d EXCEPTION: %s\nbacktrace=%s\n%!"
        !rg (Printexc.to_string e) bt;
      raise e);
    Printf.eprintf "[tet3-trace] search_fast_limited: skipped %d/%d rg(s) (s=%s p=%s o=%s)\n%!"
      !n_skipped rg_count
      (match bound_s with None -> "_" | Some _ -> "<sub>")
      (match bound_p with None -> "_" | Some s -> s)
      (match bound_o with None -> "_" | Some _ -> "<obj>");
    Printf.eprintf "[aleph6-trace] search_fast_limited: matched %d/%d row(s), walked %d/%d rg(s)\n%!"
      !n_matches limit !rg rg_count;
    List.rev !acc

  (* Estimate: same loop as search_fast but counts only — no per-row
     Hashtbl lookup or row allocation. *)
  let estimate_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : pint =
    let path = h.coh_path in
    let tables = tables_for h in
    (* Conditional populate: only the bound columns need their tables. *)
    (match bound.Parser_BallyhooCOTTAS.cbqp_s with
     | FStar_Pervasives_Native.Some _ -> ensure_subjects_loaded h tables
     | _ -> ());
    (match bound.Parser_BallyhooCOTTAS.cbqp_p with
     | FStar_Pervasives_Native.Some _ -> ensure_predicates_loaded h tables
     | _ -> ());
    (match bound.Parser_BallyhooCOTTAS.cbqp_o with
     | FStar_Pervasives_Native.Some _ -> ensure_objects_loaded h tables
     | _ -> ());
    (match bound.Parser_BallyhooCOTTAS.cbqp_g with
     | FStar_Pervasives_Native.Some _ -> ensure_graphs_loaded h tables
     | _ -> ());
    let bound_s = bound_id_to_token tables.ft_id_to_subj_tok  bound.Parser_BallyhooCOTTAS.cbqp_s in
    let bound_p = bound_id_to_token tables.ft_id_to_pred_tok  bound.Parser_BallyhooCOTTAS.cbqp_p in
    let bound_o = bound_id_to_token tables.ft_id_to_obj_tok   bound.Parser_BallyhooCOTTAS.cbqp_o in
    let bound_g = bound_id_to_token tables.ft_id_to_graph_tok bound.Parser_BallyhooCOTTAS.cbqp_g in
    let rg_count = match Parquet_Footer.probe_parquet_row_group_count path with
      | FStar_Pervasives_Native.None -> 0
      | FStar_Pervasives_Native.Some n -> Z.to_int n in
    Printf.eprintf "[qof3-trace] estimate_fast: rg_count=%d\n%!" rg_count;
    Printf.eprintf "[pe4-trace] estimate_fast pre-walk rss=%dMB heap=%dMB fd=%d\n%!"
      (pe4_rss_mb ()) (pe4_gc_mb ()) (pe4_fd_count ());
    let count = ref 0 in
    let arr_of_col col_opt =
      match col_opt with
      | FStar_Pervasives_Native.None -> [||]
      | FStar_Pervasives_Native.Some lst -> Array.of_list lst in
    let cell_of = function
      | FStar_Pervasives_Native.Some s -> s
      | FStar_Pervasives_Native.None -> "" in
    let walk_rg rg =
      Printf.eprintf "[pe4-trace] estimate_fast rg=%d enter rss=%dMB heap=%dMB count=%d\n%!"
        rg (pe4_rss_mb ()) (pe4_gc_mb ()) !count;
      let s_arr = arr_of_col (Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int rg) Z.zero) in
      Printf.eprintf "[pe4-trace] estimate_fast rg=%d decoded col=0 n=%d rss=%dMB heap=%dMB\n%!"
        rg (Array.length s_arr) (pe4_rss_mb ()) (pe4_gc_mb ());
      let p_arr = arr_of_col (Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int rg) Z.one) in
      Printf.eprintf "[pe4-trace] estimate_fast rg=%d decoded col=1 rss=%dMB heap=%dMB\n%!"
        rg (pe4_rss_mb ()) (pe4_gc_mb ());
      let o_arr = arr_of_col (Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int rg) (Z.of_int 2)) in
      Printf.eprintf "[pe4-trace] estimate_fast rg=%d decoded col=2 rss=%dMB heap=%dMB\n%!"
        rg (pe4_rss_mb ()) (pe4_gc_mb ());
      let g_arr = arr_of_col (Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int rg) (Z.of_int 3)) in
      Printf.eprintf "[pe4-trace] estimate_fast rg=%d decoded col=3 rss=%dMB heap=%dMB\n%!"
        rg (pe4_rss_mb ()) (pe4_gc_mb ());
      let n = Array.length s_arr in
      if Array.length p_arr <> n || Array.length o_arr <> n || Array.length g_arr <> n then
        Printf.eprintf "[qof3-FATAL] estimate_fast: row-group %d column lengths disagree\n%!" rg
      else begin
        for i = 0 to n - 1 do
          let s_tok = cell_of s_arr.(i) in
          let p_tok = cell_of p_arr.(i) in
          let o_tok = cell_of o_arr.(i) in
          let g_tok = cell_of g_arr.(i) in
          if cell_match_str bound_s s_tok &&
             cell_match_str bound_p p_tok &&
             cell_match_str bound_o o_tok &&
             cell_match_str bound_g g_tok
          then incr count
        done;
        Printf.eprintf "[pe4-trace] estimate_fast rg=%d done count_so_far=%d rss=%dMB heap=%dMB\n%!"
          rg !count (pe4_rss_mb ()) (pe4_gc_mb ())
      end
    in
    let n_skipped = ref 0 in
    for rg = 0 to rg_count - 1 do
      let could_p = Cottas_ondisk_lazy.pred_rg_could_contain path rg bound_p in
      let could_s = Cottas_ondisk_lazy.subj_rg_could_contain path rg bound_s in
      let could_o = Cottas_ondisk_lazy.obj_rg_could_contain  path rg bound_o in
      if not (could_p && could_s && could_o) then begin
        incr n_skipped;
        if !n_skipped <= 3 || !n_skipped mod 5 = 0 then
          Printf.eprintf "[tet3-trace] estimate_fast rg=%d skipped (could_p=%b could_s=%b could_o=%b)\n%!"
            rg could_p could_s could_o
      end else begin
        try walk_rg rg
        with e ->
          let bt = Printexc.get_backtrace () in
          Printf.eprintf "[pe4-FATAL] estimate_fast rg=%d EXCEPTION: %s\nbacktrace=%s\n%!"
            rg (Printexc.to_string e) bt;
          raise e
      end
    done;
    Printf.eprintf "[tet3-trace] estimate_fast: skipped %d/%d rg(s) (s=%s p=%s o=%s)\n%!"
      !n_skipped rg_count
      (match bound_s with None -> "_" | Some _ -> "<sub>")
      (match bound_p with None -> "_" | Some s -> s)
      (match bound_o with None -> "_" | Some _ -> "<obj>");
    Printf.eprintf "[qof3-trace] estimate_fast: matched %d row(s)\n%!" !count;
    Printf.eprintf "[pe4-trace] estimate_fast post-walk rss=%dMB heap=%dMB count=%d\n%!"
      (pe4_rss_mb ()) (pe4_gc_mb ()) !count;
    !count

  let decode_subject_fast (h : cottas_ondisk_handle) (id : Prims.nat)
    : RDF_Graph_Executable.subject =
    let tables = tables_for h in
    ensure_subjects_loaded h tables;
    let id_int = Z.to_int id in
    match Hashtbl.find_opt tables.ft_id_to_subject id_int with
    | Some s -> s
    | None ->
      (* vav3: lazy decode-fast cache miss — bulk_load_column_into_tables
         skipped eager parse to save boot time; parse on demand here. *)
      (match Hashtbl.find_opt tables.ft_id_to_subj_tok id_int with
       | None -> RDF_Graph_Executable.S_BNode "cottas_decode_oor"
       | Some raw ->
         (match parse_subject_str raw with
          | Some s ->
            Hashtbl.replace tables.ft_id_to_subject id_int s;
            s
          | None -> RDF_Graph_Executable.S_BNode "cottas_decode_oor"))

  let decode_predicate_fast (h : cottas_ondisk_handle) (id : Prims.nat)
    : RDF_Graph_Executable.wf_iri =
    let tables = tables_for h in
    ensure_predicates_loaded h tables;
    match Hashtbl.find_opt tables.ft_id_to_predicate (Z.to_int id) with
    | Some p -> p
    | None -> ("http://www.w3.org/1999/02/22-rdf-syntax-ns#type" : RDF_Graph_Executable.wf_iri)

  let decode_object_fast (h : cottas_ondisk_handle) (id : Prims.nat)
    : RDF_Graph_Executable.rdf_term =
    let tables = tables_for h in
    ensure_objects_loaded h tables;
    let id_int = Z.to_int id in
    match Hashtbl.find_opt tables.ft_id_to_object id_int with
    | Some o -> o
    | None ->
      (* vav3: lazy decode-fast cache miss for objects. *)
      (match Hashtbl.find_opt tables.ft_id_to_obj_tok id_int with
       | None -> RDF_Graph_Executable.T_BNode "cottas_decode_oor"
       | Some raw ->
         (match parse_object_str raw with
          | Some o ->
            Hashtbl.replace tables.ft_id_to_object id_int o;
            o
          | None -> RDF_Graph_Executable.T_BNode "cottas_decode_oor"))

  let decode_graph_fast (h : cottas_ondisk_handle) (id : Prims.nat)
    : RDF_Graph_Executable.iri =
    let tables = tables_for h in
    ensure_graphs_loaded h tables;
    match Hashtbl.find_opt tables.ft_id_to_graph (Z.to_int id) with
    | Some g -> g
    | None -> ""

  let encode_subject_fast (h : cottas_ondisk_handle) (s : RDF_Graph_Executable.subject)
    : Prims.nat FStar_Pervasives_Native.option =
    let tables = tables_for h in
    ensure_subjects_loaded h tables;
    let key = match s with
      | RDF_Graph_Executable.S_IRI i   -> "<" ^ i ^ ">"
      | RDF_Graph_Executable.S_BNode b -> "_:" ^ b in
    match Hashtbl.find_opt tables.ft_subj_tok_to_id key with
    | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
    | None -> FStar_Pervasives_Native.None

  let encode_predicate_fast (h : cottas_ondisk_handle) (p : RDF_Graph_Executable.wf_iri)
    : Prims.nat FStar_Pervasives_Native.option =
    let tables = tables_for h in
    ensure_predicates_loaded h tables;
    let key = "<" ^ p ^ ">" in
    match Hashtbl.find_opt tables.ft_pred_tok_to_id key with
    | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
    | None -> FStar_Pervasives_Native.None

  let encode_object_fast (h : cottas_ondisk_handle) (o : RDF_Graph_Executable.rdf_term)
    : Prims.nat FStar_Pervasives_Native.option =
    let tables = tables_for h in
    ensure_objects_loaded h tables;
    (* For literals we don't have an inverse-encoder in F* (escape rules
       differ between bound-input and parquet-stored form). Fall back to
       the F*-extracted slow path for non-IRI/non-bnode objects. *)
    match o with
    | RDF_Graph_Executable.T_IRI i ->
      let key = "<" ^ i ^ ">" in
      (match Hashtbl.find_opt tables.ft_obj_tok_to_id key with
       | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
       | None -> FStar_Pervasives_Native.None)
    | RDF_Graph_Executable.T_BNode b ->
      let key = "_:" ^ b in
      (match Hashtbl.find_opt tables.ft_obj_tok_to_id key with
       | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
       | None -> FStar_Pervasives_Native.None)
    | RDF_Graph_Executable.T_Literal _ ->
      (* Slow path via F*'s canonical-key revmap. Bound objects with
         literals are uncommon; correctness > speed here. *)
      revmap_lookup h.coh_obj_revmap (object_to_revmap_key o)

  let encode_graph_fast (h : cottas_ondisk_handle) (g : RDF_Graph_Executable.iri)
    : Prims.nat FStar_Pervasives_Native.option =
    let tables = tables_for h in
    ensure_graphs_loaded h tables;
    let key = "<" ^ g ^ ">" in
    match Hashtbl.find_opt tables.ft_graph_tok_to_id key with
    | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
    | None -> FStar_Pervasives_Native.None

  let predicate_present_fast (h : cottas_ondisk_handle) (p : RDF_Graph_Executable.wf_iri) : bool =
    let tables = tables_for h in
    ensure_predicates_loaded h tables;
    let key = "<" ^ p ^ ">" in
    Hashtbl.mem tables.ft_pred_tok_to_id key
end

let cottas_ondisk_summary (ds : cottas_ondisk_store) :
  Parser_BallyhooCOTTAS.cottas_artifact_summary
    FStar_Pervasives_Native.option=
  (ds.cods_handle).coh_summary
let cottas_ondisk_encode_subject (ds : cottas_ondisk_store)
  (s : RDF_Graph_Executable.subject) :
  Parser_BallyhooCOTTAS.cottas_term_ref FStar_Pervasives_Native.option=
  Cottas_ondisk_runtime.encode_subject_fast ds.cods_handle s
let cottas_ondisk_encode_predicate (ds : cottas_ondisk_store)
  (p : RDF_Graph_Executable.wf_iri) :
  Parser_BallyhooCOTTAS.cottas_term_ref FStar_Pervasives_Native.option=
  Cottas_ondisk_runtime.encode_predicate_fast ds.cods_handle p
let cottas_ondisk_encode_object (ds : cottas_ondisk_store)
  (o : RDF_Graph_Executable.rdf_term) :
  Parser_BallyhooCOTTAS.cottas_term_ref FStar_Pervasives_Native.option=
  Cottas_ondisk_runtime.encode_object_fast ds.cods_handle o
let cottas_ondisk_encode_graph_name (ds : cottas_ondisk_store)
  (g : RDF_Graph_Executable.iri) :
  Parser_BallyhooCOTTAS.cottas_graph_ref FStar_Pervasives_Native.option=
  Cottas_ondisk_runtime.encode_graph_fast ds.cods_handle g
let cottas_ondisk_decode_subject (ds : cottas_ondisk_store)
  (id : Parser_BallyhooCOTTAS.cottas_term_ref) :
  RDF_Graph_Executable.subject=
  Cottas_ondisk_runtime.decode_subject_fast ds.cods_handle id
let cottas_ondisk_decode_predicate (ds : cottas_ondisk_store)
  (id : Parser_BallyhooCOTTAS.cottas_term_ref) : RDF_Graph_Executable.wf_iri=
  match list_nth (ds.cods_handle).coh_predicates id with
  | FStar_Pervasives_Native.Some p -> p
  | FStar_Pervasives_Native.None ->
      let fallback = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" in
      fallback
let cottas_ondisk_decode_object (ds : cottas_ondisk_store)
  (id : Parser_BallyhooCOTTAS.cottas_term_ref) :
  RDF_Graph_Executable.rdf_term=
  Cottas_ondisk_runtime.decode_object_fast ds.cods_handle id
let cottas_ondisk_decode_graph_name (ds : cottas_ondisk_store)
  (id : Parser_BallyhooCOTTAS.cottas_graph_ref) : RDF_Graph_Executable.iri=
  Cottas_ondisk_runtime.decode_graph_fast ds.cods_handle id
let cottas_ondisk_predicate_present (ds : cottas_ondisk_store)
  (pred : RDF_Graph_Executable.wf_iri) : Prims.bool=
  Cottas_ondisk_runtime.predicate_present_fast ds.cods_handle pred
let rec named_graphs_aux (graphs : RDF_Graph_Executable.iri Prims.list)
  (idx : Prims.nat) :
  (RDF_Graph_Executable.iri * Parser_BallyhooCOTTAS.cottas_graph_ref)
    Prims.list=
  match graphs with
  | [] -> []
  | g::rest -> (g, idx) :: (named_graphs_aux rest (idx + Prims.int_one))
let cottas_ondisk_named_graphs (ds : cottas_ondisk_store) :
  (RDF_Graph_Executable.iri * Parser_BallyhooCOTTAS.cottas_graph_ref)
    Prims.list=
  named_graphs_aux (ds.cods_handle).coh_graphs Prims.int_zero
let cottas_ondisk_open (artifact_path : Prims.string) :
  cottas_ondisk_store FStar_Pervasives_Native.option=
  Printf.eprintf "[qof3-trace] cottas_ondisk_open path=%s\n%!" artifact_path;
  let h = Cottas_ondisk_runtime.load_handle artifact_path in
  Printf.eprintf "[qof3-trace] cottas_ondisk_open: handle ready\n%!";
  FStar_Pervasives_Native.Some {
    cods_artifact_path = artifact_path;
    cods_summary = h.coh_summary;
    cods_handle = h;
  }
let id_to_raw_token (raws : Prims.string Prims.list)
  (id : Parser_BallyhooCOTTAS.cottas_term_ref FStar_Pervasives_Native.option)
  : Prims.string FStar_Pervasives_Native.option=
  match id with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some i ->
      (match list_nth raws i with
       | FStar_Pervasives_Native.Some s -> FStar_Pervasives_Native.Some s
       | FStar_Pervasives_Native.None ->
           FStar_Pervasives_Native.Some "\000cottas_decode_oor")
let cell_match (expected : Prims.string FStar_Pervasives_Native.option)
  (actual : Prims.string) : Prims.bool=
  match expected with
  | FStar_Pervasives_Native.None -> true
  | FStar_Pervasives_Native.Some s -> s = actual
let graph_cell_match (expected : Prims.string FStar_Pervasives_Native.option)
  (actual : Prims.string) : Prims.bool= cell_match expected actual
let build_qp_row (h : cottas_ondisk_handle) (s_tok : Prims.string)
  (p_tok : Prims.string) (o_tok : Prims.string) (g_tok : Prims.string) :
  Parser_BallyhooCOTTAS.cottas_qp_row=
  let s_id = revmap_lookup h.coh_subj_raw_revmap s_tok in
  let p_id = revmap_lookup h.coh_pred_raw_revmap p_tok in
  let o_id = revmap_lookup h.coh_obj_raw_revmap o_tok in
  let g_id =
    if g_tok = "DEFAULT"
    then FStar_Pervasives_Native.None
    else revmap_lookup h.coh_graph_raw_revmap g_tok in
  {
    Parser_BallyhooCOTTAS.cqpr_s = s_id;
    Parser_BallyhooCOTTAS.cqpr_p = p_id;
    Parser_BallyhooCOTTAS.cqpr_o = o_id;
    Parser_BallyhooCOTTAS.cqpr_g = g_id
  }
let rec filter_zipped_rows (h : cottas_ondisk_handle)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (s_col : Prims.string FStar_Pervasives_Native.option Prims.list)
  (p_col : Prims.string FStar_Pervasives_Native.option Prims.list)
  (o_col : Prims.string FStar_Pervasives_Native.option Prims.list)
  (g_col : Prims.string FStar_Pervasives_Native.option Prims.list)
  (acc_rev : Parser_BallyhooCOTTAS.cottas_qp_row Prims.list) :
  Parser_BallyhooCOTTAS.cottas_qp_row Prims.list=
  match (s_col, p_col, o_col, g_col) with
  | (s_hd::s_tl, p_hd::p_tl, o_hd::o_tl, g_hd::g_tl) ->
      let acc_rev' =
        match (s_hd, p_hd, o_hd, g_hd) with
        | (FStar_Pervasives_Native.Some s_tok, FStar_Pervasives_Native.Some
           p_tok, FStar_Pervasives_Native.Some o_tok,
           FStar_Pervasives_Native.Some g_tok) ->
            if
              (((cell_match bound_s s_tok) && (cell_match bound_p p_tok)) &&
                 (cell_match bound_o o_tok))
                && (graph_cell_match bound_g g_tok)
            then (build_qp_row h s_tok p_tok o_tok g_tok) :: acc_rev
            else acc_rev
        | uu___ -> acc_rev in
      filter_zipped_rows h bound_s bound_p bound_o bound_g s_tl p_tl o_tl
        g_tl acc_rev'
  | uu___ -> acc_rev
let rec count_zipped_rows
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (s_col : Prims.string FStar_Pervasives_Native.option Prims.list)
  (p_col : Prims.string FStar_Pervasives_Native.option Prims.list)
  (o_col : Prims.string FStar_Pervasives_Native.option Prims.list)
  (g_col : Prims.string FStar_Pervasives_Native.option Prims.list)
  (acc : Prims.nat) : Prims.nat=
  match (s_col, p_col, o_col, g_col) with
  | (s_hd::s_tl, p_hd::p_tl, o_hd::o_tl, g_hd::g_tl) ->
      let acc' =
        match (s_hd, p_hd, o_hd, g_hd) with
        | (FStar_Pervasives_Native.Some s_tok, FStar_Pervasives_Native.Some
           p_tok, FStar_Pervasives_Native.Some o_tok,
           FStar_Pervasives_Native.Some g_tok) ->
            if
              (((cell_match bound_s s_tok) && (cell_match bound_p p_tok)) &&
                 (cell_match bound_o o_tok))
                && (graph_cell_match bound_g g_tok)
            then acc + Prims.int_one
            else acc
        | uu___ -> acc in
      count_zipped_rows bound_s bound_p bound_o bound_g s_tl p_tl o_tl g_tl
        acc'
  | uu___ -> acc
let pcache_default_capacity : Prims.nat= (Prims.of_int (128))
let rec walk_row_groups_search (h : cottas_ondisk_handle)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (rg_index : Prims.nat) (rg_count : Prims.nat) (fuel : Prims.nat)
  (acc_rev : Parser_BallyhooCOTTAS.cottas_qp_row Prims.list)
  (cache : RDF_CottasStore_PageCache.page_cache) :
  (Parser_BallyhooCOTTAS.cottas_qp_row Prims.list *
    RDF_CottasStore_PageCache.page_cache)=
  if fuel = Prims.int_zero
  then (acc_rev, cache)
  else
    if rg_index >= rg_count
    then (acc_rev, cache)
    else
      (let cap = cache.RDF_CottasStore_PageCache.pc_capacity in
       let uu___2 =
         RDF_CottasStore_PageCache.pcache_decode_in_row_group cache
           h.coh_path rg_index Prims.int_zero cap in
       match uu___2 with
       | (s_col, c1) ->
           let uu___3 =
             RDF_CottasStore_PageCache.pcache_decode_in_row_group c1
               h.coh_path rg_index Prims.int_one cap in
           (match uu___3 with
            | (p_col, c2) ->
                let uu___4 =
                  RDF_CottasStore_PageCache.pcache_decode_in_row_group c2
                    h.coh_path rg_index (Prims.of_int (2)) cap in
                (match uu___4 with
                 | (o_col, c3) ->
                     let uu___5 =
                       RDF_CottasStore_PageCache.pcache_decode_in_row_group
                         c3 h.coh_path rg_index (Prims.of_int (3)) cap in
                     (match uu___5 with
                      | (g_col, c4) ->
                          let acc_rev' =
                            match (s_col, p_col, o_col, g_col) with
                            | (FStar_Pervasives_Native.Some sc,
                               FStar_Pervasives_Native.Some pc,
                               FStar_Pervasives_Native.Some oc,
                               FStar_Pervasives_Native.Some gc) ->
                                filter_zipped_rows h bound_s bound_p bound_o
                                  bound_g sc pc oc gc acc_rev
                            | uu___6 -> acc_rev in
                          walk_row_groups_search h bound_s bound_p bound_o
                            bound_g (rg_index + Prims.int_one) rg_count
                            (fuel - Prims.int_one) acc_rev' c4))))
let rec walk_row_groups_estimate (h : cottas_ondisk_handle)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (rg_index : Prims.nat) (rg_count : Prims.nat) (fuel : Prims.nat)
  (acc : Prims.nat) (cache : RDF_CottasStore_PageCache.page_cache) :
  (Prims.nat * RDF_CottasStore_PageCache.page_cache)=
  if fuel = Prims.int_zero
  then (acc, cache)
  else
    if rg_index >= rg_count
    then (acc, cache)
    else
      (let cap = cache.RDF_CottasStore_PageCache.pc_capacity in
       let uu___2 =
         RDF_CottasStore_PageCache.pcache_decode_in_row_group cache
           h.coh_path rg_index Prims.int_zero cap in
       match uu___2 with
       | (s_col, c1) ->
           let uu___3 =
             RDF_CottasStore_PageCache.pcache_decode_in_row_group c1
               h.coh_path rg_index Prims.int_one cap in
           (match uu___3 with
            | (p_col, c2) ->
                let uu___4 =
                  RDF_CottasStore_PageCache.pcache_decode_in_row_group c2
                    h.coh_path rg_index (Prims.of_int (2)) cap in
                (match uu___4 with
                 | (o_col, c3) ->
                     let uu___5 =
                       RDF_CottasStore_PageCache.pcache_decode_in_row_group
                         c3 h.coh_path rg_index (Prims.of_int (3)) cap in
                     (match uu___5 with
                      | (g_col, c4) ->
                          let acc' =
                            match (s_col, p_col, o_col, g_col) with
                            | (FStar_Pervasives_Native.Some sc,
                               FStar_Pervasives_Native.Some pc,
                               FStar_Pervasives_Native.Some oc,
                               FStar_Pervasives_Native.Some gc) ->
                                count_zipped_rows bound_s bound_p bound_o
                                  bound_g sc pc oc gc acc
                            | uu___6 -> acc in
                          walk_row_groups_estimate h bound_s bound_p bound_o
                            bound_g (rg_index + Prims.int_one) rg_count
                            (fuel - Prims.int_one) acc' c4))))
type dict_cache =
  ((Prims.nat * Prims.nat) * Prims.string Prims.list) Prims.list
let rec dict_cache_lookup (c : dict_cache) (rg : Prims.nat) (col : Prims.nat)
  : Prims.string Prims.list FStar_Pervasives_Native.option=
  match c with
  | [] -> FStar_Pervasives_Native.None
  | ((r, k), v)::rest ->
      if (r = rg) && (k = col)
      then FStar_Pervasives_Native.Some v
      else dict_cache_lookup rest rg col
let rec list_string_mem (xs : Prims.string Prims.list) (s : Prims.string) :
  Prims.bool=
  match xs with
  | [] -> false
  | hd::rest -> if hd = s then true else list_string_mem rest s
let rec populate_dict_cache_loop (c : dict_cache) (path : Prims.string)
  (col_index : Prims.nat) (rg_index : Prims.nat) (rg_count : Prims.nat)
  (fuel : Prims.nat) : dict_cache=
  if fuel = Prims.int_zero
  then c
  else
    if rg_index >= rg_count
    then c
    else
      (let c' =
         match dict_cache_lookup c rg_index col_index with
         | FStar_Pervasives_Native.Some uu___2 -> c
         | FStar_Pervasives_Native.None ->
             (match Parquet_Footer.probe_parquet_column_dictionary_in_row_group
                      path rg_index col_index
              with
              | FStar_Pervasives_Native.None -> c
              | FStar_Pervasives_Native.Some dict ->
                  ((rg_index, col_index), dict) :: c) in
       populate_dict_cache_loop c' path col_index (rg_index + Prims.int_one)
         rg_count (fuel - Prims.int_one))
let populate_dict_cache_for_column (c : dict_cache) (path : Prims.string)
  (col_index : Prims.nat) (rg_count : Prims.nat) : dict_cache=
  populate_dict_cache_loop c path col_index Prims.int_zero rg_count rg_count
let rec compute_candidate_rgs_loop (c : dict_cache) (col_index : Prims.nat)
  (bound_token : Prims.string) (rg_index : Prims.nat) (rg_count : Prims.nat)
  (fuel : Prims.nat) (acc_rev : Prims.nat Prims.list) : Prims.nat Prims.list=
  if fuel = Prims.int_zero
  then acc_rev
  else
    if rg_index >= rg_count
    then acc_rev
    else
      (let acc_rev' =
         match dict_cache_lookup c rg_index col_index with
         | FStar_Pervasives_Native.None -> rg_index :: acc_rev
         | FStar_Pervasives_Native.Some dict ->
             if list_string_mem dict bound_token
             then rg_index :: acc_rev
             else acc_rev in
       compute_candidate_rgs_loop c col_index bound_token
         (rg_index + Prims.int_one) rg_count (fuel - Prims.int_one) acc_rev')
let compute_candidate_rgs (c : dict_cache) (col_index : Prims.nat)
  (bound_token : Prims.string) (rg_count : Prims.nat) : Prims.nat Prims.list=
  let rev_list =
    compute_candidate_rgs_loop c col_index bound_token Prims.int_zero
      rg_count rg_count [] in
  Parquet_Footer.list_rev rev_list
let rec list_nat_intersect_sorted (xs : Prims.nat Prims.list)
  (ys : Prims.nat Prims.list) (acc_rev : Prims.nat Prims.list)
  (fuel : Prims.nat) : Prims.nat Prims.list=
  if fuel = Prims.int_zero
  then acc_rev
  else
    (match (xs, ys) with
     | ([], uu___1) -> acc_rev
     | (uu___1, []) -> acc_rev
     | (x::xrest, y::yrest) ->
         if x = y
         then
           list_nat_intersect_sorted xrest yrest (x :: acc_rev)
             (fuel - Prims.int_one)
         else
           if x < y
           then
             list_nat_intersect_sorted xrest ys acc_rev
               (fuel - Prims.int_one)
           else
             list_nat_intersect_sorted xs yrest acc_rev
               (fuel - Prims.int_one))
let intersect_sorted_rg_lists (xs : Prims.nat Prims.list)
  (ys : Prims.nat Prims.list) : Prims.nat Prims.list=
  let len_xs = FStar_List_Tot_Base.length xs in
  let len_ys = FStar_List_Tot_Base.length ys in
  let fuel = (len_xs + len_ys) + Prims.int_one in
  let rev = list_nat_intersect_sorted xs ys [] fuel in
  Parquet_Footer.list_rev rev
let rec walk_candidate_rgs_search (h : cottas_ondisk_handle)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (candidates : Prims.nat Prims.list)
  (acc_rev : Parser_BallyhooCOTTAS.cottas_qp_row Prims.list)
  (cache : RDF_CottasStore_PageCache.page_cache) :
  (Parser_BallyhooCOTTAS.cottas_qp_row Prims.list *
    RDF_CottasStore_PageCache.page_cache)=
  match candidates with
  | [] -> (acc_rev, cache)
  | rg_index::rest ->
      let cap = cache.RDF_CottasStore_PageCache.pc_capacity in
      let uu___ =
        RDF_CottasStore_PageCache.pcache_decode_in_row_group cache h.coh_path
          rg_index Prims.int_zero cap in
      (match uu___ with
       | (s_col, c1) ->
           let uu___1 =
             RDF_CottasStore_PageCache.pcache_decode_in_row_group c1
               h.coh_path rg_index Prims.int_one cap in
           (match uu___1 with
            | (p_col, c2) ->
                let uu___2 =
                  RDF_CottasStore_PageCache.pcache_decode_in_row_group c2
                    h.coh_path rg_index (Prims.of_int (2)) cap in
                (match uu___2 with
                 | (o_col, c3) ->
                     let uu___3 =
                       RDF_CottasStore_PageCache.pcache_decode_in_row_group
                         c3 h.coh_path rg_index (Prims.of_int (3)) cap in
                     (match uu___3 with
                      | (g_col, c4) ->
                          let acc_rev' =
                            match (s_col, p_col, o_col, g_col) with
                            | (FStar_Pervasives_Native.Some sc,
                               FStar_Pervasives_Native.Some pc,
                               FStar_Pervasives_Native.Some oc,
                               FStar_Pervasives_Native.Some gc) ->
                                filter_zipped_rows h bound_s bound_p bound_o
                                  bound_g sc pc oc gc acc_rev
                            | uu___4 -> acc_rev in
                          walk_candidate_rgs_search h bound_s bound_p bound_o
                            bound_g rest acc_rev' c4))))
let rec walk_candidate_rgs_estimate (h : cottas_ondisk_handle)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (candidates : Prims.nat Prims.list) (acc : Prims.nat)
  (cache : RDF_CottasStore_PageCache.page_cache) :
  (Prims.nat * RDF_CottasStore_PageCache.page_cache)=
  match candidates with
  | [] -> (acc, cache)
  | rg_index::rest ->
      let cap = cache.RDF_CottasStore_PageCache.pc_capacity in
      let uu___ =
        RDF_CottasStore_PageCache.pcache_decode_in_row_group cache h.coh_path
          rg_index Prims.int_zero cap in
      (match uu___ with
       | (s_col, c1) ->
           let uu___1 =
             RDF_CottasStore_PageCache.pcache_decode_in_row_group c1
               h.coh_path rg_index Prims.int_one cap in
           (match uu___1 with
            | (p_col, c2) ->
                let uu___2 =
                  RDF_CottasStore_PageCache.pcache_decode_in_row_group c2
                    h.coh_path rg_index (Prims.of_int (2)) cap in
                (match uu___2 with
                 | (o_col, c3) ->
                     let uu___3 =
                       RDF_CottasStore_PageCache.pcache_decode_in_row_group
                         c3 h.coh_path rg_index (Prims.of_int (3)) cap in
                     (match uu___3 with
                      | (g_col, c4) ->
                          let acc' =
                            match (s_col, p_col, o_col, g_col) with
                            | (FStar_Pervasives_Native.Some sc,
                               FStar_Pervasives_Native.Some pc,
                               FStar_Pervasives_Native.Some oc,
                               FStar_Pervasives_Native.Some gc) ->
                                count_zipped_rows bound_s bound_p bound_o
                                  bound_g sc pc oc gc acc
                            | uu___4 -> acc in
                          walk_candidate_rgs_estimate h bound_s bound_p
                            bound_o bound_g rest acc' c4))))
let candidates_for_one_bound (c : dict_cache) (path : Prims.string)
  (col_index : Prims.nat) (bound_token : Prims.string) (rg_count : Prims.nat)
  : (Prims.nat Prims.list * dict_cache)=
  let c' = populate_dict_cache_for_column c path col_index rg_count in
  let cands = compute_candidate_rgs c' col_index bound_token rg_count in
  (cands, c')
let rec all_rgs_loop (rg_index : Prims.nat) (rg_count : Prims.nat)
  (fuel : Prims.nat) (acc_rev : Prims.nat Prims.list) : Prims.nat Prims.list=
  if fuel = Prims.int_zero
  then acc_rev
  else
    if rg_index >= rg_count
    then acc_rev
    else
      all_rgs_loop (rg_index + Prims.int_one) rg_count (fuel - Prims.int_one)
        (rg_index :: acc_rev)
let all_rgs (rg_count : Prims.nat) : Prims.nat Prims.list=
  Parquet_Footer.list_rev (all_rgs_loop Prims.int_zero rg_count rg_count [])
let plan_candidate_rgs (h : cottas_ondisk_handle)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (rg_count : Prims.nat) : (Prims.nat Prims.list * dict_cache)=
  let path = h.coh_path in
  let init = ((all_rgs rg_count), [], false) in
  let step acc col_index bound =
    match bound with
    | FStar_Pervasives_Native.None -> acc
    | FStar_Pervasives_Native.Some tok ->
        let uu___ = acc in
        (match uu___ with
         | (cur, c, _started) ->
             let uu___1 =
               candidates_for_one_bound c path col_index tok rg_count in
             (match uu___1 with
              | (cands, c') ->
                  let combined = intersect_sorted_rg_lists cur cands in
                  (combined, c', true))) in
  let st1 = step init Prims.int_zero bound_s in
  let st2 = step st1 Prims.int_one bound_p in
  let st3 = step st2 (Prims.of_int (2)) bound_o in
  let st4 = step st3 (Prims.of_int (3)) bound_g in
  let uu___ = st4 in match uu___ with | (final, c, uu___1) -> (final, c)
let cottas_ondisk_search (ds : cottas_ondisk_store)
  (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) :
  Parser_BallyhooCOTTAS.cottas_qp_row Prims.list=
  Cottas_ondisk_runtime.search_fast ds.cods_handle bound
let _spec_cottas_ondisk_search_unused (ds : cottas_ondisk_store)
  (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) :
  Parser_BallyhooCOTTAS.cottas_qp_row Prims.list=
  let h = ds.cods_handle in
  let bound_s =
    id_to_raw_token h.coh_subjects_raw bound.Parser_BallyhooCOTTAS.cbqp_s in
  let bound_p =
    id_to_raw_token h.coh_predicates_raw bound.Parser_BallyhooCOTTAS.cbqp_p in
  let bound_o =
    id_to_raw_token h.coh_objects_raw bound.Parser_BallyhooCOTTAS.cbqp_o in
  let bound_g =
    id_to_raw_token h.coh_graphs_raw bound.Parser_BallyhooCOTTAS.cbqp_g in
  match Parquet_Footer.probe_parquet_row_group_count h.coh_path with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some rg_count ->
      let cache0 =
        RDF_CottasStore_PageCache.pcache_empty pcache_default_capacity in
      let any_bound_present =
        (((FStar_Pervasives_Native.uu___is_Some bound_s) ||
            (FStar_Pervasives_Native.uu___is_Some bound_p))
           || (FStar_Pervasives_Native.uu___is_Some bound_o))
          || (FStar_Pervasives_Native.uu___is_Some bound_g) in
      if any_bound_present
      then
        let uu___ =
          plan_candidate_rgs h bound_s bound_p bound_o bound_g rg_count in
        (match uu___ with
         | (candidates, _dc) ->
             let uu___1 =
               walk_candidate_rgs_search h bound_s bound_p bound_o bound_g
                 candidates [] cache0 in
             (match uu___1 with
              | (acc_rev, _cache') -> Parquet_Footer.list_rev acc_rev))
      else
        (let uu___1 =
           walk_row_groups_search h bound_s bound_p bound_o bound_g
             Prims.int_zero rg_count rg_count [] cache0 in
         match uu___1 with
         | (acc_rev, _cache') -> Parquet_Footer.list_rev acc_rev)
let rec filter_zipped_rows_limited (h : cottas_ondisk_handle)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (s_col : Prims.string FStar_Pervasives_Native.option Prims.list)
  (p_col : Prims.string FStar_Pervasives_Native.option Prims.list)
  (o_col : Prims.string FStar_Pervasives_Native.option Prims.list)
  (g_col : Prims.string FStar_Pervasives_Native.option Prims.list)
  (acc_rev : Parser_BallyhooCOTTAS.cottas_qp_row Prims.list)
  (acc_count : Prims.nat) (limit : Prims.nat) :
  (Parser_BallyhooCOTTAS.cottas_qp_row Prims.list * Prims.nat * Prims.bool)=
  if acc_count >= limit
  then (acc_rev, acc_count, true)
  else
    (match (s_col, p_col, o_col, g_col) with
     | (s_hd::s_tl, p_hd::p_tl, o_hd::o_tl, g_hd::g_tl) ->
         let uu___1 =
           match (s_hd, p_hd, o_hd, g_hd) with
           | (FStar_Pervasives_Native.Some s_tok,
              FStar_Pervasives_Native.Some p_tok,
              FStar_Pervasives_Native.Some o_tok,
              FStar_Pervasives_Native.Some g_tok) ->
               if
                 (((cell_match bound_s s_tok) && (cell_match bound_p p_tok))
                    && (cell_match bound_o o_tok))
                   && (graph_cell_match bound_g g_tok)
               then
                 (((build_qp_row h s_tok p_tok o_tok g_tok) :: acc_rev),
                   (acc_count + Prims.int_one))
               else (acc_rev, acc_count)
           | uu___2 -> (acc_rev, acc_count) in
         (match uu___1 with
          | (acc_rev', acc_count') ->
              filter_zipped_rows_limited h bound_s bound_p bound_o bound_g
                s_tl p_tl o_tl g_tl acc_rev' acc_count' limit)
     | uu___1 -> (acc_rev, acc_count, (acc_count >= limit)))
let rec walk_row_groups_search_limited (h : cottas_ondisk_handle)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (rg_index : Prims.nat) (rg_count : Prims.nat) (fuel : Prims.nat)
  (acc_rev : Parser_BallyhooCOTTAS.cottas_qp_row Prims.list)
  (acc_count : Prims.nat) (limit : Prims.nat)
  (cache : RDF_CottasStore_PageCache.page_cache) :
  (Parser_BallyhooCOTTAS.cottas_qp_row Prims.list *
    RDF_CottasStore_PageCache.page_cache)=
  if fuel = Prims.int_zero
  then (acc_rev, cache)
  else
    if rg_index >= rg_count
    then (acc_rev, cache)
    else
      if acc_count >= limit
      then (acc_rev, cache)
      else
        (let cap = cache.RDF_CottasStore_PageCache.pc_capacity in
         let uu___3 =
           RDF_CottasStore_PageCache.pcache_decode_in_row_group cache
             h.coh_path rg_index Prims.int_zero cap in
         match uu___3 with
         | (s_col, c1) ->
             let uu___4 =
               RDF_CottasStore_PageCache.pcache_decode_in_row_group c1
                 h.coh_path rg_index Prims.int_one cap in
             (match uu___4 with
              | (p_col, c2) ->
                  let uu___5 =
                    RDF_CottasStore_PageCache.pcache_decode_in_row_group c2
                      h.coh_path rg_index (Prims.of_int (2)) cap in
                  (match uu___5 with
                   | (o_col, c3) ->
                       let uu___6 =
                         RDF_CottasStore_PageCache.pcache_decode_in_row_group
                           c3 h.coh_path rg_index (Prims.of_int (3)) cap in
                       (match uu___6 with
                        | (g_col, c4) ->
                            let uu___7 =
                              match (s_col, p_col, o_col, g_col) with
                              | (FStar_Pervasives_Native.Some sc,
                                 FStar_Pervasives_Native.Some pc,
                                 FStar_Pervasives_Native.Some oc,
                                 FStar_Pervasives_Native.Some gc) ->
                                  filter_zipped_rows_limited h bound_s
                                    bound_p bound_o bound_g sc pc oc gc
                                    acc_rev acc_count limit
                              | uu___8 -> (acc_rev, acc_count, false) in
                            (match uu___7 with
                             | (acc_rev', acc_count', hit) ->
                                 if hit
                                 then (acc_rev', c4)
                                 else
                                   walk_row_groups_search_limited h bound_s
                                     bound_p bound_o bound_g
                                     (rg_index + Prims.int_one) rg_count
                                     (fuel - Prims.int_one) acc_rev'
                                     acc_count' limit c4)))))
let rec walk_candidate_rgs_search_limited (h : cottas_ondisk_handle)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (candidates : Prims.nat Prims.list)
  (acc_rev : Parser_BallyhooCOTTAS.cottas_qp_row Prims.list)
  (acc_count : Prims.nat) (limit : Prims.nat)
  (cache : RDF_CottasStore_PageCache.page_cache) :
  (Parser_BallyhooCOTTAS.cottas_qp_row Prims.list *
    RDF_CottasStore_PageCache.page_cache)=
  if acc_count >= limit
  then (acc_rev, cache)
  else
    (match candidates with
     | [] -> (acc_rev, cache)
     | rg_index::rest ->
         let cap = cache.RDF_CottasStore_PageCache.pc_capacity in
         let uu___1 =
           RDF_CottasStore_PageCache.pcache_decode_in_row_group cache
             h.coh_path rg_index Prims.int_zero cap in
         (match uu___1 with
          | (s_col, c1) ->
              let uu___2 =
                RDF_CottasStore_PageCache.pcache_decode_in_row_group c1
                  h.coh_path rg_index Prims.int_one cap in
              (match uu___2 with
               | (p_col, c2) ->
                   let uu___3 =
                     RDF_CottasStore_PageCache.pcache_decode_in_row_group c2
                       h.coh_path rg_index (Prims.of_int (2)) cap in
                   (match uu___3 with
                    | (o_col, c3) ->
                        let uu___4 =
                          RDF_CottasStore_PageCache.pcache_decode_in_row_group
                            c3 h.coh_path rg_index (Prims.of_int (3)) cap in
                        (match uu___4 with
                         | (g_col, c4) ->
                             let uu___5 =
                               match (s_col, p_col, o_col, g_col) with
                               | (FStar_Pervasives_Native.Some sc,
                                  FStar_Pervasives_Native.Some pc,
                                  FStar_Pervasives_Native.Some oc,
                                  FStar_Pervasives_Native.Some gc) ->
                                   filter_zipped_rows_limited h bound_s
                                     bound_p bound_o bound_g sc pc oc gc
                                     acc_rev acc_count limit
                               | uu___6 -> (acc_rev, acc_count, false) in
                             (match uu___5 with
                              | (acc_rev', acc_count', hit) ->
                                  if hit
                                  then (acc_rev', c4)
                                  else
                                    walk_candidate_rgs_search_limited h
                                      bound_s bound_p bound_o bound_g rest
                                      acc_rev' acc_count' limit c4))))))
let cottas_ondisk_search_limited (ds : cottas_ondisk_store)
  (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) (limit : Prims.nat) :
  Parser_BallyhooCOTTAS.cottas_qp_row Prims.list=
  Cottas_ondisk_runtime.search_fast_limited ds.cods_handle bound (Z.to_int limit)
let _spec_cottas_ondisk_search_limited_unused (ds : cottas_ondisk_store)
  (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) (limit : Prims.nat) :
  Parser_BallyhooCOTTAS.cottas_qp_row Prims.list=
  let h = ds.cods_handle in
  let bound_s =
    id_to_raw_token h.coh_subjects_raw bound.Parser_BallyhooCOTTAS.cbqp_s in
  let bound_p =
    id_to_raw_token h.coh_predicates_raw bound.Parser_BallyhooCOTTAS.cbqp_p in
  let bound_o =
    id_to_raw_token h.coh_objects_raw bound.Parser_BallyhooCOTTAS.cbqp_o in
  let bound_g =
    id_to_raw_token h.coh_graphs_raw bound.Parser_BallyhooCOTTAS.cbqp_g in
  match Parquet_Footer.probe_parquet_row_group_count h.coh_path with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some rg_count ->
      let cache0 =
        RDF_CottasStore_PageCache.pcache_empty pcache_default_capacity in
      let any_bound_present =
        (((FStar_Pervasives_Native.uu___is_Some bound_s) ||
            (FStar_Pervasives_Native.uu___is_Some bound_p))
           || (FStar_Pervasives_Native.uu___is_Some bound_o))
          || (FStar_Pervasives_Native.uu___is_Some bound_g) in
      if any_bound_present
      then
        let uu___ =
          plan_candidate_rgs h bound_s bound_p bound_o bound_g rg_count in
        (match uu___ with
         | (candidates, _dc) ->
             let uu___1 =
               walk_candidate_rgs_search_limited h bound_s bound_p bound_o
                 bound_g candidates [] Prims.int_zero limit cache0 in
             (match uu___1 with
              | (acc_rev, _cache') -> Parquet_Footer.list_rev acc_rev))
      else
        (let uu___1 =
           walk_row_groups_search_limited h bound_s bound_p bound_o bound_g
             Prims.int_zero rg_count rg_count [] Prims.int_zero limit cache0 in
         match uu___1 with
         | (acc_rev, _cache') -> Parquet_Footer.list_rev acc_rev)
let cottas_ondisk_estimate (ds : cottas_ondisk_store)
  (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : Prims.nat=
  (* Aleph6 streaming-COUNT shortcut: all-None bound -> read num_rows
     from the parquet footer (microseconds). Otherwise per-rg walk via
     estimate_fast. *)
  let any_bound_present =
    (FStar_Pervasives_Native.uu___is_Some bound.Parser_BallyhooCOTTAS.cbqp_s)
    || (FStar_Pervasives_Native.uu___is_Some bound.Parser_BallyhooCOTTAS.cbqp_p)
    || (FStar_Pervasives_Native.uu___is_Some bound.Parser_BallyhooCOTTAS.cbqp_o)
    || (FStar_Pervasives_Native.uu___is_Some bound.Parser_BallyhooCOTTAS.cbqp_g) in
  if not any_bound_present then
    (match Parquet_Footer.probe_parquet_num_rows
             (ds.cods_handle).coh_path with
     | FStar_Pervasives_Native.Some n ->
       Printf.eprintf "[aleph6-trace] estimate: all-None -> probe_parquet_num_rows = %s\n%!"
         (Z.to_string n);
       n
     | FStar_Pervasives_Native.None ->
       Z.of_int (Cottas_ondisk_runtime.estimate_fast ds.cods_handle bound))
  else
    Z.of_int (Cottas_ondisk_runtime.estimate_fast ds.cods_handle bound)
let _spec_cottas_ondisk_estimate_unused (ds : cottas_ondisk_store)
  (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : Prims.nat=
  let h = ds.cods_handle in
  let bound_s =
    id_to_raw_token h.coh_subjects_raw bound.Parser_BallyhooCOTTAS.cbqp_s in
  let bound_p =
    id_to_raw_token h.coh_predicates_raw bound.Parser_BallyhooCOTTAS.cbqp_p in
  let bound_o =
    id_to_raw_token h.coh_objects_raw bound.Parser_BallyhooCOTTAS.cbqp_o in
  let bound_g =
    id_to_raw_token h.coh_graphs_raw bound.Parser_BallyhooCOTTAS.cbqp_g in
  let any_bound_present =
    (((FStar_Pervasives_Native.uu___is_Some bound_s) ||
        (FStar_Pervasives_Native.uu___is_Some bound_p))
       || (FStar_Pervasives_Native.uu___is_Some bound_o))
      || (FStar_Pervasives_Native.uu___is_Some bound_g) in
  if Prims.op_Negation any_bound_present
  then
    match Parquet_Footer.probe_parquet_num_rows h.coh_path with
    | FStar_Pervasives_Native.Some n -> n
    | FStar_Pervasives_Native.None ->
        (match Parquet_Footer.probe_parquet_row_group_count h.coh_path with
         | FStar_Pervasives_Native.None -> Prims.int_zero
         | FStar_Pervasives_Native.Some rg_count ->
             let cache0 =
               RDF_CottasStore_PageCache.pcache_empty pcache_default_capacity in
             let uu___ =
               walk_row_groups_estimate h bound_s bound_p bound_o bound_g
                 Prims.int_zero rg_count rg_count Prims.int_zero cache0 in
             (match uu___ with | (count, _cache') -> count))
  else
    (match Parquet_Footer.probe_parquet_row_group_count h.coh_path with
     | FStar_Pervasives_Native.None -> Prims.int_zero
     | FStar_Pervasives_Native.Some rg_count ->
         let cache0 =
           RDF_CottasStore_PageCache.pcache_empty pcache_default_capacity in
         let uu___1 =
           plan_candidate_rgs h bound_s bound_p bound_o bound_g rg_count in
         (match uu___1 with
          | (candidates, _dc) ->
              let uu___2 =
                walk_candidate_rgs_estimate h bound_s bound_p bound_o bound_g
                  candidates Prims.int_zero cache0 in
              (match uu___2 with | (count, _cache') -> count)))
let cottas_ondisk_build_bound_qp_opt (ds : cottas_ondisk_store)
  (s : RDF_Graph_Executable.subject FStar_Pervasives_Native.option)
  (p : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (o : RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option)
  (g : RDF_Graph_Executable.iri FStar_Pervasives_Native.option) :
  Parser_BallyhooCOTTAS.cottas_bound_qp FStar_Pervasives_Native.option=
  let s' =
    match s with
    | FStar_Pervasives_Native.None ->
        FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some sv ->
        (match cottas_ondisk_encode_subject ds sv with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some r ->
             FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some r)) in
  let p' =
    match p with
    | FStar_Pervasives_Native.None ->
        FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some pv ->
        (match cottas_ondisk_encode_predicate ds pv with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some r ->
             FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some r)) in
  let o' =
    match o with
    | FStar_Pervasives_Native.None ->
        FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some ov ->
        (match cottas_ondisk_encode_object ds ov with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some r ->
             FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some r)) in
  let g' =
    match g with
    | FStar_Pervasives_Native.None ->
        FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some gv ->
        (match cottas_ondisk_encode_graph_name ds gv with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some r ->
             FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some r)) in
  match (s', p', o', g') with
  | (FStar_Pervasives_Native.Some sb, FStar_Pervasives_Native.Some pb,
     FStar_Pervasives_Native.Some ob, FStar_Pervasives_Native.Some gb) ->
      FStar_Pervasives_Native.Some
        {
          Parser_BallyhooCOTTAS.cbqp_s = sb;
          Parser_BallyhooCOTTAS.cbqp_p = pb;
          Parser_BallyhooCOTTAS.cbqp_o = ob;
          Parser_BallyhooCOTTAS.cbqp_g = gb
        }
  | uu___ -> FStar_Pervasives_Native.None
let cottas_ondisk_row_to_quad (ds : cottas_ondisk_store)
  (row : Parser_BallyhooCOTTAS.cottas_qp_row) :
  (RDF_Graph_Executable.triple * RDF_Graph_Executable.iri
    FStar_Pervasives_Native.option) FStar_Pervasives_Native.option=
  match ((row.Parser_BallyhooCOTTAS.cqpr_s),
          (row.Parser_BallyhooCOTTAS.cqpr_p),
          (row.Parser_BallyhooCOTTAS.cqpr_o))
  with
  | (FStar_Pervasives_Native.Some sr, FStar_Pervasives_Native.Some pr,
     FStar_Pervasives_Native.Some orf) ->
      FStar_Pervasives_Native.Some
        ({
           RDF_Graph_Executable.s = (cottas_ondisk_decode_subject ds sr);
           RDF_Graph_Executable.p = (cottas_ondisk_decode_predicate ds pr);
           RDF_Graph_Executable.o = (cottas_ondisk_decode_object ds orf)
         },
          ((match row.Parser_BallyhooCOTTAS.cqpr_g with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some gr ->
                FStar_Pervasives_Native.Some
                  (cottas_ondisk_decode_graph_name ds gr))))
  | uu___ -> FStar_Pervasives_Native.None
let rec cottas_ondisk_rows_to_quads_acc (ds : cottas_ondisk_store)
  (rows : Parser_BallyhooCOTTAS.cottas_qp_row Prims.list)
  (acc :
    (RDF_Graph_Executable.triple * RDF_Graph_Executable.iri
      FStar_Pervasives_Native.option) Prims.list)
  :
  (RDF_Graph_Executable.triple * RDF_Graph_Executable.iri
    FStar_Pervasives_Native.option) Prims.list=
  match rows with
  | [] -> acc
  | row::rest ->
      (match cottas_ondisk_row_to_quad ds row with
       | FStar_Pervasives_Native.None ->
           cottas_ondisk_rows_to_quads_acc ds rest acc
       | FStar_Pervasives_Native.Some quad ->
           cottas_ondisk_rows_to_quads_acc ds rest (quad :: acc))
let cottas_ondisk_rows_to_quads (ds : cottas_ondisk_store)
  (rows : Parser_BallyhooCOTTAS.cottas_qp_row Prims.list) :
  (RDF_Graph_Executable.triple * RDF_Graph_Executable.iri
    FStar_Pervasives_Native.option) Prims.list=
  FStar_List_Tot_Base.rev (cottas_ondisk_rows_to_quads_acc ds rows [])
let rec cottas_ondisk_rows_to_triples_acc (ds : cottas_ondisk_store)
  (rows : Parser_BallyhooCOTTAS.cottas_qp_row Prims.list)
  (acc : RDF_Graph_Executable.triple Prims.list) :
  RDF_Graph_Executable.triple Prims.list=
  match rows with
  | [] -> acc
  | row::rest ->
      (match cottas_ondisk_row_to_quad ds row with
       | FStar_Pervasives_Native.None ->
           cottas_ondisk_rows_to_triples_acc ds rest acc
       | FStar_Pervasives_Native.Some (t, _gname) ->
           cottas_ondisk_rows_to_triples_acc ds rest (t :: acc))
let cottas_ondisk_rows_to_triples (ds : cottas_ondisk_store)
  (rows : Parser_BallyhooCOTTAS.cottas_qp_row Prims.list) :
  RDF_Graph_Executable.triple Prims.list=
  FStar_List_Tot_Base.rev (cottas_ondisk_rows_to_triples_acc ds rows [])

(* vav3: Cottas_companion_writer installed (issue #100, 2026-04-26).
   Walks the parquet columns once per column (subjects, predicates,
   objects, graphs) and writes the .dict + .presence companion files
   sibling to the .cottas. Atomic: writes to .tmp, fsync, rename.

   Same algorithmic cost as today's pre-warm. Once the companions exist,
   subsequent boots skip this and just mmap. *)
module Cottas_companion_writer = struct
  open Stdlib
  type pint = Stdlib.Int.t

  let dict_magic : pint  = 0x44544f43  (* 'COTD' little-endian *)
  let presence_magic : pint  = 0x50544f43  (* 'COTP' little-endian *)
  let layout_version : pint = 1

  let column_suffix = function
    | 0 -> "s"
    | 1 -> "p"
    | 2 -> "o"
    | 3 -> "g"
    | _ -> "x"

  let dict_path     base col_idx = Printf.sprintf "%s.%s.dict"     base (column_suffix col_idx)
  let presence_path base col_idx = Printf.sprintf "%s.%s.presence" base (column_suffix col_idx)

  let write_u32_le buf (v : pint) =
    Buffer.add_char buf (Stdlib.Char.chr (v land 0xff));
    Buffer.add_char buf (Stdlib.Char.chr ((v lsr 8) land 0xff));
    Buffer.add_char buf (Stdlib.Char.chr ((v lsr 16) land 0xff));
    Buffer.add_char buf (Stdlib.Char.chr ((v lsr 24) land 0xff))

  let write_u64_le buf (v : pint) =
    write_u32_le buf (v land 0xffffffff);
    write_u32_le buf ((v lsr 32) land 0xffffffff)

  (* Walk every row group of `path`, column `col_idx`, collecting
     per-rg sets of distinct tokens AND a globally-sorted unique token
     list. Returns:
       (sorted_unique_tokens : string array,
        sorted_token_to_id   : (string -> pint),  via Hashtbl
        per_rg_token_set     : pint -> (string, unit) Hashtbl.t,
        rg_count             : pint)
     The sorted_unique_tokens is the ascending lexicographic ordering
     used by the .dict's binary search. *)
  let collect_distinct_per_rg (path : string) (col_idx : pint) =
    let rg_count = match Parquet_Footer.probe_parquet_row_group_count path with
      | FStar_Pervasives_Native.None -> 0
      | FStar_Pervasives_Native.Some n -> Z.to_int n in
    let global : (string, unit) Hashtbl.t = Hashtbl.create 1024 in
    let per_rg : (pint, (string, unit) Hashtbl.t) Hashtbl.t = Hashtbl.create 32 in
    for rg = 0 to rg_count - 1 do
      let rg_set : (string, unit) Hashtbl.t = Hashtbl.create 256 in
      (match Parquet_Footer.probe_parquet_column_decode_in_row_group
               path (Z.of_int rg) (Z.of_int col_idx) with
       | FStar_Pervasives_Native.None ->
         Printf.eprintf "[vav3-WARN] writer: rg=%d col=%d decode failed\n%!" rg col_idx
       | FStar_Pervasives_Native.Some lst ->
         List.iter (function
           | FStar_Pervasives_Native.None -> ()
           | FStar_Pervasives_Native.Some raw ->
             if not (Hashtbl.mem rg_set raw) then Hashtbl.add rg_set raw ();
             if not (Hashtbl.mem global raw) then Hashtbl.add global raw ()
         ) lst);
      Hashtbl.replace per_rg rg rg_set;
      if rg = 0 || rg = rg_count - 1 || rg mod 5 = 0 then
        Printf.eprintf "[vav3-trace] writer rg=%d/%d col=%d distinct_so_far=%d\n%!"
          rg rg_count col_idx (Hashtbl.length global)
    done;
    let arr = Array.make (Hashtbl.length global) "" in
    let i = ref 0 in
    Hashtbl.iter (fun k () -> arr.(!i) <- k; incr i) global;
    Array.sort String.compare arr;
    let tok_to_id : (string, pint) Hashtbl.t = Hashtbl.create (Array.length arr * 2 + 17) in
    Array.iteri (fun id tok -> Hashtbl.add tok_to_id tok id) arr;
    (arr, tok_to_id, per_rg, rg_count)

  let atomic_write (path : string) (data : string) : unit =
    let tmp = path ^ ".tmp" in
    let oc = open_out_bin tmp in
    output_string oc data;
    flush oc;
    (try Unix.fsync (Unix.descr_of_out_channel oc) with _ -> ());
    close_out oc;
    Sys.rename tmp path

  (* Writer for one column's .dict file.
     Layout (per RDF.CottasStore.OnDiskIndex.fst):
       [ magic u32 | version u32 | num_tokens u32 | pad u32 ]
       [ ids_offset u64 | tokens_offset u64 ]
       [ ids[]         u32 * num_tokens, sorted ASC by token ]
       [ token_offs[]  u64 * (num_tokens+1) ]
       [ token_data    bytes ]
  *)
  let write_dict_file (path : string) (sorted_tokens : string array) : unit =
    let n = Array.length sorted_tokens in
    (* Header: 32 bytes. Then ids[] (4*n bytes). Then token_offs[]
       (8*(n+1) bytes). Then token_data. *)
    let header_size  = 32 in
    let ids_size     = 4 * n in
    let offs_size    = 8 * (n + 1) in
    let ids_offset    = header_size in
    let tokens_offset = header_size + ids_size in
    let token_data_offset = tokens_offset + offs_size in
    let total_token_bytes =
      Array.fold_left (fun acc s -> acc + String.length s) 0 sorted_tokens in
    let buf = Buffer.create (header_size + ids_size + offs_size + total_token_bytes) in
    (* Header. *)
    write_u32_le buf dict_magic;
    write_u32_le buf layout_version;
    write_u32_le buf n;
    write_u32_le buf 0;  (* pad *)
    write_u64_le buf ids_offset;
    write_u64_le buf tokens_offset;
    (* ids[] : since we sorted the global set, and assigned ids 0..n-1
       in that sorted order (Hashtbl.add tok_to_id tok id with id =
       sorted index), the binary-search invariant is "tokens[ids[i]] is
       lexicographically ascending in i". With our id assignment that's
       just ids[i] = i. *)
    for i = 0 to n - 1 do write_u32_le buf i done;
    (* token_offs[] *)
    let cur_off = ref token_data_offset in
    write_u64_le buf !cur_off;
    for i = 0 to n - 1 do
      cur_off := !cur_off + String.length sorted_tokens.(i);
      write_u64_le buf !cur_off
    done;
    (* token_data *)
    for i = 0 to n - 1 do
      Buffer.add_string buf sorted_tokens.(i)
    done;
    atomic_write path (Buffer.contents buf)

  (* Writer for one column's .presence file.
     Layout:
       [ magic u32 | version u32 | num_rgs u32 | num_tokens u32 ]
       [ bitmap : ceil(num_rgs * num_tokens / 8) bytes, row-major,
                  bit (rg*num_tokens + tok) ] *)
  let write_presence_file (path : string)
    (rg_count : pint)
    (sorted_tokens : string array)
    (tok_to_id : (string, pint) Hashtbl.t)
    (per_rg : (pint, (string, unit) Hashtbl.t) Hashtbl.t) : unit =
    let n = Array.length sorted_tokens in
    let bits = rg_count * n in
    let bytes = (bits + 7) / 8 in
    let bitmap = Bytes.make bytes '\000' in
    for rg = 0 to rg_count - 1 do
      match Hashtbl.find_opt per_rg rg with
      | None -> ()
      | Some rg_set ->
        Hashtbl.iter (fun tok () ->
          match Hashtbl.find_opt tok_to_id tok with
          | None -> ()
          | Some tok_id ->
            let bit_index = rg * n + tok_id in
            let byte_index = bit_index / 8 in
            let bit_in_byte = bit_index mod 8 in
            let cur = Stdlib.Char.code (Bytes.unsafe_get bitmap byte_index) in
            Bytes.unsafe_set bitmap byte_index
              (Stdlib.Char.chr (cur lor (1 lsl bit_in_byte)))
        ) rg_set
    done;
    let buf = Buffer.create (16 + bytes) in
    write_u32_le buf presence_magic;
    write_u32_le buf layout_version;
    write_u32_le buf rg_count;
    write_u32_le buf n;
    Buffer.add_bytes buf bitmap;
    atomic_write path (Buffer.contents buf)

  let build_companion_pair (cottas_path : string) (col_idx : pint) : pint =
    let dpath = dict_path     cottas_path col_idx in
    let ppath = presence_path cottas_path col_idx in
    Printf.eprintf "[vav3-trace] writer: building companion col=%d dict=%s presence=%s\n%!"
      col_idx dpath ppath;
    let t0 = Unix.gettimeofday () in
    let (sorted, tok_to_id, per_rg, rg_count) = collect_distinct_per_rg cottas_path col_idx in
    let t1 = Unix.gettimeofday () in
    Printf.eprintf "[vav3-trace] writer col=%d collect_distinct: %.2fs (%d distinct, %d rgs)\n%!"
      col_idx (t1 -. t0) (Array.length sorted) rg_count;
    write_dict_file dpath sorted;
    let t2 = Unix.gettimeofday () in
    Printf.eprintf "[vav3-trace] wrote companion %s (Nbytes=%d) in %.2fs\n%!"
      dpath (try (Unix.stat dpath).Unix.st_size with _ -> -1) (t2 -. t1);
    write_presence_file ppath rg_count sorted tok_to_id per_rg;
    let t3 = Unix.gettimeofday () in
    Printf.eprintf "[vav3-trace] wrote companion %s (Nbytes=%d) in %.2fs\n%!"
      ppath (try (Unix.stat ppath).Unix.st_size with _ -> -1) (t3 -. t2);
    Array.length sorted
end

(* vav3: Cottas_companion_boot installed.
   The orchestrator: open mmaps if companions exist + verify; else
   build them via Cottas_companion_writer and then mmap. Then bulk-
   populate the existing fast_tables Hashtbls + Yod6/Tet3 presence
   maps from the mmap'd companions. Sub-second on parliament. *)
module Cottas_companion_boot = struct
  open Stdlib
  type pint = Stdlib.Int.t

  (* Check that all 4 .dict + 4 .presence companions exist for `cottas_path`
     and verify their headers. Returns true iff every companion is loadable. *)
  let companions_present_and_valid (cottas_path : string) : bool =
    let all_ok = ref true in
    for col_idx = 0 to 3 do
      let dpath = Cottas_companion_writer.dict_path     cottas_path col_idx in
      let ppath = Cottas_companion_writer.presence_path cottas_path col_idx in
      if not (Sys.file_exists dpath && Sys.file_exists ppath) then begin
        all_ok := false;
        Printf.eprintf "[vav3-trace] companion absent for col=%d (dict=%s presence=%s)\n%!"
          col_idx dpath ppath
      end else begin
        (* Verify headers via the F*-extracted readers. *)
        let dh = RDF_CottasStore_OnDiskIndex.read_dict_header dpath in
        let ph = RDF_CottasStore_OnDiskIndex.read_presence_header ppath in
        match dh, ph with
        | FStar_Pervasives_Native.Some dh', FStar_Pervasives_Native.Some ph' ->
          if not (RDF_CottasStore_OnDiskIndex.dict_header_ok dh' &&
                  RDF_CottasStore_OnDiskIndex.presence_header_ok ph') then begin
            all_ok := false;
            Printf.eprintf "[vav3-trace] companion header verify FAILED for col=%d\n%!" col_idx
          end
        | _ ->
          all_ok := false;
          Printf.eprintf "[vav3-trace] companion header read FAILED for col=%d\n%!" col_idx
      end
    done;
    !all_ok

  (* Build all 4 companion-pair files for `cottas_path`. One-time cost
     (~110s on parliament); persists forever. *)
  let build_all_companions (cottas_path : string) : unit =
    Printf.eprintf "[vav3-trace] building all companions for %s\n%!" cottas_path;
    let t0 = Unix.gettimeofday () in
    for col_idx = 0 to 3 do
      let _n = Cottas_companion_writer.build_companion_pair cottas_path col_idx in
      ()
    done;
    let dt = Unix.gettimeofday () -. t0 in
    Printf.eprintf "[vav3-trace] all 4 companion-pair files written in %.2fs\n%!" dt

  (* Bulk-populate the Hashtbl-based fast_tables AND Yod6/Tet3 presence
     maps from the mmap'd companions. Sub-second on parliament since the
     mmap'd region is just a sequential walk.

     We iterate dict tokens 0..num_tokens-1: each id maps to the raw
     column-token via dict_decode_token. We also walk the presence
     bitmap rg-by-rg: for each rg, scan the rg's bits to find set
     positions and add those token strings to the rg_set Hashtbl.

     This is the bulk-load shim: in a follow-on phase the _fast
     functions will consult the mmap'd companions directly via
     companion_encode/companion_decode/companion_rg_could_contain
     (extracted from F-star), eliminating the Hashtbls entirely. *)
  let bulk_load_column_into_tables
    (cottas_path : string) (col_idx : pint)
    (h : cottas_ondisk_handle)
    (tables : Cottas_ondisk_runtime.fast_tables) : pint =
    let dpath = Cottas_companion_writer.dict_path     cottas_path col_idx in
    let ppath = Cottas_companion_writer.presence_path cottas_path col_idx in
    let dh_opt = RDF_CottasStore_OnDiskIndex.read_dict_header dpath in
    let ph_opt = RDF_CottasStore_OnDiskIndex.read_presence_header ppath in
    match dh_opt, ph_opt with
    | FStar_Pervasives_Native.Some dh, FStar_Pervasives_Native.Some ph ->
      let n_tok = Z.to_int dh.RDF_CottasStore_OnDiskIndex.dh_num_tokens in
      let n_rgs = Z.to_int ph.RDF_CottasStore_OnDiskIndex.ph_num_rgs in
      Printf.eprintf "[vav3-trace] bulk-load col=%d num_tokens=%d num_rgs=%d\n%!"
        col_idx n_tok n_rgs;
      (* Step 1: walk the .dict to populate global tok_to_id + id_to_tok.
         We use direct mmap reads (instead of dict_decode_token per id)
         to amortise mmap-view-lookup cost. The F* spec is byte-identical;
         this is a perf shim. *)
      let _ = h in  (* h.coh_path used only for sanity; we use cottas_path explicitly *)
      let _ = RDF_CottasStore_OnDiskIndex.Vav3_mmap.try_open_mmap dpath in
      let dview_opt = Hashtbl.find_opt RDF_CottasStore_OnDiskIndex.Vav3_mmap.views dpath in
      let read_token : pint -> string option = match dview_opt with
        | None -> (fun _ -> None)
        | Some dv ->
          let mv_data = dv.RDF_CottasStore_OnDiskIndex.Vav3_mmap.mv_data in
          let mv_size = dv.RDF_CottasStore_OnDiskIndex.Vav3_mmap.mv_size in
          let tokens_offset_int = Z.to_int dh.RDF_CottasStore_OnDiskIndex.dh_tokens_offset in
          (* Read u64 LE inline; assumes value fits in 63-bit int (yes: file
             sizes are <500MB on parliament). *)
          let read_u64 off =
            if off + 8 > mv_size then None
            else
              let g i = Stdlib.Char.code (Bigarray.Array1.unsafe_get mv_data i) in
              let b0 = g off in let b1 = g (off+1) in
              let b2 = g (off+2) in let b3 = g (off+3) in
              let b4 = g (off+4) in let b5 = g (off+5) in
              let b6 = g (off+6) in let b7 = g (off+7) in
              if b7 >= 0x80 then None
              else
                let lo = b0 lor (b1 lsl 8) lor (b2 lsl 16) lor (b3 lsl 24) in
                let hi = b4 lor (b5 lsl 8) lor (b6 lsl 16) lor (b7 lsl 24) in
                Some (lo lor (hi lsl 32)) in
          (* Token start offset for token-id `id` at byte offset
             tokens_offset + 8*id; end at tokens_offset + 8*(id+1). *)
          (fun id ->
            match read_u64 (tokens_offset_int + 8 * id) with
            | None -> None
            | Some token_start ->
              match read_u64 (tokens_offset_int + 8 * (id + 1)) with
              | None -> None
              | Some token_end ->
                if token_end < token_start then None
                else
                  let len = token_end - token_start in
                  if token_start + len > mv_size then None
                  else
                    let buf = Stdlib.Bytes.create len in
                    for i = 0 to len - 1 do
                      Stdlib.Bytes.unsafe_set buf i
                        (Bigarray.Array1.unsafe_get mv_data (token_start + i))
                    done;
                    Some (Stdlib.Bytes.unsafe_to_string buf)) in
      (* Bulk-populate the raw token mappings (encode + id_to_tok). The
         TYPED-term Hashtbls (ft_id_to_subject/predicate/object/graph)
         are NOT populated here — typed parses happen lazily on first
         decode_*_fast call. Predicates+graphs are tiny (232 + 1) so we
         do parse them eagerly here for simplicity. *)
      for id = 0 to n_tok - 1 do
        match read_token id with
        | None ->
          Printf.eprintf "[vav3-WARN] bulk-load col=%d id=%d decode failed\n%!" col_idx id
        | Some raw ->
          (match col_idx with
           | 0 ->
             Hashtbl.replace tables.Cottas_ondisk_runtime.ft_subj_tok_to_id raw id;
             Hashtbl.replace tables.Cottas_ondisk_runtime.ft_id_to_subj_tok id raw
             (* Skip ft_id_to_subject; populated lazily by decode_subject_fast. *)
           | 1 ->
             Hashtbl.replace tables.Cottas_ondisk_runtime.ft_pred_tok_to_id raw id;
             Hashtbl.replace tables.Cottas_ondisk_runtime.ft_id_to_pred_tok id raw;
             (* Predicates are small (232); eager parse is fine. *)
             (match Cottas_ondisk_runtime.parse_iri_token raw with
              | Some iri ->
                Hashtbl.replace tables.Cottas_ondisk_runtime.ft_id_to_predicate id (iri : RDF_Graph_Executable.wf_iri)
              | None -> Printf.eprintf "[vav3-WARN] bulk-load: bad predicate id=%d raw=%s\n%!" id raw)
           | 2 ->
             Hashtbl.replace tables.Cottas_ondisk_runtime.ft_obj_tok_to_id raw id;
             Hashtbl.replace tables.Cottas_ondisk_runtime.ft_id_to_obj_tok id raw
             (* Skip ft_id_to_object; populated lazily by decode_object_fast. *)
           | 3 ->
             Hashtbl.replace tables.Cottas_ondisk_runtime.ft_graph_tok_to_id raw id;
             Hashtbl.replace tables.Cottas_ondisk_runtime.ft_id_to_graph_tok id raw;
             (match Cottas_ondisk_runtime.parse_iri_token raw with
              | Some iri ->
                Hashtbl.replace tables.Cottas_ondisk_runtime.ft_id_to_graph id (iri : RDF_Graph_Executable.iri)
              | None ->
                (* DEFAULT graph token doesn't parse to an IRI; skip silently. *)
                if raw <> "DEFAULT" then
                  Printf.eprintf "[vav3-WARN] bulk-load: bad graph id=%d raw=%s\n%!" id raw)
           | _ -> ())
      done;
      (* Step 2: walk the .presence bitmap rg-by-rg to populate
         Yod6/Tet3 presence maps. Sequential byte-walk over the
         mmap'd bitmap region — one Hashtbl.add per set bit. The F*
         spec `presence_test_bit` is byte-identical to this walk; we
         skip the per-bit F* dispatch for boot speed. (Phase E swaps
         the query path to read the bitmap directly via the F*-pure
         primitive — this bulk-load is a transitional shim.) *)
      let id_to_tok_table = match col_idx with
        | 0 -> tables.Cottas_ondisk_runtime.ft_id_to_subj_tok
        | 1 -> tables.Cottas_ondisk_runtime.ft_id_to_pred_tok
        | 2 -> tables.Cottas_ondisk_runtime.ft_id_to_obj_tok
        | 3 -> tables.Cottas_ondisk_runtime.ft_id_to_graph_tok
        | _ -> Hashtbl.create 1 in
      (* Pick the right presence table from Cottas_ondisk_lazy. *)
      let target_presence_for_path : string -> (Stdlib.Int.t, (string, unit) Hashtbl.t) Hashtbl.t =
        match col_idx with
        | 0 -> Cottas_ondisk_lazy.subj_presence_for_path
        | 1 -> Cottas_ondisk_lazy.presence_for_path
        | 2 -> Cottas_ondisk_lazy.obj_presence_for_path
        | _ -> (fun _ -> Hashtbl.create 0) in
      let target_presence = target_presence_for_path cottas_path in
      (* Direct mmap byte-walk. ph_num_tokens bits per rg, packed LSB-first.
         Whole-byte zero-skip: when an entire byte is 0 it can't contain
         any set bits, so we advance 8 bit-indices at once. Otherwise we
         test each of the (up-to-)8 bits individually. *)
      let _ = RDF_CottasStore_OnDiskIndex.Vav3_mmap.try_open_mmap ppath in
      (match Hashtbl.find_opt RDF_CottasStore_OnDiskIndex.Vav3_mmap.views ppath with
       | None ->
         Printf.eprintf "[vav3-WARN] bulk-load col=%d: presence mmap not available\n%!" col_idx
       | Some v ->
         let bitmap_offset = 16 in  (* presence_header_size *)
         let mv_data = v.RDF_CottasStore_OnDiskIndex.Vav3_mmap.mv_data in
         for rg = 0 to n_rgs - 1 do
           let rg_set : (string, unit) Hashtbl.t = Hashtbl.create 256 in
           let base_bit = rg * n_tok in
           let id = ref 0 in
           while !id < n_tok do
             let bit_index = base_bit + !id in
             let byte_idx = bitmap_offset + bit_index / 8 in
             let bit_in_byte = bit_index mod 8 in
             let b = Stdlib.Char.code (Bigarray.Array1.unsafe_get mv_data byte_idx) in
             if b = 0 then begin
               (* Skip remaining bits in this byte (8 - bit_in_byte). *)
               id := !id + (8 - bit_in_byte)
             end else if (b lsr bit_in_byte) land 1 = 1 then begin
               (match Hashtbl.find_opt id_to_tok_table !id with
                | None -> ()
                | Some raw ->
                  if not (Hashtbl.mem rg_set raw) then Hashtbl.add rg_set raw ());
               incr id
             end else
               incr id
           done;
           Hashtbl.replace target_presence rg rg_set
         done);
      n_tok
    | _ ->
      Printf.eprintf "[vav3-FATAL] bulk-load col=%d header read failed\n%!" col_idx;
      0

  let prewarm_via_companions (cottas_path : string)
    (h : cottas_ondisk_handle) : unit =
    let t0 = Unix.gettimeofday () in
    let tables = Cottas_ondisk_runtime.tables_for h in
    if not (companions_present_and_valid cottas_path) then begin
      Printf.eprintf "[vav3-trace] companions absent or invalid; building (one-time cost)\n%!";
      build_all_companions cottas_path
    end else begin
      Printf.eprintf "[vav3-trace] mmap'd companion files, skipping pre-warm\n%!"
    end;
    (* Bulk-load each column's tables from the (now-present) companions. *)
    for col_idx = 0 to 3 do
      let _ = bulk_load_column_into_tables cottas_path col_idx h tables in
      ()
    done;
    (* Mark every column as loaded so the lazy populators (Bet7) skip. *)
    Cottas_ondisk_lazy.mark_subj_loaded  cottas_path;
    Cottas_ondisk_lazy.mark_pred_loaded  cottas_path;
    Cottas_ondisk_lazy.mark_obj_loaded   cottas_path;
    Cottas_ondisk_lazy.mark_graph_loaded cottas_path;
    let dt = Unix.gettimeofday () -. t0 in
    Printf.eprintf "[vav3-trace] prewarm_via_companions completed in %.2fs (subjs=%d preds=%d objs=%d graphs=%d)\n%!"
      dt
      (Hashtbl.length tables.Cottas_ondisk_runtime.ft_subj_tok_to_id)
      (Hashtbl.length tables.Cottas_ondisk_runtime.ft_pred_tok_to_id)
      (Hashtbl.length tables.Cottas_ondisk_runtime.ft_obj_tok_to_id)
      (Hashtbl.length tables.Cottas_ondisk_runtime.ft_graph_tok_to_id)
end
