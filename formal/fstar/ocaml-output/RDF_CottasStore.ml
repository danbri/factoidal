open Prims
type cottas_ondisk_handle =
  {
  coh_path: Prims.string ;
  coh_summary:
    Parser_BallyhooCOTTAS.cottas_artifact_summary
      FStar_Pervasives_Native.option
    ;
  coh_subjects: RDF_Term.subject Prims.list ;
  coh_predicates: RDF_Term.wf_iri Prims.list ;
  coh_objects: RDF_Term.rdf_term Prims.list ;
  coh_graphs: RDF_Term.iri Prims.list ;
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
  (projectee : cottas_ondisk_handle) : RDF_Term.subject Prims.list=
  match projectee with
  | { coh_path; coh_summary; coh_subjects; coh_predicates; coh_objects;
      coh_graphs; coh_subj_revmap; coh_pred_revmap; coh_obj_revmap;
      coh_graph_revmap; coh_subjects_raw; coh_predicates_raw;
      coh_objects_raw; coh_graphs_raw; coh_subj_raw_revmap;
      coh_pred_raw_revmap; coh_obj_raw_revmap; coh_graph_raw_revmap;_} ->
      coh_subjects
let __proj__Mkcottas_ondisk_handle__item__coh_predicates
  (projectee : cottas_ondisk_handle) : RDF_Term.wf_iri Prims.list=
  match projectee with
  | { coh_path; coh_summary; coh_subjects; coh_predicates; coh_objects;
      coh_graphs; coh_subj_revmap; coh_pred_revmap; coh_obj_revmap;
      coh_graph_revmap; coh_subjects_raw; coh_predicates_raw;
      coh_objects_raw; coh_graphs_raw; coh_subj_raw_revmap;
      coh_pred_raw_revmap; coh_obj_raw_revmap; coh_graph_raw_revmap;_} ->
      coh_predicates
let __proj__Mkcottas_ondisk_handle__item__coh_objects
  (projectee : cottas_ondisk_handle) : RDF_Term.rdf_term Prims.list=
  match projectee with
  | { coh_path; coh_summary; coh_subjects; coh_predicates; coh_objects;
      coh_graphs; coh_subj_revmap; coh_pred_revmap; coh_obj_revmap;
      coh_graph_revmap; coh_subjects_raw; coh_predicates_raw;
      coh_objects_raw; coh_graphs_raw; coh_subj_raw_revmap;
      coh_pred_raw_revmap; coh_obj_raw_revmap; coh_graph_raw_revmap;_} ->
      coh_objects
let __proj__Mkcottas_ondisk_handle__item__coh_graphs
  (projectee : cottas_ondisk_handle) : RDF_Term.iri Prims.list=
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
let subject_to_revmap_key (s : RDF_Term.subject) : Prims.string=
  match s with
  | RDF_Term.S_IRI i -> FStar_String.concat "" ["I_"; i]
  | RDF_Term.S_BNode b -> FStar_String.concat "" ["B_"; b]
let iri_to_revmap_key (i : RDF_Term.iri) : Prims.string=
  FStar_String.concat "" ["I_"; i]
let rec object_to_revmap_key (o : RDF_Term.rdf_term) : Prims.string=
  match o with
  | RDF_Term.T_IRI i -> FStar_String.concat "" ["I_"; i]
  | RDF_Term.T_BNode b -> FStar_String.concat "" ["B_"; b]
  | RDF_Term.T_Literal l ->
      let tag =
        match l.RDF_Term.lang_tag with
        | FStar_Pervasives_Native.Some t -> t
        | FStar_Pervasives_Native.None -> "" in
      let base =
        FStar_String.concat ""
          ["L_";
          l.RDF_Term.datatype;
          revmap_unit_sep;
          tag;
          revmap_unit_sep;
          l.RDF_Term.lexical_form] in
      (match l.RDF_Term.direction with
       | FStar_Pervasives_Native.None -> base
       | FStar_Pervasives_Native.Some (RDF_Term.Dir_LTR) ->
           FStar_String.concat "" [base; revmap_unit_sep; "ltr"]
       | FStar_Pervasives_Native.Some (RDF_Term.Dir_RTL) ->
           FStar_String.concat "" [base; revmap_unit_sep; "rtl"])
  | RDF_Term.T_TripleTerm (s, p, obj) ->
      let subj =
        match s with
        | RDF_Term.S_IRI i -> FStar_String.concat "" ["I_"; i]
        | RDF_Term.S_BNode b -> FStar_String.concat "" ["B_"; b] in
      FStar_String.concat ""
        ["T_";
        subj;
        revmap_unit_sep;
        p;
        revmap_unit_sep;
        object_to_revmap_key obj]
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

  (* Issue #110 Option B: Hashtbls and accessors retained for the Vav3
     reader (cottas_ondisk_zzzzz_ondisk_index.sh) after the dead-shim
     patches (yod6 / tet3 / mem5 / etc.) were retired. These are pure
     structural plumbing — empty per-path Hashtbl-of-Hashtbl maps with
     get-style accessors. The semantic prune logic that USED to populate
     and consult them lived in the deleted shims and is no longer on
     the public path; the F*-extracted `compute_candidate_rgs_loop`
     in RDF.CottasStore handles candidate-rg pruning now. The Vav3
     companion-file reader still references these accessors to seed
     its on-disk index path; keeping them as empty tables is safe
     glue (rule #11 allowed: structural, no decisions). *)
  (* Yod6/Tet3 in-RAM presence Hashtbls + accessors retired (issue #249).
     The query path consults RDF.CottasStore.PresenceBitmap.rg_could_contain
     against the mmap'd companion file directly; this OCaml mirror was
     populated but never read. *)
end


(* lamed3: Cottas_offset_idx installed (issue #100, 2026-04-26).
   Per-(rg, pred_id) row-position index. Sibling .p.offsets file:
     [ magic 'COTO' u32 | version u32 | num_rgs u32 | num_preds u32 ]
     [ rg_offsets : u64 array, length num_rgs * num_preds + 1 ]
     [ data : u32[] row positions, ascending, packed ]
   Saves the predicate-column decode on every bound-predicate query.
   Built once, mmap'd forever. *)
module Cottas_offset_idx = struct
  open Stdlib
  type pint = Stdlib.Int.t

  let offsets_magic : pint = 0x4f544f43  (* 'COTO' little-endian *)
  let layout_version : pint = 1
  let header_size : pint = 16  (* 4 u32 fields *)

  let offsets_path (cottas_path : string) : string =
    cottas_path ^ ".p.offsets"

  let write_u32_le buf (v : pint) =
    Buffer.add_char buf (Stdlib.Char.chr (v land 0xff));
    Buffer.add_char buf (Stdlib.Char.chr ((v lsr 8) land 0xff));
    Buffer.add_char buf (Stdlib.Char.chr ((v lsr 16) land 0xff));
    Buffer.add_char buf (Stdlib.Char.chr ((v lsr 24) land 0xff))

  let write_u64_le buf (v : pint) =
    write_u32_le buf (v land 0xffffffff);
    write_u32_le buf ((v lsr 32) land 0xffffffff)

  let atomic_write (path : string) (data : string) : unit =
    let tmp = path ^ ".tmp" in
    let oc = open_out_bin tmp in
    output_string oc data;
    flush oc;
    (try Unix.fsync (Unix.descr_of_out_channel oc) with _ -> ());
    close_out oc;
    Sys.rename tmp path

  (* Build the offsets file by walking the predicate column once per rg.
     Requires the predicate dict's tok_to_id mapping (as a Hashtbl)
     so we can encode each token to its dict id during the walk. *)
  let build_offsets_file (cottas_path : string)
    (pred_tok_to_id : (string, pint) Hashtbl.t)
    (num_rgs : pint) (num_preds : pint) : unit =
    let opath = offsets_path cottas_path in
    Printf.eprintf "[lamed3-trace] building offsets file %s (num_rgs=%d num_preds=%d)\n%!"
      opath num_rgs num_preds;
    let t0 = Unix.gettimeofday () in
    (* Per-(rg, pred) -> row-position list. We accumulate as growable
       int arrays; flatten + write at the end. We explicitly use
       Stdlib.Array because `open Prims` at the top of this file
       shadows `array` with `Prims.array`. *)
    let buckets =
      Stdlib.Array.make_matrix num_rgs num_preds (Stdlib.Array.make 0 0) in
    let bucket_lens =
      Stdlib.Array.make_matrix num_rgs num_preds 0 in
    let push_pos rg pred_id pos =
      let cur = buckets.(rg).(pred_id) in
      let n = bucket_lens.(rg).(pred_id) in
      let cap = Stdlib.Array.length cur in
      let arr =
        if n < cap then cur
        else
          let new_cap = if cap = 0 then 8 else cap * 2 in
          let na = Stdlib.Array.make new_cap 0 in
          if cap > 0 then Stdlib.Array.blit cur 0 na 0 cap;
          buckets.(rg).(pred_id) <- na;
          na
      in
      arr.(n) <- pos;
      bucket_lens.(rg).(pred_id) <- n + 1
    in
    for rg = 0 to num_rgs - 1 do
      let t_rg = Unix.gettimeofday () in
      (match Parquet_Footer.probe_parquet_column_decode_in_row_group
               cottas_path (Z.of_int rg) Z.one with
       | FStar_Pervasives_Native.None ->
         Printf.eprintf "[lamed3-WARN] offsets-build: rg=%d predicate decode failed\n%!" rg
       | FStar_Pervasives_Native.Some lst ->
         (* lst is a list of `string option`. Walk with index. *)
         let row = ref 0 in
         List.iter (function
           | FStar_Pervasives_Native.None -> incr row
           | FStar_Pervasives_Native.Some raw ->
             (match Hashtbl.find_opt pred_tok_to_id raw with
              | None ->
                Printf.eprintf "[lamed3-WARN] offsets-build: rg=%d row=%d unknown predicate token %s\n%!"
                  rg !row raw
              | Some pred_id ->
                if pred_id >= 0 && pred_id < num_preds then
                  push_pos rg pred_id !row
                else
                  Printf.eprintf "[lamed3-WARN] offsets-build: pred_id %d out of range\n%!" pred_id);
             incr row) lst);
      if rg = 0 || rg = num_rgs - 1 || rg mod 5 = 0 then
        Printf.eprintf "[lamed3-trace] offsets-build rg=%d/%d (%.2fs this rg)\n%!"
          rg num_rgs (Unix.gettimeofday () -. t_rg)
    done;
    Printf.eprintf "[lamed3-trace] offsets-build columnscan done in %.2fs\n%!"
      (Unix.gettimeofday () -. t0);
    (* Build the file. Header (16 bytes) + rg_offsets (8 bytes each,
       length num_rgs*num_preds+1) + data (4 bytes per row position). *)
    let n_index = num_rgs * num_preds + 1 in
    let index_size = 8 * n_index in
    let data_offset0 = header_size + index_size in
    (* First pass: compute byte offset for every (rg, pred) cell. *)
    let rg_offsets = Stdlib.Array.make n_index 0 in
    let cur = ref data_offset0 in
    for rg = 0 to num_rgs - 1 do
      for p = 0 to num_preds - 1 do
        rg_offsets.(rg * num_preds + p) <- !cur;
        cur := !cur + 4 * bucket_lens.(rg).(p)
      done
    done;
    rg_offsets.(num_rgs * num_preds) <- !cur;
    let total_size = !cur in
    Printf.eprintf "[lamed3-trace] offsets-build computed total_size=%d bytes (%.1f MB)\n%!"
      total_size (float_of_int total_size /. (1024.0 *. 1024.0));
    let buf = Buffer.create total_size in
    (* Header — produced by F* (rule #11(a) byte-layout boundary). *)
    let header_chars =
      RDF_CottasStore_OffsetsWriter.serialize_offsets_header
        (Z.of_int num_rgs) (Z.of_int num_preds)
    in
    List.iter (fun b -> Buffer.add_char buf (Char.chr (b land 0xff))) header_chars;
    (* Index. *)
    for i = 0 to n_index - 1 do
      write_u64_le buf rg_offsets.(i)
    done;
    (* Data. *)
    for rg = 0 to num_rgs - 1 do
      for p = 0 to num_preds - 1 do
        let arr = buckets.(rg).(p) in
        let n = bucket_lens.(rg).(p) in
        for i = 0 to n - 1 do
          write_u32_le buf (Stdlib.Array.unsafe_get arr i)
        done
      done
    done;
    let t1 = Unix.gettimeofday () in
    atomic_write opath (Buffer.contents buf);
    let t2 = Unix.gettimeofday () in
    let stat_size = try (Unix.stat opath).Unix.st_size with _ -> -1 in
    Printf.eprintf "[lamed3-trace] offsets-build wrote %s (Nbytes=%d) in %.2fs (build %.2fs + write %.2fs)\n%!"
      opath stat_size (t2 -. t0) (t1 -. t0) (t2 -. t1)

  (* ---- Reader. ---- *)

  (* Per-path cached header + mmap view. *)
  type idx_header = {
    ih_num_rgs : pint;
    ih_num_preds : pint;
    ih_index_offset : pint;  (* always 16 *)
    ih_data_offset : pint;
  }

  let header_cache : (string, idx_header) Hashtbl.t = Hashtbl.create 17

  let read_header (cottas_path : string) : idx_header option =
    let opath = offsets_path cottas_path in
    match Hashtbl.find_opt header_cache opath with
    | Some h -> Some h
    | None ->
      match RDF_CottasStore_OnDiskIndex.Vav3_mmap.try_open_mmap opath with
      | None -> None
      | Some _size ->
        match Hashtbl.find_opt RDF_CottasStore_OnDiskIndex.Vav3_mmap.views opath with
        | None -> None
        | Some v ->
          let mv_data = v.RDF_CottasStore_OnDiskIndex.Vav3_mmap.mv_data in
          let mv_size = v.RDF_CottasStore_OnDiskIndex.Vav3_mmap.mv_size in
          if mv_size < header_size then begin
            Printf.eprintf "[lamed3-WARN] offsets file %s too small (%d bytes)\n%!" opath mv_size;
            None
          end else
            let g i = Stdlib.Char.code (Bigarray.Array1.unsafe_get mv_data i) in
            let read_u32 off =
              let b0 = g off in
              let b1 = g (off+1) in
              let b2 = g (off+2) in
              let b3 = g (off+3) in
              b0 lor (b1 lsl 8) lor (b2 lsl 16) lor (b3 lsl 24) in
            let magic = read_u32 0 in
            let ver   = read_u32 4 in
            if magic <> offsets_magic || ver <> layout_version then begin
              Printf.eprintf "[lamed3-WARN] offsets file %s bad magic/ver (0x%x ver=%d)\n%!"
                opath magic ver;
              None
            end else
              let num_rgs   = read_u32 8 in
              let num_preds = read_u32 12 in
              let index_off = header_size in
              let data_off  = index_off + 8 * (num_rgs * num_preds + 1) in
              let h = {
                ih_num_rgs = num_rgs;
                ih_num_preds = num_preds;
                ih_index_offset = index_off;
                ih_data_offset = data_off;
              } in
              Hashtbl.replace header_cache opath h;
              Printf.eprintf "[lamed3-trace] offsets reader: %s mapped (rgs=%d preds=%d data_off=%d total=%d)\n%!"
                opath num_rgs num_preds data_off mv_size;
              Some h

  (* Returns Some [|row_pos; ...|] (length 0 OK), or None if the file
     is absent / mismatched / out-of-range. The returned type is
     Stdlib's `int array`; we annotate with explicit `Stdlib.Array.t`
     because `open Prims` shadows `array`. *)
  let row_positions_for (cottas_path : string) (rg : pint) (pred_id : pint)
    : pint Stdlib.Array.t option =
    match read_header cottas_path with
    | None -> None
    | Some h ->
      if rg < 0 || rg >= h.ih_num_rgs || pred_id < 0 || pred_id >= h.ih_num_preds
      then None
      else
        let opath = offsets_path cottas_path in
        match Hashtbl.find_opt RDF_CottasStore_OnDiskIndex.Vav3_mmap.views opath with
        | None -> None
        | Some v ->
          let mv_data = v.RDF_CottasStore_OnDiskIndex.Vav3_mmap.mv_data in
          let g i = Stdlib.Char.code (Bigarray.Array1.unsafe_get mv_data i) in
          let read_u32 off =
            let b0 = g off in
            let b1 = g (off+1) in
            let b2 = g (off+2) in
            let b3 = g (off+3) in
            b0 lor (b1 lsl 8) lor (b2 lsl 16) lor (b3 lsl 24) in
          let read_u64 off =
            let lo = read_u32 off in
            let hi = read_u32 (off + 4) in
            lo lor (hi lsl 32) in
          let cell_idx = rg * h.ih_num_preds + pred_id in
          let start_off = read_u64 (h.ih_index_offset + 8 * cell_idx) in
          let end_off   = read_u64 (h.ih_index_offset + 8 * (cell_idx + 1)) in
          if end_off < start_off then None
          else
            let nbytes = end_off - start_off in
            let n = nbytes / 4 in
            let arr = Stdlib.Array.make n 0 in
            for i = 0 to n - 1 do
              Stdlib.Array.unsafe_set arr i (read_u32 (start_off + 4 * i))
            done;
            Some arr

  (* Build the offsets file if absent. Reads the predicate dict's
     tok_to_id mapping from the F* extracted reader (so id assignment
     matches the on-disk dict ordering). Called from boot (after Vav3
     companions are present). *)
  let ensure_offsets_built (cottas_path : string) : unit =
    let opath = offsets_path cottas_path in
    if Sys.file_exists opath && (try (Unix.stat opath).Unix.st_size with _ -> 0) >= header_size then begin
      Printf.eprintf "[lamed3-trace] offsets file present at %s, skipping build\n%!" opath
    end else begin
      Printf.eprintf "[lamed3-trace] offsets file absent; building\n%!";
      (* Read the predicate dict header to get num_predicates AND a
         tok_to_id Hashtbl built from the dict's ordering. We inline
         the path computation (Cottas_companion_writer.dict_path is
         forward-referenced from this module's earlier position). *)
      let dpath = cottas_path ^ ".p.dict" in
      match RDF_CottasStore_OnDiskIndex.read_dict_header dpath with
      | FStar_Pervasives_Native.None ->
        Printf.eprintf "[lamed3-FATAL] offsets-build: cannot read predicate dict header at %s\n%!" dpath
      | FStar_Pervasives_Native.Some dh ->
        let n_preds = Z.to_int dh.RDF_CottasStore_OnDiskIndex.dh_num_tokens in
        (* Read the predicate presence header to get num_rgs. *)
        let ppath = cottas_path ^ ".p.presence" in
        let n_rgs = match RDF_CottasStore_OnDiskIndex.read_presence_header ppath with
          | FStar_Pervasives_Native.Some ph ->
            Z.to_int ph.RDF_CottasStore_OnDiskIndex.ph_num_rgs
          | FStar_Pervasives_Native.None ->
            (match Parquet_Footer.probe_parquet_row_group_count cottas_path with
             | FStar_Pervasives_Native.None -> 0
             | FStar_Pervasives_Native.Some n -> Z.to_int n) in
        Printf.eprintf "[lamed3-trace] offsets-build: n_rgs=%d n_preds=%d\n%!" n_rgs n_preds;
        (* Build a tok_to_id Hashtbl by reading every dict entry. The
           dict was sorted ascending so id i corresponds to the i'th
           token in lex order; we use dict_decode_token to map. *)
        let tok_to_id : (string, pint) Hashtbl.t = Hashtbl.create (n_preds * 2 + 17) in
        for id = 0 to n_preds - 1 do
          match RDF_CottasStore_OnDiskIndex.dict_decode_token
                  dpath dh (Z.of_int id) with
          | FStar_Pervasives_Native.Some raw ->
            Hashtbl.replace tok_to_id raw id
          | FStar_Pervasives_Native.None ->
            Printf.eprintf "[lamed3-WARN] offsets-build: dict_decode_token failed for id=%d\n%!" id
        done;
        Printf.eprintf "[lamed3-trace] offsets-build: built tok_to_id (size=%d)\n%!"
          (Hashtbl.length tok_to_id);
        if n_rgs > 0 && n_preds > 0 && Hashtbl.length tok_to_id > 0 then
          build_offsets_file cottas_path tok_to_id n_rgs n_preds
        else
          Printf.eprintf "[lamed3-WARN] offsets-build: skipping (n_rgs=%d n_preds=%d tok_to_id=%d)\n%!"
            n_rgs n_preds (Hashtbl.length tok_to_id)
    end;
    (* Open mmap view for runtime reads. *)
    (match read_header cottas_path with
     | None ->
       Printf.eprintf "[lamed3-WARN] offsets-build: post-build read_header failed\n%!"
     | Some _ -> ())
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

  (* Issue #110 (2026-04-29): Pe4 instrumentation helpers
     (pe4_rss_mb / pe4_fd_count / pe4_gc_mb) deleted along with the
     search_fast / estimate_fast OCaml shim functions they served.
     The F* extracted bodies now drive the public API path; their
     tracing lives in the F* spec or the page-cache runtime. *)

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
            direction = FStar_Pervasives_Native.None;
          }
        else if String.length suffix >= 1 && suffix.[0] = '@' then
          Some {
            RDF_Graph_Executable.lexical_form = lexical;
            datatype = RDF_Graph_Executable.rdf_lang_string;
            lang_tag = FStar_Pervasives_Native.Some (String.sub suffix 1 (String.length suffix - 1));
            direction = FStar_Pervasives_Native.None;
          }
        else if String.length suffix >= 4 && String.sub suffix 0 2 = "^^" then
          (match parse_iri_token (String.sub suffix 2 (String.length suffix - 2)) with
           | Some dt ->
             Some {
               RDF_Graph_Executable.lexical_form = lexical;
               datatype = dt;
               lang_tag = FStar_Pervasives_Native.None;
               direction = FStar_Pervasives_Native.None;
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

  (* ---- Distinct-token collector. We walk the row groups ONE AT A
         TIME via the F* per-row-group decoder and dedupe into the
         dictionary as we go. Phase B drops the per-row int[] columns;
         we only need the distinct token list (indexed by id) + a
         raw-token-keyed revmap.

         In-memory bytes store stage 4 (docs/designissues/2026-07-06-
         inmemory-bytes-store.md, dictionary-cost lever): this used to
         call `probe_parquet_column_decode_all_row_groups`, which
         materializes the ENTIRE column as one `string option list`
         (888,949 cons+option+string cells on the gene corpus, tens of
         MB of transient allocation) before the dedupe loop ever ran --
         and that transient, not the resulting dictionary, dominated
         peak RSS for every `ensure_*_loaded` populate (measured:
         COUNT-star on gene peaked at 86 MB with the graph-column
         enumeration as the ONLY dictionary touch). Walking per row
         group via `probe_parquet_column_decode_in_row_group[_from_
         table]` (the same F*-verified decoders `probe_parquet_column_
         decode_all_row_groups` itself dispatches to, minus the
         whole-column concatenation) bounds the transient at one row
         group's cells. Same values, same order, same failure
         behaviour -- pure memory layout, rule #11 conformant; all
         decode logic stays in F*. *)

  (* Shared per-row-group walk. `on_cell` sees every cell (row order
     within each group, groups in index order), exactly as the old
     whole-column List.iter did. Returns the total row count. *)
  let iter_column_cells (label : string) (artifact_path : string) (col_idx : pint)
      (on_cell : string -> unit) : pint =
    let rg_count =
      match Parquet_Footer.probe_parquet_row_group_count artifact_path with
      | FStar_Pervasives_Native.Some n -> Z.to_int n
      | FStar_Pervasives_Native.None ->
        Printf.eprintf "[qof3-FATAL] %s: could not read row-group count\n%!" label;
        failwith (Printf.sprintf "COTTAS on-disk: could not read row-group count (column %d)" col_idx)
    in
    (* Build the row-group-offset table ONCE for the whole walk, same
       as probe_parquet_column_decode_all_row_groups does (issue
       #98/Mim3: avoids the O(rg^2) footer re-walk). *)
    let table = Parquet_Footer.probe_parquet_row_group_offset_table artifact_path in
    let row_count = ref 0 in
    for rg = 0 to rg_count - 1 do
      let decoded =
        match table with
        | FStar_Pervasives_Native.Some t ->
          Parquet_Footer.probe_parquet_column_decode_in_row_group_from_table
            t artifact_path (Z.of_int rg) (Z.of_int col_idx)
        | FStar_Pervasives_Native.None ->
          Parquet_Footer.probe_parquet_column_decode_in_row_group
            artifact_path (Z.of_int rg) (Z.of_int col_idx)
      in
      match decoded with
      | FStar_Pervasives_Native.None ->
        Printf.eprintf "[qof3-FATAL] %s: could not decode column %d row group %d\n%!" label col_idx rg;
        failwith (Printf.sprintf "COTTAS on-disk: could not decode column %d" col_idx)
      | FStar_Pervasives_Native.Some lst ->
        List.iter (function
          | FStar_Pervasives_Native.None ->
            Printf.eprintf "[qof3-FATAL] %s: missing cell in column %d\n%!" label col_idx;
            failwith (Printf.sprintf "COTTAS on-disk: missing cell in column %d" col_idx)
          | FStar_Pervasives_Native.Some r ->
            incr row_count;
            on_cell r) lst
    done;
    !row_count

  let collect_distinct (artifact_path : string) (col_idx : pint)
    : (string list * (string, pint) Hashtbl.t * pint) =
    Printf.eprintf "[qof3-trace] collect_distinct col=%d path=%s\n%!" col_idx artifact_path;
    let revmap : (string, pint) Hashtbl.t = Hashtbl.create 257 in
    let strs_rev = ref [] in
    let next_id = ref 0 in
    let row_count =
      iter_column_cells "collect_distinct" artifact_path col_idx
        (fun r ->
          if not (Hashtbl.mem revmap r) then begin
            Hashtbl.add revmap r !next_id;
            strs_rev := r :: !strs_rev;
            incr next_id
          end)
    in
    Printf.eprintf "[qof3-trace] collect_distinct col=%d distinct=%d rows=%d\n%!"
      col_idx !next_id row_count;
    (List.rev !strs_rev, revmap, row_count)

  (* Same shape as collect_distinct, but for the graph column: skip the
     "DEFAULT" sentinel so it never enters the dictionary. *)
  let collect_distinct_graph (artifact_path : string) (col_idx : pint)
    : (string list * (string, pint) Hashtbl.t * pint) =
    Printf.eprintf "[qof3-trace] collect_distinct_graph col=%d path=%s\n%!" col_idx artifact_path;
    let revmap : (string, pint) Hashtbl.t = Hashtbl.create 17 in
    let strs_rev = ref [] in
    let next_id = ref 0 in
    let row_count =
      iter_column_cells "collect_distinct_graph" artifact_path col_idx
        (fun r ->
          if r <> "DEFAULT" && not (Hashtbl.mem revmap r) then begin
            Hashtbl.add revmap r !next_id;
            strs_rev := r :: !strs_rev;
            incr next_id
          end)
    in
    Printf.eprintf "[qof3-trace] collect_distinct_graph col=%d named_graphs=%d rows=%d\n%!"
      col_idx !next_id row_count;
    (List.rev !strs_rev, revmap, row_count)

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
      let (s_strs, s_tok_to_id, _n) = collect_distinct h.coh_path 0 in
      (* Move s_tok_to_id contents into tables.ft_subj_tok_to_id.
         (We can't just reassign — the field is a fresh Hashtbl.) *)
      Hashtbl.iter (fun k v -> Hashtbl.replace tables.ft_subj_tok_to_id k v) s_tok_to_id;
      List.iteri (fun i raw ->
        match parse_subject_str raw with
        | Some s ->
          Hashtbl.replace tables.ft_id_to_subject  i s;
          Hashtbl.replace tables.ft_id_to_subj_tok i raw
        | None ->
          Printf.eprintf "[bet7-WARN] ensure_subjects_loaded: invalid subject token id=%d val=%s\n%!" i raw)
        s_strs;
      Cottas_ondisk_lazy.mark_subj_loaded h.coh_path;
      Gc.full_major ();
      Printf.eprintf "[bet7-trace] ensure_subjects_loaded: %d distinct subjects\n%!"
        (Hashtbl.length tables.ft_subj_tok_to_id)
    end

  let ensure_objects_loaded (h : cottas_ondisk_handle) (tables : fast_tables) : unit =
    if not (Cottas_ondisk_lazy.is_obj_loaded h.coh_path) then begin
      Printf.eprintf "[bet7-trace] ensure_objects_loaded: lazy populate path=%s\n%!" h.coh_path;
      let (o_strs, o_tok_to_id, _n) = collect_distinct h.coh_path 2 in
      Hashtbl.iter (fun k v -> Hashtbl.replace tables.ft_obj_tok_to_id k v) o_tok_to_id;
      List.iteri (fun i raw ->
        match parse_object_str raw with
        | Some o ->
          Hashtbl.replace tables.ft_id_to_object  i o;
          Hashtbl.replace tables.ft_id_to_obj_tok i raw
        | None ->
          Printf.eprintf "[bet7-WARN] ensure_objects_loaded: invalid object token id=%d val=%s\n%!" i raw)
        o_strs;
      Cottas_ondisk_lazy.mark_obj_loaded h.coh_path;
      Gc.full_major ();
      Printf.eprintf "[bet7-trace] ensure_objects_loaded: %d distinct objects\n%!"
        (Hashtbl.length tables.ft_obj_tok_to_id)
    end

  let ensure_predicates_loaded (h : cottas_ondisk_handle) (tables : fast_tables) : unit =
    if not (Cottas_ondisk_lazy.is_pred_loaded h.coh_path) then begin
      Printf.eprintf "[bet7-trace] ensure_predicates_loaded: lazy populate path=%s\n%!" h.coh_path;
      let (p_strs, p_tok_to_id, _n) = collect_distinct h.coh_path 1 in
      Hashtbl.iter (fun k v -> Hashtbl.replace tables.ft_pred_tok_to_id k v) p_tok_to_id;
      List.iteri (fun i raw ->
        match parse_iri_token raw with
        | Some iri ->
          Hashtbl.replace tables.ft_id_to_predicate i iri;
          Hashtbl.replace tables.ft_id_to_pred_tok  i raw
        | None ->
          Printf.eprintf "[bet7-WARN] ensure_predicates_loaded: invalid predicate token id=%d val=%s\n%!" i raw)
        p_strs;
      Cottas_ondisk_lazy.mark_pred_loaded h.coh_path;
      Gc.full_major ();
      Printf.eprintf "[bet7-trace] ensure_predicates_loaded: %d distinct predicates\n%!"
        (Hashtbl.length tables.ft_pred_tok_to_id)
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
      (* #254 Commit 2b registry wiring: snapshot the freshly-built
         eager dicts into the path-keyed LazyDictRegistry so the F*
         consumers can consult them via the typed boundary. The
         populate thunks here just return the already-computed data;
         a future commit upgrades them to true lazy parquet reads. *)
      (try
        let zip3 typed_list raw_list =
          let rec aux i ts rs = match ts, rs with
            | t :: trest, r :: rrest -> (Z.of_int i, t, r) :: aux (i+1) trest rrest
            | _, _ -> [] in
          aux 0 typed_list raw_list in
        let s_strs_snapshot = Hashtbl.fold (fun _ tok acc -> tok :: acc)
                                tables.ft_id_to_subj_tok [] in
        let p_strs_snapshot = Hashtbl.fold (fun _ tok acc -> tok :: acc)
                                tables.ft_id_to_pred_tok [] in
        let o_strs_snapshot = Hashtbl.fold (fun _ tok acc -> tok :: acc)
                                tables.ft_id_to_obj_tok [] in
        let g_strs_snapshot = Hashtbl.fold (fun _ tok acc -> tok :: acc)
                                tables.ft_id_to_graph_tok [] in
        RDF_CottasStore_LazyDictRegistry.register_for_path
          artifact_path
          (fun () -> zip3 h.coh_subjects   s_strs_snapshot)
          (fun () -> zip3 h.coh_predicates p_strs_snapshot)
          (fun () -> zip3 h.coh_objects    o_strs_snapshot)
          (fun () -> zip3 h.coh_graphs     g_strs_snapshot)
          subject_to_revmap_key
          iri_to_revmap_key
          object_to_revmap_key
          iri_to_revmap_key
      with _ ->
        Printf.eprintf "[bet7-trace] register_for_path failed (non-fatal)\\n%!");
      h

  let tables_for handle : fast_tables =
    match Hashtbl.find_opt fast_table_cache handle.coh_path with
    | Some t -> t
    | None ->
      (* Re-build (defensive: shouldn't happen if open() always populates). *)
      let (_h, tables) = build_handle_and_tables handle.coh_path in
      Hashtbl.add fast_table_cache handle.coh_path tables;
      tables

  (* Issue #110 (2026-04-29): retired. The Cottas_ondisk_runtime
     OCaml shims `search_fast`, `estimate_fast`, and
     `search_fast_limited` (plus their helpers `pe4_*`,
     `bound_id_to_token`, `cell_match_str`, `arr_of_col`,
     `cell_of`, `walk_rg`) used to live here. Phase 2.5e
     (commit 7cf9ebc) moved the public-API path to the F*-extracted
     `cottas_ondisk_search` / `_estimate` / `_search_limited`
     bodies, which decode through the F*-verified page cache via
     `pcache_decode_in_row_group_global` and resolve token->id via
     `ondisk_lookup_*_id_global`. The shim functions were dead on
     that path; the 9 retrofitting patches plus aleph6 and
     rename_inner_pivot have all been deleted in the same commit. *)
  (* Note: search_fast / estimate_fast / search_fast_limited are
     INTENTIONALLY ABSENT from this module. Do not add them back. *)

  let decode_subject_fast (h : cottas_ondisk_handle) (id : Prims.nat)
    : RDF_Graph_Executable.subject =
    let tables = tables_for h in
    match Hashtbl.find_opt tables.ft_id_to_subject (Z.to_int id) with
    | Some s -> s
    | None -> RDF_Graph_Executable.S_BNode "cottas_decode_oor"

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
    match Hashtbl.find_opt tables.ft_id_to_object (Z.to_int id) with
    | Some o -> o
    | None -> RDF_Graph_Executable.T_BNode "cottas_decode_oor"

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
      (* #261 fix: produce the N-Triples form via the F* serialiser
         (RDF.NQuads.Serialize.nq_term_to_string) and look up in the
         Bet7-populated Hashtbl. The literal column stores tokens in
         N-Triples form ("<lex>" / "<lex>"@lang / "<lex>"^^<<dt>>);
         the old fallback to revmap_lookup against coh_obj_revmap
         silently returned None on Bet7-lazy-opened handles because
         the assoc list is empty by design. Keeps the literal byte
         layout in F* per Iron Rule #11. *)
      let key = RDF_NQuads_Serialize.nq_term_to_string o in
      (match Hashtbl.find_opt tables.ft_obj_tok_to_id key with
       | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
       | None -> FStar_Pervasives_Native.None)

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
let cottas_ondisk_predicate_present (ds : cottas_ondisk_store)
  (pred : RDF_Term.wf_iri) : Prims.bool=
  Cottas_ondisk_runtime.predicate_present_fast ds.cods_handle pred

let rec named_graphs_aux (graphs : RDF_Term.iri Prims.list) (idx : Prims.nat)
  : (RDF_Term.iri * Parser_BallyhooCOTTAS.cottas_graph_ref) Prims.list=
  match graphs with
  | [] -> []
  | g::rest -> (g, idx) :: (named_graphs_aux rest (idx + Prims.int_one))
let cottas_ondisk_named_graphs (ds : cottas_ondisk_store) :
  (RDF_Term.iri * Parser_BallyhooCOTTAS.cottas_graph_ref)
    Prims.list=
  (* #261 fix part B: Bet7-lazy-opened handles defer coh_graphs.
     Trigger the OCaml-side populate, then read from ft_id_to_graph.
     The default-graph sentinel ("DEFAULT") is not a named graph and
     is excluded by ensure_graphs_loaded's id_to_graph population. *)
  let h = ds.cods_handle in
  let tables = Cottas_ondisk_runtime.tables_for h in
  Cottas_ondisk_runtime.ensure_graphs_loaded h tables;
  let acc = ref [] in
  Hashtbl.iter (fun id iri ->
    acc := (iri, Z.of_int id) :: !acc
  ) tables.Cottas_ondisk_runtime.ft_id_to_graph;
  !acc
let cottas_ondisk_version_ok (artifact_path : Prims.string) : Prims.bool=
  match Parquet_Footer.probe_parquet_file_metadata_version artifact_path with
  | FStar_Pervasives_Native.Some v ->
      v = Parquet_Footer.cottas_format_version
  | FStar_Pervasives_Native.None -> false
let cottas_ondisk_open (artifact_path : Prims.string) :
  cottas_ondisk_store FStar_Pervasives_Native.option=
  Printf.eprintf "[qof3-trace] cottas_ondisk_open path=%s\n%!" artifact_path;
  (* Issue #445, 2026-08-15: format-compatibility gate. cottas_ondisk_version_ok
     is F*-defined logic (RDF.CottasStore.fst, extracted into this same file --
     no qualifier needed), not new OCaml semantics; this call-out is exactly the
     "if ... then None else ..." rule #11 allows the glue side to be. Owner
     decision, verbatim: "Version-bump the COTTAS header - nobody is using our
     software yet except me... I can nuke and rebuild it" -- no migration path,
     no silent fallback to the pre-#445 (non-ASCII-corrupting) reader. *)
  if not (cottas_ondisk_version_ok artifact_path) then begin
    Printf.eprintf
      "cottas_ondisk_open: %s was not written by this store's current writer \
       (FileMetaData version mismatch) -- refusing to open. This is the \
       issue #445 format-compatibility gate: stores written before the \
       2026-08-15 UTF-8 fix had corrupted non-ASCII literals and are \
       rejected rather than silently misread. Re-run `factoidal import` on \
       the original source data to rebuild this store.\n%!"
      artifact_path;
    FStar_Pervasives_Native.None
  end else begin
    let h = Cottas_ondisk_runtime.load_handle artifact_path in
    Printf.eprintf "[qof3-trace] cottas_ondisk_open: handle ready\n%!";
    FStar_Pervasives_Native.Some {
      cods_artifact_path = artifact_path;
      cods_summary = h.coh_summary;
      cods_handle = h;
    }
  end
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
type cottas_token_tables =
  {
  ctt_id_to_subj_token:
    Prims.string -> Prims.nat -> Prims.string FStar_Pervasives_Native.option ;
  ctt_id_to_pred_token:
    Prims.string -> Prims.nat -> Prims.string FStar_Pervasives_Native.option ;
  ctt_id_to_obj_token:
    Prims.string -> Prims.nat -> Prims.string FStar_Pervasives_Native.option ;
  ctt_id_to_graph_token:
    Prims.string -> Prims.nat -> Prims.string FStar_Pervasives_Native.option ;
  ctt_lookup_subj_id:
    Prims.string -> Prims.string -> Prims.nat FStar_Pervasives_Native.option ;
  ctt_lookup_pred_id:
    Prims.string -> Prims.string -> Prims.nat FStar_Pervasives_Native.option ;
  ctt_lookup_obj_id:
    Prims.string -> Prims.string -> Prims.nat FStar_Pervasives_Native.option ;
  ctt_lookup_graph_id:
    Prims.string -> Prims.string -> Prims.nat FStar_Pervasives_Native.option }
let __proj__Mkcottas_token_tables__item__ctt_id_to_subj_token
  (projectee : cottas_token_tables) :
  Prims.string -> Prims.nat -> Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ctt_id_to_subj_token; ctt_id_to_pred_token; ctt_id_to_obj_token;
      ctt_id_to_graph_token; ctt_lookup_subj_id; ctt_lookup_pred_id;
      ctt_lookup_obj_id; ctt_lookup_graph_id;_} -> ctt_id_to_subj_token
let __proj__Mkcottas_token_tables__item__ctt_id_to_pred_token
  (projectee : cottas_token_tables) :
  Prims.string -> Prims.nat -> Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ctt_id_to_subj_token; ctt_id_to_pred_token; ctt_id_to_obj_token;
      ctt_id_to_graph_token; ctt_lookup_subj_id; ctt_lookup_pred_id;
      ctt_lookup_obj_id; ctt_lookup_graph_id;_} -> ctt_id_to_pred_token
let __proj__Mkcottas_token_tables__item__ctt_id_to_obj_token
  (projectee : cottas_token_tables) :
  Prims.string -> Prims.nat -> Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ctt_id_to_subj_token; ctt_id_to_pred_token; ctt_id_to_obj_token;
      ctt_id_to_graph_token; ctt_lookup_subj_id; ctt_lookup_pred_id;
      ctt_lookup_obj_id; ctt_lookup_graph_id;_} -> ctt_id_to_obj_token
let __proj__Mkcottas_token_tables__item__ctt_id_to_graph_token
  (projectee : cottas_token_tables) :
  Prims.string -> Prims.nat -> Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ctt_id_to_subj_token; ctt_id_to_pred_token; ctt_id_to_obj_token;
      ctt_id_to_graph_token; ctt_lookup_subj_id; ctt_lookup_pred_id;
      ctt_lookup_obj_id; ctt_lookup_graph_id;_} -> ctt_id_to_graph_token
let __proj__Mkcottas_token_tables__item__ctt_lookup_subj_id
  (projectee : cottas_token_tables) :
  Prims.string -> Prims.string -> Prims.nat FStar_Pervasives_Native.option=
  match projectee with
  | { ctt_id_to_subj_token; ctt_id_to_pred_token; ctt_id_to_obj_token;
      ctt_id_to_graph_token; ctt_lookup_subj_id; ctt_lookup_pred_id;
      ctt_lookup_obj_id; ctt_lookup_graph_id;_} -> ctt_lookup_subj_id
let __proj__Mkcottas_token_tables__item__ctt_lookup_pred_id
  (projectee : cottas_token_tables) :
  Prims.string -> Prims.string -> Prims.nat FStar_Pervasives_Native.option=
  match projectee with
  | { ctt_id_to_subj_token; ctt_id_to_pred_token; ctt_id_to_obj_token;
      ctt_id_to_graph_token; ctt_lookup_subj_id; ctt_lookup_pred_id;
      ctt_lookup_obj_id; ctt_lookup_graph_id;_} -> ctt_lookup_pred_id
let __proj__Mkcottas_token_tables__item__ctt_lookup_obj_id
  (projectee : cottas_token_tables) :
  Prims.string -> Prims.string -> Prims.nat FStar_Pervasives_Native.option=
  match projectee with
  | { ctt_id_to_subj_token; ctt_id_to_pred_token; ctt_id_to_obj_token;
      ctt_id_to_graph_token; ctt_lookup_subj_id; ctt_lookup_pred_id;
      ctt_lookup_obj_id; ctt_lookup_graph_id;_} -> ctt_lookup_obj_id
let __proj__Mkcottas_token_tables__item__ctt_lookup_graph_id
  (projectee : cottas_token_tables) :
  Prims.string -> Prims.string -> Prims.nat FStar_Pervasives_Native.option=
  match projectee with
  | { ctt_id_to_subj_token; ctt_id_to_pred_token; ctt_id_to_obj_token;
      ctt_id_to_graph_token; ctt_lookup_subj_id; ctt_lookup_pred_id;
      ctt_lookup_obj_id; ctt_lookup_graph_id;_} -> ctt_lookup_graph_id
let tables_of_handle (h : cottas_ondisk_handle) : cottas_token_tables=
  {
    ctt_id_to_subj_token = (fun uu___ i -> list_nth h.coh_subjects_raw i);
    ctt_id_to_pred_token = (fun uu___ i -> list_nth h.coh_predicates_raw i);
    ctt_id_to_obj_token = (fun uu___ i -> list_nth h.coh_objects_raw i);
    ctt_id_to_graph_token = (fun uu___ i -> list_nth h.coh_graphs_raw i);
    ctt_lookup_subj_id =
      (fun uu___ t -> revmap_lookup h.coh_subj_raw_revmap t);
    ctt_lookup_pred_id =
      (fun uu___ t -> revmap_lookup h.coh_pred_raw_revmap t);
    ctt_lookup_obj_id = (fun uu___ t -> revmap_lookup h.coh_obj_raw_revmap t);
    ctt_lookup_graph_id =
      (fun uu___ t -> revmap_lookup h.coh_graph_raw_revmap t)
  }
type ('tt, 'h) token_tables_agree_with = unit

(* Realisation of RDF.CottasStore.ondisk_token_tables_global: the
   deferred read of the four dictionary columns. Rule #11 dispatch
   shim over Cottas_ondisk_lazy's ensure_*_loaded + Hashtbl.find_opt.
   Its obligation is stated in F-star as
   `token_tables_agree_with (ondisk_token_tables_global h.coh_path) h`
   and consumed by `build_qp_row_agrees`.
   __TOKEN_LOOKUP_RUNTIME_APPLIED__ *)
module Cottas_token_lookup_global = struct
  let lookup_with_ensure
      (ensure : cottas_ondisk_handle -> Cottas_ondisk_runtime.fast_tables -> unit)
      (table_of : Cottas_ondisk_runtime.fast_tables -> (string, Stdlib.Int.t) Hashtbl.t)
      (path : Prims.string) (token : Prims.string)
    : Prims.nat FStar_Pervasives_Native.option =
    match Hashtbl.find_opt Cottas_ondisk_runtime.handles path with
    | None -> FStar_Pervasives_Native.None
    | Some h ->
      let tables = Cottas_ondisk_runtime.tables_for h in
      ensure h tables;
      (match Hashtbl.find_opt (table_of tables) token with
       | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
       | None   -> FStar_Pervasives_Native.None)

  (* Mirror of lookup_with_ensure for the id -> raw token direction. *)
  let id_to_token_with_ensure
      (ensure : cottas_ondisk_handle -> Cottas_ondisk_runtime.fast_tables -> unit)
      (table_of : Cottas_ondisk_runtime.fast_tables -> (Stdlib.Int.t, string) Hashtbl.t)
      (path : Prims.string) (id : Prims.nat)
    : Prims.string FStar_Pervasives_Native.option =
    match Hashtbl.find_opt Cottas_ondisk_runtime.handles path with
    | None -> FStar_Pervasives_Native.None
    | Some h ->
      let tables = Cottas_ondisk_runtime.tables_for h in
      ensure h tables;
      (match Hashtbl.find_opt (table_of tables) (Z.to_int id) with
       | Some s -> FStar_Pervasives_Native.Some s
       | None   -> FStar_Pervasives_Native.None)
end

(* One shared record. Every closure takes its path per call, so this
   value is path-independent and `build_qp_row` allocates nothing per
   matched row. *)
let cottas_global_token_tables : cottas_token_tables =
  {
    ctt_id_to_subj_token =
      Cottas_token_lookup_global.id_to_token_with_ensure
        Cottas_ondisk_runtime.ensure_subjects_loaded
        (fun t -> t.Cottas_ondisk_runtime.ft_id_to_subj_tok);
    ctt_id_to_pred_token =
      Cottas_token_lookup_global.id_to_token_with_ensure
        Cottas_ondisk_runtime.ensure_predicates_loaded
        (fun t -> t.Cottas_ondisk_runtime.ft_id_to_pred_tok);
    ctt_id_to_obj_token =
      Cottas_token_lookup_global.id_to_token_with_ensure
        Cottas_ondisk_runtime.ensure_objects_loaded
        (fun t -> t.Cottas_ondisk_runtime.ft_id_to_obj_tok);
    ctt_id_to_graph_token =
      Cottas_token_lookup_global.id_to_token_with_ensure
        Cottas_ondisk_runtime.ensure_graphs_loaded
        (fun t -> t.Cottas_ondisk_runtime.ft_id_to_graph_tok);
    ctt_lookup_subj_id =
      Cottas_token_lookup_global.lookup_with_ensure
        Cottas_ondisk_runtime.ensure_subjects_loaded
        (fun t -> t.Cottas_ondisk_runtime.ft_subj_tok_to_id);
    ctt_lookup_pred_id =
      Cottas_token_lookup_global.lookup_with_ensure
        Cottas_ondisk_runtime.ensure_predicates_loaded
        (fun t -> t.Cottas_ondisk_runtime.ft_pred_tok_to_id);
    ctt_lookup_obj_id =
      Cottas_token_lookup_global.lookup_with_ensure
        Cottas_ondisk_runtime.ensure_objects_loaded
        (fun t -> t.Cottas_ondisk_runtime.ft_obj_tok_to_id);
    ctt_lookup_graph_id =
      Cottas_token_lookup_global.lookup_with_ensure
        Cottas_ondisk_runtime.ensure_graphs_loaded
        (fun t -> t.Cottas_ondisk_runtime.ft_graph_tok_to_id);
  }

let ondisk_token_tables_global (_path : Prims.string)
  : cottas_token_tables =
  cottas_global_token_tables
type cottas_ondisk_graph_scope =
  | COS_DefaultOnly 
  | COS_NamedGraph of RDF_Term.iri 
let uu___is_COS_DefaultOnly (projectee : cottas_ondisk_graph_scope) :
  Prims.bool= match projectee with | COS_DefaultOnly -> true | uu___ -> false
let uu___is_COS_NamedGraph (projectee : cottas_ondisk_graph_scope) :
  Prims.bool=
  match projectee with | COS_NamedGraph _0 -> true | uu___ -> false
let __proj__COS_NamedGraph__item___0 (projectee : cottas_ondisk_graph_scope)
  : RDF_Term.iri= match projectee with | COS_NamedGraph _0 -> _0
let graph_bound_to_raw_token_with (tt : cottas_token_tables)
  (path : Prims.string) (gb : Parser_BallyhooCOTTAS.cottas_graph_bound) :
  Prims.string FStar_Pervasives_Native.option=
  match gb with
  | Parser_BallyhooCOTTAS.CGB_Unbound -> FStar_Pervasives_Native.None
  | Parser_BallyhooCOTTAS.CGB_Default ->
      FStar_Pervasives_Native.Some "DEFAULT"
  | Parser_BallyhooCOTTAS.CGB_Named r -> tt.ctt_id_to_graph_token path r
let graph_bound_to_raw_token (path : Prims.string)
  (gb : Parser_BallyhooCOTTAS.cottas_graph_bound) :
  Prims.string FStar_Pervasives_Native.option=
  graph_bound_to_raw_token_with (ondisk_token_tables_global path) path gb
let id_to_raw_token_via_global
  (lookup :
    Prims.string -> Prims.nat -> Prims.string FStar_Pervasives_Native.option)
  (path : Prims.string)
  (id : Parser_BallyhooCOTTAS.cottas_term_ref FStar_Pervasives_Native.option)
  : Prims.string FStar_Pervasives_Native.option=
  match id with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some i -> lookup path i
let build_qp_row_with (tt : cottas_token_tables) (h : cottas_ondisk_handle)
  (s_tok : Prims.string) (p_tok : Prims.string) (o_tok : Prims.string)
  (g_tok : Prims.string) : Parser_BallyhooCOTTAS.cottas_qp_row=
  let s_id = tt.ctt_lookup_subj_id h.coh_path s_tok in
  let p_id = tt.ctt_lookup_pred_id h.coh_path p_tok in
  let o_id = tt.ctt_lookup_obj_id h.coh_path o_tok in
  let g_id =
    if g_tok = "DEFAULT"
    then FStar_Pervasives_Native.None
    else tt.ctt_lookup_graph_id h.coh_path g_tok in
  {
    Parser_BallyhooCOTTAS.cqpr_s = s_id;
    Parser_BallyhooCOTTAS.cqpr_p = p_id;
    Parser_BallyhooCOTTAS.cqpr_o = o_id;
    Parser_BallyhooCOTTAS.cqpr_g = g_id
  }
let build_qp_row (h : cottas_ondisk_handle) (s_tok : Prims.string)
  (p_tok : Prims.string) (o_tok : Prims.string) (g_tok : Prims.string) :
  Parser_BallyhooCOTTAS.cottas_qp_row=
  build_qp_row_with (ondisk_token_tables_global h.coh_path) h s_tok p_tok
    o_tok g_tok
let cottas_decode_oor_predicate : RDF_Term.wf_iri=
  let fallback = "urn:factoidal:cottas-decode-predicate-unknown-id" in
  fallback
let token_to_subject (tok : Prims.string) : RDF_Term.subject=
  match Parser_NTriples.parse_subject tok Prims.int_zero with
  | Parser_Combinators.ParseOk (s, pos) ->
      if pos = (Parser_FastString.fs_byte_length tok)
      then s
      else RDF_Term.S_BNode "cottas_decode_oor"
  | Parser_Combinators.ParseFail (uu___, uu___1) ->
      RDF_Term.S_BNode "cottas_decode_oor"
let token_to_predicate (tok : Prims.string) : RDF_Term.wf_iri=
  match Parser_NTriples.parse_iri tok Prims.int_zero with
  | Parser_Combinators.ParseOk (p, pos) ->
      if pos = (Parser_FastString.fs_byte_length tok)
      then p
      else cottas_decode_oor_predicate
  | Parser_Combinators.ParseFail (uu___, uu___1) ->
      cottas_decode_oor_predicate
let token_to_object (tok : Prims.string) : RDF_Term.rdf_term=
  match Parser_NTriples.parse_object tok Prims.int_zero with
  | Parser_Combinators.ParseOk (o, pos) ->
      if pos = (Parser_FastString.fs_byte_length tok)
      then o
      else RDF_Term.T_BNode "cottas_decode_oor"
  | Parser_Combinators.ParseFail (uu___, uu___1) ->
      RDF_Term.T_BNode "cottas_decode_oor"
let token_to_graph_name (tok : Prims.string) : RDF_Term.iri=
  match Parser_NTriples.parse_iri tok Prims.int_zero with
  | Parser_Combinators.ParseOk (g, pos) ->
      if pos = (Parser_FastString.fs_byte_length tok) then g else ""
  | Parser_Combinators.ParseFail (uu___, uu___1) -> ""
let bound_subject_to_token (s : RDF_Term.subject) : Prims.string=
  RDF_NQuads_Serialize.nq_subject_to_string s
let bound_predicate_to_token (p : RDF_Term.wf_iri) : Prims.string=
  Prims.strcat "<" (Prims.strcat p ">")
let bound_object_to_token (o : RDF_Term.rdf_term) : Prims.string=
  RDF_NQuads_Serialize.nq_term_to_string o
let bound_graph_iri_to_token (g : RDF_Term.iri) : Prims.string=
  Prims.strcat "<" (Prims.strcat g ">")
type cottas_qp_row_tok =
  {
  cqprt_s: Prims.string ;
  cqprt_p: Prims.string ;
  cqprt_o: Prims.string ;
  cqprt_g: Prims.string }
let __proj__Mkcottas_qp_row_tok__item__cqprt_s
  (projectee : cottas_qp_row_tok) : Prims.string=
  match projectee with | { cqprt_s; cqprt_p; cqprt_o; cqprt_g;_} -> cqprt_s
let __proj__Mkcottas_qp_row_tok__item__cqprt_p
  (projectee : cottas_qp_row_tok) : Prims.string=
  match projectee with | { cqprt_s; cqprt_p; cqprt_o; cqprt_g;_} -> cqprt_p
let __proj__Mkcottas_qp_row_tok__item__cqprt_o
  (projectee : cottas_qp_row_tok) : Prims.string=
  match projectee with | { cqprt_s; cqprt_p; cqprt_o; cqprt_g;_} -> cqprt_o
let __proj__Mkcottas_qp_row_tok__item__cqprt_g
  (projectee : cottas_qp_row_tok) : Prims.string=
  match projectee with | { cqprt_s; cqprt_p; cqprt_o; cqprt_g;_} -> cqprt_g
let build_qp_row_tok (s_tok : Prims.string) (p_tok : Prims.string)
  (o_tok : Prims.string) (g_tok : Prims.string) : cottas_qp_row_tok=
  { cqprt_s = s_tok; cqprt_p = p_tok; cqprt_o = o_tok; cqprt_g = g_tok }
let nat_min (a : Prims.nat) (b : Prims.nat) : Prims.nat=
  if a <= b then a else b
let row_group_row_count (s_col : RDF_CottasStore_ColumnSeq.cottas_column)
  (p_col : RDF_CottasStore_ColumnSeq.cottas_column)
  (o_col : RDF_CottasStore_ColumnSeq.cottas_column)
  (g_col : RDF_CottasStore_ColumnSeq.cottas_column) : Prims.nat=
  let n_s = RDF_CottasStore_ColumnSeq.cottas_column_length s_col in
  let n_p = RDF_CottasStore_ColumnSeq.cottas_column_length p_col in
  let n_o = RDF_CottasStore_ColumnSeq.cottas_column_length o_col in
  let n_g = RDF_CottasStore_ColumnSeq.cottas_column_length g_col in
  nat_min (nat_min n_s n_p) (nat_min n_o n_g)
let rec filter_zipped_rows_seq (h : cottas_ondisk_handle)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (s_col : RDF_CottasStore_ColumnSeq.cottas_column)
  (p_col : RDF_CottasStore_ColumnSeq.cottas_column)
  (o_col : RDF_CottasStore_ColumnSeq.cottas_column)
  (g_col : RDF_CottasStore_ColumnSeq.cottas_column) (n : Prims.nat)
  (i : Prims.nat) (acc_rev : Parser_BallyhooCOTTAS.cottas_qp_row Prims.list)
  : Parser_BallyhooCOTTAS.cottas_qp_row Prims.list=
  if i = n
  then acc_rev
  else
    (let acc_rev' =
       if
         (((i < (RDF_CottasStore_ColumnSeq.cottas_column_length s_col)) &&
             (i < (RDF_CottasStore_ColumnSeq.cottas_column_length p_col)))
            && (i < (RDF_CottasStore_ColumnSeq.cottas_column_length o_col)))
           && (i < (RDF_CottasStore_ColumnSeq.cottas_column_length g_col))
       then
         match ((RDF_CottasStore_ColumnSeq.cottas_column_get s_col i),
                 (RDF_CottasStore_ColumnSeq.cottas_column_get p_col i),
                 (RDF_CottasStore_ColumnSeq.cottas_column_get o_col i),
                 (RDF_CottasStore_ColumnSeq.cottas_column_get g_col i))
         with
         | (FStar_Pervasives_Native.Some s_tok, FStar_Pervasives_Native.Some
            p_tok, FStar_Pervasives_Native.Some o_tok,
            FStar_Pervasives_Native.Some g_tok) ->
             (if
                (((cell_match bound_s s_tok) && (cell_match bound_p p_tok))
                   && (cell_match bound_o o_tok))
                  && (graph_cell_match bound_g g_tok)
              then (build_qp_row h s_tok p_tok o_tok g_tok) :: acc_rev
              else acc_rev)
         | uu___1 -> acc_rev
       else acc_rev in
     filter_zipped_rows_seq h bound_s bound_p bound_o bound_g s_col p_col
       o_col g_col n (i + Prims.int_one) acc_rev')
let rec filter_zipped_rows_tok_seq
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (s_col : RDF_CottasStore_ColumnSeq.cottas_column)
  (p_col : RDF_CottasStore_ColumnSeq.cottas_column)
  (o_col : RDF_CottasStore_ColumnSeq.cottas_column)
  (g_col : RDF_CottasStore_ColumnSeq.cottas_column) (n : Prims.nat)
  (i : Prims.nat) (acc_rev : cottas_qp_row_tok Prims.list) :
  cottas_qp_row_tok Prims.list=
  if i = n
  then acc_rev
  else
    (let acc_rev' =
       if
         (((i < (RDF_CottasStore_ColumnSeq.cottas_column_length s_col)) &&
             (i < (RDF_CottasStore_ColumnSeq.cottas_column_length p_col)))
            && (i < (RDF_CottasStore_ColumnSeq.cottas_column_length o_col)))
           && (i < (RDF_CottasStore_ColumnSeq.cottas_column_length g_col))
       then
         match ((RDF_CottasStore_ColumnSeq.cottas_column_get s_col i),
                 (RDF_CottasStore_ColumnSeq.cottas_column_get p_col i),
                 (RDF_CottasStore_ColumnSeq.cottas_column_get o_col i),
                 (RDF_CottasStore_ColumnSeq.cottas_column_get g_col i))
         with
         | (FStar_Pervasives_Native.Some s_tok, FStar_Pervasives_Native.Some
            p_tok, FStar_Pervasives_Native.Some o_tok,
            FStar_Pervasives_Native.Some g_tok) ->
             (if
                (((cell_match bound_s s_tok) && (cell_match bound_p p_tok))
                   && (cell_match bound_o o_tok))
                  && (graph_cell_match bound_g g_tok)
              then (build_qp_row_tok s_tok p_tok o_tok g_tok) :: acc_rev
              else acc_rev)
         | uu___1 -> acc_rev
       else acc_rev in
     filter_zipped_rows_tok_seq bound_s bound_p bound_o bound_g s_col p_col
       o_col g_col n (i + Prims.int_one) acc_rev')
let rec count_zipped_rows_seq
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (s_col : RDF_CottasStore_ColumnSeq.cottas_column)
  (p_col : RDF_CottasStore_ColumnSeq.cottas_column)
  (o_col : RDF_CottasStore_ColumnSeq.cottas_column)
  (g_col : RDF_CottasStore_ColumnSeq.cottas_column) (n : Prims.nat)
  (i : Prims.nat) (acc : Prims.nat) : Prims.nat=
  if i = n
  then acc
  else
    (let acc' =
       if
         (((i < (RDF_CottasStore_ColumnSeq.cottas_column_length s_col)) &&
             (i < (RDF_CottasStore_ColumnSeq.cottas_column_length p_col)))
            && (i < (RDF_CottasStore_ColumnSeq.cottas_column_length o_col)))
           && (i < (RDF_CottasStore_ColumnSeq.cottas_column_length g_col))
       then
         match ((RDF_CottasStore_ColumnSeq.cottas_column_get s_col i),
                 (RDF_CottasStore_ColumnSeq.cottas_column_get p_col i),
                 (RDF_CottasStore_ColumnSeq.cottas_column_get o_col i),
                 (RDF_CottasStore_ColumnSeq.cottas_column_get g_col i))
         with
         | (FStar_Pervasives_Native.Some s_tok, FStar_Pervasives_Native.Some
            p_tok, FStar_Pervasives_Native.Some o_tok,
            FStar_Pervasives_Native.Some g_tok) ->
             (if
                (((cell_match bound_s s_tok) && (cell_match bound_p p_tok))
                   && (cell_match bound_o o_tok))
                  && (graph_cell_match bound_g g_tok)
              then acc + Prims.int_one
              else acc)
         | uu___1 -> acc
       else acc in
     count_zipped_rows_seq bound_s bound_p bound_o bound_g s_col p_col o_col
       g_col n (i + Prims.int_one) acc')
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
                                let n = row_group_row_count sc pc oc gc in
                                filter_zipped_rows_seq h bound_s bound_p
                                  bound_o bound_g sc pc oc gc n
                                  Prims.int_zero acc_rev
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
                                let n = row_group_row_count sc pc oc gc in
                                count_zipped_rows_seq bound_s bound_p bound_o
                                  bound_g sc pc oc gc n Prims.int_zero acc
                            | uu___6 -> acc in
                          walk_row_groups_estimate h bound_s bound_p bound_o
                            bound_g (rg_index + Prims.int_one) rg_count
                            (fuel - Prims.int_one) acc' c4))))
let pcache_decode_global_auto
  (table :
    Parquet_Footer.parquet_row_group_offset_table
      FStar_Pervasives_Native.option)
  (path : Prims.string) (rg_index : Prims.nat) (col_index : Prims.nat) :
  RDF_CottasStore_ColumnSeq.cottas_column FStar_Pervasives_Native.option=
  match table with
  | FStar_Pervasives_Native.Some t ->
      RDF_CottasStore_PageCache.pcache_decode_in_row_group_global_from_table
        t path rg_index col_index
  | FStar_Pervasives_Native.None ->
      RDF_CottasStore_PageCache.pcache_decode_in_row_group_global path
        rg_index col_index
let rec walk_row_groups_search_global (h : cottas_ondisk_handle)
  (table :
    Parquet_Footer.parquet_row_group_offset_table
      FStar_Pervasives_Native.option)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (rg_index : Prims.nat) (rg_count : Prims.nat) (fuel : Prims.nat)
  (acc_rev : Parser_BallyhooCOTTAS.cottas_qp_row Prims.list) :
  Parser_BallyhooCOTTAS.cottas_qp_row Prims.list=
  if fuel = Prims.int_zero
  then acc_rev
  else
    if rg_index >= rg_count
    then acc_rev
    else
      (let s_col =
         pcache_decode_global_auto table h.coh_path rg_index Prims.int_zero in
       let p_col =
         pcache_decode_global_auto table h.coh_path rg_index Prims.int_one in
       let o_col =
         pcache_decode_global_auto table h.coh_path rg_index
           (Prims.of_int (2)) in
       let g_col =
         pcache_decode_global_auto table h.coh_path rg_index
           (Prims.of_int (3)) in
       let acc_rev' =
         match (s_col, p_col, o_col, g_col) with
         | (FStar_Pervasives_Native.Some sc, FStar_Pervasives_Native.Some pc,
            FStar_Pervasives_Native.Some oc, FStar_Pervasives_Native.Some gc)
             ->
             let n = row_group_row_count sc pc oc gc in
             filter_zipped_rows_seq h bound_s bound_p bound_o bound_g sc pc
               oc gc n Prims.int_zero acc_rev
         | uu___2 -> acc_rev in
       walk_row_groups_search_global h table bound_s bound_p bound_o bound_g
         (rg_index + Prims.int_one) rg_count (fuel - Prims.int_one) acc_rev')
let rec walk_row_groups_search_tok_global (path : Prims.string)
  (table :
    Parquet_Footer.parquet_row_group_offset_table
      FStar_Pervasives_Native.option)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (rg_index : Prims.nat) (rg_count : Prims.nat) (fuel : Prims.nat)
  (acc_rev : cottas_qp_row_tok Prims.list) : cottas_qp_row_tok Prims.list=
  if fuel = Prims.int_zero
  then acc_rev
  else
    if rg_index >= rg_count
    then acc_rev
    else
      (let s_col =
         pcache_decode_global_auto table path rg_index Prims.int_zero in
       let p_col =
         pcache_decode_global_auto table path rg_index Prims.int_one in
       let o_col =
         pcache_decode_global_auto table path rg_index (Prims.of_int (2)) in
       let g_col =
         pcache_decode_global_auto table path rg_index (Prims.of_int (3)) in
       let acc_rev' =
         match (s_col, p_col, o_col, g_col) with
         | (FStar_Pervasives_Native.Some sc, FStar_Pervasives_Native.Some pc,
            FStar_Pervasives_Native.Some oc, FStar_Pervasives_Native.Some gc)
             ->
             let n = row_group_row_count sc pc oc gc in
             filter_zipped_rows_tok_seq bound_s bound_p bound_o bound_g sc pc
               oc gc n Prims.int_zero acc_rev
         | uu___2 -> acc_rev in
       walk_row_groups_search_tok_global path table bound_s bound_p bound_o
         bound_g (rg_index + Prims.int_one) rg_count (fuel - Prims.int_one)
         acc_rev')
let rec walk_row_groups_estimate_global (h : cottas_ondisk_handle)
  (table :
    Parquet_Footer.parquet_row_group_offset_table
      FStar_Pervasives_Native.option)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (rg_index : Prims.nat) (rg_count : Prims.nat) (fuel : Prims.nat)
  (acc : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then acc
  else
    if rg_index >= rg_count
    then acc
    else
      (let s_col =
         pcache_decode_global_auto table h.coh_path rg_index Prims.int_zero in
       let p_col =
         pcache_decode_global_auto table h.coh_path rg_index Prims.int_one in
       let o_col =
         pcache_decode_global_auto table h.coh_path rg_index
           (Prims.of_int (2)) in
       let g_col =
         pcache_decode_global_auto table h.coh_path rg_index
           (Prims.of_int (3)) in
       let acc' =
         match (s_col, p_col, o_col, g_col) with
         | (FStar_Pervasives_Native.Some sc, FStar_Pervasives_Native.Some pc,
            FStar_Pervasives_Native.Some oc, FStar_Pervasives_Native.Some gc)
             ->
             let n = row_group_row_count sc pc oc gc in
             count_zipped_rows_seq bound_s bound_p bound_o bound_g sc pc oc
               gc n Prims.int_zero acc
         | uu___2 -> acc in
       walk_row_groups_estimate_global h table bound_s bound_p bound_o
         bound_g (rg_index + Prims.int_one) rg_count (fuel - Prims.int_one)
         acc')
let rec count_graph_col_matches_seq
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (g_col : RDF_CottasStore_ColumnSeq.cottas_column) (n : Prims.nat)
  (i : Prims.nat) (acc : Prims.nat) : Prims.nat=
  if i = n
  then acc
  else
    (let acc' =
       if i < (RDF_CottasStore_ColumnSeq.cottas_column_length g_col)
       then
         match RDF_CottasStore_ColumnSeq.cottas_column_get g_col i with
         | FStar_Pervasives_Native.Some g_tok ->
             (if graph_cell_match bound_g g_tok
              then acc + Prims.int_one
              else acc)
         | FStar_Pervasives_Native.None -> acc
       else acc in
     count_graph_col_matches_seq bound_g g_col n (i + Prims.int_one) acc')
let rec walk_row_groups_count_graph_global (h : cottas_ondisk_handle)
  (table :
    Parquet_Footer.parquet_row_group_offset_table
      FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (rg_index : Prims.nat) (rg_count : Prims.nat) (fuel : Prims.nat)
  (acc : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then acc
  else
    if rg_index >= rg_count
    then acc
    else
      (let acc' =
         match pcache_decode_global_auto table h.coh_path rg_index
                 (Prims.of_int (3))
         with
         | FStar_Pervasives_Native.Some gc ->
             count_graph_col_matches_seq bound_g gc
               (RDF_CottasStore_ColumnSeq.cottas_column_length gc)
               Prims.int_zero acc
         | FStar_Pervasives_Native.None -> acc in
       walk_row_groups_count_graph_global h table bound_g
         (rg_index + Prims.int_one) rg_count (fuel - Prims.int_one) acc')
let bound_col_match (bound : Prims.string FStar_Pervasives_Native.option)
  (col_opt :
    RDF_CottasStore_ColumnSeq.cottas_column FStar_Pervasives_Native.option)
  (i : Prims.nat) : Prims.bool=
  match bound with
  | FStar_Pervasives_Native.None -> true
  | FStar_Pervasives_Native.Some expected ->
      (match col_opt with
       | FStar_Pervasives_Native.None -> false
       | FStar_Pervasives_Native.Some col ->
           if i < (RDF_CottasStore_ColumnSeq.cottas_column_length col)
           then
             (match RDF_CottasStore_ColumnSeq.cottas_column_get col i with
              | FStar_Pervasives_Native.Some tok -> tok = expected
              | FStar_Pervasives_Native.None -> false)
           else false)
let rec count_selective_matches_seq
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (s_col :
    RDF_CottasStore_ColumnSeq.cottas_column FStar_Pervasives_Native.option)
  (p_col :
    RDF_CottasStore_ColumnSeq.cottas_column FStar_Pervasives_Native.option)
  (o_col :
    RDF_CottasStore_ColumnSeq.cottas_column FStar_Pervasives_Native.option)
  (g_col : RDF_CottasStore_ColumnSeq.cottas_column) (n : Prims.nat)
  (i : Prims.nat) (acc : Prims.nat) : Prims.nat=
  if i = n
  then acc
  else
    (let acc' =
       if i < (RDF_CottasStore_ColumnSeq.cottas_column_length g_col)
       then
         match RDF_CottasStore_ColumnSeq.cottas_column_get g_col i with
         | FStar_Pervasives_Native.Some g_tok ->
             (if
                (((bound_col_match bound_s s_col i) &&
                    (bound_col_match bound_p p_col i))
                   && (bound_col_match bound_o o_col i))
                  && (graph_cell_match bound_g g_tok)
              then acc + Prims.int_one
              else acc)
         | FStar_Pervasives_Native.None -> acc
       else acc in
     count_selective_matches_seq bound_s bound_p bound_o bound_g s_col p_col
       o_col g_col n (i + Prims.int_one) acc')
let rec walk_row_groups_count_exact_global (h : cottas_ondisk_handle)
  (table :
    Parquet_Footer.parquet_row_group_offset_table
      FStar_Pervasives_Native.option)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (rg_index : Prims.nat) (rg_count : Prims.nat) (fuel : Prims.nat)
  (acc : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then acc
  else
    if rg_index >= rg_count
    then acc
    else
      (let acc' =
         match pcache_decode_global_auto table h.coh_path rg_index
                 (Prims.of_int (3))
         with
         | FStar_Pervasives_Native.None -> acc
         | FStar_Pervasives_Native.Some g_col ->
             let s_col =
               if FStar_Pervasives_Native.uu___is_Some bound_s
               then
                 pcache_decode_global_auto table h.coh_path rg_index
                   Prims.int_zero
               else FStar_Pervasives_Native.None in
             let p_col =
               if FStar_Pervasives_Native.uu___is_Some bound_p
               then
                 pcache_decode_global_auto table h.coh_path rg_index
                   Prims.int_one
               else FStar_Pervasives_Native.None in
             let o_col =
               if FStar_Pervasives_Native.uu___is_Some bound_o
               then
                 pcache_decode_global_auto table h.coh_path rg_index
                   (Prims.of_int (2))
               else FStar_Pervasives_Native.None in
             let needed_ok =
               (((FStar_Pervasives_Native.uu___is_None bound_s) ||
                   (FStar_Pervasives_Native.uu___is_Some s_col))
                  &&
                  ((FStar_Pervasives_Native.uu___is_None bound_p) ||
                     (FStar_Pervasives_Native.uu___is_Some p_col)))
                 &&
                 ((FStar_Pervasives_Native.uu___is_None bound_o) ||
                    (FStar_Pervasives_Native.uu___is_Some o_col)) in
             if needed_ok
             then
               count_selective_matches_seq bound_s bound_p bound_o bound_g
                 s_col p_col o_col g_col
                 (RDF_CottasStore_ColumnSeq.cottas_column_length g_col)
                 Prims.int_zero acc
             else acc in
       walk_row_groups_count_exact_global h table bound_s bound_p bound_o
         bound_g (rg_index + Prims.int_one) rg_count (fuel - Prims.int_one)
         acc')
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
let rec union_dedupe_strings_acc (acc : Prims.string Prims.list)
  (new_entries : Prims.string Prims.list) : Prims.string Prims.list=
  match new_entries with
  | [] -> acc
  | hd::tl ->
      if list_string_mem acc hd
      then union_dedupe_strings_acc acc tl
      else union_dedupe_strings_acc (hd :: acc) tl
let rec collect_distinct_column_tokens_rgs (path : Prims.string)
  (table :
    Parquet_Footer.parquet_row_group_offset_table
      FStar_Pervasives_Native.option)
  (col_index : Prims.nat) (rg_index : Prims.nat) (rg_count : Prims.nat)
  (fuel : Prims.nat) (acc : Prims.string Prims.list) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.Some acc
  else
    if rg_index >= rg_count
    then FStar_Pervasives_Native.Some acc
    else
      (let dict_opt =
         match table with
         | FStar_Pervasives_Native.Some t ->
             Parquet_Footer.probe_parquet_column_dictionary_in_row_group_from_table
               t path rg_index col_index
         | FStar_Pervasives_Native.None ->
             Parquet_Footer.probe_parquet_column_dictionary_in_row_group path
               rg_index col_index in
       match dict_opt with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some entries ->
           let acc' = union_dedupe_strings_acc acc entries in
           collect_distinct_column_tokens_rgs path table col_index
             (rg_index + Prims.int_one) rg_count (fuel - Prims.int_one) acc')
let cottas_ondisk_distinct_predicates (ds : cottas_ondisk_store) :
  RDF_Term.wf_iri Prims.list FStar_Pervasives_Native.option=
  let h = ds.cods_handle in
  match Parquet_Footer.probe_parquet_row_group_count h.coh_path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some rg_count ->
      let table =
        Parquet_Footer.probe_parquet_row_group_offset_table h.coh_path in
      (match collect_distinct_column_tokens_rgs h.coh_path table
               Prims.int_one Prims.int_zero rg_count rg_count []
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some toks ->
           FStar_Pervasives_Native.Some
             (FStar_List_Tot_Base.map token_to_predicate toks))
let rec populate_dict_cache_loop (c : dict_cache)
  (table :
    Parquet_Footer.parquet_row_group_offset_table
      FStar_Pervasives_Native.option)
  (path : Prims.string) (col_index : Prims.nat) (rg_index : Prims.nat)
  (rg_count : Prims.nat) (fuel : Prims.nat) : dict_cache=
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
             let dict_opt =
               match table with
               | FStar_Pervasives_Native.Some t ->
                   RDF_CottasStore_PageCache.dpcache_probe_dict_in_row_group_global_from_table
                     t path rg_index col_index
               | FStar_Pervasives_Native.None ->
                   Parquet_Footer.probe_parquet_column_dictionary_in_row_group
                     path rg_index col_index in
             (match dict_opt with
              | FStar_Pervasives_Native.None -> c
              | FStar_Pervasives_Native.Some dict ->
                  ((rg_index, col_index), dict) :: c) in
       populate_dict_cache_loop c' table path col_index
         (rg_index + Prims.int_one) rg_count (fuel - Prims.int_one))
let populate_dict_cache_for_column (c : dict_cache)
  (table :
    Parquet_Footer.parquet_row_group_offset_table
      FStar_Pervasives_Native.option)
  (path : Prims.string) (col_index : Prims.nat) (rg_count : Prims.nat) :
  dict_cache=
  populate_dict_cache_loop c table path col_index Prims.int_zero rg_count
    rg_count
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
                                let n = row_group_row_count sc pc oc gc in
                                filter_zipped_rows_seq h bound_s bound_p
                                  bound_o bound_g sc pc oc gc n
                                  Prims.int_zero acc_rev
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
                                let n = row_group_row_count sc pc oc gc in
                                count_zipped_rows_seq bound_s bound_p bound_o
                                  bound_g sc pc oc gc n Prims.int_zero acc
                            | uu___4 -> acc in
                          walk_candidate_rgs_estimate h bound_s bound_p
                            bound_o bound_g rest acc' c4))))
let rec walk_candidate_rgs_search_global (h : cottas_ondisk_handle)
  (table :
    Parquet_Footer.parquet_row_group_offset_table
      FStar_Pervasives_Native.option)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (candidates : Prims.nat Prims.list)
  (acc_rev : Parser_BallyhooCOTTAS.cottas_qp_row Prims.list) :
  Parser_BallyhooCOTTAS.cottas_qp_row Prims.list=
  match candidates with
  | [] -> acc_rev
  | rg_index::rest ->
      let s_col =
        pcache_decode_global_auto table h.coh_path rg_index Prims.int_zero in
      let p_col =
        pcache_decode_global_auto table h.coh_path rg_index Prims.int_one in
      let o_col =
        pcache_decode_global_auto table h.coh_path rg_index
          (Prims.of_int (2)) in
      let g_col =
        pcache_decode_global_auto table h.coh_path rg_index
          (Prims.of_int (3)) in
      let acc_rev' =
        match (s_col, p_col, o_col, g_col) with
        | (FStar_Pervasives_Native.Some sc, FStar_Pervasives_Native.Some pc,
           FStar_Pervasives_Native.Some oc, FStar_Pervasives_Native.Some gc)
            ->
            let n = row_group_row_count sc pc oc gc in
            filter_zipped_rows_seq h bound_s bound_p bound_o bound_g sc pc oc
              gc n Prims.int_zero acc_rev
        | uu___ -> acc_rev in
      walk_candidate_rgs_search_global h table bound_s bound_p bound_o
        bound_g rest acc_rev'
let rec walk_candidate_rgs_search_tok_global (path : Prims.string)
  (table :
    Parquet_Footer.parquet_row_group_offset_table
      FStar_Pervasives_Native.option)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (candidates : Prims.nat Prims.list)
  (acc_rev : cottas_qp_row_tok Prims.list) : cottas_qp_row_tok Prims.list=
  match candidates with
  | [] -> acc_rev
  | rg_index::rest ->
      let s_col =
        pcache_decode_global_auto table path rg_index Prims.int_zero in
      let p_col = pcache_decode_global_auto table path rg_index Prims.int_one in
      let o_col =
        pcache_decode_global_auto table path rg_index (Prims.of_int (2)) in
      let g_col =
        pcache_decode_global_auto table path rg_index (Prims.of_int (3)) in
      let acc_rev' =
        match (s_col, p_col, o_col, g_col) with
        | (FStar_Pervasives_Native.Some sc, FStar_Pervasives_Native.Some pc,
           FStar_Pervasives_Native.Some oc, FStar_Pervasives_Native.Some gc)
            ->
            let n = row_group_row_count sc pc oc gc in
            filter_zipped_rows_tok_seq bound_s bound_p bound_o bound_g sc pc
              oc gc n Prims.int_zero acc_rev
        | uu___ -> acc_rev in
      walk_candidate_rgs_search_tok_global path table bound_s bound_p bound_o
        bound_g rest acc_rev'
let rec walk_candidate_rgs_estimate_global (h : cottas_ondisk_handle)
  (table :
    Parquet_Footer.parquet_row_group_offset_table
      FStar_Pervasives_Native.option)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (candidates : Prims.nat Prims.list) (acc : Prims.nat) : Prims.nat=
  match candidates with
  | [] -> acc
  | rg_index::rest ->
      let s_col =
        pcache_decode_global_auto table h.coh_path rg_index Prims.int_zero in
      let p_col =
        pcache_decode_global_auto table h.coh_path rg_index Prims.int_one in
      let o_col =
        pcache_decode_global_auto table h.coh_path rg_index
          (Prims.of_int (2)) in
      let g_col =
        pcache_decode_global_auto table h.coh_path rg_index
          (Prims.of_int (3)) in
      let acc' =
        match (s_col, p_col, o_col, g_col) with
        | (FStar_Pervasives_Native.Some sc, FStar_Pervasives_Native.Some pc,
           FStar_Pervasives_Native.Some oc, FStar_Pervasives_Native.Some gc)
            ->
            let n = row_group_row_count sc pc oc gc in
            count_zipped_rows_seq bound_s bound_p bound_o bound_g sc pc oc gc
              n Prims.int_zero acc
        | uu___ -> acc in
      walk_candidate_rgs_estimate_global h table bound_s bound_p bound_o
        bound_g rest acc'
let candidates_for_one_bound (c : dict_cache)
  (table :
    Parquet_Footer.parquet_row_group_offset_table
      FStar_Pervasives_Native.option)
  (path : Prims.string) (col_index : Prims.nat) (bound_token : Prims.string)
  (rg_count : Prims.nat) : (Prims.nat Prims.list * dict_cache)=
  let c' = populate_dict_cache_for_column c table path col_index rg_count in
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
  (table :
    Parquet_Footer.parquet_row_group_offset_table
      FStar_Pervasives_Native.option)
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
               candidates_for_one_bound c table path col_index tok rg_count in
             (match uu___1 with
              | (cands, c') ->
                  let combined = intersect_sorted_rg_lists cur cands in
                  (combined, c', true))) in
  let st1 = step init Prims.int_zero bound_s in
  let st2 = step st1 Prims.int_one bound_p in
  let st3 = step st2 (Prims.of_int (2)) bound_o in
  let st4 = step st3 (Prims.of_int (3)) bound_g in
  let uu___ = st4 in match uu___ with | (final, c, uu___1) -> (final, c)
let compound_po_dict_encode (path : Prims.string) (col_suffix : Prims.string)
  (tok : Prims.string) : Prims.nat FStar_Pervasives_Native.option=
  let dict_path =
    Prims.strcat path (Prims.strcat "." (Prims.strcat col_suffix ".dict")) in
  match RDF_CottasStore_OnDiskIndex.read_dict_header dict_path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some dh ->
      if Prims.op_Negation (RDF_CottasStore_OnDiskIndex.dict_header_ok dh)
      then FStar_Pervasives_Native.None
      else RDF_CottasStore_OnDiskIndex.dict_encode_token dict_path dh tok
let filter_candidates_by_compound_po (path : Prims.string)
  (candidates : Prims.nat Prims.list)
  (bound_p_str : Prims.string FStar_Pervasives_Native.option)
  (bound_o_str : Prims.string FStar_Pervasives_Native.option) :
  Prims.nat Prims.list=
  match (bound_p_str, bound_o_str) with
  | (FStar_Pervasives_Native.Some bp, FStar_Pervasives_Native.Some bo) ->
      let p_id = compound_po_dict_encode path "p" bp in
      let o_id = compound_po_dict_encode path "o" bo in
      (match (p_id, o_id) with
       | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.Some
          uu___1) ->
           let oh =
             RDF_CottasStore_CompoundPresenceBitmap.open_compound
               (Prims.strcat path ".po.presence") in
           (match oh with
            | FStar_Pervasives_Native.None -> candidates
            | FStar_Pervasives_Native.Some uu___2 ->
                FStar_List_Tot_Base.filter
                  (fun rg ->
                     RDF_CottasStore_CompoundPresenceBitmap.compound_rg_passes_pair
                       oh rg p_id o_id) candidates)
       | uu___ -> candidates)
  | uu___ -> candidates
let rec subject_range_candidate_rgs_loop
  (table : Parquet_Footer.parquet_row_group_offset_table)
  (target_start : Prims.nat) (target_end : Prims.nat) (rg_index : Prims.nat)
  (rg_count : Prims.nat) (fuel : Prims.nat) (cum_start : Prims.nat)
  (acc_rev : Prims.nat Prims.list) :
  Prims.nat Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.Some (Parquet_Footer.list_rev acc_rev)
  else
    if rg_index >= rg_count
    then FStar_Pervasives_Native.Some (Parquet_Footer.list_rev acc_rev)
    else
      (match Parquet_Footer.probe_parquet_row_group_num_rows_from_table table
               rg_index
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some rg_rows ->
           let cum_end = cum_start + rg_rows in
           let acc_rev' =
             if (target_start < cum_end) && (cum_start < target_end)
             then rg_index :: acc_rev
             else acc_rev in
           subject_range_candidate_rgs_loop table target_start target_end
             (rg_index + Prims.int_one) rg_count (fuel - Prims.int_one)
             cum_end acc_rev')
let cottas_ondisk_subject_candidate_rgs (h : cottas_ondisk_handle)
  (table :
    Parquet_Footer.parquet_row_group_offset_table
      FStar_Pervasives_Native.option)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (rg_count : Prims.nat) :
  Prims.nat Prims.list FStar_Pervasives_Native.option=
  match bound_s with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some s ->
      let s_dict_path = Prims.strcat h.coh_path ".s.dict" in
      (match RDF_CottasStore_OnDiskIndex.read_dict_header s_dict_path with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some dh ->
           if
             Prims.op_Negation
               (RDF_CottasStore_OnDiskIndex.dict_header_ok dh)
           then FStar_Pervasives_Native.None
           else
             (match RDF_CottasStore_OnDiskIndex.dict_encode_token s_dict_path
                      dh s
              with
              | FStar_Pervasives_Native.None ->
                  FStar_Pervasives_Native.Some []
              | FStar_Pervasives_Native.Some subj_id ->
                  (match RDF_Store_Columnar_SubjectOffsetIndex.open_subject_offsets
                           (RDF_Store_Columnar_SubjectOffsetIndex.subject_offsets_path_of
                              h.coh_path)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some oh ->
                       if
                         Prims.op_Negation
                           (RDF_Store_Columnar_SubjectOffsetIndex.subject_offset_handle_ok
                              oh)
                       then FStar_Pervasives_Native.None
                       else
                         (match RDF_Store_Columnar_SubjectOffsetIndex.range_for_subject
                                  oh subj_id
                          with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some r ->
                              if
                                (RDF_Store_Columnar_SubjectOffsetIndex.subject_range_count
                                   r)
                                  = Prims.int_zero
                              then FStar_Pervasives_Native.Some []
                              else
                                (match table with
                                 | FStar_Pervasives_Native.None ->
                                     FStar_Pervasives_Native.None
                                 | FStar_Pervasives_Native.Some t ->
                                     subject_range_candidate_rgs_loop t
                                       r.RDF_Store_Columnar_SubjectOffsetIndex.sr_start
                                       r.RDF_Store_Columnar_SubjectOffsetIndex.sr_end
                                       Prims.int_zero rg_count rg_count
                                       Prims.int_zero [])))))
let cottas_ondisk_has_decode_failure (h : cottas_ondisk_handle) : Prims.bool=
  (((FStar_Pervasives_Native.uu___is_None
       (Parquet_Footer.probe_parquet_column_decode_all_row_groups h.coh_path
          Prims.int_zero))
      ||
      (FStar_Pervasives_Native.uu___is_None
         (Parquet_Footer.probe_parquet_column_decode_all_row_groups
            h.coh_path Prims.int_one)))
     ||
     (FStar_Pervasives_Native.uu___is_None
        (Parquet_Footer.probe_parquet_column_decode_all_row_groups h.coh_path
           (Prims.of_int (2)))))
    ||
    (FStar_Pervasives_Native.uu___is_None
       (Parquet_Footer.probe_parquet_column_decode_all_row_groups h.coh_path
          (Prims.of_int (3))))
type cottas_bound_qp_tok =
  {
  cbqpt_s: Prims.string FStar_Pervasives_Native.option ;
  cbqpt_p: Prims.string FStar_Pervasives_Native.option ;
  cbqpt_o: Prims.string FStar_Pervasives_Native.option ;
  cbqpt_g: Prims.string FStar_Pervasives_Native.option }
let __proj__Mkcottas_bound_qp_tok__item__cbqpt_s
  (projectee : cottas_bound_qp_tok) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | { cbqpt_s; cbqpt_p; cbqpt_o; cbqpt_g;_} -> cbqpt_s
let __proj__Mkcottas_bound_qp_tok__item__cbqpt_p
  (projectee : cottas_bound_qp_tok) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | { cbqpt_s; cbqpt_p; cbqpt_o; cbqpt_g;_} -> cbqpt_p
let __proj__Mkcottas_bound_qp_tok__item__cbqpt_o
  (projectee : cottas_bound_qp_tok) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | { cbqpt_s; cbqpt_p; cbqpt_o; cbqpt_g;_} -> cbqpt_o
let __proj__Mkcottas_bound_qp_tok__item__cbqpt_g
  (projectee : cottas_bound_qp_tok) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | { cbqpt_s; cbqpt_p; cbqpt_o; cbqpt_g;_} -> cbqpt_g
let cottas_ondisk_build_bound_qp_tok
  (s : RDF_Term.subject FStar_Pervasives_Native.option)
  (p : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (o : RDF_Term.rdf_term FStar_Pervasives_Native.option)
  (scope : cottas_ondisk_graph_scope) : cottas_bound_qp_tok=
  {
    cbqpt_s =
      (match s with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some sv ->
           FStar_Pervasives_Native.Some (bound_subject_to_token sv));
    cbqpt_p =
      (match p with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some pv ->
           FStar_Pervasives_Native.Some (bound_predicate_to_token pv));
    cbqpt_o =
      (match o with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ov ->
           FStar_Pervasives_Native.Some (bound_object_to_token ov));
    cbqpt_g =
      (match scope with
       | COS_DefaultOnly -> FStar_Pervasives_Native.Some "DEFAULT"
       | COS_NamedGraph gv ->
           FStar_Pervasives_Native.Some (bound_graph_iri_to_token gv))
  }
let cottas_ondisk_search_tok (ds : cottas_ondisk_store)
  (bound : cottas_bound_qp_tok) : cottas_qp_row_tok Prims.list=
  let h = ds.cods_handle in
  let bound_s = bound.cbqpt_s in
  let bound_p = bound.cbqpt_p in
  let bound_o = bound.cbqpt_o in
  let bound_g = bound.cbqpt_g in
  match Parquet_Footer.probe_parquet_row_group_count h.coh_path with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some rg_count ->
      let table =
        Parquet_Footer.probe_parquet_row_group_offset_table h.coh_path in
      let any_bound_present =
        (((FStar_Pervasives_Native.uu___is_Some bound_s) ||
            (FStar_Pervasives_Native.uu___is_Some bound_p))
           || (FStar_Pervasives_Native.uu___is_Some bound_o))
          || (FStar_Pervasives_Native.uu___is_Some bound_g) in
      if any_bound_present
      then
        let uu___ =
          plan_candidate_rgs h table bound_s bound_p bound_o bound_g rg_count in
        (match uu___ with
         | (candidates0, _dc) ->
             let candidates1 =
               match cottas_ondisk_subject_candidate_rgs h table bound_s
                       rg_count
               with
               | FStar_Pervasives_Native.None -> candidates0
               | FStar_Pervasives_Native.Some subj_rgs ->
                   intersect_sorted_rg_lists candidates0 subj_rgs in
             let candidates =
               filter_candidates_by_compound_po h.coh_path candidates1
                 bound_p bound_o in
             let acc_rev =
               walk_candidate_rgs_search_tok_global h.coh_path table bound_s
                 bound_p bound_o bound_g candidates [] in
             Parquet_Footer.list_rev acc_rev)
      else
        (let acc_rev =
           walk_row_groups_search_tok_global h.coh_path table bound_s bound_p
             bound_o bound_g Prims.int_zero rg_count rg_count [] in
         Parquet_Footer.list_rev acc_rev)
type cottas_qp_row_tok_selective =
  {
  rst_s: Prims.string FStar_Pervasives_Native.option ;
  rst_p: Prims.string FStar_Pervasives_Native.option ;
  rst_o: Prims.string FStar_Pervasives_Native.option ;
  rst_g: Prims.string }
let __proj__Mkcottas_qp_row_tok_selective__item__rst_s
  (projectee : cottas_qp_row_tok_selective) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | { rst_s; rst_p; rst_o; rst_g;_} -> rst_s
let __proj__Mkcottas_qp_row_tok_selective__item__rst_p
  (projectee : cottas_qp_row_tok_selective) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | { rst_s; rst_p; rst_o; rst_g;_} -> rst_p
let __proj__Mkcottas_qp_row_tok_selective__item__rst_o
  (projectee : cottas_qp_row_tok_selective) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | { rst_s; rst_p; rst_o; rst_g;_} -> rst_o
let __proj__Mkcottas_qp_row_tok_selective__item__rst_g
  (projectee : cottas_qp_row_tok_selective) : Prims.string=
  match projectee with | { rst_s; rst_p; rst_o; rst_g;_} -> rst_g
let rec matched_indices_seq
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (s_col :
    RDF_CottasStore_ColumnSeq.cottas_column FStar_Pervasives_Native.option)
  (p_col :
    RDF_CottasStore_ColumnSeq.cottas_column FStar_Pervasives_Native.option)
  (o_col :
    RDF_CottasStore_ColumnSeq.cottas_column FStar_Pervasives_Native.option)
  (g_col : RDF_CottasStore_ColumnSeq.cottas_column) (n : Prims.nat)
  (i : Prims.nat) (acc_rev : Prims.nat Prims.list) : Prims.nat Prims.list=
  if i = n
  then acc_rev
  else
    (let acc_rev' =
       if i < (RDF_CottasStore_ColumnSeq.cottas_column_length g_col)
       then
         match RDF_CottasStore_ColumnSeq.cottas_column_get g_col i with
         | FStar_Pervasives_Native.Some g_tok ->
             (if
                (((bound_col_match bound_s s_col i) &&
                    (bound_col_match bound_p p_col i))
                   && (bound_col_match bound_o o_col i))
                  && (graph_cell_match bound_g g_tok)
              then i :: acc_rev
              else acc_rev)
         | FStar_Pervasives_Native.None -> acc_rev
       else acc_rev in
     matched_indices_seq bound_s bound_p bound_o bound_g s_col p_col o_col
       g_col n (i + Prims.int_one) acc_rev')
let rec filter_column_by_indices_acc
  (col : RDF_CottasStore_ColumnSeq.cottas_column)
  (indices : Prims.nat Prims.list)
  (acc_rev : (Prims.nat * Prims.string) Prims.list) :
  (Prims.nat * Prims.string) Prims.list=
  match indices with
  | [] -> acc_rev
  | i::rest ->
      let acc_rev' =
        if i < (RDF_CottasStore_ColumnSeq.cottas_column_length col)
        then
          match RDF_CottasStore_ColumnSeq.cottas_column_get col i with
          | FStar_Pervasives_Native.Some tok -> (i, tok) :: acc_rev
          | FStar_Pervasives_Native.None -> acc_rev
        else acc_rev in
      filter_column_by_indices_acc col rest acc_rev'
let filter_column_by_indices (col : RDF_CottasStore_ColumnSeq.cottas_column)
  (indices : Prims.nat Prims.list) : (Prims.nat * Prims.string) Prims.list=
  FStar_List_Tot_Base.rev (filter_column_by_indices_acc col indices [])
let decode_indexed_or_fallback
  (table :
    Parquet_Footer.parquet_row_group_offset_table
      FStar_Pervasives_Native.option)
  (path : Prims.string) (rg_index : Prims.nat) (col_index : Prims.nat)
  (indices : Prims.nat Prims.list) : (Prims.nat * Prims.string) Prims.list=
  match table with
  | FStar_Pervasives_Native.Some t ->
      (match RDF_CottasStore_PageCache.pcache_decode_column_at_indices_global_from_table
               t path rg_index col_index indices
       with
       | FStar_Pervasives_Native.Some pairs -> pairs
       | FStar_Pervasives_Native.None -> [])
  | FStar_Pervasives_Native.None ->
      (match RDF_CottasStore_PageCache.pcache_decode_in_row_group_global path
               rg_index col_index
       with
       | FStar_Pervasives_Native.None -> []
       | FStar_Pervasives_Native.Some col ->
           filter_column_by_indices col indices)
let rec vals_advance (vals : (Prims.nat * Prims.string) Prims.list)
  (i : Prims.nat) :
  (Prims.string FStar_Pervasives_Native.option * (Prims.nat * Prims.string)
    Prims.list)=
  match vals with
  | [] -> (FStar_Pervasives_Native.None, [])
  | (k, v)::rest ->
      if k = i
      then ((FStar_Pervasives_Native.Some v), rest)
      else
        if k < i
        then vals_advance rest i
        else (FStar_Pervasives_Native.None, vals)
let rec build_selective_rows
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (need : RDF_Graph_Executable.col_need)
  (s_vals : (Prims.nat * Prims.string) Prims.list)
  (p_vals : (Prims.nat * Prims.string) Prims.list)
  (o_vals : (Prims.nat * Prims.string) Prims.list)
  (g_col : RDF_CottasStore_ColumnSeq.cottas_column)
  (indices : Prims.nat Prims.list)
  (acc_rev : cottas_qp_row_tok_selective Prims.list) :
  cottas_qp_row_tok_selective Prims.list=
  match indices with
  | [] -> acc_rev
  | i::rest ->
      let uu___ =
        if FStar_Pervasives_Native.uu___is_Some bound_s
        then (bound_s, s_vals)
        else
          if need.RDF_Graph_Executable.cn_s
          then vals_advance s_vals i
          else (FStar_Pervasives_Native.None, s_vals) in
      (match uu___ with
       | (sv, s_vals2) ->
           let uu___1 =
             if FStar_Pervasives_Native.uu___is_Some bound_p
             then (bound_p, p_vals)
             else
               if need.RDF_Graph_Executable.cn_p
               then vals_advance p_vals i
               else (FStar_Pervasives_Native.None, p_vals) in
           (match uu___1 with
            | (pv, p_vals2) ->
                let uu___2 =
                  if FStar_Pervasives_Native.uu___is_Some bound_o
                  then (bound_o, o_vals)
                  else
                    if need.RDF_Graph_Executable.cn_o
                    then vals_advance o_vals i
                    else (FStar_Pervasives_Native.None, o_vals) in
                (match uu___2 with
                 | (ov, o_vals2) ->
                     let rst_g =
                       if
                         i <
                           (RDF_CottasStore_ColumnSeq.cottas_column_length
                              g_col)
                       then
                         match RDF_CottasStore_ColumnSeq.cottas_column_get
                                 g_col i
                         with
                         | FStar_Pervasives_Native.Some g -> g
                         | FStar_Pervasives_Native.None -> ""
                       else "" in
                     let row = { rst_s = sv; rst_p = pv; rst_o = ov; rst_g } in
                     build_selective_rows bound_s bound_p bound_o need
                       s_vals2 p_vals2 o_vals2 g_col rest (row :: acc_rev))))
let process_row_group_selective (path : Prims.string)
  (table :
    Parquet_Footer.parquet_row_group_offset_table
      FStar_Pervasives_Native.option)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (need : RDF_Graph_Executable.col_need) (rg_index : Prims.nat)
  (acc_rev : cottas_qp_row_tok_selective Prims.list) :
  cottas_qp_row_tok_selective Prims.list=
  match pcache_decode_global_auto table path rg_index (Prims.of_int (3)) with
  | FStar_Pervasives_Native.None -> acc_rev
  | FStar_Pervasives_Native.Some g_col ->
      let s_col =
        if FStar_Pervasives_Native.uu___is_Some bound_s
        then pcache_decode_global_auto table path rg_index Prims.int_zero
        else FStar_Pervasives_Native.None in
      let p_col =
        if FStar_Pervasives_Native.uu___is_Some bound_p
        then pcache_decode_global_auto table path rg_index Prims.int_one
        else FStar_Pervasives_Native.None in
      let o_col =
        if FStar_Pervasives_Native.uu___is_Some bound_o
        then pcache_decode_global_auto table path rg_index (Prims.of_int (2))
        else FStar_Pervasives_Native.None in
      let bound_decode_ok =
        (((FStar_Pervasives_Native.uu___is_None bound_s) ||
            (FStar_Pervasives_Native.uu___is_Some s_col))
           &&
           ((FStar_Pervasives_Native.uu___is_None bound_p) ||
              (FStar_Pervasives_Native.uu___is_Some p_col)))
          &&
          ((FStar_Pervasives_Native.uu___is_None bound_o) ||
             (FStar_Pervasives_Native.uu___is_Some o_col)) in
      if Prims.op_Negation bound_decode_ok
      then acc_rev
      else
        (let n = RDF_CottasStore_ColumnSeq.cottas_column_length g_col in
         let matched =
           FStar_List_Tot_Base.rev
             (matched_indices_seq bound_s bound_p bound_o bound_g s_col p_col
                o_col g_col n Prims.int_zero []) in
         let s_vals =
           if
             (FStar_Pervasives_Native.uu___is_None bound_s) &&
               need.RDF_Graph_Executable.cn_s
           then
             decode_indexed_or_fallback table path rg_index Prims.int_zero
               matched
           else [] in
         let p_vals =
           if
             (FStar_Pervasives_Native.uu___is_None bound_p) &&
               need.RDF_Graph_Executable.cn_p
           then
             decode_indexed_or_fallback table path rg_index Prims.int_one
               matched
           else [] in
         let o_vals =
           if
             (FStar_Pervasives_Native.uu___is_None bound_o) &&
               need.RDF_Graph_Executable.cn_o
           then
             decode_indexed_or_fallback table path rg_index
               (Prims.of_int (2)) matched
           else [] in
         build_selective_rows bound_s bound_p bound_o need s_vals p_vals
           o_vals g_col matched acc_rev)
let rec walk_row_groups_search_tok_selective_global (path : Prims.string)
  (table :
    Parquet_Footer.parquet_row_group_offset_table
      FStar_Pervasives_Native.option)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (need : RDF_Graph_Executable.col_need) (rg_index : Prims.nat)
  (rg_count : Prims.nat) (fuel : Prims.nat)
  (acc_rev : cottas_qp_row_tok_selective Prims.list) :
  cottas_qp_row_tok_selective Prims.list=
  if fuel = Prims.int_zero
  then acc_rev
  else
    if rg_index >= rg_count
    then acc_rev
    else
      (let acc_rev' =
         process_row_group_selective path table bound_s bound_p bound_o
           bound_g need rg_index acc_rev in
       walk_row_groups_search_tok_selective_global path table bound_s bound_p
         bound_o bound_g need (rg_index + Prims.int_one) rg_count
         (fuel - Prims.int_one) acc_rev')
let rec walk_candidate_rgs_search_tok_selective_global (path : Prims.string)
  (table :
    Parquet_Footer.parquet_row_group_offset_table
      FStar_Pervasives_Native.option)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (need : RDF_Graph_Executable.col_need) (candidates : Prims.nat Prims.list)
  (acc_rev : cottas_qp_row_tok_selective Prims.list) :
  cottas_qp_row_tok_selective Prims.list=
  match candidates with
  | [] -> acc_rev
  | rg_index::rest ->
      let acc_rev' =
        process_row_group_selective path table bound_s bound_p bound_o
          bound_g need rg_index acc_rev in
      walk_candidate_rgs_search_tok_selective_global path table bound_s
        bound_p bound_o bound_g need rest acc_rev'
let cottas_ondisk_search_tok_selective (ds : cottas_ondisk_store)
  (bound : cottas_bound_qp_tok) (need : RDF_Graph_Executable.col_need) :
  cottas_qp_row_tok_selective Prims.list=
  let h = ds.cods_handle in
  let bound_s = bound.cbqpt_s in
  let bound_p = bound.cbqpt_p in
  let bound_o = bound.cbqpt_o in
  let bound_g = bound.cbqpt_g in
  match Parquet_Footer.probe_parquet_row_group_count h.coh_path with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some rg_count ->
      let table =
        Parquet_Footer.probe_parquet_row_group_offset_table h.coh_path in
      let any_bound_present =
        (((FStar_Pervasives_Native.uu___is_Some bound_s) ||
            (FStar_Pervasives_Native.uu___is_Some bound_p))
           || (FStar_Pervasives_Native.uu___is_Some bound_o))
          || (FStar_Pervasives_Native.uu___is_Some bound_g) in
      if any_bound_present
      then
        let uu___ =
          plan_candidate_rgs h table bound_s bound_p bound_o bound_g rg_count in
        (match uu___ with
         | (candidates0, _dc) ->
             let candidates =
               filter_candidates_by_compound_po h.coh_path candidates0
                 bound_p bound_o in
             let acc_rev =
               walk_candidate_rgs_search_tok_selective_global h.coh_path
                 table bound_s bound_p bound_o bound_g need candidates [] in
             Parquet_Footer.list_rev acc_rev)
      else
        (let acc_rev =
           walk_row_groups_search_tok_selective_global h.coh_path table
             bound_s bound_p bound_o bound_g need Prims.int_zero rg_count
             rg_count [] in
         Parquet_Footer.list_rev acc_rev)
let cottas_ondisk_row_tok_selective_to_triple
  (row : cottas_qp_row_tok_selective) : RDF_Triple.triple=
  {
    RDF_Triple.s =
      (match row.rst_s with
       | FStar_Pervasives_Native.Some tok -> token_to_subject tok
       | FStar_Pervasives_Native.None -> RDF_Term.S_BNode "cottas_decode_oor");
    RDF_Triple.p =
      (match row.rst_p with
       | FStar_Pervasives_Native.Some tok -> token_to_predicate tok
       | FStar_Pervasives_Native.None -> cottas_decode_oor_predicate);
    RDF_Triple.o =
      (match row.rst_o with
       | FStar_Pervasives_Native.Some tok -> token_to_object tok
       | FStar_Pervasives_Native.None -> RDF_Term.T_BNode "cottas_decode_oor")
  }
let rec cottas_ondisk_rows_tok_selective_to_triples_acc
  (rows : cottas_qp_row_tok_selective Prims.list)
  (acc : RDF_Triple.triple Prims.list) : RDF_Triple.triple Prims.list=
  match rows with
  | [] -> acc
  | row::rest ->
      cottas_ondisk_rows_tok_selective_to_triples_acc rest
        ((cottas_ondisk_row_tok_selective_to_triple row) :: acc)
let cottas_ondisk_rows_tok_selective_to_triples
  (rows : cottas_qp_row_tok_selective Prims.list) :
  RDF_Triple.triple Prims.list=
  FStar_List_Tot_Base.rev
    (cottas_ondisk_rows_tok_selective_to_triples_acc rows [])
let rec filter_zipped_rows_limited_seq (h : cottas_ondisk_handle)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (s_col : RDF_CottasStore_ColumnSeq.cottas_column)
  (p_col : RDF_CottasStore_ColumnSeq.cottas_column)
  (o_col : RDF_CottasStore_ColumnSeq.cottas_column)
  (g_col : RDF_CottasStore_ColumnSeq.cottas_column) (n : Prims.nat)
  (i : Prims.nat) (acc_rev : Parser_BallyhooCOTTAS.cottas_qp_row Prims.list)
  (acc_count : Prims.nat) (limit : Prims.nat) :
  (Parser_BallyhooCOTTAS.cottas_qp_row Prims.list * Prims.nat * Prims.bool)=
  if acc_count >= limit
  then (acc_rev, acc_count, true)
  else
    if i = n
    then (acc_rev, acc_count, (acc_count >= limit))
    else
      (let uu___2 =
         if
           (((i < (RDF_CottasStore_ColumnSeq.cottas_column_length s_col)) &&
               (i < (RDF_CottasStore_ColumnSeq.cottas_column_length p_col)))
              && (i < (RDF_CottasStore_ColumnSeq.cottas_column_length o_col)))
             && (i < (RDF_CottasStore_ColumnSeq.cottas_column_length g_col))
         then
           match ((RDF_CottasStore_ColumnSeq.cottas_column_get s_col i),
                   (RDF_CottasStore_ColumnSeq.cottas_column_get p_col i),
                   (RDF_CottasStore_ColumnSeq.cottas_column_get o_col i),
                   (RDF_CottasStore_ColumnSeq.cottas_column_get g_col i))
           with
           | (FStar_Pervasives_Native.Some s_tok,
              FStar_Pervasives_Native.Some p_tok,
              FStar_Pervasives_Native.Some o_tok,
              FStar_Pervasives_Native.Some g_tok) ->
               (if
                  (((cell_match bound_s s_tok) && (cell_match bound_p p_tok))
                     && (cell_match bound_o o_tok))
                    && (graph_cell_match bound_g g_tok)
                then
                  (((build_qp_row h s_tok p_tok o_tok g_tok) :: acc_rev),
                    (acc_count + Prims.int_one))
                else (acc_rev, acc_count))
           | uu___3 -> (acc_rev, acc_count)
         else (acc_rev, acc_count) in
       match uu___2 with
       | (acc_rev', acc_count') ->
           filter_zipped_rows_limited_seq h bound_s bound_p bound_o bound_g
             s_col p_col o_col g_col n (i + Prims.int_one) acc_rev'
             acc_count' limit)
let rec filter_zipped_rows_limited_tok_seq
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (s_col : RDF_CottasStore_ColumnSeq.cottas_column)
  (p_col : RDF_CottasStore_ColumnSeq.cottas_column)
  (o_col : RDF_CottasStore_ColumnSeq.cottas_column)
  (g_col : RDF_CottasStore_ColumnSeq.cottas_column) (n : Prims.nat)
  (i : Prims.nat) (acc_rev : cottas_qp_row_tok Prims.list)
  (acc_count : Prims.nat) (limit : Prims.nat) :
  (cottas_qp_row_tok Prims.list * Prims.nat * Prims.bool)=
  if acc_count >= limit
  then (acc_rev, acc_count, true)
  else
    if i = n
    then (acc_rev, acc_count, (acc_count >= limit))
    else
      (let uu___2 =
         if
           (((i < (RDF_CottasStore_ColumnSeq.cottas_column_length s_col)) &&
               (i < (RDF_CottasStore_ColumnSeq.cottas_column_length p_col)))
              && (i < (RDF_CottasStore_ColumnSeq.cottas_column_length o_col)))
             && (i < (RDF_CottasStore_ColumnSeq.cottas_column_length g_col))
         then
           match ((RDF_CottasStore_ColumnSeq.cottas_column_get s_col i),
                   (RDF_CottasStore_ColumnSeq.cottas_column_get p_col i),
                   (RDF_CottasStore_ColumnSeq.cottas_column_get o_col i),
                   (RDF_CottasStore_ColumnSeq.cottas_column_get g_col i))
           with
           | (FStar_Pervasives_Native.Some s_tok,
              FStar_Pervasives_Native.Some p_tok,
              FStar_Pervasives_Native.Some o_tok,
              FStar_Pervasives_Native.Some g_tok) ->
               (if
                  (((cell_match bound_s s_tok) && (cell_match bound_p p_tok))
                     && (cell_match bound_o o_tok))
                    && (graph_cell_match bound_g g_tok)
                then
                  (((build_qp_row_tok s_tok p_tok o_tok g_tok) :: acc_rev),
                    (acc_count + Prims.int_one))
                else (acc_rev, acc_count))
           | uu___3 -> (acc_rev, acc_count)
         else (acc_rev, acc_count) in
       match uu___2 with
       | (acc_rev', acc_count') ->
           filter_zipped_rows_limited_tok_seq bound_s bound_p bound_o bound_g
             s_col p_col o_col g_col n (i + Prims.int_one) acc_rev'
             acc_count' limit)
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
                                  let n = row_group_row_count sc pc oc gc in
                                  filter_zipped_rows_limited_seq h bound_s
                                    bound_p bound_o bound_g sc pc oc gc n
                                    Prims.int_zero acc_rev acc_count limit
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
                                   let n = row_group_row_count sc pc oc gc in
                                   filter_zipped_rows_limited_seq h bound_s
                                     bound_p bound_o bound_g sc pc oc gc n
                                     Prims.int_zero acc_rev acc_count limit
                               | uu___6 -> (acc_rev, acc_count, false) in
                             (match uu___5 with
                              | (acc_rev', acc_count', hit) ->
                                  if hit
                                  then (acc_rev', c4)
                                  else
                                    walk_candidate_rgs_search_limited h
                                      bound_s bound_p bound_o bound_g rest
                                      acc_rev' acc_count' limit c4))))))
let rec walk_row_groups_search_limited_global (h : cottas_ondisk_handle)
  (table :
    Parquet_Footer.parquet_row_group_offset_table
      FStar_Pervasives_Native.option)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (rg_index : Prims.nat) (rg_count : Prims.nat) (fuel : Prims.nat)
  (acc_rev : Parser_BallyhooCOTTAS.cottas_qp_row Prims.list)
  (acc_count : Prims.nat) (limit : Prims.nat) :
  Parser_BallyhooCOTTAS.cottas_qp_row Prims.list=
  if fuel = Prims.int_zero
  then acc_rev
  else
    if rg_index >= rg_count
    then acc_rev
    else
      if acc_count >= limit
      then acc_rev
      else
        (let s_col =
           pcache_decode_global_auto table h.coh_path rg_index Prims.int_zero in
         let p_col =
           pcache_decode_global_auto table h.coh_path rg_index Prims.int_one in
         let o_col =
           pcache_decode_global_auto table h.coh_path rg_index
             (Prims.of_int (2)) in
         let g_col =
           pcache_decode_global_auto table h.coh_path rg_index
             (Prims.of_int (3)) in
         let uu___3 =
           match (s_col, p_col, o_col, g_col) with
           | (FStar_Pervasives_Native.Some sc, FStar_Pervasives_Native.Some
              pc, FStar_Pervasives_Native.Some oc,
              FStar_Pervasives_Native.Some gc) ->
               let n = row_group_row_count sc pc oc gc in
               filter_zipped_rows_limited_seq h bound_s bound_p bound_o
                 bound_g sc pc oc gc n Prims.int_zero acc_rev acc_count limit
           | uu___4 -> (acc_rev, acc_count, false) in
         match uu___3 with
         | (acc_rev', acc_count', hit) ->
             if hit
             then acc_rev'
             else
               walk_row_groups_search_limited_global h table bound_s bound_p
                 bound_o bound_g (rg_index + Prims.int_one) rg_count
                 (fuel - Prims.int_one) acc_rev' acc_count' limit)
let rec walk_candidate_rgs_search_limited_global (h : cottas_ondisk_handle)
  (table :
    Parquet_Footer.parquet_row_group_offset_table
      FStar_Pervasives_Native.option)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (candidates : Prims.nat Prims.list)
  (acc_rev : Parser_BallyhooCOTTAS.cottas_qp_row Prims.list)
  (acc_count : Prims.nat) (limit : Prims.nat) :
  Parser_BallyhooCOTTAS.cottas_qp_row Prims.list=
  if acc_count >= limit
  then acc_rev
  else
    (match candidates with
     | [] -> acc_rev
     | rg_index::rest ->
         let s_col =
           pcache_decode_global_auto table h.coh_path rg_index Prims.int_zero in
         let p_col =
           pcache_decode_global_auto table h.coh_path rg_index Prims.int_one in
         let o_col =
           pcache_decode_global_auto table h.coh_path rg_index
             (Prims.of_int (2)) in
         let g_col =
           pcache_decode_global_auto table h.coh_path rg_index
             (Prims.of_int (3)) in
         let uu___1 =
           match (s_col, p_col, o_col, g_col) with
           | (FStar_Pervasives_Native.Some sc, FStar_Pervasives_Native.Some
              pc, FStar_Pervasives_Native.Some oc,
              FStar_Pervasives_Native.Some gc) ->
               let n = row_group_row_count sc pc oc gc in
               filter_zipped_rows_limited_seq h bound_s bound_p bound_o
                 bound_g sc pc oc gc n Prims.int_zero acc_rev acc_count limit
           | uu___2 -> (acc_rev, acc_count, false) in
         (match uu___1 with
          | (acc_rev', acc_count', hit) ->
              if hit
              then acc_rev'
              else
                walk_candidate_rgs_search_limited_global h table bound_s
                  bound_p bound_o bound_g rest acc_rev' acc_count' limit))
let rec walk_row_groups_search_limited_tok_global (path : Prims.string)
  (table :
    Parquet_Footer.parquet_row_group_offset_table
      FStar_Pervasives_Native.option)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (rg_index : Prims.nat) (rg_count : Prims.nat) (fuel : Prims.nat)
  (acc_rev : cottas_qp_row_tok Prims.list) (acc_count : Prims.nat)
  (limit : Prims.nat) : cottas_qp_row_tok Prims.list=
  if fuel = Prims.int_zero
  then acc_rev
  else
    if rg_index >= rg_count
    then acc_rev
    else
      if acc_count >= limit
      then acc_rev
      else
        (let s_col =
           pcache_decode_global_auto table path rg_index Prims.int_zero in
         let p_col =
           pcache_decode_global_auto table path rg_index Prims.int_one in
         let o_col =
           pcache_decode_global_auto table path rg_index (Prims.of_int (2)) in
         let g_col =
           pcache_decode_global_auto table path rg_index (Prims.of_int (3)) in
         let uu___3 =
           match (s_col, p_col, o_col, g_col) with
           | (FStar_Pervasives_Native.Some sc, FStar_Pervasives_Native.Some
              pc, FStar_Pervasives_Native.Some oc,
              FStar_Pervasives_Native.Some gc) ->
               let n = row_group_row_count sc pc oc gc in
               filter_zipped_rows_limited_tok_seq bound_s bound_p bound_o
                 bound_g sc pc oc gc n Prims.int_zero acc_rev acc_count limit
           | uu___4 -> (acc_rev, acc_count, false) in
         match uu___3 with
         | (acc_rev', acc_count', hit) ->
             if hit
             then acc_rev'
             else
               walk_row_groups_search_limited_tok_global path table bound_s
                 bound_p bound_o bound_g (rg_index + Prims.int_one) rg_count
                 (fuel - Prims.int_one) acc_rev' acc_count' limit)
let rec walk_candidate_rgs_search_limited_tok_global (path : Prims.string)
  (table :
    Parquet_Footer.parquet_row_group_offset_table
      FStar_Pervasives_Native.option)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (candidates : Prims.nat Prims.list)
  (acc_rev : cottas_qp_row_tok Prims.list) (acc_count : Prims.nat)
  (limit : Prims.nat) : cottas_qp_row_tok Prims.list=
  if acc_count >= limit
  then acc_rev
  else
    (match candidates with
     | [] -> acc_rev
     | rg_index::rest ->
         let s_col =
           pcache_decode_global_auto table path rg_index Prims.int_zero in
         let p_col =
           pcache_decode_global_auto table path rg_index Prims.int_one in
         let o_col =
           pcache_decode_global_auto table path rg_index (Prims.of_int (2)) in
         let g_col =
           pcache_decode_global_auto table path rg_index (Prims.of_int (3)) in
         let uu___1 =
           match (s_col, p_col, o_col, g_col) with
           | (FStar_Pervasives_Native.Some sc, FStar_Pervasives_Native.Some
              pc, FStar_Pervasives_Native.Some oc,
              FStar_Pervasives_Native.Some gc) ->
               let n = row_group_row_count sc pc oc gc in
               filter_zipped_rows_limited_tok_seq bound_s bound_p bound_o
                 bound_g sc pc oc gc n Prims.int_zero acc_rev acc_count limit
           | uu___2 -> (acc_rev, acc_count, false) in
         (match uu___1 with
          | (acc_rev', acc_count', hit) ->
              if hit
              then acc_rev'
              else
                walk_candidate_rgs_search_limited_tok_global path table
                  bound_s bound_p bound_o bound_g rest acc_rev' acc_count'
                  limit))
let cottas_ondisk_search_limited (ds : cottas_ondisk_store)
  (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) (limit : Prims.nat) :
  cottas_qp_row_tok Prims.list=
  let h = ds.cods_handle in
  let tt = ondisk_token_tables_global h.coh_path in
  let bound_s =
    id_to_raw_token_via_global tt.ctt_id_to_subj_token h.coh_path
      bound.Parser_BallyhooCOTTAS.cbqp_s in
  let bound_p =
    id_to_raw_token_via_global tt.ctt_id_to_pred_token h.coh_path
      bound.Parser_BallyhooCOTTAS.cbqp_p in
  let bound_o =
    id_to_raw_token_via_global tt.ctt_id_to_obj_token h.coh_path
      bound.Parser_BallyhooCOTTAS.cbqp_o in
  let bound_g =
    graph_bound_to_raw_token h.coh_path bound.Parser_BallyhooCOTTAS.cbqp_g in
  match Parquet_Footer.probe_parquet_row_group_count h.coh_path with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some rg_count ->
      let table =
        Parquet_Footer.probe_parquet_row_group_offset_table h.coh_path in
      let any_bound_present =
        (((FStar_Pervasives_Native.uu___is_Some bound_s) ||
            (FStar_Pervasives_Native.uu___is_Some bound_p))
           || (FStar_Pervasives_Native.uu___is_Some bound_o))
          || (FStar_Pervasives_Native.uu___is_Some bound_g) in
      if any_bound_present
      then
        let uu___ =
          plan_candidate_rgs h table bound_s bound_p bound_o bound_g rg_count in
        (match uu___ with
         | (candidates0, _dc) ->
             let candidates =
               filter_candidates_by_compound_po h.coh_path candidates0
                 bound_p bound_o in
             let acc_rev =
               walk_candidate_rgs_search_limited_tok_global h.coh_path table
                 bound_s bound_p bound_o bound_g candidates [] Prims.int_zero
                 limit in
             Parquet_Footer.list_rev acc_rev)
      else
        (let acc_rev =
           walk_row_groups_search_limited_tok_global h.coh_path table bound_s
             bound_p bound_o bound_g Prims.int_zero rg_count rg_count []
             Prims.int_zero limit in
         Parquet_Footer.list_rev acc_rev)
let cottas_ondisk_search_limited_tok (ds : cottas_ondisk_store)
  (bound : cottas_bound_qp_tok) (limit : Prims.nat) :
  cottas_qp_row_tok Prims.list=
  let h = ds.cods_handle in
  let bound_s = bound.cbqpt_s in
  let bound_p = bound.cbqpt_p in
  let bound_o = bound.cbqpt_o in
  let bound_g = bound.cbqpt_g in
  match Parquet_Footer.probe_parquet_row_group_count h.coh_path with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some rg_count ->
      let table =
        Parquet_Footer.probe_parquet_row_group_offset_table h.coh_path in
      let any_bound_present =
        (((FStar_Pervasives_Native.uu___is_Some bound_s) ||
            (FStar_Pervasives_Native.uu___is_Some bound_p))
           || (FStar_Pervasives_Native.uu___is_Some bound_o))
          || (FStar_Pervasives_Native.uu___is_Some bound_g) in
      if any_bound_present
      then
        let uu___ =
          plan_candidate_rgs h table bound_s bound_p bound_o bound_g rg_count in
        (match uu___ with
         | (candidates0, _dc) ->
             let candidates =
               filter_candidates_by_compound_po h.coh_path candidates0
                 bound_p bound_o in
             let acc_rev =
               walk_candidate_rgs_search_limited_tok_global h.coh_path table
                 bound_s bound_p bound_o bound_g candidates [] Prims.int_zero
                 limit in
             Parquet_Footer.list_rev acc_rev)
      else
        (let acc_rev =
           walk_row_groups_search_limited_tok_global h.coh_path table bound_s
             bound_p bound_o bound_g Prims.int_zero rg_count rg_count []
             Prims.int_zero limit in
         Parquet_Footer.list_rev acc_rev)
let cottas_ondisk_estimate_tok (ds : cottas_ondisk_store)
  (bound : cottas_bound_qp_tok) : Prims.nat=
  let h = ds.cods_handle in
  let bound_s = bound.cbqpt_s in
  let bound_p = bound.cbqpt_p in
  let bound_o = bound.cbqpt_o in
  let bound_g = bound.cbqpt_g in
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
             let table =
               Parquet_Footer.probe_parquet_row_group_offset_table h.coh_path in
             walk_row_groups_estimate_global h table bound_s bound_p bound_o
               bound_g Prims.int_zero rg_count rg_count Prims.int_zero)
  else
    (match Parquet_Footer.probe_parquet_row_group_count h.coh_path with
     | FStar_Pervasives_Native.None -> Prims.int_zero
     | FStar_Pervasives_Native.Some rg_count ->
         let table =
           Parquet_Footer.probe_parquet_row_group_offset_table h.coh_path in
         let uu___1 =
           plan_candidate_rgs h table bound_s bound_p bound_o bound_g
             rg_count in
         (match uu___1 with
          | (candidates0, _dc) ->
              let candidates =
                filter_candidates_by_compound_po h.coh_path candidates0
                  bound_p bound_o in
              let n_candidates = FStar_List_Tot_Base.length candidates in
              if n_candidates = Prims.int_zero
              then Prims.int_zero
              else
                if rg_count = Prims.int_zero
                then Prims.int_zero
                else
                  (match Parquet_Footer.probe_parquet_num_rows h.coh_path
                   with
                   | FStar_Pervasives_Native.None -> n_candidates
                   | FStar_Pervasives_Native.Some total_rows ->
                       let avg = total_rows / rg_count in
                       let prod = n_candidates * avg in
                       if prod < Prims.int_zero then Prims.int_zero else prod)))
let count_exact_offset_index_eligible (h : cottas_ondisk_handle)
  (bound_g : Prims.string FStar_Pervasives_Native.option) : Prims.bool=
  (match h.coh_graphs with | [] -> true | uu___ -> false) &&
    (match bound_g with
     | FStar_Pervasives_Native.None -> true
     | FStar_Pervasives_Native.Some g -> g = "DEFAULT")
let rec sum_predicate_offset_counts
  (oh :
    RDF_Store_Columnar_OffsetIndex.offset_handle
      FStar_Pervasives_Native.option)
  (pred_id : Prims.nat) (rg_index : Prims.nat) (rg_count : Prims.nat)
  (fuel : Prims.nat) (acc : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.Some acc
  else
    if rg_index >= rg_count
    then FStar_Pervasives_Native.Some acc
    else
      (match SPARQL_Plan_AccessPath.choose_access_path oh rg_index
               (FStar_Pervasives_Native.Some pred_id)
       with
       | SPARQL_Plan_AccessPath.AP_FullScan -> FStar_Pervasives_Native.None
       | SPARQL_Plan_AccessPath.AP_Skip ->
           sum_predicate_offset_counts oh pred_id (rg_index + Prims.int_one)
             rg_count (fuel - Prims.int_one) acc
       | SPARQL_Plan_AccessPath.AP_OffsetJump cv ->
           sum_predicate_offset_counts oh pred_id (rg_index + Prims.int_one)
             rg_count (fuel - Prims.int_one)
             (acc + cv.RDF_Store_Columnar_OffsetIndex.cv_count))
let cottas_ondisk_count_exact_via_offset_index (h : cottas_ondisk_handle)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option)
  (rg_count : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match (bound_s, bound_p, bound_o) with
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some p,
     FStar_Pervasives_Native.None) ->
      if Prims.op_Negation (count_exact_offset_index_eligible h bound_g)
      then FStar_Pervasives_Native.None
      else
        (match compound_po_dict_encode h.coh_path "p" p with
         | FStar_Pervasives_Native.None ->
             FStar_Pervasives_Native.Some Prims.int_zero
         | FStar_Pervasives_Native.Some pred_id ->
             let oh =
               RDF_Store_Columnar_OffsetIndex.open_offsets
                 (RDF_Store_Columnar_OffsetIndex.offsets_path_of h.coh_path) in
             sum_predicate_offset_counts oh pred_id Prims.int_zero rg_count
               rg_count Prims.int_zero)
  | (uu___, uu___1, uu___2) -> FStar_Pervasives_Native.None
let cottas_ondisk_count_exact_via_subject_offset_index
  (h : cottas_ondisk_handle)
  (bound_s : Prims.string FStar_Pervasives_Native.option)
  (bound_p : Prims.string FStar_Pervasives_Native.option)
  (bound_o : Prims.string FStar_Pervasives_Native.option)
  (bound_g : Prims.string FStar_Pervasives_Native.option) :
  Prims.nat FStar_Pervasives_Native.option=
  match (bound_s, bound_p, bound_o) with
  | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.None,
     FStar_Pervasives_Native.None) ->
      if Prims.op_Negation (count_exact_offset_index_eligible h bound_g)
      then FStar_Pervasives_Native.None
      else
        (match compound_po_dict_encode h.coh_path "s" s with
         | FStar_Pervasives_Native.None ->
             FStar_Pervasives_Native.Some Prims.int_zero
         | FStar_Pervasives_Native.Some subj_id ->
             (match RDF_Store_Columnar_SubjectOffsetIndex.open_subject_offsets
                      (RDF_Store_Columnar_SubjectOffsetIndex.subject_offsets_path_of
                         h.coh_path)
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some oh ->
                  if
                    RDF_Store_Columnar_SubjectOffsetIndex.subject_offset_handle_ok
                      oh
                  then
                    (match RDF_Store_Columnar_SubjectOffsetIndex.range_for_subject
                             oh subj_id
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some r ->
                         FStar_Pervasives_Native.Some
                           (RDF_Store_Columnar_SubjectOffsetIndex.subject_range_count
                              r))
                  else FStar_Pervasives_Native.None))
  | (uu___, uu___1, uu___2) -> FStar_Pervasives_Native.None
let cottas_ondisk_count_exact_tok (ds : cottas_ondisk_store)
  (bound : cottas_bound_qp_tok) : Prims.nat=
  let h = ds.cods_handle in
  let bound_s = bound.cbqpt_s in
  let bound_p = bound.cbqpt_p in
  let bound_o = bound.cbqpt_o in
  let bound_g = bound.cbqpt_g in
  if
    (((FStar_Pervasives_Native.uu___is_None bound_s) &&
        (FStar_Pervasives_Native.uu___is_None bound_p))
       && (FStar_Pervasives_Native.uu___is_None bound_o))
      && (FStar_Pervasives_Native.uu___is_None bound_g)
  then
    match Parquet_Footer.probe_parquet_num_rows h.coh_path with
    | FStar_Pervasives_Native.Some n -> n
    | FStar_Pervasives_Native.None ->
        (match Parquet_Footer.probe_parquet_row_group_count h.coh_path with
         | FStar_Pervasives_Native.None -> Prims.int_zero
         | FStar_Pervasives_Native.Some rg_count ->
             let table =
               Parquet_Footer.probe_parquet_row_group_offset_table h.coh_path in
             walk_row_groups_estimate_global h table bound_s bound_p bound_o
               bound_g Prims.int_zero rg_count rg_count Prims.int_zero)
  else
    (match Parquet_Footer.probe_parquet_row_group_count h.coh_path with
     | FStar_Pervasives_Native.None -> Prims.int_zero
     | FStar_Pervasives_Native.Some rg_count ->
         let table =
           Parquet_Footer.probe_parquet_row_group_offset_table h.coh_path in
         if
           ((FStar_Pervasives_Native.uu___is_None bound_s) &&
              (FStar_Pervasives_Native.uu___is_None bound_p))
             && (FStar_Pervasives_Native.uu___is_None bound_o)
         then
           walk_row_groups_count_graph_global h table bound_g Prims.int_zero
             rg_count rg_count Prims.int_zero
         else
           (match cottas_ondisk_count_exact_via_offset_index h bound_s
                    bound_p bound_o bound_g rg_count
            with
            | FStar_Pervasives_Native.Some n -> n
            | FStar_Pervasives_Native.None ->
                (match cottas_ondisk_count_exact_via_subject_offset_index h
                         bound_s bound_p bound_o bound_g
                 with
                 | FStar_Pervasives_Native.Some n -> n
                 | FStar_Pervasives_Native.None ->
                     walk_row_groups_count_exact_global h table bound_s
                       bound_p bound_o bound_g Prims.int_zero rg_count
                       rg_count Prims.int_zero)))
let cottas_ondisk_row_tok_to_quad (row : cottas_qp_row_tok) :
  (RDF_Triple.triple * RDF_Term.iri FStar_Pervasives_Native.option)=
  ({
     RDF_Triple.s = (token_to_subject row.cqprt_s);
     RDF_Triple.p = (token_to_predicate row.cqprt_p);
     RDF_Triple.o = (token_to_object row.cqprt_o)
   },
    (if row.cqprt_g = "DEFAULT"
     then FStar_Pervasives_Native.None
     else FStar_Pervasives_Native.Some (token_to_graph_name row.cqprt_g)))
let rec cottas_ondisk_rows_tok_to_quads_acc
  (rows : cottas_qp_row_tok Prims.list)
  (acc :
    (RDF_Triple.triple * RDF_Term.iri FStar_Pervasives_Native.option)
      Prims.list)
  :
  (RDF_Triple.triple * RDF_Term.iri FStar_Pervasives_Native.option)
    Prims.list=
  match rows with
  | [] -> acc
  | row::rest ->
      cottas_ondisk_rows_tok_to_quads_acc rest
        ((cottas_ondisk_row_tok_to_quad row) :: acc)
let cottas_ondisk_rows_tok_to_quads (rows : cottas_qp_row_tok Prims.list) :
  (RDF_Triple.triple * RDF_Term.iri FStar_Pervasives_Native.option)
    Prims.list=
  FStar_List_Tot_Base.rev (cottas_ondisk_rows_tok_to_quads_acc rows [])
let rec cottas_ondisk_rows_tok_to_triples_acc
  (rows : cottas_qp_row_tok Prims.list) (acc : RDF_Triple.triple Prims.list)
  : RDF_Triple.triple Prims.list=
  match rows with
  | [] -> acc
  | row::rest ->
      let uu___ = cottas_ondisk_row_tok_to_quad row in
      (match uu___ with
       | (t, _gname) -> cottas_ondisk_rows_tok_to_triples_acc rest (t :: acc))
let cottas_ondisk_rows_tok_to_triples (rows : cottas_qp_row_tok Prims.list) :
  RDF_Triple.triple Prims.list=
  FStar_List_Tot_Base.rev (cottas_ondisk_rows_tok_to_triples_acc rows [])

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
  (* #200 PR2 (2026-05-09): byte assembly migrated to F* at
     RDF.CottasStore.DictWriter.serialize_dict. The OCaml side here is
     reduced to the rule-#11(a) I/O step: convert the F*-extracted byte
     list to a string and atomic-write to disk. The F* serializer
     enforces the same on-disk format invariants (magic 'COTD', version,
     32-byte header, ids[], token_offs[], token_data) but with verified
     overflow checks (n < 2^32, total_offset < 2^64). *)
  let write_dict_file (path : string) (sorted_tokens : string array) : unit =
    let bytes_list =
      RDF_CottasStore_DictWriter.serialize_dict
        (Array.to_list sorted_tokens)
    in
    let buf = Buffer.create (List.length bytes_list) in
    List.iter (fun b -> Buffer.add_char buf (Char.chr (b land 0xff))) bytes_list;
    atomic_write path (Buffer.contents buf)

  (* Writer for one column's .presence file.
     Layout:
       [ magic u32 | version u32 | num_rgs u32 | num_tokens u32 ]
       [ bitmap : ceil(num_rgs * num_tokens / 8) bytes, row-major,
                  bit (rg*num_tokens + tok) ]

     #200 PR2 part 2 (2026-05-09): the 16-byte header is now produced
     by F* (RDF.CottasStore.PresenceWriter.serialize_presence_header).
     Bitmap contents stay in OCaml because parliament-scale .presence
     files reach ~12.5MB; materialising as F-star's list-of-char
     would cost millions of cons cells per column. Atomic-write +
     bitmap bit-set are rule-#11(a) acceptable I/O-glue work. *)
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
    let header_chars =
      RDF_CottasStore_PresenceWriter.serialize_presence_header
        (Z.of_int rg_count) (Z.of_int n)
    in
    let buf = Buffer.create (16 + bytes) in
    List.iter (fun b -> Buffer.add_char buf (Char.chr (b land 0xff))) header_chars;
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

(* compound-po: Cottas_compound_po_writer installed (issue #104, 2026-04-26).

   Sibling .po.presence companion file: per-row-group sparse-roaring
   sorted (p_id, o_id) pair list. Format:

     [ magic 'COPO' u32 (0x4f504f43 LE) | version u32 | num_rgs u32 |
       pred_dict_size u32 | obj_dict_size u32 ]                   (20 bytes)
     [ rg_offsets : u64 array, length num_rgs + 1                ]
       rg_offsets[k]   = byte offset into file where rg k's pairs begin
       rg_offsets[k+1] = end offset (exclusive)
     [ pairs : u64[] sorted lex (p_id, o_id)
               per pair: u32-LE o_id then u32-LE p_id
               so u64-LE read = (p_id << 32) | o_id and ascending
               u64 sort == lex (p_id, o_id).                       ]

   WRITER ONLY this run. No reader code; query results are unchanged.
   Future reader patch (#104 follow-on) will redirect search_fast /
   estimate_fast to consult this file when both p and o are bound. *)
module Cottas_compound_po_writer = struct
  open Stdlib
  type pint = Stdlib.Int.t

  let copo_magic : pint = 0x4f504f43  (* 'COPO' little-endian *)
  let layout_version : pint = 1
  let header_size : pint = 20  (* 5 u32 fields *)

  let compound_path (cottas_path : string) : string =
    cottas_path ^ ".po.presence"

  let write_u32_le buf (v : pint) =
    Buffer.add_char buf (Stdlib.Char.chr (v land 0xff));
    Buffer.add_char buf (Stdlib.Char.chr ((v lsr 8) land 0xff));
    Buffer.add_char buf (Stdlib.Char.chr ((v lsr 16) land 0xff));
    Buffer.add_char buf (Stdlib.Char.chr ((v lsr 24) land 0xff))

  let write_u64_le buf (v : pint) =
    write_u32_le buf (v land 0xffffffff);
    write_u32_le buf ((v lsr 32) land 0xffffffff)

  let atomic_write (path : string) (data : string) : unit =
    let tmp = path ^ ".tmp" in
    let oc = open_out_bin tmp in
    output_string oc data;
    flush oc;
    (try Unix.fsync (Unix.descr_of_out_channel oc) with _ -> ());
    close_out oc;
    Sys.rename tmp path

  (* Build a token -> id Hashtbl from a column dict, by walking every
     dict entry. The dict was sorted ascending so id i corresponds to
     the i'th token in lex order (Vav3 invariant). Hashtbl size hint
     is 2x num_tokens to keep load factor low. *)
  let build_tok_to_id (dict_path : string)
    (dh : RDF_CottasStore_OnDiskIndex.dict_header)
    (n_tok : pint) : (string, pint) Hashtbl.t =
    let tab : (string, pint) Hashtbl.t = Hashtbl.create (n_tok * 2 + 17) in
    for id = 0 to n_tok - 1 do
      match RDF_CottasStore_OnDiskIndex.dict_decode_token
              dict_path dh (Z.of_int id) with
      | FStar_Pervasives_Native.Some raw -> Hashtbl.replace tab raw id
      | FStar_Pervasives_Native.None ->
        Printf.eprintf "[compound-po-WARN] tok_to_id build: id=%d decode failed in %s\n%!"
          id dict_path
    done;
    tab

  (* Returns true iff the existing .po.presence file has the right
     magic, version, num_rgs, pred_dict_size, obj_dict_size. Otherwise
     the file is stale (corpus reload, dict size changed) and a rebuild
     is needed. *)
  let existing_file_matches (cottas_path : string)
    (expected_num_rgs : pint)
    (expected_pred_dict_size : pint)
    (expected_obj_dict_size  : pint) : bool =
    let opath = compound_path cottas_path in
    if not (Sys.file_exists opath) then false
    else begin
      let sz = try (Unix.stat opath).Unix.st_size with _ -> 0 in
      if sz < header_size then false
      else begin
        let ic = open_in_bin opath in
        let buf = Stdlib.Bytes.create header_size in
        let n_read = try Stdlib.really_input ic buf 0 header_size; header_size
                     with End_of_file -> 0 in
        close_in ic;
        if n_read < header_size then false
        else
          let g i = Stdlib.Char.code (Stdlib.Bytes.unsafe_get buf i) in
          let read_u32 off =
            let b0 = g off in
            let b1 = g (off+1) in
            let b2 = g (off+2) in
            let b3 = g (off+3) in
            b0 lor (b1 lsl 8) lor (b2 lsl 16) lor (b3 lsl 24) in
          let magic = read_u32 0 in
          let ver   = read_u32 4 in
          let num_rgs = read_u32 8 in
          let pred_sz = read_u32 12 in
          let obj_sz  = read_u32 16 in
          let ok =
            magic = copo_magic &&
            ver = layout_version &&
            num_rgs = expected_num_rgs &&
            pred_sz = expected_pred_dict_size &&
            obj_sz  = expected_obj_dict_size in
          if not ok then
            Printf.eprintf "[compound-po-trace] existing %s header mismatch (magic=0x%x ver=%d rgs=%d pred=%d obj=%d vs exp rgs=%d pred=%d obj=%d) -> rebuild\n%!"
              opath magic ver num_rgs pred_sz obj_sz
              expected_num_rgs expected_pred_dict_size expected_obj_dict_size;
          ok
      end
    end

  (* Build the .po.presence file by walking the predicate + object
     columns of each rg in tandem and collecting distinct (p_id, o_id)
     pairs. Idempotent: skip if existing file's header matches.
     Returns unit; logs progress on stderr. *)
  let build_compound_po_file (cottas_path : string)
    (pred_tok_to_id : (string, pint) Hashtbl.t)
    (obj_tok_to_id  : (string, pint) Hashtbl.t)
    (num_rgs : pint) (pred_dict_size : pint) (obj_dict_size : pint) : unit =
    let opath = compound_path cottas_path in
    Printf.eprintf "[compound-po-trace] writing %s (num_rgs=%d pred_dict=%d obj_dict=%d)\n%!"
      opath num_rgs pred_dict_size obj_dict_size;
    let t0 = Unix.gettimeofday () in
    (* Per-rg sorted distinct pair set. We accumulate unique pair-codes
       (p_id << 32) | o_id into a Hashtbl per rg, then sort + emit.
       Memory: each rg has up to ~120 K rows on parliament; pairs are
       8 bytes raw, Hashtbl overhead ~3-4x means ~5 MB per rg, peak
       ~125 MB across all rgs concurrently. We instead collect rg-by-
       rg and write into a per-rg buffer to amortise that. *)
    let n_index = num_rgs + 1 in
    let index_size = 8 * n_index in
    let data_offset0 = header_size + index_size in
    (* Two passes: first collect per-rg sorted unique pair-codes; then
       compute byte offsets; then emit header + index + data. We hold
       one rg's pair codes at a time as Stdlib.Array. *)
    let per_rg_codes : pint Stdlib.Array.t Stdlib.Array.t =
      Stdlib.Array.make num_rgs (Stdlib.Array.make 0 0) in
    let total_pairs = ref 0 in
    for rg = 0 to num_rgs - 1 do
      let t_rg = Unix.gettimeofday () in
      (* Decode predicate column (col=1) and object column (col=2) for this rg. *)
      let p_col_opt = Parquet_Footer.probe_parquet_column_decode_in_row_group
                        cottas_path (Z.of_int rg) Z.one in
      let o_col_opt = Parquet_Footer.probe_parquet_column_decode_in_row_group
                        cottas_path (Z.of_int rg) (Z.of_int 2) in
      (match p_col_opt, o_col_opt with
       | FStar_Pervasives_Native.None, _ ->
         Printf.eprintf "[compound-po-WARN] rg=%d: predicate-column decode failed; rg empty in compound\n%!" rg
       | _, FStar_Pervasives_Native.None ->
         Printf.eprintf "[compound-po-WARN] rg=%d: object-column decode failed; rg empty in compound\n%!" rg
       | FStar_Pervasives_Native.Some p_lst, FStar_Pervasives_Native.Some o_lst ->
         (* Walk the two lists in lockstep; require same length (rg-row
            count). Mismatch => log + truncate to min length. *)
         let p_arr = Stdlib.Array.of_list p_lst in
         let o_arr = Stdlib.Array.of_list o_lst in
         let np = Stdlib.Array.length p_arr in
         let no = Stdlib.Array.length o_arr in
         if np <> no then
           Printf.eprintf "[compound-po-WARN] rg=%d: pred col len=%d obj col len=%d (using min)\n%!"
             rg np no;
         let n_rows = if np < no then np else no in
         (* Use Hashtbl keyed by pair-code for de-dup. *)
         let seen : (pint, unit) Hashtbl.t = Hashtbl.create (n_rows + 17) in
         let unknown_p = ref 0 in
         let unknown_o = ref 0 in
         let null_cells = ref 0 in
         for i = 0 to n_rows - 1 do
           match p_arr.(i), o_arr.(i) with
           | FStar_Pervasives_Native.None, _
           | _, FStar_Pervasives_Native.None ->
             incr null_cells
           | FStar_Pervasives_Native.Some p_raw, FStar_Pervasives_Native.Some o_raw ->
             (match Hashtbl.find_opt pred_tok_to_id p_raw,
                    Hashtbl.find_opt obj_tok_to_id  o_raw with
              | None, _ -> incr unknown_p
              | _, None -> incr unknown_o
              | Some p_id, Some o_id ->
                if p_id < 0 || p_id >= pred_dict_size ||
                   o_id < 0 || o_id >= obj_dict_size  then
                  Printf.eprintf "[compound-po-WARN] rg=%d row=%d id-out-of-range (p=%d/%d o=%d/%d)\n%!"
                    rg i p_id pred_dict_size o_id obj_dict_size
                else
                  let code = (p_id lsl 32) lor o_id in
                  if not (Hashtbl.mem seen code) then
                    Hashtbl.add seen code ())
         done;
         (* Materialise + sort. *)
         let n_uniq = Hashtbl.length seen in
         let arr = Stdlib.Array.make n_uniq 0 in
         let k = ref 0 in
         Hashtbl.iter (fun code () ->
           Stdlib.Array.unsafe_set arr !k code;
           incr k) seen;
         Stdlib.Array.sort Stdlib.compare arr;
         per_rg_codes.(rg) <- arr;
         total_pairs := !total_pairs + n_uniq;
         if rg = 0 || rg = num_rgs - 1 || rg mod 5 = 0 then
           Printf.eprintf "[compound-po-trace] rg=%d/%d: rows=%d uniq_pairs=%d (unknown_p=%d unknown_o=%d nulls=%d) in %.2fs\n%!"
             rg num_rgs n_rows n_uniq !unknown_p !unknown_o !null_cells
             (Unix.gettimeofday () -. t_rg))
    done;
    Printf.eprintf "[compound-po-trace] columnscan done in %.2fs (total_unique_pairs=%d)\n%!"
      (Unix.gettimeofday () -. t0) !total_pairs;
    (* Compute rg_offsets (byte offsets into the data section). *)
    let rg_offsets = Stdlib.Array.make n_index 0 in
    let cur = ref data_offset0 in
    for rg = 0 to num_rgs - 1 do
      rg_offsets.(rg) <- !cur;
      cur := !cur + 8 * Stdlib.Array.length per_rg_codes.(rg)
    done;
    rg_offsets.(num_rgs) <- !cur;
    let total_size = !cur in
    Printf.eprintf "[compound-po-trace] total file size = %d bytes (%.1f MB)\n%!"
      total_size (float_of_int total_size /. (1024.0 *. 1024.0));
    let buf = Buffer.create total_size in
    (* Header — produced by F* (rule #11(a) byte-layout boundary). *)
    let header_chars =
      RDF_CottasStore_CompoundPresenceWriter.serialize_compound_presence_header
        (Z.of_int num_rgs) (Z.of_int pred_dict_size) (Z.of_int obj_dict_size)
    in
    List.iter (fun b -> Buffer.add_char buf (Char.chr (b land 0xff))) header_chars;
    (* Index. *)
    for i = 0 to n_index - 1 do
      write_u64_le buf rg_offsets.(i)
    done;
    (* Data. *)
    for rg = 0 to num_rgs - 1 do
      let arr = per_rg_codes.(rg) in
      let n = Stdlib.Array.length arr in
      for i = 0 to n - 1 do
        write_u64_le buf (Stdlib.Array.unsafe_get arr i)
      done
    done;
    let t1 = Unix.gettimeofday () in
    atomic_write opath (Buffer.contents buf);
    let t2 = Unix.gettimeofday () in
    let stat_size = try (Unix.stat opath).Unix.st_size with _ -> -1 in
    Printf.eprintf "[compound-po-trace] wrote %s (Nbytes=%d) in %.2fs (build %.2fs + write %.2fs)\n%!"
      opath stat_size (t2 -. t0) (t1 -. t0) (t2 -. t1)

  (* Build .po.presence if absent OR if its header doesn't match the
     current .p.dict / .o.dict / .p.presence dimensions. Reads dict
     headers + tok_to_id maps via the F*-extracted RDF_CottasStore_OnDiskIndex
     primitives. Idempotent. *)
  let ensure_compound_po_built (cottas_path : string)
    (_h : cottas_ondisk_handle) : unit =
    let dpath_p = cottas_path ^ ".p.dict" in
    let dpath_o = cottas_path ^ ".o.dict" in
    let ppath_p = cottas_path ^ ".p.presence" in
    match RDF_CottasStore_OnDiskIndex.read_dict_header dpath_p,
          RDF_CottasStore_OnDiskIndex.read_dict_header dpath_o with
    | FStar_Pervasives_Native.None, _ ->
      Printf.eprintf "[compound-po-WARN] cannot read predicate dict header at %s; skip compound build\n%!" dpath_p
    | _, FStar_Pervasives_Native.None ->
      Printf.eprintf "[compound-po-WARN] cannot read object dict header at %s; skip compound build\n%!" dpath_o
    | FStar_Pervasives_Native.Some dh_p, FStar_Pervasives_Native.Some dh_o ->
      let n_preds = Z.to_int dh_p.RDF_CottasStore_OnDiskIndex.dh_num_tokens in
      let n_objs  = Z.to_int dh_o.RDF_CottasStore_OnDiskIndex.dh_num_tokens in
      let n_rgs = match RDF_CottasStore_OnDiskIndex.read_presence_header ppath_p with
        | FStar_Pervasives_Native.Some ph ->
          Z.to_int ph.RDF_CottasStore_OnDiskIndex.ph_num_rgs
        | FStar_Pervasives_Native.None ->
          (match Parquet_Footer.probe_parquet_row_group_count cottas_path with
           | FStar_Pervasives_Native.None -> 0
           | FStar_Pervasives_Native.Some n -> Z.to_int n) in
      Printf.eprintf "[compound-po-trace] dimensions: n_rgs=%d n_preds=%d n_objs=%d\n%!"
        n_rgs n_preds n_objs;
      if n_rgs <= 0 || n_preds <= 0 || n_objs <= 0 then begin
        Printf.eprintf "[compound-po-WARN] degenerate dimensions; skip\n%!"
      end else if existing_file_matches cottas_path n_rgs n_preds n_objs then begin
        Printf.eprintf "[compound-po-trace] existing %s header matches; skip\n%!"
          (compound_path cottas_path)
      end else begin
        let pred_tok_to_id = build_tok_to_id dpath_p dh_p n_preds in
        let obj_tok_to_id  = build_tok_to_id dpath_o dh_o n_objs in
        Printf.eprintf "[compound-po-trace] tok_to_id sizes: pred=%d obj=%d\n%!"
          (Hashtbl.length pred_tok_to_id) (Hashtbl.length obj_tok_to_id);
        if Hashtbl.length pred_tok_to_id > 0 && Hashtbl.length obj_tok_to_id > 0 then
          build_compound_po_file cottas_path pred_tok_to_id obj_tok_to_id
            n_rgs n_preds n_objs
        else
          Printf.eprintf "[compound-po-WARN] empty tok_to_id; skip\n%!"
      end
end


(* subject-offset-index: Cottas_subject_offset_idx installed (issue
   #100 follow-up, 2026-07-13). Per-SUBJECT contiguous global
   row-range index. Sibling .s.offsets file:
     [ magic 'COTS' u32 | version u32 | num_subjects u32 | num_rows_total u32 ]
     [ ranges : (u64 start, u64 end_exclusive) * num_subjects, ascending
       subject-id order ]
   Closes the q3 subject-point-lookup gap: a bound-subject query can
   read one dense (start,end) entry instead of decoding whole row
   groups on spec. Built once (subject column is globally contiguous
   post-sort, so this is a single sequential pass), mmap'd on demand
   by the generic companion-file primitives at query time (no
   OCaml-side reader in this patch -- see this file's own header
   comment). *)
module Cottas_subject_offset_idx = struct
  open Stdlib
  type pint = Stdlib.Int.t

  let header_size : pint = 16  (* 4 u32 fields *)

  let subject_offsets_path (cottas_path : string) : string =
    cottas_path ^ ".s.offsets"

  let write_u32_le buf (v : pint) =
    Buffer.add_char buf (Stdlib.Char.chr (v land 0xff));
    Buffer.add_char buf (Stdlib.Char.chr ((v lsr 8) land 0xff));
    Buffer.add_char buf (Stdlib.Char.chr ((v lsr 16) land 0xff));
    Buffer.add_char buf (Stdlib.Char.chr ((v lsr 24) land 0xff))

  let write_u64_le buf (v : pint) =
    write_u32_le buf (v land 0xffffffff);
    write_u32_le buf ((v lsr 32) land 0xffffffff)

  let atomic_write (path : string) (data : string) : unit =
    let tmp = path ^ ".tmp" in
    let oc = open_out_bin tmp in
    output_string oc data;
    flush oc;
    (try Unix.fsync (Unix.descr_of_out_channel oc) with _ -> ());
    close_out oc;
    Sys.rename tmp path

  (* Build the offsets file by walking the SUBJECT column once,
     row-group order (= global row order, per BaseWriter's subject-
     primary sort). Requires the subject dict's tok_to_id mapping (as
     a Hashtbl) so we can encode each token to its dict id during the
     walk. Detects subject-value transitions (rows are pre-sorted) and
     records each subject's [start, end) global row range. *)
  let build_subject_offsets_file (cottas_path : string)
    (subj_tok_to_id : (string, pint) Hashtbl.t)
    (num_subjects : pint) (num_rgs : pint) : unit =
    let opath = subject_offsets_path cottas_path in
    Printf.eprintf "[subject-offset-trace] building offsets file %s (num_subjects=%d num_rgs=%d)\n%!"
      opath num_subjects num_rgs;
    let t0 = Unix.gettimeofday () in
    let starts = Stdlib.Array.make num_subjects (-1) in
    let ends   = Stdlib.Array.make num_subjects (-1) in
    let global_row = ref 0 in
    let cur_subj = ref (-1) in
    let close_cur () =
      if !cur_subj >= 0 then ends.(!cur_subj) <- !global_row
    in
    for rg = 0 to num_rgs - 1 do
      let t_rg = Unix.gettimeofday () in
      (match Parquet_Footer.probe_parquet_column_decode_in_row_group
               cottas_path (Z.of_int rg) Z.zero with  (* col_index 0 = subject *)
       | FStar_Pervasives_Native.None ->
         Printf.eprintf "[subject-offset-WARN] offsets-build: rg=%d subject decode failed\n%!" rg
       | FStar_Pervasives_Native.Some lst ->
         List.iter (function
           | FStar_Pervasives_Native.None -> incr global_row
           | FStar_Pervasives_Native.Some raw ->
             (match Hashtbl.find_opt subj_tok_to_id raw with
              | None ->
                Printf.eprintf "[subject-offset-WARN] offsets-build: rg=%d row=%d unknown subject token %s\n%!"
                  rg !global_row raw
              | Some sid ->
                if sid >= 0 && sid < num_subjects then begin
                  if sid <> !cur_subj then begin
                    close_cur ();
                    cur_subj := sid;
                    starts.(sid) <- !global_row
                  end
                end else
                  Printf.eprintf "[subject-offset-WARN] offsets-build: subject id %d out of range\n%!" sid);
             incr global_row) lst);
      if rg = 0 || rg = num_rgs - 1 || rg mod 5 = 0 then
        Printf.eprintf "[subject-offset-trace] offsets-build rg=%d/%d (%.2fs this rg)\n%!"
          rg num_rgs (Unix.gettimeofday () -. t_rg)
    done;
    close_cur ();
    Printf.eprintf "[subject-offset-trace] offsets-build columnscan done in %.2fs (total_rows=%d)\n%!"
      (Unix.gettimeofday () -. t0) !global_row;
    (* Header — produced by F* (rule #11(a) byte-layout boundary). *)
    let header_chars =
      RDF_CottasStore_SubjectOffsetsWriter.serialize_subject_offsets_header
        (Z.of_int num_subjects) (Z.of_int !global_row)
    in
    let buf = Buffer.create (header_size + 16 * num_subjects) in
    List.iter (fun b -> Buffer.add_char buf (Char.chr (b land 0xff))) header_chars;
    for sid = 0 to num_subjects - 1 do
      let s = starts.(sid) and e = ends.(sid) in
      if s < 0 || e < 0 then begin
        Printf.eprintf "[subject-offset-WARN] offsets-build: subject id %d never observed; writing (0,0)\n%!" sid;
        write_u64_le buf 0;
        write_u64_le buf 0
      end else begin
        write_u64_le buf s;
        write_u64_le buf e
      end
    done;
    let t1 = Unix.gettimeofday () in
    atomic_write opath (Buffer.contents buf);
    let t2 = Unix.gettimeofday () in
    let stat_size = try (Unix.stat opath).Unix.st_size with _ -> -1 in
    Printf.eprintf "[subject-offset-trace] offsets-build wrote %s (Nbytes=%d) in %.2fs (build %.2fs + write %.2fs)\n%!"
      opath stat_size (t2 -. t0) (t1 -. t0) (t2 -. t1)

  (* Build the offsets file if absent. Reads the subject dict's
     tok_to_id mapping from the F* extracted reader (so id assignment
     matches the on-disk dict's sorted-rank ordering, the SAME
     id-space `compound_po_dict_encode path "s" tok` resolves at query
     time). Called from boot (after Vav3 companions are present). *)
  let ensure_subject_offsets_built (cottas_path : string) : unit =
    let opath = subject_offsets_path cottas_path in
    if Sys.file_exists opath && (try (Unix.stat opath).Unix.st_size with _ -> 0) >= header_size then
      Printf.eprintf "[subject-offset-trace] offsets file present at %s, skipping build\n%!" opath
    else begin
      Printf.eprintf "[subject-offset-trace] offsets file absent; building\n%!";
      let dpath = cottas_path ^ ".s.dict" in
      match RDF_CottasStore_OnDiskIndex.read_dict_header dpath with
      | FStar_Pervasives_Native.None ->
        Printf.eprintf "[subject-offset-FATAL] offsets-build: cannot read subject dict header at %s\n%!" dpath
      | FStar_Pervasives_Native.Some dh ->
        let n_subjects = Z.to_int dh.RDF_CottasStore_OnDiskIndex.dh_num_tokens in
        let ppath = cottas_path ^ ".s.presence" in
        let n_rgs = match RDF_CottasStore_OnDiskIndex.read_presence_header ppath with
          | FStar_Pervasives_Native.Some ph ->
            Z.to_int ph.RDF_CottasStore_OnDiskIndex.ph_num_rgs
          | FStar_Pervasives_Native.None ->
            (match Parquet_Footer.probe_parquet_row_group_count cottas_path with
             | FStar_Pervasives_Native.None -> 0
             | FStar_Pervasives_Native.Some n -> Z.to_int n) in
        Printf.eprintf "[subject-offset-trace] offsets-build: n_rgs=%d n_subjects=%d\n%!" n_rgs n_subjects;
        let tok_to_id : (string, pint) Hashtbl.t = Hashtbl.create (n_subjects * 2 + 17) in
        for id = 0 to n_subjects - 1 do
          match RDF_CottasStore_OnDiskIndex.dict_decode_token
                  dpath dh (Z.of_int id) with
          | FStar_Pervasives_Native.Some raw ->
            Hashtbl.replace tok_to_id raw id
          | FStar_Pervasives_Native.None ->
            Printf.eprintf "[subject-offset-WARN] offsets-build: dict_decode_token failed for id=%d\n%!" id
        done;
        Printf.eprintf "[subject-offset-trace] offsets-build: built tok_to_id (size=%d)\n%!"
          (Hashtbl.length tok_to_id);
        if n_rgs > 0 && n_subjects > 0 && Hashtbl.length tok_to_id > 0 then
          build_subject_offsets_file cottas_path tok_to_id n_subjects n_rgs
        else
          Printf.eprintf "[subject-offset-WARN] offsets-build: skipping (n_rgs=%d n_subjects=%d tok_to_id=%d)\n%!"
            n_rgs n_subjects (Hashtbl.length tok_to_id)
    end
end

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
      (* Yod6/Tet3 presence Hashtbl population previously lived here as
         a transitional shim. The query path now consults the F*-pure
         RDF.CottasStore.PresenceBitmap.rg_could_contain (verifiable in
         SPARQL.Plan.Pruning.fst) directly against the mmap'd companion
         file, so the in-RAM Hashtbl mirror is unread dead code. Issue
         #249 retires this presence-bytewalk; #200 Section A codename
         track. *)
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
    (* lamed3: build / mmap the predicate row-offset companion. *)
    (try Cottas_offset_idx.ensure_offsets_built cottas_path
     with e ->
       Printf.eprintf "[lamed3-WARN] ensure_offsets_built raised: %s
%!"
         (Printexc.to_string e));
    (* compound-po: build the (p, o) joint presence companion. *)
    (try Cottas_compound_po_writer.ensure_compound_po_built cottas_path h
     with e ->
       Printf.eprintf "[compound-po-WARN] ensure_compound_po_built raised: %s
%!"
         (Printexc.to_string e));
    (* subject-offset-index: build the per-subject contiguous
       global row-range companion. *)
    (try Cottas_subject_offset_idx.ensure_subject_offsets_built cottas_path
     with e ->
       Printf.eprintf "[subject-offset-WARN] ensure_subject_offsets_built raised: %s
%!"
         (Printexc.to_string e));
    let dt = Unix.gettimeofday () -. t0 in
    Printf.eprintf "[vav3-trace] prewarm_via_companions completed in %.2fs (subjs=%d preds=%d objs=%d graphs=%d)\n%!"
      dt
      (Hashtbl.length tables.Cottas_ondisk_runtime.ft_subj_tok_to_id)
      (Hashtbl.length tables.Cottas_ondisk_runtime.ft_pred_tok_to_id)
      (Hashtbl.length tables.Cottas_ondisk_runtime.ft_obj_tok_to_id)
      (Hashtbl.length tables.Cottas_ondisk_runtime.ft_graph_tok_to_id)
end
