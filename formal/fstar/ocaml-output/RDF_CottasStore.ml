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
let cottas_ondisk_summary (ds : cottas_ondisk_store) :
  Parser_BallyhooCOTTAS.cottas_artifact_summary
    FStar_Pervasives_Native.option=
  (ds.cods_handle).coh_summary
let cottas_ondisk_predicate_present (ds : cottas_ondisk_store)
  (pred : RDF_Term.wf_iri) : Prims.bool=
  match revmap_lookup (ds.cods_handle).coh_pred_revmap
          (iri_to_revmap_key pred)
  with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some uu___ -> true
let rec named_graphs_aux (graphs : RDF_Term.iri Prims.list) (idx : Prims.nat)
  : (RDF_Term.iri * Parser_BallyhooCOTTAS.cottas_graph_ref) Prims.list=
  match graphs with
  | [] -> []
  | g::rest -> (g, idx) :: (named_graphs_aux rest (idx + Prims.int_one))
let cottas_ondisk_named_graphs (ds : cottas_ondisk_store) :
  (RDF_Term.iri * Parser_BallyhooCOTTAS.cottas_graph_ref) Prims.list=
  named_graphs_aux (ds.cods_handle).coh_graphs Prims.int_zero
let cottas_ondisk_version_ok (artifact_path : Prims.string) : Prims.bool=
  match Parquet_Footer.probe_parquet_file_metadata_version artifact_path with
  | FStar_Pervasives_Native.Some v ->
      v = Parquet_Footer.cottas_format_version
  | FStar_Pervasives_Native.None -> false
let cottas_ondisk_open (artifact_path : Prims.string) :
  cottas_ondisk_store FStar_Pervasives_Native.option=
  failwith "Not yet implemented: RDF.CottasStore.cottas_ondisk_open"
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
let ondisk_token_tables_global (path : Prims.string) : cottas_token_tables=
  failwith "Not yet implemented: RDF.CottasStore.ondisk_token_tables_global"
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
