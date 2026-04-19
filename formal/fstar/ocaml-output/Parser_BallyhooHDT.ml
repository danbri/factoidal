open Prims
type ballyhoo_order =
  | BO_SPO 
  | BO_SOP 
  | BO_PSO 
  | BO_POS 
  | BO_OSP 
  | BO_OPS 
let uu___is_BO_SPO (projectee : ballyhoo_order) : Prims.bool=
  match projectee with | BO_SPO -> true | uu___ -> false
let uu___is_BO_SOP (projectee : ballyhoo_order) : Prims.bool=
  match projectee with | BO_SOP -> true | uu___ -> false
let uu___is_BO_PSO (projectee : ballyhoo_order) : Prims.bool=
  match projectee with | BO_PSO -> true | uu___ -> false
let uu___is_BO_POS (projectee : ballyhoo_order) : Prims.bool=
  match projectee with | BO_POS -> true | uu___ -> false
let uu___is_BO_OSP (projectee : ballyhoo_order) : Prims.bool=
  match projectee with | BO_OSP -> true | uu___ -> false
let uu___is_BO_OPS (projectee : ballyhoo_order) : Prims.bool=
  match projectee with | BO_OPS -> true | uu___ -> false
type hdt_control_info =
  {
  hci_format_iri: Prims.string ;
  hci_length_hint: Prims.nat }
let __proj__Mkhdt_control_info__item__hci_format_iri
  (projectee : hdt_control_info) : Prims.string=
  match projectee with
  | { hci_format_iri; hci_length_hint;_} -> hci_format_iri
let __proj__Mkhdt_control_info__item__hci_length_hint
  (projectee : hdt_control_info) : Prims.nat=
  match projectee with
  | { hci_format_iri; hci_length_hint;_} -> hci_length_hint
type hdt_dictionary_summary =
  {
  hds_num_shared_subject_object: Prims.nat ;
  hds_num_subjects: Prims.nat ;
  hds_num_predicates: Prims.nat ;
  hds_num_objects: Prims.nat ;
  hds_size_strings: Prims.nat }
let __proj__Mkhdt_dictionary_summary__item__hds_num_shared_subject_object
  (projectee : hdt_dictionary_summary) : Prims.nat=
  match projectee with
  | { hds_num_shared_subject_object; hds_num_subjects; hds_num_predicates;
      hds_num_objects; hds_size_strings;_} -> hds_num_shared_subject_object
let __proj__Mkhdt_dictionary_summary__item__hds_num_subjects
  (projectee : hdt_dictionary_summary) : Prims.nat=
  match projectee with
  | { hds_num_shared_subject_object; hds_num_subjects; hds_num_predicates;
      hds_num_objects; hds_size_strings;_} -> hds_num_subjects
let __proj__Mkhdt_dictionary_summary__item__hds_num_predicates
  (projectee : hdt_dictionary_summary) : Prims.nat=
  match projectee with
  | { hds_num_shared_subject_object; hds_num_subjects; hds_num_predicates;
      hds_num_objects; hds_size_strings;_} -> hds_num_predicates
let __proj__Mkhdt_dictionary_summary__item__hds_num_objects
  (projectee : hdt_dictionary_summary) : Prims.nat=
  match projectee with
  | { hds_num_shared_subject_object; hds_num_subjects; hds_num_predicates;
      hds_num_objects; hds_size_strings;_} -> hds_num_objects
let __proj__Mkhdt_dictionary_summary__item__hds_size_strings
  (projectee : hdt_dictionary_summary) : Prims.nat=
  match projectee with
  | { hds_num_shared_subject_object; hds_num_subjects; hds_num_predicates;
      hds_num_objects; hds_size_strings;_} -> hds_size_strings
type hdt_triples_summary =
  {
  hts_num_triples: Prims.nat ;
  hts_order: ballyhoo_order }
let __proj__Mkhdt_triples_summary__item__hts_num_triples
  (projectee : hdt_triples_summary) : Prims.nat=
  match projectee with | { hts_num_triples; hts_order;_} -> hts_num_triples
let __proj__Mkhdt_triples_summary__item__hts_order
  (projectee : hdt_triples_summary) : ballyhoo_order=
  match projectee with | { hts_num_triples; hts_order;_} -> hts_order
type hdt_statistics = {
  hs_hdt_size: Prims.nat ;
  hs_original_size: Prims.nat }
let __proj__Mkhdt_statistics__item__hs_hdt_size (projectee : hdt_statistics)
  : Prims.nat=
  match projectee with | { hs_hdt_size; hs_original_size;_} -> hs_hdt_size
let __proj__Mkhdt_statistics__item__hs_original_size
  (projectee : hdt_statistics) : Prims.nat=
  match projectee with
  | { hs_hdt_size; hs_original_size;_} -> hs_original_size
type hdt_artifact_summary =
  {
  has_source_iri: RDF_Graph_Executable.iri FStar_Pervasives_Native.option ;
  has_dictionary: hdt_dictionary_summary ;
  has_triples: hdt_triples_summary ;
  has_statistics: hdt_statistics }
let __proj__Mkhdt_artifact_summary__item__has_source_iri
  (projectee : hdt_artifact_summary) :
  RDF_Graph_Executable.iri FStar_Pervasives_Native.option=
  match projectee with
  | { has_source_iri; has_dictionary; has_triples; has_statistics;_} ->
      has_source_iri
let __proj__Mkhdt_artifact_summary__item__has_dictionary
  (projectee : hdt_artifact_summary) : hdt_dictionary_summary=
  match projectee with
  | { has_source_iri; has_dictionary; has_triples; has_statistics;_} ->
      has_dictionary
let __proj__Mkhdt_artifact_summary__item__has_triples
  (projectee : hdt_artifact_summary) : hdt_triples_summary=
  match projectee with
  | { has_source_iri; has_dictionary; has_triples; has_statistics;_} ->
      has_triples
let __proj__Mkhdt_artifact_summary__item__has_statistics
  (projectee : hdt_artifact_summary) : hdt_statistics=
  match projectee with
  | { has_source_iri; has_dictionary; has_triples; has_statistics;_} ->
      has_statistics
type corpus_graph_binding =
  {
  cgb_graph_name: RDF_Graph_Executable.iri ;
  cgb_artifact_path: Prims.string ;
  cgb_summary: hdt_artifact_summary FStar_Pervasives_Native.option }
let __proj__Mkcorpus_graph_binding__item__cgb_graph_name
  (projectee : corpus_graph_binding) : RDF_Graph_Executable.iri=
  match projectee with
  | { cgb_graph_name; cgb_artifact_path; cgb_summary;_} -> cgb_graph_name
let __proj__Mkcorpus_graph_binding__item__cgb_artifact_path
  (projectee : corpus_graph_binding) : Prims.string=
  match projectee with
  | { cgb_graph_name; cgb_artifact_path; cgb_summary;_} -> cgb_artifact_path
let __proj__Mkcorpus_graph_binding__item__cgb_summary
  (projectee : corpus_graph_binding) :
  hdt_artifact_summary FStar_Pervasives_Native.option=
  match projectee with
  | { cgb_graph_name; cgb_artifact_path; cgb_summary;_} -> cgb_summary
type hdt_handle = unit
type hdt_term_ref = Prims.nat
type hdt_bound_tp =
  {
  hbt_s: hdt_term_ref FStar_Pervasives_Native.option ;
  hbt_p: hdt_term_ref FStar_Pervasives_Native.option ;
  hbt_o: hdt_term_ref FStar_Pervasives_Native.option }
let __proj__Mkhdt_bound_tp__item__hbt_s (projectee : hdt_bound_tp) :
  hdt_term_ref FStar_Pervasives_Native.option=
  match projectee with | { hbt_s; hbt_p; hbt_o;_} -> hbt_s
let __proj__Mkhdt_bound_tp__item__hbt_p (projectee : hdt_bound_tp) :
  hdt_term_ref FStar_Pervasives_Native.option=
  match projectee with | { hbt_s; hbt_p; hbt_o;_} -> hbt_p
let __proj__Mkhdt_bound_tp__item__hbt_o (projectee : hdt_bound_tp) :
  hdt_term_ref FStar_Pervasives_Native.option=
  match projectee with | { hbt_s; hbt_p; hbt_o;_} -> hbt_o
type hdt_tp_row =
  {
  hrow_s: hdt_term_ref FStar_Pervasives_Native.option ;
  hrow_p: hdt_term_ref FStar_Pervasives_Native.option ;
  hrow_o: hdt_term_ref FStar_Pervasives_Native.option }
let __proj__Mkhdt_tp_row__item__hrow_s (projectee : hdt_tp_row) :
  hdt_term_ref FStar_Pervasives_Native.option=
  match projectee with | { hrow_s; hrow_p; hrow_o;_} -> hrow_s
let __proj__Mkhdt_tp_row__item__hrow_p (projectee : hdt_tp_row) :
  hdt_term_ref FStar_Pervasives_Native.option=
  match projectee with | { hrow_s; hrow_p; hrow_o;_} -> hrow_p
let __proj__Mkhdt_tp_row__item__hrow_o (projectee : hdt_tp_row) :
  hdt_term_ref FStar_Pervasives_Native.option=
  match projectee with | { hrow_s; hrow_p; hrow_o;_} -> hrow_o
type hdt_graph_store =
  {
  hgs_graph_name: RDF_Graph_Executable.iri FStar_Pervasives_Native.option ;
  hgs_artifact_path: Prims.string ;
  hgs_summary: hdt_artifact_summary FStar_Pervasives_Native.option ;
  hgs_handle: hdt_handle }
let __proj__Mkhdt_graph_store__item__hgs_graph_name
  (projectee : hdt_graph_store) :
  RDF_Graph_Executable.iri FStar_Pervasives_Native.option=
  match projectee with
  | { hgs_graph_name; hgs_artifact_path; hgs_summary; hgs_handle;_} ->
      hgs_graph_name
let __proj__Mkhdt_graph_store__item__hgs_artifact_path
  (projectee : hdt_graph_store) : Prims.string=
  match projectee with
  | { hgs_graph_name; hgs_artifact_path; hgs_summary; hgs_handle;_} ->
      hgs_artifact_path
let __proj__Mkhdt_graph_store__item__hgs_summary
  (projectee : hdt_graph_store) :
  hdt_artifact_summary FStar_Pervasives_Native.option=
  match projectee with
  | { hgs_graph_name; hgs_artifact_path; hgs_summary; hgs_handle;_} ->
      hgs_summary
let __proj__Mkhdt_graph_store__item__hgs_handle (projectee : hdt_graph_store)
  : hdt_handle=
  match projectee with
  | { hgs_graph_name; hgs_artifact_path; hgs_summary; hgs_handle;_} ->
      hgs_handle

module Ballyhoo_hdt_runtime = struct
  open Stdlib

  type cache = {
    next_id: Z.t ref;
    subject_to_id: (string, Z.t) Hashtbl.t;
    predicate_to_id: (string, Z.t) Hashtbl.t;
    object_to_id: (string, Z.t) Hashtbl.t;
    id_to_subject: (Z.t, RDF_Graph_Executable.subject) Hashtbl.t;
    id_to_predicate: (Z.t, RDF_Graph_Executable.wf_iri) Hashtbl.t;
    id_to_object: (Z.t, RDF_Graph_Executable.rdf_term) Hashtbl.t;
  }

  let caches : (string, cache) Hashtbl.t = Hashtbl.create 17
  type predicate_bloom = {
    pb_bit_count: int;
    pb_hash_count: int;
    pb_bytes: bytes;
  }

  let bloom_cache : (string, predicate_bloom option) Hashtbl.t = Hashtbl.create 251
  let position_cache : ((string * Z.t * Z.t), Z.t list) Hashtbl.t = Hashtbl.create 251

  let get_cache path =
    match Hashtbl.find_opt caches path with
    | Some c -> c
    | None ->
      let c = {
        next_id = ref Z.one;
        subject_to_id = Hashtbl.create 251;
        predicate_to_id = Hashtbl.create 251;
        object_to_id = Hashtbl.create 251;
        id_to_subject = Hashtbl.create 251;
        id_to_predicate = Hashtbl.create 251;
        id_to_object = Hashtbl.create 251;
      } in
      Hashtbl.add caches path c;
      c

  let read_file path =
    let ic = open_in_bin path in
    Fun.protect
      ~finally:(fun () -> close_in_noerr ic)
      (fun () ->
         let len = in_channel_length ic in
         really_input_string ic len)

  let extract_json_int_field text key =
    let needle = "\"" ^ key ^ "\"" in
    try
      let key_pos = String.index_from text 0 needle.[0] in
      let rec find_key i =
        if i >= String.length text then raise Not_found
        else if i + String.length needle <= String.length text &&
                String.sub text i (String.length needle) = needle then i
        else find_key (i + 1) in
      let p = find_key key_pos in
      let colon = String.index_from text (p + String.length needle) ':' in
      let rec skip i =
        if i < String.length text &&
           (text.[i] = ' ' || text.[i] = '\n' || text.[i] = '\r' || text.[i] = '\t')
        then skip (i + 1) else i in
      let start = skip (colon + 1) in
      let rec finish i =
        if i < String.length text && text.[i] >= '0' && text.[i] <= '9'
        then finish (i + 1) else i in
      let stop = finish start in
      if stop = start then raise Not_found;
      int_of_string (String.sub text start (stop - start))
    with Not_found ->
      failwith ("Missing integer field in bloom metadata: " ^ key)

  let load_predicate_bloom artifact_path =
    let graph_dir = Filename.dirname artifact_path in
    let meta_path = Filename.concat graph_dir "graph.bloom.pred.json" in
    let bin_path = Filename.concat graph_dir "graph.bloom.pred.bin" in
    if Sys.file_exists meta_path && Sys.file_exists bin_path then
      let meta = read_file meta_path in
      let bit_count = extract_json_int_field meta "bit_count" in
      let hash_count = extract_json_int_field meta "hash_count" in
      let bytes = Bytes.of_string (read_file bin_path) in
      Some { pb_bit_count = Z.of_int bit_count; pb_hash_count = Z.of_int hash_count; pb_bytes = bytes }
    else
      None

  let get_predicate_bloom artifact_path =
    match Hashtbl.find_opt bloom_cache artifact_path with
    | Some bloom -> bloom
    | None ->
      let bloom = load_predicate_bloom artifact_path in
      Hashtbl.add bloom_cache artifact_path bloom;
      bloom

  let sha256_hex value =
    let cmd =
      Printf.sprintf "printf %%s %s | sha256sum | awk '{print $1}'"
        (Filename.quote value) in
    let ic = Unix.open_process_in cmd in
    Fun.protect
      ~finally:(fun () -> ignore (Unix.close_process_in ic))
      (fun () -> input_line ic)

  let hex_nibble c =
    match c with
    | '0' .. '9' -> Char.code c - Char.code '0'
    | 'a' .. 'f' -> 10 + Char.code c - Char.code 'a'
    | 'A' .. 'F' -> 10 + Char.code c - Char.code 'A'
    | _ -> failwith "Invalid hex digit in sha256 output"

  let bytes_of_hex hex =
    let len = String.length hex in
    if len mod 2 <> 0 then failwith "Odd-length hex digest";
    Bytes.init (len / 2) (fun i ->
      Char.chr ((hex_nibble hex.[2 * i] lsl 4) lor (hex_nibble hex.[2 * i + 1])))

  let z_of_bytes_slice b start len =
    let acc = ref Z.zero in
    for i = 0 to len - 1 do
      acc := Z.logor (Z.shift_left !acc 8) (Z.of_int (Char.code (Bytes.get b (start + i))))
    done;
    !acc

  let bloom_positions value m k =
    match Hashtbl.find_opt position_cache (value, m, k) with
    | Some ps -> ps
    | None ->
      let digest = bytes_of_hex (sha256_hex value) in
      let h1 = z_of_bytes_slice digest 0 16 in
      let h2_raw = z_of_bytes_slice digest 16 16 in
      let h2 = if Z.equal h2_raw Z.zero then Z.one else h2_raw in
      let rec loop i acc =
        if Z.equal i k then List.rev acc
        else
          let pos = Z.erem (Z.add h1 (Z.mul i h2)) m in
          loop (Z.succ i) (pos :: acc) in
      let ps = loop Z.zero [] in
      Hashtbl.add position_cache (value, m, k) ps;
      ps

  let bloom_test bloom value =
    List.for_all
      (fun bit_index_z ->
        let bit_index = Z.to_int bit_index_z in
        let byte_index = bit_index / 8 in
        let mask = 1 lsl (bit_index mod 8) in
        byte_index < Bytes.length bloom.pb_bytes &&
        ((Char.code (Bytes.get bloom.pb_bytes byte_index)) land mask) <> 0)
      (bloom_positions value bloom.pb_bit_count bloom.pb_hash_count)

  let fresh_id c =
    let id = !(c.next_id) in
    c.next_id := Z.succ id;
    id

  let subject_key = function
    | RDF_Graph_Executable.S_IRI i -> "I:" ^ i
    | RDF_Graph_Executable.S_BNode b -> "B:" ^ b

  let object_key = function
    | RDF_Graph_Executable.T_IRI i -> "I:" ^ i
    | RDF_Graph_Executable.T_BNode b -> "B:" ^ b
    | RDF_Graph_Executable.T_Literal l ->
      let lang = match l.RDF_Graph_Executable.lang_tag with
        | Some t -> t
        | None -> "" in
      "L:" ^ l.RDF_Graph_Executable.lexical_form ^ "|" ^ l.RDF_Graph_Executable.datatype ^ "|" ^ lang

  let intern_subject path s =
    let c = get_cache path in
    let k = subject_key s in
    match Hashtbl.find_opt c.subject_to_id k with
    | Some id -> id
    | None ->
      let id = fresh_id c in
      Hashtbl.add c.subject_to_id k id;
      Hashtbl.add c.id_to_subject id s;
      id

  let intern_predicate path p =
    let c = get_cache path in
    match Hashtbl.find_opt c.predicate_to_id p with
    | Some id -> id
    | None ->
      let id = fresh_id c in
      Hashtbl.add c.predicate_to_id p id;
      Hashtbl.add c.id_to_predicate id p;
      id

  let intern_object path o =
    let c = get_cache path in
    let k = object_key o in
    match Hashtbl.find_opt c.object_to_id k with
    | Some id -> id
    | None ->
      let id = fresh_id c in
      Hashtbl.add c.object_to_id k id;
      Hashtbl.add c.id_to_object id o;
      id

  let lookup_subject path id =
    match Hashtbl.find_opt (get_cache path).id_to_subject id with
    | Some s -> s
    | None -> failwith "Unknown HDT subject ref"

  let lookup_predicate path id =
    match Hashtbl.find_opt (get_cache path).id_to_predicate id with
    | Some p -> p
    | None -> failwith "Unknown HDT predicate ref"

  let lookup_object path id =
    match Hashtbl.find_opt (get_cache path).id_to_object id with
    | Some o -> o
    | None -> failwith "Unknown HDT object ref"

  let escape_literal s =
    let b = Buffer.create (String.length s + 8) in
    String.iter (function
      | '\\' -> Buffer.add_string b "\\\\"
      | '"' -> Buffer.add_string b "\\\""
      | '\n' -> Buffer.add_string b "\\n"
      | '\r' -> Buffer.add_string b "\\r"
      | '\t' -> Buffer.add_string b "\\t"
      | c -> Buffer.add_char b c
    ) s;
    Buffer.contents b

  let render_subject = function
    | RDF_Graph_Executable.S_IRI i -> i
    | RDF_Graph_Executable.S_BNode b -> "_:" ^ b

  let render_predicate p = p

  let render_object = function
    | RDF_Graph_Executable.T_IRI i -> i
    | RDF_Graph_Executable.T_BNode b -> "_:" ^ b
    | RDF_Graph_Executable.T_Literal l ->
      let base = "\"" ^ escape_literal l.RDF_Graph_Executable.lexical_form ^ "\"" in
      match l.RDF_Graph_Executable.lang_tag with
      | Some tag -> base ^ "@" ^ tag
      | None ->
        if l.RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_string then base
        else base ^ "^^<" ^ l.RDF_Graph_Executable.datatype ^ ">"

  let starts_with s prefix =
    String.length s >= String.length prefix &&
    String.sub s 0 (String.length prefix) = prefix

  let rec find_quote s i =
    if i >= String.length s then None
    else if s.[i] = '"' then
      let rec count_backslashes j acc =
        if j < 0 then acc
        else if s.[j] = '\\' then count_backslashes (j - 1) (acc + 1)
        else acc in
      let bs = count_backslashes (i - 1) 0 in
      if bs mod 2 = 0 then Some i else find_quote s (i + 1)
    else find_quote s (i + 1)

  let unescape_literal s =
    let b = Buffer.create (String.length s) in
    let rec loop i =
      if i >= String.length s then ()
      else if s.[i] <> '\\' then (Buffer.add_char b s.[i]; loop (i + 1))
      else if i + 1 >= String.length s then Buffer.add_char b '\\'
      else
        let c = s.[i + 1] in
        let out = match c with
          | 'n' -> '\n'
          | 'r' -> '\r'
          | 't' -> '\t'
          | '"' -> '"'
          | '\\' -> '\\'
          | _ -> c in
        Buffer.add_char b out;
        loop (i + 2)
    in
    loop 0;
    Buffer.contents b

  let parse_subject tok =
    if starts_with tok "_:" then
      RDF_Graph_Executable.S_BNode (String.sub tok 2 (String.length tok - 2))
    else
      RDF_Graph_Executable.S_IRI tok

  let parse_predicate tok = tok

  let parse_object tok =
    if tok = "" then failwith "Empty HDT object token";
    if starts_with tok "_:" then
      RDF_Graph_Executable.T_BNode (String.sub tok 2 (String.length tok - 2))
    else if tok.[0] = '"' then
      match find_quote tok 1 with
      | None -> failwith ("Malformed HDT literal: " ^ tok)
      | Some q ->
        let lex = unescape_literal (String.sub tok 1 (q - 1)) in
        let suffix =
          if q + 1 >= String.length tok then ""
          else String.sub tok (q + 1) (String.length tok - q - 1) in
        if starts_with suffix "@" then
          RDF_Graph_Executable.T_Literal {
            RDF_Graph_Executable.lexical_form = lex;
            datatype = RDF_Graph_Executable.rdf_lang_string;
            lang_tag = Some (String.sub suffix 1 (String.length suffix - 1));
          }
        else if starts_with suffix "^^<" && String.length suffix > 3 && suffix.[String.length suffix - 1] = '>' then
          let dt = String.sub suffix 3 (String.length suffix - 4) in
          RDF_Graph_Executable.T_Literal {
            RDF_Graph_Executable.lexical_form = lex;
            datatype = dt;
            lang_tag = None;
          }
        else if starts_with suffix "^^" then
          let dt = String.sub suffix 2 (String.length suffix - 2) in
          RDF_Graph_Executable.T_Literal {
            RDF_Graph_Executable.lexical_form = lex;
            datatype = dt;
            lang_tag = None;
          }
        else
          RDF_Graph_Executable.T_Literal {
            RDF_Graph_Executable.lexical_form = lex;
            datatype = RDF_Graph_Executable.xsd_string;
            lang_tag = None;
          }
    else
      RDF_Graph_Executable.T_IRI tok

  let parse_triple_line line =
    let line = String.trim line in
    if line = "" || starts_with line ">>" || starts_with line "HELP:" ||
       starts_with line "Index generated" || starts_with line "Predicate Bitmap" ||
       starts_with line "Count predicates" || starts_with line "Count Objects" ||
       starts_with line "Bitmap in" || starts_with line "Object references in" ||
       starts_with line "Sort object sublists" || starts_with line "Iterated " ||
       starts_with line "Could not parse triple pattern" then
      None
    else
      match String.index_opt line ' ' with
      | None -> None
      | Some s1 ->
        match String.index_from_opt line (s1 + 1) ' ' with
        | None -> None
        | Some s2 ->
          let subj = String.sub line 0 s1 in
          let pred = String.sub line (s1 + 1) (s2 - s1 - 1) in
          let obj = String.sub line (s2 + 1) (String.length line - s2 - 1) |> String.trim in
          Some (parse_subject subj, parse_predicate pred, parse_object obj)

  let run_hdt_search path pattern =
    let cmd = "hdtSearch " ^ Filename.quote path in
    let (ic, oc, ec) = Unix.open_process_full cmd (Unix.environment ()) in
    output_string oc pattern;
    output_char oc '\n';
    output_string oc "exit\n";
    flush oc;
    close_out oc;
    let rec collect ch acc =
      try
        let line = input_line ch in
        collect ch (line :: acc)
      with End_of_file -> List.rev acc in
    let out_lines = collect ic [] in
    let _err_lines = collect ec [] in
    let _ = Unix.close_process_full (ic, oc, ec) in
    List.filter_map parse_triple_line out_lines
end

let hdt_open_graph_store
  (graph_name : RDF_Graph_Executable.iri FStar_Pervasives_Native.option)
  (artifact_path : Prims.string)
  (summary : hdt_artifact_summary FStar_Pervasives_Native.option) :
  hdt_graph_store FStar_Pervasives_Native.option=
  FStar_Pervasives_Native.Some
    { hgs_graph_name = graph_name; hgs_artifact_path = artifact_path; hgs_summary = summary; hgs_handle = () }
let hdt_graph_summary (gs : hdt_graph_store) :
  hdt_artifact_summary FStar_Pervasives_Native.option=
  gs.hgs_summary
let hdt_encode_subject (gs : hdt_graph_store)
  (s : RDF_Graph_Executable.subject) :
  hdt_term_ref FStar_Pervasives_Native.option=
  FStar_Pervasives_Native.Some (Ballyhoo_hdt_runtime.intern_subject gs.hgs_artifact_path s)
let hdt_encode_predicate (gs : hdt_graph_store)
  (p : RDF_Graph_Executable.wf_iri) :
  hdt_term_ref FStar_Pervasives_Native.option=
  FStar_Pervasives_Native.Some (Ballyhoo_hdt_runtime.intern_predicate gs.hgs_artifact_path p)
let hdt_encode_object (gs : hdt_graph_store)
  (o : RDF_Graph_Executable.rdf_term) :
  hdt_term_ref FStar_Pervasives_Native.option=
  FStar_Pervasives_Native.Some (Ballyhoo_hdt_runtime.intern_object gs.hgs_artifact_path o)
let hdt_decode_subject (gs : hdt_graph_store) (id : hdt_term_ref) :
  RDF_Graph_Executable.subject=
  Ballyhoo_hdt_runtime.lookup_subject gs.hgs_artifact_path id
let hdt_decode_predicate (gs : hdt_graph_store) (id : hdt_term_ref) :
  RDF_Graph_Executable.wf_iri=
  Ballyhoo_hdt_runtime.lookup_predicate gs.hgs_artifact_path id
let hdt_decode_object (gs : hdt_graph_store) (id : hdt_term_ref) :
  RDF_Graph_Executable.rdf_term=
  Ballyhoo_hdt_runtime.lookup_object gs.hgs_artifact_path id
let hdt_search (gs : hdt_graph_store) (bound : hdt_bound_tp) :
  hdt_tp_row Prims.list=
  let path = gs.hgs_artifact_path in
  let subj_pat = match bound.hbt_s with
    | FStar_Pervasives_Native.None -> "?"
    | FStar_Pervasives_Native.Some id -> Ballyhoo_hdt_runtime.render_subject (Ballyhoo_hdt_runtime.lookup_subject path id) in
  let pred_pat = match bound.hbt_p with
    | FStar_Pervasives_Native.None -> "?"
    | FStar_Pervasives_Native.Some id -> Ballyhoo_hdt_runtime.render_predicate (Ballyhoo_hdt_runtime.lookup_predicate path id) in
  let obj_pat = match bound.hbt_o with
    | FStar_Pervasives_Native.None -> "?"
    | FStar_Pervasives_Native.Some id -> Ballyhoo_hdt_runtime.render_object (Ballyhoo_hdt_runtime.lookup_object path id) in
  let pattern = String.concat " " [subj_pat; pred_pat; obj_pat] in
  let triples = Ballyhoo_hdt_runtime.run_hdt_search path pattern in
  List.map (fun (s, p, o) ->
    { hrow_s = FStar_Pervasives_Native.Some (Ballyhoo_hdt_runtime.intern_subject path s);
      hrow_p = FStar_Pervasives_Native.Some (Ballyhoo_hdt_runtime.intern_predicate path p);
      hrow_o = FStar_Pervasives_Native.Some (Ballyhoo_hdt_runtime.intern_object path o) })
    triples
let hdt_estimate (gs : hdt_graph_store) (bound : hdt_bound_tp) :
  Prims.nat= Z.of_int (List.length (hdt_search gs bound))
let hdt_predicate_present (gs : hdt_graph_store)
  (pred : RDF_Graph_Executable.wf_iri) : Prims.bool=
  match Ballyhoo_hdt_runtime.get_predicate_bloom gs.hgs_artifact_path with
  | Some bloom ->
    Ballyhoo_hdt_runtime.bloom_test bloom pred
  | None ->
    let pid = Ballyhoo_hdt_runtime.intern_predicate gs.hgs_artifact_path pred in
    not (Z.equal
      (hdt_estimate gs { hbt_s = FStar_Pervasives_Native.None; hbt_p = FStar_Pervasives_Native.Some pid; hbt_o = FStar_Pervasives_Native.None })
      Z.zero)
let hdt_named_candidate_graphs (bindings : corpus_graph_binding Prims.list)
  (predicate_hint :
    RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  : corpus_graph_binding Prims.list=
  match predicate_hint with
  | FStar_Pervasives_Native.None -> bindings
  | FStar_Pervasives_Native.Some _ -> bindings
let hdt_build_bound_tp (gs : hdt_graph_store)
  (s : RDF_Graph_Executable.subject FStar_Pervasives_Native.option)
  (p : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (o : RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option) :
  hdt_bound_tp=
  {
    hbt_s =
      (match s with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some sv -> hdt_encode_subject gs sv);
    hbt_p =
      (match p with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some pv -> hdt_encode_predicate gs pv);
    hbt_o =
      (match o with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ov -> hdt_encode_object gs ov)
  }
let hdt_row_to_triple (gs : hdt_graph_store) (row : hdt_tp_row) :
  RDF_Graph_Executable.triple FStar_Pervasives_Native.option=
  match ((row.hrow_s), (row.hrow_p), (row.hrow_o)) with
  | (FStar_Pervasives_Native.Some sr, FStar_Pervasives_Native.Some pr,
     FStar_Pervasives_Native.Some orf) ->
      FStar_Pervasives_Native.Some
        {
          RDF_Graph_Executable.s = (hdt_decode_subject gs sr);
          RDF_Graph_Executable.p = (hdt_decode_predicate gs pr);
          RDF_Graph_Executable.o = (hdt_decode_object gs orf)
        }
  | uu___ -> FStar_Pervasives_Native.None
let rec hdt_rows_to_triples (gs : hdt_graph_store)
  (rows : hdt_tp_row Prims.list) : RDF_Graph_Executable.triple Prims.list=
  match rows with
  | [] -> []
  | row::rest ->
      let rest' = hdt_rows_to_triples gs rest in
      (match hdt_row_to_triple gs row with
       | FStar_Pervasives_Native.Some t -> t :: rest'
       | FStar_Pervasives_Native.None -> rest')
let hdt_search_triples (gs : hdt_graph_store)
  (s : RDF_Graph_Executable.subject FStar_Pervasives_Native.option)
  (p : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (o : RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option) :
  RDF_Graph_Executable.triple Prims.list=
  let bound = hdt_build_bound_tp gs s p o in
  hdt_rows_to_triples gs (hdt_search gs bound)
