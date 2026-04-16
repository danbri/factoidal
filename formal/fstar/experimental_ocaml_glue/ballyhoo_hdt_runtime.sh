#!/bin/bash
# Experimental runtime glue for Parser.BallyhooHDT.ml
#
# This is intentionally outside minimal_regrettable_glue_code_each_with_an_open_issue/
# because it is an experimental backend adapter, not project-semantic glue that
# already has a corresponding elimination issue.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

FILE="$OUTDIR/Parser_BallyhooHDT.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Warning: $FILE not found, skipping Ballyhoo HDT runtime glue" >&2
  exit 0
fi

if grep -q 'module Ballyhoo_hdt_runtime' "$FILE"; then
  echo "  Ballyhoo HDT runtime glue already present."
  exit 0
fi

python3 - "$FILE" <<'PYEOF'
import sys
from pathlib import Path

path = Path(sys.argv[1])
content = path.read_text()

marker = """let hdt_open_graph_store
  (graph_name : RDF_Graph_Executable.iri FStar_Pervasives_Native.option)
  (artifact_path : Prims.string)
  (summary : hdt_artifact_summary FStar_Pervasives_Native.option) :
  hdt_graph_store FStar_Pervasives_Native.option=
  failwith "Not yet implemented: Parser.BallyhooHDT.hdt_open_graph_store"
"""

runtime = r'''
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
'''

content = content.replace(marker, runtime)

replacements = {
'''let hdt_graph_summary (uu___ : hdt_graph_store) :
  hdt_artifact_summary FStar_Pervasives_Native.option=
  failwith "Not yet implemented: Parser.BallyhooHDT.hdt_graph_summary"
''':
'''let hdt_graph_summary (gs : hdt_graph_store) :
  hdt_artifact_summary FStar_Pervasives_Native.option=
  gs.hgs_summary
''',
'''let hdt_encode_subject (uu___ : hdt_graph_store)
  (uu___1 : RDF_Graph_Executable.subject) :
  hdt_term_ref FStar_Pervasives_Native.option=
  failwith "Not yet implemented: Parser.BallyhooHDT.hdt_encode_subject"
''':
'''let hdt_encode_subject (gs : hdt_graph_store)
  (s : RDF_Graph_Executable.subject) :
  hdt_term_ref FStar_Pervasives_Native.option=
  FStar_Pervasives_Native.Some (Ballyhoo_hdt_runtime.intern_subject gs.hgs_artifact_path s)
''',
'''let hdt_encode_predicate (uu___ : hdt_graph_store)
  (uu___1 : RDF_Graph_Executable.wf_iri) :
  hdt_term_ref FStar_Pervasives_Native.option=
  failwith "Not yet implemented: Parser.BallyhooHDT.hdt_encode_predicate"
''':
'''let hdt_encode_predicate (gs : hdt_graph_store)
  (p : RDF_Graph_Executable.wf_iri) :
  hdt_term_ref FStar_Pervasives_Native.option=
  FStar_Pervasives_Native.Some (Ballyhoo_hdt_runtime.intern_predicate gs.hgs_artifact_path p)
''',
'''let hdt_encode_object (uu___ : hdt_graph_store)
  (uu___1 : RDF_Graph_Executable.rdf_term) :
  hdt_term_ref FStar_Pervasives_Native.option=
  failwith "Not yet implemented: Parser.BallyhooHDT.hdt_encode_object"
''':
'''let hdt_encode_object (gs : hdt_graph_store)
  (o : RDF_Graph_Executable.rdf_term) :
  hdt_term_ref FStar_Pervasives_Native.option=
  FStar_Pervasives_Native.Some (Ballyhoo_hdt_runtime.intern_object gs.hgs_artifact_path o)
''',
'''let hdt_decode_subject (uu___ : hdt_graph_store) (uu___1 : hdt_term_ref) :
  RDF_Graph_Executable.subject=
  failwith "Not yet implemented: Parser.BallyhooHDT.hdt_decode_subject"
''':
'''let hdt_decode_subject (gs : hdt_graph_store) (id : hdt_term_ref) :
  RDF_Graph_Executable.subject=
  Ballyhoo_hdt_runtime.lookup_subject gs.hgs_artifact_path id
''',
'''let hdt_decode_predicate (uu___ : hdt_graph_store) (uu___1 : hdt_term_ref) :
  RDF_Graph_Executable.wf_iri=
  failwith "Not yet implemented: Parser.BallyhooHDT.hdt_decode_predicate"
''':
'''let hdt_decode_predicate (gs : hdt_graph_store) (id : hdt_term_ref) :
  RDF_Graph_Executable.wf_iri=
  Ballyhoo_hdt_runtime.lookup_predicate gs.hgs_artifact_path id
''',
'''let hdt_decode_object (uu___ : hdt_graph_store) (uu___1 : hdt_term_ref) :
  RDF_Graph_Executable.rdf_term=
  failwith "Not yet implemented: Parser.BallyhooHDT.hdt_decode_object"
''':
'''let hdt_decode_object (gs : hdt_graph_store) (id : hdt_term_ref) :
  RDF_Graph_Executable.rdf_term=
  Ballyhoo_hdt_runtime.lookup_object gs.hgs_artifact_path id
''',
'''let hdt_search (uu___ : hdt_graph_store) (uu___1 : hdt_bound_tp) :
  hdt_tp_row Prims.list=
  failwith "Not yet implemented: Parser.BallyhooHDT.hdt_search"
''':
'''let hdt_search (gs : hdt_graph_store) (bound : hdt_bound_tp) :
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
''',
'''let hdt_estimate (uu___ : hdt_graph_store) (uu___1 : hdt_bound_tp) :
  Prims.nat= failwith "Not yet implemented: Parser.BallyhooHDT.hdt_estimate"
''':
'''let hdt_estimate (gs : hdt_graph_store) (bound : hdt_bound_tp) :
  Prims.nat= Z.of_int (List.length (hdt_search gs bound))
''',
'''let hdt_predicate_present (uu___ : hdt_graph_store)
  (uu___1 : RDF_Graph_Executable.wf_iri) : Prims.bool=
  failwith "Not yet implemented: Parser.BallyhooHDT.hdt_predicate_present"
''':
'''let hdt_predicate_present (gs : hdt_graph_store)
  (pred : RDF_Graph_Executable.wf_iri) : Prims.bool=
  match Ballyhoo_hdt_runtime.get_predicate_bloom gs.hgs_artifact_path with
  | Some bloom ->
    Ballyhoo_hdt_runtime.bloom_test bloom pred
  | None ->
    let pid = Ballyhoo_hdt_runtime.intern_predicate gs.hgs_artifact_path pred in
    not (Z.equal
      (hdt_estimate gs { hbt_s = FStar_Pervasives_Native.None; hbt_p = FStar_Pervasives_Native.Some pid; hbt_o = FStar_Pervasives_Native.None })
      Z.zero)
''',
'''let hdt_named_candidate_graphs (bindings : corpus_graph_binding Prims.list)
  (predicate_hint :
    RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  : corpus_graph_binding Prims.list=
  failwith
    "Not yet implemented: Parser.BallyhooHDT.hdt_named_candidate_graphs"
''':
'''let hdt_named_candidate_graphs (bindings : corpus_graph_binding Prims.list)
  (predicate_hint :
    RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  : corpus_graph_binding Prims.list=
  match predicate_hint with
  | FStar_Pervasives_Native.None -> bindings
  | FStar_Pervasives_Native.Some _ -> bindings
'''
}

for old, new in replacements.items():
    if old not in content:
        raise SystemExit(f"Expected snippet not found for replacement:\\n{old}")
    content = content.replace(old, new)

path.write_text(content)
PYEOF

echo "  Ballyhoo HDT runtime glue applied."
