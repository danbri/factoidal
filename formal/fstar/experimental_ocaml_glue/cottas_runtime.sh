#!/bin/bash
# Experimental runtime glue for Parser.BallyhooCOTTAS.ml
#
# The format semantics remain in F* through Parquet.Footer probing; this glue
# only materializes runtime caches and backend hooks from those verified probes.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

FILE="$OUTDIR/Parser_BallyhooCOTTAS.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Warning: $FILE not found, skipping Ballyhoo COTTAS runtime glue" >&2
  exit 0
fi

if grep -q 'module Ballyhoo_cottas_runtime' "$FILE"; then
  echo "  Ballyhoo COTTAS runtime glue already present."
  exit 0
fi

python3 - "$FILE" <<'PYEOF'
import sys
from pathlib import Path

path = Path(sys.argv[1])
content = path.read_text()

marker = """let cottas_open_dataset_store (artifact_path : Prims.string)
  (summary : cottas_artifact_summary FStar_Pervasives_Native.option) :
  cottas_dataset_store FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_open_dataset_store"
"""

runtime = r'''
module Ballyhoo_cottas_runtime = struct
  open Stdlib

  type quad_row = {
    qr_s: Z.t;
    qr_p: Z.t;
    qr_o: Z.t;
    qr_g: Z.t option;
  }

  type cache = {
    quads: quad_row list;
    subject_to_id: (string, Z.t) Hashtbl.t;
    predicate_to_id: (string, Z.t) Hashtbl.t;
    object_to_id: (string, Z.t) Hashtbl.t;
    graph_to_id: (string, Z.t) Hashtbl.t;
    id_to_subject: (Z.t, RDF_Graph_Executable.subject) Hashtbl.t;
    id_to_predicate: (Z.t, RDF_Graph_Executable.wf_iri) Hashtbl.t;
    id_to_object: (Z.t, RDF_Graph_Executable.rdf_term) Hashtbl.t;
    id_to_graph: (Z.t, RDF_Graph_Executable.iri) Hashtbl.t;
    (* Vav2 (2026-04-25): O(1) per-column id counters. The previous
       [next_id] walked all four hashtables (Hashtbl.fold) on every
       intern call -- O(N) per row per column, which was O(N^2) overall
       for the 3.14 M-quad parliament COTTAS load. Per-column monotonic
       counters preserve semantics (id spaces were never shared across
       columns -- decode functions dispatch off the column-typed
       hashtable) and make each intern O(1). Single-threaded load => no
       lock needed.
       Note: stored as Z.t ref because [open Prims] at file top shadows
       [int] with [Z.t]; using Z.t directly skips the conversion. *)
    subj_counter: Z.t ref;
    pred_counter: Z.t ref;
    obj_counter: Z.t ref;
    graph_counter: Z.t ref;
    summary: cottas_artifact_summary FStar_Pervasives_Native.option;
  }

  let caches : (string, cache) Hashtbl.t = Hashtbl.create 17

  let subject_key = function
    | RDF_Graph_Executable.S_IRI i -> "I:" ^ i
    | RDF_Graph_Executable.S_BNode b -> "B:" ^ b

  let object_key = function
    | RDF_Graph_Executable.T_IRI i -> "I:" ^ i
    | RDF_Graph_Executable.T_BNode b -> "B:" ^ b
    | RDF_Graph_Executable.T_Literal l ->
      let lang = match l.RDF_Graph_Executable.lang_tag with
        | FStar_Pervasives_Native.None -> ""
        | FStar_Pervasives_Native.Some tag -> tag in
      "L:" ^ l.RDF_Graph_Executable.lexical_form ^ "|" ^ l.RDF_Graph_Executable.datatype ^ "|" ^ lang

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

  let parse_literal_token s =
    if String.length s < 2 || s.[0] <> '"' then
      None
    else
      match find_unescaped_quote s with
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
        else
          None

  let parse_subject s =
    match parse_iri_token s with
    | Some iri -> Some (RDF_Graph_Executable.S_IRI iri)
    | None ->
      if String.length s >= 2 && String.sub s 0 2 = "_:" then
        Some (RDF_Graph_Executable.S_BNode (String.sub s 2 (String.length s - 2)))
      else
        None

  let parse_object s =
    match parse_iri_token s with
    | Some iri -> Some (RDF_Graph_Executable.T_IRI iri)
    | None ->
      if String.length s >= 2 && String.sub s 0 2 = "_:" then
        Some (RDF_Graph_Executable.T_BNode (String.sub s 2 (String.length s - 2)))
      else
        match parse_literal_token s with
        | Some lit -> Some (RDF_Graph_Executable.T_Literal lit)
        | None -> None

  let parse_graph s =
    if s = "DEFAULT" then Some None
    else match parse_iri_token s with
      | Some iri -> Some (Some iri)
      | None -> None

  (* Vav2 (2026-04-25): O(1) per-column allocators. Each call bumps a
     Z.t-valued counter and returns the prior value. Counters start at
     Z.one to preserve the previous behaviour (old [next_id] folded from
     Z.zero then Z.succ'd, so the first id was always Z.one). *)
  let alloc_subject_id cache =
    let id = !(cache.subj_counter) in
    cache.subj_counter := Z.succ id;
    id

  let alloc_predicate_id cache =
    let id = !(cache.pred_counter) in
    cache.pred_counter := Z.succ id;
    id

  let alloc_object_id cache =
    let id = !(cache.obj_counter) in
    cache.obj_counter := Z.succ id;
    id

  let alloc_graph_id cache =
    let id = !(cache.graph_counter) in
    cache.graph_counter := Z.succ id;
    id

  let intern_subject cache s =
    let key = subject_key s in
    match Hashtbl.find_opt cache.subject_to_id key with
    | Some id -> id
    | None ->
      let id = alloc_subject_id cache in
      Hashtbl.add cache.subject_to_id key id;
      Hashtbl.add cache.id_to_subject id s;
      id

  let intern_predicate cache p =
    match Hashtbl.find_opt cache.predicate_to_id p with
    | Some id -> id
    | None ->
      let id = alloc_predicate_id cache in
      Hashtbl.add cache.predicate_to_id p id;
      Hashtbl.add cache.id_to_predicate id p;
      id

  let intern_object cache o =
    let key = object_key o in
    match Hashtbl.find_opt cache.object_to_id key with
    | Some id -> id
    | None ->
      let id = alloc_object_id cache in
      Hashtbl.add cache.object_to_id key id;
      Hashtbl.add cache.id_to_object id o;
      id

  let intern_graph cache g =
    match Hashtbl.find_opt cache.graph_to_id g with
    | Some id -> id
    | None ->
      let id = alloc_graph_id cache in
      Hashtbl.add cache.graph_to_id g id;
      Hashtbl.add cache.id_to_graph id g;
      id

  let build_summary artifact_path quads graph_count =
    let num_quads = Z.of_int (List.length quads) in
    let row_groups =
      match Parquet_Footer.probe_parquet_row_group_count artifact_path with
      | FStar_Pervasives_Native.None -> Z.one
      | FStar_Pervasives_Native.Some n -> n in
    let mk_col kind =
      {
        ccs_kind = kind;
        ccs_num_values = num_quads;
        ccs_null_count = Z.zero;
        ccs_encoding = CE_Delta;
      } in
    FStar_Pervasives_Native.Some {
      cas_path = artifact_path;
      cas_num_quads = num_quads;
      cas_num_row_groups = row_groups;
      cas_dictionary =
        FStar_Pervasives_Native.Some {
          cds_num_terms = num_quads;
          cds_num_graphs = Z.of_int graph_count;
          cds_bytes_strings = Z.zero;
        };
      cas_row_groups = [{
        crgs_index = Z.zero;
        crgs_num_rows = num_quads;
        crgs_columns = [mk_col CC_Subject; mk_col CC_Predicate; mk_col CC_Object; mk_col CC_Graph];
      }];
    }

  (* Codex Phase 1 (2026-04-25): bulk per-column decode.
     Previously this loop did 4 per-cell calls per row × N rows
     (~12.6 M for the 3.14 M-quad parliament COTTAS), each of which
     re-decompressed the column page and re-walked every prior length —
     a per-column O(N^2) blowup.

     Bet5 / issue #98 Gap B (2026-04-25): walk every row group, not just
     the first. The F* helper `probe_parquet_column_decode_all_row_groups`
     dispatches per-row-group between DELTA_LENGTH_BYTE_ARRAY (cols 0+2:
     subjects + objects) and RLE_DICTIONARY (cols 1+3: predicates + graphs),
     concatenating the per-row-group results. For the 25-row-group
     parliament COTTAS we now load all 3.14 M rows instead of the first
     ~125 k. *)
  let decode_column artifact_path col_idx =
    match Parquet_Footer.probe_parquet_column_decode_all_row_groups
            artifact_path (Z.of_int col_idx) with
    | FStar_Pervasives_Native.None ->
      failwith (Printf.sprintf "Could not bulk-decode COTTAS column %d" col_idx)
    | FStar_Pervasives_Native.Some lst ->
      (* lst : (string option) list  in row order. Convert to an array of
         strings so the row-zip below is O(1) per row. *)
      let arr = Array.of_list lst in
      Array.map (function
        | FStar_Pervasives_Native.Some v -> v
        | FStar_Pervasives_Native.None ->
          failwith (Printf.sprintf "Missing COTTAS cell in column %d" col_idx))
        arr

  let load_cache artifact_path =
    match Hashtbl.find_opt caches artifact_path with
    | Some cache -> cache
    | None ->
      let s_col = decode_column artifact_path 0 in
      let p_col = decode_column artifact_path 1 in
      let o_col = decode_column artifact_path 2 in
      let g_col = decode_column artifact_path 3 in
      let value_count = Array.length s_col in
      if Array.length p_col <> value_count
         || Array.length o_col <> value_count
         || Array.length g_col <> value_count then
        failwith (Printf.sprintf
          "COTTAS column row counts disagree: s=%d p=%d o=%d g=%d"
          value_count (Array.length p_col) (Array.length o_col) (Array.length g_col));
      let cache = {
        quads = [];
        subject_to_id = Hashtbl.create 257;
        predicate_to_id = Hashtbl.create 257;
        object_to_id = Hashtbl.create 257;
        graph_to_id = Hashtbl.create 257;
        id_to_subject = Hashtbl.create 257;
        id_to_predicate = Hashtbl.create 257;
        id_to_object = Hashtbl.create 257;
        id_to_graph = Hashtbl.create 257;
        subj_counter = ref Z.one;
        pred_counter = ref Z.one;
        obj_counter = ref Z.one;
        graph_counter = ref Z.one;
        summary = FStar_Pervasives_Native.None;
      } in
      let quad_rev = ref [] in
      for i = 0 to value_count - 1 do
        let s = match parse_subject s_col.(i) with
          | Some v -> v | None -> failwith "Invalid COTTAS subject token" in
        let p = match parse_iri_token p_col.(i) with
          | Some v -> v | None -> failwith "Invalid COTTAS predicate token" in
        let o = match parse_object o_col.(i) with
          | Some v -> v | None -> failwith "Invalid COTTAS object token" in
        let g = match parse_graph g_col.(i) with
          | Some v -> v | None -> failwith "Invalid COTTAS graph token" in
        let s_id = intern_subject cache s in
        let p_id = intern_predicate cache p in
        let o_id = intern_object cache o in
        let g_id = match g with
          | None -> None
          | Some name -> Some (intern_graph cache name) in
        quad_rev := { qr_s = s_id; qr_p = p_id; qr_o = o_id; qr_g = g_id } :: !quad_rev
      done;
      let quads = List.rev !quad_rev in
      let summary = build_summary artifact_path quads (Hashtbl.length cache.graph_to_id) in
      let cache = { cache with quads; summary } in
      Hashtbl.add caches artifact_path cache;
      cache

  let cache_for_store ds = load_cache ds.cds_artifact_path

  let graph_name_of_ref cache id =
    match Hashtbl.find_opt cache.id_to_graph id with
    | Some g -> g
    | None -> failwith "Unknown COTTAS graph ref"

  let named_graphs_of_cache ds cache =
    Hashtbl.fold (fun id iri acc ->
      { cngs_name = iri; cngs_ref = id; cngs_dataset = ds } :: acc
    ) cache.id_to_graph []

  let search_rows ds bound =
    let cache = cache_for_store ds in
    let match_opt expected actual =
      match expected with
      | FStar_Pervasives_Native.None -> true
      | FStar_Pervasives_Native.Some e -> Z.equal e actual in
    (* issue #267: cbqp_g is the 3-way cottas_graph_bound. In the cache
       rows, qr_g = None is a default-graph row (the DEFAULT sentinel),
       Some id a named-graph row. *)
    let match_graph expected actual =
      match expected, actual with
      | CGB_Unbound, _ -> true
      | CGB_Default, None -> true
      | CGB_Default, Some _ -> false
      | CGB_Named e, Some a -> Z.equal e a
      | CGB_Named _, None -> false in
    List.fold_right (fun row acc ->
      if match_opt bound.cbqp_s row.qr_s &&
         match_opt bound.cbqp_p row.qr_p &&
         match_opt bound.cbqp_o row.qr_o &&
         match_graph bound.cbqp_g row.qr_g
      then
        {
          cqpr_s = FStar_Pervasives_Native.Some row.qr_s;
          cqpr_p = FStar_Pervasives_Native.Some row.qr_p;
          cqpr_o = FStar_Pervasives_Native.Some row.qr_o;
          cqpr_g = (match row.qr_g with None -> FStar_Pervasives_Native.None | Some g -> FStar_Pervasives_Native.Some g);
        } :: acc
      else
        acc
    ) cache.quads []
end

let cottas_open_dataset_store (artifact_path : Prims.string)
  (summary : cottas_artifact_summary FStar_Pervasives_Native.option) :
  cottas_dataset_store FStar_Pervasives_Native.option=
  let cache = Ballyhoo_cottas_runtime.load_cache artifact_path in
  FStar_Pervasives_Native.Some {
    cds_artifact_path = artifact_path;
    cds_summary =
      (match summary with
       | FStar_Pervasives_Native.Some s -> FStar_Pervasives_Native.Some s
       | FStar_Pervasives_Native.None -> cache.Ballyhoo_cottas_runtime.summary);
    cds_handle = ();
  }

let cottas_close_dataset_store (_ : cottas_dataset_store) : Prims.unit = ()

let cottas_dataset_summary (ds : cottas_dataset_store) :
  cottas_artifact_summary FStar_Pervasives_Native.option=
  (Ballyhoo_cottas_runtime.cache_for_store ds).Ballyhoo_cottas_runtime.summary

let cottas_named_graphs (ds : cottas_dataset_store) :
  cottas_named_graph_store Prims.list=
  let cache = Ballyhoo_cottas_runtime.cache_for_store ds in
  Ballyhoo_cottas_runtime.named_graphs_of_cache ds cache

(* cottas_lookup_named_graph (#448 wave 2, module 1): lifted to a real F*
   `let` in Parser.BallyhooCOTTAS.fst -- it was a pure linear scan over
   cottas_named_graphs with no I/O of its own. The F*-extracted body now
   provides it directly at its natural position further down this file;
   defining it again here would just be a dead shadow. *)

let cottas_encode_subject (ds : cottas_dataset_store)
  (s : RDF_Graph_Executable.subject) :
  cottas_term_ref FStar_Pervasives_Native.option=
  Hashtbl.find_opt (Ballyhoo_cottas_runtime.cache_for_store ds).Ballyhoo_cottas_runtime.subject_to_id
    (Ballyhoo_cottas_runtime.subject_key s)

let cottas_encode_predicate (ds : cottas_dataset_store)
  (p : RDF_Graph_Executable.wf_iri) :
  cottas_term_ref FStar_Pervasives_Native.option=
  Hashtbl.find_opt (Ballyhoo_cottas_runtime.cache_for_store ds).Ballyhoo_cottas_runtime.predicate_to_id p

let cottas_encode_object (ds : cottas_dataset_store)
  (o : RDF_Graph_Executable.rdf_term) :
  cottas_term_ref FStar_Pervasives_Native.option=
  Hashtbl.find_opt (Ballyhoo_cottas_runtime.cache_for_store ds).Ballyhoo_cottas_runtime.object_to_id
    (Ballyhoo_cottas_runtime.object_key o)

let cottas_encode_graph_name (ds : cottas_dataset_store)
  (g : RDF_Graph_Executable.iri) :
  cottas_graph_ref FStar_Pervasives_Native.option=
  Hashtbl.find_opt (Ballyhoo_cottas_runtime.cache_for_store ds).Ballyhoo_cottas_runtime.graph_to_id g

let cottas_decode_subject (ds : cottas_dataset_store)
  (id : cottas_term_ref) : RDF_Graph_Executable.subject=
  match Hashtbl.find_opt (Ballyhoo_cottas_runtime.cache_for_store ds).Ballyhoo_cottas_runtime.id_to_subject id with
  | Some s -> s
  | None -> failwith "Unknown COTTAS subject ref"

let cottas_decode_predicate (ds : cottas_dataset_store)
  (id : cottas_term_ref) : RDF_Graph_Executable.wf_iri=
  match Hashtbl.find_opt (Ballyhoo_cottas_runtime.cache_for_store ds).Ballyhoo_cottas_runtime.id_to_predicate id with
  | Some p -> p
  | None -> failwith "Unknown COTTAS predicate ref"

let cottas_decode_object (ds : cottas_dataset_store)
  (id : cottas_term_ref) : RDF_Graph_Executable.rdf_term=
  match Hashtbl.find_opt (Ballyhoo_cottas_runtime.cache_for_store ds).Ballyhoo_cottas_runtime.id_to_object id with
  | Some o -> o
  | None -> failwith "Unknown COTTAS object ref"

let cottas_decode_graph_name (ds : cottas_dataset_store)
  (id : cottas_graph_ref) : RDF_Graph_Executable.iri=
  (Ballyhoo_cottas_runtime.graph_name_of_ref (Ballyhoo_cottas_runtime.cache_for_store ds) id)

let cottas_search (ds : cottas_dataset_store) (bound : cottas_bound_qp) :
  cottas_qp_row Prims.list=
  Ballyhoo_cottas_runtime.search_rows ds bound

(* cottas_estimate (#448 wave 2, module 1): lifted to a real F* `let` in
   Parser.BallyhooCOTTAS.fst as `length (cottas_search ds bound)` -- that
   was exactly this glue's body, so the assumed signature was hiding an
   exact-count invariant it never stated. The F*-extracted body now
   provides it directly at its natural position further down this file;
   defining it again here would just be a dead shadow.

   cottas_predicate_present_in_graph and cottas_graph_candidates_for_predicate
   both (transitively) depend on cottas_estimate, and are now themselves
   lifted to real F* `let`s too (#448 wave 2, module 1) -- none of the four
   are stubs anymore, so none of them are defined in this block. All four
   are provided directly by F* extraction at their natural post-extraction
   position, in the order the .fst declares them (cottas_estimate first,
   since the other two call it -- an unbound-value forward reference within
   the same compilation unit otherwise). *)
'''

if marker not in content:
    raise SystemExit("cottas_open_dataset_store stub not found")
content = content.replace(marker, runtime, 1)

# The remaining assume vals' raw F*-extracted "Not yet implemented" stubs
# get deleted below; their real bodies already live in `runtime` above.
#
# #448 wave 2 module 1: this used to match each stub via an exact literal
# string keyed on its parameter types (e.g. "RDF_Graph_Executable.subject").
# A fresh from-scratch extraction showed F* now printing those same types
# qualified as "RDF_Term.subject" instead -- `subject`/`wf_iri`/`rdf_term`/
# `iri` are declared in RDF.Term and reach this module via `include` chains
# (RDF.Term -> RDF.Graph.Executable), and which qualifier F* prints for an
# `include`-inherited type in a plain assume-val signature is not something
# this glue script should have to track by hand. The literal-string keys
# silently stopped matching, so the stale stubs survived deletion and
# SHADOWED the real bodies above for any freshly re-extracted build -- an
# always-"Not yet implemented" regression that a normal incremental build
# never exercised because this module's .ml is rarely regenerated from
# scratch. Matching on the stub's failwith message instead (unique per
# function name, independent of argument-type qualifiers) survives that
# kind of drift.
#
# Every name below also has a REAL definition already sitting earlier in
# `content` (inserted by the `runtime` substitution above), with the same
# "let <name>" opening text -- so the match must be anchored to a
# *top-level* `let <name> ... = ...` block (bounded by the next top-level
# `let`, i.e. one starting at column 0) and then filtered to the one block
# among same-named occurrences that actually contains the failwith text.
# Matching "let name .*? failwith ...name" directly (unanchored on the
# following `let`) is wrong: for a name with both a real and a stub
# definition, the non-greedy `.*?` would swallow everything from the real
# definition's opening line through to the stub's failwith line, deleting
# every function in between.
import re

def stub_blocks(name):
    pat = re.compile(r"^let " + re.escape(name) + r"\b.*?(?=^let |\Z)",
                      re.DOTALL | re.MULTILINE)
    return list(pat.finditer(content))

def find_stub_block(name):
    marker_text = f'Not yet implemented: Parser.BallyhooCOTTAS.{name}"'
    hits = [b for b in stub_blocks(name) if marker_text in b.group(0)]
    if len(hits) != 1:
        raise SystemExit(
            f"cottas_runtime.sh: expected exactly 1 raw \"Not yet "
            f"implemented\" stub block for {name} in {path}, found "
            f"{len(hits)}. Either it was already lifted to a real F* "
            f"`let` in Parser.BallyhooCOTTAS.fst (remove it from this "
            f"list) or the stub's own text changed again -- do NOT let "
            f"this fall through silently, a missed delete leaves the raw "
            f"stub's failwith SHADOWING the real implementation above.")
    return hits[0]

def delete_stub(name):
    global content
    b = find_stub_block(name)
    content = content[:b.start()] + content[b.end():]

for name in [
    "cottas_dataset_summary",
    "cottas_named_graphs",
    "cottas_encode_subject",
    "cottas_encode_predicate",
    "cottas_encode_object",
    "cottas_encode_graph_name",
    "cottas_decode_subject",
    "cottas_decode_predicate",
    "cottas_decode_object",
    "cottas_decode_graph_name",
    "cottas_search",
]:
    delete_stub(name)

# cottas_predicate_present_in_graph and cottas_graph_candidates_for_predicate
# (#448 wave 2, module 1): both lifted to real F* `let`s in
# Parser.BallyhooCOTTAS.fst -- pure derivations of cottas_encode_predicate /
# cottas_estimate / cottas_named_graphs with no I/O of their own. Neither is
# a stub anymore, so there is nothing left for this script to delete or
# replace; the F*-extracted body provides both directly at their natural
# post-extraction position (see the comment on `runtime` above for why they
# were moved out of that block in the first place -- unchanged, they still
# need cottas_estimate's real definition to appear textually before them).

path.write_text(content)
PYEOF
