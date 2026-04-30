module SPARQL.HTTP.BackendInfo

// /backend-info.json renderer.
//
// Migrated from factoidal_http.ml's `serve_backend_info_json` body
// (rule #1 / rule #11 - F-star is the source of truth; aggregation
// rule is auditable in F-star rather than buried in OCaml glue).
//
// The OCaml side keeps the I/O syscalls (Sys.readdir, Unix mtime,
// reading the live dataset_ref / cottas_stores_ref). It collects the
// observed state into a `backend_info` record and hands that record
// to `render_backend_info`, which builds the JSON byte string.
//
// Aggregation rule for the top-level "triples" field:
//
//   total = bi_in_memory_triples + sum (cs_quads of bi_cottas)
//
// This is a sum (NOT max, NOT first). Reviewer 2026-04-26 flagged
// that an earlier draft of the OCaml code under-reported "triples":0
// for a --data-cottas-only daemon despite COUNT-star returning 3.14M.
// The OCaml code was patched to do this sum at the same time it was
// migrated; this F-star module enforces the rule at extraction time
// so it cannot silently regress.
//
// Output bytes are intended to be byte-for-byte identical to the
// previous hand-written OCaml `Printf.sprintf` template, including:
//   - field order
//   - lack of whitespace between fields
//   - trailing newline
//   - lowercase hex escapes via SPARQL.JSON.Escape.json_escape

open SPARQL.JSON.Escape

type backend_kind =
  | BK_InMem
  | BK_CottasOnDisk
  | BK_Hybrid
  | BK_Empty

let backend_kind_string (k:backend_kind) : string =
  match k with
  | BK_InMem        -> "in-memory"
  | BK_CottasOnDisk -> "binary"
  | BK_Hybrid       -> "mixed"
  | BK_Empty        -> "empty"

type cottas_summary = {
  cs_path       : string;
  cs_quads      : int;
  cs_row_groups : int;
}

type backend_info = {
  bi_kind                            : backend_kind;
  bi_source                          : string;
  bi_in_memory_triples               : int;
  bi_in_memory_default_graph_triples : int;
  bi_in_memory_named_graphs          : int;
  bi_in_memory_named_graph_triples   : int;
  bi_cottas                          : list cottas_summary;
}

let rec sum_cottas_quads (xs:list cottas_summary) : int =
  match xs with
  | [] -> 0
  | x :: rest -> x.cs_quads + sum_cottas_quads rest

let render_backend_info (info:backend_info) : string =
  let cottas_quads = sum_cottas_quads info.bi_cottas in
  let n_files = FStar.List.Tot.length info.bi_cottas in
  let triples_total = info.bi_in_memory_triples + cottas_quads in
  let kind_s = json_escape (backend_kind_string info.bi_kind) in
  let source_s = json_escape info.bi_source in
  String.concat "" [
    "{\"kind\":\""; kind_s;
    "\",\"triples\":"; string_of_int triples_total;
    ",\"in_memory_triples\":"; string_of_int info.bi_in_memory_triples;
    ",\"in_memory_default_graph_triples\":"; string_of_int info.bi_in_memory_default_graph_triples;
    ",\"in_memory_named_graphs\":"; string_of_int info.bi_in_memory_named_graphs;
    ",\"in_memory_named_graph_triples\":"; string_of_int info.bi_in_memory_named_graph_triples;
    ",\"cottas_triples\":"; string_of_int cottas_quads;
    ",\"cottas_files\":"; string_of_int n_files;
    ",\"source\":\""; source_s;
    "\"}\n"
  ]
