module SPARQL.HTTP.QueriesIndex

open FStar.List.Tot
open Parser.FastString
open SPARQL.JSON.Escape

// JSON manifest renderer for the /parliament-queries.json endpoint.
//
// The OCaml side (factoidal_http.ml) keeps the filesystem I/O — directory
// resolution, Sys.readdir, read_file — because that is pure I/O glue
// (rule #15). The OCaml side also keeps the per-group label-prefixing
// policy ("Vendored - foo" vs "Modernised - foo") because that decides
// which tree the entry came from.
//
// This module owns the byte shape of the emitted JSON. Every string field
// is run through SPARQL.JSON.Escape.json_escape (already F*-extracted),
// which guarantees the escaping algorithm matches the previous OCaml
// hand-written escape byte-for-byte. The shape is one entry per object
// with fields {group, key, label, body} in that order, separated by
// "," and wrapped in "[...]\n".
//
// Migration of factoidal_http.ml's build_parliament_queries_json into
// F-star (rule #1 -- F-star is the source of truth). Step 4 of the
// factoidal_http.ml unwind series.

// One entry in the manifest. `qe_group` is the rendered group label
// ("Vendored", "Modernised", ...). `qe_key` is the dropdown key.
// `qe_label` is the human-readable label (already prefixed by the caller,
// e.g. "Vendored - main / 03 ...").  `qe_body` is the .rq file body.
type query_entry = {
  qe_group : string;
  qe_key   : string;
  qe_label : string;
  qe_body  : string;
}

// The OCaml side packages entries into groups, but for byte-for-byte
// compatibility with the previous output we just flatten and emit them
// in order. We expose `query_group` so the caller can keep the grouped
// shape if it wants to, but `render_queries_index` only needs the list.
type query_group = {
  qg_name    : string;
  qg_entries : list query_entry;
}

// Strip the .rq suffix from a filename. Total: if there is no suffix,
// the input is returned unchanged. Used by the OCaml caller to derive
// the dropdown key, but kept here so the spec is the single source.
//
// We deliberately do not parse the SPARQL body -- the filename is the
// canonical handle for these fixture queries.
val strip_rq_suffix : string -> string
let strip_rq_suffix s =
  let len = fs_byte_length s in
  if len < 3 then s
  else
    let b0 = fs_byte_at s (len - 3) in
    let b1 = fs_byte_at s (len - 2) in
    let b2 = fs_byte_at s (len - 1) in
    // ".rq" = 0x2E 0x72 0x71
    if b0 = 0x2E && b1 = 0x72 && b2 = 0x71
    then fs_byte_sub s 0 (len - 3)
    else s

// Build the human-readable label for a vendored entry. Mirrors the OCaml
// `parliament_label ~group ~filename` exactly: "<group> / <stem>".
val parliament_label : string -> string -> string
let parliament_label group filename =
  group ^ " / " ^ strip_rq_suffix filename

// Render one entry as a JSON object. Reverse-prepends bytes onto the
// caller's accumulator (a string list); caller concatenates at the end.
let render_entry_chars (e:query_entry) : string =
  "  {\"group\":\"" ^ json_escape e.qe_group
  ^ "\",\"key\":\""   ^ json_escape e.qe_key
  ^ "\",\"label\":\"" ^ json_escape e.qe_label
  ^ "\",\"body\":\""  ^ json_escape e.qe_body
  ^ "\"}"

// Render the comma-separated body of the array. Each entry is preceded
// by ",\n" except the first, which is preceded by "\n". This matches
// the OCaml Buffer-based emission in build_parliament_queries_json.
let rec render_entries_acc (entries:list query_entry) (first:bool) (acc:string)
  : Tot string (decreases entries)
  =
  match entries with
  | [] -> acc
  | e :: rest ->
    let sep = if first then "\n" else ",\n" in
    let acc' = acc ^ sep ^ render_entry_chars e in
    render_entries_acc rest false acc'

// Top-level renderer. Takes a flat list of entries (already in the order
// they should appear) and returns the full JSON string ending in "\n".
val render_queries_index : list query_entry -> string
let render_queries_index entries =
  let body = render_entries_acc entries true "" in
  "[" ^ body ^ "\n]\n"

// Convenience: flatten a list of groups into the entry list. Pure
// concatenation in group order. The OCaml caller can use this if it
// prefers to build groups; the byte output is the same as if it had
// concatenated entries itself.
val flatten_groups : list query_group -> list query_entry
let rec flatten_groups groups =
  match groups with
  | [] -> []
  | g :: rest -> g.qg_entries @ flatten_groups rest
