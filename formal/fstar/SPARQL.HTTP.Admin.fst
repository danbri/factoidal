module SPARQL.HTTP.Admin

// /admin/recent.json renderer.
//
// Migrated from factoidal_http.ml's `recent_query_to_json` and
// `serve_recent_queries_json` JSON template (PR #136 added the
// per-stage query-timing infrastructure; the JSON shape is the
// public API for the /admin/recent.json endpoint and belongs in F\*
// per Iron Rule #1).
//
// We deliberately don't lift the OCaml record types `recent_query`
// and `query_timing` into F\* — the OCaml side owns the
// Mutex-protected ring buffer and the gettimeofday timestamps;
// the F\* side just renders. Each F\* function takes the field
// values as primitives.
//
// The query text is JSON-escaped on the OCaml side before being
// passed in — that uses SPARQL.JSON.Escape.json_escape (PR #126).
//
// Output format (byte-for-byte identical to the legacy OCaml
// Printf templates):
//
//   recent_query_to_json:
//     {"started_at":<float>,"query":"<escaped>","form":"<form>",
//      "status":<int>,"rows":<int>,"body_bytes":<int>,
//      "parse_ms":<float>,"eval_ms":<float>,"format_ms":<float>,
//      "total_ms":<float>}
//
//   recent_queries_envelope:
//     {"total_queries_seen":<int>,"total_wall_ms":<float>,
//      "status_2xx":<int>,"status_4xx":<int>,"status_5xx":<int>,
//      "recent":[<rq_json>,...]}\n

open FStar.List.Tot
open SPARQL.JSON.Escape

// ---------------------------------------------------------------
// Float -> string. F\*'s standard library doesn't ship a string-
// formatter for FStar.Float.float that matches OCaml's "%.3f" /
// "%.2f" / "%.1f" exactly. Keeping the OCaml caller responsible
// for the float-to-string conversion (it's a Printf %.Nf) lets
// us preserve the legacy bytes without porting OCaml's Printf
// FP rounding into F\*. The F\* function takes already-formatted
// strings.
// ---------------------------------------------------------------

let render_recent_query_json
    (started_at_str   : string)   // pre-formatted "%.3f"
    (query_escaped    : string)   // already JSON-escaped
    (form             : string)
    (status           : int)
    (rows             : int)
    (body_bytes       : int)
    (parse_ms_str     : string)   // pre-formatted "%.2f"
    (eval_ms_str      : string)
    (format_ms_str    : string)
    (total_ms_str     : string)
  : Tot string =
  "{\"started_at\":" ^ started_at_str
  ^ ",\"query\":\"" ^ query_escaped
  ^ "\",\"form\":\"" ^ form
  ^ "\",\"status\":" ^ string_of_int status
  ^ ",\"rows\":" ^ string_of_int rows
  ^ ",\"body_bytes\":" ^ string_of_int body_bytes
  ^ ",\"parse_ms\":" ^ parse_ms_str
  ^ ",\"eval_ms\":" ^ eval_ms_str
  ^ ",\"format_ms\":" ^ format_ms_str
  ^ ",\"total_ms\":" ^ total_ms_str
  ^ "}"

// ---------------------------------------------------------------
// Render the envelope around a list of pre-rendered recent_query
// JSON object strings. The OCaml caller passes the per-query
// strings already formatted (each via render_recent_query_json
// above); this function adds the surrounding counters and the
// "recent" array.
// ---------------------------------------------------------------

let rec join_array_elements (xs : list string) : Tot string (decreases xs) =
  match xs with
  | [] -> ""
  | [x] -> x
  | x :: rest -> x ^ "," ^ join_array_elements rest

let render_recent_queries_envelope
    (total_queries_seen : int)
    (total_wall_ms_str  : string)   // pre-formatted "%.1f"
    (status_2xx         : int)
    (status_4xx         : int)
    (status_5xx         : int)
    (recent_jsons       : list string)
  : Tot string =
  "{\"total_queries_seen\":" ^ string_of_int total_queries_seen
  ^ ",\"total_wall_ms\":" ^ total_wall_ms_str
  ^ ",\"status_2xx\":" ^ string_of_int status_2xx
  ^ ",\"status_4xx\":" ^ string_of_int status_4xx
  ^ ",\"status_5xx\":" ^ string_of_int status_5xx
  ^ ",\"recent\":[" ^ join_array_elements recent_jsons
  ^ "]}\n"
