module SPARQL.HTTP.Timing

(* Section F Commit 1 (2026-05-13). Per-query timing record, hosted in F*
   instead of the OCaml-side `query_timing` previously at
   `bin/factoidal-http/factoidal_http.ml:1091-1100`.

   Float fields (parse_ms, eval_ms, format_ms, total_ms) are stored as
   already-formatted strings because F* has no native `float` formatter
   — the OCaml glue calls `Printf.sprintf "%.1f"` once at the boundary
   and the F* renderers (in `SPARQL.HTTP.Admin`) consume the strings
   verbatim. Same convention as the existing `serialise_response_*`
   string-typed payloads. Rule-#11(c) classification: the float→string
   formatting is consumer-side instrumentation, not semantic logic.

   Tracking: docs/designissues/2026-05-11-section-f-runquery-migration.md *)

type query_timing = {
  qt_parse_ms_str  : string;   (* "%.1f"-formatted by OCaml glue *)
  qt_eval_ms_str   : string;
  qt_format_ms_str : string;
  qt_total_ms_str  : string;
  qt_status        : nat;
  qt_rows          : int;       (* -1 = unknown (ASK / parse-error) *)
  qt_form          : string;    (* "SELECT" / "ASK" / "parse-error" / ... *)
  qt_body_bytes    : nat;
}

(* Constants for the q_form string field — keeps the render-side
   string compares against well-known literals. *)
let form_select       : string = "SELECT"
let form_ask          : string = "ASK"
let form_construct    : string = "CONSTRUCT"
let form_describe     : string = "DESCRIBE"
let form_parse_error  : string = "parse-error"
let form_eval_error   : string = "eval-error"

(* Sentinel for the row-count field on ASK queries (no rows) and on
   parse-error responses (no eval happened). *)
let rows_unknown : int = -1

(* Zero record — used by the OCaml glue to initialise a timing accumulator
   before the parse + eval + format passes fill in the fields. Total. *)
let zero_timing : query_timing = {
  qt_parse_ms_str  = "0.0";
  qt_eval_ms_str   = "0.0";
  qt_format_ms_str = "0.0";
  qt_total_ms_str  = "0.0";
  qt_status        = 0;
  qt_rows          = rows_unknown;
  qt_form          = form_parse_error;
  qt_body_bytes    = 0;
}
