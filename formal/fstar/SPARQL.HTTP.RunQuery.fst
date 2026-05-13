module SPARQL.HTTP.RunQuery

(* Section F Commit 1 Sub-step 2 (2026-05-13): the actual `run_query`
   body, lifted from bin/factoidal-http/factoidal_http.ml:977-1076.
   See docs/designissues/2026-05-11-section-f-runquery-migration.md.
   The OCaml caller pre-evaluates ASK / SELECT / CONSTRUCT / DESCRIBE
   inside its own try/with (host-runtime exceptions are rule-#11(c)
   territory) and hands the option to F*. F* dispatches on q_form,
   applies the cap, picks the serialiser strategy + content-type,
   builds the body, and returns the response_body record. *)

(* Pure-F\* response-policy module for the SPARQL HTTP query path.
   #200 Section F (parse_and_run_timed + run_query MIXED-row migration).

   Per the SPARQL 1.1 Protocol spec (W3C Recommendation, 2013) §2.1 and
   the SPARQL 1.1 Query / Update Results spec, the server side has three
   concrete decisions to make per request:

     1. Parse error? Reply 400 with a plain-text error body.
     2. Evaluation error? Reply 500 with a plain-text error body
        (best-effort; covers OCaml-host exceptions in extracted
        evaluator code).
     3. Success? Pick the response serialiser based on the query form
        (ASK / SELECT / CONSTRUCT / DESCRIBE) and the negotiated
        response format (JSON / XML / CSV / TSV).

   This module owns those decisions in F\*. The OCaml glue at
   bin/factoidal-http/factoidal_http.ml's run_query / parse_and_run_timed
   reduces to:
     - call SPARQL11_Parser.parse_sparql, on ParseErr build a 400
       response from parse_error_status / parse_error_body /
       parse_error_content_type;
     - call the F\*-extracted evaluator, on OCaml exception build a 500
       response from eval_error_status / eval_error_body /
       eval_error_content_type;
     - on success, call serialiser_strategy_for query.q_form fmt, then
       dispatch the strategy enum to the actual SPARQL.Protocol
       serialiser. The dispatcher is a tiny finite match in OCaml
       (rule #15 — translating an F\* enum to host-language
       function-pointers).

   The MIXED rows in the boundary audit (`parse_and_run_timed` + `run_query`)
   become consumer-only after this lands: timing instrumentation,
   eprintf logging, evaluator invocation, exception catching, response
   wrapping. No semantic logic stays in OCaml. *)

open SPARQL.Protocol
open SPARQL.HTTP.Response

module Alg = SPARQL11.Algebra
module Lim = SPARQL.Eval.Limits

(* --- HTTP status codes for the SPARQL Protocol response policy ------ *)

let parse_error_status : nat = 400
let eval_error_status  : nat = 500
let success_status     : nat = 200

(* --- Error body templates ------------------------------------------- *)

(* Parse-error response: plain text describing the parser's complaint.
   Trailing newline matches existing OCaml output (preserved for any
   client diffing the response body literally). *)
let parse_error_body (msg : string) : Tot string =
  "SPARQL parse error: " ^ msg ^ "\n"

(* Evaluation-error response: plain text including the host exception
   message and (best-effort) backtrace. The backtrace is OCaml-runtime
   info that F\* doesn't synthesise; the OCaml side captures it via
   Printexc.get_backtrace and passes it in here. *)
let eval_error_body (msg : string) (backtrace : string) : Tot string =
  "Query evaluation error: " ^ msg ^ "\n" ^
  "Backtrace:\n" ^ backtrace

let parse_error_content_type : string = "text/plain; charset=utf-8"
let eval_error_content_type  : string = "text/plain; charset=utf-8"

(* --- Per-(form, format) serialiser strategy dispatch ---------------- *)

(* SPARQL Query Results spec defines four wire formats (JSON, XML, CSV,
   TSV) and three result shapes (boolean for ASK, solutions for SELECT,
   triples for CONSTRUCT/DESCRIBE). Not every (shape, format) pair has
   a defined serialiser:

     - ASK: JSON + XML have dedicated boolean-result serialisers
       (sparql-results-json §3.2 / sparql-results-xml §3.4); CSV/TSV
       are not defined for boolean results, so we fall back to JSON.
     - SELECT: all four formats are defined.
     - CONSTRUCT/DESCRIBE: triples should serialise to RDF formats
       (Turtle / N-Triples / etc.), not the SPARQL Results formats.
       The current evaluator's CONSTRUCT/DESCRIBE branch returns an
       empty solutions list and we serialise as SELECT — XML or JSON;
       CSV/TSV fall back to JSON. Real triples-output is a separate
       deliverable. *)

(* The strategy enum names the concrete SPARQL.Protocol serialiser
   the OCaml dispatcher should call. Six strategies for three shapes
   times the relevant formats per shape. *)
type serialiser_strategy =
  | SS_BooleanJson    (* serialise_response_boolean_json *)
  | SS_BooleanXml     (* serialise_response_boolean_xml *)
  | SS_RowsJson       (* serialise_response_json *)
  | SS_RowsXml        (* serialise_response_xml *)
  | SS_RowsCsv        (* serialise_response_csv *)
  | SS_RowsTsv        (* serialise_response_tsv *)

(* ASK: only JSON / XML defined; CSV/TSV fall back to JSON. *)
let serialiser_strategy_for_ask (fmt : response_format)
  : Tot (serialiser_strategy & string)
  =
  match fmt with
  | RF_Xml -> (SS_BooleanXml,  content_type_for RF_Xml)
  | _      -> (SS_BooleanJson, content_type_for RF_Json)

(* SELECT: all four formats defined. *)
let serialiser_strategy_for_select (fmt : response_format)
  : Tot (serialiser_strategy & string)
  =
  match fmt with
  | RF_Xml -> (SS_RowsXml, content_type_for RF_Xml)
  | RF_Csv -> (SS_RowsCsv, content_type_for RF_Csv)
  | RF_Tsv -> (SS_RowsTsv, content_type_for RF_Tsv)
  | _      -> (SS_RowsJson, content_type_for RF_Json)

(* CONSTRUCT / DESCRIBE: temporary fall-through to SELECT-shaped
   results until triples-output lands; only JSON / XML defined. *)
let serialiser_strategy_for_construct_describe (fmt : response_format)
  : Tot (serialiser_strategy & string)
  =
  match fmt with
  | RF_Xml -> (SS_RowsXml,  content_type_for RF_Xml)
  | _      -> (SS_RowsJson, content_type_for RF_Json)

(* --- Response-body constructors for the three error/cap paths --- *)
(* Section F Commit 1: the OCaml caller used to build these inline
   from the existing status/body/content-type primitives. Hoisting
   them into F* gives a single place where the response_body shape
   is assembled, and lets the OCaml glue shrink to a thin dispatch. *)

let make_parse_error_response (msg : string) : Tot response_body =
  { rb_status       = parse_error_status;
    rb_content_type = parse_error_content_type;
    rb_body         = parse_error_body msg }

let make_eval_error_response (msg : string) (backtrace : string)
  : Tot response_body =
  { rb_status       = eval_error_status;
    rb_content_type = eval_error_content_type;
    rb_body         = eval_error_body msg backtrace }

(* --- Result-cap response (HTTP 413) -------------------------------- *)
(* Strict-overflow encoding: caller passes max_rows; we build a cap of
   (max_rows + 1) and ask `cap_reached` whether the row count meets it.
   `n >= cap + 1` iff `n > cap`, so a result of exactly `max_rows`
   passes through and only `length > max_rows` fires the 413. Matches
   the long-standing OCaml `exceeds_cap` semantics at
   factoidal_http.ml:958-966. *)
let row_count_overflows (max_rows : nat) (rows : list binding_row) : Tot bool =
  let strict_cap = Lim.mk_cap (max_rows + 1) in
  Lim.cap_reached strict_cap (FStar.List.Tot.length rows)

let make_result_cap_response (max_rows : nat) : Tot response_body =
  { rb_status       = 413;
    rb_content_type = "application/json; charset=utf-8";
    rb_body         = result_cap_response_body max_rows }

(* --- Strategy → body dispatch -------------------------------------- *)
(* Tiny finite-match helpers. Total. Kept private; the public surface
   below dispatches on q_form and routes through these. *)

let body_for_ask_strategy (strat : serialiser_strategy) (b : bool) : Tot string =
  match strat with
  | SS_BooleanXml  -> serialise_response_boolean_xml b
  | _              -> serialise_response_boolean_json b

let body_for_rows_strategy
    (strat : serialiser_strategy)
    (vars : list string)
    (rows : list binding_row)
  : Tot string =
  match strat with
  | SS_RowsXml  -> serialise_response_xml  vars rows
  | SS_RowsCsv  -> serialise_response_csv  vars rows
  | SS_RowsTsv  -> serialise_response_tsv  vars rows
  | _           -> serialise_response_json vars rows

(* --- Public entry point: run_query --------------------------------- *)
(* Replaces the OCaml-side dispatch body at factoidal_http.ml:977-1076.
   The OCaml caller:
     - parses Accept header into a `response_format` via SPARQL.Protocol;
     - pre-evaluates the query inside try/with (host-runtime exceptions
       are rule-#11(c) territory) and passes the option;
     - on parse error, builds the response from
       `make_parse_error_response` directly without calling here;
     - on eval exception, builds from `make_eval_error_response` directly.

   Returns the constructed `response_body` for any q_form. *)
let run_query
    (qform : Alg.query_form)
    (fmt : response_format)
    (max_rows : nat)
    (vars : list string)
    (ask_result : option bool)
    (rows_result : option (list binding_row))
  : Tot response_body =
  match qform with
  | Alg.QF_Ask ->
    let b = match ask_result with | Some v -> v | None -> false in
    let (strat, ct) = serialiser_strategy_for_ask fmt in
    { rb_status       = success_status;
      rb_content_type = ct;
      rb_body         = body_for_ask_strategy strat b }
  | Alg.QF_Select _ ->
    let rows = match rows_result with | Some r -> r | None -> [] in
    if row_count_overflows max_rows rows then
      make_result_cap_response max_rows
    else
      let (strat, ct) = serialiser_strategy_for_select fmt in
      { rb_status       = success_status;
        rb_content_type = ct;
        rb_body         = body_for_rows_strategy strat vars rows }
  | Alg.QF_Construct _ | Alg.QF_Describe _ ->
    let rows = match rows_result with | Some r -> r | None -> [] in
    if row_count_overflows max_rows rows then
      make_result_cap_response max_rows
    else
      let (strat, ct) = serialiser_strategy_for_construct_describe fmt in
      { rb_status       = success_status;
        rb_content_type = ct;
        rb_body         = body_for_rows_strategy strat vars rows }
