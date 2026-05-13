module SPARQL.HTTP.RunQuery

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
