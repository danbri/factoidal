module SPARQL.Service.Wrap

(** ======================================================================== **)
(** Virtual sources, Part A, Stages 1-2 — the "wrap+http(s):" SERVICE       **)
(** resolver (docs/designissues/2026-07-06-virtual-sources-design.md).      **)
(**                                                                          **)
(** This module is PURE F* — no I/O, no new `assume val`. Per the design    **)
(** doc §2.5/§4/§6: `SPARQL11.Algebra.fst`'s `service_endpoint_lookup`      **)
(** stays an `assume val` with the SAME signature; its OCaml realisation    **)
(** (a disclosed extension of                                               **)
(** `minimal_regrettable_glue_code_each_with_an_open_issue/57_service_client_bind.sh`,**)
(** issue #57 family) consults a small forward-ref hook that a NEW,         **)
(** hand-written, ASSUME-IO-class glue file (`ocaml-output/service_wrap_http.ml`, **)
(** no corresponding `.fst` — same footing as the existing                  **)
(** `ocaml-output/fstar_pure_hashes.ml`) wires up. That glue file does      **)
(** socket I/O + env/config plumbing ONLY; every decision this doc calls    **)
(** out as "must be F*" — wrap+ IRI recognition, control-fragment parsing,  **)
(** format detection, the default Facade-X-equivalent mapping, and the      **)
(** `rml=` override dispatch — lives here.                                  **)
(**                                                                          **)
(** Why this module sits AFTER SPARQL11.Algebra.fst in the module DAG (and  **)
(** hence cannot be `open`ed BY it): `RML.Eval.fst` itself already opens    **)
(** `SPARQL11.Algebra` (percent/URI-encoding reuse), so anything needing    **)
(** RML.Eval — which Stage 2's `rml=` override does — is structurally      **)
(** downstream of SPARQL11.Algebra. The OCaml-side forward-ref-hook pattern **)
(** (a mutable ref cell declared in `SPARQL11_Algebra.ml`, set once by a    **)
(** later-linked module) is the SAME general technique this codebase       **)
(** already uses for `eval_expr_fwd`/`eval_exists_fwd`/etc., just crossing  **)
(** a compilation-unit boundary instead of staying within one file.         **)
(**                                                                          **)
(** Stage 1: `wrap+https:`/`wrap+http:` GET fetch (fetch itself is OCaml    **)
(**   glue — §2.2 step 1), format auto-detection (§2.2 step 2), default    **)
(**   Facade-X-equivalent mapping for JSON/CSV (§2.3).                      **)
(** Stage 2: `#rml=<name>` control-fragment override, reusing               **)
(**   `RML.Eval.eval_triples_map_json`/`eval_triples_map_csv` verbatim on   **)
(**   the freshly-fetched bytes instead of file bytes (§2.2 step 3).        **)
(**                                                                          **)
(** NOT here (deliberately, per the doc's staged rollout §5): `wrap+mcp:`,  **)
(** `wrap+exec:`, `process_run`, Part B's `caps_of_rml_source`.             **)
(** ======================================================================== **)

open FStar.String
open FStar.List.Tot
open RDF.Graph.Executable
open RML.Mapping
open RML.Sources
open RML.Eval
open Parser.JSON
open SPARQL.HTTP.Client

module Turtle = Parser.Turtle
module NT     = Parser.NTriples
module NQ     = Parser.NQuads

#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"

(** ====================================================================== **)
(** Part 1: small string helpers not already exposed by a module this file **)
(** can reach without introducing the SPARQL11.Algebra cycle described in  **)
(** the banner above (SPARQL.Protocol.fst is itself independent of         **)
(** SPARQL11.Algebra, but pulling it in only for three one-line helpers    **)
(** is not worth a fourth module edge here — these mirror                  **)
(** `SPARQL.Protocol.fst`'s `split_once_on`/`parse_query_string` shapes    **)
(** exactly, just re-derived locally).                                     **)
(** ====================================================================== **)

let str_starts_with (s prefix : string) : bool =
  let lp = String.length prefix in
  String.length s >= lp && String.sub s 0 lp = prefix

let str_drop_prefix (s prefix : string) : string =
  let lp = String.length prefix in
  if String.length s >= lp then String.sub s lp (String.length s - lp) else s

// Split cs on the first occurrence of sep (char-list based, so it stays
// structurally total the same way SPARQL.Protocol.fst's own splitter does).
let rec split_once_chars_acc
    (sep : nat) (cs : list FStar.Char.char) (acc : list FStar.Char.char)
  : Tot (list FStar.Char.char & option (list FStar.Char.char)) (decreases cs) =
  match cs with
  | [] -> (List.Tot.rev acc, None)
  | c :: rest ->
    if char_code c = sep then (List.Tot.rev acc, Some rest)
    else split_once_chars_acc sep rest (c :: acc)

let split_once_on (s : string) (sep : FStar.Char.char) : string & option string =
  let (before, after) = split_once_chars_acc (char_code sep) (String.list_of_string s) [] in
  (String.string_of_list before,
   (match after with None -> None | Some cs -> Some (String.string_of_list cs)))

let rec split_all_chars_acc
    (sep : nat) (cs : list FStar.Char.char) (cur : list FStar.Char.char)
  : Tot (list (list FStar.Char.char)) (decreases cs) =
  match cs with
  | [] -> [List.Tot.rev cur]
  | c :: rest ->
    if char_code c = sep then List.Tot.rev cur :: split_all_chars_acc sep rest []
    else split_all_chars_acc sep rest (c :: cur)

let split_all_on (s : string) (sep : FStar.Char.char) : list string =
  List.Tot.map String.string_of_list (split_all_chars_acc (char_code sep) (String.list_of_string s) [])

// RFC 3986 %XX decode, plus-is-space per application/x-www-form-urlencoded
// (the control fragment is authored the same way a query string is —
// mirrors SPARQL.Protocol.fst's `url_decode_chars`/`form_decode` exactly).
let is_hex_digit_wrap (c : FStar.Char.char) : bool =
  let cd = char_code c in
  (cd >= 0x30 && cd <= 0x39) || (cd >= 0x41 && cd <= 0x46) || (cd >= 0x61 && cd <= 0x66)

let hex_value_wrap (c : FStar.Char.char) : nat =
  let cd = char_code c in
  if cd >= 0x30 && cd <= 0x39 then cd - 0x30
  else if cd >= 0x41 && cd <= 0x46 then cd - 0x41 + 10
  else if cd >= 0x61 && cd <= 0x66 then cd - 0x61 + 10
  else 0

let rec form_decode_chars (cs : list FStar.Char.char) : Tot (list FStar.Char.char) (decreases cs) =
  match cs with
  | [] -> []
  | c :: rest ->
    let code = char_code c in
    if code = 0x25 (* % *) then
      (match rest with
       | h1 :: h2 :: rest' ->
         if is_hex_digit_wrap h1 && is_hex_digit_wrap h2 then
           FStar.Char.char_of_int (hex_value_wrap h1 `op_Multiply` 16 + hex_value_wrap h2)
             :: form_decode_chars rest'
         else c :: form_decode_chars rest
       | _ -> c :: form_decode_chars rest)
    else if code = 0x2B (* + *) then FStar.Char.char_of_int 0x20 :: form_decode_chars rest
    else c :: form_decode_chars rest

let form_decode (s : string) : string =
  String.string_of_list (form_decode_chars (String.list_of_string s))

let parse_kv_pair (pair : string) : option (string & string) =
  match split_once_on pair (FStar.Char.char_of_int 0x3D (* = *)) with
  | (k, Some v) -> Some (form_decode k, form_decode v)
  | (k, None) -> if String.length k = 0 then None else Some (form_decode k, "")

// "k=v&k=v&..." -> [(k,v); ...], duplicate keys preserved (first match
// wins downstream via List.Tot.assoc, matching SPARQL.Protocol.fst's own
// query-string convention).
let parse_control_fragment (frag : string) : list (string & string) =
  List.Tot.concatMap
    (fun p -> match parse_kv_pair p with Some kv -> [kv] | None -> [])
    (split_all_on frag (FStar.Char.char_of_int 0x26 (* & *)))

// Content-Type-style "media/type;params" -> lower-cased base media type
// (mirrors SPARQL.Protocol.fst's `content_type_base`).
let ascii_lower_char_wrap (c : FStar.Char.char) : FStar.Char.char =
  let cd = char_code c in
  if cd >= 0x41 && cd <= 0x5A then FStar.Char.char_of_int (cd + 32) else c

let ascii_lower_string_wrap (s : string) : string =
  String.string_of_list (List.Tot.map ascii_lower_char_wrap (String.list_of_string s))

let rec trim_ws_left (cs : list FStar.Char.char) : Tot (list FStar.Char.char) (decreases cs) =
  match cs with
  | c :: rest -> if char_code c = 0x20 || char_code c = 0x09 then trim_ws_left rest else cs
  | [] -> cs

let trim_ws_wrap (s : string) : string =
  String.string_of_list (List.Tot.rev (trim_ws_left (List.Tot.rev (trim_ws_left (String.list_of_string s)))))

let content_type_base (ct : string) : string =
  match split_once_on ct (FStar.Char.char_of_int 0x3B (* ; *)) with
  | (base, _) -> ascii_lower_string_wrap (trim_ws_wrap base)

let rec header_lookup_ci_wrap
    (hs : list (string & string)) (needle : string)
  : Tot (option string) (decreases hs) =
  match hs with
  | [] -> None
  | (k, v) :: rest -> if k = needle then Some v else header_lookup_ci_wrap rest needle

let header_lookup_ci_local (headers : list (string & string)) (name : string) : option string =
  header_lookup_ci_wrap headers (ascii_lower_string_wrap name)


(** ====================================================================== **)
(** Part 2: `wrap+https:`/`wrap+http:` IRI parsing (§2.1)                   **)
(** ====================================================================== **)

type wrap_transport =
  | WT_Https
  | WT_Http

let wrap_https_prefix : string = "wrap+https://"
let wrap_http_prefix  : string = "wrap+http://"

// Control fragment (`#k=v&k=v...`), plus everything the wrap+ scheme
// resolves to before dereferencing: the transport, and the literal
// authority+path+query the real https/http request targets (scheme
// already stripped — §2.1's "everything between the scheme and an
// optional # is the literal target URL, unmodified").
noeq type wrap_target = {
  wt_transport : wrap_transport;
  wt_target    : string;
  wt_control   : list (string & string);
}

// Reconstitute the fully-legible https://.../http://... URL (§2.1's own
// "keeps the real target 100% legible" claim) -- used for CLI/error
// display only; request-building (Part 4) re-splits `wt_target` directly.
let wrap_target_url (wt : wrap_target) : string =
  (match wt.wt_transport with WT_Https -> "https://" | WT_Http -> "http://") ^ wt.wt_target

let wrap_target_rml_name (wt : wrap_target) : option string =
  List.Tot.assoc "rml" wt.wt_control

let wrap_target_mime_override (wt : wrap_target) : option string =
  List.Tot.assoc "mime" wt.wt_control

// v1: `ttl=` is parsed but ignored (§2.4 — cross-query caching is a v2
// follow-up); exposed for forward compatibility / diagnostics only.
let wrap_target_ttl (wt : wrap_target) : option string =
  List.Tot.assoc "ttl" wt.wt_control

// Recognize a `wrap+https:`/`wrap+http:` IRI and decode it. Any other
// string (including `wrap+mcp:`/`wrap+exec:`, out of scope this stage,
// or a plain non-wrap+ IRI) yields `None` -- IDENTICAL to today's
// "unregistered SERVICE endpoint" outcome, per §2.5's own requirement.
let parse_wrap_iri (s : string) : option wrap_target =
  let (before_frag, frag) = split_once_on s (FStar.Char.char_of_int 0x23 (* # *)) in
  let control = match frag with None -> [] | Some f -> parse_control_fragment f in
  if str_starts_with before_frag wrap_https_prefix then
    Some { wt_transport = WT_Https; wt_target = str_drop_prefix before_frag wrap_https_prefix; wt_control = control }
  else if str_starts_with before_frag wrap_http_prefix then
    Some { wt_transport = WT_Http; wt_target = str_drop_prefix before_frag wrap_http_prefix; wt_control = control }
  else None


(** ====================================================================== **)
(** Part 3: format detection (§2.2 step 2)                                  **)
(** ====================================================================== **)

type wrap_format =
  | WF_Json
  | WF_Csv
  | WF_Turtle
  | WF_NTriples
  | WF_NQuads
  | WF_PlainString

// `mime=` (when present) always wins over the response's actual
// Content-Type -- "declares the format when no Content-Type header
// exists ... or when the declared type disagrees with what auto-
// detection would guess" (§2.2 step 2).
let detect_wrap_format (content_type : option string) (mime_override : option string) : wrap_format =
  let base = match mime_override with
    | Some m -> content_type_base m
    | None -> (match content_type with Some ct -> content_type_base ct | None -> "") in
  if base = "application/json" then WF_Json
  else if base = "text/csv" then WF_Csv
  else if base = "text/turtle" || base = "application/x-turtle" then WF_Turtle
  else if base = "application/n-triples" then WF_NTriples
  else if base = "application/n-quads" then WF_NQuads
  else WF_PlainString


(** ====================================================================== **)
(** Part 4: HTTP GET request construction (§2.2 step 1's non-I/O half —    **)
(** URL splitting + `http_request_msg` assembly is pure string             **)
(** manipulation, the same class of work `SPARQL.Protocol.Client.fst`'s    **)
(** own `build_get_request` does; only the socket connect/send/receive is  **)
(** I/O, done by the OCaml glue this function's result feeds).             **)
(** ====================================================================== **)

let default_port_for (t : wrap_transport) : nat =
  match t with WT_Https -> 443 | WT_Http -> 80

// "host[:port][/path?query]" -> (authority, "/path?query" or "/").
let split_authority_path (s : string) : string & string =
  match split_once_on s (FStar.Char.char_of_int 0x2F (* / *)) with
  | (auth, None) -> (auth, "/")
  | (auth, Some rest) -> (auth, "/" ^ rest)

let split_host_port (authority : string) (default_port : nat) : string & nat =
  match split_once_on authority (FStar.Char.char_of_int 0x3A (* : *)) with
  | (host, None) -> (host, default_port)
  | (host, Some port_s) ->
    (match parse_nat port_s with Some p -> (host, p) | None -> (host, default_port))

let split_path_query (path_and_query : string) : string & string =
  match split_once_on path_and_query (FStar.Char.char_of_int 0x3F (* ? *)) with
  | (p, None) -> (p, "")
  | (p, Some q) -> (p, q)

noeq type wrap_request = {
  wr_host : string;
  wr_port : nat;
  wr_msg  : http_request_msg;
}

// Straight passthrough GET of the wrap+ target: no SPARQL-protocol-style
// query-param assembly (the target's own query string, if any, already
// sits inside `wt_target` verbatim per §2.1) -- POST is out of scope for
// v1 (§2.2 step 1's own note: "wrapping a tool for read-only query
// answering has no SPARQL-Update-shaped need for a request body").
let build_wrap_get_request (wt : wrap_target) : wrap_request =
  let (authority, path_and_query) = split_authority_path wt.wt_target in
  let (host, port) = split_host_port authority (default_port_for wt.wt_transport) in
  let (path, query) = split_path_query path_and_query in
  { wr_host = host; wr_port = port;
    wr_msg = { rm_method = "GET"; rm_path = path; rm_query_str = query;
               rm_version = "HTTP/1.1"; rm_host = host;
               rm_headers = [("Accept", "*/*"); ("Connection", "close")];
               rm_body = "" } }


(** ====================================================================== **)
(** Part 5: default Facade-X-equivalent mapping (§2.3)                      **)
(**                                                                         **)
(** Implementation note (disclosed deviation from the doc's literal "one   **)
(** canned RML.Mapping.mapping_document value" phrasing): a default        **)
(** mapping whose PREDICATE is "whatever JSON key / CSV header the source  **)
(** happens to carry" cannot be expressed as a static `predicate_object_map`**)
(** list, since `RML.Mapping.term_map`'s predicate position is always      **)
(** fixed at authoring time (`TMF_Constant`/`TMF_Reference`/`TMF_Template`  **)
(** all evaluate against ROW VALUES, never against "the key at this        **)
(** position") -- there is no RML construct for "predicate = the field     **)
(** name itself." This is therefore a direct, bespoke walker (matching     **)
(** Facade-X's own actual implementation shape, which is not RML-based     **)
(** either) rather than a value fed through `RML.Eval.eval_triples_map`.   **)
(** It reuses RML.Eval's own term-construction primitives VERBATIM         **)
(** wherever they apply: `RML.Eval.string_encode_iri` (IRI-safe key        **)
(** encoding), `RML.Eval.json_natural_value` + `RML.Eval.build_literal_opt` **)
(** (JSON-scalar -> literal, RML-IO's own natural-typing rule), and        **)
(** `RML.Sources.csv_iterate` (CSV tokenizing + `rml:null`-style empty-    **)
(** cell filtering, called here with `[""]` as the null-values list so     **)
(** "one triple per non-null cell" falls out of the EXISTING filter        **)
(** rather than a second hand-rolled check).                                **)
(** ====================================================================== **)

let default_wrap_ns : string = "http://factoidal.example/ns/wrap#"

// `ns ^ key` is a `wf_iri` whenever `ns` itself already contains a colon
// (true for `default_wrap_ns`) -- `is_iri` only demands non-empty + a
// colon present, and appending never removes one. Gated at runtime
// (mirroring `RML.Eval.iri_like_term_gated`'s `if ok value then Some ...`
// idiom) rather than proved, so a future caller with an unusual `ns`
// degrades to a dropped field instead of a proof obligation here.
let wrap_predicate_iri (ns : string) (key_encoded : string) : option wf_iri =
  let candidate = ns ^ key_encoded in
  if is_iri candidate then Some candidate else None

let json_scalar_to_object (v : json_val) : option rdf_term =
  match json_natural_value v with
  | Some (lex, dt) -> build_literal_opt lex dt None
  | None -> None

let subject_to_term (s : subject) : rdf_term =
  match s with S_IRI i -> T_IRI i | S_BNode b -> T_BNode b

// One JSON value reached in OBJECT position of (subj, pred, _): scalar ->
// one literal triple; nested object -> a fresh blank-node subject plus
// its own recursively-walked triples; array -> "fan out as repeated
// (subj, pred, object) triples" (§2.3), the SAME predicate for every
// element, never an `rdf:_n`/`rdf:List` container encoding (§2.3's own
// reasoning: an unbounded `rdf:rest` chain is an awkward SPARQL BGP
// shape). `seed` derives fresh, deterministic blank-node labels the same
// way `RML.Eval.eval_triples_map`'s own `tmap.tm_id ^ "#r" ^ string_of_int idx`
// convention does, so this stays `Tot` with no counter/effect threading.
let rec json_field_value_triples
    (ns : string) (subj : subject) (pred : wf_iri) (seed : string) (v : json_val)
  : Tot (list triple) (decreases v) =
  match v with
  | JArray items -> json_array_items_triples ns subj pred seed items
  | JObject fields ->
    let nested : subject = S_BNode seed in
    { s = subj; p = pred; o = subject_to_term nested } :: json_object_fields_triples ns nested seed fields
  | _ ->
    (match json_scalar_to_object v with
     | None -> []
     | Some obj -> [{ s = subj; p = pred; o = obj }])

and json_array_items_triples
    (ns : string) (subj : subject) (pred : wf_iri) (seed : string) (items : list json_val)
  : Tot (list triple) (decreases items) =
  match items with
  | [] -> []
  | item :: rest ->
    // `List.Tot.length rest` strictly decreases position-to-position
    // (n-1, n-2, ..., 0), giving every array element a distinct nested-
    // blank-node seed without threading an explicit index accumulator.
    let item_seed = seed ^ "i" ^ string_of_int (List.Tot.length rest) in
    json_field_value_triples ns subj pred item_seed item @ json_array_items_triples ns subj pred seed rest

and json_object_fields_triples
    (ns : string) (subj : subject) (seed : string) (fields : list (string & json_val))
  : Tot (list triple) (decreases fields) =
  match fields with
  | [] -> []
  | (key, value) :: rest ->
    (match wrap_predicate_iri ns (string_encode_iri key) with
     | None -> json_object_fields_triples ns subj seed rest
     | Some pred ->
       json_field_value_triples ns subj pred (seed ^ "_" ^ key) value
         @ json_object_fields_triples ns subj seed rest)

// Whole-document entry point. Root object -> one blank-node subject,
// its fields walked directly (§2.3: "the document root is one blank-
// node subject"). Root array -> Facade-X's own "container membership as
// repeated triples" read applied at the top level: every element hangs
// off ONE root subject under a synthetic "member" predicate. Root
// scalar (degenerate, no key context at all) -> RML-IO's natural-typing
// fallback, at most one triple.
let default_json_document_triples (root : json_val) : list triple =
  let subj = S_BNode "wrapdoc" in
  match root with
  | JObject fields -> json_object_fields_triples default_wrap_ns subj "wrapdoc" fields
  | JArray items ->
    (match wrap_predicate_iri default_wrap_ns "member" with
     | None -> []
     | Some pred -> json_array_items_triples default_wrap_ns subj pred "wrapdoc" items)
  | _ ->
    (match wrap_predicate_iri default_wrap_ns "value", json_scalar_to_object root with
     | Some pred, Some obj -> [{ s = subj; p = pred; o = obj }]
     | _ -> [])

// CSV default mapping: header row -> predicate names (same synthetic
// namespace), each data row -> one blank-node subject, one triple per
// non-null cell (§2.3) -- `csv_iterate`'s own `[""]` null-values filter
// does the "non-null" part; this function only builds triples.
let csv_row_triples (ns : string) (idx : int) (bindings : list (string & string)) : list triple =
  let subj = S_BNode ("wrapcsv_r" ^ string_of_int idx) in
  List.Tot.concatMap
    (fun (cell : string & string) ->
       let (header, value) = cell in
       match wrap_predicate_iri ns (string_encode_iri header) with
       | None -> []
       | Some pred ->
         (match build_literal_opt value xsd_string None with
          | None -> []
          | Some obj -> [{ s = subj; p = pred; o = obj }]))
    bindings

let default_csv_document_triples (rows : list source_row) : list triple =
  List.Tot.concatMap
    (fun (pair : int & source_row) ->
       let (i, row) = pair in
       match row with
       | Row_CSV bindings -> csv_row_triples default_wrap_ns i bindings
       | Row_JSON _ -> [])
    (List.Tot.mapi (fun i r -> (i, r)) rows)

// "No recognized type and no `mime=` override" fallback (§2.2 step 2's
// last sentence): the whole body as one xsd:string literal, at most one
// triple.
let plain_string_fallback_triples (body : string) : list triple =
  match wrap_predicate_iri default_wrap_ns "value" with
  | None -> []
  | Some pred ->
    (match build_literal_opt body xsd_string None with
     | None -> []
     | Some obj -> [{ s = S_BNode "wrapdoc"; p = pred; o = obj }])

let nquads_dataset_triples (ds : rdf_dataset) : list triple =
  ds.ds_default @ List.Tot.concatMap (fun (ng : named_graph) -> ng.ng_graph) ds.ds_named


(** ====================================================================== **)
(** Part 6: `rml=` override (Stage 2, §2.2 step 3)                         **)
(**                                                                        **)
(** `rml=`'s value is resolved to a LOCAL FILE PATH by the OCaml glue      **)
(** (per this task's own brief: "local file path in CLI context; vendored **)
(** fixture in tests") rather than a lookup into the query's own already- **)
(** loaded default/named graphs -- `service_endpoint_lookup`'s fixed       **)
(** `wf_iri -> option graph_store` signature has no dataset parameter to   **)
(** reach that data through, and the doc itself leaves the exact wiring    **)
(** "decide at implementation time" (§2.5). Turtle-parsing +               **)
(** `RML.Mapping.decode_mapping_document` are BOTH pure, so they run HERE  **)
(** in F* proper, not in the OCaml glue -- the glue's only job for        **)
(** `rml=` is reading the named file's bytes (rule #11: file I/O only).   **)
(** ====================================================================== **)

// `rml=`'s value names either one specific TriplesMap's node_ref (subject
// identity, e.g. an `rr:TriplesMap` blank node's synthesized id or an
// IRI) or nothing more specific than "the whole document" -- fall back to
// every triples map in the document if the name matches none of them
// (§2.2 step 3: "or the whole mapping document containing several").
let select_triples_maps (doc : mapping_document) (name : option string) : list triples_map =
  match name with
  | None -> doc.md_triples_maps
  | Some n ->
    let matches = List.Tot.filter (fun (tm : triples_map) -> tm.tm_id = n) doc.md_triples_maps in
    if Nil? matches then doc.md_triples_maps else matches

// Apply every candidate triples map to the SAME freshly-fetched bytes,
// via `RML.Eval.eval_triples_map_json`/`eval_triples_map_csv` --
// unmodified convenience wrappers that already no-op (return []) for a
// triples map whose own logical source reference formulation doesn't
// match `fmt`, so no extra filtering is needed here (§2.2 step 3: "same
// F* function signature, different byte source"). Graph-map placements
// collapse to the default graph only (v1 simplification, disclosed): a
// `graph_store`'s target is one flat `rdf_graph`, the same shape
// `57_service_client_bind.sh`'s `graph_to_store` already assumes.
let triplify_with_rml (fmt : wrap_format) (body : string) (tmaps : list triples_map) : list triple =
  match fmt with
  | WF_Json ->
    (match parse_json body with
     | Some root ->
       (place_into_dataset empty_dataset (List.Tot.concatMap (fun tm -> eval_triples_map_json tm root None) tmaps)).ds_default
     | None -> [])
  | WF_Csv ->
    (place_into_dataset empty_dataset (List.Tot.concatMap (fun tm -> eval_triples_map_csv tm body None) tmaps)).ds_default
  | _ -> []  // RML-Core's logical-source shape covers JSON/CSV (+ XML, not built); a pure-RDF fetch has nothing to map.


(** ====================================================================== **)
(** Part 7: top-level resolver entry point                                 **)
(**                                                                        **)
(** Called by the OCaml glue once it has: the original wrap+ IRI string    **)
(** (to recover the control fragment), the HTTP response's status/headers/ **)
(** body, and — Stage 2 only, when `rml=` was present and the glue         **)
(** successfully read the named file — that file's raw Turtle text.       **)
(** Returns `[]` on any parse failure, non-2xx status, or resolver         **)
(** mismatch; the OCaml glue is the one place that turns "empty triples"   **)
(** into `Some (graph_to_store [])` (endpoint resolved, yielded nothing)    **)
(** versus `None` (endpoint not resolved at all — wrap+ prefix unrecognized,**)
(** opt-in flag off, host not allowlisted, or the fetch itself failed) —   **)
(** see the glue file's own banner for that split.                        **)
(** ====================================================================== **)

let resolve_wrap_response
    (wrap_iri : string)
    (status : nat)
    (headers : list (string & string))
    (body : string)
    (rml_ttl_text : option string)
  : list triple =
  match parse_wrap_iri wrap_iri with
  | None -> []
  | Some wt ->
    if status < 200 || status >= 300 then []
    else
      let content_type = header_lookup_ci_local headers "Content-Type" in
      let fmt = detect_wrap_format content_type (wrap_target_mime_override wt) in
      (match rml_ttl_text with
       | Some ttl ->
         let doc = decode_mapping_document (Turtle.parse_turtle ttl) in
         let tmaps = select_triples_maps doc (wrap_target_rml_name wt) in
         triplify_with_rml fmt body tmaps
       | None ->
         (match fmt with
          | WF_Turtle -> (match Turtle.parse_turtle_strict body with Some ts -> ts | None -> [])
          | WF_NTriples -> (match NT.parse_ntriples_strict body with Some ts -> ts | None -> [])
          | WF_NQuads -> (match NQ.parse_nquads_strict body with Some ds -> nquads_dataset_triples ds | None -> [])
          | WF_Json -> (match parse_json body with Some root -> default_json_document_triples root | None -> [])
          | WF_Csv -> default_csv_document_triples (csv_iterate body [""])
          | WF_PlainString -> plain_string_fallback_triples body))

#pop-options


(** ====================================================================== **)
(** Part 8: smoke tests (compile-time)                                     **)
(** ====================================================================== **)

let _test_parse_wrap_https =
  match parse_wrap_iri "wrap+https://api.example.org/v1/users?id=42#rml=urn:mapping:users-api" with
  | Some wt ->
    wt.wt_transport = WT_Https
    && wt.wt_target = "api.example.org/v1/users?id=42"
    && wrap_target_rml_name wt = Some "urn:mapping:users-api"
  | None -> false

let _test_parse_wrap_http_no_fragment =
  match parse_wrap_iri "wrap+http://internal.example.org/status" with
  | Some wt -> wt.wt_transport = WT_Http && wt.wt_target = "internal.example.org/status" && wrap_target_rml_name wt = None
  | None -> false

let _test_parse_wrap_rejects_unknown_scheme =
  None? (parse_wrap_iri "wrap+mcp:geocoder/geocode?x=1")
  && None? (parse_wrap_iri "http://example.org/plain")

let _test_wrap_target_url =
  match parse_wrap_iri "wrap+https://127.0.0.1:8099/data.json" with
  | Some wt -> wrap_target_url wt = "https://127.0.0.1:8099/data.json"
  | None -> false

let _test_build_wrap_get_request =
  match parse_wrap_iri "wrap+http://127.0.0.1:8099/data.json?x=1" with
  | Some wt ->
    let req = build_wrap_get_request wt in
    req.wr_host = "127.0.0.1" && req.wr_port = 8099
    && req.wr_msg.rm_path = "/data.json" && req.wr_msg.rm_query_str = "x=1" && req.wr_msg.rm_method = "GET"
  | None -> false

let _test_default_port =
  match parse_wrap_iri "wrap+https://example.org/x" with
  | Some wt -> (build_wrap_get_request wt).wr_port = 443
  | None -> false

let _test_detect_format_mime_override_wins =
  detect_wrap_format (Some "text/plain") (Some "application/json") = WF_Json

let _test_detect_format_content_type =
  detect_wrap_format (Some "text/csv; charset=utf-8") None = WF_Csv

let _test_detect_format_unknown =
  detect_wrap_format None None = WF_PlainString

let _test_default_json_object_mapping =
  match parse_json "{\"name\": \"Ada\", \"age\": 36}" with
  | Some root ->
    let ts = default_json_document_triples root in
    List.Tot.length ts = 2
  | None -> false

let _test_default_json_nested_object =
  match parse_json "{\"name\": \"Ada\", \"address\": {\"city\": \"London\"}}" with
  | Some root -> List.Tot.length (default_json_document_triples root) = 3  // name + address-link + city
  | None -> false

let _test_default_json_array_fanout =
  match parse_json "{\"tag\": [\"a\", \"b\", \"c\"]}" with
  | Some root -> List.Tot.length (default_json_document_triples root) = 3
  | None -> false

let _test_default_csv_mapping =
  let rows = csv_iterate "name,age\nAda,36\nGrace,85\n" [""] in
  List.Tot.length (default_csv_document_triples rows) = 4  // 2 rows x 2 cells

let _test_plain_string_fallback =
  List.Tot.length (plain_string_fallback_triples "hello") = 1

let _test_resolve_default_json =
  List.Tot.length
    (resolve_wrap_response "wrap+http://127.0.0.1:8099/x" 200 [("content-type", "application/json")]
       "{\"a\": \"b\"}" None) = 1

let _test_resolve_non_2xx_status =
  Nil? (resolve_wrap_response "wrap+http://127.0.0.1:8099/x" 404 [("content-type", "application/json")] "{}" None)

let _test_resolve_turtle_passthrough =
  List.Tot.length
    (resolve_wrap_response "wrap+http://127.0.0.1:8099/x" 200 [("content-type", "text/turtle")]
       "<http://example.org/s> <http://example.org/p> \"o\" ." None) = 1

let _test_resolve_unrecognized_iri =
  Nil? (resolve_wrap_response "http://example.org/plain-service" 200 [] "irrelevant" None)
