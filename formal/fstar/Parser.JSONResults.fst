module Parser.JSONResults

// SPARQL Query Results JSON Format parser
// W3C Specification: https://www.w3.org/TR/sparql11-results-json/
//
// JSON format structure:
//   {"head":{"vars":["x","y"]},
//    "results":{"bindings":[
//      {"x":{"type":"uri","value":"..."},
//       "y":{"type":"literal","value":"...","xml:lang":"en"}}]}}
//
// Or for ASK queries:
//   {"head":{}, "boolean": true}

open FStar.String
open FStar.List.Tot
open Parser.Combinators
open RDF.Graph.Executable
open Parser.JSON  // byte-safe JSON parser (this module was migrated onto it; #310)

// ================================================================
// Helper: construct a T_Literal only if well-formed
// ================================================================

let mk_literal (lexical : string) (dt : string) (lang : option string) : option rdf_term =
  if is_iri dt then
    let lit : literal = {
      lexical_form = lexical;
      datatype = dt;
      lang_tag = lang; direction = None
    } in
    if literal_wf lit then Some (T_Literal lit) else None
  else None

// SPARQL 1.2 base-direction result field ("its:dir": "ltr" | "rtl" —
// SPARQL 1.2 Query Results JSON Format, lang-basedir W3C family
// fixtures langdir-literal.srj / strlangdir.srj / concat.srj). Strict/
// lowercase only, mirroring SPARQL11.Algebra.parse_text_direction: an
// unrecognized value is simply "no direction" rather than a hard parse
// error, so a malformed "its:dir" degrades to the RDF 1.1 rdf:langString
// reading instead of failing the whole result-file parse.
let json_parse_text_direction (s : string) : option text_direction =
  if s = "ltr" then Some Dir_LTR
  else if s = "rtl" then Some Dir_RTL
  else None

// Directional variant of mk_literal above: builds an rdf:dirLangString
// literal when both a language tag and a valid base direction are given.
let mk_dir_literal (lexical : string) (lang : string) (dir : text_direction) : option rdf_term =
  let lit : literal = {
    lexical_form = lexical;
    datatype = rdf_dir_lang_string;
    lang_tag = Some lang; direction = Some dir
  } in
  if literal_wf lit then Some (T_Literal lit) else None

// ================================================================
// SRJ (SPARQL Results JSON) extraction
// ================================================================

// Parse a single binding value object:
//   {"type":"uri","value":"http://..."}
//   {"type":"literal","value":"foo"}
//   {"type":"literal","value":"foo","xml:lang":"en"}
//   {"type":"literal","value":"foo","datatype":"http://..."}
//   {"type":"bnode","value":"b0"}
// SPARQL 1.2 SRJ (Results-JSON WD): a triple-term binding is encoded as
//   {"type":"triple","value":{"subject":{...},"predicate":{...},"object":{...}}}
// so `value` is an object, not a string, and the three sub-values recurse
// through the same decoder. `fuel` bounds the (shallow) nesting depth.
let rec parse_binding_value_fuel (fuel: nat) (obj: json_val) : option rdf_term =
  if fuel = 0 then None else
  match json_get_string "type" obj with
  | None -> None
  | Some typ ->
    let val_str : string = match json_get_string "value" obj with
      | Some s -> (s <: string)
      | None -> "" in
    if typ = "uri" then
      if is_iri val_str then Some (T_IRI val_str) else None
    else if typ = "bnode" then
      Some (T_BNode val_str)
    else if typ = "literal" || typ = "typed-literal" then
      let lang = json_get_string "xml:lang" obj in
      let dt = json_get_string "datatype" obj in
      let its_dir = json_get_string "its:dir" obj in
      (match lang, its_dir with
       | Some lang_val, Some dir_str ->
         (match json_parse_text_direction dir_str with
          | Some dir_val -> mk_dir_literal val_str lang_val dir_val
          | None -> mk_literal val_str rdf_lang_string (Some lang_val))
       | Some lang_val, None ->
         mk_literal val_str rdf_lang_string (Some lang_val)
       | None, _ ->
         (match dt with
          | Some dt_val -> mk_literal val_str dt_val None
          | None -> mk_literal val_str xsd_string None))
    else if typ = "triple" then
      (match json_get_field "value" obj with
       | None -> None
       | Some tval ->
         (match json_get_field "subject" tval,
                json_get_field "predicate" tval,
                json_get_field "object" tval with
          | Some sj, Some pj, Some oj ->
            (match parse_binding_value_fuel (fuel - 1) sj,
                   parse_binding_value_fuel (fuel - 1) pj,
                   parse_binding_value_fuel (fuel - 1) oj with
             | Some (T_IRI si), Some (T_IRI p), Some ot -> Some (T_TripleTerm (S_IRI si) p ot)
             | Some (T_BNode sb), Some (T_IRI p), Some ot -> Some (T_TripleTerm (S_BNode sb) p ot)
             | _, _, _ -> None)
          | _, _, _ -> None))
    else None

let parse_binding_value (obj: json_val) : option rdf_term =
  parse_binding_value_fuel 64 obj

// Parse a single binding row object:
//   {"x":{"type":"uri","value":"..."},"y":{"type":"literal","value":"..."}}
// Returns list of (var_name, rdf_term) pairs
let parse_binding_row (obj: json_val) : list (string * rdf_term) =
  match obj with
  | JObject fields ->
    List.Tot.concatMap (fun (pair: (string * json_val)) ->
      let (var_name, val_obj) = pair in
      match parse_binding_value val_obj with
      | Some term -> [(var_name, term)]
      | None -> []
    ) fields
  | _ -> []

// Parse full SRJ results: returns variable names and binding rows
let parse_srj_results (input: string)
  : option (list string * list (list (string * rdf_term))) =
  match parse_json input with
  | None -> None
  | Some root ->
    // Get head.vars
    let vars = match json_get_field "head" root with
      | None -> []
      | Some head ->
        match json_get_string_array "vars" head with
        | Some vs -> vs
        | None -> []
    in
    // Get results.bindings
    match json_get_field "results" root with
    | Some results_obj ->
      (match json_get_array "bindings" results_obj with
       | Some bindings ->
         let rows = List.Tot.map parse_binding_row bindings in
         Some (vars, rows)
       | None -> Some (vars, []))
    | None -> Some (vars, [])

// Parse SRJ boolean result: {"head":{}, "boolean": true/false}
let parse_srj_boolean (input: string) : option bool =
  match parse_json input with
  | None -> None
  | Some root -> json_get_bool "boolean" root
