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

// ================================================================
// Minimal JSON value type (just enough for SRJ)
// ================================================================

type json_value =
  | JNull   : json_value
  | JBool   : bool -> json_value
  | JString : string -> json_value
  | JNumber : string -> json_value
  | JArray  : list json_value -> json_value
  | JObject : list (string * json_value) -> json_value

// ================================================================
// JSON parser
// ================================================================

// Skip JSON whitespace (space, tab, newline, CR)
let json_ws : parser unit =
  fun input pos ->
    match pskip_whitespace input pos with
    | ParseOk _ pos' -> ParseOk () pos'
    | ParseFail msg fpos -> ParseFail msg fpos

// Helper: convert a hex digit character code to its value
let hex_digit_val (h: int) : int =
  if h >= 0x30 && h <= 0x39 then h - 0x30
  else if h >= 0x41 && h <= 0x46 then h - 0x41 + 10
  else if h >= 0x61 && h <= 0x66 then h - 0x61 + 10
  else 0

// Parse a JSON string (double-quoted, with escape sequences)
// Returns the unescaped string content
let rec json_string_body (input:string) (pos:nat) (acc: list FStar.Char.char) (fuel:nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseFail "unterminated JSON string" pos
  else
    let len = String.length input in
    if pos >= len then ParseFail "unterminated JSON string" pos
    else
      let ch = String.index input pos in
      let code = FStar.Char.int_of_char ch in
      if code = 0x22 then  // closing "
        ParseOk (String.string_of_list (List.Tot.rev acc)) (pos + 1)
      else if code = 0x5C then  // backslash
        if pos + 1 >= len then ParseFail "backslash at end of string" pos
        else
          let esc = String.index input (pos + 1) in
          let esc_code = FStar.Char.int_of_char esc in
          if esc_code = 0x22 then  // \"
            json_string_body input (pos + 2) (FStar.Char.char_of_int 0x22 :: acc) (fuel - 1)
          else if esc_code = 0x5C then  // backslash-backslash
            json_string_body input (pos + 2) (FStar.Char.char_of_int 0x5C :: acc) (fuel - 1)
          else if esc_code = 0x2F then  // \/
            json_string_body input (pos + 2) (FStar.Char.char_of_int 0x2F :: acc) (fuel - 1)
          else if esc_code = 0x6E then  // \n
            json_string_body input (pos + 2) (FStar.Char.char_of_int 0x0A :: acc) (fuel - 1)
          else if esc_code = 0x72 then  // \r
            json_string_body input (pos + 2) (FStar.Char.char_of_int 0x0D :: acc) (fuel - 1)
          else if esc_code = 0x74 then  // \t
            json_string_body input (pos + 2) (FStar.Char.char_of_int 0x09 :: acc) (fuel - 1)
          else if esc_code = 0x62 then  // \b
            json_string_body input (pos + 2) (FStar.Char.char_of_int 0x08 :: acc) (fuel - 1)
          else if esc_code = 0x66 then  // \f
            json_string_body input (pos + 2) (FStar.Char.char_of_int 0x0C :: acc) (fuel - 1)
          else if esc_code = 0x75 then begin  // \uXXXX
            if pos + 5 >= len then ParseFail "incomplete unicode escape" pos
            else
              // For simplicity, skip 4 hex digits and insert a replacement char
              // Full Unicode handling would need UTF-8 encoding
              let h0 = FStar.Char.int_of_char (String.index input (pos + 2)) in
              let h1 = FStar.Char.int_of_char (String.index input (pos + 3)) in
              let h2 = FStar.Char.int_of_char (String.index input (pos + 4)) in
              let h3 = FStar.Char.int_of_char (String.index input (pos + 5)) in
              let v0 = hex_digit_val h0 in
              let v1 = hex_digit_val h1 in
              let v2 = hex_digit_val h2 in
              let v3 = hex_digit_val h3 in
              let codepoint = (op_Multiply v0 4096) + (op_Multiply v1 256) + (op_Multiply v2 16) + v3 in
              // Simple ASCII or Latin-1 range: emit directly
              if codepoint <= 0x7F then
                json_string_body input (pos + 6) (FStar.Char.char_of_int codepoint :: acc) (fuel - 1)
              else
                // For non-ASCII, emit UTF-8 bytes
                if codepoint <= 0x7FF then
                  let b1 = FStar.Char.char_of_int (0xC0 + codepoint / 64) in
                  let b2 = FStar.Char.char_of_int (0x80 + (codepoint % 64)) in
                  json_string_body input (pos + 6) (b2 :: b1 :: acc) (fuel - 1)
                else
                  let b1 = FStar.Char.char_of_int (0xE0 + codepoint / 4096) in
                  let b2 = FStar.Char.char_of_int (0x80 + (codepoint % 4096) / 64) in
                  let b3 = FStar.Char.char_of_int (0x80 + (codepoint % 64)) in
                  json_string_body input (pos + 6) (b3 :: b2 :: b1 :: acc) (fuel - 1)
          end
          else
            // Unknown escape, just include the character
            json_string_body input (pos + 2) (esc :: acc) (fuel - 1)
      else
        json_string_body input (pos + 1) (ch :: acc) (fuel - 1)

let parse_json_string (input:string) (pos:nat) : parse_result string =
  let len = String.length input in
  if pos >= len then ParseFail "expected JSON string" pos
  else
    let ch = String.index input pos in
    if FStar.Char.int_of_char ch = 0x22 then  // opening "
      let fuel = len - pos in
      json_string_body input (pos + 1) [] fuel
    else ParseFail "expected opening double-quote" pos

// Parse a JSON number (just capture as string)
let parse_json_number (input:string) (pos:nat) : parse_result string =
  let is_num_char (c: FStar.Char.char) : bool =
    let code = FStar.Char.int_of_char c in
    (code >= 0x30 && code <= 0x39) ||  // 0-9
    code = 0x2D ||  // -
    code = 0x2B ||  // +
    code = 0x2E ||  // .
    code = 0x65 ||  // e
    code = 0x45     // E
  in
  ptake_while1 is_num_char input pos

// Safe character peek: returns the character at position pos if in bounds
let safe_index (input:string) (pos:nat) : option FStar.Char.char =
  if pos < String.length input then Some (String.index input pos)
  else None

// Forward-declare json_value parser via fuel-based recursion
let rec parse_json_value (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result json_value) (decreases fuel) =
  if fuel = 0 then ParseFail "JSON nesting too deep" pos
  else
    // Skip whitespace
    let pos = match json_ws input pos with
      | ParseOk _ p -> p
      | _ -> pos in
    match safe_index input pos with
    | None -> ParseFail "unexpected end of JSON" pos
    | Some ch ->
      let code = FStar.Char.int_of_char ch in
      if code = 0x22 then  // string
        (match parse_json_string input pos with
         | ParseOk s pos' -> ParseOk (JString s) pos'
         | ParseFail msg fpos -> ParseFail msg fpos)
      else if code = 0x7B then  // { object
        parse_json_object input (pos + 1) (fuel - 1)
      else if code = 0x5B then  // [ array
        parse_json_array input (pos + 1) (fuel - 1)
      else if code = 0x74 then  // true
        (match pstring "true" input pos with
         | ParseOk _ pos' -> ParseOk (JBool true) pos'
         | ParseFail msg fpos -> ParseFail msg fpos)
      else if code = 0x66 then  // false
        (match pstring "false" input pos with
         | ParseOk _ pos' -> ParseOk (JBool false) pos'
         | ParseFail msg fpos -> ParseFail msg fpos)
      else if code = 0x6E then  // null
        (match pstring "null" input pos with
         | ParseOk _ pos' -> ParseOk (JNull) pos'
         | ParseFail msg fpos -> ParseFail msg fpos)
      else if code = 0x2D || (code >= 0x30 && code <= 0x39) then  // number
        (match parse_json_number input pos with
         | ParseOk s pos' -> ParseOk (JNumber s) pos'
         | ParseFail msg fpos -> ParseFail msg fpos)
      else
        ParseFail "unexpected character in JSON" pos

and parse_json_object (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result json_value) (decreases fuel) =
  if fuel = 0 then ParseFail "JSON nesting too deep" pos
  else
    // Skip whitespace
    let pos = match json_ws input pos with
      | ParseOk _ p -> p | _ -> pos in
    match safe_index input pos with
    | None -> ParseFail "unterminated object" pos
    | Some ch ->
      if FStar.Char.int_of_char ch = 0x7D then  // empty object }
        ParseOk (JObject []) (pos + 1)
      else
        parse_json_object_members input pos (fuel - 1) []

and parse_json_object_members (input:string) (pos:nat) (fuel:nat) (acc: list (string * json_value))
  : Tot (parse_result json_value) (decreases fuel) =
  if fuel = 0 then ParseFail "JSON nesting too deep" pos
  else
    // Skip whitespace, parse key
    let pos = match json_ws input pos with
      | ParseOk _ p -> p | _ -> pos in
    match parse_json_string input pos with
    | ParseFail msg fpos -> ParseFail msg fpos
    | ParseOk key pos1 ->
      // Skip whitespace, expect colon
      let pos1 = match json_ws input pos1 with
        | ParseOk _ p -> p | _ -> pos1 in
      (match safe_index input pos1 with
      | None -> ParseFail "expected colon" pos1
      | Some colon_ch ->
      if FStar.Char.int_of_char colon_ch <> 0x3A then  // :
        ParseFail "expected colon" pos1
      else
        // Parse value
        match parse_json_value input (pos1 + 1) (fuel - 1) with
        | ParseFail msg fpos -> ParseFail msg fpos
        | ParseOk value pos2 ->
          let acc = List.Tot.append acc [(key, value)] in
          // Skip whitespace, check for comma or closing brace
          let pos2 = match json_ws input pos2 with
            | ParseOk _ p -> p | _ -> pos2 in
          (match safe_index input pos2 with
          | None -> ParseFail "unterminated object" pos2
          | Some ch2 ->
            if FStar.Char.int_of_char ch2 = 0x7D then  // }
              ParseOk (JObject acc) (pos2 + 1)
            else if FStar.Char.int_of_char ch2 = 0x2C then  // ,
              parse_json_object_members input (pos2 + 1) (fuel - 1) acc
            else
              ParseFail "expected comma or closing brace" pos2))

and parse_json_array (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result json_value) (decreases fuel) =
  if fuel = 0 then ParseFail "JSON nesting too deep" pos
  else
    // Skip whitespace
    let pos = match json_ws input pos with
      | ParseOk _ p -> p | _ -> pos in
    match safe_index input pos with
    | None -> ParseFail "unterminated array" pos
    | Some ch ->
      if FStar.Char.int_of_char ch = 0x5D then  // empty array ]
        ParseOk (JArray []) (pos + 1)
      else
        parse_json_array_items input pos (fuel - 1) []

and parse_json_array_items (input:string) (pos:nat) (fuel:nat) (acc: list json_value)
  : Tot (parse_result json_value) (decreases fuel) =
  if fuel = 0 then ParseFail "JSON nesting too deep" pos
  else
    match parse_json_value input pos (fuel - 1) with
    | ParseFail msg fpos -> ParseFail msg fpos
    | ParseOk item pos1 ->
      let acc = List.Tot.append acc [item] in
      // Skip whitespace, check for comma or closing bracket
      let pos1 = match json_ws input pos1 with
        | ParseOk _ p -> p | _ -> pos1 in
      (match safe_index input pos1 with
      | None -> ParseFail "unterminated array" pos1
      | Some ch1 ->
        if FStar.Char.int_of_char ch1 = 0x5D then  // ]
          ParseOk (JArray acc) (pos1 + 1)
        else if FStar.Char.int_of_char ch1 = 0x2C then  // ,
          parse_json_array_items input (pos1 + 1) (fuel - 1) acc
        else
          ParseFail "expected comma or closing bracket" pos1)

// Top-level JSON parse
let parse_json (input:string) : option json_value =
  let fuel = String.length input in
  match parse_json_value input 0 fuel with
  | ParseOk v _ -> Some v
  | ParseFail _ _ -> None

// ================================================================
// JSON object helpers
// ================================================================

let json_get_field (key: string) (obj: json_value) : option json_value =
  match obj with
  | JObject fields ->
    (match List.Tot.find (fun (k, _) -> k = key) fields with
     | Some (_, v) -> Some v
     | None -> None)
  | _ -> None

let json_get_string (key: string) (obj: json_value) : option string =
  match json_get_field key obj with
  | Some (JString s) -> Some s
  | _ -> None

let json_get_bool (key: string) (obj: json_value) : option bool =
  match json_get_field key obj with
  | Some (JBool b) -> Some b
  | _ -> None

let json_get_array (key: string) (obj: json_value) : option (list json_value) =
  match json_get_field key obj with
  | Some (JArray items) -> Some items
  | _ -> None

let json_get_string_array (key: string) (obj: json_value) : option (list string) =
  match json_get_array key obj with
  | None -> None
  | Some items ->
    Some (List.Tot.concatMap (fun (v: json_value) ->
      match v with
      | JString s -> [s]
      | _ -> []
    ) items)

// ================================================================
// Helper: construct a T_Literal only if well-formed
// ================================================================

let mk_literal (lexical : string) (dt : string) (lang : option string) : option rdf_term =
  if is_iri dt then
    let lit : literal = {
      lexical_form = lexical;
      datatype = dt;
      lang_tag = lang
    } in
    if literal_wf lit then Some (T_Literal lit) else None
  else None

// ================================================================
// SRJ (SPARQL Results JSON) extraction
// ================================================================

// Parse a single binding value object:
//   {"type":"uri","value":"http://..."}
//   {"type":"literal","value":"foo"}
//   {"type":"literal","value":"foo","xml:lang":"en"}
//   {"type":"literal","value":"foo","datatype":"http://..."}
//   {"type":"bnode","value":"b0"}
let parse_binding_value (obj: json_value) : option rdf_term =
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
      (match lang, dt with
       | Some lang_val, _ ->
         mk_literal val_str rdf_lang_string (Some lang_val)
       | None, Some dt_val ->
         mk_literal val_str dt_val None
       | None, None ->
         mk_literal val_str xsd_string None)
    else None

// Parse a single binding row object:
//   {"x":{"type":"uri","value":"..."},"y":{"type":"literal","value":"..."}}
// Returns list of (var_name, rdf_term) pairs
let parse_binding_row (obj: json_value) : list (string * rdf_term) =
  match obj with
  | JObject fields ->
    List.Tot.concatMap (fun (pair: (string * json_value)) ->
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
