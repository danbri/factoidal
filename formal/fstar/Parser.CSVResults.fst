module Parser.CSVResults

(** ======================================================================== **)
(** SPARQL CSV/TSV Results Format Parser                                      **)
(**                                                                          **)
(** W3C Specifications:                                                      **)
(**   https://www.w3.org/TR/sparql11-results-csv-tsv/                        **)
(**                                                                          **)
(** CSV format:                                                              **)
(**   - Header: variable names (no ? prefix), comma-separated               **)
(**   - Rows: values comma-separated                                         **)
(**   - IRIs: bare (no angle brackets)                                       **)
(**   - Blank nodes: _:label                                                 **)
(**   - Literals: plain values (no quotes unless containing comma/newline)   **)
(**   - Quoted fields: "..." with "" for escaped quote                       **)
(**   - Empty field = unbound                                                **)
(**                                                                          **)
(** TSV format:                                                              **)
(**   - Header: variable names (with ? prefix), tab-separated               **)
(**   - Rows: values tab-separated                                           **)
(**   - IRIs: <...>                                                          **)
(**   - Blank nodes: _:label                                                 **)
(**   - Literals: "string", "string"@lang, "string"^^<datatype>             **)
(**   - Numeric literals: bare integers/decimals/doubles                     **)
(**   - Empty field = unbound                                                **)
(** ======================================================================== **)

open FStar.String
open FStar.List.Tot
open Parser.Combinators
open RDF.Graph.Executable

(** Helper: construct a T_Literal only if well-formed *)
let mk_literal (lexical : string) (dt : string) (lang : option string) : option rdf_term =
  if is_iri dt then
    let lit : literal = {
      lexical_form = lexical;
      datatype = dt;
      lang_tag = lang
    } in
    if literal_wf lit then Some (T_Literal lit) else None
  else None

(* ================================================================ *)
(* Helper: line splitting                                           *)
(* ================================================================ *)

(** Split a string into lines on LF or CRLF boundaries.
    We process the character list manually for termination. *)
let rec split_lines_acc (cs : list FStar.Char.char) (acc : list FStar.Char.char)
  : Tot (list (list FStar.Char.char)) (decreases (List.Tot.length cs)) =
  match cs with
  | [] ->
    (* emit final accumulated line *)
    [List.Tot.rev acc]
  | c :: rest ->
    let code = FStar.Char.int_of_char c in
    if code = 0x0A then  (* LF *)
      List.Tot.rev acc :: split_lines_acc rest []
    else if code = 0x0D then  (* CR *)
      (* check for CRLF *)
      (match rest with
       | c2 :: rest2 ->
         if FStar.Char.int_of_char c2 = 0x0A
         then List.Tot.rev acc :: split_lines_acc rest2 []
         else List.Tot.rev acc :: split_lines_acc rest []
       | [] -> [List.Tot.rev acc])
    else
      split_lines_acc rest (c :: acc)

let split_lines (s : string) : list string =
  let char_lists = split_lines_acc (String.list_of_string s) [] in
  List.Tot.map String.string_of_list char_lists

(** Remove trailing empty lines (common in files ending with newline) *)
let rev_length_lemma (#a:Type) (l : list a)
  : Lemma (List.Tot.length (List.Tot.rev l) = List.Tot.length l)
  = List.Tot.rev_length l

let rec remove_trailing_empty (lines : list string)
  : Tot (list string) (decreases (List.Tot.length lines)) =
  match lines with
  | [] -> []
  | _ ->
    let rev = List.Tot.rev lines in
    (match rev with
     | [] -> []
     | last :: rest ->
       if String.length last = 0
       then begin
         rev_length_lemma rest;
         rev_length_lemma lines;
         remove_trailing_empty (List.Tot.rev rest)
       end
       else lines)

(* ================================================================ *)
(* Helper: split on separator character                             *)
(* ================================================================ *)

(** Split a string on a separator, respecting CSV double-quoted fields.
    Inside a quoted field (started by "), the separator and newlines are
    literal. A doubled quote "" inside a quoted field represents a single ".
    Returns a list of raw field strings (quotes not yet stripped). *)
let rec csv_split_fields_acc
  (cs : list FStar.Char.char)
  (sep : FStar.Char.char)
  (in_quote : bool)
  (acc : list FStar.Char.char)
  : Tot (list string) (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> [String.string_of_list (List.Tot.rev acc)]
  | c :: rest ->
    let code = FStar.Char.int_of_char c in
    if in_quote then
      (* Inside a quoted field *)
      if code = 0x22 then  (* double quote *)
        (match rest with
         | c2 :: rest2 ->
           if FStar.Char.int_of_char c2 = 0x22 then
             (* escaped quote "" -> single " *)
             csv_split_fields_acc rest2 sep true (c :: acc)
           else
             (* closing quote *)
             csv_split_fields_acc rest sep false acc
         | [] ->
           (* closing quote at end *)
           [String.string_of_list (List.Tot.rev acc)])
      else
        csv_split_fields_acc rest sep true (c :: acc)
    else
      (* Outside a quoted field *)
      if c = sep then
        (* field separator *)
        String.string_of_list (List.Tot.rev acc) :: csv_split_fields_acc rest sep false []
      else if code = 0x22 then
        (* opening quote *)
        csv_split_fields_acc rest sep true acc
      else
        csv_split_fields_acc rest sep false (c :: acc)

let csv_split_fields (line : string) (sep : FStar.Char.char) : list string =
  csv_split_fields_acc (String.list_of_string line) sep false []

(** Simple tab split (no quoting for TSV per W3C spec — TSV fields are not quoted
    at the field level; quotes are part of the RDF term syntax) *)
let rec tsv_split_fields_acc
  (cs : list FStar.Char.char)
  (acc : list FStar.Char.char)
  : Tot (list string) (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> [String.string_of_list (List.Tot.rev acc)]
  | c :: rest ->
    if FStar.Char.int_of_char c = 0x09 then  (* TAB *)
      String.string_of_list (List.Tot.rev acc) :: tsv_split_fields_acc rest []
    else
      tsv_split_fields_acc rest (c :: acc)

let tsv_split_fields (line : string) : list string =
  tsv_split_fields_acc (String.list_of_string line) []

(* ================================================================ *)
(* CSV header parser                                                *)
(* ================================================================ *)

(** Parse CSV header line: variable names without ? prefix, comma-separated *)
let parse_csv_header (line : string) : option (list var_name) =
  let fields = csv_split_fields line (FStar.Char.char_of_int 0x2C) in  (* comma *)
  if List.Tot.length fields = 0 then None
  else Some fields

(* ================================================================ *)
(* TSV header parser                                                *)
(* ================================================================ *)

(** Strip leading ? from a TSV variable name *)
let strip_question_mark (s : string) : string =
  let cs = String.list_of_string s in
  match cs with
  | c :: rest ->
    if FStar.Char.int_of_char c = 0x3F then  (* '?' *)
      String.string_of_list rest
    else s
  | [] -> s

(** Parse TSV header line: variable names with ? prefix, tab-separated *)
let parse_tsv_header (line : string) : option (list var_name) =
  let fields = tsv_split_fields line in
  if List.Tot.length fields = 0 then None
  else Some (List.Tot.map strip_question_mark fields)

(* ================================================================ *)
(* CSV value parser                                                 *)
(* ================================================================ *)

(** Check if a string looks like a blank node: _:label *)
let is_blank_node_str (s : string) : bool =
  let cs = String.list_of_string s in
  match cs with
  | c1 :: c2 :: _ ->
    FStar.Char.int_of_char c1 = 0x5F &&   (* '_' *)
    FStar.Char.int_of_char c2 = 0x3A      (* ':' *)
  | _ -> false

(** Extract blank node label after _: *)
let bnode_label (s : string) : string =
  if String.length s > 2
  then String.sub s 2 (String.length s - 2)
  else ""

(** Check if a character is an ASCII digit *)
let is_ascii_digit (c : FStar.Char.char) : bool =
  let code = FStar.Char.int_of_char c in
  code >= 0x30 && code <= 0x39

(** Check if a string looks like a number (integer, decimal, or double).
    Matches: optional sign, digits, optional decimal part, optional exponent. *)
let rec all_digits (cs : list FStar.Char.char) : bool =
  match cs with
  | [] -> true
  | c :: rest -> is_ascii_digit c && all_digits rest

let is_numeric_str (s : string) : bool =
  let cs = String.list_of_string s in
  let len = String.length s in
  if len = 0 then false
  else
    (* Simple heuristic: starts with digit, +, -, or . followed by digit *)
    match cs with
    | c :: _ ->
      let code = FStar.Char.int_of_char c in
      (is_ascii_digit c) ||
      (code = 0x2D) ||  (* '-' *)
      (code = 0x2B) ||  (* '+' *)
      (code = 0x2E &&   (* '.' followed by digit *)
        (match cs with
         | _ :: c2 :: _ -> is_ascii_digit c2
         | _ -> false))
    | [] -> false

(** Check if a string looks like an IRI (contains :// heuristic for CSV).
    In CSV format, IRIs are bare (no angle brackets). We detect them by
    checking for a colon which is the IRI scheme separator. *)
let looks_like_iri (s : string) : bool =
  is_iri s  (* reuse from RDF.Graph.Executable: non-empty and contains colon *)

(** Parse a single CSV field into an optional rdf_term.
    CSV format is lossy — we use heuristics:
    - Empty string -> None (unbound)
    - _:label -> blank node
    - Contains colon (IRI-like) -> IRI
    - Otherwise -> plain literal with xsd:string datatype *)
let parse_csv_value (field : string) : option rdf_term =
  if String.length field = 0 then None  (* unbound *)
  else if is_blank_node_str field then
    Some (T_BNode (bnode_label field))
  else if looks_like_iri field then
    Some (T_IRI field)
  else
    (* Plain literal — CSV format does not preserve datatype info *)
    mk_literal field xsd_string None

(** Parse a CSV data row into a list of optional rdf_terms *)
let parse_csv_row (line : string) : list (option rdf_term) =
  let fields = csv_split_fields line (FStar.Char.char_of_int 0x2C) in
  List.Tot.map parse_csv_value fields

(* ================================================================ *)
(* TSV value parser                                                 *)
(* ================================================================ *)

(** Parse a TSV IRI field: <iri> -> iri string *)
let parse_tsv_iri (s : string) : option rdf_term =
  let cs = String.list_of_string s in
  let len = String.length s in
  if len >= 2 then
    match cs with
    | c :: _ ->
      if FStar.Char.int_of_char c = 0x3C then  (* '<' *)
        let last_chars = String.list_of_string s in
        (* Check that it ends with > *)
        let rev = List.Tot.rev last_chars in
        (match rev with
         | cl :: _ ->
           if FStar.Char.int_of_char cl = 0x3E then  (* '>' *)
             let inner = String.sub s 1 (len - 2) in
             if is_iri inner then Some (T_IRI inner)
             else None
           else None
         | [] -> None)
      else None
    | [] -> None
  else None

(** Find the position of ^^ in a character list, returning index or -1.
    We look for two consecutive ^ characters (0x5E). *)
let rec find_double_caret (cs : list FStar.Char.char) (idx : nat)
  : Tot (option nat) (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> None
  | c1 :: rest ->
    if FStar.Char.int_of_char c1 = 0x5E then
      (match rest with
       | c2 :: _ ->
         if FStar.Char.int_of_char c2 = 0x5E then Some idx
         else find_double_caret rest (idx + 1)
       | [] -> None)
    else find_double_caret rest (idx + 1)

(** Find the last @ in a string that is after the closing quote.
    For "string"@lang, the @ is at position after the closing ".
    We search from the end. *)
let rec find_last_at (cs : list FStar.Char.char) (idx : nat)
  : Tot (option nat) (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> None
  | c :: rest ->
    let sub_result = find_last_at rest (idx + 1) in
    if FStar.Char.int_of_char c = 0x40 then  (* '@' *)
      (match sub_result with
       | Some _ -> sub_result  (* prefer later @ *)
       | None -> Some idx)
    else sub_result

(** Strip surrounding double quotes from a string *)
let strip_quotes (s : string) : string =
  let len = String.length s in
  if len >= 2 then
    let cs = String.list_of_string s in
    match cs with
    | c :: _ ->
      if FStar.Char.int_of_char c = 0x22 then  (* '"' *)
        let rev = List.Tot.rev cs in
        (match rev with
         | cl :: _ ->
           if FStar.Char.int_of_char cl = 0x22 then
             String.sub s 1 (len - 2)
           else s
         | [] -> s)
      else s
    | [] -> s
  else s

(** Check if string starts with a double quote *)
let starts_with_quote (s : string) : bool =
  let cs = String.list_of_string s in
  match cs with
  | c :: _ -> FStar.Char.int_of_char c = 0x22
  | [] -> false

(** Extract IRI from <iri> string *)
let extract_angle_iri (s : string) : option string =
  let len = String.length s in
  if len >= 2 then
    let cs = String.list_of_string s in
    match cs with
    | c :: _ ->
      if FStar.Char.int_of_char c = 0x3C then
        let rev = List.Tot.rev cs in
        (match rev with
         | cl :: _ ->
           if FStar.Char.int_of_char cl = 0x3E then
             Some (String.sub s 1 (len - 2))
           else None
         | [] -> None)
      else None
    | [] -> None
  else None

(** Parse a TSV quoted literal: "lexical"^^<datatype> or "lexical"@lang or "lexical"
    The field starts with a double quote. *)
let parse_tsv_quoted_literal (s : string) : option rdf_term =
  let cs = String.list_of_string s in
  let len = String.length s in
  if len < 2 then None
  else
    (* Find the closing quote position — scan for first unescaped " after position 0 *)
    (* Look for ^^ first *)
    let caret_pos = find_double_caret cs 0 in
    match caret_pos with
    | Some cp ->
      if cp >= 2 && cp <= len then  (* at least "x"^^<dt>, and in bounds *)
        let quoted_part = String.sub s 0 cp in
        let lexical = strip_quotes quoted_part in
        let rest_str = if cp + 2 < len then String.sub s (cp + 2) (len - cp - 2) else "" in
        (* rest_str should be <datatype> *)
        (match extract_angle_iri rest_str with
         | Some dt_str ->
           if is_iri dt_str then
             mk_literal lexical dt_str None
           else None
         | None -> None)
      else None
    | None ->
      (* No ^^, check for @lang *)
      let at_pos = find_last_at cs 0 in
      (match at_pos with
       | Some ap ->
         if ap >= 2 && ap < len then  (* at least "x"@lang, and in bounds *)
           (* Verify that character before @ is a closing quote *)
           let prev_char = String.index s (ap - 1) in
           if FStar.Char.int_of_char prev_char = 0x22 then  (* '"' *)
             let quoted_part = String.sub s 0 ap in
             let lexical = strip_quotes quoted_part in
             let lang = if ap + 1 < len then String.sub s (ap + 1) (len - ap - 1) else "" in
             mk_literal lexical rdf_lang_string (Some lang)
           else
             (* @ is inside the string, treat as plain literal *)
             let lexical = strip_quotes s in
             mk_literal lexical xsd_string None
         else
           let lexical = strip_quotes s in
           mk_literal lexical xsd_string None
       | None ->
         (* Plain quoted string — xsd:string *)
         let lexical = strip_quotes s in
         mk_literal lexical xsd_string None)

(** Check if a string looks like an integer: optional sign + digits *)
let rec is_all_digits (cs : list FStar.Char.char)
  : Tot bool (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> true
  | c :: rest -> is_ascii_digit c && is_all_digits rest

let is_integer_str (s : string) : bool =
  let cs = String.list_of_string s in
  match cs with
  | [] -> false
  | c :: rest ->
    let code = FStar.Char.int_of_char c in
    if code = 0x2D || code = 0x2B then  (* +/- *)
      List.Tot.length rest > 0 && is_all_digits rest
    else
      is_ascii_digit c && is_all_digits rest

(** Check if a string looks like a decimal: optional sign, digits, '.', digits *)
let rec has_dot (cs : list FStar.Char.char)
  : Tot bool (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> false
  | c :: rest ->
    FStar.Char.int_of_char c = 0x2E || has_dot rest

let is_decimal_str (s : string) : bool =
  let cs = String.list_of_string s in
  let len = String.length s in
  if len = 0 then false
  else
    let (sign_stripped : list FStar.Char.char) =
      match cs with
      | c :: rest ->
        let code = FStar.Char.int_of_char c in
        if code = 0x2D || code = 0x2B then rest else cs
      | [] -> cs
    in
    (* Must have a dot and all chars must be digits or dot *)
    has_dot sign_stripped &&
    (let rec all_digit_or_dot (l : list FStar.Char.char)
       : Tot bool (decreases (List.Tot.length l)) =
       match l with
       | [] -> true
       | c :: rest -> (is_ascii_digit c || FStar.Char.int_of_char c = 0x2E) && all_digit_or_dot rest
     in all_digit_or_dot sign_stripped)

(** Check if a string looks like a double: contains 'e' or 'E' *)
let rec has_exponent (cs : list FStar.Char.char)
  : Tot bool (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> false
  | c :: rest ->
    let code = FStar.Char.int_of_char c in
    (code = 0x65 || code = 0x45) || has_exponent rest  (* 'e' or 'E' *)

let is_double_str (s : string) : bool =
  has_exponent (String.list_of_string s)

(** Parse a single TSV field into an optional rdf_term.
    TSV format preserves more type information than CSV. *)
let parse_tsv_value (field : string) : option rdf_term =
  if String.length field = 0 then None  (* unbound *)
  else
    let cs = String.list_of_string field in
    match cs with
    | c :: _ ->
      let code = FStar.Char.int_of_char c in
      if code = 0x3C then  (* '<' — IRI *)
        parse_tsv_iri field
      else if code = 0x22 then  (* '"' — quoted literal *)
        parse_tsv_quoted_literal field
      else if code = 0x5F then  (* '_' — possibly blank node *)
        if is_blank_node_str field then
          Some (T_BNode (bnode_label field))
        else
          (* Fallback: treat as plain literal *)
          mk_literal field xsd_string None
      else if is_integer_str field then
        (* Bare integer *)
        mk_literal field xsd_integer None
      else if is_double_str field then
        (* Bare double (must check before decimal since doubles also have dots) *)
        mk_literal field xsd_double None
      else if is_decimal_str field then
        (* Bare decimal *)
        mk_literal field xsd_decimal None
      else
        (* Fallback: plain literal *)
        mk_literal field xsd_string None
    | [] -> None

(** Parse a TSV data row into a list of optional rdf_terms *)
let parse_tsv_row (line : string) : list (option rdf_term) =
  let fields = tsv_split_fields line in
  List.Tot.map parse_tsv_value fields

(* ================================================================ *)
(* Top-level CSV/TSV result parsers                                 *)
(* ================================================================ *)

(** Pad or truncate a row to match the expected number of columns.
    If the row has fewer fields than variables, pad with None.
    If it has more, truncate to match. *)
let rec pad_row (row : list (option rdf_term)) (n : nat)
  : Tot (list (option rdf_term)) (decreases n) =
  if n = 0 then []
  else
    match row with
    | [] -> None :: pad_row [] (n - 1)
    | v :: rest -> v :: pad_row rest (n - 1)

(** Parse a complete CSV results string.
    Returns the list of variable names and the list of rows,
    where each row is a list of optional rdf_terms aligned with the variables. *)
let parse_csv_results (input : string)
  : option (list var_name * list (list (option rdf_term))) =
  let lines = remove_trailing_empty (split_lines input) in
  match lines with
  | [] -> None  (* no header *)
  | header_line :: data_lines ->
    match parse_csv_header header_line with
    | None -> None
    | Some vars ->
      let nvars = List.Tot.length vars in
      let rows = List.Tot.map
        (fun (line : string) ->
          let raw = parse_csv_row line in
          pad_row raw nvars)
        data_lines
      in
      Some (vars, rows)

(** Parse a complete TSV results string.
    Returns the list of variable names and the list of rows,
    where each row is a list of optional rdf_terms aligned with the variables. *)
let parse_tsv_results (input : string)
  : option (list var_name * list (list (option rdf_term))) =
  let lines = remove_trailing_empty (split_lines input) in
  match lines with
  | [] -> None  (* no header *)
  | header_line :: data_lines ->
    match parse_tsv_header header_line with
    | None -> None
    | Some vars ->
      let nvars = List.Tot.length vars in
      let rows = List.Tot.map
        (fun (line : string) ->
          let raw = parse_tsv_row line in
          pad_row raw nvars)
        data_lines
      in
      Some (vars, rows)

(* ================================================================ *)
(* Conversion to solution mappings                                  *)
(* ================================================================ *)

(** Build a solution_mapping from a list of variable names and a row of values.
    Only includes bindings where the value is Some. *)
let rec build_solution_mapping (vars : list var_name) (vals : list (option rdf_term))
  : Tot solution_mapping (decreases vars) =
  match vars, vals with
  | [], _ -> []
  | _ :: _, [] -> []
  | v :: vrest, oval :: orest ->
    (match oval with
     | Some term -> (v, term) :: build_solution_mapping vrest orest
     | None -> build_solution_mapping vrest orest)

(** Convert parsed CSV/TSV results into a list of solution_mappings *)
let results_to_solution_mappings
  (vars : list var_name)
  (rows : list (list (option rdf_term)))
  : list solution_mapping =
  List.Tot.map (build_solution_mapping vars) rows

(** All-in-one: parse CSV and return solution mappings *)
let parse_csv_to_solutions (input : string)
  : option (list var_name * list solution_mapping) =
  match parse_csv_results input with
  | None -> None
  | Some (vars, rows) ->
    Some (vars, results_to_solution_mappings vars rows)

(** All-in-one: parse TSV and return solution mappings *)
let parse_tsv_to_solutions (input : string)
  : option (list var_name * list solution_mapping) =
  match parse_tsv_results input with
  | None -> None
  | Some (vars, rows) ->
    Some (vars, results_to_solution_mappings vars rows)
