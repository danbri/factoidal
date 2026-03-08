(* N-Triples parser — UNVERIFIED TEST INFRASTRUCTURE.
   Not extracted from F*. Hand-written OCaml for loading W3C test data.
   Produces RDF_Graph_Executable types directly. *)

open RDF_Graph_Executable

let bnode_counter = ref 0

let fresh_bnode () =
  let id = Printf.sprintf "_:b%d" !bnode_counter in
  incr bnode_counter; id

let reset_bnodes () = bnode_counter := 0

exception Parse_error of string

type parser_state = {
  input : string;
  mutable pos : int;
}

let make_parser input = { input; pos = 0 }

let at_end ps = ps.pos >= String.length ps.input

let peek ps =
  if ps.pos < String.length ps.input then Some ps.input.[ps.pos] else None

let advance ps =
  if ps.pos < String.length ps.input then begin
    let c = ps.input.[ps.pos] in ps.pos <- ps.pos + 1; Some c
  end else None

let expect ps ch =
  match advance ps with
  | Some c when c = ch -> ()
  | _ -> raise (Parse_error (Printf.sprintf "Expected '%c' at %d" ch ps.pos))

let skip_ws ps =
  while ps.pos < String.length ps.input &&
        let c = ps.input.[ps.pos] in (c = ' ' || c = '\t') do
    ps.pos <- ps.pos + 1
  done

let is_hex c =
  (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')

let hex_val c =
  if c >= '0' && c <= '9' then Char.code c - Char.code '0'
  else if c >= 'a' && c <= 'f' then 10 + Char.code c - Char.code 'a'
  else 10 + Char.code c - Char.code 'A'

(* Encode a Unicode code point as UTF-8 *)
let utf8_of_codepoint cp =
  if cp < 0x80 then
    String.make 1 (Char.chr cp)
  else if cp < 0x800 then
    let b0 = 0xC0 lor (cp lsr 6) in
    let b1 = 0x80 lor (cp land 0x3F) in
    Printf.sprintf "%c%c" (Char.chr b0) (Char.chr b1)
  else if cp < 0x10000 then
    let b0 = 0xE0 lor (cp lsr 12) in
    let b1 = 0x80 lor ((cp lsr 6) land 0x3F) in
    let b2 = 0x80 lor (cp land 0x3F) in
    Printf.sprintf "%c%c%c" (Char.chr b0) (Char.chr b1) (Char.chr b2)
  else
    let b0 = 0xF0 lor (cp lsr 18) in
    let b1 = 0x80 lor ((cp lsr 12) land 0x3F) in
    let b2 = 0x80 lor ((cp lsr 6) land 0x3F) in
    let b3 = 0x80 lor (cp land 0x3F) in
    Printf.sprintf "%c%c%c%c" (Char.chr b0) (Char.chr b1) (Char.chr b2) (Char.chr b3)

(* Check if codepoint is a surrogate (invalid in UTF-8/RDF) *)
let is_surrogate cp = cp >= 0xD800 && cp <= 0xDFFF

let parse_hex_esc ps n =
  let hex = Buffer.create n in
  for _ = 1 to n do
    match advance ps with
    | Some c when is_hex c -> Buffer.add_char hex c
    | _ -> raise (Parse_error "Invalid hex digit")
  done;
  let cp = int_of_string ("0x" ^ Buffer.contents hex) in
  if is_surrogate cp then
    raise (Parse_error (Printf.sprintf "Surrogate codepoint U+%04X not allowed" cp));
  utf8_of_codepoint cp

(* Validate IRI characters: reject disallowed chars per RFC 3987 *)
let is_invalid_iri_char c =
  let code = Char.code c in
  c = ' ' || c = '<' || c = '>' || c = '{' || c = '}' || c = '"' ||
  c = '|' || c = '\\' || c = '^' || c = '`' || code < 0x20

let parse_iri_ref ps =
  expect ps '<';
  let buf = Buffer.create 64 in
  let rec loop () =
    match advance ps with
    | None -> raise (Parse_error "Unterminated IRI")
    | Some '>' -> Buffer.contents buf
    | Some '\\' ->
      (match advance ps with
       | Some 'u' -> Buffer.add_string buf (parse_hex_esc ps 4); loop ()
       | Some 'U' -> Buffer.add_string buf (parse_hex_esc ps 8); loop ()
       | _ -> raise (Parse_error "Invalid IRI escape"))
    | Some c when is_invalid_iri_char c ->
      raise (Parse_error (Printf.sprintf "Invalid char in IRI: U+%04X" (Char.code c)))
    | Some c -> Buffer.add_char buf c; loop ()
  in loop ()

(* Validate that IRI is absolute (contains scheme ':') — required by N-Triples *)
let validate_absolute_iri iri =
  (* An absolute IRI must have a scheme, i.e., something like "http:" *)
  let has_scheme =
    try
      let colon_pos = String.index iri ':' in
      (* Everything before ':' must be scheme chars: letter followed by letter/digit/+/-/. *)
      colon_pos > 0 &&
      (let c = iri.[0] in (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')) &&
      (let ok = ref true in
       for i = 1 to colon_pos - 1 do
         let c = iri.[i] in
         if not ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
                 (c >= '0' && c <= '9') || c = '+' || c = '-' || c = '.') then
           ok := false
       done;
       !ok)
    with Not_found -> false
  in
  if not has_scheme then
    raise (Parse_error (Printf.sprintf "Relative IRI not allowed in N-Triples: <%s>" iri))

let is_bnode_char c =
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
  (c >= '0' && c <= '9') || c = '_' || c = '-' || c = '.'

let parse_bnode_label ps =
  expect ps '_';
  expect ps ':';
  let buf = Buffer.create 16 in
  while ps.pos < String.length ps.input && is_bnode_char ps.input.[ps.pos] do
    Buffer.add_char buf ps.input.[ps.pos];
    ps.pos <- ps.pos + 1
  done;
  (* Remove trailing dots *)
  let s = ref (Buffer.contents buf) in
  while String.length !s > 0 && !s.[String.length !s - 1] = '.' do
    s := String.sub !s 0 (String.length !s - 1)
  done;
  if !s = "" then raise (Parse_error "Empty blank node label");
  !s

let parse_string_escape ps =
  match advance ps with
  | Some 't' -> "\t"
  | Some 'b' -> "\b"
  | Some 'n' -> "\n"
  | Some 'r' -> "\r"
  | Some 'f' -> String.make 1 (Char.chr 0x0C)
  | Some '"' -> "\""
  | Some '\'' -> "'"
  | Some '\\' -> "\\"
  | Some 'u' -> parse_hex_esc ps 4
  | Some 'U' -> parse_hex_esc ps 8
  | _ -> raise (Parse_error "Invalid escape")

let parse_literal ps =
  (* N-Triples only allows simple "..." strings, not triple-quoted *)
  if ps.pos + 2 < String.length ps.input &&
     ps.input.[ps.pos] = '"' && ps.input.[ps.pos + 1] = '"' && ps.input.[ps.pos + 2] = '"' then
    raise (Parse_error "Triple-quoted strings not allowed in N-Triples");
  expect ps '"';
  let buf = Buffer.create 64 in
  let rec loop () =
    match advance ps with
    | None -> raise (Parse_error "Unterminated literal")
    | Some '"' -> Buffer.contents buf
    | Some '\\' -> Buffer.add_string buf (parse_string_escape ps); loop ()
    | Some '\n' | Some '\r' ->
      raise (Parse_error "Newline not allowed in N-Triples string literal")
    | Some c -> Buffer.add_char buf c; loop ()
  in
  let lex = loop () in
  match peek ps with
  | Some '@' ->
    ps.pos <- ps.pos + 1;
    (* Language tag must start with a letter per BCP 47 *)
    (match peek ps with
     | Some c when (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') -> ()
     | _ -> raise (Parse_error "Language tag must start with a letter"));
    let lang = Buffer.create 8 in
    while ps.pos < String.length ps.input &&
          let c = ps.input.[ps.pos] in
          (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
          (c >= '0' && c <= '9') || c = '-' do
      Buffer.add_char lang ps.input.[ps.pos];
      ps.pos <- ps.pos + 1
    done;
    T_Literal { lexical_form = lex;
                datatype = rdf_lang_string;
                lang_tag = Some (Buffer.contents lang) }
  | Some '^' when ps.pos + 1 < String.length ps.input &&
                   ps.input.[ps.pos + 1] = '^' ->
    ps.pos <- ps.pos + 2;
    let dt = parse_iri_ref ps in
    validate_absolute_iri dt;
    T_Literal { lexical_form = lex; datatype = dt; lang_tag = None }
  | _ ->
    T_Literal { lexical_form = lex; datatype = xsd_string; lang_tag = None }

let parse_nt_line line bnode_map =
  let ps = make_parser line in
  skip_ws ps;
  if at_end ps then None
  else begin
    (* Subject *)
    let s = match peek ps with
      | Some '<' ->
        let iri_str = parse_iri_ref ps in
        validate_absolute_iri iri_str;
        S_IRI iri_str
      | Some '_' ->
        let label = parse_bnode_label ps in
        let id = match Hashtbl.find_opt bnode_map label with
          | Some id -> id
          | None -> let id = fresh_bnode () in Hashtbl.add bnode_map label id; id
        in S_BNode id
      | _ -> raise (Parse_error "Expected subject")
    in
    skip_ws ps;
    (* Predicate — must be absolute IRI *)
    let p = match peek ps with
      | Some '<' ->
        let iri_str = parse_iri_ref ps in
        validate_absolute_iri iri_str;
        iri_str
      | _ -> raise (Parse_error "Expected predicate")
    in
    skip_ws ps;
    (* Object *)
    let o = match peek ps with
      | Some '<' ->
        let iri_str = parse_iri_ref ps in
        validate_absolute_iri iri_str;
        T_IRI iri_str
      | Some '_' ->
        let label = parse_bnode_label ps in
        let id = match Hashtbl.find_opt bnode_map label with
          | Some id -> id
          | None -> let id = fresh_bnode () in Hashtbl.add bnode_map label id; id
        in T_BNode id
      | Some '"' -> parse_literal ps
      | _ -> raise (Parse_error "Expected object")
    in
    skip_ws ps;
    (* N-Triples requires '.' terminator *)
    (match peek ps with
     | Some '.' -> ps.pos <- ps.pos + 1
     | Some ',' -> raise (Parse_error "Comma not allowed in N-Triples")
     | Some ';' -> raise (Parse_error "Semicolon not allowed in N-Triples")
     | _ -> ());
    (* After dot, only whitespace or comment allowed *)
    skip_ws ps;
    if not (at_end ps) then begin
      match peek ps with
      | Some '#' -> ()  (* comment — ok *)
      | _ -> raise (Parse_error (Printf.sprintf "Extra content after triple at %d" ps.pos))
    end;
    Some { s; p; o }
  end

let parse_ntriples input =
  let bnode_map = Hashtbl.create 16 in
  let lines = String.split_on_char '\n' input in
  List.filter_map (fun line ->
    let trimmed = String.trim line in
    if trimmed = "" || trimmed.[0] = '#' then None
    else
      try parse_nt_line trimmed bnode_map
      with Parse_error msg ->
        raise (Parse_error (Printf.sprintf "%s: %s" msg trimmed))
  ) lines
