(* N-Quads parser — UNVERIFIED TEST INFRASTRUCTURE.
   Not extracted from F*. Hand-written OCaml for W3C N-Quads syntax tests.
   N-Quads extends N-Triples with an optional 4th element (graph name).
   For our purposes we parse and discard the graph name, returning triples. *)

open RDF_Graph_Executable

exception Parse_error of string

(* An N-Quads line is: subject predicate object [graphLabel] '.'
   where graphLabel is optional and can be an IRI or blank node.
   We reuse ntriples_parser internals where possible. *)

type nq_state = {
  input : string;
  len : int;
  mutable pos : int;
}

let make_state s = { input = s; len = String.length s; pos = 0 }

let peek st = if st.pos < st.len then Some st.input.[st.pos] else None
let advance st = st.pos <- st.pos + 1
let remaining st = st.len - st.pos

let skip_whitespace st =
  while st.pos < st.len && (st.input.[st.pos] = ' ' || st.input.[st.pos] = '\t') do
    advance st
  done

let skip_line st =
  while st.pos < st.len && st.input.[st.pos] <> '\n' && st.input.[st.pos] <> '\r' do
    advance st
  done;
  (* skip newline *)
  if st.pos < st.len && st.input.[st.pos] = '\r' then advance st;
  if st.pos < st.len && st.input.[st.pos] = '\n' then advance st

(* Parse a unicode escape \uXXXX or \UXXXXXXXX *)
let parse_hex_escape st n =
  let hex = Buffer.create n in
  for _ = 1 to n do
    if st.pos >= st.len then raise (Parse_error "Unexpected end in unicode escape");
    Buffer.add_char hex st.input.[st.pos];
    advance st
  done;
  let cp = int_of_string ("0x" ^ Buffer.contents hex) in
  let buf = Buffer.create 4 in
  if cp < 0x80 then
    Buffer.add_char buf (Char.chr cp)
  else if cp < 0x800 then begin
    Buffer.add_char buf (Char.chr (0xC0 lor (cp lsr 6)));
    Buffer.add_char buf (Char.chr (0x80 lor (cp land 0x3F)))
  end else if cp < 0x10000 then begin
    Buffer.add_char buf (Char.chr (0xE0 lor (cp lsr 12)));
    Buffer.add_char buf (Char.chr (0x80 lor ((cp lsr 6) land 0x3F)));
    Buffer.add_char buf (Char.chr (0x80 lor (cp land 0x3F)))
  end else begin
    Buffer.add_char buf (Char.chr (0xF0 lor (cp lsr 18)));
    Buffer.add_char buf (Char.chr (0x80 lor ((cp lsr 12) land 0x3F)));
    Buffer.add_char buf (Char.chr (0x80 lor ((cp lsr 6) land 0x3F)));
    Buffer.add_char buf (Char.chr (0x80 lor (cp land 0x3F)))
  end;
  Buffer.contents buf

let parse_iri st =
  if peek st <> Some '<' then raise (Parse_error "Expected '<' for IRI");
  advance st;
  let buf = Buffer.create 64 in
  let rec loop () =
    if st.pos >= st.len then raise (Parse_error "Unterminated IRI");
    let c = st.input.[st.pos] in
    if c = '>' then (advance st; Buffer.contents buf)
    else if c = '\\' then begin
      advance st;
      if st.pos >= st.len then raise (Parse_error "Unterminated escape in IRI");
      (match st.input.[st.pos] with
       | 'u' -> advance st; Buffer.add_string buf (parse_hex_escape st 4); loop ()
       | 'U' -> advance st; Buffer.add_string buf (parse_hex_escape st 8); loop ()
       | _ -> raise (Parse_error "Invalid escape in IRI"))
    end else if c = ' ' || c = '{' || c = '}' || c = '|' || c = '^' || c = '`' then
      raise (Parse_error (Printf.sprintf "Invalid character in IRI: %c" c))
    else begin
      Buffer.add_char buf c; advance st; loop ()
    end
  in
  loop ()

let parse_bnode st =
  if remaining st < 2 || st.input.[st.pos] <> '_' || st.input.[st.pos + 1] <> ':' then
    raise (Parse_error "Expected '_:' for blank node");
  st.pos <- st.pos + 2;
  let buf = Buffer.create 16 in
  Buffer.add_string buf "_:";
  while st.pos < st.len &&
        let c = st.input.[st.pos] in
        (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
        (c >= '0' && c <= '9') || c = '_' || c = '-' || c = '.' do
    Buffer.add_char buf st.input.[st.pos];
    advance st
  done;
  (* Remove trailing dots *)
  let s = Buffer.contents buf in
  let len = String.length s in
  let last = ref (len - 1) in
  while !last > 1 && s.[!last] = '.' do decr last done;
  if !last < len - 1 then begin
    st.pos <- st.pos - (len - 1 - !last);
    String.sub s 0 (!last + 1)
  end else s

let parse_string_escape st =
  (* st.pos is right after the backslash *)
  if st.pos >= st.len then raise (Parse_error "Unterminated escape");
  let c = st.input.[st.pos] in
  advance st;
  match c with
  | 'n' -> "\n" | 'r' -> "\r" | 't' -> "\t"
  | '\\' -> "\\" | '"' -> "\""
  | 'u' -> parse_hex_escape st 4
  | 'U' -> parse_hex_escape st 8
  | _ -> raise (Parse_error (Printf.sprintf "Invalid string escape: \\%c" c))

let parse_string_literal st =
  if peek st <> Some '"' then raise (Parse_error "Expected '\"'");
  advance st;
  let buf = Buffer.create 64 in
  let rec loop () =
    if st.pos >= st.len then raise (Parse_error "Unterminated string");
    let c = st.input.[st.pos] in
    if c = '"' then (advance st; Buffer.contents buf)
    else if c = '\\' then begin
      advance st;
      Buffer.add_string buf (parse_string_escape st);
      loop ()
    end else if c = '\n' || c = '\r' then
      raise (Parse_error "Newline in N-Triples/N-Quads string literal")
    else begin
      Buffer.add_char buf c; advance st; loop ()
    end
  in
  loop ()

let parse_langtag st =
  if peek st <> Some '@' then None
  else begin
    advance st;
    let buf = Buffer.create 8 in
    while st.pos < st.len &&
          let c = st.input.[st.pos] in
          (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
          (c >= '0' && c <= '9') || c = '-' do
      Buffer.add_char buf st.input.[st.pos];
      advance st
    done;
    if Buffer.length buf = 0 then raise (Parse_error "Empty language tag");
    Some (Buffer.contents buf)
  end

let parse_literal st =
  let lex = parse_string_literal st in
  skip_whitespace st;
  if st.pos + 1 < st.len && st.input.[st.pos] = '^' && st.input.[st.pos + 1] = '^' then begin
    st.pos <- st.pos + 2;
    skip_whitespace st;
    let dt = parse_iri st in
    T_Literal { lexical_form = lex; datatype = dt; lang_tag = None }
  end else
    match parse_langtag st with
    | Some lang ->
      T_Literal { lexical_form = lex; datatype = rdf_lang_string; lang_tag = Some lang }
    | None ->
      T_Literal { lexical_form = lex; datatype = xsd_string; lang_tag = None }

let parse_subject st =
  match peek st with
  | Some '<' -> S_IRI (parse_iri st)
  | Some '_' -> S_BNode (parse_bnode st)
  | Some c -> raise (Parse_error (Printf.sprintf "Invalid subject char: %c" c))
  | None -> raise (Parse_error "Unexpected end of input")

let parse_object st =
  match peek st with
  | Some '<' -> T_IRI (parse_iri st)
  | Some '_' -> T_BNode (parse_bnode st)
  | Some '"' -> parse_literal st
  | Some c -> raise (Parse_error (Printf.sprintf "Invalid object char: %c" c))
  | None -> raise (Parse_error "Unexpected end of input")

(* Parse optional graph label (IRI or blank node), skip it *)
let skip_graph_label st =
  match peek st with
  | Some '<' -> ignore (parse_iri st)
  | Some '_' -> ignore (parse_bnode st)
  | _ -> ()

let parse_nquads input =
  let st = make_state input in
  let triples = ref [] in
  while st.pos < st.len do
    skip_whitespace st;
    match peek st with
    | None -> ()
    | Some '\n' | Some '\r' -> skip_line st
    | Some '#' -> skip_line st
    | _ ->
      let subj = parse_subject st in
      skip_whitespace st;
      let pred = parse_iri st in
      skip_whitespace st;
      let obj = parse_object st in
      skip_whitespace st;
      (* Optional graph label *)
      skip_graph_label st;
      skip_whitespace st;
      (match peek st with
       | Some '.' -> advance st
       | Some c -> raise (Parse_error (Printf.sprintf "Expected '.' but got '%c' at pos %d" c st.pos))
       | None -> raise (Parse_error "Expected '.' at end of statement"));
      triples := { s = subj; p = pred; o = obj } :: !triples;
      (* Skip to end of line *)
      skip_whitespace st;
      (match peek st with
       | Some '#' -> skip_line st
       | Some '\n' | Some '\r' -> skip_line st
       | None -> ()
       | Some c -> raise (Parse_error (Printf.sprintf "Unexpected char after statement: %c at pos %d" c st.pos)))
  done;
  List.rev !triples
