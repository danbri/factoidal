(* Turtle parser — UNVERIFIED TEST INFRASTRUCTURE.
   Not extracted from F*. Hand-written OCaml for loading W3C test data
   and manifest files. Produces RDF_Graph_Executable types directly. *)

open RDF_Graph_Executable
open Ntriples_parser  (* reuse: fresh_bnode, parse_hex_esc, parse_string_escape, utf8_of_codepoint *)

let rdf_type = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let rdf_first = "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"
let rdf_rest = "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"
let rdf_nil = "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"

type turtle_parser = {
  input : string;
  mutable pos : int;
  prefixes : (string, string) Hashtbl.t;
  mutable base : string option;
  graph : triple list ref;
  bnode_labels : (string, string) Hashtbl.t;
}

let make_turtle_parser input base_iri =
  { input; pos = 0;
    prefixes = Hashtbl.create 16;
    base = base_iri;
    graph = ref [];
    bnode_labels = Hashtbl.create 16 }

let tp_peek tp = if tp.pos < String.length tp.input then Some tp.input.[tp.pos] else None
let tp_advance tp =
  if tp.pos < String.length tp.input then begin
    let c = tp.input.[tp.pos] in tp.pos <- tp.pos + 1; Some c
  end else None
let tp_at_end tp = tp.pos >= String.length tp.input
let tp_expect tp ch =
  match tp_advance tp with
  | Some c when c = ch -> ()
  | _ -> raise (Parse_error (Printf.sprintf "Expected '%c' at %d" ch tp.pos))
let tp_starts_with tp s =
  let len = String.length s in
  tp.pos + len <= String.length tp.input &&
  String.sub tp.input tp.pos len = s

(* Case-insensitive keyword check *)
let tp_starts_with_ci tp s =
  let len = String.length s in
  tp.pos + len <= String.length tp.input &&
  String.lowercase_ascii (String.sub tp.input tp.pos len) = String.lowercase_ascii s

let tp_skip_ws tp =
  let rec loop () =
    (* skip whitespace *)
    while tp.pos < String.length tp.input &&
          let c = tp.input.[tp.pos] in
          c = ' ' || c = '\t' || c = '\n' || c = '\r' do
      tp.pos <- tp.pos + 1
    done;
    (* skip comments *)
    if tp.pos < String.length tp.input && tp.input.[tp.pos] = '#' then begin
      while tp.pos < String.length tp.input &&
            tp.input.[tp.pos] <> '\n' && tp.input.[tp.pos] <> '\r' do
        tp.pos <- tp.pos + 1
      done;
      loop ()
    end
  in loop ()

(* UTF-8 codepoint decoding: returns (codepoint, byte_length) at position in string *)
let utf8_decode s pos =
  if pos >= String.length s then (0, 0)
  else
    let b0 = Char.code s.[pos] in
    if b0 < 0x80 then (b0, 1)
    else if b0 < 0xC0 then (b0, 1)  (* continuation byte, treat as single *)
    else if b0 < 0xE0 then begin
      if pos + 1 < String.length s then
        let b1 = Char.code s.[pos + 1] in
        ((b0 land 0x1F) lsl 6) lor (b1 land 0x3F), 2
      else (b0, 1)
    end else if b0 < 0xF0 then begin
      if pos + 2 < String.length s then
        let b1 = Char.code s.[pos + 1] in
        let b2 = Char.code s.[pos + 2] in
        ((b0 land 0x0F) lsl 12) lor ((b1 land 0x3F) lsl 6) lor (b2 land 0x3F), 3
      else (b0, 1)
    end else begin
      if pos + 3 < String.length s then
        let b1 = Char.code s.[pos + 1] in
        let b2 = Char.code s.[pos + 2] in
        let b3 = Char.code s.[pos + 3] in
        ((b0 land 0x07) lsl 18) lor ((b1 land 0x3F) lsl 12) lor
        ((b2 land 0x3F) lsl 6) lor (b3 land 0x3F), 4
      else (b0, 1)
    end

(* PN_CHARS_BASE per SPARQL/Turtle grammar:
   [A-Z] | [a-z] | [#x00C0-#x00D6] | [#x00D8-#x00F6] | [#x00F8-#x02FF] |
   [#x0370-#x037D] | [#x037F-#x1FFF] | [#x200C-#x200D] | [#x2070-#x218F] |
   [#x2C00-#x2FEF] | [#x3001-#xD7FF] | [#xF900-#xFDCF] | [#xFDF0-#xFFFD] |
   [#x10000-#xEFFFF] *)
let is_pn_chars_base_codepoint cp =
  (cp >= 0x41 && cp <= 0x5A) ||        (* A-Z *)
  (cp >= 0x61 && cp <= 0x7A) ||        (* a-z *)
  (cp >= 0x00C0 && cp <= 0x00D6) ||
  (cp >= 0x00D8 && cp <= 0x00F6) ||
  (cp >= 0x00F8 && cp <= 0x02FF) ||
  (cp >= 0x0370 && cp <= 0x037D) ||
  (cp >= 0x037F && cp <= 0x1FFF) ||
  (cp >= 0x200C && cp <= 0x200D) ||
  (cp >= 0x2070 && cp <= 0x218F) ||
  (cp >= 0x2C00 && cp <= 0x2FEF) ||
  (cp >= 0x3001 && cp <= 0xD7FF) ||
  (cp >= 0xF900 && cp <= 0xFDCF) ||
  (cp >= 0xFDF0 && cp <= 0xFFFD) ||
  (cp >= 0x10000 && cp <= 0xEFFFF)

(* PN_CHARS_U: PN_CHARS_BASE | '_' *)
let is_pn_chars_u_codepoint cp =
  is_pn_chars_base_codepoint cp || cp = 0x5F (* '_' *)

(* PN_CHARS: PN_CHARS_U | '-' | [0-9] | #x00B7 | [#x0300-#x036F] | [#x203F-#x2040] *)
let is_pn_chars_codepoint cp =
  is_pn_chars_u_codepoint cp || cp = 0x2D (* '-' *) ||
  (cp >= 0x30 && cp <= 0x39) (* 0-9 *) ||
  cp = 0x00B7 ||
  (cp >= 0x0300 && cp <= 0x036F) ||
  (cp >= 0x203F && cp <= 0x2040)

(* Character classification — single-byte wrappers for backward compat *)
let is_pn_chars_base_unicode c =
  let code = Char.code c in
  is_pn_chars_base_codepoint code

let is_pn_chars_u c = is_pn_chars_base_unicode c || c = '_'
let is_pn_chars c =
  let code = Char.code c in
  is_pn_chars_codepoint code

let is_pn_local_esc c =
  String.contains "_~.-!$&'()*+,;=/?#@%" c

(* RFC 3986 Section 5 — Reference Resolution *)

(* Parse a URI into components: (scheme, authority, path, query, fragment) *)
let parse_uri_components uri =
  let len = String.length uri in
  let scheme = ref None in
  let authority = ref None in
  let path = ref "" in
  let query = ref None in
  let fragment = ref None in
  let pos = ref 0 in
  (* Extract scheme *)
  (try
    let colon = String.index uri ':' in
    let valid_scheme = colon > 0 &&
      (let c = uri.[0] in (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')) &&
      (let ok = ref true in
       for i = 1 to colon - 1 do
         let c = uri.[i] in
         if not ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
                 (c >= '0' && c <= '9') || c = '+' || c = '-' || c = '.') then
           ok := false
       done; !ok) in
    if valid_scheme then begin
      scheme := Some (String.sub uri 0 colon);
      pos := colon + 1
    end
  with Not_found -> ());
  (* Extract fragment *)
  (match String.index_opt uri '#' with
   | Some i when i >= !pos ->
     fragment := Some (String.sub uri (i + 1) (len - i - 1));
     let remaining = String.sub uri !pos (i - !pos) in
     pos := 0;
     let uri_nofrag = remaining in
     (* Extract query from remaining *)
     (match String.index_opt uri_nofrag '?' with
      | Some j ->
        query := Some (String.sub uri_nofrag (j + 1) (String.length uri_nofrag - j - 1));
        path := String.sub uri_nofrag 0 j
      | None -> path := uri_nofrag);
     (* Extract authority *)
     if String.length !path >= 2 && !path.[0] = '/' && !path.[1] = '/' then begin
       let rest = String.sub !path 2 (String.length !path - 2) in
       match String.index_opt rest '/' with
       | Some k -> authority := Some (String.sub rest 0 k);
                   path := String.sub rest k (String.length rest - k)
       | None -> authority := Some rest; path := ""
     end
   | _ ->
     let remaining = String.sub uri !pos (len - !pos) in
     (* Extract query *)
     (match String.index_opt remaining '?' with
      | Some j ->
        query := Some (String.sub remaining (j + 1) (String.length remaining - j - 1));
        let before_q = String.sub remaining 0 j in
        (* Extract authority *)
        if String.length before_q >= 2 && before_q.[0] = '/' && before_q.[1] = '/' then begin
          let rest = String.sub before_q 2 (String.length before_q - 2) in
          match String.index_opt rest '/' with
          | Some k -> authority := Some (String.sub rest 0 k);
                      path := String.sub rest k (String.length rest - k)
          | None -> authority := Some rest; path := ""
        end else
          path := before_q
      | None ->
        if String.length remaining >= 2 && remaining.[0] = '/' && remaining.[1] = '/' then begin
          let rest = String.sub remaining 2 (String.length remaining - 2) in
          match String.index_opt rest '/' with
          | Some k -> authority := Some (String.sub rest 0 k);
                      path := String.sub rest k (String.length rest - k)
          | None -> authority := Some rest; path := ""
        end else
          path := remaining));
  (!scheme, !authority, !path, !query, !fragment)

(* Remove dot segments from a path per RFC 3986 Section 5.2.4 *)
let remove_dot_segments path =
  let input = Buffer.create (String.length path) in
  Buffer.add_string input path;
  let output = Buffer.create (String.length path) in
  while Buffer.length input > 0 do
    let s = Buffer.contents input in
    let len = String.length s in
    if len >= 3 && String.sub s 0 3 = "../" then begin
      Buffer.clear input; Buffer.add_string input (String.sub s 3 (len - 3))
    end else if len >= 2 && String.sub s 0 2 = "./" then begin
      Buffer.clear input; Buffer.add_string input (String.sub s 2 (len - 2))
    end else if len >= 3 && String.sub s 0 3 = "/./" then begin
      Buffer.clear input; Buffer.add_string input ("/" ^ String.sub s 3 (len - 3))
    end else if s = "/." then begin
      Buffer.clear input; Buffer.add_string input "/"
    end else if len >= 4 && String.sub s 0 4 = "/../" then begin
      Buffer.clear input; Buffer.add_string input ("/" ^ String.sub s 4 (len - 4));
      (* Remove last segment from output *)
      let out = Buffer.contents output in
      Buffer.clear output;
      (match String.rindex_opt out '/' with
       | Some i -> Buffer.add_string output (String.sub out 0 i)
       | None -> ())
    end else if s = "/.." then begin
      Buffer.clear input; Buffer.add_string input "/";
      let out = Buffer.contents output in
      Buffer.clear output;
      (match String.rindex_opt out '/' with
       | Some i -> Buffer.add_string output (String.sub out 0 i)
       | None -> ())
    end else if s = "." || s = ".." then begin
      Buffer.clear input
    end else begin
      (* Move first path segment to output *)
      let start = if len > 0 && s.[0] = '/' then 1 else 0 in
      let next_slash = try String.index_from s start '/' with Not_found -> len in
      let seg = String.sub s 0 next_slash in
      Buffer.add_string output seg;
      Buffer.clear input;
      if next_slash < len then
        Buffer.add_string input (String.sub s next_slash (len - next_slash))
    end
  done;
  Buffer.contents output

(* Recompose URI from components per RFC 3986 Section 5.3 *)
let recompose_uri scheme authority path query fragment =
  let buf = Buffer.create 128 in
  (match scheme with Some s -> Buffer.add_string buf s; Buffer.add_char buf ':' | None -> ());
  (match authority with Some a -> Buffer.add_string buf "//"; Buffer.add_string buf a | None -> ());
  Buffer.add_string buf path;
  (match query with Some q -> Buffer.add_char buf '?'; Buffer.add_string buf q | None -> ());
  (match fragment with Some f -> Buffer.add_char buf '#'; Buffer.add_string buf f | None -> ());
  Buffer.contents buf

(* Merge paths per RFC 3986 Section 5.2.3 *)
let merge_paths base_authority base_path ref_path =
  if base_authority <> None && base_path = "" then
    "/" ^ ref_path
  else
    match String.rindex_opt base_path '/' with
    | Some i -> String.sub base_path 0 (i + 1) ^ ref_path
    | None -> ref_path

(* Resolve a reference against a base URI per RFC 3986 Section 5.2.2 *)
let resolve_iri tp ref_str =
  let (r_scheme, r_auth, r_path, r_query, r_frag) = parse_uri_components ref_str in
  match r_scheme with
  | Some _ ->
    (* Reference has scheme — it's absolute, use as-is *)
    recompose_uri r_scheme r_auth (remove_dot_segments r_path) r_query r_frag
  | None ->
    match tp.base with
    | None -> ref_str
    | Some base ->
      let (b_scheme, b_auth, b_path, b_query, _b_frag) = parse_uri_components base in
      if r_auth <> None then
        recompose_uri b_scheme r_auth (remove_dot_segments r_path) r_query r_frag
      else if r_path = "" then
        let q = if r_query <> None then r_query else b_query in
        recompose_uri b_scheme b_auth b_path q r_frag
      else begin
        let merged_path =
          if String.length r_path > 0 && r_path.[0] = '/' then r_path
          else merge_paths b_auth b_path r_path in
        recompose_uri b_scheme b_auth (remove_dot_segments merged_path) r_query r_frag
      end

let tp_parse_hex_esc tp n =
  let ps = { input = tp.input; pos = tp.pos } in
  let result = parse_hex_esc ps n in
  tp.pos <- ps.pos;
  result

(* Validate IRI content after escape processing — checks for chars not allowed in IRIs *)
let validate_iri_content iri =
  let len = String.length iri in
  let i = ref 0 in
  while !i < len do
    let c = iri.[!i] in
    let code = Char.code c in
    if c = ' ' || c = '<' || c = '>' || c = '{' || c = '}' || c = '"' ||
       c = '|' || c = '\\' || c = '^' || c = '`' || code < 0x20 then
      raise (Parse_error (Printf.sprintf "Invalid character in IRI: U+%04X" code));
    incr i
  done

let tp_parse_iri_ref tp =
  tp_expect tp '<';
  let buf = Buffer.create 64 in
  let rec loop () =
    match tp_advance tp with
    | None -> raise (Parse_error "Unterminated IRI")
    | Some '>' -> Buffer.contents buf
    | Some '\\' ->
      (match tp_advance tp with
       | Some 'u' -> Buffer.add_string buf (tp_parse_hex_esc tp 4); loop ()
       | Some 'U' -> Buffer.add_string buf (tp_parse_hex_esc tp 8); loop ()
       | _ -> raise (Parse_error "Invalid IRI escape"))
    | Some c when c = ' ' || Char.code c < 0x20 ->
      raise (Parse_error (Printf.sprintf "Invalid char in IRI: U+%04X" (Char.code c)))
    | Some c -> Buffer.add_char buf c; loop ()
  in
  let raw = loop () in
  validate_iri_content raw;
  resolve_iri tp raw

(* Parse prefixed name *)
let tp_parse_pn_local tp =
  let buf = Buffer.create 32 in
  (* First char: PN_CHARS_U | ':' | [0-9] | PLX *)
  (match tp_peek tp with
   | Some '\\' ->
     tp.pos <- tp.pos + 1;
     (match tp_advance tp with
      | Some c when is_pn_local_esc c -> Buffer.add_char buf c
      | _ -> raise (Parse_error "Invalid PN_LOCAL escape"))
   | Some '%' ->
     tp.pos <- tp.pos + 1;
     Buffer.add_char buf '%';
     for _ = 1 to 2 do
       match tp_advance tp with
       | Some c when is_hex c -> Buffer.add_char buf c
       | _ -> raise (Parse_error "Invalid percent encoding")
     done
   | _ ->
     if tp.pos < String.length tp.input then begin
       let (cp, len) = utf8_decode tp.input tp.pos in
       if is_pn_chars_u_codepoint cp || cp = 0x3A (* ':' *) ||
          (cp >= 0x30 && cp <= 0x39) (* 0-9 *) then begin
         Buffer.add_string buf (String.sub tp.input tp.pos len);
         tp.pos <- tp.pos + len
       end
     end);
  (* Rest: PN_CHARS | '.' | ':' | PLX — only if first char was consumed *)
  let has_first = Buffer.length buf > 0 in
  let rec loop () =
    if tp.pos >= String.length tp.input then ()
    else match tp.input.[tp.pos] with
    | '\\' ->
      tp.pos <- tp.pos + 1;
      (match tp_advance tp with
       | Some c when is_pn_local_esc c -> Buffer.add_char buf c
       | _ -> raise (Parse_error "Invalid PN_LOCAL escape"));
      loop ()
    | '%' ->
      tp.pos <- tp.pos + 1;
      Buffer.add_char buf '%';
      for _ = 1 to 2 do
        match tp_advance tp with
        | Some c when is_hex c -> Buffer.add_char buf c
        | _ -> raise (Parse_error "Invalid percent encoding")
      done;
      loop ()
    | '.' ->
      let save = tp.pos in
      tp.pos <- tp.pos + 1;
      (* Dot valid only if followed by PN_CHARS | ':' | '.' | PLX *)
      if tp.pos < String.length tp.input then begin
        let c2 = tp.input.[tp.pos] in
        if c2 = '.' || c2 = ':' || c2 = '%' || c2 = '\\' then begin
          Buffer.add_char buf '.'; loop ()
        end else begin
          let (cp2, _) = utf8_decode tp.input tp.pos in
          if is_pn_chars_codepoint cp2 then begin
            Buffer.add_char buf '.'; loop ()
          end else
            tp.pos <- save  (* put back, dot is statement terminator *)
        end
      end else
        tp.pos <- save
    | _ ->
      let (cp, len) = utf8_decode tp.input tp.pos in
      if is_pn_chars_codepoint cp || cp = 0x3A (* ':' *) then begin
        Buffer.add_string buf (String.sub tp.input tp.pos len);
        tp.pos <- tp.pos + len;
        loop ()
      end
  in (if has_first then loop ());
  Buffer.contents buf

let tp_parse_prefixed_name tp =
  let prefix = Buffer.create 16 in
  (* First char must be PN_CHARS_BASE *)
  let first = ref true in
  let continue = ref true in
  while !continue && tp.pos < String.length tp.input && tp.input.[tp.pos] <> ':' do
    let (cp, len) = utf8_decode tp.input tp.pos in
    if !first then begin
      if is_pn_chars_base_codepoint cp then begin
        Buffer.add_string prefix (String.sub tp.input tp.pos len);
        tp.pos <- tp.pos + len;
        first := false
      end else
        continue := false
    end else begin
      (* Subsequent chars: PN_CHARS | '.' (but not trailing dot) *)
      if is_pn_chars_codepoint cp then begin
        Buffer.add_string prefix (String.sub tp.input tp.pos len);
        tp.pos <- tp.pos + len
      end else if cp = 0x2E (* '.' *) then begin
        (* Look ahead: dot is only valid if followed by PN_CHARS *)
        if tp.pos + 1 < String.length tp.input then begin
          let (next_cp, _) = utf8_decode tp.input (tp.pos + 1) in
          if is_pn_chars_codepoint next_cp then begin
            Buffer.add_char prefix '.';
            tp.pos <- tp.pos + 1
          end else
            continue := false
        end else
          continue := false
      end else
        continue := false
    end
  done;
  tp_expect tp ':';
  let local = tp_parse_pn_local tp in
  let pfx = Buffer.contents prefix in
  match Hashtbl.find_opt tp.prefixes pfx with
  | Some ns -> ns ^ local
  | None -> raise (Parse_error (Printf.sprintf "Undefined prefix: '%s:'" pfx))

let tp_parse_iri tp =
  match tp_peek tp with
  | Some '<' -> tp_parse_iri_ref tp
  | _ -> tp_parse_prefixed_name tp

(* String parsing *)
let tp_parse_string_escape tp =
  let ps = { input = tp.input; pos = tp.pos } in
  let result = parse_string_escape ps in
  tp.pos <- ps.pos;
  result

let tp_parse_long_string tp quote =
  let buf = Buffer.create 128 in
  let rec loop () =
    if tp_at_end tp then raise (Parse_error "Unterminated long string");
    match tp_peek tp with
    | Some c when c = quote &&
                  tp.pos + 2 < String.length tp.input &&
                  tp.input.[tp.pos + 1] = quote &&
                  tp.input.[tp.pos + 2] = quote ->
      tp.pos <- tp.pos + 3;
      Buffer.contents buf
    | Some '\\' ->
      tp.pos <- tp.pos + 1;
      Buffer.add_string buf (tp_parse_string_escape tp);
      loop ()
    | Some c ->
      Buffer.add_char buf c; tp.pos <- tp.pos + 1; loop ()
    | None -> raise (Parse_error "Unterminated long string")
  in loop ()

let tp_parse_string tp =
  (* Check for long strings first *)
  if tp_starts_with tp "\"\"\"" then begin
    tp.pos <- tp.pos + 3; tp_parse_long_string tp '"'
  end else if tp_starts_with tp "'''" then begin
    tp.pos <- tp.pos + 3; tp_parse_long_string tp '\''
  end else begin
    let quote = match tp_advance tp with
      | Some ('"' | '\'' as q) -> q
      | _ -> raise (Parse_error "Expected quote")
    in
    let buf = Buffer.create 64 in
    let rec loop () =
      match tp_advance tp with
      | None -> raise (Parse_error "Unterminated string")
      | Some c when c = quote -> Buffer.contents buf
      | Some '\\' -> Buffer.add_string buf (tp_parse_string_escape tp); loop ()
      | Some c -> Buffer.add_char buf c; loop ()
    in loop ()
  end

(* Blank node label *)
let tp_parse_bnode_label tp =
  tp_expect tp '_';
  tp_expect tp ':';
  let buf = Buffer.create 16 in
  (* First char: PN_CHARS_U | [0-9] *)
  if tp.pos < String.length tp.input then begin
    let (cp, len) = utf8_decode tp.input tp.pos in
    if is_pn_chars_u_codepoint cp || (cp >= 0x30 && cp <= 0x39) then begin
      Buffer.add_string buf (String.sub tp.input tp.pos len);
      tp.pos <- tp.pos + len
    end else
      raise (Parse_error "Expected blank node label")
  end else
    raise (Parse_error "Expected blank node label");
  (* Rest: PN_CHARS | '.' (not trailing) *)
  let rec loop () =
    if tp.pos >= String.length tp.input then ()
    else if tp.input.[tp.pos] = '.' then begin
      let save = tp.pos in
      tp.pos <- tp.pos + 1;
      if tp.pos < String.length tp.input then begin
        let (next_cp, _) = utf8_decode tp.input tp.pos in
        if is_pn_chars_codepoint next_cp || tp.input.[tp.pos] = '.' then begin
          Buffer.add_char buf '.';
          loop ()
        end else
          tp.pos <- save  (* put back *)
      end else
        tp.pos <- save
    end else begin
      let (cp, len) = utf8_decode tp.input tp.pos in
      if is_pn_chars_codepoint cp then begin
        Buffer.add_string buf (String.sub tp.input tp.pos len);
        tp.pos <- tp.pos + len;
        loop ()
      end
    end
  in loop ();
  let label = Buffer.contents buf in
  match Hashtbl.find_opt tp.bnode_labels label with
  | Some id -> id
  | None -> let id = fresh_bnode () in Hashtbl.add tp.bnode_labels label id; id

(* Numeric literals *)
let tp_parse_numeric_literal tp =
  let start = tp.pos in
  (match tp_peek tp with Some ('+' | '-') -> tp.pos <- tp.pos + 1 | _ -> ());
  let has_int = ref false in
  while tp.pos < String.length tp.input &&
        tp.input.[tp.pos] >= '0' && tp.input.[tp.pos] <= '9' do
    has_int := true; tp.pos <- tp.pos + 1
  done;
  let has_dot = ref false in
  if tp.pos < String.length tp.input && tp.input.[tp.pos] = '.' then begin
    let next_ok = tp.pos + 1 < String.length tp.input &&
                  let nc = tp.input.[tp.pos + 1] in
                  (nc >= '0' && nc <= '9') || nc = 'e' || nc = 'E' in
    if next_ok || not !has_int then begin
      has_dot := true; tp.pos <- tp.pos + 1;
      while tp.pos < String.length tp.input &&
            tp.input.[tp.pos] >= '0' && tp.input.[tp.pos] <= '9' do
        tp.pos <- tp.pos + 1
      done
    end
  end;
  let has_exp = ref false in
  if tp.pos < String.length tp.input &&
     (tp.input.[tp.pos] = 'e' || tp.input.[tp.pos] = 'E') then begin
    has_exp := true; tp.pos <- tp.pos + 1;
    (match tp_peek tp with Some ('+' | '-') -> tp.pos <- tp.pos + 1 | _ -> ());
    let had_digit = ref false in
    while tp.pos < String.length tp.input &&
          tp.input.[tp.pos] >= '0' && tp.input.[tp.pos] <= '9' do
      had_digit := true; tp.pos <- tp.pos + 1
    done;
    if not !had_digit then raise (Parse_error "Exponent requires digits")
  end;
  let text = String.sub tp.input start (tp.pos - start) in
  let dt = if !has_exp then xsd_double
           else if !has_dot then xsd_decimal
           else xsd_integer in
  T_Literal { lexical_form = text; datatype = dt; lang_tag = None }

(* Forward declarations via mutual recursion *)
let rec tp_parse_object tp =
  tp_skip_ws tp;
  match tp_peek tp with
  | Some '<' -> T_IRI (tp_parse_iri_ref tp)
  | Some '_' -> T_BNode (tp_parse_bnode_label tp)
  | Some ('"' | '\'') -> tp_parse_literal_value tp
  | Some '(' -> tp_parse_collection tp
  | Some '[' -> T_BNode (tp_parse_blank_node_property_list tp)
  | Some ('+' | '-') -> tp_parse_numeric_literal tp
  | Some '.' when tp.pos + 1 < String.length tp.input &&
                   tp.input.[tp.pos + 1] >= '0' && tp.input.[tp.pos + 1] <= '9' ->
    tp_parse_numeric_literal tp
  | Some c when c >= '0' && c <= '9' -> tp_parse_numeric_literal tp
  | _ when tp_starts_with tp "true" &&
           (tp.pos + 4 >= String.length tp.input || not (is_pn_chars tp.input.[tp.pos + 4])) ->
    tp.pos <- tp.pos + 4;
    T_Literal { lexical_form = "true"; datatype = xsd_boolean; lang_tag = None }
  | _ when tp_starts_with tp "false" &&
           (tp.pos + 5 >= String.length tp.input || not (is_pn_chars tp.input.[tp.pos + 5])) ->
    tp.pos <- tp.pos + 5;
    T_Literal { lexical_form = "false"; datatype = xsd_boolean; lang_tag = None }
  | Some c when c = ':' || is_pn_chars_base_unicode c -> T_IRI (tp_parse_prefixed_name tp)
  | _ ->
    (* Check for multi-byte UTF-8 PN_CHARS_BASE *)
    if tp.pos < String.length tp.input then begin
      let (cp, _) = utf8_decode tp.input tp.pos in
      if is_pn_chars_base_codepoint cp then T_IRI (tp_parse_prefixed_name tp)
      else raise (Parse_error (Printf.sprintf "Expected object at %d" tp.pos))
    end else
      raise (Parse_error (Printf.sprintf "Expected object at %d" tp.pos))

and tp_parse_literal_value tp =
  let lex = tp_parse_string tp in
  match tp_peek tp with
  | Some '@' ->
    tp.pos <- tp.pos + 1;
    (* Language tag must start with a letter per BCP 47 *)
    (match tp_peek tp with
     | Some c when (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') -> ()
     | _ -> raise (Parse_error "Language tag must start with a letter"));
    let lang = Buffer.create 8 in
    while tp.pos < String.length tp.input &&
          let c = tp.input.[tp.pos] in
          (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
          (c >= '0' && c <= '9') || c = '-' do
      Buffer.add_char lang tp.input.[tp.pos];
      tp.pos <- tp.pos + 1
    done;
    T_Literal { lexical_form = lex; datatype = rdf_lang_string;
                lang_tag = Some (Buffer.contents lang) }
  | Some '^' when tp.pos + 1 < String.length tp.input && tp.input.[tp.pos + 1] = '^' ->
    tp.pos <- tp.pos + 2;
    let dt = tp_parse_iri tp in
    T_Literal { lexical_form = lex; datatype = dt; lang_tag = None }
  | _ ->
    T_Literal { lexical_form = lex; datatype = xsd_string; lang_tag = None }

and tp_parse_collection tp =
  tp_expect tp '(';
  tp_skip_ws tp;
  match tp_peek tp with
  | Some ')' -> tp.pos <- tp.pos + 1; T_IRI rdf_nil
  | _ ->
    let items = ref [] in
    let rec loop () =
      tp_skip_ws tp;
      match tp_peek tp with
      | Some ')' -> tp.pos <- tp.pos + 1
      | _ -> items := tp_parse_object tp :: !items; loop ()
    in loop ();
    let items = List.rev !items in
    let nodes = List.map (fun _ -> fresh_bnode ()) items in
    List.iteri (fun i item ->
      let node_id = List.nth nodes i in
      tp.graph := { s = S_BNode node_id; p = rdf_first; o = item } :: !(tp.graph);
      let rest_obj = if i + 1 < List.length nodes
                     then T_BNode (List.nth nodes (i + 1))
                     else T_IRI rdf_nil in
      tp.graph := { s = S_BNode node_id; p = rdf_rest; o = rest_obj } :: !(tp.graph)
    ) items;
    T_BNode (List.hd nodes)

and tp_parse_blank_node_property_list tp =
  tp_expect tp '[';
  let id = fresh_bnode () in
  let subj = S_BNode id in
  tp_skip_ws tp;
  (match tp_peek tp with
   | Some ']' -> ()
   | _ -> tp_parse_predicate_object_list tp subj);
  tp_skip_ws tp;
  tp_expect tp ']';
  id

and tp_parse_predicate_object_list tp subject =
  let rec loop () =
    tp_skip_ws tp;
    (match tp_peek tp with
     | Some ']' | Some '.' | None -> ()
     | _ ->
       let pred = tp_parse_predicate tp in
       tp_parse_object_list tp subject pred;
       tp_skip_ws tp;
       if tp.pos < String.length tp.input && tp.input.[tp.pos] = ';' then begin
         while tp.pos < String.length tp.input && tp.input.[tp.pos] = ';' do
           tp.pos <- tp.pos + 1; tp_skip_ws tp
         done;
         loop ()
       end)
  in loop ()

and tp_parse_object_list tp subject predicate =
  let rec loop () =
    let obj = tp_parse_object tp in
    tp.graph := { s = subject; p = predicate; o = obj } :: !(tp.graph);
    tp_skip_ws tp;
    if tp.pos < String.length tp.input && tp.input.[tp.pos] = ',' then begin
      tp.pos <- tp.pos + 1;
      loop ()
    end
  in loop ()

and tp_parse_predicate tp =
  tp_skip_ws tp;
  if tp_starts_with tp "a" then begin
    let after = if tp.pos + 1 < String.length tp.input
                then Some tp.input.[tp.pos + 1] else None in
    match after with
    | None | Some ' ' | Some '\t' | Some '\n' | Some '\r' ->
      tp.pos <- tp.pos + 1; rdf_type
    | _ -> tp_parse_iri tp
  end else
    tp_parse_iri tp

and tp_parse_subject tp =
  tp_skip_ws tp;
  match tp_peek tp with
  | Some '<' -> S_IRI (tp_parse_iri_ref tp)
  | Some '_' -> S_BNode (tp_parse_bnode_label tp)
  | Some '(' ->
    let t = tp_parse_collection tp in
    (match t with
     | T_IRI i -> S_IRI i
     | T_BNode b -> S_BNode b
     | _ -> raise (Parse_error "Collection head cannot be a literal"))
  | Some '[' -> S_BNode (tp_parse_blank_node_property_list tp)
  | Some c when c = ':' || is_pn_chars_base_unicode c -> S_IRI (tp_parse_prefixed_name tp)
  | _ ->
    if tp.pos < String.length tp.input then begin
      let (cp, _) = utf8_decode tp.input tp.pos in
      if is_pn_chars_base_codepoint cp then S_IRI (tp_parse_prefixed_name tp)
      else raise (Parse_error (Printf.sprintf "Expected subject at %d" tp.pos))
    end else
      raise (Parse_error (Printf.sprintf "Expected subject at %d" tp.pos))

let tp_parse_prefix_directive tp =
  let is_at = tp_starts_with tp "@prefix" in
  if is_at then tp.pos <- tp.pos + 7
  else if tp_starts_with_ci tp "PREFIX" then tp.pos <- tp.pos + 6
  else raise (Parse_error "Expected @prefix or PREFIX");
  tp_skip_ws tp;
  let prefix = Buffer.create 16 in
  (* First char must be PN_CHARS_BASE (or empty prefix) *)
  let first = ref true in
  let continue = ref true in
  while !continue && tp.pos < String.length tp.input && tp.input.[tp.pos] <> ':' do
    let c = tp.input.[tp.pos] in
    if c = ' ' || c = '\t' || c = '\n' || c = '\r' then
      continue := false
    else begin
      let (cp, len) = utf8_decode tp.input tp.pos in
      if !first then begin
        if is_pn_chars_base_codepoint cp then begin
          Buffer.add_string prefix (String.sub tp.input tp.pos len);
          tp.pos <- tp.pos + len;
          first := false
        end else
          continue := false
      end else begin
        if is_pn_chars_codepoint cp then begin
          Buffer.add_string prefix (String.sub tp.input tp.pos len);
          tp.pos <- tp.pos + len
        end else if cp = 0x2E (* '.' *) then begin
          (* Dot allowed in prefix if followed by PN_CHARS *)
          if tp.pos + 1 < String.length tp.input && tp.input.[tp.pos + 1] <> ':' then begin
            let (next_cp, _) = utf8_decode tp.input (tp.pos + 1) in
            if is_pn_chars_codepoint next_cp then begin
              Buffer.add_char prefix '.';
              tp.pos <- tp.pos + 1
            end else
              continue := false
          end else
            continue := false
        end else
          continue := false
      end
    end
  done;
  tp_expect tp ':';
  tp_skip_ws tp;
  let iri = tp_parse_iri_ref tp in
  tp_skip_ws tp;
  (match tp_peek tp with Some '.' -> tp.pos <- tp.pos + 1 | _ -> ());
  Hashtbl.replace tp.prefixes (Buffer.contents prefix) iri

let tp_parse_base_directive tp =
  let is_at = tp_starts_with tp "@base" in
  if is_at then tp.pos <- tp.pos + 5
  else if tp_starts_with_ci tp "BASE" then tp.pos <- tp.pos + 4
  else raise (Parse_error "Expected @base or BASE");
  tp_skip_ws tp;
  let iri = tp_parse_iri_ref tp in
  tp_skip_ws tp;
  if is_at then (match tp_peek tp with Some '.' -> tp.pos <- tp.pos + 1 | _ -> ());
  tp.base <- Some iri

let parse_turtle input base_iri =
  let tp = make_turtle_parser input base_iri in
  let rec loop () =
    tp_skip_ws tp;
    if not (tp_at_end tp) then begin
      if tp_starts_with tp "@prefix" then begin tp_parse_prefix_directive tp; loop () end
      else if tp_starts_with tp "@base" then begin tp_parse_base_directive tp; loop () end
      else if tp_starts_with_ci tp "PREFIX" &&
              tp.pos + 6 < String.length tp.input &&
              let c = tp.input.[tp.pos + 6] in c = ' ' || c = '\t' || c = '\n' || c = '\r'
      then begin tp_parse_prefix_directive tp; loop () end
      else if tp_starts_with_ci tp "BASE" &&
              tp.pos + 4 < String.length tp.input &&
              let c = tp.input.[tp.pos + 4] in c = ' ' || c = '\t' || c = '\n' || c = '\r'
      then begin tp_parse_base_directive tp; loop () end
      else begin
        (* Determine if subject is a blankNodePropertyList (which allows empty predicateObjectList) *)
        let is_bnpl = (match tp_peek tp with Some '[' -> true | _ -> false) in
        let subject = tp_parse_subject tp in
        tp_skip_ws tp;
        if is_bnpl then begin
          (* blankNodePropertyList predicateObjectList? '.' *)
          (match tp_peek tp with
           | Some '.' -> tp.pos <- tp.pos + 1  (* empty predicateObjectList *)
           | _ ->
             tp_parse_predicate_object_list tp subject;
             tp_skip_ws tp;
             (match tp_peek tp with
              | Some '.' -> tp.pos <- tp.pos + 1
              | Some c ->
                raise (Parse_error (Printf.sprintf "Expected '.' at %d, got '%c'" tp.pos c))
              | None ->
                raise (Parse_error "Expected '.' at end of input")))
        end else begin
          (* Non-BNPL subject requires at least one predicate-object pair *)
          (match tp_peek tp with
           | Some '.' | None ->
             raise (Parse_error (Printf.sprintf "Expected predicate at %d" tp.pos))
           | _ -> ());
          tp_parse_predicate_object_list tp subject;
          tp_skip_ws tp;
          (* After triple, must have '.' *)
          (match tp_peek tp with
           | Some '.' -> tp.pos <- tp.pos + 1
           | Some c ->
             raise (Parse_error (Printf.sprintf "Expected '.' at %d, got '%c'" tp.pos c))
           | None ->
             raise (Parse_error "Expected '.' at end of input"))
        end;
        loop ()
      end
    end
  in
  loop ();
  List.rev !(tp.graph)
