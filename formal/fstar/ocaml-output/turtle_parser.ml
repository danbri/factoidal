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

(* Character classification *)
let is_pn_chars_base_unicode c =
  let code = Char.code c in
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
  (code >= 0xC0 && code <= 0xD6) || (code >= 0xD8 && code <= 0xF6) ||
  (code >= 0xF8)  (* simplified: accept high bytes as part of UTF-8 *)

let is_pn_chars_u c = is_pn_chars_base_unicode c || c = '_'
let is_pn_chars c =
  is_pn_chars_u c || c = '-' || (c >= '0' && c <= '9') ||
  c = '\xB7'  (* middle dot, simplified *)

let is_pn_local_esc c =
  String.contains "_~.-!$&'()*+,;=/?#@%" c

(* IRI resolution *)
let resolve_iri tp iri_str =
  if String.contains iri_str ':' && (String.length iri_str = 0 || iri_str.[0] <> '#') then
    iri_str
  else match tp.base with
  | None -> iri_str
  | Some base ->
    if iri_str = "" then base
    else if iri_str.[0] = '#' then base ^ iri_str
    else begin
      (* Find last / in base *)
      match String.rindex_opt base '/' with
      | Some idx -> String.sub base 0 idx ^ "/" ^ iri_str
      | None -> base ^ iri_str
    end

let tp_parse_hex_esc tp n =
  let ps = { input = tp.input; pos = tp.pos } in
  let result = parse_hex_esc ps n in
  tp.pos <- ps.pos;
  result

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
  resolve_iri tp raw

(* Parse prefixed name *)
let tp_parse_pn_local tp =
  let buf = Buffer.create 32 in
  (* First char *)
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
   | Some c when is_pn_chars_u c || c = ':' || (c >= '0' && c <= '9') ->
     Buffer.add_char buf c; tp.pos <- tp.pos + 1
   | _ -> ());
  (* Rest *)
  let rec loop () =
    match tp_peek tp with
    | Some '\\' ->
      tp.pos <- tp.pos + 1;
      (match tp_advance tp with
       | Some c when is_pn_local_esc c -> Buffer.add_char buf c
       | _ -> raise (Parse_error "Invalid PN_LOCAL escape"));
      loop ()
    | Some '%' ->
      tp.pos <- tp.pos + 1;
      Buffer.add_char buf '%';
      for _ = 1 to 2 do
        match tp_advance tp with
        | Some c when is_hex c -> Buffer.add_char buf c
        | _ -> raise (Parse_error "Invalid percent encoding")
      done;
      loop ()
    | Some '.' ->
      let save = tp.pos in
      tp.pos <- tp.pos + 1;
      (match tp_peek tp with
       | Some c when is_pn_chars c || c = ':' || c = '.' || c = '%' || c = '\\' ->
         Buffer.add_char buf '.'; loop ()
       | _ -> tp.pos <- save)  (* put back, dot is statement terminator *)
    | Some c when is_pn_chars c || c = ':' ->
      Buffer.add_char buf c; tp.pos <- tp.pos + 1; loop ()
    | _ -> ()
  in loop ();
  Buffer.contents buf

let tp_parse_prefixed_name tp =
  let prefix = Buffer.create 16 in
  while tp.pos < String.length tp.input && tp.input.[tp.pos] <> ':' &&
        let c = tp.input.[tp.pos] in
        is_pn_chars_base_unicode c || c = '_' || c = '-' || c = '.' ||
        (c >= '0' && c <= '9') do
    Buffer.add_char prefix tp.input.[tp.pos];
    tp.pos <- tp.pos + 1
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
  (match tp_peek tp with
   | Some c when is_pn_chars_u c || (c >= '0' && c <= '9') ->
     Buffer.add_char buf c; tp.pos <- tp.pos + 1
   | _ -> raise (Parse_error "Expected blank node label"));
  let rec loop () =
    match tp_peek tp with
    | Some '.' ->
      if tp.pos + 1 < String.length tp.input then begin
        let next = tp.input.[tp.pos + 1] in
        if is_pn_chars next || next = '.' then begin
          Buffer.add_char buf '.'; tp.pos <- tp.pos + 1; loop ()
        end
      end
    | Some c when is_pn_chars c ->
      Buffer.add_char buf c; tp.pos <- tp.pos + 1; loop ()
    | _ -> ()
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
                  tp.input.[tp.pos + 1] >= '0' && tp.input.[tp.pos + 1] <= '9' in
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
  | _ -> raise (Parse_error (Printf.sprintf "Expected object at %d" tp.pos))

and tp_parse_literal_value tp =
  let lex = tp_parse_string tp in
  match tp_peek tp with
  | Some '@' ->
    tp.pos <- tp.pos + 1;
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
  | _ -> raise (Parse_error (Printf.sprintf "Expected subject at %d" tp.pos))

let tp_parse_prefix_directive tp =
  let is_at = tp_starts_with tp "@prefix" in
  if is_at then tp.pos <- tp.pos + 7
  else if tp_starts_with tp "PREFIX" || tp_starts_with tp "prefix" then tp.pos <- tp.pos + 6
  else raise (Parse_error "Expected @prefix or PREFIX");
  tp_skip_ws tp;
  let prefix = Buffer.create 16 in
  while tp.pos < String.length tp.input && tp.input.[tp.pos] <> ':' &&
        not (let c = tp.input.[tp.pos] in c = ' ' || c = '\t' || c = '\n' || c = '\r') do
    Buffer.add_char prefix tp.input.[tp.pos];
    tp.pos <- tp.pos + 1
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
  else if tp_starts_with tp "BASE" || tp_starts_with tp "base" then tp.pos <- tp.pos + 4
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
      else if (tp_starts_with tp "PREFIX" || tp_starts_with tp "prefix") &&
              tp.pos + 6 < String.length tp.input &&
              let c = tp.input.[tp.pos + 6] in c = ' ' || c = '\t' || c = '\n' || c = '\r'
      then begin tp_parse_prefix_directive tp; loop () end
      else if (tp_starts_with tp "BASE" || tp_starts_with tp "base") &&
              tp.pos + 4 < String.length tp.input &&
              let c = tp.input.[tp.pos + 4] in c = ' ' || c = '\t' || c = '\n' || c = '\r'
      then begin tp_parse_base_directive tp; loop () end
      else begin
        let subject = tp_parse_subject tp in
        tp_skip_ws tp;
        (match tp_peek tp with
         | Some '.' -> tp.pos <- tp.pos + 1  (* empty predicate-object list *)
         | _ ->
           tp_parse_predicate_object_list tp subject;
           tp_skip_ws tp;
           (match tp_peek tp with
            | Some '.' -> tp.pos <- tp.pos + 1
            | _ -> ()));
        loop ()
      end
    end
  in
  loop ();
  List.rev !(tp.graph)
