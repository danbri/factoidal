(* RDF/XML parser — UNVERIFIED TEST INFRASTRUCTURE.
   Not extracted from F*. Hand-written OCaml for loading W3C test data in .rdf format.
   Handles the basic RDF/XML patterns found in W3C SPARQL 1.1 test files:
     - rdf:Description with rdf:about
     - Property elements with rdf:resource, rdf:datatype, xml:lang
     - Plain literal content
   Produces RDF_Graph_Executable types directly. *)

open RDF_Graph_Executable

let bnode_counter = ref 0

let fresh_bnode () =
  let id = Printf.sprintf "_:rdfxml_b%d" !bnode_counter in
  incr bnode_counter; id

type xml_attr = { attr_ns : string; attr_local : string; attr_value : string }

type xml_event =
  | Start_element of string * string * xml_attr list  (* ns, local, attrs *)
  | End_element of string * string
  | Text of string

(* Minimal XML pull parser *)
type xml_parser = {
  input : string;
  mutable pos : int;
}

let xp_make s = { input = s; pos = 0 }

let xp_at_end xp = xp.pos >= String.length xp.input

let xp_peek xp =
  if xp.pos < String.length xp.input then Some xp.input.[xp.pos] else None

let xp_advance xp =
  if xp.pos < String.length xp.input then xp.pos <- xp.pos + 1

let xp_skip_ws xp =
  while xp.pos < String.length xp.input &&
        (let c = xp.input.[xp.pos] in c = ' ' || c = '\t' || c = '\n' || c = '\r') do
    xp.pos <- xp.pos + 1
  done

let xp_read_until xp stop_char =
  let start = xp.pos in
  while xp.pos < String.length xp.input && xp.input.[xp.pos] <> stop_char do
    xp.pos <- xp.pos + 1
  done;
  String.sub xp.input start (xp.pos - start)

let xp_read_name xp =
  let start = xp.pos in
  while xp.pos < String.length xp.input &&
        (let c = xp.input.[xp.pos] in
         (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
         (c >= '0' && c <= '9') || c = '_' || c = '-' || c = '.' || c = ':') do
    xp.pos <- xp.pos + 1
  done;
  String.sub xp.input start (xp.pos - start)

let xp_expect xp c =
  if xp.pos < String.length xp.input && xp.input.[xp.pos] = c then
    xp.pos <- xp.pos + 1
  else
    failwith (Printf.sprintf "RDF/XML parse error: expected '%c' at pos %d" c xp.pos)

let xp_read_attr_value xp =
  let quote = xp.input.[xp.pos] in
  if quote <> '"' && quote <> '\'' then
    failwith "RDF/XML parse error: expected quote for attribute value";
  xp.pos <- xp.pos + 1;
  let buf = Buffer.create 64 in
  while xp.pos < String.length xp.input && xp.input.[xp.pos] <> quote do
    if xp.input.[xp.pos] = '&' then begin
      xp.pos <- xp.pos + 1;
      let entity = xp_read_until xp ';' in
      xp.pos <- xp.pos + 1; (* skip ';' *)
      (match entity with
       | "amp" -> Buffer.add_char buf '&'
       | "lt" -> Buffer.add_char buf '<'
       | "gt" -> Buffer.add_char buf '>'
       | "quot" -> Buffer.add_char buf '"'
       | "apos" -> Buffer.add_char buf '\''
       | _ -> Buffer.add_char buf '&'; Buffer.add_string buf entity; Buffer.add_char buf ';')
    end else begin
      Buffer.add_char buf xp.input.[xp.pos];
      xp.pos <- xp.pos + 1
    end
  done;
  xp.pos <- xp.pos + 1; (* skip closing quote *)
  Buffer.contents buf

let xp_skip_comment xp =
  (* skip <!-- ... --> *)
  while xp.pos + 2 < String.length xp.input &&
        not (xp.input.[xp.pos] = '-' && xp.input.[xp.pos+1] = '-' && xp.input.[xp.pos+2] = '>') do
    xp.pos <- xp.pos + 1
  done;
  if xp.pos + 2 < String.length xp.input then xp.pos <- xp.pos + 3

let xp_skip_pi xp =
  (* skip <?...?> *)
  while xp.pos + 1 < String.length xp.input &&
        not (xp.input.[xp.pos] = '?' && xp.input.[xp.pos+1] = '>') do
    xp.pos <- xp.pos + 1
  done;
  if xp.pos + 1 < String.length xp.input then xp.pos <- xp.pos + 2

(* Namespace resolution *)
type ns_context = {
  mutable prefixes : (string * string) list;
  base_iri : string option;
}

let ns_make base = { prefixes = []; base_iri = base }

let ns_resolve ctx prefix =
  try List.assoc prefix ctx.prefixes
  with Not_found -> prefix ^ ":"

let split_qname name =
  match String.index_opt name ':' with
  | Some i -> (String.sub name 0 i, String.sub name (i+1) (String.length name - i - 1))
  | None -> ("", name)

let resolve_iri ctx prefix local =
  let ns = ns_resolve ctx prefix in
  ns ^ local

(* Parse a single XML element tag (after '<') *)
let xp_parse_tag xp ns_ctx =
  let is_end = match xp_peek xp with Some '/' -> xp_advance xp; true | _ -> false in
  let name = xp_read_name xp in
  if is_end then begin
    xp_skip_ws xp;
    xp_expect xp '>';
    let (prefix, local) = split_qname name in
    let ns = ns_resolve ns_ctx prefix in
    [End_element (ns, local)]
  end else begin
    (* Parse attributes *)
    let attrs = ref [] in
    let self_closing = ref false in
    let rec parse_attrs () =
      xp_skip_ws xp;
      match xp_peek xp with
      | Some '/' -> xp_advance xp; xp_expect xp '>'; self_closing := true
      | Some '>' -> xp_advance xp
      | _ ->
        let attr_name = xp_read_name xp in
        xp_skip_ws xp;
        xp_expect xp '=';
        xp_skip_ws xp;
        let attr_val = xp_read_attr_value xp in
        let (ap, al) = split_qname attr_name in
        (* Register namespace declarations *)
        if attr_name = "xmlns" then
          ns_ctx.prefixes <- ("", attr_val) :: ns_ctx.prefixes
        else if ap = "xmlns" then
          ns_ctx.prefixes <- (al, attr_val) :: ns_ctx.prefixes
        else
          attrs := { attr_ns = ap; attr_local = al; attr_value = attr_val } :: !attrs;
        parse_attrs ()
    in
    parse_attrs ();
    let (prefix, local) = split_qname name in
    let ns = ns_resolve ns_ctx prefix in
    let resolved_attrs = List.rev_map (fun a ->
      let ans = if a.attr_ns = "" then "" else ns_resolve ns_ctx a.attr_ns in
      { attr_ns = ans; attr_local = a.attr_local; attr_value = a.attr_value }
    ) !attrs in
    if !self_closing then
      [Start_element (ns, local, resolved_attrs); End_element (ns, local)]
    else
      [Start_element (ns, local, resolved_attrs)]
  end

(* Pull next events from the XML stream *)
let xp_next xp ns_ctx =
  xp_skip_ws xp;
  if xp_at_end xp then []
  else match xp_peek xp with
  | Some '<' ->
    xp_advance xp;
    (match xp_peek xp with
     | Some '!' ->
       xp_advance xp;
       if xp.pos + 1 < String.length xp.input && xp.input.[xp.pos] = '-' && xp.input.[xp.pos+1] = '-' then begin
         xp.pos <- xp.pos + 2;
         xp_skip_comment xp; []
       end else begin
         (* Skip DOCTYPE etc *)
         let _ = xp_read_until xp '>' in xp_advance xp; []
       end
     | Some '?' -> xp_advance xp; xp_skip_pi xp; []
     | _ -> xp_parse_tag xp ns_ctx)
  | _ ->
    (* Text content *)
    let buf = Buffer.create 64 in
    while xp.pos < String.length xp.input && xp.input.[xp.pos] <> '<' do
      if xp.input.[xp.pos] = '&' then begin
        xp.pos <- xp.pos + 1;
        let entity = xp_read_until xp ';' in
        xp.pos <- xp.pos + 1;
        (match entity with
         | "amp" -> Buffer.add_char buf '&'
         | "lt" -> Buffer.add_char buf '<'
         | "gt" -> Buffer.add_char buf '>'
         | "quot" -> Buffer.add_char buf '"'
         | "apos" -> Buffer.add_char buf '\''
         | _ -> Buffer.add_char buf '&'; Buffer.add_string buf entity; Buffer.add_char buf ';')
      end else begin
        Buffer.add_char buf xp.input.[xp.pos];
        xp.pos <- xp.pos + 1
      end
    done;
    [Text (Buffer.contents buf)]

let rdf_ns = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"

let find_attr attrs ns local =
  try Some (List.find (fun a -> a.attr_ns = ns && a.attr_local = local) attrs).attr_value
  with Not_found ->
  (* Also try with empty namespace for unresolved attrs like rdf:about *)
  try Some (List.find (fun a -> a.attr_local = local &&
    (a.attr_ns = ns || a.attr_ns = "")) attrs).attr_value
  with Not_found -> None

let find_rdf_attr attrs local =
  find_attr attrs rdf_ns local

let find_xml_attr attrs local =
  find_attr attrs "http://www.w3.org/XML/1998/namespace" local

let make_subject iri = S_IRI iri

let make_iri_term iri = T_IRI iri

let make_literal lex dt lang =
  T_Literal {
    lexical_form = lex;
    datatype = dt;
    lang_tag = lang;
  }

let xsd_string_iri = "http://www.w3.org/2001/XMLSchema#string"

(* Parse RDF/XML and return a list of triples *)
let parse_rdf_xml content base_iri =
  let xp = xp_make content in
  let ns_ctx = ns_make base_iri in
  let triples = ref [] in
  let add_triple s p o =
    triples := { s; p; o } :: !triples
  in
  (* Collect all events *)
  let events = ref [] in
  while not (xp_at_end xp) do
    let evts = xp_next xp ns_ctx in
    events := !events @ evts
  done;
  (* Now process events as a simple state machine *)
  let evts = ref !events in
  let next () = match !evts with [] -> None | e :: rest -> evts := rest; Some e in
  let rec skip_until_start () =
    match next () with
    | None -> ()
    | Some (Start_element (ns, local, attrs)) when ns = rdf_ns && local = "RDF" ->
      parse_rdf_content ()
    | Some _ -> skip_until_start ()
  and parse_rdf_content () =
    (* Inside rdf:RDF, look for Description elements *)
    let rec loop () =
      match next () with
      | None -> ()
      | Some (End_element (ns, local)) when ns = rdf_ns && local = "RDF" -> ()
      | Some (Start_element (ns, local, attrs)) ->
        parse_description ns local attrs;
        loop ()
      | Some _ -> loop ()
    in loop ()
  and parse_description ns local attrs =
    (* Determine the subject *)
    let subj = match find_rdf_attr attrs "about" with
      | Some iri -> S_IRI iri
      | None -> match find_rdf_attr attrs "ID" with
        | Some id ->
          let base = match ns_ctx.base_iri with Some b -> b | None -> "" in
          S_IRI (base ^ "#" ^ id)
        | None ->
          match find_rdf_attr attrs "nodeID" with
          | Some nid -> S_BNode ("_:" ^ nid)
          | None -> S_BNode (fresh_bnode ())
    in
    (* If the element is not rdf:Description, add rdf:type triple *)
    if not (ns = rdf_ns && local = "Description") then begin
      let type_iri = ns ^ local in
      add_triple subj (rdf_ns ^ "type") (T_IRI type_iri)
    end;
    (* Parse property elements *)
    parse_properties subj
  and parse_properties subj =
    match next () with
    | None -> ()
    | Some (End_element (_, _)) -> () (* end of description *)
    | Some (Start_element (ns, local, attrs)) ->
      let pred = ns ^ local in
      (* Check for rdf:resource (object is IRI) *)
      (match find_rdf_attr attrs "resource" with
       | Some iri ->
         add_triple subj pred (T_IRI iri);
         (* Consume the end element *)
         let rec skip_end () = match next () with
           | Some (End_element _) -> ()
           | Some _ -> skip_end ()
           | None -> ()
         in skip_end ()
       | None ->
         match find_rdf_attr attrs "nodeID" with
         | Some nid ->
           add_triple subj pred (T_BNode ("_:" ^ nid));
           let rec skip_end () = match next () with
             | Some (End_element _) -> ()
             | Some _ -> skip_end ()
             | None -> ()
           in skip_end ()
         | None ->
           (* Check for rdf:parseType *)
           let parse_type = find_rdf_attr attrs "parseType" in
           match parse_type with
           | Some "Resource" ->
             (* Nested blank node *)
             let bnode = fresh_bnode () in
             let bsubj = S_BNode bnode in
             add_triple subj pred (T_BNode bnode);
             parse_properties bsubj
           | _ ->
             (* Collect text content or nested Description *)
             let datatype = find_rdf_attr attrs "datatype" in
             let lang = find_xml_attr attrs "lang" in
             let buf = Buffer.create 64 in
             let has_nested = ref false in
             let rec collect () =
               match next () with
               | None -> ()
               | Some (End_element _) -> ()
               | Some (Text t) -> Buffer.add_string buf t; collect ()
               | Some (Start_element (ns2, local2, attrs2)) ->
                 (* Nested resource element *)
                 has_nested := true;
                 let bnode = fresh_bnode () in
                 let obj_subj = S_BNode bnode in
                 add_triple subj pred (T_BNode bnode);
                 parse_description ns2 local2 attrs2;
                 (* There might be a closing tag for the property still *)
                 let rec drain () = match next () with
                   | Some (End_element _) -> ()
                   | Some _ -> drain ()
                   | None -> ()
                 in drain ()
             in
             collect ();
             if not !has_nested then begin
               let text = Buffer.contents buf in
               let dt = match datatype with
                 | Some d -> d
                 | None -> match lang with
                   | Some _ -> "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString"
                   | None -> xsd_string_iri
               in
               let lang_opt = match lang with
                 | Some l -> FStar_Pervasives_Native.Some l
                 | None -> FStar_Pervasives_Native.None
               in
               add_triple subj pred (make_literal text dt lang_opt)
             end);
      parse_properties subj
    | Some (Text _) -> parse_properties subj (* skip whitespace text *)
  in
  skip_until_start ();
  List.rev !triples
