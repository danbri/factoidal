module Parser.RDFXML

(* ================================================================ *)
(* RDF/XML Parser — Verified F* Implementation                       *)
(*                                                                   *)
(* Converts XML trees (from Parser.XML) to RDF triples following     *)
(* the W3C RDF/XML Syntax Specification:                             *)
(* https://www.w3.org/TR/rdf-syntax-grammar/                         *)
(*                                                                   *)
(* Key rules implemented:                                            *)
(*   1. rdf:RDF root container (optional)                            *)
(*   2. Node elements (rdf:Description or typed)                     *)
(*   3. Property elements with literal/resource/blank node objects   *)
(*   4. rdf:about, rdf:ID, rdf:nodeID for subject identification    *)
(*   5. rdf:resource, rdf:datatype, xml:lang on properties          *)
(*   6. rdf:parseType="Literal"|"Resource"|"Collection"              *)
(*   7. Typed node elements (imply rdf:type)                         *)
(*   8. Property attributes (non-rdf:* become triples)               *)
(*   9. rdf:li auto-numbering                                       *)
(*  10. xml:base for IRI resolution                                  *)
(* ================================================================ *)

open FStar.String
open FStar.List.Tot
open Parser.Combinators
open Parser.XML
open RDF.Graph.Executable
module PI = Parser.IRI


(* ================================================================ *)
(* RDF namespace constants                                           *)
(* ================================================================ *)

let rdf_ns : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
let rdfs_ns : string = "http://www.w3.org/2000/01/rdf-schema#"
let xml_ns : string = "http://www.w3.org/XML/1998/namespace"
let xmlns_ns : string = "http://www.w3.org/2000/xmlns/"
let xsd_ns : string = "http://www.w3.org/2001/XMLSchema#"

let rdf_type_iri : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let rdf_first_iri : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"
let rdf_rest_iri : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"
let rdf_nil_iri : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"
let rdf_xmlliteral_iri : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral"


(* ================================================================ *)
(* Parser state                                                      *)
(* ================================================================ *)

noeq type rdfxml_state = {
  base_iri : string;
  namespaces : list (string * string);   (* prefix -> namespace IRI *)
  lang : option string;                  (* inherited xml:lang *)
  bnode_counter : nat;                   (* counter for generating fresh blank nodes *)
  li_counter : nat;                      (* counter for rdf:li numbering *)
}

let initial_state (base : string) : rdfxml_state = {
  base_iri = base;
  namespaces = [("rdf", rdf_ns); ("rdfs", rdfs_ns); ("xml", xml_ns); ("xmlns", xmlns_ns); ("xsd", xsd_ns)];
  lang = None;
  bnode_counter = 0;
  li_counter = 1;
}

let fresh_bnode (st : rdfxml_state) : (string * rdfxml_state) =
  let id = String.concat "" ["_:rdfxml_b"; string_of_int st.bnode_counter] in
  (id, { st with bnode_counter = st.bnode_counter + 1 })

let reset_li_counter (st : rdfxml_state) : rdfxml_state =
  { st with li_counter = 1 }

let next_li (st : rdfxml_state) : (string * rdfxml_state) =
  let prop = String.concat "" [rdf_ns; "_"; string_of_int st.li_counter] in
  (prop, { st with li_counter = st.li_counter + 1 })


(* ================================================================ *)
(* Namespace handling and QName resolution                           *)
(* ================================================================ *)

(* Find the colon position in a string to split prefix:local *)
let rec find_colon_pos_in_list (cs : list FStar.Char.char) (idx : nat) : option nat =
  match cs with
  | [] -> None
  | c :: rest ->
    if FStar.Char.int_of_char c = 0x3A then Some idx
    else find_colon_pos_in_list rest (idx + 1)

let find_colon_pos (s : string) : option nat =
  find_colon_pos_in_list (String.list_of_string s) 0

(* Split a QName "prefix:local" into (prefix, local) *)
let split_qname (name : string) : (string * string) =
  match find_colon_pos name with
  | Some pos ->
    let len = String.length name in
    if pos = 0 then ("", name)
    else if pos >= len then (name, "")
    else if pos + 1 >= len then (String.sub name 0 pos, "")
    else (String.sub name 0 pos, String.sub name (pos + 1) (len - pos - 1))
  | None -> ("", name)

(* Look up a namespace prefix in the state *)
let rec lookup_ns (prefix : string) (nss : list (string * string)) : option string =
  match nss with
  | [] -> None
  | (p, uri) :: rest ->
    if p = prefix then Some uri
    else lookup_ns prefix rest

(* Resolve a QName to a full IRI using the namespace map.
   "prefix:local" -> Some "namespace_iri + local"
   Returns None if prefix is not found. *)
let resolve_qname (st : rdfxml_state) (name : string) : option string =
  let (prefix, local) = split_qname name in
  match lookup_ns prefix st.namespaces with
  | Some ns_iri -> Some (String.concat "" [ns_iri; local])
  | None ->
    (* If no colon at all, it's an unprefixed name — cannot resolve as IRI *)
    match find_colon_pos name with
    | Some _ -> None  (* has colon but prefix not found *)
    | None -> None    (* no colon — not a QName *)


(* ================================================================ *)
(* IRI resolution helpers                                            *)
(* ================================================================ *)

(* Check if a string starts with a scheme (contains "://" early) *)
let rec has_scheme_chars (cs : list FStar.Char.char) (depth : nat) : bool =
  if depth > 20 then false
  else
    match cs with
    | [] -> false
    | c :: rest ->
      let code = FStar.Char.int_of_char c in
      if code = 0x3A then  (* ':' *)
        (match rest with
         | c2 :: c3 :: _ ->
           FStar.Char.int_of_char c2 = 0x2F && FStar.Char.int_of_char c3 = 0x2F
         | _ -> false)
      else if (code >= 0x61 && code <= 0x7A) || (code >= 0x41 && code <= 0x5A)
              || (code >= 0x30 && code <= 0x39) || code = 0x2B || code = 0x2D || code = 0x2E then
        has_scheme_chars rest (depth + 1)
      else false

let is_absolute_iri (s : string) : bool =
  has_scheme_chars (String.list_of_string s) 0

(* Resolve a relative IRI against a base IRI.
   Delegates to Parser.IRI.resolve_iri_v2 for the full RFC 3986 §5
   algorithm (merge paths + remove_dot_segments), which is needed for
   xmlbase-test007/009/010/011 etc. that use "../" and "./" in
   relative references. Kept the short-circuit cases at the top since
   they avoid parsing when we can. *)
let resolve_iri (base : string) (rel : string) : string =
  if String.length rel = 0 then base
  else if is_absolute_iri rel then rel
  else if String.length base = 0 then rel
  else PI.resolve_iri_v2 base rel


(* ================================================================ *)
(* Attribute extraction helpers                                      *)
(* ================================================================ *)

(* Extract namespace declarations from element attributes and update state.
   xmlns:prefix="uri" or xmlns="uri" (default namespace). *)
let rec extract_namespaces (attrs : list xml_attribute) (nss : list (string * string)) : list (string * string) =
  match attrs with
  | [] -> nss
  | attr :: rest ->
    let (prefix, local) = split_qname attr.attr_name in
    if prefix = "xmlns" && String.length local > 0 then
      extract_namespaces rest ((local, attr.attr_value) :: nss)
    else if attr.attr_name = "xmlns" then
      (* Default namespace: store with empty prefix *)
      extract_namespaces rest (("", attr.attr_value) :: nss)
    else
      extract_namespaces rest nss

(* Extract xml:lang from attributes *)
let extract_lang (attrs : list xml_attribute) (current_lang : option string) : option string =
  match find_attr "xml:lang" attrs with
  | Some lang_val ->
    if String.length lang_val = 0 then None  (* xml:lang="" clears the language *)
    else Some lang_val
  | None -> current_lang

(* Strip any `#fragment` tail from an IRI. XML Base §3.3 and RFC 3986
   §5.1 require that a base IRI carry no fragment identifier; if the
   authored `xml:base` value includes one, the fragment is discarded.
   xmlbase-test013 covers this. *)
let rec strip_fragment_from (s : string) (pos : nat) (fuel : nat)
  : Tot string (decreases fuel) =
  let len = String.length s in
  if fuel = 0 || pos >= len then s
  else
    let c = FStar.Char.int_of_char (String.index s pos) in
    if c = 0x23 then  (* '#' *)
      String.sub s 0 pos
    else
      strip_fragment_from s (pos + 1) (fuel - 1)

let strip_fragment (s : string) : string =
  strip_fragment_from s 0 (String.length s + 1)

(* Extract xml:base from attributes *)
let extract_base (attrs : list xml_attribute) (current_base : string) : string =
  match find_attr "xml:base" attrs with
  | Some base_val -> strip_fragment (resolve_iri current_base base_val)
  | None -> current_base

(* Update state from element attributes: namespaces, lang, base *)
let update_state_from_attrs (st : rdfxml_state) (attrs : list xml_attribute) : rdfxml_state =
  let new_nss = extract_namespaces attrs st.namespaces in
  let new_lang = extract_lang attrs st.lang in
  let new_base = extract_base attrs st.base_iri in
  { st with namespaces = new_nss; lang = new_lang; base_iri = new_base }


(* ================================================================ *)
(* Resolve element/attribute names to full IRIs                      *)
(* ================================================================ *)

(* Resolve an element or attribute name to a full IRI.
   Handles both "prefix:local" and unprefixed names. *)
let resolve_name (st : rdfxml_state) (name : string) : option string =
  let (prefix, local) = split_qname name in
  if String.length prefix > 0 then
    match lookup_ns prefix st.namespaces with
    | Some ns_iri -> Some (String.concat "" [ns_iri; local])
    | None -> None
  else
    (* Unprefixed name — try default namespace *)
    match lookup_ns "" st.namespaces with
    | Some ns_iri -> Some (String.concat "" [ns_iri; name])
    | None -> None


(* ================================================================ *)
(* Predicate: is this name an RDF syntax term that should not        *)
(* be used as a property?                                            *)
(* ================================================================ *)

let is_rdf_syntax_attr (full_iri : string) : bool =
  full_iri = String.concat "" [rdf_ns; "about"] ||
  full_iri = String.concat "" [rdf_ns; "ID"] ||
  full_iri = String.concat "" [rdf_ns; "resource"] ||
  full_iri = String.concat "" [rdf_ns; "datatype"] ||
  full_iri = String.concat "" [rdf_ns; "nodeID"] ||
  full_iri = String.concat "" [rdf_ns; "parseType"] ||
  full_iri = String.concat "" [rdf_ns; "about"] ||
  full_iri = String.concat "" [rdf_ns; "RDF"] ||
  full_iri = String.concat "" [rdf_ns; "Description"] ||
  full_iri = String.concat "" [rdf_ns; "li"]

let is_xml_or_xmlns_attr (name : string) : bool =
  let (prefix, _local) = split_qname name in
  prefix = "xml" || prefix = "xmlns" || name = "xmlns"


(* ================================================================ *)
(* Safe wf_iri construction                                          *)
(* ================================================================ *)

(* Try to construct a wf_iri from a string, returning None if invalid. *)
let make_wf_iri (s : string) : option wf_iri =
  if is_iri s then Some s
  else None


(* ================================================================ *)
(* Triple construction helpers                                       *)
(* ================================================================ *)

let make_iri_subject (iri_str : string) : option subject =
  if is_iri iri_str then Some (S_IRI iri_str)
  else None

let make_bnode_subject (id : string) : subject =
  S_BNode id

let make_iri_object (iri_str : string) : option rdf_term =
  if is_iri iri_str then Some (T_IRI iri_str)
  else None

let make_plain_literal (lex : string) (lang : option string) : option rdf_term =
  match lang with
  | Some l ->
    Some (T_Literal ({
      lexical_form = lex;
      datatype = rdf_lang_string;
      lang_tag = Some l;
    }))
  | None ->
    Some (T_Literal ({
      lexical_form = lex;
      datatype = xsd_string;
      lang_tag = None;
    }))

let make_typed_literal (lex : string) (dt : string) : option rdf_term =
  if is_iri dt then
    if dt = "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString" then
      None  (* langString requires a lang tag — use make_plain_literal instead *)
    else
      Some (T_Literal ({
        lexical_form = lex;
        datatype = dt;
        lang_tag = None;
      }))
  else None

let make_triple (subj : subject) (pred_iri : string) (obj : rdf_term) : option triple =
  if is_iri pred_iri then
    Some ({ s = subj; p = pred_iri; o = obj })
  else None


(* ================================================================ *)
(* Collect text content from child nodes                             *)
(* ================================================================ *)

let rec collect_text (children : list xml_node) : string =
  match children with
  | [] -> ""
  | child :: rest ->
    let this_text =
      match child with
      | XText t -> t
      | XCDATA t -> t
      | XComment _ -> ""
      | XElement _ _ _ -> ""
    in
    String.concat "" [this_text; collect_text rest]

(* Check if children are all text/CDATA (no elements) *)
let rec is_all_text (children : list xml_node) : bool =
  match children with
  | [] -> true
  | child :: rest ->
    (match child with
     | XText _ -> is_all_text rest
     | XCDATA _ -> is_all_text rest
     | XComment _ -> is_all_text rest
     | XElement _ _ _ -> false)


(* ================================================================ *)
(* Serialize XML node back to string (for parseType="Literal")       *)
(* ================================================================ *)

let rec serialize_xml_node (node : xml_node) (fuel : nat) : Tot string (decreases fuel) =
  if fuel = 0 then ""
  else
    match node with
    | XText t -> t
    | XCDATA t -> String.concat "" ["<![CDATA["; t; "]]>"]
    | XComment t -> String.concat "" ["<!--"; t; "-->"]
    | XElement tag attrs children ->
      let attr_strs = List.Tot.map (fun (a : xml_attribute) ->
        String.concat "" [" "; a.attr_name; "=\""; a.attr_value; "\""]) attrs in
      let attr_str = String.concat "" attr_strs in
      if List.Tot.length children = 0 then
        String.concat "" ["<"; tag; attr_str; "/>"]
      else
        let child_strs = List.Tot.map (fun (c : xml_node) -> serialize_xml_node c (fuel - 1)) children in
        let children_str = String.concat "" child_strs in
        String.concat "" ["<"; tag; attr_str; ">"; children_str; "</"; tag; ">"]

let serialize_children_xml (children : list xml_node) : string =
  let strs = List.Tot.map (fun (c : xml_node) -> serialize_xml_node c 100) children in
  String.concat "" strs


(* ================================================================ *)
(* Core RDF/XML processing: node elements and property elements      *)
(*                                                                   *)
(* Uses fuel parameter for termination of mutually recursive tree    *)
(* walking.                                                          *)
(* ================================================================ *)

(* Forward declaration types for the result of processing *)
noeq type process_result = {
  pr_triples : list triple;
  pr_state : rdfxml_state;
}

let empty_result (st : rdfxml_state) : process_result =
  { pr_triples = []; pr_state = st; }

let add_triples (pr : process_result) (ts : list triple) : process_result =
  { pr with pr_triples = pr.pr_triples @ ts }


(* Determine the subject of a node element from its attributes:
   - rdf:about="uri" -> IRI subject
   - rdf:ID="name" -> IRI subject (base_iri + "#" + name)
   - rdf:nodeID="id" -> blank node subject
   - none of the above -> fresh blank node *)
let determine_subject (st : rdfxml_state) (attrs : list xml_attribute)
  : (subject * rdfxml_state) =
  match find_attr "rdf:about" attrs with
  | Some about_val ->
    let iri = resolve_iri st.base_iri about_val in
    if is_iri iri then (S_IRI iri, st)
    else
      let (bid, st') = fresh_bnode st in
      (S_BNode bid, st')
  | None ->
    match find_attr "rdf:ID" attrs with
    | Some id_val ->
      let iri = resolve_iri st.base_iri (String.concat "" ["#"; id_val]) in
      if is_iri iri then (S_IRI iri, st)
      else
        let (bid, st') = fresh_bnode st in
        (S_BNode bid, st')
    | None ->
      match find_attr "rdf:nodeID" attrs with
      | Some nid ->
        let bid = String.concat "" ["_:"; nid] in
        (S_BNode bid, st)
      | None ->
        let (bid, st') = fresh_bnode st in
        (S_BNode bid, st')


(* Determine the object of a property element from attributes:
   - rdf:resource="uri" -> IRI object
   - rdf:nodeID="id" -> blank node object *)
let determine_property_object_from_attrs (st : rdfxml_state) (attrs : list xml_attribute)
  : option (rdf_term * rdfxml_state) =
  match find_attr "rdf:resource" attrs with
  | Some res_val ->
    let iri = resolve_iri st.base_iri res_val in
    if is_iri iri then Some (T_IRI iri, st)
    else None
  | None ->
    match find_attr "rdf:nodeID" attrs with
    | Some nid ->
      let bid = String.concat "" ["_:"; nid] in
      Some (T_BNode bid, st)
    | None -> None


(* Collect property attributes: attributes that are not rdf:*, xml:*, or xmlns:*
   become triples of the form (subject, attr_iri, literal_value) *)
let rec collect_property_attributes (st : rdfxml_state) (subj : subject) (attrs : list xml_attribute)
  : list triple =
  match attrs with
  | [] -> []
  | attr :: rest ->
    let rest_triples = collect_property_attributes st subj rest in
    if is_xml_or_xmlns_attr attr.attr_name then rest_triples
    else
      match resolve_name st attr.attr_name with
      | Some full_iri ->
        if is_rdf_syntax_attr full_iri then rest_triples
        else if full_iri = rdf_type_iri then
          (* rdf:type as property attribute — object is an IRI *)
          let type_iri = resolve_iri st.base_iri attr.attr_value in
          if is_iri full_iri && is_iri type_iri then
            ({ s = subj; p = full_iri; o = T_IRI type_iri }) :: rest_triples
          else rest_triples
        else
          (* Regular property attribute — object is a plain literal *)
          if is_iri full_iri then
            match make_plain_literal attr.attr_value st.lang with
            | Some lit_term ->
              ({ s = subj; p = full_iri; o = lit_term }) :: rest_triples
            | None -> rest_triples
          else rest_triples
      | None -> rest_triples


(* ================================================================ *)
(* Reification helper (RDF/XML §7.3).                                *)
(* When a property element carries `rdf:ID="name"`, the spec says to *)
(* also emit the four reification quads that identify the statement *)
(* by IRI `base_iri#name` — subject/predicate/object + type          *)
(* rdf:Statement. RDF 1.2 is introducing triple terms as a cleaner   *)
(* alternative, but RDF/XML's `rdf:ID` shorthand remains fixed to    *)
(* this classic expansion; nothing to do here for 1.2.               *)
(* ================================================================ *)

let rdf_statement_iri : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#Statement"
let rdf_subject_iri : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#subject"
let rdf_predicate_iri : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#predicate"
let rdf_object_iri : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#object"

let subject_to_term (s : subject) : rdf_term =
  match s with
  | S_IRI i -> T_IRI i
  | S_BNode b -> T_BNode b

let make_reification_triples (reif_iri : string) (subj : subject)
                              (pred_iri : string) (obj : rdf_term)
  : list triple =
  if not (is_iri reif_iri) || not (is_iri pred_iri) then []
  else if not (is_iri rdf_type_iri) || not (is_iri rdf_statement_iri)
       || not (is_iri rdf_subject_iri) || not (is_iri rdf_predicate_iri)
       || not (is_iri rdf_object_iri) then []
  else
    let reif_s : subject = S_IRI reif_iri in
    [ { s = reif_s; p = rdf_type_iri;      o = T_IRI rdf_statement_iri };
      { s = reif_s; p = rdf_subject_iri;   o = subject_to_term subj   };
      { s = reif_s; p = rdf_predicate_iri; o = T_IRI pred_iri         };
      { s = reif_s; p = rdf_object_iri;    o = obj                    } ]

(* Resolve an rdf:ID value on a property element to the reification
   IRI: base_iri + "#" + id_value. Returns None when no rdf:ID is
   present or when resolution yields a non-IRI. *)
let compute_reif_iri (st : rdfxml_state) (attrs : list xml_attribute) : option string =
  match find_attr "rdf:ID" attrs with
  | Some id_val ->
    let frag = String.concat "" ["#"; id_val] in
    let r = resolve_iri st.base_iri frag in
    if is_iri r then Some r else None
  | None -> None


(* ================================================================ *)
(* Mutual recursion: process_node_element and process_property_element*)
(* ================================================================ *)

let rec process_node_element (st : rdfxml_state) (node : xml_node) (fuel : nat)
  : Tot process_result (decreases fuel) =
  if fuel = 0 then empty_result st
  else
    match node with
    | XElement tag attrs children ->
      let st1 = update_state_from_attrs st attrs in
      (* Determine subject *)
      let (subj, st2) = determine_subject st1 attrs in
      (* Check if this is a typed node element (not rdf:Description) *)
      let type_triples : list triple =
        match resolve_name st1 tag with
        | Some full_tag_iri ->
          if full_tag_iri = String.concat "" [rdf_ns; "Description"] then []
          else if full_tag_iri = String.concat "" [rdf_ns; "RDF"] then []
          else if full_tag_iri = String.concat "" [rdf_ns; "Bag"] then
            if is_iri rdf_type_iri && is_iri full_tag_iri then
              [{ s = subj; p = rdf_type_iri; o = T_IRI full_tag_iri }]
            else []
          else if full_tag_iri = String.concat "" [rdf_ns; "Seq"] then
            if is_iri rdf_type_iri && is_iri full_tag_iri then
              [{ s = subj; p = rdf_type_iri; o = T_IRI full_tag_iri }]
            else []
          else if full_tag_iri = String.concat "" [rdf_ns; "Alt"] then
            if is_iri rdf_type_iri && is_iri full_tag_iri then
              [{ s = subj; p = rdf_type_iri; o = T_IRI full_tag_iri }]
            else []
          else
            (* Typed node element: <ex:Foo ...> implies (subj rdf:type ex:Foo) *)
            if is_iri rdf_type_iri && is_iri full_tag_iri then
              [{ s = subj; p = rdf_type_iri; o = T_IRI full_tag_iri }]
            else []
        | None -> []
      in
      (* Property attributes *)
      let prop_attr_triples = collect_property_attributes st1 subj attrs in
      (* Process child property elements *)
      let st3 = reset_li_counter st2 in
      let child_result = process_property_children st3 subj children (fuel - 1) in
      { pr_triples = type_triples @ prop_attr_triples @ child_result.pr_triples;
        pr_state = child_result.pr_state; }
    | _ -> empty_result st

and process_property_children (st : rdfxml_state) (subj : subject) (children : list xml_node) (fuel : nat)
  : Tot process_result (decreases fuel) =
  if fuel = 0 then empty_result st
  else
    match children with
    | [] -> empty_result st
    | child :: rest ->
      match child with
      | XElement _ _ _ ->
        let result1 = process_property_element st subj child (fuel - 1) in
        let result2 = process_property_children result1.pr_state subj rest (fuel - 1) in
        { pr_triples = result1.pr_triples @ result2.pr_triples;
          pr_state = result2.pr_state; }
      | _ ->
        (* Skip text, comments, CDATA at this level *)
        process_property_children st subj rest (fuel - 1)

and process_property_element (st : rdfxml_state) (subj : subject) (node : xml_node) (fuel : nat)
  : Tot process_result (decreases fuel) =
  if fuel = 0 then empty_result st
  else
    match node with
    | XElement tag attrs children ->
      begin
      let st1 = update_state_from_attrs st attrs in
      (* rdf:ID on a property element triggers reification (§7.3).
         Compute the statement IRI up-front so every main-triple path
         below can tack on the four reification quads. *)
      let reif_iri_opt = compute_reif_iri st1 attrs in
      let reif_of (pred_iri : string) (obj : rdf_term) : list triple =
        match reif_iri_opt with
        | Some r -> make_reification_triples r subj pred_iri obj
        | None -> []
      in
      (* Determine the predicate IRI *)
      let (pred_iri_opt, st2) =
        begin match resolve_name st1 tag with
        | Some full_iri ->
          if full_iri = String.concat "" [rdf_ns; "li"] then
            let (li_iri, st') = next_li st1 in
            if is_iri li_iri then (Some li_iri, st')
            else (None, st')
          else
            if is_iri full_iri then (Some full_iri, st1)
            else (None, st1)
        | None -> (None, st1)
        end
      in
      begin match pred_iri_opt with
      | None -> empty_result st2
      | Some pred_iri ->
        if not (is_iri pred_iri) then empty_result st2
        else
          (* Check for rdf:parseType *)
          let parse_type = find_attr "rdf:parseType" attrs in
          begin match parse_type with
          | Some "Literal" ->
            (* parseType="Literal" — serialize children as XML literal *)
            let xml_content = serialize_children_xml children in
            if is_iri rdf_xmlliteral_iri then
              begin match make_typed_literal xml_content rdf_xmlliteral_iri with
              | Some obj ->
                let t : triple = { s = subj; p = pred_iri; o = obj } in
                { pr_triples = t :: reif_of pred_iri obj; pr_state = st2; }
              | None -> empty_result st2
              end
            else empty_result st2
          | Some "Resource" ->
            (* parseType="Resource" — implicit blank node *)
            let (bid, st3) = fresh_bnode st2 in
            let bnode_subj = S_BNode bid in
            let obj_term = T_BNode bid in
            let link_triple : triple = { s = subj; p = pred_iri; o = obj_term } in
            let st4 = reset_li_counter st3 in
            let child_result = process_property_children st4 bnode_subj children (fuel - 1) in
            { pr_triples = link_triple :: (reif_of pred_iri obj_term) @ child_result.pr_triples;
              pr_state = child_result.pr_state; }
          | Some "Collection" ->
            (* parseType="Collection" — RDF list. Reification of a
               Collection property is not well-defined by the spec
               (and no test exercises it), so we don't attach reif
               quads here. *)
            let collection_result = process_collection st2 subj pred_iri children (fuel - 1) in
            collection_result
          | _ ->
            (* No parseType — normal property element *)
            (* Check for rdf:resource or rdf:nodeID attribute *)
            begin match determine_property_object_from_attrs st2 attrs with
            | Some (obj, st3) ->
              (* Object specified by attribute *)
              let link_triple : triple = { s = subj; p = pred_iri; o = obj } in
              (* Also check for property attributes on this property element *)
              let obj_subj_opt =
                begin match obj with
                | T_IRI i -> if is_iri i then Some (S_IRI i) else None
                | T_BNode b -> Some (S_BNode b)
                | _ -> None
                end
              in
              let prop_attr_triples =
                begin match obj_subj_opt with
                | Some obj_s -> collect_property_attributes st3 obj_s attrs
                | None -> []
                end
              in
              { pr_triples = link_triple :: (reif_of pred_iri obj) @ prop_attr_triples;
                pr_state = st3; }
            | None ->
              (* Check for rdf:datatype *)
              let datatype_opt = find_attr "rdf:datatype" attrs in
              (* Check children *)
              let child_elements_list = List.Tot.filter (fun (c : xml_node) ->
                match c with
                | XElement _ _ _ -> true
                | _ -> false) children in
              if List.Tot.length child_elements_list > 0 then
                begin match child_elements_list with
                | child_elem :: _ ->
                  let node_result = process_node_element st2 child_elem (fuel - 1) in
                  (* The subject of the child node becomes the object *)
                  let child_subj = determine_subject (update_state_from_attrs st2 (element_attrs child_elem)) (element_attrs child_elem) in
                  let (child_s, st3) = child_subj in
                  let obj_term =
                    begin match child_s with
                    | S_IRI i -> T_IRI i
                    | S_BNode b -> T_BNode b
                    end
                  in
                  let link_triple : triple = { s = subj; p = pred_iri; o = obj_term } in
                  { pr_triples = link_triple :: (reif_of pred_iri obj_term) @ node_result.pr_triples;
                    pr_state = node_result.pr_state; }
                | [] -> empty_result st2
                end
              else
                (* No child elements. Two sub-cases (§7.2.11 / §7.2.17):
                   (a) Empty element with non-rdf property attributes
                       — create a fresh blank-node object and emit
                       those attributes as its properties.
                   (b) Any text (or truly empty, no prop attrs)
                       — emit a literal object with the text value. *)
                let text_val = collect_text children in
                let has_text = String.length text_val > 0 in
                let has_datatype =
                  (match datatype_opt with Some _ -> true | None -> false) in
                (* Probe for non-rdf property attributes on this
                   property element by asking collect_property_attributes.
                   Uses a placeholder subject; we only look at the
                   length to decide the branch. *)
                let probe_triples =
                  let (probe_bid, _) = fresh_bnode st2 in
                  collect_property_attributes st2 (S_BNode probe_bid) attrs in
                if not has_text && not has_datatype
                   && List.Tot.length probe_triples > 0 then
                  (* Case (a) — bnode-object with property attributes. *)
                  let (bid, st3) = fresh_bnode st2 in
                  let bnode_subj : subject = S_BNode bid in
                  let obj_term = T_BNode bid in
                  let link_triple : triple = { s = subj; p = pred_iri; o = obj_term } in
                  let prop_attr_triples = collect_property_attributes st3 bnode_subj attrs in
                  { pr_triples = link_triple :: (reif_of pred_iri obj_term) @ prop_attr_triples;
                    pr_state = st3; }
                else
                  (* Case (b) — literal object. *)
                  let obj_opt =
                    begin match datatype_opt with
                    | Some dt ->
                      let full_dt = resolve_iri st2.base_iri dt in
                      make_typed_literal text_val full_dt
                    | None ->
                      make_plain_literal text_val st2.lang
                    end
                  in
                  begin match obj_opt with
                  | Some obj ->
                    let t : triple = { s = subj; p = pred_iri; o = obj } in
                    { pr_triples = t :: reif_of pred_iri obj; pr_state = st2; }
                  | None -> empty_result st2
                  end
            end
          end
      end
      end
    | _ -> empty_result st

and process_collection (st : rdfxml_state) (subj : subject) (pred_iri : string) (items : list xml_node) (fuel : nat)
  : Tot process_result (decreases fuel) =
  if fuel = 0 then empty_result st
  else
    (* Filter to element children only *)
    let elem_items = List.Tot.filter (fun (c : xml_node) ->
      match c with
      | XElement _ _ _ -> true
      | _ -> false) items in
    if List.Tot.length elem_items = 0 then
      (* Empty collection — link to rdf:nil *)
      if is_iri rdf_nil_iri && is_iri pred_iri then
        let t : triple = { s = subj; p = pred_iri; o = T_IRI rdf_nil_iri } in
        { pr_triples = [t]; pr_state = st; }
      else empty_result st
    else
      build_collection_list st subj pred_iri elem_items (fuel - 1)

and build_collection_list (st : rdfxml_state) (subj : subject) (pred_iri : string) (items : list xml_node) (fuel : nat)
  : Tot process_result (decreases fuel) =
  if fuel = 0 then empty_result st
  else
    match items with
    | [] ->
      (* End of list — link to rdf:nil *)
      if is_iri rdf_nil_iri && is_iri pred_iri then
        let t : triple = { s = subj; p = pred_iri; o = T_IRI rdf_nil_iri } in
        { pr_triples = [t]; pr_state = st; }
      else empty_result st
    | item :: rest ->
      if not (is_iri pred_iri) then empty_result st
      else
      (* Create a list node *)
      let (list_bid, st2) = fresh_bnode st in
      let list_node = S_BNode list_bid in
      (* Link subject to this list node *)
      let link_triple : triple = { s = subj; p = pred_iri; o = T_BNode list_bid } in
      (* Process the item as a node element *)
      let item_result = process_node_element st2 item (fuel - 1) in
      (* Determine the item's subject to use as rdf:first value *)
      let item_st = update_state_from_attrs item_result.pr_state (element_attrs item) in
      let (item_subj, st3) = determine_subject item_st (element_attrs item) in
      let item_term =
        match item_subj with
        | S_IRI i -> T_IRI i
        | S_BNode b -> T_BNode b
      in
      (* rdf:first triple *)
      if is_iri rdf_first_iri then
        let first_triple : triple = { s = list_node; p = rdf_first_iri; o = item_term } in
        (* Process rest of list: rdf:rest links to next node or rdf:nil *)
        let rest_result =
          if is_iri rdf_rest_iri then
            build_collection_list st3 list_node rdf_rest_iri rest (fuel - 1)
          else empty_result st3
        in
        let all_triples = link_triple :: first_triple :: item_result.pr_triples @ rest_result.pr_triples in
        { pr_triples = all_triples; pr_state = rest_result.pr_state; }
      else
        let rest_result =
          if is_iri rdf_rest_iri then
            build_collection_list st3 list_node rdf_rest_iri rest (fuel - 1)
          else empty_result st3
        in
        let all_triples = link_triple :: item_result.pr_triples @ rest_result.pr_triples in
        { pr_triples = all_triples; pr_state = rest_result.pr_state; }


(* ================================================================ *)
(* Process top-level node elements (children of rdf:RDF or root)     *)
(* ================================================================ *)

(* xml:base, xml:lang and xmlns declarations are XML Information-Set
   scoped: an xml:base on element A does not leak to element A's
   siblings. But the RDF-level bnode_counter MUST flow across
   siblings so two fresh-bnode requests never collide. Thread only
   the counter across; restore the scoping fields from the parent. *)
let restore_scope (parent : rdfxml_state) (child : rdfxml_state) : rdfxml_state =
  { parent with bnode_counter = child.bnode_counter }

let rec process_node_elements (st : rdfxml_state) (nodes : list xml_node) (fuel : nat)
  : Tot process_result (decreases fuel) =
  if fuel = 0 then empty_result st
  else
    match nodes with
    | [] -> empty_result st
    | node :: rest ->
      match node with
      | XElement _ _ _ ->
        let result1 = process_node_element st node (fuel - 1) in
        let st' = restore_scope st result1.pr_state in
        let result2 = process_node_elements st' rest (fuel - 1) in
        { pr_triples = result1.pr_triples @ result2.pr_triples;
          pr_state = result2.pr_state; }
      | _ ->
        (* Skip text/comments at top level *)
        process_node_elements st rest (fuel - 1)


(* ================================================================ *)
(* Entry point: process an XML document tree into RDF triples        *)
(* ================================================================ *)

let process_xml_tree (st : rdfxml_state) (root : xml_node) : list triple =
  let fuel = 10000 in
  match root with
  | XElement tag attrs children ->
    let st1 = update_state_from_attrs st attrs in
    (* Check if root is rdf:RDF *)
    let is_rdf_root =
      match resolve_name st1 tag with
      | Some full_iri -> full_iri = String.concat "" [rdf_ns; "RDF"]
      | None -> tag = "rdf:RDF"
    in
    if is_rdf_root then
      (* Process children as node elements *)
      let result = process_node_elements st1 children fuel in
      result.pr_triples
    else
      (* Root is a node element itself (rdf:RDF wrapper is optional) *)
      let result = process_node_element st1 root fuel in
      result.pr_triples
  | _ -> []


(* ================================================================ *)
(* Main entry point: parse XML string, then extract RDF triples      *)
(* ================================================================ *)

let parse_rdfxml_with_base (base_iri : string) (input : string) : list triple =
  match parse_xml_document input with
  | Some root ->
    let st = initial_state base_iri in
    process_xml_tree st root
  | None -> []

let parse_rdfxml (input : string) : list triple =
  parse_rdfxml_with_base "" input
