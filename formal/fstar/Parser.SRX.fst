module Parser.SRX

(* ================================================================ *)
(* SPARQL Results XML (SRX) parser — verified F* implementation     *)
(*                                                                  *)
(* Parses SRX format (W3C SPARQL Query Results XML Format):         *)
(*   https://www.w3.org/TR/rdf-sparql-XMLres/                      *)
(*                                                                  *)
(* Takes an XML string, parses it via Parser.XML, then walks the    *)
(* xml_node tree to extract variable bindings or boolean results.   *)
(* ================================================================ *)

open FStar.String
open FStar.List.Tot
open Parser.XML
open RDF.Graph.Executable

(* ================================================================ *)
(* Namespace-flexible tag matching                                   *)
(*                                                                  *)
(* SRX files may use bare tags like <result> or namespace-prefixed  *)
(* tags like <rs:result>. We strip the prefix when matching.        *)
(* ================================================================ *)

(* Find the position of ':' in a character list, returning the tail after it *)
let rec find_colon_in_list (cs: list FStar.Char.char) : list FStar.Char.char =
  match cs with
  | [] -> []
  | c :: rest ->
    if FStar.Char.int_of_char c = 0x3A (* ':' *)
    then rest
    else find_colon_in_list rest

(* Strip namespace prefix from a tag name: "rs:result" -> "result" *)
let strip_ns_prefix (tag: string) : string =
  let cs = String.list_of_string tag in
  let after = find_colon_in_list cs in
  match after with
  | [] -> tag  (* no colon found, return original *)
  | _ -> String.string_of_list after

(* Match a tag name against an expected local name, ignoring namespace prefix *)
let tag_matches (expected: string) (actual: string) : bool =
  actual = expected || strip_ns_prefix actual = expected


(* ================================================================ *)
(* XML tree navigation helpers                                       *)
(* ================================================================ *)

(* Find the first child element matching a tag name (namespace-flexible) *)
let find_child (tag: string) (children: list xml_node) : option xml_node =
  match List.Tot.find (fun (node: xml_node) ->
    match node with
    | XElement t _ _ -> tag_matches tag t
    | _ -> false
  ) children with
  | Some n -> Some n
  | None -> None

(* Find all child elements matching a tag name (namespace-flexible) *)
let find_children (tag: string) (children: list xml_node) : list xml_node =
  List.Tot.filter (fun (node: xml_node) ->
    match node with
    | XElement t _ _ -> tag_matches tag t
    | _ -> false
  ) children

(* Get an attribute value by name from an attribute list *)
let get_attr (name: string) (attrs: list xml_attribute) : option string =
  match List.Tot.find (fun (a: xml_attribute) -> a.attr_name = name) attrs with
  | Some a -> Some a.attr_value
  | None -> None

(* Collect text content from an xml_node (concatenating all text/cdata children).
   Delegates to text_content from Parser.XML which has proper mutual-recursion
   termination proof via text_content_list. *)
let collect_text (node: xml_node) : string = text_content node


(* ================================================================ *)
(* Binding value parsers                                             *)
(*                                                                  *)
(* Each <binding> contains exactly one of:                          *)
(*   <uri>...</uri>                                                 *)
(*   <bnode>...</bnode>                                             *)
(*   <literal ...>...</literal>                                     *)
(* ================================================================ *)

(* Parse a <uri>...</uri> node into an rdf_term *)
let parse_uri_value (node: xml_node) : option rdf_term =
  let uri_str = collect_text node in
  if is_iri uri_str then Some (T_IRI uri_str)
  else None

(* Parse a <bnode>...</bnode> node into an rdf_term *)
let parse_bnode_value (node: xml_node) : option rdf_term =
  let bnode_str = collect_text node in
  Some (T_BNode bnode_str)

(* Parse a <literal>...</literal> node into an rdf_term.
   Handles:
   - Plain literals: <literal>foo</literal>  -> "foo"^^xsd:string
   - Language-tagged: <literal xml:lang="en">foo</literal> -> "foo"@en
   - Datatyped: <literal datatype="...">foo</literal> -> "foo"^^datatype *)
let parse_literal_value (node: xml_node) : option rdf_term =
  match node with
  | XElement _ attrs children ->
    let lex = String.concat "" (List.Tot.map collect_text children) in
    let lang = get_attr "xml:lang" attrs in
    let dt = get_attr "datatype" attrs in
    begin match lang, dt with
    | Some lang_val, _ ->
      (* Language-tagged literal: datatype must be rdf:langString *)
      let lit : literal = {
        lexical_form = lex;
        datatype = rdf_lang_string;
        lang_tag = Some lang_val;
      } in
      if literal_wf lit then Some (T_Literal lit)
      else None
    | None, Some dt_val ->
      (* Datatyped literal *)
      if is_iri dt_val then
        let lit : literal = {
          lexical_form = lex;
          datatype = dt_val;
          lang_tag = None;
        } in
        if literal_wf lit then Some (T_Literal lit)
        else None
      else None
    | None, None ->
      (* Plain literal: defaults to xsd:string per RDF 1.1 *)
      let lit : literal = {
        lexical_form = lex;
        datatype = xsd_string;
        lang_tag = None;
      } in
      if literal_wf lit then Some (T_Literal lit)
      else None
    end
  | _ -> None


(* Parse the value child of a <binding> element.
   Looks for the first <uri>, <literal>, or <bnode> child. *)
let parse_binding_value (node: xml_node) : option rdf_term =
  match node with
  | XElement _ _ children ->
    let elems = List.Tot.filter (fun (child: xml_node) ->
      match child with
      | XElement _ _ _ -> true
      | _ -> false
    ) children in
    begin match elems with
    | [] -> None
    | value_node :: _ ->
      match value_node with
      | XElement t _ _ ->
        let local = strip_ns_prefix t in
        if local = "uri" then parse_uri_value value_node
        else if local = "bnode" then parse_bnode_value value_node
        else if local = "literal" then parse_literal_value value_node
        else None
      | _ -> None
    end
  | _ -> None


(* ================================================================ *)
(* Result row parser                                                 *)
(* ================================================================ *)

(* Parse a single <binding name="x">...</binding> element *)
let parse_binding (node: xml_node) : option (string * rdf_term) =
  match node with
  | XElement _ attrs _ ->
    begin match get_attr "name" attrs with
    | Some var_name ->
      begin match parse_binding_value node with
      | Some term -> Some (var_name, term)
      | None -> None
      end
    | None -> None
    end
  | _ -> None

(* Parse a <result> element containing multiple <binding> children.
   Skips bindings that fail to parse (unbound variables are allowed in SRX). *)
let parse_result_row (node: xml_node) : list (string * rdf_term) =
  match node with
  | XElement _ _ children ->
    let bindings = find_children "binding" children in
    List.Tot.concatMap (fun (b: xml_node) ->
      match parse_binding b with
      | Some pair -> [pair]
      | None -> []
    ) bindings
  | _ -> []


(* ================================================================ *)
(* Variable extraction from <head>                                   *)
(* ================================================================ *)

(* Extract variable names from <head><variable name="x"/>...</head> *)
let parse_head_vars (head_node: xml_node) : list string =
  match head_node with
  | XElement _ _ children ->
    let var_elems = find_children "variable" children in
    List.Tot.concatMap (fun (v: xml_node) ->
      match v with
      | XElement _ attrs _ ->
        begin match get_attr "name" attrs with
        | Some n -> [n]
        | None -> []
        end
      | _ -> []
    ) var_elems
  | _ -> []


(* ================================================================ *)
(* Top-level SRX parsers                                             *)
(* ================================================================ *)

(* Parse a full SRX document into variable names and result rows.
   Returns None if parsing fails. *)
let parse_srx_results (input: string) : option (list string * list (list (string * rdf_term))) =
  match parse_xml_document input with
  | None -> None
  | Some root ->
    match root with
    | XElement _ _ children ->
      (* Find <head> element *)
      let vars = match find_child "head" children with
        | Some head_node -> parse_head_vars head_node
        | None -> []
      in
      (* Find <results> element *)
      begin match find_child "results" children with
      | Some results_node ->
        begin match results_node with
        | XElement _ _ result_children ->
          let result_elems = find_children "result" result_children in
          let rows = List.Tot.map parse_result_row result_elems in
          Some (vars, rows)
        | _ -> None
        end
      | None ->
        (* No <results> — might be a boolean result, or empty *)
        Some (vars, [])
      end
    | _ -> None

(* Parse a boolean SRX result.
   Returns None if parsing fails or the document is not a boolean result. *)
let parse_srx_boolean (input: string) : option bool =
  match parse_xml_document input with
  | None -> None
  | Some root ->
    match root with
    | XElement _ _ children ->
      begin match find_child "boolean" children with
      | Some bool_node ->
        let txt = collect_text bool_node in
        if txt = "true" then Some true
        else if txt = "false" then Some false
        else None
      | None -> None
      end
    | _ -> None
