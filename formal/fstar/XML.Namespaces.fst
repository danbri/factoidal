module XML.Namespaces

// "Namespaces in XML" (1.0 and 1.1) well-formedness, as a SEPARATE
// layer on top of Parser.XML's plain-XML-1.0 parse tree -- not baked
// into Parser.XML.parse_xml_document itself. Plain XML 1.0 legally
// allows ':' anywhere in a Name outside a Namespaces-aware reading
// (xmltest/ exercises this on purpose, predating Namespaces in XML),
// and Parser.RDFXML.fst already does its own namespace processing
// for RDF/XML documents -- this module exists so bin/xml-runner's
// xmlconf runner can additionally score the `eduni/namespaces/*`
// collections, without changing what Parser.XML itself accepts or
// touching Parser.RDFXML's separate, RDF/XML-specific namespace
// handling. See CLAUDE.md 2026-07-05 owner directive, cluster 3.
//
// References:
//   https://www.w3.org/TR/xml-names/       (Namespaces in XML 1.0)
//   https://www.w3.org/TR/xml-names11/     (Namespaces in XML 1.1)

open FStar.List.Tot
open Parser.FastString
open Parser.XML

(* --- Reserved namespace names ---------------------------------------- *)

let xml_ns_uri : string = "http://www.w3.org/XML/1998/namespace"
let xmlns_ns_uri : string = "http://www.w3.org/2000/xmlns/"

(* --- QName syntax ------------------------------------------------------
   QName ::= PrefixedName | UnprefixedName
   PrefixedName ::= Prefix ':' LocalPart
   A raw XML Name is a legal QName iff it has at most one colon, and
   that colon is neither the first nor the last character (which
   would give an empty prefix or empty local part). Plain XML 1.0
   Names may contain any number of colons anywhere -- this production
   is strictly a Namespaces-layer restriction on top of that. *)

type qname_split =
  | QSimple    : local:string -> qname_split
  | QPrefixed  : prefix:string -> local:string -> qname_split
  | QMalformed : qname_split

let rec find_colon_positions (s:string) (pos:nat) (limit:nat) (fuel:nat) (acc:list nat)
  : Tot (list nat) (decreases fuel) =
  if fuel = 0 then List.Tot.rev acc
  else if pos >= limit then List.Tot.rev acc
  else
    let c = fs_byte_index s pos in
    if c = ':' then find_colon_positions s (pos + 1) limit (fuel - 1) (pos :: acc)
    else find_colon_positions s (pos + 1) limit (fuel - 1) acc

let split_qname (s:string) : qname_split =
  let len = fs_byte_length s in
  match find_colon_positions s 0 len len [] with
  | [] -> QSimple s
  | [i] ->
    if i = 0 || i + 1 >= len then QMalformed
    else QPrefixed (fs_byte_sub s 0 i) (fs_byte_sub s (i + 1) (len - (i + 1)))
  | _ -> QMalformed

(* --- Namespace scope -----------------------------------------------------
   A binding list (prefix, Some uri) | (prefix, None). `None` records
   an EXPLICIT unbind (xmlns:prefix=""), so a lookup that hits it
   reports "unbound" rather than silently falling through to an outer
   scope's stale binding for the same prefix -- this is what makes
   rmt-ns11-005 ("Illegal use of a prefix that has been unbound", on
   the SAME element as the unbinding attribute) reject correctly.
   New declarations are prepended, so the innermost/most-recent
   declaration for a prefix always shadows outer ones. *)

type ns_scope = list (string & option string)

let initial_scope : ns_scope = [("xml", Some xml_ns_uri)]

let rec lookup_prefix (scope:ns_scope) (prefix:string) : Tot (option string) (decreases scope) =
  match scope with
  | [] -> None
  | (p, u) :: rest -> if p = prefix then u else lookup_prefix rest prefix

(* --- Applying one element's own xmlns:*/xmlns declarations --------------
   `version` is the document's declared XML version ("1.0" default,
   or "1.1"): Namespaces in XML 1.0 forbids undeclaring a *prefixed*
   namespace binding via an empty value (only the default namespace
   may be undeclared that way); Namespaces in XML 1.1 permits it for
   prefixed bindings too. Returns None if any declaration on this
   element is itself illegal (a reserved-prefix/reserved-URI
   violation, or an out-of-version unbind attempt). *)

let rec apply_declarations (version:string) (scope:ns_scope) (attrs:list xml_attribute)
  : Tot (option ns_scope) (decreases attrs) =
  match attrs with
  | [] -> Some scope
  | a :: rest ->
    begin match split_qname a.attr_name with
    | QSimple "xmlns" ->
      // Default namespace declaration. Reserved-URI rules apply the
      // same as for prefixed declarations; unlike prefixed bindings,
      // the default namespace may always be undeclared via "" (both
      // XML Namespaces 1.0 and 1.1).
      let v = a.attr_value in
      if v = xml_ns_uri || v = xmlns_ns_uri then None
      else
        let entry = if v = "" then ("", None) else ("", Some v) in
        begin match apply_declarations version scope rest with
        | None -> None
        | Some sc -> Some (entry :: sc)
        end
    | QPrefixed "xmlns" local ->
      let v = a.attr_value in
      if local = "xmlns" then None                          // "xmlns" itself is never a bindable prefix
      else if local = "xml" && v <> xml_ns_uri then None     // "xml" is fixed to its one URI
      else if local <> "xml" && v = xml_ns_uri then None     // the XML namespace name is reserved to "xml"
      else if v = xmlns_ns_uri then None                     // the xmlns namespace name binds to no prefix
      else if v = "" && version <> "1.1" then None            // 1.0: prefixed unbind is illegal
      else
        let entry = if v = "" then (local, None) else (local, Some v) in
        begin match apply_declarations version scope rest with
        | None -> None
        | Some sc -> Some (entry :: sc)
        end
    | _ -> apply_declarations version scope rest
    end

(* --- QName syntax gate over a whole attribute list ---------------------- *)

let rec all_attr_names_wellformed (attrs:list xml_attribute) : Tot bool (decreases attrs) =
  match attrs with
  | [] -> true
  | a :: rest ->
    begin match split_qname a.attr_name with
    | QMalformed -> false
    | _ -> all_attr_names_wellformed rest
    end

(* --- Prefix-bound checks -------------------------------------------------
   Every element/attribute QName with a (non-"xmlns"-declaration)
   prefix must resolve against the in-scope bindings computed AFTER
   this same element's own declarations have been applied -- a
   declaration is in scope for the element that carries it, including
   that element's own name and its other attributes. *)

let tag_prefix_bound (scope:ns_scope) (qs:qname_split) : bool =
  match qs with
  | QSimple _ -> true
  | QPrefixed pfx _ -> (match lookup_prefix scope pfx with Some _ -> true | None -> false)
  | QMalformed -> false

let rec attrs_prefixes_bound (scope:ns_scope) (attrs:list xml_attribute)
  : Tot bool (decreases attrs) =
  match attrs with
  | [] -> true
  | a :: rest ->
    begin match split_qname a.attr_name with
    | QSimple "xmlns" -> attrs_prefixes_bound scope rest
    | QPrefixed "xmlns" _ -> attrs_prefixes_bound scope rest
    | QSimple _ -> attrs_prefixes_bound scope rest
    | QPrefixed pfx _ ->
      begin match lookup_prefix scope pfx with
      | Some _ -> attrs_prefixes_bound scope rest
      | None -> false
      end
    | QMalformed -> false
    end

(* --- Attribute uniqueness after namespace expansion ---------------------
   Two attributes with different QNames can still collide once their
   prefixes resolve to the same (namespace-uri, local-name) pair
   (rmt-ns10-036: prefixes 'a' and 'b' both bound to the same URI).
   Unprefixed attributes are never subject to the default namespace
   (XML Namespaces §5.2), so their key is simply (None, name). The
   xmlns:*/xmlns declarations themselves are excluded (they are not,
   in this sense, "attributes in a namespace" to be compared). *)

let expand_attr_key (scope:ns_scope) (a:xml_attribute) : option (option string & string) =
  match split_qname a.attr_name with
  | QSimple "xmlns" -> None
  | QPrefixed "xmlns" _ -> None
  | QSimple name -> Some (None, name)
  | QPrefixed pfx local -> Some (lookup_prefix scope pfx, local)
  | QMalformed -> None

let rec expand_attr_keys (scope:ns_scope) (attrs:list xml_attribute)
  : Tot (list (option string & string)) (decreases attrs) =
  match attrs with
  | [] -> []
  | a :: rest ->
    (match expand_attr_key scope a with
     | Some k -> k :: expand_attr_keys scope rest
     | None -> expand_attr_keys scope rest)

let rec mem_key (k:(option string & string)) (ks:list (option string & string))
  : Tot bool (decreases ks) =
  match ks with
  | [] -> false
  | k2 :: rest -> if k = k2 then true else mem_key k rest

let rec keys_unique (ks:list (option string & string)) : Tot bool (decreases ks) =
  match ks with
  | [] -> true
  | k :: rest -> if mem_key k rest then false else keys_unique rest

let attrs_unique_expanded (scope:ns_scope) (attrs:list xml_attribute) : bool =
  keys_unique (expand_attr_keys scope attrs)

(* --- Whole-tree walk ------------------------------------------------------ *)

let rec check_element (version:string) (scope:ns_scope) (node:xml_node)
  : Tot bool (decreases node) =
  match node with
  | XElement tag attrs children ->
    begin match split_qname tag with
    | QMalformed -> false
    | tag_split ->
      if not (all_attr_names_wellformed attrs) then false
      else
        begin match apply_declarations version scope attrs with
        | None -> false
        | Some new_scope ->
          if not (tag_prefix_bound new_scope tag_split) then false
          else if not (attrs_prefixes_bound new_scope attrs) then false
          else if not (attrs_unique_expanded new_scope attrs) then false
          else check_children version new_scope children
        end
    end
  | _ -> true

and check_children (version:string) (scope:ns_scope) (nodes:list xml_node)
  : Tot bool (decreases nodes) =
  match nodes with
  | [] -> true
  | hd :: tl ->
    if check_element version scope hd then check_children version scope tl else false

(* is_namespace_wellformed version root
     True iff every element/attribute QName, xmlns:*/xmlns
     declaration, and namespace-uniqueness constraint in `root` (as
     parsed by Parser.XML.parse_xml_document) satisfies "Namespaces in
     XML" well-formedness. `version` is the document's declared XML
     version string ("1.0" if absent), which only affects whether an
     empty-value PREFIXED xmlns declaration is a legal unbind (1.1
     only) or a violation (1.0). *)
let is_namespace_wellformed (version:string) (root:xml_node) : bool =
  check_element version initial_scope root
