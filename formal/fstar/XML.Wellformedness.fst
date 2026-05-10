module XML.Wellformedness

(* Pure-F\* XML well-formedness checks used by the RDF/XML parser.
   #200 PR5 / Issue #67 (2026-05-10).

   Migrates the byte-/codepoint-walking validation logic out of
   formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/
   67_rdfxml_validation.sh.

   What this module proves:
     - `is_valid_ncname` accepts exactly the codepoint sequences
       matching the XML 1.1 NCName production (NameStartChar (NameChar)*,
       where NameStartChar is NameStartChar minus ':').
     - The forbidden-name lists for RDF/XML node/property element
       positions (RDF/XML §7.2.11, §7.2.12) are constants here, not
       OCaml-side magic strings.
     - `check_conflicting_attrs_*` enforce the mutual-exclusion rules
       from RDF/XML §7.2.4..7.2.10.

   The OCaml glue patch (67_rdfxml_validation.sh) is reduced to the
   thinnest possible adapter: it converts the F\*-extracted
   `option string` return values into the raised
   `Rdfxml_error` exception that Parser_RDFXML.ml's call sites
   already expect.

   References:
     - https://www.w3.org/TR/xml-names/#NT-NCName
     - https://www.w3.org/TR/xml11/#NT-NameStartChar
     - https://www.w3.org/TR/rdf-syntax-grammar/#section-Syntax *)

open FStar.List.Tot

(* --- RDF namespace --------------------------------------------------- *)

let rdf_ns : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"

(* --- NCName validation (XML 1.1) ------------------------------------- *)

(* XML 1.1 NameStartChar minus ':' = NCName start character. *)
let is_name_start_char (cp : int) : Tot bool =
  (cp >= 0x41   && cp <= 0x5A)   ||                          (* A-Z *)
  cp =  0x5F                     ||                          (* _   *)
  (cp >= 0x61   && cp <= 0x7A)   ||                          (* a-z *)
  (cp >= 0xC0   && cp <= 0xD6)   ||
  (cp >= 0xD8   && cp <= 0xF6)   ||
  (cp >= 0xF8   && cp <= 0x2FF)  ||
  (cp >= 0x370  && cp <= 0x37D)  ||
  (cp >= 0x37F  && cp <= 0x1FFF) ||
  (cp >= 0x200C && cp <= 0x200D) ||
  (cp >= 0x2070 && cp <= 0x218F) ||
  (cp >= 0x2C00 && cp <= 0x2FEF) ||
  (cp >= 0x3001 && cp <= 0xD7FF) ||
  (cp >= 0xF900 && cp <= 0xFDCF) ||
  (cp >= 0xFDF0 && cp <= 0xFFFD) ||
  (cp >= 0x10000 && cp <= 0xEFFFF)

let is_name_char (cp : int) : Tot bool =
  is_name_start_char cp                            ||
  (cp >= 0x30   && cp <= 0x39)                     ||        (* 0-9 *)
  cp = 0x2D || cp = 0x2E                           ||        (* - .  *)
  cp = 0xB7                                        ||        (* middle dot *)
  (cp >= 0x0300 && cp <= 0x036F)                   ||        (* combining marks *)
  (cp >= 0x203F && cp <= 0x2040)

(* Walk the codepoint tail; every entry must be a NameChar. *)
let rec all_name_char (cps : list FStar.Char.char)
  : Tot bool (decreases cps)
  =
  match cps with
  | [] -> true
  | c :: rest ->
    if is_name_char (FStar.Char.int_of_char c)
    then all_name_char rest
    else false

(* is_valid_ncname s
     True iff [s], decoded as a codepoint sequence, matches the XML 1.1
     NCName production: a single NameStartChar followed by zero or more
     NameChar codepoints.
     Empty strings are rejected. *)
let is_valid_ncname (s : string) : Tot bool =
  match String.list_of_string s with
  | [] -> false
  | c :: rest ->
    if is_name_start_char (FStar.Char.int_of_char c)
    then all_name_char rest
    else false

(* --- Forbidden RDF/XML element names (RDF/XML §7.2.11/§7.2.12) ------- *)

(* Names forbidden as node element names. RDF/XML §7.2.11. *)
let forbidden_node_element_names : list string = [
  rdf_ns ^ "RDF";
  rdf_ns ^ "ID";
  rdf_ns ^ "about";
  rdf_ns ^ "bagID";
  rdf_ns ^ "parseType";
  rdf_ns ^ "resource";
  rdf_ns ^ "nodeID";
  rdf_ns ^ "li";
  rdf_ns ^ "aboutEach";
  rdf_ns ^ "aboutEachPrefix";
]

(* Names forbidden as property element names. RDF/XML §7.2.12. *)
let forbidden_property_element_names : list string = [
  rdf_ns ^ "Description";
  rdf_ns ^ "RDF";
  rdf_ns ^ "ID";
  rdf_ns ^ "about";
  rdf_ns ^ "bagID";
  rdf_ns ^ "parseType";
  rdf_ns ^ "resource";
  rdf_ns ^ "nodeID";
  rdf_ns ^ "aboutEach";
  rdf_ns ^ "aboutEachPrefix";
]

(* Membership helper. F*'s List.Tot.mem requires decidable equality on
   the element type; for `string` we use the structural-equality form. *)
let rec mem_string (x : string) (xs : list string) : Tot bool (decreases xs) =
  match xs with
  | [] -> false
  | y :: rest -> if x = y then true else mem_string x rest

let is_forbidden_node_element_name (full_iri : string) : Tot bool =
  mem_string full_iri forbidden_node_element_names

let is_forbidden_property_element_name (full_iri : string) : Tot bool =
  mem_string full_iri forbidden_property_element_names

(* --- rdf:ID / rdf:nodeID NCName check -------------------------------- *)

(* validate_rdf_id_attr attrs
     Walk the attribute list. If any attribute named "rdf:ID" or
     "rdf:nodeID" has a value that is not a valid NCName, return
     Some msg describing the failure. None means OK. *)
let rec validate_rdf_id_attr (attrs : list (string & string))
  : Tot (option string) (decreases attrs)
  =
  match attrs with
  | [] -> None
  | (name, value) :: rest ->
    if (name = "rdf:ID" || name = "rdf:nodeID") &&
       not (is_valid_ncname value)
    then Some (FStar.String.concat "" ["Invalid "; name; " value: "; value])
    else validate_rdf_id_attr rest

(* --- Conflicting-attribute checks ------------------------------------ *)

let rec has_attr (name : string) (attrs : list (string & string))
  : Tot bool (decreases attrs)
  =
  match attrs with
  | [] -> false
  | (n, _) :: rest -> if n = name then true else has_attr name rest

(* Common rules for both node and property elements. *)
let check_conflicting_attrs_common (attrs : list (string & string))
  : Tot (option string)
  =
  if has_attr "rdf:parseType" attrs && has_attr "rdf:resource" attrs then
    Some "conflicting rdf:parseType and rdf:resource"
  else if has_attr "rdf:aboutEach" attrs then
    Some "rdf:aboutEach is deprecated and forbidden"
  else if has_attr "rdf:aboutEachPrefix" attrs then
    Some "rdf:aboutEachPrefix is deprecated and forbidden"
  else if has_attr "rdf:bagID" attrs then
    Some "rdf:bagID is not supported in RDF 1.1"
  else if has_attr "rdf:li" attrs then
    Some "rdf:li may not be used as an attribute"
  else
    None

(* Node-element extra rules: rdf:ID / rdf:about / rdf:nodeID all
   identify the node itself, so any two together are contradictory. *)
let check_conflicting_attrs_node (attrs : list (string & string))
  : Tot (option string)
  =
  match check_conflicting_attrs_common attrs with
  | Some msg -> Some msg
  | None ->
    if has_attr "rdf:nodeID" attrs && has_attr "rdf:ID" attrs then
      Some "conflicting rdf:nodeID and rdf:ID on a node element"
    else if has_attr "rdf:nodeID" attrs && has_attr "rdf:about" attrs then
      Some "conflicting rdf:nodeID and rdf:about on a node element"
    else if has_attr "rdf:ID" attrs && has_attr "rdf:about" attrs then
      Some "conflicting rdf:ID and rdf:about on a node element"
    else
      None

(* Property-element rules: rdf:ID identifies the *statement* (for
   reification), so the only object-identifying conflict is
   rdf:nodeID + rdf:resource. *)
let check_conflicting_attrs_property (attrs : list (string & string))
  : Tot (option string)
  =
  match check_conflicting_attrs_common attrs with
  | Some msg -> Some msg
  | None ->
    if has_attr "rdf:nodeID" attrs && has_attr "rdf:resource" attrs then
      Some "conflicting rdf:nodeID and rdf:resource on a property element"
    else
      None
