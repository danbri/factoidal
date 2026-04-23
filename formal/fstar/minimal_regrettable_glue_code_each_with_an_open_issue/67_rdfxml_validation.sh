#!/bin/bash
# Post-extraction patch: RDF/XML validation (NCName checks, forbidden names)
# Issue: https://github.com/danbri/factoidal/issues/67
#
# Patches Parser_RDFXML.ml with:
#   - Rdfxml_error exception and forbidden name lists
#   - is_valid_ncname, validate_rdf_id_attr, check_conflicting_attrs
#   - Validation calls in process_node_element
#   - Validation calls in process_property_element

set -euo pipefail

OUTDIR="$1"

FILE="$OUTDIR/Parser_RDFXML.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Skipping 67_rdfxml_validation.sh: $FILE not found" >&2
  exit 0
fi

echo "  Applying 67_rdfxml_validation.sh to $FILE..."

python3 - "$FILE" << 'PYEOF'
import sys

with open(sys.argv[1], 'r') as f:
    content = f.read()

# 1. Add validation infrastructure after rdf_xmlliteral_iri
if 'exception Rdfxml_error' not in content:
    content = content.replace(
        '''let rdf_xmlliteral_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral"
type rdfxml_state =''',
        '''let rdf_xmlliteral_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral"

(* RDF/XML validation: forbidden rdf: names *)
exception Rdfxml_error of string

(* Names forbidden as node element names (sec 7.2.11) *)
let forbidden_node_element_names = [
  rdf_ns ^ "RDF"; rdf_ns ^ "ID"; rdf_ns ^ "about"; rdf_ns ^ "bagID";
  rdf_ns ^ "parseType"; rdf_ns ^ "resource"; rdf_ns ^ "nodeID";
  rdf_ns ^ "li"; rdf_ns ^ "aboutEach"; rdf_ns ^ "aboutEachPrefix"
]

(* Names forbidden as property element names (sec 7.2.12) *)
let forbidden_property_element_names = [
  rdf_ns ^ "Description"; rdf_ns ^ "RDF"; rdf_ns ^ "ID"; rdf_ns ^ "about";
  rdf_ns ^ "bagID"; rdf_ns ^ "parseType"; rdf_ns ^ "resource";
  rdf_ns ^ "nodeID"; rdf_ns ^ "aboutEach"; rdf_ns ^ "aboutEachPrefix"
]

(* Validate rdf:ID / rdf:nodeID values: must be valid XML NCName.
   Now codepoint-aware: decodes UTF-8 and checks against XML 1.1
   NameStartChar / NameChar productions. Previously we approximated
   by treating every byte >= 0x80 as a valid start, which incorrectly
   accepted e.g. a leading U+0301 (combining acute — `&#x301;`).
   Reference: https://www.w3.org/TR/xml-names/#NT-NCName

   Uses Stdlib operators explicitly because open Prims shadows them with Z.t. *)
let is_valid_ncname s =
  let module S = Stdlib in
  let len = S.String.length s in
  if S.(=) len 0 then false
  else
    let byte_at i = S.Char.code (S.String.get s i) in
    (* Decode one UTF-8 codepoint starting at byte i.
       Returns (cp, bytes_consumed). Returns (-1, 1) on malformed bytes. *)
    let decode_cp i =
      let band a b = Stdlib.(land) a b in
      let bor a b = Stdlib.(lor) a b in
      let bshl a n = Stdlib.(lsl) a n in
      let b0 = byte_at i in
      if S.(<) b0 0x80 then (b0, 1)
      else if S.(<) b0 0xC0 then (-1, 1)
      else if S.(<) b0 0xE0 && S.(<) (S.(+) i 1) len then
        let b1 = byte_at (S.(+) i 1) in
        (bor (bshl (band b0 0x1F) 6) (band b1 0x3F), 2)
      else if S.(<) b0 0xF0 && S.(<) (S.(+) i 2) len then
        let b1 = byte_at (S.(+) i 1) in
        let b2 = byte_at (S.(+) i 2) in
        (bor (bor (bshl (band b0 0x0F) 12)
                  (bshl (band b1 0x3F) 6))
             (band b2 0x3F), 3)
      else if S.(<) b0 0xF8 && S.(<) (S.(+) i 3) len then
        let b1 = byte_at (S.(+) i 1) in
        let b2 = byte_at (S.(+) i 2) in
        let b3 = byte_at (S.(+) i 3) in
        (bor (bor (bor (bshl (band b0 0x07) 18)
                       (bshl (band b1 0x3F) 12))
                  (bshl (band b2 0x3F) 6))
             (band b3 0x3F), 4)
      else (-1, 1)
    in
    (* XML 1.1 NameStartChar minus ':' (= NCName start char). *)
    let is_name_start_char cp =
      (S.(>=) cp 0x41 && S.(<=) cp 0x5A) ||                (* A-Z *)
      S.(=) cp 0x5F ||                                      (* _   *)
      (S.(>=) cp 0x61 && S.(<=) cp 0x7A) ||                (* a-z *)
      (S.(>=) cp 0xC0 && S.(<=) cp 0xD6) ||
      (S.(>=) cp 0xD8 && S.(<=) cp 0xF6) ||
      (S.(>=) cp 0xF8 && S.(<=) cp 0x2FF) ||
      (S.(>=) cp 0x370 && S.(<=) cp 0x37D) ||
      (S.(>=) cp 0x37F && S.(<=) cp 0x1FFF) ||
      (S.(>=) cp 0x200C && S.(<=) cp 0x200D) ||
      (S.(>=) cp 0x2070 && S.(<=) cp 0x218F) ||
      (S.(>=) cp 0x2C00 && S.(<=) cp 0x2FEF) ||
      (S.(>=) cp 0x3001 && S.(<=) cp 0xD7FF) ||
      (S.(>=) cp 0xF900 && S.(<=) cp 0xFDCF) ||
      (S.(>=) cp 0xFDF0 && S.(<=) cp 0xFFFD) ||
      (S.(>=) cp 0x10000 && S.(<=) cp 0xEFFFF)
    in
    let is_name_char cp =
      is_name_start_char cp ||
      (S.(>=) cp 0x30 && S.(<=) cp 0x39) ||                (* 0-9 *)
      S.(=) cp 0x2D || S.(=) cp 0x2E ||                    (* - . *)
      S.(=) cp 0xB7 ||                                      (* middle dot *)
      (S.(>=) cp 0x0300 && S.(<=) cp 0x036F) ||            (* combining marks *)
      (S.(>=) cp 0x203F && S.(<=) cp 0x2040)
    in
    let (cp0, n0) = decode_cp 0 in
    if not (is_name_start_char cp0) then false
    else
      let ok = S.ref true in
      let i = S.ref n0 in
      while S.(&&) (S.(!) ok) (S.(<) (S.(!) i) len) do
        let (cp, n) = decode_cp (S.(!) i) in
        if not (is_name_char cp) then ok := false;
        i := S.(+) (S.(!) i) n
      done;
      S.(!) ok

let validate_rdf_id_attr (attrs : Parser_XML.xml_attribute list) =
  List.iter (fun (a : Parser_XML.xml_attribute) ->
    if a.attr_name = "rdf:ID" || a.attr_name = "rdf:nodeID" then
      if not (is_valid_ncname a.attr_value) then
        raise (Rdfxml_error (Printf.sprintf "Invalid %s value: %s" a.attr_name a.attr_value))
  ) attrs

let check_conflicting_attrs (attrs : Parser_XML.xml_attribute list) =
  let has a = List.exists (fun (x : Parser_XML.xml_attribute) -> x.attr_name = a) attrs in
  if has "rdf:parseType" && has "rdf:resource" then
    raise (Rdfxml_error "conflicting rdf:parseType and rdf:resource");
  if has "rdf:aboutEach" then
    raise (Rdfxml_error "rdf:aboutEach is deprecated and forbidden");
  if has "rdf:aboutEachPrefix" then
    raise (Rdfxml_error "rdf:aboutEachPrefix is deprecated and forbidden");
  (* rdf:bagID was removed in RDF 1.1 (§18 of the Concepts spec).
     Accept as an explicit error; error006/error007 exercise this. *)
  if has "rdf:bagID" then
    raise (Rdfxml_error "rdf:bagID is not supported in RDF 1.1");
  (* Mutual exclusion rules per RDF/XML §7: a single element cannot
     identify itself with more than one of rdf:ID / rdf:about / rdf:nodeID,
     and a property element cannot pair rdf:nodeID with rdf:resource.
     These cover syntax-incomplete error004/005/006. *)
  if has "rdf:nodeID" && has "rdf:ID" then
    raise (Rdfxml_error "conflicting rdf:nodeID and rdf:ID");
  if has "rdf:nodeID" && has "rdf:about" then
    raise (Rdfxml_error "conflicting rdf:nodeID and rdf:about");
  if has "rdf:nodeID" && has "rdf:resource" then
    raise (Rdfxml_error "conflicting rdf:nodeID and rdf:resource");
  if has "rdf:ID" && has "rdf:about" then
    raise (Rdfxml_error "conflicting rdf:ID and rdf:about");
  (* rdf:li is an element name, never an attribute. Covers
     rdf-containers-syntax-vs-schema-error001. *)
  if has "rdf:li" then
    raise (Rdfxml_error "rdf:li may not be used as an attribute")

type rdfxml_state ='''
    )

# 2. Add validation in process_node_element
if 'Forbidden node element name' not in content:
    content = content.replace(
        '''     | Parser_XML.XElement (tag, attrs, children) ->
         let st1 = update_state_from_attrs st attrs in
         let uu___1 = determine_subject st1 attrs in
         (match uu___1 with''',
        '''     | Parser_XML.XElement (tag, attrs, children) ->
         (* Validate: reject forbidden rdf: names as node elements *)
         (match resolve_name st tag with
          | Some full_iri ->
            if List.mem full_iri forbidden_node_element_names then
              raise (Rdfxml_error (Printf.sprintf "Forbidden node element name: %s" full_iri))
          | None -> ());
         validate_rdf_id_attr attrs;
         check_conflicting_attrs attrs;
         let st1 = update_state_from_attrs st attrs in
         let uu___1 = determine_subject st1 attrs in
         (match uu___1 with''',
        1  # first occurrence only (process_node_element)
    )

# 3. Add validation in process_property_element
if 'Forbidden property element name' not in content:
    content = content.replace(
        '''     | Parser_XML.XElement (tag, attrs, children) ->
         let st1 = update_state_from_attrs st attrs in
         let uu___1 =
           match resolve_name st1 tag with''',
        '''     | Parser_XML.XElement (tag, attrs, children) ->
         (* Validate: reject forbidden rdf: names as property elements *)
         (match resolve_name st tag with
          | Some full_iri ->
            if List.mem full_iri forbidden_property_element_names then
              raise (Rdfxml_error (Printf.sprintf "Forbidden property element name: %s" full_iri));
            (* rdf:Bag/Seq/Alt ARE legal as property element names per
               RDF/XML §7.2.2.1 — they are just IRIs in the rdf: namespace
               when used as predicates. The guard that used to reject them
               here failed tests rdfms-rdf-names-use-test-017/018/019. *)
            ()
          | None -> ());
         validate_rdf_id_attr attrs;
         check_conflicting_attrs attrs;
         let st1 = update_state_from_attrs st attrs in
         let uu___1 =
           match resolve_name st1 tag with'''
    )

with open(sys.argv[1], 'w') as f:
    f.write(content)
PYEOF

echo "  67_rdfxml_validation.sh applied."
