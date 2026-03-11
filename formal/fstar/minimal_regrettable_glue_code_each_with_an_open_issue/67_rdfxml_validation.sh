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
   Uses Stdlib operators explicitly because open Prims shadows them with Z.t. *)
let is_valid_ncname s =
  let module S = Stdlib in
  let len = S.String.length s in
  if S.(=) len 0 then false
  else
    let byte_at i = S.Char.code (S.String.get s i) in
    let is_start b =
      (S.(>=) b 0x41 && S.(<=) b 0x5A) || (S.(>=) b 0x61 && S.(<=) b 0x7A)
      || S.(=) b 0x5F || S.(>) b 0x7F in
    let is_cont b =
      is_start b || (S.(>=) b 0x30 && S.(<=) b 0x39)
      || S.(=) b 0x2D || S.(=) b 0x2E || S.(=) b 0xB7 in
    let ok = S.ref (is_start (byte_at 0)) in
    for i = 1 to S.(-) len 1 do
      if not (is_cont (byte_at i)) then ok := false
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
    raise (Rdfxml_error "rdf:aboutEach is deprecated and forbidden")

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
            (* Also reject rdf:Bag/Seq/Alt as property elements *)
            if full_iri = rdf_ns ^ "Bag" || full_iri = rdf_ns ^ "Seq" ||
               full_iri = rdf_ns ^ "Alt" then
              raise (Rdfxml_error (Printf.sprintf "Container type used as property element: %s" full_iri))
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
