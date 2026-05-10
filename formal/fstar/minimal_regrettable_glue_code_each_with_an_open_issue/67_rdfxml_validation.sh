#!/bin/bash
# Post-extraction patch: RDF/XML validation (NCName checks, forbidden names)
# Issue: https://github.com/danbri/factoidal/issues/67
#
# #200 PR5 (2026-05-10): the validation LOGIC has been moved to
# formal/fstar/XML.Wellformedness.fst (pure F\* — codepoint-aware
# NCName + RDF/XML §7.2.11/§7.2.12 forbidden-name lists +
# §7.2.4..7.2.10 mutual-exclusion rules).
#
# This patch is now a thin GLUE layer that:
#   - Defines the `Rdfxml_error` exception that Parser_RDFXML.ml's call
#     sites already raise.
#   - Adapts the OCaml `Parser_XML.xml_attribute list` into the F*
#     `(string * string) list` representation by `List.map`.
#   - Translates the F*-returned `option string` into the
#     `Rdfxml_error` exception the caller expects.
#   - Inserts validation calls at the two existing anchor points in
#     process_node_element / process_property_element.
#
# Per CLAUDE.md rule #11 corrected taxonomy: this patch is now in the
# `ASSUME-IO` class — pure raise-on-Some-msg adapter, no semantic
# logic. The byte-walking + UTF-8 decode + XML 1.1 NameChar /
# NameStartChar productions are all in the verified F\* module.

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

# 1. Add validation infrastructure after rdf_xmlliteral_iri.
#
# Body delegates to XML_Wellformedness (F*-extracted, formally
# verified). The OCaml side here is pure adapter glue: type
# conversion + raise-on-Some-msg.
if 'exception Rdfxml_error' not in content:
    content = content.replace(
        '''let rdf_xmlliteral_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral"
type rdfxml_state =''',
        '''let rdf_xmlliteral_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral"

(* RDF/XML validation: thin adapter over XML_Wellformedness.
   The validation LOGIC (NCName productions, forbidden-name lists,
   mutual-exclusion rules) lives in formal/fstar/XML.Wellformedness.fst
   under #200 PR5. This patch is rule-#11(a) glue only. *)
exception Rdfxml_error of string

let forbidden_node_element_names =
  XML_Wellformedness.forbidden_node_element_names

let forbidden_property_element_names =
  XML_Wellformedness.forbidden_property_element_names

let is_valid_ncname s =
  XML_Wellformedness.is_valid_ncname s

(* Convert the OCaml record-list to the F*-shaped (string * string)
   list. Pure byte-identical mapping. *)
let attrs_to_pairs (attrs : Parser_XML.xml_attribute list)
  : (Prims.string * Prims.string) list
  =
  List.map (fun (a : Parser_XML.xml_attribute) ->
    (a.attr_name, a.attr_value)) attrs

let validate_rdf_id_attr (attrs : Parser_XML.xml_attribute list) =
  match XML_Wellformedness.validate_rdf_id_attr (attrs_to_pairs attrs) with
  | FStar_Pervasives_Native.None -> ()
  | FStar_Pervasives_Native.Some msg -> raise (Rdfxml_error msg)

let check_conflicting_attrs (attrs : Parser_XML.xml_attribute list) =
  match XML_Wellformedness.check_conflicting_attrs_node
          (attrs_to_pairs attrs) with
  | FStar_Pervasives_Native.None -> ()
  | FStar_Pervasives_Native.Some msg -> raise (Rdfxml_error msg)

let check_conflicting_attrs_property (attrs : Parser_XML.xml_attribute list) =
  match XML_Wellformedness.check_conflicting_attrs_property
          (attrs_to_pairs attrs) with
  | FStar_Pervasives_Native.None -> ()
  | FStar_Pervasives_Native.Some msg -> raise (Rdfxml_error msg)

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

# 3. Add validation in process_property_element.
# Anchors on the first let binding inside the XElement match arm, which
# is stable across F* edits that introduce further local helpers
# (reif_iri_opt, reif_of) between st1 and the pred_iri resolution.
if 'Forbidden property element name' not in content:
    content = content.replace(
        '''     | Parser_XML.XElement (tag, attrs, children) ->
         let st1 = update_state_from_attrs st attrs in''',
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
         check_conflicting_attrs_property attrs;
         let st1 = update_state_from_attrs st attrs in''',
        1  # first occurrence only (process_property_element)
    )

with open(sys.argv[1], 'w') as f:
    f.write(content)
PYEOF

echo "  67_rdfxml_validation.sh applied."
