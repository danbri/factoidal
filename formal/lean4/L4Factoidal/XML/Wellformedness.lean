/-
L4Factoidal.XML.Wellformedness — the NCName production, and the
RDF/XML-specific name and attribute checks.

Port of `formal/fstar/XML.Wellformedness.fst` (F*) to Lean 4.

**Read the name carefully.** Despite the F* module's title, this is NOT
where generic XML well-formedness is decided. In XML there is no
separate validator pass: a document is well-formed exactly when the
parser accepts it, so the generic well-formedness constraints live in
`L4Factoidal.XML.Parser` — the header there lists all twenty of them.
What the F* `XML.Wellformedness` module actually holds is two things:

  1. the `[4] NCName` production of **Namespaces in XML**, which is
     `[5] Name` minus `:`; and
  2. the name and attribute constraints of **RDF/XML**, which belong to
     the RDF/XML layer above the XML parser, not to XML itself.

Both are ported here, keeping the F* module's scope exactly. The
RDF/XML half is included for completeness of the port and has no
consumer inside `L4Factoidal.XML`; an RDF/XML reader is the module that
would call it.

References:
  * `[4] NCName` — Namespaces in XML 1.0 (Third Edition) §3,
    https://www.w3.org/TR/xml-names/#NT-NCName
  * `[4] NameStartChar` / `[4a] NameChar` — XML 1.1,
    https://www.w3.org/TR/xml11/#NT-NameStartChar (the table the F*
    uses)
  * RDF/XML §7.2.4-§7.2.12 — RDF 1.1 XML Syntax, W3C Recommendation
    25 February 2014, https://www.w3.org/TR/rdf-syntax-grammar/
-/
import L4Factoidal.XML.Document

namespace L4Factoidal.XML

/-! ## `[4] NCName` — Namespaces in XML §3

`NCName ::= NameStartChar (NameChar)*`, where `NameStartChar` here
EXCLUDES `:`. That exclusion is the whole difference from XML 1.0's
`[5] Name`, which `L4Factoidal.XML.Document.isName` implements. -/

/-- An NCName start character: `[4] NameStartChar` minus `:`.
Port of F* `XML.Wellformedness.is_name_start_char` (which takes a
codepoint; this takes the `Char` that holds it). -/
def isNCNameStartChar (c : Char) : Bool :=
  isNameStartChar c && c != ':'

/-- An NCName character: `[4a] NameChar` minus `:`.
Port of F* `XML.Wellformedness.is_name_char`. -/
def isNCNameChar (c : Char) : Bool :=
  isNameChar c && c != ':'

/-- `[4] NCName ::= NameStartChar (NameChar)*` with `:` excluded
throughout. The empty string is rejected. Port of F*
`is_valid_ncname`. -/
def isValidNCName (str : String) : Bool :=
  match str.toList with
  | [] => false
  | c :: rest => isNCNameStartChar c && rest.all isNCNameChar

/-! ## RDF/XML name and attribute constraints

Everything below is RDF/XML's, not XML's. It is ported because the F*
module carries it; nothing in `L4Factoidal.XML` calls it. -/

/-- The RDF namespace name. -/
def rdfNs : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"

/-- Names forbidden in a node-element position — RDF/XML §7.2.11. -/
def forbiddenNodeElementNames : List String :=
  [ rdfNs ++ "RDF", rdfNs ++ "ID", rdfNs ++ "about", rdfNs ++ "bagID",
    rdfNs ++ "parseType", rdfNs ++ "resource", rdfNs ++ "nodeID",
    rdfNs ++ "li", rdfNs ++ "aboutEach", rdfNs ++ "aboutEachPrefix" ]

/-- Names forbidden in a property-element position — RDF/XML §7.2.12.
`rdf:Description` is forbidden here and `rdf:li` is not — the mirror
image of the node-element list. -/
def forbiddenPropertyElementNames : List String :=
  [ rdfNs ++ "Description", rdfNs ++ "RDF", rdfNs ++ "ID", rdfNs ++ "about",
    rdfNs ++ "bagID", rdfNs ++ "parseType", rdfNs ++ "resource",
    rdfNs ++ "nodeID", rdfNs ++ "aboutEach", rdfNs ++ "aboutEachPrefix" ]

/-- RDF/XML §7.2.11. Port of F* `is_forbidden_node_element_name`. -/
def isForbiddenNodeElementName (fullIri : String) : Bool :=
  forbiddenNodeElementNames.contains fullIri

/-- RDF/XML §7.2.12. Port of F* `is_forbidden_property_element_name`. -/
def isForbiddenPropertyElementName (fullIri : String) : Bool :=
  forbiddenPropertyElementNames.contains fullIri

/-- `rdf:ID` and `rdf:nodeID` values must be `[4] NCName`s. Returns a
message describing the first violation, or `none`. Port of F*
`validate_rdf_id_attr`. -/
def validateRdfIdAttr : List Attribute → Option String
  | [] => none
  | a :: rest =>
    if (a.name == "rdf:ID" || a.name == "rdf:nodeID") && !isValidNCName a.value then
      some s!"Invalid {a.name} value: {a.value}"
    else validateRdfIdAttr rest

/-- The mutual-exclusion rules common to node and property elements —
RDF/XML §7.2.4-§7.2.10. Port of F* `check_conflicting_attrs_common`. -/
def checkConflictingAttrsCommon (attrs : List Attribute) : Option String :=
  if hasAttr "rdf:parseType" attrs && hasAttr "rdf:resource" attrs then
    some "conflicting rdf:parseType and rdf:resource"
  else if hasAttr "rdf:aboutEach" attrs then
    some "rdf:aboutEach is deprecated and forbidden"
  else if hasAttr "rdf:aboutEachPrefix" attrs then
    some "rdf:aboutEachPrefix is deprecated and forbidden"
  else if hasAttr "rdf:bagID" attrs then
    some "rdf:bagID is not supported in RDF 1.1"
  else if hasAttr "rdf:li" attrs then
    some "rdf:li may not be used as an attribute"
  else none

/-- Node-element rules: `rdf:ID`, `rdf:about` and `rdf:nodeID` all
identify the node itself, so any two together contradict.
Port of F* `check_conflicting_attrs_node`. -/
def checkConflictingAttrsNode (attrs : List Attribute) : Option String :=
  match checkConflictingAttrsCommon attrs with
  | some msg => some msg
  | none =>
    if hasAttr "rdf:nodeID" attrs && hasAttr "rdf:ID" attrs then
      some "conflicting rdf:nodeID and rdf:ID on a node element"
    else if hasAttr "rdf:nodeID" attrs && hasAttr "rdf:about" attrs then
      some "conflicting rdf:nodeID and rdf:about on a node element"
    else if hasAttr "rdf:ID" attrs && hasAttr "rdf:about" attrs then
      some "conflicting rdf:ID and rdf:about on a node element"
    else none

/-- Property-element rules: here `rdf:ID` identifies the STATEMENT (for
reification), so the only object-identifying conflict is
`rdf:nodeID` with `rdf:resource`.
Port of F* `check_conflicting_attrs_property`. -/
def checkConflictingAttrsProperty (attrs : List Attribute) : Option String :=
  match checkConflictingAttrsCommon attrs with
  | some msg => some msg
  | none =>
    if hasAttr "rdf:nodeID" attrs && hasAttr "rdf:resource" attrs then
      some "conflicting rdf:nodeID and rdf:resource on a property element"
    else none

end L4Factoidal.XML
