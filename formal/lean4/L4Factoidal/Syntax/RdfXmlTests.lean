/-
L4Factoidal.Syntax.RdfXmlTests — build-time guards for the RDF/XML
grammar walk, one per §7.2 production plus the negative cases the W3C
`rdf-xml` suite exercises.

Every `#guard` evaluates during elaboration, so a wrong answer is a
BUILD error, not a silent regression (see `skills/factoidal-lean-basics`).
Production numbers cite **RDF 1.1 XML Syntax**,
https://www.w3.org/TR/rdf-syntax-grammar/ .

Expected graphs are written as N-Triples and compared up to blank-node
renaming (`RDF.Graph.isomorphic?`, RDF 1.1 Concepts §3.6), so these
guards do not depend on the port's blank-node labelling scheme.

Attribute values use SINGLE quotes throughout — legal per XML `[10]
AttValue` — so the Lean string literals stay readable.
-/
import L4Factoidal.Syntax.RdfXml
import L4Factoidal.Syntax.NTriples
import L4Factoidal.RDF.Isomorphism

namespace L4Factoidal.Syntax.RdfXmlTests

open L4Factoidal.RDF
open L4Factoidal.Syntax

/-! ## Fixtures -/

/-- The retrieval IRI every guard below resolves against. -/
def base : String := "http://example.org/dir/doc.rdf"

/-- An `rdf:RDF` document element declaring `rdf:` and `eg:`. -/
def hdr : String :=
  "<rdf:RDF xmlns:rdf='http://www.w3.org/1999/02/22-rdf-syntax-ns#'"
    ++ " xmlns:eg='http://example.org/'>"

def ftr : String := "</rdf:RDF>"

/-- Wrap a body in the standard document element. -/
def doc (body : String) : String := hdr ++ body ++ ftr

/-- The graph `body` denotes, up to blank-node renaming, equals the
graph the N-Triples `nt` denotes. -/
def iso (body nt : String) : Bool :=
  match RdfXml.parseRdfXml (doc body) (some base), parseNTriples nt with
  | .ok g, .ok e => Graph.isomorphic? g e
  | _, _         => false

/-- As `iso`, but the RDF/XML is a whole document (no `rdf:RDF` wrapper
supplied). -/
def isoDoc (whole nt : String) : Bool :=
  match RdfXml.parseRdfXml whole (some base), parseNTriples nt with
  | .ok g, .ok e => Graph.isomorphic? g e
  | _, _         => false

/-- The parser REJECTS this body — a §7.2 rule violation. -/
def rejects (body : String) : Bool :=
  (RdfXml.parseRdfXml (doc body) (some base)).toOption.isNone

/-- The parser rejects this whole document. -/
def rejectsDoc (whole : String) : Bool :=
  (RdfXml.parseRdfXml whole (some base)).toOption.isNone

/-- The parser accepts this body. -/
def accepts (body : String) : Bool :=
  (RdfXml.parseRdfXml (doc body) (some base)).toOption.isSome

/-- How many triples the body denotes. -/
def count (body : String) : Nat :=
  match RdfXml.parseRdfXml (doc body) (some base) with
  | .ok g    => g.length
  | .error _ => 0

/-- The lexical form of the single literal object the body denotes —
used to inspect `[7.2.17]` canonicalisation directly. -/
def soleLiteralLex (body : String) : Option String :=
  match RdfXml.parseRdfXml (doc body) (some base) with
  | .ok [t] => match t.o with
               | .literal l => some l.val.lexicalForm
               | _          => none
  | _ => none

/-! ## `[7.2.2] doc` and `[7.2.8] RDF` -/

-- [7.2.8] RDF: an empty `rdf:RDF` denotes the empty graph.
#guard count "" == 0

-- [7.2.8] RDF: whitespace, comments and processing instructions between
-- node elements contribute nothing.
#guard count "  <!-- c --> <?pi d?>  " == 0

-- [7.2.2] doc: the `rdf:RDF` wrapper is OPTIONAL — a lone node element
-- is a whole document.
#guard isoDoc
  ("<eg:Thing xmlns:eg='http://example.org/' "
    ++ "xmlns:rdf='http://www.w3.org/1999/02/22-rdf-syntax-ns#' "
    ++ "rdf:about='http://example.org/s'/>")
  "<http://example.org/s> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.org/Thing> ."

-- [7.2.2] doc: an `rdf:RDF`-less document element with no identifying
-- attribute is still a node element — of a blank node.
#guard isoDoc
  ("<eg:Thing xmlns:eg='http://example.org/' "
    ++ "xmlns:rdf='http://www.w3.org/1999/02/22-rdf-syntax-ns#'><eg:p>v</eg:p></eg:Thing>")
  ("_:x <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.org/Thing> .\n"
    ++ "_:x <http://example.org/p> \"v\" .")

/-! ## `[7.2.9] nodeElementList` and `[7.2.11] nodeElement` -/

-- [7.2.9] nodeElementList: sibling node elements each contribute.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/a'><eg:p>1</eg:p></rdf:Description>"
    ++ "<rdf:Description rdf:about='http://example.org/b'><eg:p>2</eg:p></rdf:Description>")
  ("<http://example.org/a> <http://example.org/p> \"1\" .\n"
    ++ "<http://example.org/b> <http://example.org/p> \"2\" .")

-- [7.2.11] nodeElement: `rdf:Description` contributes no type triple.
#guard iso
  "<rdf:Description rdf:about='http://example.org/s'><eg:p>v</eg:p></rdf:Description>"
  "<http://example.org/s> <http://example.org/p> \"v\" ."

-- [7.2.11] nodeElement: a TYPED node element implies `rdf:type`.
#guard iso
  "<eg:Thing rdf:about='http://example.org/s'/>"
  "<http://example.org/s> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.org/Thing> ."

-- [7.2.11] nodeElement: no identifying attribute at all denotes a fresh
-- blank node, and the in-scope base never enters its label.
#guard iso
  "<rdf:Description><eg:p>v</eg:p></rdf:Description>"
  "_:x <http://example.org/p> \"v\" ."

-- [7.2.11] nodeElement: two attribute-less node elements are two
-- DISTINCT blank nodes.
#guard iso
  ("<rdf:Description><eg:p>v</eg:p></rdf:Description>"
    ++ "<rdf:Description><eg:p>v</eg:p></rdf:Description>")
  ("_:x <http://example.org/p> \"v\" .\n_:y <http://example.org/p> \"v\" .")

/-! ## `[7.2.13] propertyEltList` / `[7.2.14] propertyElt` -/

-- [7.2.13] propertyEltList: several property elements on one subject.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p>1</eg:p><eg:q>2</eg:q></rdf:Description>")
  ("<http://example.org/s> <http://example.org/p> \"1\" .\n"
    ++ "<http://example.org/s> <http://example.org/q> \"2\" .")

-- [7.2.13] propertyEltList: a repeated predicate gives two triples.
#guard count
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p>1</eg:p><eg:p>2</eg:p></rdf:Description>") == 2

/-! ## `[7.2.15] resourcePropertyElt` -/

-- [7.2.15]: the nested node element's subject becomes the object.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/s'><eg:p>"
    ++ "<rdf:Description rdf:about='http://example.org/o'/></eg:p></rdf:Description>")
  "<http://example.org/s> <http://example.org/p> <http://example.org/o> ."

-- [7.2.15]: the nested node element's OWN triples are emitted too.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/s'><eg:p>"
    ++ "<eg:Thing rdf:about='http://example.org/o'><eg:q>v</eg:q></eg:Thing>"
    ++ "</eg:p></rdf:Description>")
  ("<http://example.org/s> <http://example.org/p> <http://example.org/o> .\n"
    ++ "<http://example.org/o> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.org/Thing> .\n"
    ++ "<http://example.org/o> <http://example.org/q> \"v\" .")

-- [7.2.15]: TWO node elements inside one property element match no
-- production.
#guard rejects
  ("<rdf:Description rdf:about='http://example.org/s'><eg:p>"
    ++ "<rdf:Description/><rdf:Description/></eg:p></rdf:Description>")

/-! ## `[7.2.16] literalPropertyElt` -/

-- [7.2.16]: text content with no datatype is an `xsd:string`.
#guard iso
  "<rdf:Description rdf:about='http://example.org/s'><eg:p>v</eg:p></rdf:Description>"
  "<http://example.org/s> <http://example.org/p> \"v\"^^<http://www.w3.org/2001/XMLSchema#string> ."

-- [7.2.16] + [7.2.28] datatypeAttr: an absolute datatype IRI.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:datatype='http://www.w3.org/2001/XMLSchema#integer'>42</eg:p>"
    ++ "</rdf:Description>")
  "<http://example.org/s> <http://example.org/p> \"42\"^^<http://www.w3.org/2001/XMLSchema#integer> ."

-- [7.2.28] datatypeAttr: a RELATIVE datatype reference resolves against
-- the in-scope base.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:datatype='dt'>x</eg:p></rdf:Description>")
  "<http://example.org/s> <http://example.org/p> \"x\"^^<http://example.org/dir/dt> ."

-- [7.2.16]: CDATA is character data, and contributes its content.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p><![CDATA[a<b]]></eg:p></rdf:Description>")
  "<http://example.org/s> <http://example.org/p> \"a<b\" ."

-- [7.2.16]: `rdf:langString` cannot be named as a datatype — it needs a
-- language tag, which `rdf:datatype` cannot supply.
#guard rejects
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:datatype='http://www.w3.org/1999/02/22-rdf-syntax-ns#langString'>x</eg:p>"
    ++ "</rdf:Description>")

/-! ## `xml:lang` — XML §2.12, RDF/XML §6.1.5 -/

-- A language in scope makes the literal an `rdf:langString`.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/s' xml:lang='en'>"
    ++ "<eg:p>v</eg:p></rdf:Description>")
  "<http://example.org/s> <http://example.org/p> \"v\"@en ."

-- `xml:lang` INHERITS: a property element without one takes the node
-- element's.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/s' xml:lang='fr'>"
    ++ "<eg:p>v</eg:p><eg:q xml:lang='de'>w</eg:q></rdf:Description>")
  ("<http://example.org/s> <http://example.org/p> \"v\"@fr .\n"
    ++ "<http://example.org/s> <http://example.org/q> \"w\"@de .")

-- `xml:lang=""` CLEARS the inherited language rather than setting one.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/s' xml:lang='en'>"
    ++ "<eg:p xml:lang=''>v</eg:p></rdf:Description>")
  "<http://example.org/s> <http://example.org/p> \"v\" ."

-- A language does NOT survive out of the element that declared it: the
-- second node element is unaffected.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/a' xml:lang='en'><eg:p>v</eg:p></rdf:Description>"
    ++ "<rdf:Description rdf:about='http://example.org/b'><eg:p>v</eg:p></rdf:Description>")
  ("<http://example.org/a> <http://example.org/p> \"v\"@en .\n"
    ++ "<http://example.org/b> <http://example.org/p> \"v\" .")

-- A language tag never applies to a DATATYPED literal (§7.2.16).
#guard iso
  ("<rdf:Description rdf:about='http://example.org/s' xml:lang='en'>"
    ++ "<eg:p rdf:datatype='http://www.w3.org/2001/XMLSchema#integer'>1</eg:p></rdf:Description>")
  "<http://example.org/s> <http://example.org/p> \"1\"^^<http://www.w3.org/2001/XMLSchema#integer> ."

/-! ## `[7.2.17] parseTypeLiteralPropertyElt` and `[7.2.20] parseTypeOtherPropertyElt` -/

-- [7.2.17]: text-only content is the lexical form verbatim.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:parseType='Literal'>text</eg:p></rdf:Description>")
  ("<http://example.org/s> <http://example.org/p> \"text\""
    ++ "^^<http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral> .")

-- [7.2.17]: an empty element is written open+close, and the ambient
-- namespace declarations land on the top-level element of the content.
#guard soleLiteralLex
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:parseType='Literal'><br/></eg:p></rdf:Description>")
  == some ("<br xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\""
            ++ " xmlns:eg=\"http://example.org/\"></br>")

-- [7.2.17]: markup-significant characters in character data are escaped.
#guard soleLiteralLex
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:parseType='Literal'>a &amp; b</eg:p></rdf:Description>")
  == some "a &amp; b"

-- [7.2.17]: nested elements keep their structure; only the TOP-level
-- element carries the ambient declarations.
#guard soleLiteralLex
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:parseType='Literal'><a><b>x</b></a></eg:p></rdf:Description>")
  == some ("<a xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\""
            ++ " xmlns:eg=\"http://example.org/\"><b>x</b></a>")

-- [7.2.20] parseTypeOtherPropertyElt: any other `rdf:parseType` value is
-- treated as if it were `Literal`.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:parseType='Other'>text</eg:p></rdf:Description>")
  ("<http://example.org/s> <http://example.org/p> \"text\""
    ++ "^^<http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral> .")

/-! ## `[7.2.18] parseTypeResourcePropertyElt` -/

-- [7.2.18]: the object is a fresh blank node, and the content is that
-- node's property element list.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:parseType='Resource'><eg:q>v</eg:q></eg:p></rdf:Description>")
  ("<http://example.org/s> <http://example.org/p> _:x .\n"
    ++ "_:x <http://example.org/q> \"v\" .")

-- [7.2.18]: empty `parseType='Resource'` content still makes the node.
#guard count
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:parseType='Resource'/></rdf:Description>") == 1

/-! ## `[7.2.19] parseTypeCollectionPropertyElt` -/

-- [7.2.19]: an EMPTY collection is `rdf:nil`.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:parseType='Collection'/></rdf:Description>")
  ("<http://example.org/s> <http://example.org/p> "
    ++ "<http://www.w3.org/1999/02/22-rdf-syntax-ns#nil> .")

-- [7.2.19]: one item.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:parseType='Collection'>"
    ++ "<rdf:Description rdf:about='http://example.org/a'/></eg:p></rdf:Description>")
  ("<http://example.org/s> <http://example.org/p> _:c1 .\n"
    ++ "_:c1 <http://www.w3.org/1999/02/22-rdf-syntax-ns#first> <http://example.org/a> .\n"
    ++ "_:c1 <http://www.w3.org/1999/02/22-rdf-syntax-ns#rest> "
    ++ "<http://www.w3.org/1999/02/22-rdf-syntax-ns#nil> .")

-- [7.2.19]: two items chain through `rdf:rest`.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:parseType='Collection'>"
    ++ "<rdf:Description rdf:about='http://example.org/a'/>"
    ++ "<rdf:Description rdf:about='http://example.org/b'/></eg:p></rdf:Description>")
  ("<http://example.org/s> <http://example.org/p> _:c1 .\n"
    ++ "_:c1 <http://www.w3.org/1999/02/22-rdf-syntax-ns#first> <http://example.org/a> .\n"
    ++ "_:c1 <http://www.w3.org/1999/02/22-rdf-syntax-ns#rest> _:c2 .\n"
    ++ "_:c2 <http://www.w3.org/1999/02/22-rdf-syntax-ns#first> <http://example.org/b> .\n"
    ++ "_:c2 <http://www.w3.org/1999/02/22-rdf-syntax-ns#rest> "
    ++ "<http://www.w3.org/1999/02/22-rdf-syntax-ns#nil> .")

-- [7.2.19]: a collection item's own triples are emitted.
#guard count
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:parseType='Collection'>"
    ++ "<eg:Thing rdf:about='http://example.org/a'/></eg:p></rdf:Description>") == 4

/-! ## `[7.2.21] emptyPropertyElt` -/

-- [7.2.21]: no content, no attributes — the empty `xsd:string`.
#guard iso
  "<rdf:Description rdf:about='http://example.org/s'><eg:p/></rdf:Description>"
  "<http://example.org/s> <http://example.org/p> \"\" ."

-- [7.2.21]: the empty literal still picks up the in-scope language.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/s' xml:lang='en'>"
    ++ "<eg:p/></rdf:Description>")
  "<http://example.org/s> <http://example.org/p> \"\"@en ."

-- [7.2.21] + [7.2.31] resourceAttr: an absolute `rdf:resource`.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:resource='http://example.org/o'/></rdf:Description>")
  "<http://example.org/s> <http://example.org/p> <http://example.org/o> ."

-- [7.2.31] resourceAttr: a RELATIVE `rdf:resource` resolves against the
-- in-scope base.
#guard iso
  "<rdf:Description rdf:about='http://example.org/s'><eg:p rdf:resource='o'/></rdf:Description>"
  "<http://example.org/s> <http://example.org/p> <http://example.org/dir/o> ."

-- [7.2.21] + [7.2.24] nodeIdAttr: `rdf:nodeID` as the OBJECT.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:nodeID='n1'/></rdf:Description>"
    ++ "<rdf:Description rdf:nodeID='n1'><eg:q>v</eg:q></rdf:Description>")
  ("<http://example.org/s> <http://example.org/p> _:x .\n"
    ++ "_:x <http://example.org/q> \"v\" .")

-- [7.2.21]: property attributes on an empty property element describe a
-- FRESH blank node.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p eg:q='v'/></rdf:Description>")
  ("<http://example.org/s> <http://example.org/p> _:x .\n"
    ++ "_:x <http://example.org/q> \"v\" .")

-- [7.2.21]: property attributes alongside `rdf:resource` describe THAT
-- resource, not a new node.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:resource='http://example.org/o' eg:q='v'/></rdf:Description>")
  ("<http://example.org/s> <http://example.org/p> <http://example.org/o> .\n"
    ++ "<http://example.org/o> <http://example.org/q> \"v\" .")

/-! ## `[7.2.23] idAttr` -/

-- [7.2.23]: `rdf:ID` names `base#id`.
#guard iso
  "<rdf:Description rdf:ID='foo'><eg:p>v</eg:p></rdf:Description>"
  "<http://example.org/dir/doc.rdf#foo> <http://example.org/p> \"v\" ."

-- [7.2.23] constraint: the same `rdf:ID` twice under one base is an error.
#guard rejects "<rdf:Description rdf:ID='foo'/><rdf:Description rdf:ID='foo'/>"

-- [7.2.23]: the same `rdf:ID` under DIFFERENT `xml:base` values is fine.
#guard accepts
  ("<rdf:Description rdf:ID='foo'/>"
    ++ "<rdf:Description xml:base='http://other.example/' rdf:ID='foo'/>")

-- [7.2.23]: the value must be an XML `NCName` — a leading digit is not.
#guard rejects "<rdf:Description rdf:ID='333-555-666'/>"

-- [7.2.23]: an `NCName` may not contain a colon.
#guard rejects "<rdf:Description rdf:ID='a:b'/>"

/-! ## `[7.2.24] nodeIdAttr` -/

-- [7.2.24]: two node elements with the same `rdf:nodeID` are ONE node.
#guard iso
  ("<rdf:Description rdf:nodeID='n'><eg:p>1</eg:p></rdf:Description>"
    ++ "<rdf:Description rdf:nodeID='n'><eg:q>2</eg:q></rdf:Description>")
  ("_:x <http://example.org/p> \"1\" .\n_:x <http://example.org/q> \"2\" .")

-- [7.2.24]: the value must be an `NCName`.
#guard rejects "<rdf:Description rdf:nodeID='9bad'/>"

/-! ## `[7.2.25] aboutAttr` and XML Base -/

-- [7.2.25]: a relative `rdf:about` resolves against the retrieval IRI.
#guard iso
  "<rdf:Description rdf:about='s'><eg:p>v</eg:p></rdf:Description>"
  "<http://example.org/dir/s> <http://example.org/p> \"v\" ."

-- [7.2.25]: `rdf:about=''` is RFC 3986 §4.4's same-document reference.
#guard iso
  "<rdf:Description rdf:about=''><eg:p>v</eg:p></rdf:Description>"
  "<http://example.org/dir/doc.rdf> <http://example.org/p> \"v\" ."

-- [7.2.25]: a dot-segment reference goes through RFC 3986 §5.2.4.
#guard iso
  "<rdf:Description rdf:about='../up'><eg:p>v</eg:p></rdf:Description>"
  "<http://example.org/up> <http://example.org/p> \"v\" ."

-- XML Base §3: `xml:base` retargets the resolution for the element and
-- its descendants.
#guard iso
  ("<rdf:Description xml:base='http://other.example/x/' rdf:about='s'>"
    ++ "<eg:p>v</eg:p></rdf:Description>")
  "<http://other.example/x/s> <http://example.org/p> \"v\" ."

-- XML Base §3.3 / RFC 3986 §5.1: a FRAGMENT on `xml:base` is discarded
-- before the base is used.
#guard iso
  ("<rdf:Description xml:base='http://other.example/x/file#frag' rdf:about='#f'>"
    ++ "<eg:p>v</eg:p></rdf:Description>")
  "<http://other.example/x/file#f> <http://example.org/p> \"v\" ."

-- XML Base: an `xml:base` does NOT leak to a sibling node element.
#guard iso
  ("<rdf:Description xml:base='http://other.example/' rdf:about='a'/>"
    ++ "<rdf:Description rdf:about='b'><eg:p>v</eg:p></rdf:Description>")
  "<http://example.org/dir/b> <http://example.org/p> \"v\" ."

-- XML Base: nested `xml:base` values compose (RFC 3986 §5.2).
#guard iso
  ("<rdf:Description xml:base='http://other.example/x/' rdf:about='s'>"
    ++ "<eg:p rdf:resource='y/o' xml:base='http://other.example/x/deep/'/></rdf:Description>")
  "<http://other.example/x/s> <http://example.org/p> <http://other.example/x/deep/y/o> ."

/-! ## `[7.2.26] propertyAttr` -/

-- [7.2.26]: an attribute in a non-RDF namespace licenses a literal
-- triple on the node element's subject.
#guard iso
  "<rdf:Description rdf:about='http://example.org/s' eg:p='v'/>"
  "<http://example.org/s> <http://example.org/p> \"v\" ."

-- [7.2.26]: `rdf:type` as a property attribute takes an IRI object.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/s' "
    ++ "rdf:type='http://example.org/T'/>")
  "<http://example.org/s> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.org/T> ."

-- [7.2.26]: a property attribute picks up the in-scope `xml:lang`.
#guard iso
  "<rdf:Description rdf:about='http://example.org/s' xml:lang='en' eg:p='v'/>"
  "<http://example.org/s> <http://example.org/p> \"v\"@en ."

-- [7.2.26]: `xmlns` declarations and `xml:*` attributes are NOT property
-- attributes.
#guard count "<rdf:Description rdf:about='http://example.org/s' xml:lang='en'/>" == 0

-- [7.2.26]: an UNPREFIXED attribute has no namespace, so no predicate
-- IRI, so no triple (Namespaces in XML §6.2).
#guard count "<rdf:Description rdf:about='http://example.org/s' foo='v'/>" == 0

/-! ## `rdf:li` — RDF/XML §5.3 -/

-- §5.3: `rdf:li` becomes `rdf:_1`, `rdf:_2`, … in document order.
#guard iso
  ("<rdf:Bag rdf:about='http://example.org/s'>"
    ++ "<rdf:li>a</rdf:li><rdf:li>b</rdf:li></rdf:Bag>")
  ("<http://example.org/s> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> "
    ++ "<http://www.w3.org/1999/02/22-rdf-syntax-ns#Bag> .\n"
    ++ "<http://example.org/s> <http://www.w3.org/1999/02/22-rdf-syntax-ns#_1> \"a\" .\n"
    ++ "<http://example.org/s> <http://www.w3.org/1999/02/22-rdf-syntax-ns#_2> \"b\" .")

-- §5.3: the counter is per NODE ELEMENT — a nested one starts at 1
-- again and does not disturb the outer numbering.
#guard iso
  ("<rdf:Seq rdf:about='http://example.org/s'>"
    ++ "<rdf:li><rdf:Seq rdf:about='http://example.org/t'><rdf:li>x</rdf:li></rdf:Seq></rdf:li>"
    ++ "<rdf:li>b</rdf:li></rdf:Seq>")
  ("<http://example.org/s> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> "
    ++ "<http://www.w3.org/1999/02/22-rdf-syntax-ns#Seq> .\n"
    ++ "<http://example.org/t> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> "
    ++ "<http://www.w3.org/1999/02/22-rdf-syntax-ns#Seq> .\n"
    ++ "<http://example.org/s> <http://www.w3.org/1999/02/22-rdf-syntax-ns#_1> "
    ++ "<http://example.org/t> .\n"
    ++ "<http://example.org/t> <http://www.w3.org/1999/02/22-rdf-syntax-ns#_1> \"x\" .\n"
    ++ "<http://example.org/s> <http://www.w3.org/1999/02/22-rdf-syntax-ns#_2> \"b\" .")

-- §5.3: an `rdf:parseType='Resource'` group opens its own counter scope
-- and restores the outer one on the way out.
#guard iso
  ("<rdf:Bag rdf:about='http://example.org/s'>"
    ++ "<rdf:li rdf:parseType='Resource'><rdf:li>x</rdf:li></rdf:li>"
    ++ "<rdf:li>b</rdf:li></rdf:Bag>")
  ("<http://example.org/s> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> "
    ++ "<http://www.w3.org/1999/02/22-rdf-syntax-ns#Bag> .\n"
    ++ "<http://example.org/s> <http://www.w3.org/1999/02/22-rdf-syntax-ns#_1> _:x .\n"
    ++ "_:x <http://www.w3.org/1999/02/22-rdf-syntax-ns#_1> \"x\" .\n"
    ++ "<http://example.org/s> <http://www.w3.org/1999/02/22-rdf-syntax-ns#_2> \"b\" .")

-- §7.2.11: `rdf:li` is forbidden as a NODE element name.
#guard rejects
  ("<rdf:Description rdf:about='http://example.org/s'><eg:p>"
    ++ "<rdf:li rdf:about='http://example.org/o'/></eg:p></rdf:Description>")

-- §7.2.14: `rdf:li` is an element name, never an attribute.
#guard rejects "<rdf:Description rdf:about='http://example.org/s' rdf:li='v'/>"

/-! ## §7.3 reification -/

-- §7.3: `rdf:ID` on a PROPERTY element names the statement and adds the
-- four reification triples.
#guard iso
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:ID='r'>v</eg:p></rdf:Description>")
  ("<http://example.org/s> <http://example.org/p> \"v\" .\n"
    ++ "<http://example.org/dir/doc.rdf#r> "
    ++ "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type> "
    ++ "<http://www.w3.org/1999/02/22-rdf-syntax-ns#Statement> .\n"
    ++ "<http://example.org/dir/doc.rdf#r> "
    ++ "<http://www.w3.org/1999/02/22-rdf-syntax-ns#subject> <http://example.org/s> .\n"
    ++ "<http://example.org/dir/doc.rdf#r> "
    ++ "<http://www.w3.org/1999/02/22-rdf-syntax-ns#predicate> <http://example.org/p> .\n"
    ++ "<http://example.org/dir/doc.rdf#r> "
    ++ "<http://www.w3.org/1999/02/22-rdf-syntax-ns#object> \"v\" .")

-- §7.3: reification of an `rdf:resource` object.
#guard count
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:ID='r' rdf:resource='http://example.org/o'/></rdf:Description>") == 5

-- §7.2.23: the statement `rdf:ID` shares the document's uniqueness
-- constraint with node-element `rdf:ID`s.
#guard rejects
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:ID='r'>1</eg:p><eg:q rdf:ID='r'>2</eg:q></rdf:Description>")

/-! ## Negative cases the W3C `rdf-xml` suite carries -/

-- §7.2.11: `rdf:RDF` may not be a node element name.
#guard rejects
  ("<rdf:Description rdf:about='http://example.org/s'><eg:p>"
    ++ "<rdf:RDF/></eg:p></rdf:Description>")

-- §7.2.14: `rdf:Description` may not be a property element name.
#guard rejects "<rdf:Description rdf:about='http://example.org/s'><rdf:Description/></rdf:Description>"

-- §5.1: `rdf:aboutEach` was withdrawn from RDF.
#guard rejects "<rdf:Description rdf:aboutEach='http://example.org/c'><eg:p>v</eg:p></rdf:Description>"

-- §5.1: so was `rdf:aboutEachPrefix`.
#guard rejects "<rdf:Description rdf:aboutEachPrefix='http://example.org/'/>"

-- §5.1: `rdf:bagID` is not in RDF 1.1.
#guard rejects "<rdf:Description rdf:about='http://example.org/s' rdf:bagID='b'/>"

-- §7.2.11: at most ONE of `rdf:ID`, `rdf:about`, `rdf:nodeID`.
#guard rejects "<rdf:Description rdf:ID='a' rdf:about='http://example.org/s'/>"
#guard rejects "<rdf:Description rdf:nodeID='n' rdf:about='http://example.org/s'/>"
#guard rejects "<rdf:Description rdf:ID='a' rdf:nodeID='n'/>"

-- §7.2.11: `rdf:resource` belongs to a property element.
#guard rejects "<rdf:Description rdf:resource='http://example.org/o'/>"

-- §7.2.21: `rdf:nodeID` and `rdf:resource` both name the object.
#guard rejects
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:nodeID='n' rdf:resource='http://example.org/o'/></rdf:Description>")

-- §7.2.14: `rdf:parseType` excludes `rdf:resource`.
#guard rejects
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:parseType='Resource' rdf:resource='http://example.org/o'/></rdf:Description>")

-- §7.2.14: `rdf:parseType` excludes `rdf:datatype`.
#guard rejects
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:parseType='Literal' rdf:datatype='http://example.org/d'>x</eg:p></rdf:Description>")

-- §7.2.17: a property attribute alongside `rdf:parseType` matches no
-- production (the `rdfms-empty-property-elements/error003` case).
#guard rejects
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p eg:q='v' rdf:parseType='Literal'/></rdf:Description>")

-- §7.2.14: `rdf:about` belongs to a node element.
#guard rejects
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p rdf:about='http://example.org/o'/></rdf:Description>")

-- Namespaces in XML §3: an unbound prefix leaves the element name with
-- no namespace, so no node/property element IRI.
#guard rejectsDoc
  ("<rdf:RDF xmlns:rdf='http://www.w3.org/1999/02/22-rdf-syntax-ns#'>"
    ++ "<rdf:Description rdf:about='http://example.org/s'><nope:p>v</nope:p>"
    ++ "</rdf:Description></rdf:RDF>")

-- XML `[39] element`: an unclosed tag is not well-formed XML at all.
#guard rejectsDoc
  ("<rdf:RDF xmlns:rdf='http://www.w3.org/1999/02/22-rdf-syntax-ns#'>"
    ++ "<rdf:Description rdf:about='http://example.org/s'>")

-- §7.2.16: property attributes on a property element WITH content match
-- no production.
#guard rejects
  ("<rdf:Description rdf:about='http://example.org/s'>"
    ++ "<eg:p eg:q='v'>text</eg:p></rdf:Description>")

/-! ## Base-less documents

With no retrieval IRI, a relative reference cannot become an IRI and the
document is rejected — the same treatment `parseTurtle` gives a relative
IRI with no `@base`. Absolute references are unaffected. -/

#guard (RdfXml.parseRdfXml
  (doc "<rdf:Description rdf:about='rel'/>") none).toOption.isNone

#guard (RdfXml.parseRdfXml
  (doc "<rdf:Description rdf:about='http://example.org/s'><eg:p>v</eg:p></rdf:Description>")
  none).toOption.isSome

/-! ## Blank-node label spaces are disjoint

A generated label and an `rdf:nodeID`-derived label can never collide,
whatever the document says — the property `genLabel_ne_nodeIdLabel`
proves in RdfXmlTheorems.lean, exercised here on the shape that would
collide under the F* source's scheme. -/

#guard iso
  ("<rdf:Description rdf:nodeID='b0'><eg:p>named</eg:p></rdf:Description>"
    ++ "<rdf:Description><eg:p>anon</eg:p></rdf:Description>")
  ("_:x <http://example.org/p> \"named\" .\n_:y <http://example.org/p> \"anon\" .")

end L4Factoidal.Syntax.RdfXmlTests
