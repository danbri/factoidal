/-
L4Factoidal.XML.Tests — compile-time executable checks for the XML
port.

Every `#guard` below is evaluated during `lake build`: a wrong answer
is a BUILD FAILURE, so these are unit tests with no separate runner.

The first group is the two documents hub post 25
(`docs/web/hub/25-xml-wellformedness-and-xpath.md`) uses live, with the
verdicts that post states. The rest exercise each well-formedness
constraint listed in `Parser.lean`'s header, the namespace layer, and
the round-trip and reflexivity claims from `Theorems.lean`.

Conformance discipline (iron rule #6): NOTHING here is a conformance
claim. These are hand-written fixtures. The W3C XML Conformance Test
Suite is run by `xmlconf-probe` (`ConfProbe.lean`), which reads the
vendored corpus files from disk.
-/
import L4Factoidal.XML.Theorems
import L4Factoidal.XML.Wellformedness

namespace L4Factoidal.XML.Tests

open L4Factoidal.XML

/-! ## Hub post 25 — the two live documents

The post names one document, reuses it, then breaks it. -/

/-- The `XML` cell of hub post 25. -/
def hubXML : String :=
  "<library>\n" ++
  "  <book id=\"b1\"><title>SPARQL 1.1</title></book>\n" ++
  "  <book id=\"b2\"><title>RDF Primer</title></book>\n" ++
  "</library>"

/-- The `BAD` cell of hub post 25 — a closing tag that does not match
the element it closes. -/
def hubBAD : String := "<library><book></shelf></library>"

-- The post says `{ ok: true, wellformed: true }`.
#guard isWellFormed hubXML
-- The post says `{ ok: true, wellformed: false }`: `</shelf>` closes
-- nothing that is open.
#guard !isWellFormed hubBAD

-- The post's XPath cells select `//book/title`, so the two titles must
-- be reachable with the string-values it prints.
#guard (match parseXML hubXML with
        | .ok d => (d.root.childElements "book").map (·.textContent)
        | .error _ => []) == ["SPARQL 1.1", "RDF Primer"]

-- and `string(//book[2]/@id)` is `b2`.
#guard (match parseXML hubXML with
        | .ok d => ((d.root.childElements "book")[1]?).bind
                     (fun b => findAttr "id" b.elementAttrs)
        | .error _ => none) == some "b2"

/-! ## `[39] element` — WFC: Element Type Match -/

#guard isWellFormed "<a/>"
#guard isWellFormed "<a></a>"
#guard isWellFormed "<a><b><c/></b></a>"
-- Mismatched tags.
#guard !isWellFormed "<a></b>"
#guard !isWellFormed "<a><b></a></b>"
-- Unclosed.
#guard !isWellFormed "<a>"

/-! ## `[41] Attribute` — WFC: Unique Att Spec -/

#guard isWellFormed "<a x=\"1\" y=\"2\"/>"
-- Duplicate attribute name.
#guard !isWellFormed "<a x=\"1\" x=\"2\"/>"
-- Unescaped `<` in an attribute value ([10] AttValue excludes it).
#guard !isWellFormed "<a x=\"<\"/>"
-- Unquoted value.
#guard !isWellFormed "<a x=1/>"

/-! ## `[66] CharRef` and `[68] EntityRef` -/

#guard isWellFormed "<a>&#65;&#x41;&amp;&lt;&gt;&quot;&apos;</a>"
-- `&#RE;` — `R` is not a decimal digit.
#guard !isWellFormed "<a>&#RE;</a>"
-- `&#x4G;` — `G` is not a hexadecimal digit.
#guard !isWellFormed "<a>&#x4G;</a>"
-- Uppercase `X` is not the hexadecimal marker; it falls through to the
-- decimal path, where it is not a digit.
#guard !isWellFormed "<a>&#X41;</a>"
-- A character reference to a codepoint outside `[2] Char`.
#guard !isWellFormed "<a>&#0;</a>"
-- Not terminated by `;`.
#guard !isWellFormed "<a>&amp</a>"
-- WFC: Entity Declared.
#guard !isWellFormed "<a>&undeclared;</a>"
-- A declared internal general entity resolves.
#guard isWellFormed "<!DOCTYPE a [<!ENTITY e \"val\">]><a>&e;</a>"
#guard (match parseXML "<!DOCTYPE a [<!ENTITY e \"val\">]><a>&e;</a>" with
        | .ok d => d.root.textContent
        | .error _ => "") == "val"
-- WFC: No Recursion.
#guard !isWellFormed "<!DOCTYPE a [<!ENTITY e \"&e;\">]><a>&e;</a>"

/-! ### Entities with empty replacement text

The one place this port's VERDICT differs from `Parser.XML.fst`'s. When
an element's whole content is a reference to an entity whose
replacement text is empty, the F* parser stops collecting children at
the `&` and then rejects the document for want of an end tag. These
documents are well-formed, and the W3C conformance suite marks them
valid — `xmltest/valid/sa/023.xml`, `085.xml`, `086.xml`. See the
comment on `parseChildren`. -/

-- The body of xmltest/valid/sa/023.xml.
#guard isWellFormed "<!DOCTYPE doc [<!ELEMENT doc (#PCDATA)><!ENTITY e \"\">]><doc>&e;</doc>"
-- The body of xmltest/valid/sa/086.xml — a duplicate declaration, where
-- §4.2 says the FIRST binding wins, so `e` is still empty.
#guard isWellFormed
  "<!DOCTYPE doc [<!ELEMENT doc (#PCDATA)><!ENTITY e \"\"><!ENTITY e \"<foo>\">]><doc>&e;</doc>"
-- An expansion yielding no characters contributes no `[14] CharData`:
-- the element has no child at all, rather than an empty text node.
#guard (match parseXML "<!DOCTYPE doc [<!ENTITY e \"\">]><doc>&e;</doc>" with
        | .ok d => d.root.elementChildren.length
        | .error _ => 99) == 0
#guard roundTripsFrom "<!DOCTYPE doc [<!ENTITY e \"\">]><doc>&e;</doc>"

/-! ## `[15] Comment` -/

#guard isWellFormed "<a><!-- hi --></a>"
-- `--` may not occur inside a comment.
#guard !isWellFormed "<a><!-- a -- b --></a>"
-- ...nor may the body end in `-`.
#guard !isWellFormed "<a><!-- ---></a>"

/-! ## `[16] PI` — `[17] PITarget` -/

#guard isWellFormed "<a><?tgt data?></a>"
#guard isWellFormed "<a><?tgt?></a>"
-- The reserved target `xml`, in any case, is not a legal generic PI.
#guard !isWellFormed "<a><?xml foo?></a>"
#guard !isWellFormed "<a><?xMl foo?></a>"
-- A target is required.
#guard !isWellFormed "<a><? ?></a>"

/-! ## `[18] CDSect` and `[14] CharData` -/

#guard isWellFormed "<a><![CDATA[x < y & z]]></a>"
-- The content of a CDATA section reaches the infoset verbatim.
#guard (match parseXML "<a><![CDATA[x < y & z]]></a>" with
        | .ok d => d.root.textContent
        | .error _ => "") == "x < y & z"
-- `[14] CharData` excludes a literal `]]>`.
#guard !isWellFormed "<a>]]></a>"
-- ...but a reference may put those characters into the infoset.
#guard isWellFormed "<a>]]&gt;</a>"
-- An unterminated CDATA section.
#guard !isWellFormed "<a><![CDATA[x</a>"

/-! ## `[2] Char` -/

-- A vertical tab (#xB) is outside `[2] Char`.
#guard !isWellFormed ("<a>" ++ String.singleton (Char.ofNat 0xB) ++ "</a>")
-- Tab, LF and CR are inside it.
#guard isWellFormed "<a>\t\n</a>"

/-! ## UTF-8 — non-ASCII text and names -/

#guard isWellFormed "<a>日本語 café</a>"
#guard (match parseXML "<a>日本語 café</a>" with
        | .ok d => d.root.textContent
        | .error _ => "") == "日本語 café"
-- `[4] NameStartChar` admits these codepoints, so the element name
-- parses whole rather than being truncated mid-character.
#guard (match parseXML "<日本 x=\"1\">t</日本>" with
        | .ok d => d.root.elementTag
        | .error _ => none) == some "日本"

/-! ## `[23] XMLDecl` -/

#guard isWellFormed "<?xml version=\"1.0\"?><a/>"
#guard isWellFormed "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"yes\"?><a/>"
#guard (match parseXML "<?xml version=\"1.0\" encoding=\"UTF-8\"?><a/>" with
        | .ok d => d.decl
        | .error _ => none)
       == some { version := "1.0", encoding := some "UTF-8", standalone := none }
-- `[26] VersionNum ::= '1.' [0-9]+`.
#guard !isWellFormed "<?xml version=\"2.0\"?><a/>"
-- `[32] SDDecl` is lowercase only.
#guard !isWellFormed "<?xml version=\"1.0\" standalone=\"YES\"?><a/>"
-- Out of order.
#guard !isWellFormed "<?xml version=\"1.0\" standalone=\"yes\" encoding=\"UTF-8\"?><a/>"
-- Nothing may precede the declaration.
#guard !isWellFormed " <?xml version=\"1.0\"?><a/>"

/-! ## `[1] document` — one root, and a Misc-only epilog -/

#guard isWellFormed "<!-- prolog --><a/><!-- epilog -->"
#guard isWellFormed "<?pi d?><a/><?pi d?>"
-- A second document element.
#guard !isWellFormed "<a/><b/>"
-- Stray text in the epilog.
#guard !isWellFormed "<a/>junk"
-- No document element at all.
#guard !isWellFormed "<!-- only a comment -->"

/-! ## `[28] doctypedecl` -/

#guard isWellFormed "<!DOCTYPE a><a/>"
#guard isWellFormed "<!DOCTYPE a SYSTEM \"a.dtd\"><a/>"
#guard isWellFormed "<!DOCTYPE a [<!ELEMENT a EMPTY>]><a/>"
-- The internal subset's ATTLIST ID pairs reach the infoset.
#guard (match parseXML "<!DOCTYPE a [<!ATTLIST a k ID #IMPLIED>]><a k=\"v\"/>" with
        | .ok d => (d.doctype.map (·.idAttrs)).getD []
        | .error _ => []) == [("a", "k")]
-- An unterminated internal subset.
#guard !isWellFormed "<!DOCTYPE a [<!ENTITY e \"v\"><a/>"

/-! ## §3.3.3 attribute-value normalisation -/

-- A LITERAL tab in an attribute value becomes a space...
#guard (match parseXML "<a x=\"p\tq\"/>" with
        | .ok d => findAttr "x" d.root.elementAttrs
        | .error _ => none) == some "p q"
-- ...while a CHARACTER REFERENCE to one keeps the character itself.
#guard (match parseXML "<a x=\"p&#9;q\"/>" with
        | .ok d => findAttr "x" d.root.elementAttrs
        | .error _ => none) == some "p\tq"

/-! ## §2.11 line-ending normalisation -/

#guard normalizeLineEndings "a\r\nb\rc\nd".toList == "a\nb\nc\nd".toList
#guard (match parseXML "<a>x\r\ny</a>" with
        | .ok d => d.root.textContent
        | .error _ => "") == "x\ny"

/-! ## Namespaces in XML -/

-- A declaration is in scope for the element that carries it.
#guard isNamespaceWellFormedDoc "<r xmlns:p=\"http://e/\"><p:c/></r>"
-- An undeclared prefix rejects.
#guard !isNamespaceWellFormedDoc "<r><p:c/></r>"
-- ...though it is perfectly well-formed PLAIN XML 1.0, where `:` is an
-- ordinary Name character. The two layers are separate on purpose.
#guard isWellFormed "<r><p:c/></r>"
-- The default namespace applies to unprefixed ELEMENT names (§4).
#guard isNamespaceWellFormedDoc "<r xmlns=\"http://d/\"><c/></r>"
#guard resolveElementName [("", some "http://d/")] "c"
       == some { namespace_ := some "http://d/", localPart := "c" }
-- An unprefixed ATTRIBUTE name is never in the default namespace (§6.2).
#guard resolveAttributeName [("", some "http://d/")] "c"
       == some { namespace_ := none, localPart := "c" }
-- §6.3: two attributes collide once their prefixes expand to the same
-- namespace name, even though their QNames differ.
#guard !isNamespaceWellFormedDoc
  "<r xmlns:a=\"http://e/\" xmlns:b=\"http://e/\"><c a:x=\"1\" b:x=\"2\"/></r>"
-- Reserved prefixes and namespace names.
#guard !isNamespaceWellFormedDoc "<r xmlns:xmlns=\"http://e/\"/>"
#guard !isNamespaceWellFormedDoc "<r xmlns:xml=\"http://bogus/\"/>"
#guard isNamespaceWellFormedDoc "<r xmlns:xml=\"http://www.w3.org/XML/1998/namespace\"/>"
-- `xml` is bound without being declared.
#guard isNamespaceWellFormedDoc "<r xml:lang=\"en\"/>"
-- Undeclaring a PREFIXED binding: illegal in 1.0, legal in 1.1.
#guard !isNamespaceWellFormedDoc "<r xmlns:p=\"http://e/\"><s xmlns:p=\"\"/></r>"
#guard isNamespaceWellFormedDoc
  "<?xml version=\"1.1\"?><r xmlns:p=\"http://e/\"><s xmlns:p=\"\"/></r>"
-- The default namespace may always be undeclared.
#guard isNamespaceWellFormedDoc "<r xmlns=\"http://d/\"><s xmlns=\"\"/></r>"
-- `[7] QName` syntax.
#guard splitQName "p:c" == .prefixed "p" "c"
#guard splitQName "c" == .simple "c"
#guard splitQName "a:b:c" == .malformed
#guard splitQName ":c" == .malformed
#guard splitQName "p:" == .malformed
#guard !isNamespaceWellFormedDoc "<a:b:c/>"

/-! ## `[4] NCName` — Namespaces in XML §3 -/

#guard isValidNCName "abc"
#guard isValidNCName "_a-b.c1"
#guard !isValidNCName "a:b"
#guard !isValidNCName ""
#guard !isValidNCName "1abc"

/-! ## RDF/XML checks — `XML.Wellformedness.fst`'s other half -/

#guard isForbiddenNodeElementName "http://www.w3.org/1999/02/22-rdf-syntax-ns#li"
#guard !isForbiddenPropertyElementName "http://www.w3.org/1999/02/22-rdf-syntax-ns#li"
#guard isForbiddenPropertyElementName "http://www.w3.org/1999/02/22-rdf-syntax-ns#Description"
#guard checkConflictingAttrsNode [{ name := "rdf:ID", value := "x" },
                                  { name := "rdf:about", value := "y" }]
       == some "conflicting rdf:ID and rdf:about on a node element"
#guard checkConflictingAttrsProperty [{ name := "rdf:ID", value := "x" },
                                      { name := "rdf:about", value := "y" }] == none
#guard validateRdfIdAttr [{ name := "rdf:ID", value := "a:b" }]
       == some "Invalid rdf:ID value: a:b"

/-! ## Reflexivity of the well-formedness checker

Evidence for `ReflexiveOnParserOutput` on fixtures — NOT a proof of it.
The tag-matching component IS proved, in
`Node.serialize_element_tags_match`. -/

#guard reflexiveOn hubXML
#guard reflexiveOn "<a/>"
#guard reflexiveOn "<a x=\"1\"><b>t</b><!-- c --><![CDATA[d]]><?p e?></a>"
#guard reflexiveOn "<?xml version=\"1.0\"?><!-- p --><!DOCTYPE a><a>日本</a><!-- e -->"
-- The checker is stated on the INFOSET, so it accepts characters the
-- SYNTAX forbids but a reference legally introduces.
#guard reflexiveOn "<a x=\"&lt;\">]]&gt;</a>"

/-! ## Round-trip: `parseXML (Document.toString d) = .ok d`

Evidence for `RoundTripsOnParse` on fixtures — NOT a proof of it. The
STRING deliberately does not round-trip: `<a></a>` serialises as
`<a/>`, because the infoset is what the parser is a function into. -/

#guard roundTripsFrom hubXML
#guard roundTripsFrom "<a/>"
#guard roundTripsFrom "<a></a>"
#guard roundTripsFrom "<a x=\"1\" y=\"2\">text</a>"
#guard roundTripsFrom "<a x=\"&lt;&amp;&quot;\"/>"
-- Tab / LF / CR in an attribute value survive as character references,
-- so §3.3.3 normalisation does not flatten them on the way back in.
#guard roundTripsFrom "<a x=\"&#9;&#10;tab\"/>"
#guard roundTripsFrom "<a><!-- c --><![CDATA[x < y]]><?p d?></a>"
#guard roundTripsFrom "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"yes\"?><a/>"
#guard roundTripsFrom "<!-- p --><?pi d?><a/><!-- e -->"
#guard roundTripsFrom "<!DOCTYPE a [<!ENTITY e \"val\"><!ENTITY f \"two\">]><a>&e;&f;</a>"
#guard roundTripsFrom "<!DOCTYPE a [<!ATTLIST a k ID #IMPLIED>]><a k=\"v\"/>"
#guard roundTripsFrom "<a>日本語 café</a>"
#guard roundTripsFrom "<日本 x=\"1\">t</日本>"
#guard roundTripsFrom "<a>]]&gt; and &lt;</a>"
#guard roundTripsFrom "<r xmlns:p=\"http://e/\" xmlns=\"http://d/\"><p:c a=\"1\"/></r>"

/-! ## Axiom audit

Every build log carries these lines. The acceptable base is exactly
Lean's standard foundations; no `sorry`, no user `axiom`, no
`native_decide`. -/

#print axioms Node.serialize_element_tags_match
#print axioms Node.wellFormedList_eq_all
#print axioms Node.wellFormed_of_mem_children
#print axioms Node.serializeList_cons
#print axioms parseXML
#print axioms isNamespaceWellFormed

end L4Factoidal.XML.Tests
