/-
L4Factoidal.XML.Document — the XML infoset data model and the
character classes the grammar is stated over.

Port of the AST and character-classification sections of
`formal/fstar/Parser.XML.fst` (F*) to Lean 4. Production numbers cite
**Extensible Markup Language (XML) 1.0 (Fifth Edition)**,
W3C Recommendation 26 November 2008, https://www.w3.org/TR/xml/ .
The namespace layer cites **Namespaces in XML 1.0 (Third Edition)**,
W3C Recommendation 8 December 2009, https://www.w3.org/TR/xml-names/ .

What this module holds:
  * `[2] Char`, `[3] S`, `[4] NameStartChar`, `[4a] NameChar` — the
    character classes every other production is phrased in terms of;
  * `Attribute` / `Node` — the parse tree `Parser.XML.parse_xml_document`
    produces (F* `xml_attribute` / `xml_node`);
  * `XmlDecl` / `Doctype` / `Document` — the prolog information the F*
    parser computes (`parse_xml_declaration`, `parse_doctype`) bundled
    with the root element and the prolog/epilog Misc nodes, exactly the
    content of F* `parse_xml_document_children_with_ids`;
  * `QNameSplit` / `ExpandedName` — the Namespaces-in-XML §3 name model
    (F* `XML.Namespaces.qname_split`).

Design correspondences (F* → Lean 4):
  * `noeq type xml_node`            → `inductive Node` (nested in `List`)
  * `type xml_attribute = {...}`    → `structure Attribute`
  * byte offsets + `fs_byte_index`  → `Array Char` + `Nat` index
  * `Tot ... (decreases fuel)`      → structural recursion on a `Nat`
  * `assert_norm`                   → `rfl` / `#guard`

**Byte semantics vs codepoint semantics.** The F* parser indexes raw
UTF-8 BYTES (`Parser.FastString`), so it carries machinery whose only
purpose is to rebuild codepoints from bytes and to reject byte
sequences that are not valid UTF-8 at all: `fs_cp_at`,
`is_utf8_continuation_byte`, `is_valid_decoded_char`'s
`(0xFFFD, adv = 1)` sentinel, and the hand-written UTF-8 encoder
`codepoint_to_string`. Lean's `String`/`Char` are codepoint types and a
`Char` is a valid scalar value by construction (surrogates are
excluded by `Char.isValidChar`), so **none of that machinery has a
Lean counterpart** — the invalid-UTF-8 rejection the F* performs is
discharged by Lean's type, not by a check. Every rule stated over
CODEPOINTS is ported in full; see PORT_NOTES.md.

Deliberately NOT ported (out of the F* modules' own scope):
  * validity constraints — content models, ATTLIST enforcement,
    ID/IDREF uniqueness (`[28] doctypedecl` is recognised, never
    enforced: the F* is an explicitly non-validating processor);
  * the external DTD subset, conditional sections, and general
    parameter-entity expansion.
-/

namespace L4Factoidal.XML

/-! ## Character classes

Every production below is phrased over these four classes. -/

/-- `[2] Char ::= #x9 | #xA | #xD | [#x20-#xD7FF] | [#xE000-#xFFFD] |
[#x10000-#x10FFFF]` — the characters an XML document may contain at
all. Excludes #x0-#x8, #xB, #xC, #xE-#x1F, the surrogate block
#xD800-#xDFFF, and the two non-characters #xFFFE / #xFFFF.
Port of F* `is_valid_xml_char`. -/
def isXmlCharCode (cp : Nat) : Bool :=
  cp == 0x9 || cp == 0xA || cp == 0xD ||
  (0x20 ≤ cp && cp ≤ 0xD7FF) ||
  (0xE000 ≤ cp && cp ≤ 0xFFFD) ||
  (0x10000 ≤ cp && cp ≤ 0x10FFFF)

/-- `[2] Char` as a predicate on a Lean `Char`. -/
def isXmlChar (c : Char) : Bool := isXmlCharCode c.toNat

/-- `[3] S ::= (#x20 | #x9 | #xD | #xA)+` — the whitespace class (this
predicate is the single character; the `+` is applied by the parser).
Port of F* `is_xml_space`. -/
def isXmlSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- The non-ASCII half of `[4] NameStartChar`. These are the XML 1.1
`NameStartChar` ranges (https://www.w3.org/TR/xml11/#NT-NameStartChar),
which is the table the F* parser uses — it is a superset of XML 1.0
Fifth Edition's own `NameStartChar` in the same shape. Port of F*
`is_name_start_char_nonascii_cp`. -/
def isNameStartCharNonAscii (cp : Nat) : Bool :=
  (0xC0 ≤ cp && cp ≤ 0xD6) ||
  (0xD8 ≤ cp && cp ≤ 0xF6) ||
  (0xF8 ≤ cp && cp ≤ 0x2FF) ||
  (0x370 ≤ cp && cp ≤ 0x37D) ||
  (0x37F ≤ cp && cp ≤ 0x1FFF) ||
  (0x200C ≤ cp && cp ≤ 0x200D) ||
  (0x2070 ≤ cp && cp ≤ 0x218F) ||
  (0x2C00 ≤ cp && cp ≤ 0x2FEF) ||
  (0x3001 ≤ cp && cp ≤ 0xD7FF) ||
  (0xF900 ≤ cp && cp ≤ 0xFDCF) ||
  (0xFDF0 ≤ cp && cp ≤ 0xFFFD) ||
  (0x10000 ≤ cp && cp ≤ 0xEFFFF)

/-- The non-ASCII half of `[4a] NameChar` — `NameStartChar` plus the
Extender U+00B7, the combining marks U+0300-U+036F, and
U+203F-U+2040. Port of F* `is_name_char_nonascii_cp`. -/
def isNameCharNonAscii (cp : Nat) : Bool :=
  isNameStartCharNonAscii cp ||
  cp == 0xB7 ||
  (0x300 ≤ cp && cp ≤ 0x36F) ||
  (0x203F ≤ cp && cp ≤ 0x2040)

/-- `[4] NameStartChar ::= ":" | [A-Z] | "_" | [a-z] | …`.

`:` IS a name start character here: `Parser.XML` is a plain XML 1.0,
**non-namespace** parser, in which a colon is an ordinary Name
character (`xmltest/` exercises that on purpose, predating Namespaces
in XML). The colon restriction belongs to the separate namespace
layer — see `L4Factoidal.XML.Namespaces`. Port of F*
`is_name_start_cp`. -/
def isNameStartChar (c : Char) : Bool :=
  let cp := c.toNat
  if cp < 0x80 then
    (0x41 ≤ cp && cp ≤ 0x5A) ||   -- A-Z
    (0x61 ≤ cp && cp ≤ 0x7A) ||   -- a-z
    cp == 0x5F ||                 -- _
    cp == 0x3A                    -- :
  else isNameStartCharNonAscii cp

/-- `[4a] NameChar ::= NameStartChar | "-" | "." | [0-9] | #xB7 | …`.
Port of F* `is_name_char` / `is_name_char_cp`. -/
def isNameChar (c : Char) : Bool :=
  let cp := c.toNat
  if cp < 0x80 then
    (0x41 ≤ cp && cp ≤ 0x5A) ||   -- A-Z
    (0x61 ≤ cp && cp ≤ 0x7A) ||   -- a-z
    (0x30 ≤ cp && cp ≤ 0x39) ||   -- 0-9
    cp == 0x5F || cp == 0x3A ||   -- _ :
    cp == 0x2D || cp == 0x2E      -- - .
  else isNameCharNonAscii cp

/-- ASCII-only lowercasing, used for exactly one thing: the
case-insensitive comparison of a `[17] PITarget` against the reserved
name `xml`. Never applied to Name or content characters generally.
Port of F* `to_lower_ascii`. -/
def toLowerAscii (c : Char) : Char :=
  let cp := c.toNat
  if 0x41 ≤ cp && cp ≤ 0x5A then Char.ofNat (cp + 0x20) else c

/-- `[17] PITarget ::= Name - (('X'|'x')('M'|'m')('L'|'l'))` — true
when `s` is the reserved target name `xml` in any case combination.
Such a token may be consumed only by `[23] XMLDecl`, at the literal
start of the document; anywhere else it is not a legal generic
processing instruction. Port of F* `is_xml_target_name_ci`. -/
def isXmlTargetNameCI (s : String) : Bool :=
  match s.toList with
  | [a, b, c] => toLowerAscii a == 'x' && toLowerAscii b == 'm' && toLowerAscii c == 'l'
  | _ => false

/-- `[5] Name ::= NameStartChar (NameChar)*` as a predicate on a whole
string. The parser scans names positionally; this is the same rule
stated over an already-extracted string, used by the well-formedness
checker and the round-trip theorems. -/
def isName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest => isNameStartChar c && rest.all isNameChar

/-! ## The parse tree

F* `xml_attribute` / `xml_node`, unchanged in shape. -/

/-- `[41] Attribute ::= Name Eq AttValue` — one attribute of a start
tag, with its value already normalised per §3.3.3 and with character
and entity references already resolved. Port of F* `xml_attribute`. -/
structure Attribute where
  /-- `[5] Name` — the attribute's name, exactly as written (a QName is
  only a QName to the namespace layer; here it is a plain Name). -/
  name : String
  /-- `[10] AttValue`, after §3.3.3 normalisation and reference
  resolution. -/
  value : String
deriving DecidableEq, Repr, Inhabited

/-- A node of the XML parse tree.

Constructor ↔ production:
  * `text`    — `[14] CharData` (with `[67] Reference`s resolved)
  * `element` — `[39] element ::= EmptyElemTag | STag content ETag`
  * `comment` — `[15] Comment ::= '<!--' … '-->'`
  * `cdata`   — `[18] CDSect ::= CDStart CData CDEnd`
  * `pi`      — `[16] PI ::= '<?' PITarget (S …)? '?>'`

Processing instructions are RETAINED in the tree rather than skipped,
so XPath's `processing-instruction()` node test and XSLT can see them;
the `data` component excludes the target and the single run of
whitespace separating it from the target, per the DOM/XPath
string-value convention. Port of F* `xml_node`. -/
inductive Node where
  /-- `[14] CharData` — character data. -/
  | text (content : String) : Node
  /-- `[39] element` — tag name, attributes, children. -/
  | element (tag : String) (attrs : List Attribute) (children : List Node) : Node
  /-- `[15] Comment` — the body, between `<!--` and `-->`. -/
  | comment (body : String) : Node
  /-- `[18] CDSect` — the raw character data of a CDATA section. -/
  | cdata (content : String) : Node
  /-- `[16] PI` — `[17] PITarget` and the instruction data. -/
  | pi (target : String) (data : String) : Node
deriving Repr, Inhabited

mutual

/-- Decidable equality on `Node`. Written by hand rather than derived:
`Node` is a NESTED inductive (`List Node` in `element`) and no
`DecidableEq` deriving handler applies to it. `DecidableEq` — never
`deriving BEq` — is what the project's Lean pitfall #1 requires, so
that `==` comes from the lawful `instBEqOfDecidableEq`. -/
protected def Node.decEq : (a b : Node) → Decidable (a = b)
  | .text x, .text y =>
      if h : x = y then isTrue (by subst h; rfl)
      else isFalse (by intro hc; cases hc; exact h rfl)
  | .comment x, .comment y =>
      if h : x = y then isTrue (by subst h; rfl)
      else isFalse (by intro hc; cases hc; exact h rfl)
  | .cdata x, .cdata y =>
      if h : x = y then isTrue (by subst h; rfl)
      else isFalse (by intro hc; cases hc; exact h rfl)
  | .pi t1 d1, .pi t2 d2 =>
      if ht : t1 = t2 then
        if hd : d1 = d2 then isTrue (by subst ht; subst hd; rfl)
        else isFalse (by intro hc; cases hc; exact hd rfl)
      else isFalse (by intro hc; cases hc; exact ht rfl)
  | .element t1 a1 c1, .element t2 a2 c2 =>
      if ht : t1 = t2 then
        if ha : a1 = a2 then
          match Node.decEqList c1 c2 with
          | isTrue hc => isTrue (by subst ht; subst ha; subst hc; rfl)
          | isFalse hc => isFalse (by intro he; cases he; exact hc rfl)
        else isFalse (by intro he; cases he; exact ha rfl)
      else isFalse (by intro he; cases he; exact ht rfl)
  | .text _, .element _ _ _ => isFalse (by intro h; cases h)
  | .text _, .comment _ => isFalse (by intro h; cases h)
  | .text _, .cdata _ => isFalse (by intro h; cases h)
  | .text _, .pi _ _ => isFalse (by intro h; cases h)
  | .element _ _ _, .text _ => isFalse (by intro h; cases h)
  | .element _ _ _, .comment _ => isFalse (by intro h; cases h)
  | .element _ _ _, .cdata _ => isFalse (by intro h; cases h)
  | .element _ _ _, .pi _ _ => isFalse (by intro h; cases h)
  | .comment _, .text _ => isFalse (by intro h; cases h)
  | .comment _, .element _ _ _ => isFalse (by intro h; cases h)
  | .comment _, .cdata _ => isFalse (by intro h; cases h)
  | .comment _, .pi _ _ => isFalse (by intro h; cases h)
  | .cdata _, .text _ => isFalse (by intro h; cases h)
  | .cdata _, .element _ _ _ => isFalse (by intro h; cases h)
  | .cdata _, .comment _ => isFalse (by intro h; cases h)
  | .cdata _, .pi _ _ => isFalse (by intro h; cases h)
  | .pi _ _, .text _ => isFalse (by intro h; cases h)
  | .pi _ _, .element _ _ _ => isFalse (by intro h; cases h)
  | .pi _ _, .comment _ => isFalse (by intro h; cases h)
  | .pi _ _, .cdata _ => isFalse (by intro h; cases h)

/-- Decidable equality on a child list — the nested-inductive
companion of `Node.decEq`. -/
protected def Node.decEqList : (a b : List Node) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | x :: xs, y :: ys =>
      match Node.decEq x y with
      | isTrue hx =>
          match Node.decEqList xs ys with
          | isTrue hs => isTrue (by subst hx; subst hs; rfl)
          | isFalse hs => isFalse (by intro h; cases h; exact hs rfl)
      | isFalse hx => isFalse (by intro h; cases h; exact hx rfl)

end

instance : DecidableEq Node := Node.decEq

/-! ## The prolog

`[22] prolog ::= XMLDecl? Misc* (doctypedecl Misc*)?` -/

/-- `[23] XMLDecl ::= '<?xml' VersionInfo EncodingDecl? SDDecl? S? '?>'`
— the three pseudo-attributes, in the one order the grammar permits.

The F* `parse_xml_declaration` returns these as a `list xml_attribute`
and `parse_xml_document` then DISCARDS them; recording them in a
structure loses nothing and lets the namespace layer read the declared
version (which decides whether a prefixed namespace may be undeclared).
-/
structure XmlDecl where
  /-- `[26] VersionNum ::= '1.' [0-9]+`. -/
  version : String
  /-- `[81] EncName ::= [A-Za-z] ([A-Za-z0-9._] | '-')*`. -/
  encoding : Option String
  /-- `[32] SDDecl` value — `"yes"` or `"no"`, lowercase only. -/
  standalone : Option String
deriving DecidableEq, Repr, Inhabited

/-- `[28] doctypedecl ::= '<!DOCTYPE' S Name (S ExternalID)? S?
('[' intSubset ']' S?)? '>'`, as far as a NON-VALIDATING processor
reads it — which is exactly as far as the F* `parse_doctype` reads it.

Recorded: the root Name, the general internal entity declarations
(`[71] GEDecl` with an `[9] EntityValue`, first declaration wins per
§4.2), and the `(element, attribute)` pairs whose `[54] AttType` is
exactly `ID` (the substrate for XPath's `id()`).

NOT recorded and NOT acted on: the external subset (never loaded — no
external resource is read), `[45] elementdecl`, `[52] AttlistDecl`
enforcement, `[82] NotationDecl`, parameter entities, and conditional
sections. They are skipped structurally. -/
structure Doctype where
  /-- The document type name — `[28]`'s `Name`. -/
  rootName : String
  /-- `[71] GEDecl` internal general entities: name ↦ raw replacement
  text, un-expanded (references inside are resolved lazily at the
  reference site). -/
  entities : List (String × String)
  /-- `(element name, attribute name)` pairs declared `[54] AttType`
  = `ID` in the internal subset. -/
  idAttrs : List (String × String)
deriving DecidableEq, Repr, Inhabited

/-- `[1] document ::= prolog element Misc*`.

`prolog`/`epilog` hold the `[27] Misc` Comment and PI nodes in
document order. Whitespace between them is NOT a node (XML has no
document-level text nodes), so only those two Misc kinds appear —
exactly the two the F* `collect_misc` accumulates. `root` is the
single document element.

This is the content of F* `parse_xml_document_children_with_ids`
(prolog Misc ++ root :: epilog Misc, plus the ID pairs) with the
declaration and DOCTYPE kept as structured fields instead of being
discarded. -/
structure Document where
  /-- `[23] XMLDecl`, if the document opened with one. -/
  decl : Option XmlDecl
  /-- `[28] doctypedecl`, if present. -/
  doctype : Option Doctype
  /-- `[27] Misc` — Comment / PI nodes before the document element. -/
  prolog : List Node
  /-- `[39] element` — the single document element. -/
  root : Node
  /-- `[27] Misc` — Comment / PI nodes after the document element. -/
  epilog : List Node
deriving DecidableEq, Repr, Inhabited

/-- The document node's ordered child list — prolog Misc, then the
document element, then epilog Misc. This is exactly what F*
`parse_xml_document_children` returns, and it is what XPath's `/`
ranges over. -/
def Document.children (d : Document) : List Node :=
  d.prolog ++ (d.root :: d.epilog)

/-! ## Namespace names — Namespaces in XML 1.0 §3

The parse tree above carries raw `[5] Name`s. Turning a Name into a
namespace-qualified name is a SEPARATE layer, deliberately not baked
into the parser (see `L4Factoidal.XML.Namespaces`). -/

/-- The result of splitting a raw Name against
`[7] QName ::= PrefixedName | UnprefixedName`,
`[8] PrefixedName ::= Prefix ':' LocalPart`.

A Name is a legal QName iff it has at most one colon, and that colon is
neither first nor last (either would give an empty Prefix or an empty
LocalPart). Plain XML 1.0 Names may carry any number of colons
anywhere — `malformed` records a violation of the NAMESPACE layer's
extra restriction, never of XML 1.0 itself. Port of F*
`XML.Namespaces.qname_split`. -/
inductive QNameSplit where
  /-- `[9] UnprefixedName ::= LocalPart` — no colon. -/
  | simple (localPart : String) : QNameSplit
  /-- `[8] PrefixedName ::= Prefix ':' LocalPart`. -/
  | prefixed (prefix_ : String) (localPart : String) : QNameSplit
  /-- Not a QName: two or more colons, or a leading/trailing colon. -/
  | malformed : QNameSplit
deriving DecidableEq, Repr, Inhabited

/-- An expanded name — Namespaces in XML §2.1: a (namespace name,
local name) pair, where the namespace name is absent for a name in no
namespace. Unprefixed ATTRIBUTE names are never in the default
namespace (§6.2), so their expanded name always has `namespace = none`.
-/
structure ExpandedName where
  /-- The namespace name (an IRI), or `none` for no namespace. -/
  namespace_ : Option String
  /-- `[10] LocalPart`. -/
  localPart : String
deriving DecidableEq, Repr, Inhabited

/-! ## Convenience accessors

Port of the `Convenience accessors` section of F* `Parser.XML.fst`. -/

/-- The tag of an element node; `none` for every other node kind.
Port of F* `element_tag`. -/
def Node.elementTag : Node → Option String
  | .element tag _ _ => some tag
  | _ => none

/-- The attributes of an element node; `[]` for every other node kind.
Port of F* `element_attrs`. -/
def Node.elementAttrs : Node → List Attribute
  | .element _ attrs _ => attrs
  | _ => []

/-- The children of an element node; `[]` for every other node kind.
Port of F* `element_children`. -/
def Node.elementChildren : Node → List Node
  | .element _ _ cs => cs
  | _ => []

/-- The value of the attribute named `name`, if present.
Port of F* `find_attr`. -/
def findAttr (name : String) (attrs : List Attribute) : Option String :=
  (attrs.find? (fun a => a.name == name)).map (·.value)

/-- True when some attribute in the list carries `name`.
Port of F* `has_attr` (`XML.Wellformedness`) / `mem_attr_name`. -/
def hasAttr (name : String) (attrs : List Attribute) : Bool :=
  attrs.any (fun a => a.name == name)

mutual

/-- The string-value of a node: the concatenation of all `[14] CharData`
and `[18] CDSect` descendants, in document order. Comments and
processing instructions contribute nothing. Port of F* `text_content`. -/
def Node.textContent : Node → String
  | .text t => t
  | .cdata t => t
  | .comment _ => ""
  | .pi _ _ => ""
  | .element _ _ children => Node.textContentList children

/-- `Node.textContent` mapped over a child list and concatenated.
Port of F* `text_content_list` (which returns the list; folding it is
what the single F* caller does). -/
def Node.textContentList : List Node → String
  | [] => ""
  | c :: rest => Node.textContent c ++ Node.textContentList rest

end

/-- The element children of `node` whose tag is `tag`.
Port of F* `child_elements`. -/
def Node.childElements (tag : String) (node : Node) : List Node :=
  node.elementChildren.filter (fun c => c.elementTag == some tag)

/-- The first element child of `node` tagged `tag`, if any.
Port of F* `child_element`. -/
def Node.childElement (tag : String) (node : Node) : Option Node :=
  (node.childElements tag).head?

/-- Every element child of `node`, whatever its tag.
Port of F* `all_child_elements`. -/
def Node.allChildElements (node : Node) : List Node :=
  node.elementChildren.filter (fun c => c.elementTag.isSome)

end L4Factoidal.XML
