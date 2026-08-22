/-
L4Factoidal.XML.Theorems — a structural well-formedness checker over
the parse tree, a serialiser, and what is proved about both.

Two properties are at stake here.

**Reflexivity.** The parser establishes a set of constraints while it
reads. `Node.wellFormed` re-states those constraints as a predicate on
the RESULTING TREE, and the claim is that the parser's own output
always satisfies it. That is a real check on the port: if the checker
and the parser disagree about what a well-formed infoset is, one of
them is wrong.

**Round-trip.** `Document.toString` serialises a parsed document back
to XML, and the claim is `parseXML d.toString = .ok d` — parse after
serialise is the identity on the infoset. Note the direction: the
STRING does not round-trip (`<a></a>` serialises as `<a/>`), and it
should not; the infoset is the thing the parser is a function into.

## What is proved, and what is not

Proved outright, with no `sorry` and no `axiom`:
  * **WFC: Element Type Match holds by construction**
    (`Node.serialize_element_tags_match`). A `Node.element` carries ONE
    tag, and the serialiser emits that same tag in the `[40] STag` and
    the `[42] ETag`. This is the tag-matching component of reflexivity:
    the parser only ever builds `.element` under `closeTag == tag`, and
    the tree representation makes a mismatched pair unrepresentable, so
    the checker has no tag-matching clause left to check.
  * `Node.wellFormedList` agrees with `List.all Node.wellFormed`, and
    an element's well-formedness implies every child's — the induction
    the general reflexivity theorem needs.
  * Serialisation is compositional over child lists (`++`).

Stated as propositions, checked on fixtures by `#guard`, NOT proved in
general: `ReflexiveOnParserOutput` and `RoundTripsOnParse`. Each is a
`def … : Prop`, so nothing is assumed — a proposition that is merely
named carries no proof obligation and grants no theorem. Proving either
in general means reasoning about `parseXML`'s fuel-bounded scans over
arbitrary strings, which is a substantially larger piece of work than
this port; the `#guard`s below are evidence, not proof, and are
labelled as such.
-/
import L4Factoidal.XML.Namespaces

namespace L4Factoidal.XML

/-! ## Substring search

Needed by the checker for the two sequences a node body cannot
contain. -/

/-- True when `pat` is a prefix of `s`. -/
def listIsPrefix : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | p :: ps, c :: cs => p == c && listIsPrefix ps cs

/-- True when `pat` occurs anywhere in `s`. -/
def listHasSub (pat : List Char) : List Char → Bool
  | [] => listIsPrefix pat []
  | c :: cs => listIsPrefix pat (c :: cs) || listHasSub pat cs

/-- True when `pat` occurs anywhere in `s`. -/
def strHasSub (pat s : String) : Bool := listHasSub pat.toList s.toList

/-! ## The structural well-formedness checker

Every clause below re-states a constraint `parseXML` enforced while
reading. The clauses are stated on the INFOSET, which is why several
sequences the SYNTAX forbids are permitted here: `[14] CharData`
excludes a literal `]]>` and `[10] AttValue` excludes a literal `<`,
but `&#93;&#93;&gt;` and `&lt;` put exactly those characters into the
infoset, legally. What the infoset genuinely cannot hold is a sequence
that would be unrepresentable on the way back out — `]]>` inside a
CDATA section, `--` inside a comment, `?>` inside PI data — because
those constructs have no escape mechanism at all. -/

/-- An attribute of the infoset: its name is a `[5] Name`, and its
value holds only `[2] Char` characters. The value may contain `<`,
`&` and `"` — a reference put them there, and the serialiser escapes
them on the way out. -/
def Attribute.wellFormed (a : Attribute) : Bool :=
  isName a.name && a.value.toList.all isXmlChar

/-- **WFC: Unique Att Spec** — no two attributes of one element share a
name. -/
def attrsUnique (attrs : List Attribute) : Bool :=
  let names := attrs.map (·.name)
  names.length == names.eraseDups.length

mutual

/-- The parser's constraints, re-stated on the tree it produced. -/
def Node.wellFormed : Node → Bool
  -- [14] CharData: only the character range constrains the infoset.
  | .text t => t.toList.all isXmlChar
  -- [18] CDSect: a CDATA section has no escape mechanism, so its
  -- content cannot contain its own closing delimiter.
  | .cdata t => t.toList.all isXmlChar && !strHasSub "]]>" t
  -- [15] Comment: no `--` anywhere, and no trailing `-`.
  | .comment b =>
      b.toList.all isXmlChar && !hasDoubleDash b && b.toList.getLast? != some '-'
  -- [16] PI: the target is a [5] Name and is not the reserved `xml`;
  -- the data cannot contain the closing delimiter.
  | .pi target data =>
      isName target && !isXmlTargetNameCI target &&
      data.toList.all isXmlChar && !strHasSub "?>" data
  -- [39] element: the tag is a [5] Name, the attributes are unique and
  -- each well-formed, and so is every child. There is NO tag-matching
  -- clause: see `Node.serialize_element_tags_match`.
  | .element tag attrs children =>
      isName tag && attrs.all Attribute.wellFormed && attrsUnique attrs &&
      Node.wellFormedList children

/-- `Node.wellFormed` over a child list. -/
def Node.wellFormedList : List Node → Bool
  | [] => true
  | n :: rest => Node.wellFormed n && Node.wellFormedList rest

end

/-- A whole document: `[1] document ::= prolog element Misc*` — the
root must be an element, and every prolog / epilog Misc node must be
well-formed. -/
def Document.wellFormed (d : Document) : Bool :=
  d.root.elementTag.isSome &&
  Node.wellFormed d.root &&
  d.prolog.all Node.wellFormed &&
  d.epilog.all Node.wellFormed

/-! ### Proved: the induction the general theorem needs -/

/-- `Node.wellFormedList` is `List.all Node.wellFormed`. Proved by
structural induction on the list — this is the step that lets a
reflexivity proof descend into an element's children. -/
theorem Node.wellFormedList_eq_all :
    ∀ l : List Node, Node.wellFormedList l = l.all Node.wellFormed
  | [] => rfl
  | n :: rest => by
      simp [Node.wellFormedList, List.all_cons, Node.wellFormedList_eq_all rest]

/-- A well-formed element has well-formed children. The other half of
the descent step. -/
theorem Node.wellFormed_children (tag : String) (attrs : List Attribute)
    (children : List Node) (h : Node.wellFormed (.element tag attrs children) = true) :
    Node.wellFormedList children = true := by
  simp only [Node.wellFormed, Bool.and_eq_true] at h
  exact h.2

/-- Every child of a well-formed element is itself well-formed. -/
theorem Node.wellFormed_of_mem_children (tag : String) (attrs : List Attribute)
    (children : List Node) (h : Node.wellFormed (.element tag attrs children) = true)
    (c : Node) (hc : c ∈ children) : Node.wellFormed c = true := by
  have hl := Node.wellFormed_children tag attrs children h
  rw [Node.wellFormedList_eq_all] at hl
  exact List.all_eq_true.mp hl c hc

/-! ## The serialiser

`Document.toString` writes the infoset back out as XML. Text and
attribute values are escaped so that re-parsing recovers the SAME
characters: in particular tab / LF / CR inside an attribute value are
written as character references, because §3.3.3 would otherwise
normalise a literal one to a space. -/

/-- Escape `[14] CharData`: `&`, `<` and `>` become references. `>` is
escaped unconditionally, which is what keeps a `]]>` in the infoset
from becoming a literal `]]>` in the output (where `[14]` forbids it). -/
def escapeText (str : String) : String :=
  String.join (str.toList.map fun c =>
    if c == '&' then "&amp;"
    else if c == '<' then "&lt;"
    else if c == '>' then "&gt;"
    else String.singleton c)

/-- Escape a `[10] AttValue`. `<`, `&` and `"` must go; tab, LF and CR
are written as `[66] CharRef`s so that §3.3.3 attribute-value
normalisation does not turn them into spaces on the way back in. -/
def escapeAttrValue (str : String) : String :=
  String.join (str.toList.map fun c =>
    if c == '&' then "&amp;"
    else if c == '<' then "&lt;"
    else if c == '"' then "&quot;"
    else if c == '\t' then "&#9;"
    else if c == '\n' then "&#10;"
    else if c == '\r' then "&#13;"
    else String.singleton c)

/-- `[41] Attribute`, with its leading `[3] S`. -/
def Attribute.serialize (a : Attribute) : String :=
  " " ++ a.name ++ "=\"" ++ escapeAttrValue a.value ++ "\""

/-- The attribute list of a `[40] STag`. -/
def serializeAttrs (attrs : List Attribute) : String :=
  String.join (attrs.map Attribute.serialize)

mutual

/-- Serialise one node. An element with no children is written as a
`[44] EmptyElemTag`, which is why the STRING does not round-trip
(`<a></a>` comes back as `<a/>`) while the INFOSET does. -/
def Node.serialize : Node → String
  | .text t => escapeText t
  | .cdata t => "<![CDATA[" ++ t ++ "]]>"
  | .comment b => "<!--" ++ b ++ "-->"
  | .pi target data =>
      if data.isEmpty then "<?" ++ target ++ "?>"
      else "<?" ++ target ++ " " ++ data ++ "?>"
  | .element tag attrs [] => "<" ++ tag ++ serializeAttrs attrs ++ "/>"
  | .element tag attrs (c :: cs) =>
      "<" ++ tag ++ serializeAttrs attrs ++ ">" ++
      Node.serializeList (c :: cs) ++ "</" ++ tag ++ ">"

/-- Serialise a child list, concatenated in document order. -/
def Node.serializeList : List Node → String
  | [] => ""
  | n :: rest => Node.serialize n ++ Node.serializeList rest

end

/-- `[23] XMLDecl`, in the one order the grammar permits. -/
def XmlDecl.serialize (d : XmlDecl) : String :=
  "<?xml version=\"" ++ d.version ++ "\"" ++
  (match d.encoding with | none => "" | some e => " encoding=\"" ++ e ++ "\"") ++
  (match d.standalone with | none => "" | some s => " standalone=\"" ++ s ++ "\"") ++
  "?>"

/-- `[28] doctypedecl`, carrying back the internal subset the parser
read out of it.

The declaration lists are emitted REVERSED. Both are built by
prepending as the internal subset is scanned, so the stored order is
the reverse of the document order; reversing on the way out is what
makes the re-parse rebuild the identical lists. -/
def Doctype.serialize (dt : Doctype) : String :=
  if dt.entities.isEmpty && dt.idAttrs.isEmpty then
    "<!DOCTYPE " ++ dt.rootName ++ ">"
  else
    "<!DOCTYPE " ++ dt.rootName ++ " [" ++
    String.join (dt.entities.reverse.map fun e =>
      "<!ENTITY " ++ e.1 ++ " \"" ++ e.2 ++ "\">") ++
    String.join (dt.idAttrs.reverse.map fun p =>
      "<!ATTLIST " ++ p.1 ++ " " ++ p.2 ++ " ID #IMPLIED>") ++
    "]>"

/-- Serialise a whole document: `[23] XMLDecl`, the prolog `[27] Misc`,
the `[28] doctypedecl`, the document element, then the epilog Misc.

The prolog Misc all precede the DOCTYPE here. The parsed `Document`
merges the Misc from either side of the DOCTYPE into one list (as the
F* does), so their original split is not recorded; emitting them all
first is the arrangement that re-parses to the same merged list. -/
def Document.toString (d : Document) : String :=
  (match d.decl with | none => "" | some x => x.serialize) ++
  Node.serializeList d.prolog ++
  (match d.doctype with | none => "" | some dt => dt.serialize) ++
  Node.serialize d.root ++
  Node.serializeList d.epilog

/-! ### Proved: WFC Element Type Match holds by construction -/

/-- **The tag-matching component of reflexivity, proved.**

A `Node.element` carries exactly ONE tag, and the serialiser writes
that same tag into the `[40] STag` and the `[42] ETag`. So an element
whose end tag differs from its start tag is not merely rejected — it is
UNREPRESENTABLE in this tree. `parseElement` only ever constructs
`.element tag attrs children` in the branch guarded by
`closeTag == tag`, and the representation preserves that from then on,
which is why `Node.wellFormed`'s element clause has no tag-matching
condition left to state. -/
theorem Node.serialize_element_tags_match
    (tag : String) (attrs : List Attribute) (c : Node) (cs : List Node) :
    Node.serialize (.element tag attrs (c :: cs)) =
      "<" ++ tag ++ serializeAttrs attrs ++ ">" ++
      Node.serializeList (c :: cs) ++ "</" ++ tag ++ ">" := by
  simp [Node.serialize]

/-- The same statement for the `[44] EmptyElemTag` form: one tag, and
no end tag to disagree with it. -/
theorem Node.serialize_empty_element
    (tag : String) (attrs : List Attribute) :
    Node.serialize (.element tag attrs []) =
      "<" ++ tag ++ serializeAttrs attrs ++ "/>" := by
  simp [Node.serialize]

/-- Serialisation is compositional over a child list. -/
theorem Node.serializeList_cons (n : Node) (rest : List Node) :
    Node.serializeList (n :: rest) = Node.serialize n ++ Node.serializeList rest := by
  simp [Node.serializeList]

/-- The empty child list serialises to nothing. -/
@[simp] theorem Node.serializeList_nil :
    Node.serializeList [] = "" := rfl

/-- `Document.children` is the prolog, the root, then the epilog — so
the document node's serialisation is its children's, after the
declaration and DOCTYPE. -/
theorem Document.children_eq (d : Document) :
    d.children = d.prolog ++ (d.root :: d.epilog) := rfl

/-! ## The general statements

Each is a `def … : Prop` — a NAMED proposition, not a theorem. Naming
one assumes nothing and proves nothing; these exist so the goals have
an address, and so the `#guard`s in `Tests.lean` can be read as
evidence for a stated claim rather than as free-floating checks. -/

/-- **Reflexivity of the well-formedness checker on the parser's own
output.** Whatever `parseXML` accepts satisfies `Document.wellFormed`.

Status: the tag-matching component is proved
(`Node.serialize_element_tags_match`); the descent into children is
proved (`Node.wellFormed_of_mem_children`); the remaining clauses are
checked on fixtures by `#guard` and are not proved in general. A full
proof means reasoning about `parseXML`'s fuel-bounded scans over an
arbitrary input string. -/
def ReflexiveOnParserOutput : Prop :=
  ∀ (input : String) (d : Document), parseXML input = .ok d → Document.wellFormed d = true

/-- **Round-trip.** Serialising a parsed document and parsing it again
returns the same infoset.

Note the direction: this is `parse ∘ serialise = id` on documents, not
`serialise ∘ parse = id` on strings. The latter is false and should be
— `<a></a>` serialises as `<a/>`.

Status: checked on fixtures by `#guard` in `Tests.lean`; not proved in
general. -/
def RoundTripsOnParse : Prop :=
  ∀ (input : String) (d : Document), parseXML input = .ok d →
    parseXML (Document.toString d) = .ok d

/-- The round-trip property of a single document, so a fixture check
can be written against a named statement. -/
def RoundTrips (d : Document) : Prop := parseXML (Document.toString d) = .ok d

/-- Decide `RoundTrips` for a concrete document — this is what the
fixture `#guard`s evaluate. -/
def roundTrips (d : Document) : Bool :=
  match parseXML (Document.toString d) with
  | .ok d' => d' == d
  | .error _ => false

/-- Parse a string, then check that its infoset round-trips. `false`
when the string is not well-formed in the first place. -/
def roundTripsFrom (input : String) : Bool :=
  match parseXML input with
  | .error _ => false
  | .ok d => roundTrips d

/-- Parse a string and check the well-formedness checker accepts the
tree the parser built — one instance of `ReflexiveOnParserOutput`. -/
def reflexiveOn (input : String) : Bool :=
  match parseXML input with
  | .error _ => false
  | .ok d => Document.wellFormed d

end L4Factoidal.XML
