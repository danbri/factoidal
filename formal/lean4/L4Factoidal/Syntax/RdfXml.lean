/-
L4Factoidal.Syntax.RdfXml — the RDF/XML grammar, as a total function
from an XML infoset to an RDF graph.

Port of `formal/fstar/Parser.RDFXML.fst` (F*) to Lean 4, together with
the RDF/XML-specific well-formedness rules of
`formal/fstar/XML.Wellformedness.fst`. Production numbers cite
**RDF 1.1 XML Syntax**, W3C Recommendation 25 February 2014,
https://www.w3.org/TR/rdf-syntax-grammar/ . Section numbers of the form
§7.2.N are that document's grammar productions.

This module is a GRAMMAR WALK, not a character parser: the XML layer
(`L4Factoidal.XML.Parser`) has already produced the infoset, and the
namespace layer (`L4Factoidal.XML.Namespaces`) already knows how to turn
a raw `[5] Name` into an expanded name. What is left is §7.2 — which
element is a node element, which is a property element, what triples
each licenses.

Productions implemented (each cited at its definition below):
  [7.2.2]  doc                          [7.2.17] parseTypeLiteralPropertyElt
  [7.2.8]  RDF                          [7.2.18] parseTypeResourcePropertyElt
  [7.2.9]  nodeElementList              [7.2.19] parseTypeCollectionPropertyElt
  [7.2.11] nodeElement                  [7.2.20] parseTypeOtherPropertyElt
  [7.2.13] propertyEltList              [7.2.21] emptyPropertyElt
  [7.2.14] propertyElt                  [7.2.23] idAttr
  [7.2.15] resourcePropertyElt          [7.2.24] nodeIdAttr
  [7.2.16] literalPropertyElt           [7.2.25] aboutAttr
  [7.2.26] propertyAttr / [7.2.30]-[7.2.31] resourceAttr, datatypeAttr
  §7.3     reification of a property element carrying `rdf:ID`
  §5.3     `rdf:li` ↦ `rdf:_n` (per-node-element counter)
  XML Base §3.3 / RFC 3986 §5 base resolution, `xml:lang` inheritance.

RDF 1.2 additions (RDF 1.2 XML Syntax, the `rdf12/rdf-xml` suite), each
cited at its definition:
  `rdf:version="1.2"`      the feature switch, inherited by descendants
  `its:dir`                base direction (ITS 2.0), inherited like `xml:lang`
  `rdf:parseType="Triple"` a triple term as the property's object
  `rdf:annotation` / `rdf:annotationNodeID`
                           a reifier: `<r> rdf:reifies <<( s p o )>>`
They are unconditional except the triple term, which the F* source gates
on `rdf:version="1.2"` and this port gates the same way.

Deliberately NOT ported:
  * the F* source's "a datatyped property element with element children
    is an opaque XML literal" leniency, which exists for OWL fixtures
    outside the RDF/XML suite and has no production in §7.2.

**Where this port is namespace-correct and the F* source is not.**
`Parser.RDFXML.fst` looks attributes up by their LITERAL spelling
(`find_attr "rdf:about"`) against a namespace map seeded with five
default prefix bindings, so it reads `rdf:about` on a document that
never declared `rdf`, and misses `foo:about` on one that bound `foo` to
the RDF namespace. This port resolves every element and attribute name
through `XML.resolveElementName` / `XML.resolveAttributeName` against
the real in-scope bindings, which is what "Namespaces in XML" and
RDF/XML §6 require. See PORT_NOTES.md.

**Errors.** The F* threads a `has_error` flag through its state and the
strict entry point turns it into `None`. This port threads the first
`ParseError` instead, so a rejection says WHICH rule was violated.
Triples found before the error are discarded, exactly as
`parse_rdfxml_strict` discards them.

Assumption report: `Parser.RDFXML.fst` is PURE — no `assume val`, no
effectful call-out. Every function in it is `Tot`, fuel-bounded where
F* could not see termination. This port needs no purity workaround.
-/
import L4Factoidal.XML.Parser
import L4Factoidal.XML.Namespaces
import L4Factoidal.XML.Wellformedness
import L4Factoidal.RDF.Core
import L4Factoidal.RDF.Graph
import L4Factoidal.Syntax.IriResolve
import L4Factoidal.Syntax.Lexing

namespace L4Factoidal.Syntax.RdfXml

open L4Factoidal.RDF

/-! ## Vocabulary

The RDF namespace and the terms §7.2 names. `WfIri` witnesses are `rfl`
(kernel evaluation of `RDF.isIri`), the Lean counterpart of the F*
`assert_norm (is_iri "…")`. -/

/-- The RDF namespace name (RDF 1.1 Concepts §1.4). -/
def rdfNs : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"

/-- The full IRI of the RDF term with local name `localName`. -/
def rdfTerm (localName : String) : String := rdfNs ++ localName

def rdfTypeIri      : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#type", rfl⟩
def rdfFirstIri     : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#first", rfl⟩
def rdfRestIri      : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#rest", rfl⟩
def rdfNilIri       : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#nil", rfl⟩
def rdfStatementIri : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#Statement", rfl⟩
def rdfSubjectIri   : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#subject", rfl⟩
def rdfPredicateIri : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#predicate", rfl⟩
def rdfObjectIri    : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#object", rfl⟩

/-- RDF 1.2's reifier property, the object of an `rdf:annotation` /
`rdf:annotationNodeID` reifier triple. -/
def rdfReifiesIri   : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies", rfl⟩

/-- The ITS 2.0 namespace name. RDF 1.2 XML Syntax borrows `its:dir`
from Internationalization Tag Set 2.0 to carry a literal's base
direction, the way it borrows `xml:lang` for the language tag. -/
def itsNs : String := "http://www.w3.org/2005/11/its"

/-- Attribute local names in the RDF namespace that §7.2 CONSUMES: they
control the grammar and never become `[7.2.26] propertyAttr` triples.
`rdf:type` is deliberately absent — it IS a property attribute, with an
IRI object rather than a literal one (§7.2.26 note).

The last three are RDF 1.2's: `rdf:version` announces the version and
`rdf:annotation` / `rdf:annotationNodeID` name a reifier, so all three
are consumed here. Excluding `rdf:annotation` is also what lets an
empty property element carrying only that attribute fall through to the
empty-literal case rather than the blank-node-object case — the F*
source's `is_rdf_syntax_attr` carries the same note, naming
`rdf12-xml-an-04`…`-12`. -/
def rdfSyntaxAttrNames : List String :=
  ["about", "ID", "resource", "datatype", "nodeID", "parseType",
   "bagID", "aboutEach", "aboutEachPrefix", "li", "RDF", "Description",
   "version", "annotation", "annotationNodeID"]

/-! ## Well-formed-term constructors

`Triple.p`, `Term.iri` and `Term.literal` carry proofs, so every
construction from a runtime string is an `Option`. -/

/-- A `WfIri` from a string, or `none` when `RDF.isIri` rejects it. -/
def mkIri? (s : String) : Option WfIri :=
  if h : RDF.isIri s = true then some ⟨s, h⟩ else none

/-- A typed literal. `none` for `rdf:langString` / `rdf:dirLangString`,
which are not expressible without a language tag — port of the F*
`make_typed_literal` guard. -/
def mkTypedLiteral? (lex : String) (dt : WfIri) : Option WfLiteral :=
  let l : Literal :=
    { lexicalForm := lex, datatype := dt, langTag := none, direction := none }
  if h : RDF.literalWf l = true then some ⟨l, h⟩ else none

/-- A plain literal: `xsd:string` with no language, `rdf:langString`
with one, and (RDF 1.2) `rdf:dirLangString` with a language AND a base
direction. A direction with no language tag is ill-formed, so it is
dropped rather than made into an unrepresentable literal. Port of
`make_plain_literal`. -/
def mkPlainLiteral (lex : String) (lang : Option String)
    (dir : Option TextDirection := none) : WfLiteral :=
  match lang, dir with
  | none,   _      => Literal.string lex
  | some l, none   => Literal.langString lex l
  | some l, some d => Literal.dirLangString lex l d

/-! ## Blank-node labels

The F* mints `rdfxml_b<N>` from a document-scoped counter and uses an
`rdf:nodeID` value verbatim, so a document containing
`rdf:nodeID="rdfxml_b0"` can collide with a generated label. Blank-node
labels are document-local and graph identity is up to renaming
(RDF 1.1 Concepts §3.4), so this port simply puts the two in disjoint
label spaces — see `genLabel_ne_nodeIdLabel` in RdfXmlTheorems.lean. -/

/-- The label of the `n`-th generated blank node. -/
def genLabel (n : Nat) : BNodeId := "b" ++ toString n

/-- The label denoted by `[7.2.24] nodeIdAttr` value `x`. -/
def nodeIdLabel (x : String) : BNodeId := "n" ++ x

/-! ## Parser state

Port of F* `rdfxml_state`. `scope` replaces the F*'s hand-rolled
prefix→IRI list with the real "Namespaces in XML" scope; `err` replaces
the `has_error : bool` flag with the violated rule. -/

/-- The information §7.2 productions read from their context. -/
structure St where
  /-- The in-scope base IRI (XML Base §3), already fragment-stripped. -/
  base : String
  /-- The in-scope namespace bindings (Namespaces in XML §3). -/
  scope : XML.NsScope
  /-- The inherited `xml:lang`, `none` when none is in scope or the
  nearest one is `xml:lang=""`. -/
  lang : Option String
  /-- Next generated blank-node number. Document-scoped: it must NOT be
  restored when an element's scope closes, or two siblings mint the same
  label. -/
  bnodeCounter : Nat
  /-- Next `rdf:li` ordinal (§5.3). Scoped to ONE node element: nesting
  must not corrupt the parent's numbering (the F* comment names
  rdf-containers-syntax-vs-schema test004 / test007 as the regression). -/
  liCounter : Nat
  /-- RDF 1.2: the inherited `its:dir` base direction (ITS 2.0),
  `none` when none is in scope or the nearest one is `its:dir=""`.
  XML-scoped, exactly like `lang`. -/
  dir : Option TextDirection := none
  /-- RDF 1.2: has an ancestor (or this element) said
  `rdf:version="1.2"`? The switch flows DOWN to descendants and is
  restored for siblings by `restoreScope`, like the other XML-scoped
  fields. Only `rdf:parseType="Triple"` is gated on it; `its:dir` and
  the annotation reifiers are not (the F* source gates the same way). -/
  sawVersion12 : Bool := false
  /-- Resolved `[7.2.23] idAttr` keys seen so far. Document-scoped —
  §7.2.23's uniqueness constraint is per base IRI over the whole
  document. -/
  seenIds : List String
  /-- The FIRST rule violation found, if any. -/
  err : Option ParseError
  deriving DecidableEq, Repr

/-- The initial state for a document retrieved from `base`. -/
def St.init (base : String) : St :=
  { base := base, scope := XML.initialScope, lang := none,
    dir := none, sawVersion12 := false,
    bnodeCounter := 0, liCounter := 1, seenIds := [], err := none }

/-- Record a rule violation. The FIRST one wins, so the reported error
is the outermost/earliest, not the last one encountered. -/
def St.fail (st : St) (msg : String) : St :=
  match st.err with
  | some _ => st
  | none   => { st with err := some { msg := msg, pos := 0 } }

/-- Mint a fresh blank node (§7.2.11's "neither `rdf:ID` nor
`rdf:about` nor `rdf:nodeID`" case, and the implicit nodes of
§7.2.18 / §7.2.19 / §7.2.21). -/
def St.freshBnode (st : St) : BNodeId × St :=
  (genLabel st.bnodeCounter, { st with bnodeCounter := st.bnodeCounter + 1 })

/-- The next `rdf:li` ordinal, and the state with the counter advanced
(§5.3). -/
def St.nextLi (st : St) : Nat × St :=
  (st.liCounter, { st with liCounter := st.liCounter + 1 })

/-- Open a fresh `rdf:li` numbering scope — done on entry to every node
element and every `rdf:parseType="Resource"` group. -/
def St.resetLi (st : St) : St := { st with liCounter := 1 }

/-- Close a child's scope: `base` / `scope` / `lang` / `dir` /
`sawVersion12` / `liCounter` are XML-scoped and revert to the parent's;
`bnodeCounter` / `seenIds` / `err` are document-scoped and flow out.
Port of F* `restore_scope`. -/
def restoreScope (parent child : St) : St :=
  { parent with
    bnodeCounter := child.bnodeCounter,
    seenIds := child.seenIds,
    err := match parent.err with | some e => some e | none => child.err }

/-! ## Reading the context off an element

Namespace declarations, `xml:base` and `xml:lang` are XML-scoped: they
apply to the element carrying them and its descendants, never to its
siblings. -/

/-- The value of the attribute whose EXPANDED name is `(ns, localName)`.
Namespace-correct, unlike the F* `find_attr "rdf:about"`. -/
def findNsAttr (st : St) (ns localName : String) (attrs : List XML.Attribute) :
    Option String :=
  (attrs.find? (fun a =>
    match XML.resolveAttributeName st.scope a.name with
    | some e => e.namespace_ == some ns && e.localPart == localName
    | none   => false)).map (·.value)

/-- An attribute in the RDF namespace, by local name. -/
def findRdfAttr (st : St) (localName : String) (attrs : List XML.Attribute) :
    Option String :=
  findNsAttr st rdfNs localName attrs

/-- An attribute in the XML namespace (`xml:base`, `xml:lang`). -/
def findXmlAttr (st : St) (localName : String) (attrs : List XML.Attribute) :
    Option String :=
  findNsAttr st XML.xmlNsUri localName attrs

/-- Is an RDF-namespace attribute with this local name present? -/
def hasRdfAttr (st : St) (localName : String) (attrs : List XML.Attribute) : Bool :=
  (findRdfAttr st localName attrs).isSome

/-- XML Base §3.3 / RFC 3986 §5.1: a base IRI carries no fragment
identifier, so an authored `xml:base` value containing one has it
discarded. -/
def stripFragment (s : String) : String :=
  match s.splitOn "#" with
  | []     => s
  | h :: _ => h

/-- Apply this element's `xmlns` / `xmlns:*` declarations. A declaration
that is itself illegal (a reserved prefix or reserved namespace name)
is a namespace well-formedness violation, not an RDF question, but it
makes every name on the element meaningless — so it is reported here. -/
def updateScope (st : St) (attrs : List XML.Attribute) : St :=
  match XML.applyDeclarations "1.0" st.scope attrs with
  | some sc => { st with scope := sc }
  | none    => st.fail "illegal xmlns declaration (Namespaces in XML §3)"

/-- XML Base §3: resolve this element's `xml:base` against the base
already in scope, then strip any fragment. -/
def updateBase (st : St) (attrs : List XML.Attribute) : St :=
  match findXmlAttr st "base" attrs with
  | some b => { st with base := stripFragment (resolveIri st.base b) }
  | none   => st

/-- XML §2.12: `xml:lang` applies to the element and its descendants;
`xml:lang=""` CLEARS the inherited value rather than setting an empty
one. Absent, the parent's value is inherited unchanged — this is the
clause `lang_inherited_when_absent` states. -/
def updateLang (st : St) (attrs : List XML.Attribute) : St :=
  match findXmlAttr st "lang" attrs with
  | some l => if l.isEmpty then { st with lang := none } else { st with lang := some l }
  | none   => st

/-- RDF 1.2 XML Syntax: `its:dir` (ITS 2.0) carries a literal's base
direction the way `xml:lang` carries its language, and inherits the
same way. `its:dir="ltr"` / `"rtl"` set it, `its:dir=""` CLEARS it, and
any other value leaves the inherited value unchanged. Port of
`extract_dir`. -/
def updateDir (st : St) (attrs : List XML.Attribute) : St :=
  match findNsAttr st itsNs "dir" attrs with
  | some d =>
      if d == "ltr" then { st with dir := some .ltr }
      else if d == "rtl" then { st with dir := some .rtl }
      else if d.isEmpty then { st with dir := none }
      else st
  | none => st

/-- RDF 1.2 XML Syntax: `rdf:version="1.2"` switches the version-gated
features on for this element and its descendants. Any other value
leaves the inherited setting alone (it never switches 1.2 back off).
Port of `extract_version`. -/
def updateVersion (st : St) (attrs : List XML.Attribute) : St :=
  match findRdfAttr st "version" attrs with
  | some v => if v == "1.2" then { st with sawVersion12 := true } else st
  | none   => st

/-- All the scoped updates, in the order the later ones depend on:
declarations first (they decide what `xml:base` even resolves to as a
name), then base, then language, then the two RDF 1.2 ones (`its:dir`
and `rdf:version`, both of which need the declarations resolved).
Port of `update_state_from_attrs`. -/
def updateState (st : St) (attrs : List XML.Attribute) : St :=
  updateVersion (updateDir (updateLang (updateBase (updateScope st attrs) attrs) attrs) attrs) attrs

/-- The base direction that actually applies: RDF 1.2's, and only when
`rdf:version="1.2"` is in scope. Port of `effective_dir`. -/
def St.effectiveDir (st : St) : Option TextDirection :=
  if st.sawVersion12 then st.dir else none

/-- Resolve a relative reference against the in-scope base
(RFC 3986 §5). Definitionally `Syntax.resolveIri` — see
`resolveRef_eq_resolveIri`. -/
def resolveRef (st : St) (r : String) : String := resolveIri st.base r

/-- The expanded name of an element tag, flattened to the full IRI §7.2
compares against. `none` when the prefix is unbound or the name is not
a QName. -/
def elementIri (st : St) (tag : String) : Option String :=
  match XML.resolveElementName st.scope tag with
  | some e => some ((e.namespace_.getD "") ++ e.localPart)
  | none   => none

/-! ## `[7.2.26] propertyAttr`

An attribute that is not a namespace declaration, not in the XML
namespace, and not one of the RDF-namespace names §7.2 consumes,
licenses one triple whose object is a plain literal of the attribute
value — except `rdf:type`, whose object is the IRI the value resolves
to. -/

/-- Is `a` an `xmlns` / `xmlns:*` declaration? -/
def isNsDecl (a : XML.Attribute) : Bool :=
  match XML.splitQName a.name with
  | .simple "xmlns"     => true
  | .prefixed "xmlns" _ => true
  | _                   => false

/-- The triples licensed by the property attributes of one element,
attached to `subj`. Attributes in NO namespace (unprefixed, other than
the RDF/XML-specific ones) contribute nothing: §7.2.26 needs a URI, and
an unprefixed attribute name has no namespace (Namespaces in XML §6.2).
Port of `collect_property_attributes`. -/
def propertyAttrTriples (st : St) (subj : Subject) :
    List XML.Attribute → List Triple
  | [] => []
  | a :: rest =>
    let restTriples := propertyAttrTriples st subj rest
    if isNsDecl a then restTriples
    else
      match XML.resolveAttributeName st.scope a.name with
      | none => restTriples
      | some e =>
        match e.namespace_ with
        | none => restTriples                       -- no namespace: no predicate IRI
        | some ns =>
          if ns == XML.xmlNsUri then restTriples    -- xml:lang / xml:base / xml:space
          else if ns == rdfNs && rdfSyntaxAttrNames.contains e.localPart then restTriples
          else if ns == itsNs then restTriples      -- RDF 1.2: its:dir / its:version
          else
            let full := ns ++ e.localPart
            match mkIri? full with
            | none => restTriples
            | some p =>
              if full == rdfTypeIri.val then
                match mkIri? (resolveRef st a.value) with
                | some o => { s := subj, p := p, o := Term.iri o } :: restTriples
                | none   => restTriples
              else
                { s := subj, p := p,
                  o := Term.literal (mkPlainLiteral a.value st.lang st.effectiveDir) }
                  :: restTriples

/-! ## §7.2's attribute constraints

`XML/Wellformedness.lean` states these over LITERAL attribute spellings
(`"rdf:parseType"`), inherited from the F* module it ports. The
namespace-correct forms live here; see the "what XML/ should gain" note
in PORT_NOTES.md. The forbidden-element-name lists and the NCName
predicate ARE reused from `XML/Wellformedness.lean`, since those are
stated over full IRIs and over a bare string. -/

/-- Constraints common to `[7.2.11] nodeElement` and
`[7.2.14] propertyElt`: the withdrawn RDF 1.0 attributes are forbidden
outright, and `rdf:li` is an element name, never an attribute. -/
def checkCommonAttrs (st : St) (attrs : List XML.Attribute) : Option String :=
  if hasRdfAttr st "aboutEach" attrs then
    some "rdf:aboutEach was withdrawn from RDF (RDF/XML §5.1)"
  else if hasRdfAttr st "aboutEachPrefix" attrs then
    some "rdf:aboutEachPrefix was withdrawn from RDF (RDF/XML §5.1)"
  else if hasRdfAttr st "bagID" attrs then
    some "rdf:bagID was withdrawn from RDF 1.1 (RDF/XML §5.1)"
  else if hasRdfAttr st "li" attrs then
    some "rdf:li is an element name, not an attribute (RDF/XML §7.2.14)"
  else none

/-- `[7.2.11] nodeElement ::= ... (idAttr | nodeIdAttr | aboutAttr)? propertyAttr*`
— at most ONE of the three node-identifying attributes, and neither
`rdf:parseType` nor `rdf:resource`, which belong to property elements
only. -/
def checkNodeAttrs (st : St) (attrs : List XML.Attribute) : Option String :=
  match checkCommonAttrs st attrs with
  | some m => some m
  | none =>
    if hasRdfAttr st "parseType" attrs then
      some "rdf:parseType on a node element (RDF/XML §7.2.11)"
    else if hasRdfAttr st "resource" attrs then
      some "rdf:resource on a node element (RDF/XML §7.2.11)"
    else if hasRdfAttr st "datatype" attrs then
      some "rdf:datatype on a node element (RDF/XML §7.2.11)"
    else
      let n := (if hasRdfAttr st "ID" attrs then 1 else 0)
             + (if hasRdfAttr st "about" attrs then 1 else 0)
             + (if hasRdfAttr st "nodeID" attrs then 1 else 0)
      if n > 1 then
        some "a node element may carry at most one of rdf:ID, rdf:about, rdf:nodeID (RDF/XML §7.2.11)"
      else none

/-- `[7.2.14] propertyElt` constraints. `rdf:ID` here identifies the
STATEMENT (§7.3 reification), not the object, so it does not conflict
with `rdf:resource`; `rdf:nodeID` and `rdf:resource` both name the
object and do conflict. `rdf:parseType` excludes every other object
attribute. -/
def checkPropertyAttrs (st : St) (attrs : List XML.Attribute) : Option String :=
  match checkCommonAttrs st attrs with
  | some m => some m
  | none =>
    if hasRdfAttr st "nodeID" attrs && hasRdfAttr st "resource" attrs then
      some "conflicting rdf:nodeID and rdf:resource on a property element (RDF/XML §7.2.21)"
    else if hasRdfAttr st "parseType" attrs && hasRdfAttr st "resource" attrs then
      some "conflicting rdf:parseType and rdf:resource (RDF/XML §7.2.14)"
    else if hasRdfAttr st "parseType" attrs && hasRdfAttr st "nodeID" attrs then
      some "conflicting rdf:parseType and rdf:nodeID (RDF/XML §7.2.14)"
    else if hasRdfAttr st "parseType" attrs && hasRdfAttr st "datatype" attrs then
      some "conflicting rdf:parseType and rdf:datatype (RDF/XML §7.2.14)"
    else if hasRdfAttr st "datatype" attrs && hasRdfAttr st "resource" attrs then
      some "conflicting rdf:datatype and rdf:resource (RDF/XML §7.2.14)"
    else if hasRdfAttr st "about" attrs then
      some "rdf:about on a property element (RDF/XML §7.2.14)"
    else if hasRdfAttr st "parseType" attrs
            && !(propertyAttrTriples st (.bnode "probe") attrs).isEmpty then
      -- §7.2.17 / §7.2.18 / §7.2.19 each admit only `idAttr` and the
      -- `parseType` attribute itself; a `[7.2.26] propertyAttr` alongside
      -- one of them matches no production.
      some "a property attribute alongside rdf:parseType (RDF/XML §7.2.17)"
    else none

/-- `[7.2.23] idAttr` and `[7.2.24] nodeIdAttr` both take an `rdf-id`,
which is an XML `NCName`. -/
def checkIdNCNames (st : St) (attrs : List XML.Attribute) : Option String :=
  match findRdfAttr st "ID" attrs with
  | some v =>
    if XML.isValidNCName v then
      match findRdfAttr st "nodeID" attrs with
      | some n => if XML.isValidNCName n then none
                  else some s!"rdf:nodeID value is not an NCName: {n} (RDF/XML §7.2.24)"
      | none => none
    else some s!"rdf:ID value is not an NCName: {v} (RDF/XML §7.2.23)"
  | none =>
    match findRdfAttr st "nodeID" attrs with
    | some n => if XML.isValidNCName n then none
                else some s!"rdf:nodeID value is not an NCName: {n} (RDF/XML §7.2.24)"
    | none => none

/-! ## `[7.2.23] idAttr` — the resolved IRI and its uniqueness

"The value of `rdf:ID` … must not be used more than once in the scope of
one base URI" (§7.2.23 constraint). The key is the resolved IRI, which
already carries the base, so two identical `rdf:ID`s under DIFFERENT
`xml:base` values do not collide. -/

/-- Register an `rdf:ID` value and report whether it repeats. -/
def registerId (st : St) (idValue : String) : St :=
  let key := st.base ++ "#" ++ idValue
  if st.seenIds.contains key then
    st.fail s!"rdf:ID {idValue} is used twice under the same base (RDF/XML §7.2.23)"
  else { st with seenIds := key :: st.seenIds }

/-! ## §7.3 Reification

`rdf:ID` on a property element names the statement the element makes;
the parser adds the four triples that describe it. -/

/-- The four reification triples for statement IRI `r`. -/
def reificationTriples (r : WfIri) (s : Subject) (p : WfIri) (o : Term) : List Triple :=
  [ { s := .iri r, p := rdfTypeIri,      o := Term.iri rdfStatementIri },
    { s := .iri r, p := rdfSubjectIri,   o := s.toTerm },
    { s := .iri r, p := rdfPredicateIri, o := Term.iri p },
    { s := .iri r, p := rdfObjectIri,    o := o } ]

/-- The reification triples licensed by an optional statement IRI. -/
def reifyWith (r : Option WfIri) (s : Subject) (p : WfIri) (o : Term) : List Triple :=
  match r with
  | none   => []
  | some w => reificationTriples w s p o

/-! ### RDF 1.2 reifiers — `rdf:annotation` / `rdf:annotationNodeID`

RDF 1.2 XML Syntax's replacement for the §7.3 `rdf:ID` expansion: the
named reifier is asserted to `rdf:reifies` the TRIPLE TERM of the
statement the property element makes, one triple instead of four. The
two forms are exclusive alternatives — `rdf:annotation` names the
reifier by IRI, `rdf:annotationNodeID` by blank-node label — and
neither is version-gated (the F* source reads them unconditionally). A
property element may carry an `rdf:ID` reification AND an annotation
reifier; both are emitted. -/

/-- The reifier a property element names, if any. An `rdf:annotation`
value that does not resolve to an IRI names nothing. -/
def annotReifier (st : St) (attrs : List XML.Attribute) : Option Subject :=
  match findRdfAttr st "annotation" attrs with
  | some v => (mkIri? (resolveRef st v)).map Subject.iri
  | none   =>
    match findRdfAttr st "annotationNodeID" attrs with
    | some n => some (.bnode (nodeIdLabel n))
    | none   => none

/-- `<reifier> rdf:reifies <<( s p o )>>`, or nothing. -/
def annotTriples (r : Option Subject) (s : Subject) (p : WfIri) (o : Term) : List Triple :=
  match r with
  | none         => []
  | some reifier => [{ s := reifier, p := rdfReifiesIri, o := Term.tripleTerm s p o }]

/-- Both reification forms for one statement: the §7.3 `rdf:ID`
expansion and the RDF 1.2 reifier. Port of the F* `reif_of`. -/
def reifyAll (r : Option WfIri) (a : Option Subject) (s : Subject) (p : WfIri) (o : Term) :
    List Triple :=
  reifyWith r s p o ++ annotTriples a s p o

/-! ## `[7.2.17] parseTypeLiteralPropertyElt` — serialising the content

The object is a literal whose datatype is `rdf:XMLLiteral` and whose
lexical form is the exclusive canonical XML of the property element's
children (§7.2.17, referencing Exclusive XML Canonicalization). Two
canonical-form rules matter for the shape produced here:
  * an empty element is written open+close, never self-closing;
  * the top-level element(s) of the content carry the namespace
    declarations inherited from the enclosing document.
Attribute ORDER is also part of c14n, but it is not part of this
function's job: `RDF.XmlCanon` sorts attributes when it compares two
`rdf:XMLLiteral` values (RDF 1.1 §5.1 defines their value space that
way), so `Literal.eqb` — and therefore graph equality and isomorphism —
is already insensitive to it. `RDF.XmlCanon.canonTag` likewise expands
a self-closing tag, so the two rules above are belt and braces. -/

/-- §2.4 escaping for character data. -/
def escapeText (s : String) : String :=
  String.ofList (s.toList.flatMap (fun c =>
    if c == '&' then "&amp;".toList
    else if c == '<' then "&lt;".toList
    else if c == '>' then "&gt;".toList
    else [c]))

/-- §2.4 / §3.3.3 escaping inside a double-quoted attribute value. -/
def escapeAttrValue (s : String) : String :=
  String.ofList (s.toList.flatMap (fun c =>
    if c == '&' then "&amp;".toList
    else if c == '<' then "&lt;".toList
    else if c == '"' then "&quot;".toList
    else if c == '\t' then "&#x9;".toList
    else if c == '\n' then "&#xA;".toList
    else if c == '\r' then "&#xD;".toList
    else [c]))

/-- Keep the FIRST binding of each prefix — the scope list is ordered
innermost-first, so the first is the one actually in force. -/
def dedupScope : XML.NsScope → List String → XML.NsScope
  | [], _ => []
  | (p, u) :: rest, seen =>
    if seen.contains p then dedupScope rest seen
    else (p, u) :: dedupScope rest (p :: seen)

/-- The ambient namespace declarations, rendered as attribute fragments
for the top-level element(s) of `rdf:parseType="Literal"` content. The
`xml` prefix is bound without being declared (Namespaces in XML §3) and
is never emitted; an explicitly UNDECLARED prefix (`(p, none)`) has no
declaration to emit either. -/
def renderNsDecls (scope : XML.NsScope) : String :=
  String.join ((dedupScope scope []).filterMap (fun b =>
    match b with
    | (p, some u) =>
      if p == "xml" then none
      else if p.isEmpty then some (" xmlns=\"" ++ escapeAttrValue u ++ "\"")
      else some (" xmlns:" ++ p ++ "=\"" ++ escapeAttrValue u ++ "\"")
    | (_, none) => none))

/-- One element's own attributes, rendered. -/
def renderAttrs : List XML.Attribute → String
  | [] => ""
  | a :: rest => " " ++ a.name ++ "=\"" ++ escapeAttrValue a.value ++ "\"" ++ renderAttrs rest

mutual

/-- Serialise one node of `rdf:parseType="Literal"` content.
Canonical XML "without comments" drops comment nodes; a CDATA section is
replaced by its character content. `nsDecls` is emitted only on the
top-level elements (`isRoot`). -/
def serializeNode : Nat → String → Bool → XML.Node → String
  | 0, _, _, _ => ""
  | _ + 1, _, _, .text t    => escapeText t
  | _ + 1, _, _, .cdata t   => escapeText t
  | _ + 1, _, _, .comment _ => ""
  | _ + 1, _, _, .pi tgt d  => "<?" ++ tgt ++ (if d.isEmpty then "" else " " ++ d) ++ "?>"
  | fuel + 1, nsDecls, isRoot, .element tag attrs children =>
    "<" ++ tag ++ (if isRoot then nsDecls else "") ++ renderAttrs attrs ++ ">"
      ++ serializeNodes fuel nsDecls children
      ++ "</" ++ tag ++ ">"

/-- `serializeNode` over a child list; only the OUTERMOST call passes
`isRoot := true`. -/
def serializeNodes : Nat → String → List XML.Node → String
  | 0, _, _ => ""
  | _ + 1, _, [] => ""
  | fuel + 1, nsDecls, c :: rest =>
    serializeNode fuel nsDecls false c ++ serializeNodes fuel nsDecls rest

end

/-- The lexical form of the `rdf:XMLLiteral` a `[7.2.17]` property
element denotes. -/
def serializeLiteralContent (scope : XML.NsScope) (children : List XML.Node) : String :=
  let nsDecls := renderNsDecls scope
  String.join (children.map (fun c => serializeNode 10000 nsDecls true c))

/-! ## The grammar walk

`fuel` bounds the mutual recursion the way the F* source's `fuel`
parameter does; callers size it from the input length, which is a safe
upper bound because every element, attribute and text run costs at least
one character of markup. -/

/-- What a node element contributes: its subject (which the enclosing
`[7.2.15]` / `[7.2.19]` production needs as an object), its triples, and
the outgoing state. The F* re-derives the subject at the call site with
`determine_subject_readonly`; returning it removes that duplication and
the counter-desynchronisation bug its comment describes. -/
structure NodeRes where
  subj : Subject
  triples : List Triple
  st : St

/-- What a property element or a list of them contributes. -/
structure Res where
  triples : List Triple
  st : St

/-- `[7.2.17] parseTypeLiteralPropertyElt` (also the target of
`[7.2.20]`). -/
def parseTypeLiteral (st : St) (subj : Subject) (pred : WfIri)
    (reif : Option WfIri) (annot : Option Subject) (children : List XML.Node) : Res :=
  let lex := serializeLiteralContent st.scope children
  match mkTypedLiteral? lex rdfXMLLiteral with
  | none => ⟨[], st.fail "rdf:XMLLiteral cannot type this literal"⟩
  | some l =>
    let obj := Term.literal l
    ⟨{ s := subj, p := pred, o := obj } :: reifyAll reif annot subj pred obj, st⟩

/-- `[7.2.23] idAttr` / `[7.2.24] nodeIdAttr` / `[7.2.25] aboutAttr`, in
the order §7.2.11 tries them. A node element carrying none of the three
denotes a fresh blank node — the base IRI, empty or not, does NOT enter
a blank-node label (the F* source carries a long comment defending this
against WebOnt-imports-011). -/
def determineSubject (st : St) (attrs : List XML.Attribute) : Subject × St :=
  match findRdfAttr st "about" attrs with
  | some a =>
    match mkIri? (resolveRef st a) with
    | some w => (.iri w, st)
    | none =>
      let (b, st1) := st.freshBnode
      (.bnode b, st1.fail s!"rdf:about does not resolve to an IRI: {a} (RDF/XML §7.2.25)")
  | none =>
    match findRdfAttr st "ID" attrs with
    | some v =>
      let st1 := registerId st v
      match mkIri? (resolveRef st1 ("#" ++ v)) with
      | some w => (.iri w, st1)
      | none =>
        let (b, st2) := st1.freshBnode
        (.bnode b, st2.fail s!"rdf:ID does not resolve to an IRI: {v} (RDF/XML §7.2.23)")
    | none =>
      match findRdfAttr st "nodeID" attrs with
      | some n => (.bnode (nodeIdLabel n), st)
      | none   =>
        let (b, st1) := st.freshBnode
        (.bnode b, st1)

mutual

/-- `[7.2.11] nodeElement ::= start-element(URI == nodeElementURIs,
attributes == set((idAttr | nodeIdAttr | aboutAttr)?, propertyAttr*))
propertyEltList end-element()`.

A tag other than `rdf:Description` is a TYPED node element (§7.2.11
note): it additionally licenses `subject rdf:type <tag>`. -/
def nodeElement : Nat → St → XML.Node → NodeRes
  | 0, st, _ => ⟨.bnode (genLabel st.bnodeCounter), [], st.fail "recursion budget exhausted"⟩
  | fuel + 1, st, node =>
    match node with
    | .element tag attrs children =>
      let st1 := updateState st attrs
      match elementIri st1 tag with
      | none => ⟨.bnode (genLabel st1.bnodeCounter), [],
                 st1.fail s!"node element name has no namespace: {tag} (RDF/XML §7.2.11)"⟩
      | some full =>
        if XML.isForbiddenNodeElementName full then
          ⟨.bnode (genLabel st1.bnodeCounter), [],
           st1.fail s!"{full} may not be a node element name (RDF/XML §7.2.11)"⟩
        else
          match checkNodeAttrs st1 attrs with
          | some m => ⟨.bnode (genLabel st1.bnodeCounter), [], st1.fail m⟩
          | none =>
          match checkIdNCNames st1 attrs with
          | some m => ⟨.bnode (genLabel st1.bnodeCounter), [], st1.fail m⟩
          | none =>
            let (subj, st2) := determineSubject st1 attrs
            let typeTriples : List Triple :=
              if full == rdfTerm "Description" then []
              else match mkIri? full with
                   | some t => [{ s := subj, p := rdfTypeIri, o := Term.iri t }]
                   | none   => []
            let attrTriples := propertyAttrTriples st2 subj attrs
            let inner := propertyEltList fuel st2.resetLi subj children []
            ⟨subj, typeTriples ++ attrTriples ++ inner.triples, restoreScope st inner.st⟩
    | _ => ⟨.bnode (genLabel st.bnodeCounter), [], st⟩

/-- `[7.2.9] nodeElementList ::= ws* (nodeElement ws*)*` — the children
of `rdf:RDF`. Non-element children (whitespace, comments, processing
instructions) contribute nothing. -/
def nodeElementList : Nat → St → List XML.Node → List Triple → Res
  | 0, st, _, acc => ⟨acc.reverse, st⟩
  | _ + 1, st, [], acc => ⟨acc.reverse, st⟩
  | fuel + 1, st, c :: rest, acc =>
    match c with
    | .element _ _ _ =>
      let r := nodeElement fuel st c
      nodeElementList fuel r.st rest (r.triples.reverse ++ acc)
    | _ => nodeElementList fuel st rest acc

/-- `[7.2.13] propertyEltList ::= ws* (propertyElt ws*)*`. -/
def propertyEltList : Nat → St → Subject → List XML.Node → List Triple → Res
  | 0, st, _, _, acc => ⟨acc.reverse, st⟩
  | _ + 1, st, _, [], acc => ⟨acc.reverse, st⟩
  | fuel + 1, st, subj, c :: rest, acc =>
    match c with
    | .element _ _ _ =>
      let r := propertyElt fuel st subj c
      propertyEltList fuel r.st subj rest (r.triples.reverse ++ acc)
    | _ => propertyEltList fuel st subj rest acc

/-- `[7.2.14] propertyElt` — the dispatch over the six property-element
productions, in the order §7.2.14 lists them. -/
def propertyElt : Nat → St → Subject → XML.Node → Res
  | 0, st, _, _ => ⟨[], st.fail "recursion budget exhausted"⟩
  | fuel + 1, st, subj, node =>
    match node with
    | .element tag attrs children =>
      let st1 := updateState st attrs
      match elementIri st1 tag with
      | none => ⟨[], st1.fail s!"property element name has no namespace: {tag} (RDF/XML §7.2.14)"⟩
      | some full =>
        if XML.isForbiddenPropertyElementName full then
          ⟨[], st1.fail s!"{full} may not be a property element name (RDF/XML §7.2.14)"⟩
        else
          match checkPropertyAttrs st1 attrs with
          | some m => ⟨[], st1.fail m⟩
          | none =>
          match checkIdNCNames st1 attrs with
          | some m => ⟨[], st1.fail m⟩
          | none =>
            -- §5.3: `rdf:li` becomes `rdf:_n` with the enclosing node
            -- element's counter; every other name is the predicate itself.
            let (predOpt, st2) : Option WfIri × St :=
              if full == rdfTerm "li" then
                let (n, s') := st1.nextLi
                (mkIri? (rdfNs ++ "_" ++ toString n), s')
              else (mkIri? full, st1)
            match predOpt with
            | none => ⟨[], st2.fail s!"property element name is not an IRI: {full}"⟩
            | some pred =>
              -- §7.2.23 idAttr HERE identifies the statement (§7.3).
              let st3 := match findRdfAttr st2 "ID" attrs with
                         | some v => registerId st2 v
                         | none   => st2
              let reif : Option WfIri :=
                match findRdfAttr st3 "ID" attrs with
                | some v => mkIri? (resolveRef st3 ("#" ++ v))
                | none   => none
              -- RDF 1.2: the `rdf:annotation` / `rdf:annotationNodeID` reifier.
              let annot : Option Subject := annotReifier st3 attrs
              propertyEltBody fuel st3 subj pred reif annot attrs children
    | _ => ⟨[], st⟩

/-- The object-shaped half of `[7.2.14]`, once the predicate and the
§7.3 statement IRI are known. Split out so `propertyElt` stays readable;
the six branches below are the six productions. -/
def propertyEltBody : Nat → St → Subject → WfIri → Option WfIri →
    Option Subject → List XML.Attribute → List XML.Node → Res
  | 0, st, _, _, _, _, _, _ => ⟨[], st.fail "recursion budget exhausted"⟩
  | fuel + 1, st, subj, pred, reif, annot, attrs, children =>
    match findRdfAttr st "parseType" attrs with
    -- [7.2.17] parseTypeLiteralPropertyElt
    | some "Literal" => parseTypeLiteral st subj pred reif annot children
    -- [7.2.18] parseTypeResourcePropertyElt
    | some "Resource" =>
      let (bid, st1) := st.freshBnode
      let obj := Term.bnode bid
      let inner := propertyEltList fuel st1.resetLi (.bnode bid) children []
      ⟨{ s := subj, p := pred, o := obj } :: reifyAll reif annot subj pred obj ++ inner.triples,
       restoreScope st inner.st⟩
    -- [7.2.19] parseTypeCollectionPropertyElt
    | some "Collection" =>
      let items := children.filter (fun c => c.elementTag.isSome)
      let (head, ts, st1) := collectionList fuel st items
      ⟨{ s := subj, p := pred, o := head } :: reifyAll reif annot subj pred head ++ ts, st1⟩
    -- RDF 1.2: `rdf:parseType="Triple"` — the property element holds
    -- exactly ONE `rdf:Description` making exactly ONE triple, and that
    -- triple becomes this property's object as a TRIPLE TERM
    -- `<<( s p o )>>`. Gated on `rdf:version="1.2"`: without it the
    -- content is IGNORED and nothing is emitted (`rdf12-xml-tt-01`).
    -- With it, an inner element that does not make exactly one triple —
    -- or a content that is not exactly one element — is a syntax error
    -- (`rdf12-xml-tt-07` / `-08`). Port of the F* `Some "Triple"` arm.
    | some "Triple" =>
      if !st.sawVersion12 then ⟨[], st⟩
      else
        match children.filter (fun c => c.elementTag.isSome) with
        | [childDesc] =>
          let inner := nodeElement fuel st childDesc
          (match inner.triples with
           | [tt] =>
             let obj := Term.tripleTerm tt.s tt.p tt.o
             ⟨{ s := subj, p := pred, o := obj } :: reifyAll reif annot subj pred obj,
              restoreScope st inner.st⟩
           | ts =>
             ⟨[], (restoreScope st inner.st).fail
                s!"rdf:parseType=\"Triple\" content makes {ts.length} triples, not 1 (RDF 1.2 XML Syntax)"⟩)
        | cs =>
          ⟨[], st.fail
             s!"rdf:parseType=\"Triple\" needs exactly one element child, found {cs.length} (RDF 1.2 XML Syntax)"⟩
    -- [7.2.20] parseTypeOtherPropertyElt — "any other value … is
    -- treated as if it were rdf:parseType='Literal'".
    | some _ => parseTypeLiteral st subj pred reif annot children
    | none =>
      -- [7.2.21] emptyPropertyElt with an explicit object
      match findRdfAttr st "resource" attrs with
      | some r =>
        match mkIri? (resolveRef st r) with
        | none => ⟨[], st.fail s!"rdf:resource does not resolve to an IRI: {r} (RDF/XML §7.2.31)"⟩
        | some w =>
          let obj := Term.iri w
          ⟨{ s := subj, p := pred, o := obj } :: reifyAll reif annot subj pred obj
             ++ propertyAttrTriples st (.iri w) attrs, st⟩
      | none =>
      match findRdfAttr st "nodeID" attrs with
      | some n =>
        let obj := Term.bnode (nodeIdLabel n)
        ⟨{ s := subj, p := pred, o := obj } :: reifyAll reif annot subj pred obj
           ++ propertyAttrTriples st (.bnode (nodeIdLabel n)) attrs, st⟩
      | none =>
        let elemChildren := children.filter (fun c => c.elementTag.isSome)
        match elemChildren with
        -- [7.2.15] resourcePropertyElt ::= start-element … nodeElement … end-element
        | child :: restChildren =>
          if !restChildren.isEmpty then
            ⟨[], st.fail "a property element may contain at most one node element (RDF/XML §7.2.15)"⟩
          else if (findRdfAttr st "datatype" attrs).isSome then
            ⟨[], st.fail "rdf:datatype on a property element with element content (RDF/XML §7.2.16)"⟩
          else
            let nr := nodeElement fuel st child
            let obj := nr.subj.toTerm
            ⟨{ s := subj, p := pred, o := obj } :: reifyAll reif annot subj pred obj ++ nr.triples,
             nr.st⟩
        | [] =>
          let text := XML.Node.textContentList children
          let probe := propertyAttrTriples st (.bnode "probe") attrs
          if text.isEmpty && (findRdfAttr st "datatype" attrs).isNone
             && !probe.isEmpty then
            -- [7.2.21] emptyPropertyElt with property attributes: the
            -- object is a fresh blank node they describe.
            let (bid, st1) := st.freshBnode
            let obj := Term.bnode bid
            ⟨{ s := subj, p := pred, o := obj } :: reifyAll reif annot subj pred obj
               ++ propertyAttrTriples st1 (.bnode bid) attrs, st1⟩
          else if !probe.isEmpty then
            ⟨[], st.fail "property attributes on a property element with content (RDF/XML §7.2.16)"⟩
          else
            -- [7.2.16] literalPropertyElt, and the no-content case of
            -- [7.2.21] (an empty lexical form).
            match findRdfAttr st "datatype" attrs with
            | some dt =>
              match mkIri? (resolveRef st dt) with
              | none => ⟨[], st.fail s!"rdf:datatype does not resolve to an IRI: {dt} (RDF/XML §7.2.28)"⟩
              | some w =>
                match mkTypedLiteral? text w with
                | none => ⟨[], st.fail s!"{w.val} needs a language tag and cannot type a literal"⟩
                | some l =>
                  let obj := Term.literal l
                  ⟨{ s := subj, p := pred, o := obj } :: reifyAll reif annot subj pred obj, st⟩
            | none =>
              let obj := Term.literal (mkPlainLiteral text st.lang st.effectiveDir)
              ⟨{ s := subj, p := pred, o := obj } :: reifyAll reif annot subj pred obj, st⟩

/-- `[7.2.19]`'s list construction: the collection's items become an
`rdf:first`/`rdf:rest` chain terminated by `rdf:nil`. Returns the head
term, the triples, and the outgoing state. -/
def collectionList : Nat → St → List XML.Node → Term × List Triple × St
  | 0, st, _ => (Term.iri rdfNilIri, [], st)
  | _ + 1, st, [] => (Term.iri rdfNilIri, [], st)
  | fuel + 1, st, item :: rest =>
    let nr := nodeElement fuel st item
    let (cellId, st1) := nr.st.freshBnode
    let (restHead, restTriples, st2) := collectionList fuel st1 rest
    let cell : Subject := .bnode cellId
    (Term.bnode cellId,
     { s := cell, p := rdfFirstIri, o := nr.subj.toTerm }
       :: { s := cell, p := rdfRestIri, o := restHead }
       :: (nr.triples ++ restTriples),
     st2)

end

/-! ## `[7.2.2] doc` and `[7.2.8] RDF` -/

/-- `[7.2.8] RDF ::= start-element(URI == rdf:RDF, attributes == set())
nodeElementList end-element()` — and `[7.2.2] doc`'s alternative, in
which the document element IS the single node element and the `rdf:RDF`
wrapper is absent. -/
def processDocument (fuel : Nat) (st : St) (root : XML.Node) : Res :=
  match root with
  | .element tag attrs children =>
    let st1 := updateState st attrs
    match elementIri st1 tag with
    | none => ⟨[], st1.fail s!"document element name has no namespace: {tag}"⟩
    | some full =>
      if full == rdfTerm "RDF" then nodeElementList fuel st1 children []
      else
        let nr := nodeElement fuel st root
        ⟨nr.triples, nr.st⟩
  | _ => ⟨[], st.fail "the document element is not an element"⟩

/-- Parse an RDF/XML document into a graph.

`base` is the retrieval IRI of the document (RFC 3986 §5.1.3), against
which `xml:base`, `rdf:about`, `rdf:ID`, `rdf:resource` and
`rdf:datatype` resolve. `none` means no base is known, in which case a
relative reference simply fails `RDF.isIri` and the document is
rejected — the same treatment `parseTurtle` gives a relative IRI with no
`@base`.

Port of `parse_rdfxml_with_base_strict`: an XML document that is not
well-formed, or an RDF/XML rule violation anywhere in it, is a
rejection, not a partial graph. -/
def parseRdfXml (text : String) (base : Option String := none) :
    Except ParseError Graph :=
  match XML.parseXML text with
  | .error e => .error { msg := s!"XML: {e.message}", pos := e.position }
  | .ok doc =>
    let res := processDocument (text.length + 2) (St.init (base.getD "")) doc.root
    match res.st.err with
    | some e => .error e
    | none   => .ok res.triples

end L4Factoidal.Syntax.RdfXml
