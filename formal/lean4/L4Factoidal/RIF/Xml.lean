/-
L4Factoidal.RIF.Xml — the RIF Core XML serialization, parsed.

Port of `formal/fstar/Parser.RIFXML.fst` (1,349 lines).

    parseRifProgram : String → Option Document

Two stages, as in the F\* source: `XML.parseXML` builds the document
tree, and this module walks it into the `RIF.Syntax` AST. The XML
scanner is not touched.

W3C RIF Core XML serialization: <https://www.w3.org/TR/rif-core/#XML_Serialization>.
Default namespace `http://www.w3.org/2007/rif#`.

## Element names are matched on the LOCAL name

The suite emits elements under the RIF namespace, sometimes prefixed
(`rif:Atom`), sometimes not (`Atom`). Every match here is on the part
after the last colon, exactly as the F\* source does it. That accepts a
document that puts RIF element names in the wrong namespace; the F\*
module makes the same trade, and the W3C conformance signal these tests
carry is about rule structure rather than namespace binding.

## Where this port DIVERGES from the F\* parser: rdf:PlainLiteral

The F\* parser DECODES an `rdf:PlainLiteral` constant — whose lexical
space packs a text and a language tag as `text@lang`, with `text@`
meaning no tag — into an RDF literal: language-tagged when the tag is
non-empty, `xsd:string` when it is empty.

This port keeps the packed form, `Tm.const "text@lang"
(rdfNs ++ "PlainLiteral")`, for two reasons:

1. `RIF.Ps` — the presentation-syntax front end already in this tree —
   produces exactly that (`Ps.lean`, the `.plain` case). Decoding here
   and not there would make the SAME RIF document parse to different
   terms depending on which syntax it arrived in.
2. `Tm.const` carries a lexical form and a symbol space, with no
   language-tag slot. A language-tagged literal is not representable in
   this AST at all, so the decode cannot happen at parse time without
   changing the AST.

The consequence is real and is NOT fixed here: `RIF.Translation.termOfConst`
turns the packed form into a literal typed `rdf:PlainLiteral`, where the
RIF-RDF combination spec says it denotes a plain or language-tagged
literal. The decode belongs in `termOfConst`, where it would serve both
front ends at once. Recorded at
<https://github.com/danbri/factoidal/issues/561>.

## Fuel

The F\* walkers are fuel-bounded because F\*'s termination checker
cannot see through the `firstChildWithLocalName` indirection. Lean has
the same problem for the same reason, and carries the same generous
budget so the difference is a nuisance rather than a semantic choice.
-/
import L4Factoidal.RIF.Syntax
import L4Factoidal.XML.Parser

namespace L4Factoidal.RIF.Xml

/-! The AST names (`Tm`, `Atom`, `Formula`, `Rule`, `Document`,
`iriSpace`, `rdfNs`, `xsdNs`) come from the enclosing `L4Factoidal.RIF`.
`L4Factoidal.XML` is NOT opened: both namespaces declare a `Document`,
and the XML side is written `XML.Node` / `XML.Attribute` throughout so a
reader always knows which tree a name belongs to. The presentation-syntax
front end `RIF.Ps` declares its own `parseTerm` and `parseConst`, which is
the other reason this one lives in a namespace of its own. -/

/-! ## Names -/

def rifNs : String := "http://www.w3.org/2007/rif#"

/-- The part of a tag after the LAST colon. RIF-XML never nests
prefixes, but `rif:Atom` has to reduce to `Atom`. -/
def localName (tag : String) : String :=
  match (tag.toList.reverse.takeWhile (· != ':')).reverse with
  | []  => if tag.contains ':' then "" else tag
  | cs  => String.ofList cs

def tagIs (expected tag : String) : Bool := localName tag == expected

/-! ## Walking the tree -/

def firstChildWithLocalName (name : String) : List XML.Node → Option XML.Node
  | [] => none
  | (n@(.element t _ _)) :: rest =>
      if tagIs name t then some n else firstChildWithLocalName name rest
  | _ :: rest => firstChildWithLocalName name rest

def childrenWithLocalName (name : String) : List XML.Node → List XML.Node
  | [] => []
  | (n@(.element t _ _)) :: rest =>
      if tagIs name t then n :: childrenWithLocalName name rest
      else childrenWithLocalName name rest
  | _ :: rest => childrenWithLocalName name rest

def childElementsOnly : List XML.Node → List XML.Node
  | [] => []
  | (n@(.element _ _ _)) :: rest => n :: childElementsOnly rest
  | _ :: rest => childElementsOnly rest

/-- Text content of an element, `text` and `cdata` children joined,
nested elements ignored. RIF-XML only puts text inside the `Const` and
`Var` leaves, which is all this is used for. -/
def collectLeafText : List XML.Node → String
  | [] => ""
  | n :: rest =>
      let here := match n with
        | .text t  => t
        | .cdata t => t
        | _        => ""
      here ++ collectLeafText rest

def elementText : XML.Node → String
  | .element _ _ children => collectLeafText children
  | _ => ""

def elementChildren : XML.Node → List XML.Node
  | .element _ _ children => children
  | _ => []

def findAttr (name : String) : List XML.Attribute → Option String
  | [] => none
  | a :: rest => if a.name == name then some a.value else findAttr name rest

/-- Strip leading and trailing ASCII whitespace. `Const` and `Var` text
usually arrives with the surrounding indentation attached. -/
def trimWs (s : String) : String :=
  let isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'
  String.ofList ((s.toList.dropWhile isWs).reverse.dropWhile isWs).reverse

/-! ## Constants and variables

    <Const type="&rif;iri">http://example.org/foo</Const>
    <Const type="&xs;integer">42</Const>
    <Var>x</Var>

The `type` attribute names the symbol space. Three spellings of each
marker are accepted — the full IRI the spec mandates, the bare local
name, and any `prefix:name` form — because serialisers in the wild emit
all three. -/

def isIriTypeMarker (ty : String) : Bool :=
  ty == rifNs ++ "iri" || ty == "iri" || localName ty == "iri"

def isLocalTypeMarker (ty : String) : Bool :=
  ty == rifNs ++ "local" || ty == "local" || localName ty == "local"

def isPlainLiteralTypeMarker (ty : String) : Bool :=
  ty == rdfNs ++ "PlainLiteral" || ty == "PlainLiteral"
    || localName ty == "PlainLiteral"

/-- `rif:local` names a constant scoped to the document. The W3C
combination spec maps it to a fresh blank node per document; this keeps
the F\* choice of a synthetic `urn:rif-local:` IRI, which is enough for
every fixture and does not pretend to the blank-node semantics. -/
def localToIri (lex : String) : Tm := .const ("urn:rif-local:" ++ lex) iriSpace

def constFromType (ty lex : String) : Option Tm :=
  if isIriTypeMarker ty then some (.const lex iriSpace)
  else if isLocalTypeMarker ty then some (localToIri lex)
  else if isPlainLiteralTypeMarker ty then some (.const lex (rdfNs ++ "PlainLiteral"))
  else if ty.contains ':' then some (.const lex ty)
  else none

def parseConst : XML.Node → Option Tm
  | .element _ attrs children =>
      let lex := trimWs (collectLeafText children)
      match findAttr "type" attrs with
      | some ty => constFromType ty lex
      -- No `type`: the spec requires one, but a missing marker reads as
      -- a plain string rather than failing the whole document.
      | none    => some (.const lex (xsdNs ++ "string"))
  | _ => none

def parseVar : XML.Node → Option Tm
  | .element _ _ children =>
      let raw := trimWs (collectLeafText children)
      if raw.isEmpty then none else some (.var raw)
  | _ => none

def listCollectSome {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | none :: _ => none
  | some x :: rest => (listCollectSome rest).map (x :: ·)

/-! ## Terms, including `External` in FUNCTION position

    <External><content><Expr>
      <op><Const type="&rif;iri">builtin</Const></op>
      <args ordered="yes"> term* </args>
    </Expr></content></External>

`parseTermFuel` and `parseOpAndArgsFuel` are mutually recursive: an
`External`'s arguments can nest another one. -/

mutual

def parseTermFuel (n : XML.Node) : Nat → Option Tm
  | 0 => none
  | fuel + 1 =>
      match n with
      | .element tag _ children =>
          if tagIs "Const" tag then parseConst n
          else if tagIs "Var" tag then parseVar n
          else if tagIs "External" tag then
            match firstChildWithLocalName "content" children with
            | none => none
            | some contentNode =>
                match childElementsOnly (elementChildren contentNode) with
                | [inner] =>
                    match inner with
                    | .element itag _ _ =>
                        if tagIs "Expr" itag then
                          match parseOpAndArgsFuel inner fuel with
                          | none => none
                          | some (op, args) => some (.external op args)
                        else none
                    | _ => none
                | _ => none
          else none
      | _ => none

/-- `<op>…</op><args>term*</args>`, shared by `External`'s `Expr`
(function position) and by `Atom` (predicate position). The operator has
to resolve to a plain IRI constant: RIF-DTB builtin symbols always are
one. -/
def parseOpAndArgsFuel (n : XML.Node) : Nat → Option (String × List Tm)
  | 0 => none
  | fuel + 1 =>
      match n with
      | .element _ _ children =>
          match firstChildWithLocalName "op" children with
          | none => none
          | some opNode =>
              match parseTermHostFuel opNode fuel with
              | some (.const pi sp) =>
                  if sp != iriSpace then none
                  else
                    let argNodes := match firstChildWithLocalName "args" children with
                      | none => []
                      | some argsNode => childElementsOnly (elementChildren argsNode)
                    match listCollectSome (argNodes.map (parseTermFuel · fuel)) with
                    | none => none
                    | some args => some (pi, args)
              | _ => none
      | _ => none

/-- A term wrapped in a single-element host (`<object>`, `<op>`, a
`<slot>` key or value): find the one element child and decode it. -/
def parseTermHostFuel (n : XML.Node) : Nat → Option Tm
  | 0 => none
  | fuel + 1 =>
      match childElementsOnly (elementChildren n) with
      | [] => none
      | first :: _ => parseTermFuel first fuel

end

def rifFuel : Nat := 1000

def parseTerm (n : XML.Node) : Option Tm := parseTermFuel n rifFuel
def parseTermHost (n : XML.Node) : Option Tm := parseTermHostFuel n rifFuel
def parseOpAndArgs (n : XML.Node) : Option (String × List Tm) :=
  parseOpAndArgsFuel n rifFuel

/-! ## Atoms

A binary atom `p(s,o)` is the triple `(s, p, o)` per the RIF/RDF
combination spec. Arity 0, 1 and ≥ 3 keep the generic positional
encoding, which `RIF.Translation` gives a triple mapping. -/

def parseAtomElement (n : XML.Node) : Option Atom :=
  match n with
  | .element _ _ children =>
      match firstChildWithLocalName "op" children with
      | none => none
      | some opNode =>
          match parseTermHost opNode with
          | some (.const pred sp) =>
              let argNodes := match firstChildWithLocalName "args" children with
                | none => []
                | some argsNode => childElementsOnly (elementChildren argsNode)
              match listCollectSome (argNodes.map parseTerm) with
              | none => none
              | some args => some (.pos pred sp args)
          | _ => none
  | _ => none

/-- `<Frame><object>…</object><slot>key value</slot>…</Frame>`. A
multi-slot frame is one atom per slot, so this returns a list. -/
def parseSlotPair (slot : XML.Node) (obj : Tm) : Option Atom :=
  match childElementsOnly (elementChildren slot) with
  | [k, v] =>
      match parseTerm k, parseTerm v with
      | some kt, some vt => some (.frame obj kt vt)
      | _, _ => none
  | _ => none

def parseFrameElement (n : XML.Node) : Option (List Atom) :=
  match n with
  | .element _ _ children =>
      match firstChildWithLocalName "object" children with
      | none => none
      | some objNode =>
          match parseTermHost objNode with
          | none => none
          | some obj =>
              listCollectSome
                ((childrenWithLocalName "slot" children).map (parseSlotPair · obj))
  | _ => none

def parseMemberElement (n : XML.Node) : Option Atom :=
  match n with
  | .element _ _ children =>
      match firstChildWithLocalName "instance" children,
            firstChildWithLocalName "class" children with
      | some iNode, some cNode =>
          match parseTermHost iNode, parseTermHost cNode with
          | some i, some c => some (.member i c)
          | _, _ => none
      | _, _ => none
  | _ => none

def parseSubclassElement (n : XML.Node) : Option Atom :=
  match n with
  | .element _ _ children =>
      match firstChildWithLocalName "sub" children,
            firstChildWithLocalName "super" children with
      | some sNode, some uNode =>
          match parseTermHost sNode, parseTermHost uNode with
          | some sb, some su => some (.sub sb su)
          | _, _ => none
      | _, _ => none
  | _ => none

def isAtomTag (tag : String) : Bool :=
  tagIs "Atom" tag || tagIs "Frame" tag || tagIs "Member" tag
    || tagIs "Subclass" tag

def parseAtomNode (n : XML.Node) : Option (List Atom) :=
  match n with
  | .element tag _ _ =>
      if tagIs "Atom" tag then (parseAtomElement n).map ([·])
      else if tagIs "Frame" tag then parseFrameElement n
      else if tagIs "Member" tag then (parseMemberElement n).map ([·])
      else if tagIs "Subclass" tag then (parseSubclassElement n).map ([·])
      else none
  | _ => none

/-! ## Rule bodies

A body is one atomic formula, an `And`, an `External` in PREDICATE
position, an `Equal`, or a `<if>` / `<body>` / `<formula>` wrapper
around one of those. Wrappers are unwrapped transparently. -/

def isBodyWrapperTag (tag : String) : Bool :=
  tagIs "if" tag || tagIs "body" tag || tagIs "formula" tag

mutual

def parseBodyNode (n : XML.Node) : Nat → Option Formula
  | 0 => none
  | fuel + 1 =>
      match n with
      | .element tag _ children =>
          if tagIs "And" tag then
            (parseBodyList (childElementsOnly children) fuel).map Formula.and
          else if isBodyWrapperTag tag then
            match childElementsOnly children with
            | [] => none
            | first :: _ => parseBodyNode first fuel
          else if tagIs "External" tag then
            -- Predicate position wraps an `Atom`; function position
            -- wraps an `Expr` and is handled by `parseTermFuel`. A
            -- function-mode External standing alone as a whole conjunct
            -- is not a shape any fixture uses, so it fails rather than
            -- being guessed at.
            match firstChildWithLocalName "content" children with
            | none => none
            | some contentNode =>
                match childElementsOnly (elementChildren contentNode) with
                | [inner] =>
                    match inner with
                    | .element itag _ _ =>
                        if tagIs "Atom" itag then
                          match parseOpAndArgs inner with
                          | none => none
                          | some (op, args) => some (.atom (.externalPred op args))
                        else none
                    | _ => none
                | _ => none
          else if tagIs "Equal" tag then
            match firstChildWithLocalName "left" children,
                  firstChildWithLocalName "right" children with
            | some lNode, some rNode =>
                match parseTermHost lNode, parseTermHost rNode with
                | some l, some r => some (.atom (.equal l r))
                | _, _ => none
            | _, _ => none
          else if isAtomTag tag then
            match parseAtomNode n with
            | none => none
            | some [a] => some (.atom a)
            -- A multi-slot frame is a conjunction.
            | some atoms => some (.and (atoms.map Formula.atom))
          else none
      | _ => none

def parseBodyList (xs : List XML.Node) : Nat → Option (List Formula)
  | 0 => none
  | fuel + 1 =>
      match xs with
      | [] => some []
      | hd :: rest =>
          match parseBodyNode hd fuel with
          | none => none
          | some b => (parseBodyList rest fuel).map (b :: ·)

end

/-! ## Rule heads

Exactly one atom: RIF Core forbids head disjunction and head function
symbols. A head frame with several slots is not a single atom, so it
fails rather than silently taking the first slot. -/

def isHeadWrapperTag (tag : String) : Bool :=
  tagIs "then" tag || tagIs "head" tag || tagIs "formula" tag

def unwrapHeadNode (n : XML.Node) : Nat → Option XML.Node
  | 0 => none
  | fuel + 1 =>
      match n with
      | .element tag _ children =>
          if isAtomTag tag then some n
          else if isHeadWrapperTag tag then
            match childElementsOnly children with
            | [] => none
            | first :: _ => unwrapHeadNode first fuel
          else none
      | _ => none

def parseHeadNode (n : XML.Node) (fuel : Nat) : Option Atom :=
  match unwrapHeadNode n fuel with
  | none => none
  | some atomNode =>
      match parseAtomNode atomNode with
      | some [a] => some a
      | _        => none

/-! ## Implies -/

def findFirstNamed : List String → List XML.Node → Option XML.Node
  | [], _ => none
  | name :: rest, children =>
      match firstChildWithLocalName name children with
      | some n => some n
      | none   => findFirstNamed rest children

/-- `<Implies><if>body</if><then>head</then></Implies>`. Some
serialisations write `<body>`/`<head>`; both pairs are accepted, and the
children are found by name rather than by position. -/
def parseImplies (n : XML.Node) (fuel : Nat) : Option Rule :=
  match n with
  | .element _ _ children =>
      match findFirstNamed ["if", "body"] children,
            findFirstNamed ["then", "head"] children with
      | some i, some t =>
          match parseBodyNode i fuel, parseHeadNode t fuel with
          | some body, some head => some { head := head, body := some body }
          | _, _ => none
      | _, _ => none
  | _ => none

/-! ## Sentences

`Forall` is stripped: the variables it declares are the free variables
of the rule, which is how `RIF.Syntax` reads a rule already. -/

mutual

def parseSentenceContent (n : XML.Node) : Nat → Option (List Rule)
  | 0 => none
  | fuel + 1 =>
      match n with
      | .element tag _ children =>
          if tagIs "Forall" tag then
            match firstChildWithLocalName "formula" children with
            | some fNode => parseSentenceContent fNode fuel
            -- Some serialisers omit the formula wrapper inside Forall.
            | none =>
                match firstChildWithLocalName "Implies" children with
                | some impNode => (parseImplies impNode fuel).map ([·])
                | none => none
          else if tagIs "Implies" tag then
            (parseImplies n fuel).map ([·])
          else if tagIs "formula" tag || tagIs "sentence" tag then
            match childElementsOnly children with
            | [] => none
            | first :: _ => parseSentenceContent first fuel
          else if tagIs "Exists" tag then
            -- An existential CONCLUSION document. The declared variables
            -- stay free in the parsed fact, and the entailment question
            -- the runner builds treats a free variable existentially,
            -- which is RIF's own reading. Not accepted in rule-BODY
            -- position: `parseBodyNode` has no `Exists` arm.
            match firstChildWithLocalName "formula" children with
            | none => none
            | some fNode => parseSentenceContent fNode fuel
          else if tagIs "And" tag then
            -- A conjunction of FACTS at document level: a conclusion
            -- naming several facts that must ALL be entailed. Rule-body
            -- `And` is `parseBodyNode`'s, not this.
            parseSentenceConjuncts (childElementsOnly children) fuel
          else if isAtomTag tag then
            match parseAtomNode n with
            | none => none
            | some atoms => some (atoms.map (fun a => { head := a }))
          else none
      | _ => none

def parseSentenceConjuncts (xs : List XML.Node) : Nat → Option (List Rule)
  | 0 => none
  | fuel + 1 =>
      match xs with
      | [] => some []
      | hd :: rest =>
          match parseSentenceContent hd fuel with
          | none => none
          | some these => (parseSentenceConjuncts rest fuel).map (these ++ ·)

end

/-! ## Groups

Nested groups are walked, though no target fixture nests them. An
element inside a group that is neither a sentence nor a group — `<id>`,
`<meta>` — is an annotation and is skipped rather than failing the
document. -/

mutual

def parseGroupChildren (xs : List XML.Node) : Nat → Option (List Rule)
  | 0 => none
  | fuel + 1 =>
      match xs with
      | [] => some []
      | hd :: rest =>
          match hd with
          | .element tag _ children =>
              if tagIs "sentence" tag then
                match childElementsOnly children with
                | [] => parseGroupChildren rest fuel
                | first :: _ =>
                    let inner :=
                      match first with
                      | .element t _ _ =>
                          if tagIs "Group" t then parseGroupNode first fuel
                          else parseSentenceContent first fuel
                      | _ => parseSentenceContent first fuel
                    match inner with
                    | none => none
                    | some these => (parseGroupChildren rest fuel).map (these ++ ·)
              else if tagIs "Group" tag then
                match parseGroupNode hd fuel with
                | none => none
                | some these => (parseGroupChildren rest fuel).map (these ++ ·)
              else parseGroupChildren rest fuel
          | _ => parseGroupChildren rest fuel

def parseGroupNode (n : XML.Node) : Nat → Option (List Rule)
  | 0 => none
  | fuel + 1 =>
      match n with
      | .element tag _ children =>
          if tagIs "Group" tag then parseGroupChildren children fuel else none
      | _ => none

end

/-! ## Documents

`<payload>` may be absent (the group sits directly under `<Document>`)
and `<Document>` may be absent (a bare `<Group>` fragment). -/

def extractGroupFromDoc (root : XML.Node) : Option XML.Node :=
  match root with
  | .element tag _ children =>
      if tagIs "Document" tag then
        match firstChildWithLocalName "payload" children with
        | some payloadNode =>
            firstChildWithLocalName "Group" (elementChildren payloadNode)
        | none => firstChildWithLocalName "Group" children
      else if tagIs "Group" tag then some root
      else if tagIs "payload" tag then firstChildWithLocalName "Group" children
      else none
  | _ => none

/-! ### Imports

`<directive><Import><location>…</location><profile>…</profile></Import></directive>`.
The profile names the entailment regime the imported document is read
under; dropping it makes an OWL-Direct import look like a plain RDF one,
which is why `Document.imports` carries the pair. Resolving a location
to bytes is the consumer's I/O and is not here. -/

def parseImportLocation (importNode : XML.Node) : Option String :=
  match firstChildWithLocalName "location" (elementChildren importNode) with
  | none => none
  | some locNode =>
      let raw := trimWs (elementText locNode)
      if raw.isEmpty then none else some raw

def parseImportProfile (importNode : XML.Node) : Option String :=
  match firstChildWithLocalName "profile" (elementChildren importNode) with
  | none => none
  | some profNode =>
      let raw := trimWs (elementText profNode)
      if raw.isEmpty then none else some raw

def parseDirectiveImport (directiveNode : XML.Node) : Option (String × Option String) :=
  match firstChildWithLocalName "Import" (elementChildren directiveNode) with
  | none => none
  | some impNode =>
      match parseImportLocation impNode with
      | none => none
      | some url => some (url, parseImportProfile impNode)

def extractImportsFromDirectives : List XML.Node → List (String × Option String)
  | [] => []
  | (n@(.element t _ _)) :: rest =>
      if tagIs "directive" t then
        match parseDirectiveImport n with
        | none => extractImportsFromDirectives rest
        | some pair => pair :: extractImportsFromDirectives rest
      else extractImportsFromDirectives rest
  | _ :: rest => extractImportsFromDirectives rest

/-- A bare `<Group>` declares no directives, so it imports nothing. -/
def extractDocumentImports (root : XML.Node) : List (String × Option String) :=
  match root with
  | .element tag _ children =>
      if tagIs "Document" tag then extractImportsFromDirectives children else []
  | _ => []

def parseRifDocumentNode (root : XML.Node) : Option Document :=
  match extractGroupFromDoc root with
  | none => none
  | some groupNode =>
      match parseGroupNode groupNode rifFuel with
      | none => none
      | some rules =>
          some { imports := extractDocumentImports root, rules := rules }

/-- The entry point: RIF-XML text in, a `Document` out. -/
def parseRifProgram (input : String) : Option Document :=
  match XML.parseXML input with
  | .error _ => none
  | .ok doc  => parseRifDocumentNode doc.root

/-! ## Pinned behaviour -/

section Pins

private def factDoc : String :=
  "<Document xmlns=\"http://www.w3.org/2007/rif#\">" ++
  "<payload><Group><sentence>" ++
  "<Atom><op><Const type=\"http://www.w3.org/2007/rif#iri\">http://example.org/p</Const></op>" ++
  "<args><Const type=\"http://www.w3.org/2007/rif#iri\">http://example.org/a</Const>" ++
  "<Const type=\"http://www.w3.org/2007/rif#iri\">http://example.org/b</Const></args>" ++
  "</Atom></sentence></Group></payload></Document>"

/-! One fact, no imports. A parser that returned `none` would satisfy
nothing below, so every pin states what it got rather than that it got
something. -/
#guard (parseRifProgram factDoc).isSome

#guard match parseRifProgram factDoc with
       | some d => d.rules.length == 1 && d.imports.isEmpty
       | none   => false

/-! The binary atom keeps its predicate and both arguments, in order. -/
#guard match parseRifProgram factDoc with
       | some d =>
           match d.rules with
           | [r] =>
               (match r.head with
                | .pos p sp [.const a asp, .const b bsp] =>
                    p == "http://example.org/p" && sp == iriSpace
                      && a == "http://example.org/a" && asp == iriSpace
                      && b == "http://example.org/b" && bsp == iriSpace
                | _ => false)
               && r.body.isNone
           | _ => false
       | none => false

private def ruleDoc : String :=
  "<Document xmlns=\"http://www.w3.org/2007/rif#\"><payload><Group><sentence>" ++
  "<Forall><declare><Var>x</Var></declare><formula><Implies>" ++
  "<if><Atom><op><Const type=\"&#x72;if:iri\">http://example.org/q</Const></op>" ++
  "<args><Var>x</Var><Const type=\"rif:iri\">http://example.org/b</Const></args></Atom></if>" ++
  "<then><Atom><op><Const type=\"rif:iri\">http://example.org/p</Const></op>" ++
  "<args><Var>x</Var><Const type=\"rif:iri\">http://example.org/c</Const></args></Atom></then>" ++
  "</Implies></formula></Forall></sentence></Group></payload></Document>"

/-! A `Forall`-wrapped `Implies` gives ONE rule with a body — the
`Forall` is stripped and the wrapper elements are unwrapped. -/
#guard match parseRifProgram ruleDoc with
       | some d =>
           match d.rules with
           | [r] => r.body.isSome
           | _   => false
       | none => false

/-! The prefixed `rif:iri` type marker is accepted, so the body's
variable and constant both survive. -/
#guard match parseRifProgram ruleDoc with
       | some d =>
           match d.rules with
           | [r] =>
               match r.body with
               | some (.atom (.pos q _ [.var v, .const b bsp])) =>
                   q == "http://example.org/q" && v == "x"
                     && b == "http://example.org/b" && bsp == iriSpace
               | _ => false
           | _ => false
       | none => false

private def importDoc : String :=
  "<Document xmlns=\"http://www.w3.org/2007/rif#\">" ++
  "<directive><Import><location>http://example.org/data</location>" ++
  "<profile>http://www.w3.org/ns/entailment/RDFS</profile></Import></directive>" ++
  "<payload><Group></Group></payload></Document>"

/-! An import carries its PROFILE, not just its location. -/
#guard match parseRifProgram importDoc with
       | some d => d.imports == [("http://example.org/data",
                                 some "http://www.w3.org/ns/entailment/RDFS")]
       | none   => false

/-! A `Group` with no sentences parses to a document with no rules,
rather than failing. -/
#guard match parseRifProgram importDoc with
       | some d => d.rules.isEmpty
       | none   => false

/-! A bare `<Group>` fragment with no `Document` wrapper is accepted. -/
#guard (parseRifProgram
          ("<Group xmlns=\"http://www.w3.org/2007/rif#\"><sentence>" ++
           "<Member><instance><Const type=\"rif:iri\">http://example.org/a</Const></instance>" ++
           "<class><Const type=\"rif:iri\">http://example.org/C</Const></class></Member>" ++
           "</sentence></Group>")).isSome

/-! Text that is not XML at all fails, and so does XML that is not RIF.
Without these the parser could be accepting everything. -/
#guard (parseRifProgram "not xml at all").isNone
#guard (parseRifProgram "<html><body>hello</body></html>").isNone

/-! `localName` strips a prefix and leaves an unprefixed name alone. -/
#guard localName "rif:Atom" == "Atom"
#guard localName "Atom" == "Atom"
#guard localName "a:b:c" == "c"

#guard trimWs "  x \n" == "x"
#guard trimWs "" == ""

end Pins

end L4Factoidal.RIF.Xml
