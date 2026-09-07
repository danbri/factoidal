/-
L4Factoidal.XSD.SchemaReader — read the SIMPLE-TYPE part of a schema
document (XML Schema 1.1 Part 1 §3.16, the `<simpleType>` element) into
the `SimpleType` of `XSD/SimpleType.lean`.

This is NOT the Part 1 schema-document parser: it reads exactly the
subset a DATATYPE test needs — top-level `element` declarations, named
and anonymous `simpleType` definitions, `restriction` / `list` /
`union`, and the §4.3 facet elements — and it CLASSIFIES every other
schema document rather than pretending to read it. The classification
is what lets the runner report a datatype score whose denominator is
the datatype tests and not the whole suite (Part 1 Structures is
https://github.com/danbri/factoidal/issues/666, not this run).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XSD.SimpleType
import L4Factoidal.XML.Parser

namespace L4Factoidal.XSD

open L4Factoidal.XML

/-- What a schema document contains, from the datatype runner's point
of view. -/
inductive SchemaClass where
  /-- Only simple type definitions and element declarations whose type
  is a simple type: a datatype test. -/
  | datatypeOnly
  /-- Complex types, attributes, groups, identity constraints: a Part 1
  Structures test. -/
  | structures
  /-- Both, or a construct the reader does not model (`include`,
  `import`, `redefine`, `override`). -/
  | mixed
deriving DecidableEq, Repr, Inhabited

/-! ## Names and namespaces -/

def localOf (qn : String) : String :=
  match qn.splitOn ":" with
  | [_, l] => l
  | _      => qn

def prefixOf (qn : String) : String :=
  match qn.splitOn ":" with
  | [p, _] => p
  | _      => ""

abbrev NsBindings := List (String × String)

def bindingsOf (attrs : List Attribute) : NsBindings :=
  attrs.filterMap (fun a =>
    if a.name == "xmlns" then some ("", a.value)
    else if a.name.startsWith "xmlns:"
    then some ((a.name.drop 6).toString, a.value)
    else none)

def resolvePrefix (bs : NsBindings) (p : String) : Option String :=
  (bs.find? (fun b => b.1 == p)).map (·.2)

def attrOf (name : String) : Node → Option String
  | .element _ attrs _ => (attrs.find? (fun a => a.name == name)).map (·.value)
  | _ => none

def childrenOf : Node → List Node
  | .element _ _ cs => cs
  | _ => []

def tagOf : Node → String
  | .element t _ _ => t
  | _ => ""

def elementChildren (n : Node) : List Node :=
  (childrenOf n).filter (fun c => match c with | .element _ _ _ => true | _ => false)

/-! ## Facets -/

def natOfString? (s : String) : Option Nat :=
  let cs := s.toList
  if allDigitsL cs then some (natOfDigits cs) else none

def explicitTzOf? (s : String) : Option ExplicitTz :=
  if s == "required" then some .required
  else if s == "prohibited" then some .prohibited
  else if s == "optional" then some .optional
  else none

def whiteSpaceOf? (s : String) : Option WhiteSpace :=
  if s == "preserve" then some .preserve
  else if s == "replace" then some .replace
  else if s == "collapse" then some .collapse
  else none

/-- Fold the facet children of one `restriction` into a `Facets`. The
`pattern` children of ONE restriction are alternatives, so they become
a single group (§4.3.4). -/
def facetsOfRestriction (children : List Node) : Facets :=
  let facetName (n : Node) := localOf (tagOf n)
  let valueOfFacet (n : Node) := (attrOf "value" n).getD ""
  let pats := (children.filter (fun c => facetName c == "pattern")).map valueOfFacet
  let enums := (children.filter (fun c => facetName c == "enumeration")).map valueOfFacet
  let find1 (nm : String) : Option String :=
    (children.find? (fun c => facetName c == nm)).map valueOfFacet
  { length := (find1 "length").bind natOfString?
    minLength := (find1 "minLength").bind natOfString?
    maxLength := (find1 "maxLength").bind natOfString?
    patterns := if pats.isEmpty then [] else [pats]
    enumeration := if enums.isEmpty then none else some enums
    whiteSpace := (find1 "whiteSpace").bind whiteSpaceOf?
    maxInclusive := find1 "maxInclusive"
    maxExclusive := find1 "maxExclusive"
    minInclusive := find1 "minInclusive"
    minExclusive := find1 "minExclusive"
    totalDigits := (find1 "totalDigits").bind natOfString?
    fractionDigits := (find1 "fractionDigits").bind natOfString?
    explicitTimezone := (find1 "explicitTimezone").bind explicitTzOf?
    hasAssertion := children.any (fun c =>
      facetName c == "assertion" || facetName c == "assert") }

/-! ## The schema document -/

structure SchemaDoc where
  bindings : NsBindings
  /-- Named `simpleType` definitions, by name. -/
  named    : List (String × Node)
  /-- Top-level `element` declarations: name, `type` attribute, inline
  `simpleType` child. -/
  elements : List (String × Option String × Option Node)
  klass    : SchemaClass
deriving Inhabited

/-- Is this QName the XML Schema namespace? -/
def isXsdQName (bs : NsBindings) (qn : String) : Bool :=
  resolvePrefix bs (prefixOf qn) == some xsdNamespace

/-- The built-in a QName names, if it names one. -/
def builtinOfQName? (bs : NsBindings) (qn : String) : Option Builtin :=
  if isXsdQName bs qn then builtinOfName? (localOf qn) else none

/-- Resolve a `simpleType` node into a `SimpleType`. `fuel` bounds the
chain of named-type references. -/
def readSimpleType : Nat → SchemaDoc → Node → Option SimpleType
  | 0, _, _ => none
  | fuel + 1, doc, node =>
    match (elementChildren node).find? (fun c =>
      let l := localOf (tagOf c)
      l == "restriction" || l == "list" || l == "union") with
    | none => none
    | some body =>
      let bodyKind := localOf (tagOf body)
      let kids := elementChildren body
      let inline := kids.find? (fun c => localOf (tagOf c) == "simpleType")
      if bodyKind == "restriction" then
        let f := facetsOfRestriction kids
        match attrOf "base" body with
        | some baseQn =>
            match builtinOfQName? doc.bindings baseQn with
            | some b => some (.atomic b f)
            | none =>
              match (doc.named.find? (fun p => p.1 == localOf baseQn)).map (·.2) with
              | some bn =>
                  match readSimpleType fuel doc bn with
                  | some (.atomic b bf) => some (.atomic b (Facets.merge bf f))
                  | some (.list it bf)  => some (.list it (Facets.merge bf f))
                  | some (.union ms bf) => some (.union ms (Facets.merge bf f))
                  | none => none
              | none => none
        | none =>
            match inline with
            | some st =>
                match readSimpleType fuel doc st with
                | some (.atomic b bf) => some (.atomic b (Facets.merge bf f))
                | some (.list it bf)  => some (.list it (Facets.merge bf f))
                | some (.union ms bf) => some (.union ms (Facets.merge bf f))
                | none => none
            | none => none
      else if bodyKind == "list" then
        match attrOf "itemType" body with
        | some itemQn =>
            match builtinOfQName? doc.bindings itemQn with
            | some b => some (.list (.atomic b Facets.empty) Facets.empty)
            | none =>
              match (doc.named.find? (fun p => p.1 == localOf itemQn)).map (·.2) with
              | some bn => (readSimpleType fuel doc bn).map (fun t => .list t Facets.empty)
              | none => none
        | none =>
            match inline with
            | some st => (readSimpleType fuel doc st).map (fun t => .list t Facets.empty)
            | none => none
      else
        -- union
        let named := match attrOf "memberTypes" body with
          | none => []
          | some ms => (ms.splitOn " ").filter (fun s => s != "")
        let namedTys := named.filterMap (fun qn =>
          match builtinOfQName? doc.bindings qn with
          | some b => some (SimpleType.atomic b Facets.empty)
          | none =>
            match (doc.named.find? (fun p => p.1 == localOf qn)).map (·.2) with
            | some bn => readSimpleType fuel doc bn
            | none => none)
        let inlineTys := (kids.filter (fun c => localOf (tagOf c) == "simpleType")).filterMap
          (fun c => readSimpleType fuel doc c)
        let ms := namedTys ++ inlineTys
        if ms.length == named.length
             + (kids.filter (fun c => localOf (tagOf c) == "simpleType")).length
        then some (.union ms Facets.empty) else none

/-- The Part 1 constructs that put a schema document outside the
datatype-only class. -/
def structureTags : List String :=
  ["complexType", "attribute", "attributeGroup", "group", "notation",
   "include", "import", "redefine", "override", "defaultOpenContent"]

def classifySchema (root : Node) : SchemaClass :=
  let kids := elementChildren root
  let hasStructure := kids.any (fun c => structureTags.contains (localOf (tagOf c)))
  let simpleOnly := kids.all (fun c =>
    let l := localOf (tagOf c)
    l == "simpleType" || l == "annotation" || l == "element")
  -- An element declaration with a complexType child, or with an
  -- identity constraint, is a structures test even when the schema has
  -- no top-level complexType.
  let elemComplex := kids.any (fun c =>
    localOf (tagOf c) == "element" &&
    (elementChildren c).any (fun g =>
      let gl := localOf (tagOf g)
      gl == "complexType" || gl == "key" || gl == "keyref" || gl == "unique"))
  if hasStructure || elemComplex then
    (if simpleOnly && !elemComplex then .mixed else .structures)
  else if simpleOnly then .datatypeOnly
  else .structures

/-- Read a parsed schema document. -/
def readSchema (doc : Document) : Option SchemaDoc :=
  let root := doc.root
  match root with
  | .element tag attrs _ =>
      let bs := bindingsOf attrs
      if localOf tag != "schema" then none
      else
        let kids := elementChildren root
        let named := kids.filterMap (fun c =>
          if localOf (tagOf c) == "simpleType" then
            (attrOf "name" c).map (fun n => (n, c))
          else none)
        let elems := kids.filterMap (fun c =>
          if localOf (tagOf c) == "element" then
            (attrOf "name" c).map (fun n =>
              (n, attrOf "type" c,
               (elementChildren c).find? (fun g => localOf (tagOf g) == "simpleType")))
          else none)
        some { bindings := bs, named := named, elements := elems,
               klass := classifySchema root }
  | _ => none

/-- The simple type of a top-level element declaration. -/
def elementType? (doc : SchemaDoc) (name : String) : Option SimpleType :=
  match doc.elements.find? (fun e => e.1 == name) with
  | none => none
  | some (_, tyQn, inline) =>
      match tyQn with
      | some qn =>
          match builtinOfQName? doc.bindings qn with
          | some b => some (.atomic b Facets.empty)
          | none =>
            match (doc.named.find? (fun p => p.1 == localOf qn)).map (·.2) with
            | some bn => readSimpleType 16 doc bn
            | none => none
      | none =>
          match inline with
          | some st => readSimpleType 16 doc st
          | none => none

end L4Factoidal.XSD
