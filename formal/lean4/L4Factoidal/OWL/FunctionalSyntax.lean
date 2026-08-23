/-
L4Factoidal.OWL.FunctionalSyntax — a narrow OWL 2 Functional-Syntax
parser that produces RDF triples.

Port of `formal/fstar/Parser.OWLFunctional.fst`.

Spec: OWL 2 Structural Specification and Functional-Style Syntax
(https://www.w3.org/TR/owl2-syntax/) for the grammar, and OWL 2
Mapping to RDF Graphs (https://www.w3.org/TR/owl2-mapping-to-rdf/)
for the axiom-to-triple tables every production below follows.

## This is a SUBSET, and the boundary is the point

It covers exactly the grammar the W3C OWL 2 catalogs need for their
functional-syntax-only entries — the ones the OWL probe reports as
`unsupported` today. Everything else is a CLEAN PARSE FAILURE
(`none`), which the caller reports as "unsupported input syntax": the
same honest skip, never a silent wrong answer. No production is a
literal match on one test's text; every one is a general grammar rule
over the alphabet the fixtures use.

Accepted:

    Prefix( pfx = <IRI> )*        before Ontology
    Ontology( Declaration/Axiom* )
    Declaration(ObjectProperty|DataProperty|NamedIndividual|Class (IRI))
    TransitiveObjectProperty(IRI)      FunctionalDataProperty(IRI)
    DataPropertyRange(IRI IRI)         DataPropertyAssertion(IRI IRI Lit)
    NegativeDataPropertyAssertion(IRI IRI Lit)
    DisjointDataProperties(IRI IRI)    exactly two arguments
    SubClassOf(CE CE)                  ClassAssertion(CE IRI)
    SubObjectPropertyOf(ObjectPropertyChain(IRI IRI) IRI)

    CE ::= IRI | DataHasValue(IRI Lit) | DataSomeValuesFrom(IRI DR)
         | DataAllValuesFrom(IRI DR)   | ObjectComplementOf(CE)
    DR ::= IRI | DataOneOf(Lit+) | DataComplementOf(DR)
         | DatatypeRestriction(IRI (IRI Lit)+)

## Blank-node labels are generated, and the counter is threaded

Every fresh node takes a label built from a counter that every
production threads through. Two expressions in one document therefore
never collide, and one expression parsed twice gives the same labels
— which is what makes a graph comparison of the result reproducible.
-/
import L4Factoidal.OWL.Vocabulary
import L4Factoidal.RDFS.Vocabulary

namespace L4Factoidal.OWL.FS

open L4Factoidal.RDF
open L4Factoidal.RDFS
open L4Factoidal.OWL.RL

/-! ## Vocabulary this module needs beyond the shared ones -/

def owlObjectPropertyIri : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#ObjectProperty", rfl⟩
def owlDatatypePropertyIri : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#DatatypeProperty", rfl⟩
def owlNamedIndividualIri : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#NamedIndividual", rfl⟩
def owlOnDatatypeIri : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#onDatatype", rfl⟩
def owlWithRestrictionsIri : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#withRestrictions", rfl⟩
def owlDatatypeComplementOfIri : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#datatypeComplementOf", rfl⟩
def owlNegativePropertyAssertionIri : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#NegativePropertyAssertion", rfl⟩

/-! ## The character layer

`Chars = Array Char` for O(1) indexing, as everywhere else in this
tree. The F* module indexes UTF-8 BYTES; Lean's `Char` is a codepoint
by construction, so the byte-rebuilding machinery has no counterpart
here — see `PORT_NOTES.md`. -/

abbrev Chars := Array Char

def charAt (s : Chars) (i : Nat) : Option Char := s[i]?

def isFsWs (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

def skipWs (s : Chars) (i : Nat) : Nat :=
  let rec go (j : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => j
    | f + 1 => match s[j]? with
      | some c => if isFsWs c then go (j + 1) f else j
      | none   => j
  go i (s.size + 1 - min i (s.size + 1))

/-- Identifier characters: keywords and the two halves of an
    abbreviated IRI. -/
def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-'

def takeIdent (s : Chars) (i : Nat) : String × Nat :=
  let rec go (j : Nat) (acc : List Char) (fuel : Nat) : List Char × Nat :=
    match fuel with
    | 0 => (acc.reverse, j)
    | f + 1 => match s[j]? with
      | some c => if isIdentChar c then go (j + 1) (c :: acc) f else (acc.reverse, j)
      | none   => (acc.reverse, j)
  let (cs, j) := go i [] (s.size + 1)
  (String.ofList cs, j)

/-- Read a MAXIMAL identifier run and compare it with `kw`. Maximal
    munch is what keeps a longer identifier that begins with `kw` from
    matching — there are no such pairs among these keywords, but the
    rule stays general. -/
def tryWord (s : Chars) (i : Nat) (kw : String) : Option Nat :=
  let (w, j) := takeIdent s i
  if w.isEmpty then none else if w == kw then some j else none

def isChar (s : Chars) (i : Nat) (c : Char) : Bool := s[i]? == some c

/-! ## IRIs and literals -/

/-- Scan from just after the opening `<`; returns the content and the
    position after `>`. -/
def scanAngleIri (s : Chars) (start : Nat) : Option (String × Nat) :=
  let rec go (j : Nat) (acc : List Char) (fuel : Nat) : Option (String × Nat) :=
    match fuel with
    | 0 => none
    | f + 1 => match s[j]? with
      | none   => none
      | some c => if c == '>' then some (String.ofList acc.reverse, j + 1)
                  else go (j + 1) (c :: acc) f
  go start [] (s.size + 1)

def lookupPrefix (ps : List (String × String)) (p : String) : Option String :=
  (ps.find? (fun (q, _) => q == p)).map (·.2)

/-- `PNAME_NS ':' PN_LOCAL`, e.g. `:a` (empty prefix) or
    `xsd:integer`. -/
def parseCurie (ps : List (String × String)) (s : Chars) (i : Nat)
    : Option (WfIri × Nat) :=
  let (pfx, i1) := takeIdent s i
  if !(isChar s i1 ':') then none
  else
    let (localPart, i2) := takeIdent s (i1 + 1)
    if localPart.isEmpty then none
    else match lookupPrefix ps pfx with
      | none    => none
      | some ns =>
          let full := ns ++ localPart
          if h : isIri full then some (⟨full, h⟩, i2) else none

def parseFsIri (ps : List (String × String)) (s : Chars) (i : Nat)
    : Option (WfIri × Nat) :=
  if isChar s i '<' then
    match scanAngleIri s (i + 1) with
    | none        => none
    | some (t, j) => if h : isIri t then some (⟨t, h⟩, j) else none
  else parseCurie ps s i

def scanQuoted (s : Chars) (start : Nat) : Option (String × Nat) :=
  let rec go (j : Nat) (acc : List Char) (fuel : Nat) : Option (String × Nat) :=
    match fuel with
    | 0 => none
    | f + 1 => match s[j]? with
      | none   => none
      | some c => if c == '"' then some (String.ofList acc.reverse, j + 1)
                  else go (j + 1) (c :: acc) f
  go start [] (s.size + 1)

/-- `"lexical"^^<datatype>`. Every literal in the target fixtures
    carries a datatype, and a literal without one is a clean parse
    failure rather than a guessed `xsd:string`. -/
def parseFsLiteral (ps : List (String × String)) (s : Chars) (i : Nat)
    : Option (WfLiteral × Nat) :=
  if !(isChar s i '"') then none
  else match scanQuoted s (i + 1) with
    | none => none
    | some (lex, j) =>
      let j1 := skipWs s j
      if isChar s j1 '^' && isChar s (j1 + 1) '^' then
        match parseFsIri ps s (j1 + 2) with
        | none => none
        | some (dt, j2) =>
            let l : Literal :=
              { lexicalForm := lex, datatype := dt, langTag := none, direction := none }
            if h : literalWf l then some (⟨l, h⟩, j2) else none
      else none

/-! ## Prefixes -/

def parsePrefixes (s : Chars) : Option (List (String × String) × Nat) :=
  let rec go (i : Nat) (acc : List (String × String)) (fuel : Nat)
      : Option (List (String × String) × Nat) :=
    match fuel with
    | 0 => some (acc, i)
    | f + 1 =>
      let i0 := skipWs s i
      match tryWord s i0 "Prefix" with
      | none => some (acc, i0)
      | some i1 =>
        let i2 := skipWs s i1
        if !(isChar s i2 '(') then none
        else
          let i3 := skipWs s (i2 + 1)
          let (pfx, i4) := takeIdent s i3
          if !(isChar s i4 ':') then none
          else
            let i5 := skipWs s (i4 + 1)
            if !(isChar s i5 '=') then none
            else
              let i6 := skipWs s (i5 + 1)
              if !(isChar s i6 '<') then none
              else match scanAngleIri s (i6 + 1) with
                | none => none
                | some (ns, i7) =>
                    let i8 := skipWs s i7
                    if !(isChar s i8 ')') then none
                    else go (i8 + 1) (acc ++ [(pfx, ns)]) f
  go 0 [] (s.size + 1)

/-! ## Blank-node labels -/

def bnRestriction (n : Nat) : Subject := .bnode ("owlfs_restr" ++ toString n)
def bnComplement (n : Nat) : Subject := .bnode ("owlfs_comp" ++ toString n)
def bnListCell (n : Nat) : Subject := .bnode ("owlfs_lst" ++ toString n)
def bnFacet (n : Nat) : Subject := .bnode ("owlfs_facet" ++ toString n)
def bnFacetCell (n : Nat) : Subject := .bnode ("owlfs_flst" ++ toString n)
def bnDataOneOf (n : Nat) : Subject := .bnode ("owlfs_dtoneof" ++ toString n)
def bnDataRestr (n : Nat) : Subject := .bnode ("owlfs_dtrestr" ++ toString n)
def bnDataComp (n : Nat) : Subject := .bnode ("owlfs_dtcomp" ++ toString n)
def bnNpa (n : Nat) : Subject := .bnode ("owlfs_npa" ++ toString n)
def bnChain (n : Nat) : Subject := .bnode ("owlfs_chain" ++ toString n)

def subjTerm : Subject → Term
  | .iri i   => .iri i
  | .bnode b => .bnode b

def termToSubject : Term → Option Subject
  | .iri i   => some (.iri i)
  | .bnode b => some (.bnode b)
  | _        => none

/-! ## Literal and facet lists -/

def parseLiteralList (ps : List (String × String)) (s : Chars) (i : Nat)
    : Option (List WfLiteral × Nat) :=
  let rec go (j : Nat) (acc : List WfLiteral) (fuel : Nat)
      : Option (List WfLiteral × Nat) :=
    match fuel with
    | 0 => none
    | f + 1 =>
      let j0 := skipWs s j
      if isChar s j0 ')' then
        -- `DataOneOf` needs at least one literal; an empty one is a
        -- parse failure rather than an empty datatype.
        (if acc.isEmpty then none else some (acc, j0))
      else match parseFsLiteral ps s j0 with
        | none        => none
        | some (l, j1) => go j1 (acc ++ [l]) f
  go i [] (s.size + 1)

/-- `T([v1 … vn])` — the `rdf:first`/`rdf:rest` collection. -/
def buildLiteralList : List WfLiteral → Nat → List Triple × Term × Nat
  | [],      bc => ([], .iri RL.rdfNil, bc)
  | l :: rest, bc =>
      let (restTriples, restTerm, bc1) := buildLiteralList rest bc
      let node := bnListCell bc1
      ( ⟨node, RL.rdfFirst, .literal l⟩ :: ⟨node, RL.rdfRest, restTerm⟩ :: restTriples,
        subjTerm node, bc1 + 1 )

def parseFacetList (ps : List (String × String)) (s : Chars) (i : Nat)
    : Option (List (WfIri × WfLiteral) × Nat) :=
  let rec go (j : Nat) (acc : List (WfIri × WfLiteral)) (fuel : Nat)
      : Option (List (WfIri × WfLiteral) × Nat) :=
    match fuel with
    | 0 => none
    | f + 1 =>
      let j0 := skipWs s j
      if isChar s j0 ')' then
        (if acc.isEmpty then none else some (acc, j0))
      else match parseFsIri ps s j0 with
        | none => none
        | some (facet, j1) =>
            let j2 := skipWs s j1
            match parseFsLiteral ps s j2 with
            | none        => none
            | some (l, j3) => go j3 (acc ++ [(facet, l)]) f
  go i [] (s.size + 1)

/-- Each `(facet, value)` pair becomes its OWN blank node carrying
    exactly one triple — the mapping specification says a
    facet-restriction node carries one — and the nodes are collected
    into an `rdf:first`/`rdf:rest` list. -/
def buildFacetList : List (WfIri × WfLiteral) → Nat → List Triple × Term × Nat
  | [],             bc => ([], .iri RL.rdfNil, bc)
  | (facet, l) :: rest, bc =>
      let (restTriples, restTerm, bc1) := buildFacetList rest bc
      let fnode := bnFacet bc1
      let vnode := bnFacetCell (bc1 + 1)
      ( ⟨fnode, facet, .literal l⟩
          :: ⟨vnode, RL.rdfFirst, subjTerm fnode⟩
          :: ⟨vnode, RL.rdfRest, restTerm⟩ :: restTriples,
        subjTerm vnode, bc1 + 2 )

/-! ## Class expressions and data ranges

Each production returns the term that DENOTES the expression, the
triples that define it, the position after the closing `)`, and the
updated blank-node counter. -/

/-- `DataHasValue(P Lit)` — a leaf; it never recurses. -/
def parseDataHasValue (ps : List (String × String)) (s : Chars) (i : Nat) (bc : Nat)
    : Option (Term × List Triple × Nat × Nat) :=
  let i1 := skipWs s i
  if !(isChar s i1 '(') then none
  else
    let i2 := skipWs s (i1 + 1)
    match parseFsIri ps s i2 with
    | none => none
    | some (prop, i3) =>
      let i4 := skipWs s i3
      match parseFsLiteral ps s i4 with
      | none => none
      | some (l, i5) =>
        let i6 := skipWs s i5
        if !(isChar s i6 ')') then none
        else
          let r := bnRestriction bc
          some (subjTerm r,
                [ ⟨r, RL.rdfType, .iri owlRestriction⟩,
                  ⟨r, owlOnProperty, .iri prop⟩,
                  ⟨r, owlHasValue, .literal l⟩ ],
                i6 + 1, bc + 1)

/-- `DataOneOf(v1 … vn)` — a leaf. -/
def parseDataOneOf (ps : List (String × String)) (s : Chars) (i : Nat) (bc : Nat)
    : Option (Term × List Triple × Nat × Nat) :=
  let i1 := skipWs s i
  if !(isChar s i1 '(') then none
  else
    let i2 := skipWs s (i1 + 1)
    match parseLiteralList ps s i2 with
    | none => none
    | some (lits, i3) =>
      let i4 := skipWs s i3
      if !(isChar s i4 ')') then none
      else
        let (lt, head, bc1) := buildLiteralList lits bc
        let dt := bnDataOneOf bc1
        some (subjTerm dt,
              lt ++ [ ⟨dt, RL.rdfType, .iri RL.rdfsDatatype⟩, ⟨dt, owlOneOf, head⟩ ],
              i4 + 1, bc1 + 1)

/-- `DatatypeRestriction(DT F1 v1 …)` — a leaf. -/
def parseDatatypeRestriction (ps : List (String × String)) (s : Chars) (i : Nat)
    (bc : Nat) : Option (Term × List Triple × Nat × Nat) :=
  let i1 := skipWs s i
  if !(isChar s i1 '(') then none
  else
    let i2 := skipWs s (i1 + 1)
    match parseFsIri ps s i2 with
    | none => none
    | some (baseDt, i3) =>
      match parseFacetList ps s i3 with
      | none => none
      | some (facets, i4) =>
        let i5 := skipWs s i4
        if !(isChar s i5 ')') then none
        else
          let (ft, head, bc1) := buildFacetList facets bc
          let dt := bnDataRestr bc1
          some (subjTerm dt,
                ft ++ [ ⟨dt, RL.rdfType, .iri RL.rdfsDatatype⟩,
                        ⟨dt, owlOnDatatypeIri, .iri baseDt⟩,
                        ⟨dt, owlWithRestrictionsIri, head⟩ ],
                i5 + 1, bc1 + 1)

mutual

partial def parseClassExprFS (ps : List (String × String)) (s : Chars) (i : Nat)
    (bc : Nat) : Option (Term × List Triple × Nat × Nat) :=
  let i0 := skipWs s i
  match parseFsIri ps s i0 with
  | some (iri, i1) => some (.iri iri, [], i1, bc)
  | none =>
  match tryWord s i0 "DataHasValue" with
  | some i1 => parseDataHasValue ps s i1 bc
  | none =>
  match tryWord s i0 "DataSomeValuesFrom" with
  | some i1 => parseDataValuesFrom ps s i1 bc owlSomeValuesFrom
  | none =>
  match tryWord s i0 "DataAllValuesFrom" with
  | some i1 => parseDataValuesFrom ps s i1 bc owlAllValuesFrom
  | none =>
  match tryWord s i0 "ObjectComplementOf" with
  | some i1 => parseObjectComplementOf ps s i1 bc
  | none => none

/-- `DataSomeValuesFrom(P DR)` and `DataAllValuesFrom(P DR)` differ
    only in which relation IRI the restriction carries. -/
partial def parseDataValuesFrom (ps : List (String × String)) (s : Chars) (i : Nat)
    (bc : Nat) (rel : WfIri) : Option (Term × List Triple × Nat × Nat) :=
  let i1 := skipWs s i
  if !(isChar s i1 '(') then none
  else
    let i2 := skipWs s (i1 + 1)
    match parseFsIri ps s i2 with
    | none => none
    | some (prop, i3) =>
      let i4 := skipWs s i3
      match parseDataRangeFS ps s i4 bc with
      | none => none
      | some (drTerm, drTriples, i5, bc1) =>
        let i6 := skipWs s i5
        if !(isChar s i6 ')') then none
        else
          let r := bnRestriction bc1
          some (subjTerm r,
                drTriples ++ [ ⟨r, RL.rdfType, .iri owlRestriction⟩,
                               ⟨r, owlOnProperty, .iri prop⟩,
                               ⟨r, rel, drTerm⟩ ],
                i6 + 1, bc1 + 1)

partial def parseObjectComplementOf (ps : List (String × String)) (s : Chars)
    (i : Nat) (bc : Nat) : Option (Term × List Triple × Nat × Nat) :=
  let i1 := skipWs s i
  if !(isChar s i1 '(') then none
  else
    let i2 := skipWs s (i1 + 1)
    match parseClassExprFS ps s i2 bc with
    | none => none
    | some (ceTerm, ceTriples, i3, bc1) =>
      let i4 := skipWs s i3
      if !(isChar s i4 ')') then none
      else
        let c := bnComplement bc1
        some (subjTerm c,
              ceTriples ++ [ ⟨c, RL.rdfType, .iri owlClass⟩,
                             ⟨c, owlComplementOf, ceTerm⟩ ],
              i4 + 1, bc1 + 1)

partial def parseDataRangeFS (ps : List (String × String)) (s : Chars) (i : Nat)
    (bc : Nat) : Option (Term × List Triple × Nat × Nat) :=
  let i0 := skipWs s i
  match parseFsIri ps s i0 with
  | some (iri, i1) => some (.iri iri, [], i1, bc)
  | none =>
  match tryWord s i0 "DataOneOf" with
  | some i1 => parseDataOneOf ps s i1 bc
  | none =>
  match tryWord s i0 "DataComplementOf" with
  | some i1 => parseDataComplementOf ps s i1 bc
  | none =>
  match tryWord s i0 "DatatypeRestriction" with
  | some i1 => parseDatatypeRestriction ps s i1 bc
  | none => none

partial def parseDataComplementOf (ps : List (String × String)) (s : Chars)
    (i : Nat) (bc : Nat) : Option (Term × List Triple × Nat × Nat) :=
  let i1 := skipWs s i
  if !(isChar s i1 '(') then none
  else
    let i2 := skipWs s (i1 + 1)
    match parseDataRangeFS ps s i2 bc with
    | none => none
    | some (drTerm, drTriples, i3, bc1) =>
      let i4 := skipWs s i3
      if !(isChar s i4 ')') then none
      else
        let dt := bnDataComp bc1
        some (subjTerm dt,
              drTriples ++ [ ⟨dt, RL.rdfType, .iri RL.rdfsDatatype⟩,
                             ⟨dt, owlDatatypeComplementOfIri, drTerm⟩ ],
              i4 + 1, bc1 + 1)

end

/-! ## Axioms -/

def parseDeclaration (ps : List (String × String)) (s : Chars) (i : Nat)
    : Option (Triple × Nat) :=
  let i1 := skipWs s i
  if !(isChar s i1 '(') then none
  else
    let i2 := skipWs s (i1 + 1)
    let kind : Option (Nat × WfIri) :=
      match tryWord s i2 "ObjectProperty" with
      | some p => some (p, owlObjectPropertyIri)
      | none => match tryWord s i2 "DataProperty" with
        | some p => some (p, owlDatatypePropertyIri)
        | none => match tryWord s i2 "NamedIndividual" with
          | some p => some (p, owlNamedIndividualIri)
          | none => match tryWord s i2 "Class" with
            | some p => some (p, owlClass)
            | none => none
    match kind with
    | none => none
    | some (i3, typeIri) =>
      let i4 := skipWs s i3
      if !(isChar s i4 '(') then none
      else
        let i5 := skipWs s (i4 + 1)
        match parseFsIri ps s i5 with
        | none => none
        | some (iri, i6) =>
          let i7 := skipWs s i6
          if !(isChar s i7 ')') then none
          else
            let i8 := skipWs s (i7 + 1)
            if !(isChar s i8 ')') then none
            else some (⟨.iri iri, RL.rdfType, .iri typeIri⟩, i8 + 1)

/-- `TransitiveObjectProperty(IRI)` and `FunctionalDataProperty(IRI)`
    both map to one `rdf:type` triple; only the marker differs. -/
def parseUnaryTypeAxiom (ps : List (String × String)) (s : Chars) (i : Nat)
    (typeIri : WfIri) : Option (Triple × Nat) :=
  let i1 := skipWs s i
  if !(isChar s i1 '(') then none
  else
    let i2 := skipWs s (i1 + 1)
    match parseFsIri ps s i2 with
    | none => none
    | some (iri, i3) =>
      let i4 := skipWs s i3
      if !(isChar s i4 ')') then none
      else some (⟨.iri iri, RL.rdfType, .iri typeIri⟩, i4 + 1)

def parseDataPropertyRange (ps : List (String × String)) (s : Chars) (i : Nat)
    : Option (Triple × Nat) :=
  let i1 := skipWs s i
  if !(isChar s i1 '(') then none
  else
    let i2 := skipWs s (i1 + 1)
    match parseFsIri ps s i2 with
    | none => none
    | some (prop, i3) =>
      let i4 := skipWs s i3
      match parseFsIri ps s i4 with
      | none => none
      | some (dt, i5) =>
        let i6 := skipWs s i5
        if !(isChar s i6 ')') then none
        else some (⟨.iri prop, RL.rdfsRange, .iri dt⟩, i6 + 1)

def parseDataPropertyAssertion (ps : List (String × String)) (s : Chars) (i : Nat)
    : Option (Triple × Nat) :=
  let i1 := skipWs s i
  if !(isChar s i1 '(') then none
  else
    let i2 := skipWs s (i1 + 1)
    match parseFsIri ps s i2 with
    | none => none
    | some (prop, i3) =>
      let i4 := skipWs s i3
      match parseFsIri ps s i4 with
      | none => none
      | some (ind, i5) =>
        let i6 := skipWs s i5
        match parseFsLiteral ps s i6 with
        | none => none
        | some (l, i7) =>
          let i8 := skipWs s i7
          if !(isChar s i8 ')') then none
          else some (⟨.iri ind, prop, .literal l⟩, i8 + 1)

def parseSubClassOfFS (ps : List (String × String)) (s : Chars) (i : Nat) (bc : Nat)
    : Option (List Triple × Nat × Nat) :=
  let i1 := skipWs s i
  if !(isChar s i1 '(') then none
  else
    let i2 := skipWs s (i1 + 1)
    match parseClassExprFS ps s i2 bc with
    | none => none
    | some (ce1, t1, i3, bc1) =>
      let i4 := skipWs s i3
      match parseClassExprFS ps s i4 bc1 with
      | none => none
      | some (ce2, t2, i5, bc2) =>
        let i6 := skipWs s i5
        if !(isChar s i6 ')') then none
        else match termToSubject ce1 with
          | none      => none
          | some sub1 => some (t1 ++ t2 ++ [⟨sub1, RL.rdfsSubClassOf, ce2⟩], i6 + 1, bc2)

def parseClassAssertionFS (ps : List (String × String)) (s : Chars) (i : Nat)
    (bc : Nat) : Option (List Triple × Nat × Nat) :=
  let i1 := skipWs s i
  if !(isChar s i1 '(') then none
  else
    let i2 := skipWs s (i1 + 1)
    match parseClassExprFS ps s i2 bc with
    | none => none
    | some (ceTerm, ceTriples, i3, bc1) =>
      let i4 := skipWs s i3
      match parseFsIri ps s i4 with
      | none => none
      | some (ind, i5) =>
        let i6 := skipWs s i5
        if !(isChar s i6 ')') then none
        else some (ceTriples ++ [⟨.iri ind, RL.rdfType, ceTerm⟩], i6 + 1, bc1)

/-- `DisjointDataProperties(P1 P2)`, exactly two arguments. The
    mapping specification makes n = 2 the direct-triple case; n > 2
    needs an `owl:AllDisjointProperties` encoding this module does not
    produce, so a third argument is a clean parse failure. -/
def parseDisjointDataProperties (ps : List (String × String)) (s : Chars) (i : Nat)
    : Option (Triple × Nat) :=
  let i1 := skipWs s i
  if !(isChar s i1 '(') then none
  else
    let i2 := skipWs s (i1 + 1)
    match parseFsIri ps s i2 with
    | none => none
    | some (p1, i3) =>
      let i4 := skipWs s i3
      match parseFsIri ps s i4 with
      | none => none
      | some (p2, i5) =>
        let i6 := skipWs s i5
        if !(isChar s i6 ')') then none
        else some (⟨.iri p1, owlPropertyDisjointWith, .iri p2⟩, i6 + 1)

def parseNegativeDataPropertyAssertion (ps : List (String × String)) (s : Chars)
    (i : Nat) (bc : Nat) : Option (List Triple × Nat × Nat) :=
  let i1 := skipWs s i
  if !(isChar s i1 '(') then none
  else
    let i2 := skipWs s (i1 + 1)
    match parseFsIri ps s i2 with
    | none => none
    | some (prop, i3) =>
      let i4 := skipWs s i3
      match parseFsIri ps s i4 with
      | none => none
      | some (ind, i5) =>
        let i6 := skipWs s i5
        match parseFsLiteral ps s i6 with
        | none => none
        | some (l, i7) =>
          let i8 := skipWs s i7
          if !(isChar s i8 ')') then none
          else
            let n := bnNpa bc
            some ([ ⟨n, RL.rdfType, .iri owlNegativePropertyAssertionIri⟩,
                    ⟨n, owlSourceIndividual, .iri ind⟩,
                    ⟨n, owlAssertionProperty, .iri prop⟩,
                    ⟨n, owlTargetValue, .literal l⟩ ], i8 + 1, bc + 1)

/-- `SubObjectPropertyOf(ObjectPropertyChain(P1 P2) Q)` — only the
    two-link chain, which is the shape the corpus needs. -/
def parseSubObjectPropertyOf (ps : List (String × String)) (s : Chars) (i : Nat)
    (bc : Nat) : Option (List Triple × Nat × Nat) :=
  let i1 := skipWs s i
  if !(isChar s i1 '(') then none
  else
    let i2 := skipWs s (i1 + 1)
    match tryWord s i2 "ObjectPropertyChain" with
    | none => none
    | some i3 =>
      let i4 := skipWs s i3
      if !(isChar s i4 '(') then none
      else
        let i5 := skipWs s (i4 + 1)
        match parseFsIri ps s i5 with
        | none => none
        | some (p1, i6) =>
          let i7 := skipWs s i6
          match parseFsIri ps s i7 with
          | none => none
          | some (p2, i8) =>
            let i9 := skipWs s i8
            if !(isChar s i9 ')') then none
            else
              let i10 := skipWs s (i9 + 1)
              match parseFsIri ps s i10 with
              | none => none
              | some (q, i11) =>
                let i12 := skipWs s i11
                if !(isChar s i12 ')') then none
                else
                  let b1 := bnChain bc
                  let b2 := bnChain (bc + 1)
                  some ([ ⟨b1, RL.rdfFirst, .iri p1⟩,
                          ⟨b1, RL.rdfRest, subjTerm b2⟩,
                          ⟨b2, RL.rdfFirst, .iri p2⟩,
                          ⟨b2, RL.rdfRest, .iri RL.rdfNil⟩,
                          ⟨.iri q, owlPropertyChainAxiom, subjTerm b1⟩ ],
                        i12 + 1, bc + 2)

/-! ## The ontology body and the entry point -/

def parseAxioms (ps : List (String × String)) (s : Chars) (i0 : Nat)
    : Option (List Triple × Nat) :=
  let rec go (i : Nat) (bc : Nat) (acc : List Triple) (fuel : Nat)
      : Option (List Triple × Nat) :=
    match fuel with
    | 0 => none
    | f + 1 =>
      let i' := skipWs s i
      if isChar s i' ')' then some (acc, i')
      else
        let one : Option (List Triple × Nat × Nat) :=
          match tryWord s i' "Declaration" with
          | some j => (parseDeclaration ps s j).map (fun (t, k) => ([t], k, bc))
          | none =>
          match tryWord s i' "TransitiveObjectProperty" with
          | some j => (parseUnaryTypeAxiom ps s j owlTransitiveProperty).map
                        (fun (t, k) => ([t], k, bc))
          | none =>
          match tryWord s i' "FunctionalDataProperty" with
          | some j => (parseUnaryTypeAxiom ps s j owlFunctionalProperty).map
                        (fun (t, k) => ([t], k, bc))
          | none =>
          match tryWord s i' "DataPropertyRange" with
          | some j => (parseDataPropertyRange ps s j).map (fun (t, k) => ([t], k, bc))
          | none =>
          match tryWord s i' "DataPropertyAssertion" with
          | some j => (parseDataPropertyAssertion ps s j).map (fun (t, k) => ([t], k, bc))
          | none =>
          match tryWord s i' "ClassAssertion" with
          | some j => parseClassAssertionFS ps s j bc
          | none =>
          match tryWord s i' "SubObjectPropertyOf" with
          | some j => parseSubObjectPropertyOf ps s j bc
          | none =>
          match tryWord s i' "SubClassOf" with
          | some j => parseSubClassOfFS ps s j bc
          | none =>
          match tryWord s i' "DisjointDataProperties" with
          | some j => (parseDisjointDataProperties ps s j).map (fun (t, k) => ([t], k, bc))
          | none =>
          match tryWord s i' "NegativeDataPropertyAssertion" with
          | some j => parseNegativeDataPropertyAssertion ps s j bc
          -- An unknown construct is a CLEAN parse failure. Skipping it
          -- would produce a graph missing an axiom, and a missing
          -- axiom makes an inconsistent ontology look consistent.
          | none => none
        match one with
        | none            => none
        | some (ts, j, bc') => go j bc' (acc ++ ts) f
  go i0 0 [] (s.size + 1)

/-- Read a whole functional-syntax document into triples. `none` for
    anything outside the subset — the caller reports that as
    "unsupported input syntax", never as an empty ontology. -/
def parseFunctionalSyntax (input : String) : Option (List Triple) :=
  let s : Chars := input.toList.toArray
  match parsePrefixes s with
  | none => none
  | some (ps, i0) =>
    let i1 := skipWs s i0
    match tryWord s i1 "Ontology" with
    | none => none
    | some i2 =>
      let i3 := skipWs s i2
      if !(isChar s i3 '(') then none
      else
        let i4 := skipWs s (i3 + 1)
        match parseAxioms ps s i4 with
        | none => none
        | some (ts, i5) => if isChar s i5 ')' then some ts else none

end L4Factoidal.OWL.FS
