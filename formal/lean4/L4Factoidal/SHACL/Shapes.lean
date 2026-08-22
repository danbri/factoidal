/-
L4Factoidal.SHACL.Shapes — the typed abstract syntax of SHACL Core
shapes and the decoder from a shapes graph (RDF) into it.

W3C SHACL Recommendation (20 July 2017), https://www.w3.org/TR/shacl/:
  §2.1   targets                    → `Target`
  §2.2   node / property shapes     → `Shape` (`isProperty`, `path`)
  §2.3.1 property paths             → `Path`, `decodePath`
  §2.3.2 non-validating properties  → `Shape.severity`, `Shape.message`
  §3.6.1 deactivated shapes         → dropped at decode time
  §4     Core constraint components → `Constraint`, `decodeConstraints`

Port of `formal/fstar/SHACL.Validation.fst` sections 2–7 (the AST) and
11a/11b/11c/11f (`rdf_list_terms`, `parse_path`, `build_targets`,
`build_constraints`, `build_shape`, `parse_shape_from_graph_pure`).
The F* constructors for SHACL 1.2 (list-valued sh:datatype,
sh:singleLine, sh:memberShape, …), SHACL-AF (sh:values, sh:targetWhere)
and SHACL-SPARQL (CC_Sparql, CC_Custom, T_Sparql) are not ported —
see `Vocabulary.lean`'s header. A shapes graph that uses a SHACL-SPARQL
predicate is recorded in `ShapesGraph.unsupported` so the harness can
name it.

Decoding is a total function of the shapes graph. Every graph walk
that follows runtime data (rdf:first/rdf:rest chains, nested path
nodes) is fuel-bounded by the graph size, as in the F* source; running
out of fuel yields an inert value (an empty sequence path, an empty
list), never a fabricated reading.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.SHACL.Vocabulary
import L4Factoidal.RDF.Graph

namespace L4Factoidal.SHACL

open L4Factoidal.RDF

/-! ## §3.6.1.3 severity -/

/-- sh:severity. The Recommendation names three; any other IRI is
allowed as a value ("the value of sh:severity is an IRI") and is
reported back verbatim (core/misc/severity-002). -/
inductive Severity where
  | info
  | warning
  | violation
  | custom (i : WfIri)
  deriving DecidableEq, Repr, Inhabited

/-! ## §4.1.3 node kinds -/

inductive NodeKind where
  | blankNode
  | iri
  | literal
  | blankNodeOrIri
  | blankNodeOrLiteral
  | iriOrLiteral
  deriving DecidableEq, Repr, Inhabited

/-! ## §2.3.1 property paths -/

/-- A SHACL property path: the seven syntactic forms of §2.3.1
(predicate, inverse, sequence, alternative, zero-or-more, one-or-more,
zero-or-one). -/
inductive Path where
  | pred (p : WfIri)
  | inverse (p : Path)
  | seq (ps : List Path)
  | alt (ps : List Path)
  | zeroOrMore (p : Path)
  | oneOrMore (p : Path)
  | zeroOrOne (p : Path)
  deriving Repr, Inhabited

/-! ## §2.1 targets -/

/-- The target declarations of §2.1.1–§2.1.4, plus the implicit class
target of §2.1.3.1 (a node shape that is also a class). SPARQL-based
targets (SHACL-SPARQL §5) are not a constructor: the decoder names them
in `ShapesGraph.unsupported`. -/
inductive Target where
  | cls (c : WfIri)
  | node (t : Term)
  | subjectsOf (p : WfIri)
  | objectsOf (p : WfIri)
  | implicitClass (c : WfIri)
  deriving DecidableEq, Repr

instance : Inhabited Target := ⟨.node (.bnode "")⟩

/-- A shape is referenced by the string of its IRI, or `"_:" ++ label`
for a blank-node shape (F* `shape_ref`). -/
abbrev ShapeRef := String

/-! ## §4 the Core constraint components -/

/-- One parameterised Core constraint component (§4.1–§4.8). The
logical components (§4.6) and sh:node / sh:qualifiedValueShape (§4.7)
refer to other shapes by `ShapeRef`; they are resolved against the
shapes graph at validation time, so the AST stays a finite tree over
an arbitrary (possibly cyclic) shapes graph. -/
inductive Constraint where
  -- §4.1 value type
  | cls (c : WfIri)
  | datatype (dt : WfIri)
  | nodeKind (nk : NodeKind)
  -- §4.2 cardinality
  | minCount (n : Nat)
  | maxCount (n : Nat)
  -- §4.3 value range
  | minExclusive (t : Term)
  | minInclusive (t : Term)
  | maxExclusive (t : Term)
  | maxInclusive (t : Term)
  -- §4.4 string-based
  | minLength (n : Nat)
  | maxLength (n : Nat)
  | pattern (re : String) (flags : String)
  | languageIn (langs : List String)
  | uniqueLang (b : Bool)
  -- §4.5 property pair
  | equals (p : Path)
  | disjoint (p : Path)
  | lessThan (p : Path)
  | lessThanOrEquals (p : Path)
  -- §4.6 logical
  | notOf (r : ShapeRef)
  | andOf (rs : List ShapeRef)
  | orOf (rs : List ShapeRef)
  | xoneOf (rs : List ShapeRef)
  -- §4.7 shape-based
  | nodeOf (r : ShapeRef)
  | qualifiedMinCount (r : ShapeRef) (n : Nat) (disjoint : Bool)
  | qualifiedMaxCount (r : ShapeRef) (n : Nat) (disjoint : Bool)
  -- §4.8 other
  | closed (ignored : List WfIri)
  | hasValue (t : Term)
  | inSet (items : List Term)
  deriving Repr, Inhabited

/-- §2.2: one record covers node shapes and property shapes; a
property shape has `isProperty = true` and `path = some _` (§2.3,
"a property shape is a shape ... that has exactly one value for
sh:path"). -/
structure Shape where
  id           : ShapeRef
  isProperty   : Bool
  path         : Option Path
  targets      : List Target
  severity     : Severity
  message      : Option WfLiteral
  constraints  : List Constraint
  /-- The shapes named by sh:property (§2.2 "property shapes of a
  shape"), by reference. -/
  propertyRefs : List ShapeRef
  deriving Repr, Inhabited

/-- §2.2 "the property shape must have exactly one value for sh:path"
and a node shape none: the shape-arity well-formedness check (F*
`shape_well_formed`). -/
def Shape.wellFormed (s : Shape) : Bool :=
  if s.isProperty then s.path.isSome else s.path.isNone

/-- The decoded shapes graph. `unsupported` lists the SHACL-SPARQL
feature names found in the source graph (empty for a SHACL Core
shapes graph). -/
structure ShapesGraph where
  shapes      : List Shape
  unsupported : List String := []
  deriving Repr, Inhabited

def ShapesGraph.empty : ShapesGraph := { shapes := [] }

/-- Look a shape up by reference (F* `lookup_shape`). -/
def lookupShape (r : ShapeRef) : List Shape → Option Shape
  | []        => none
  | s :: rest => if s.id == r then some s else lookupShape r rest

/-! ## Graph accessors

Specification-level list scans, as in `RDFS/Closure.lean`. -/

/-- Every object of a `(s, p, ·)` triple. -/
def objectsOf (g : Graph) (s : Subject) (p : WfIri) : List Term :=
  (g.filter (fun t => t.s == s && t.p == p)).map (fun t => t.o)

/-- The objects of `(t, p, ·)` when `t` can be a subject, else none. -/
def objectsOfTerm (g : Graph) (t : Term) (p : WfIri) : List Term :=
  match t.toSubject? with
  | some s => objectsOf g s p
  | none   => []

/-- Every subject of a `(·, p, o)` triple, as terms. -/
def subjectsOf (g : Graph) (p : WfIri) (o : Term) : List Term :=
  (g.filter (fun t => t.p == p && t.o.eqb o)).map (fun t => t.s.toTerm)

/-- The distinct subjects of a graph, in first-appearance order. -/
def distinctSubjects (g : Graph) : List Subject :=
  g.foldl (fun acc t => if acc.contains t.s then acc else acc ++ [t.s]) []

/-- Deduplicate terms under the engine equality `Term.eqb`, keeping
first occurrences (F* `dedup_terms`). -/
def dedupTerms (l : List Term) : List Term :=
  l.foldl (fun acc t => if acc.any (fun u => u.eqb t) then acc else acc ++ [t]) []

/-- Does `t` occur in `l` under `Term.eqb`? -/
def termMem (t : Term) (l : List Term) : Bool := l.any (fun u => u.eqb t)

/-- Walk an RDF collection (rdf:first / rdf:rest chain ending in
rdf:nil) from `head`. Fuel-bounded by the graph size (F*
`rdf_list_terms`). A malformed chain yields the prefix read so far. -/
def rdfListTerms (g : Graph) : Term → Nat → List Term
  | _, 0 => []
  | head, fuel + 1 =>
    match head with
    | .bnode _ | .iri _ =>
      if head == .iri rdfNil then []
      else
        match objectsOfTerm g head rdfFirst, objectsOfTerm g head rdfRest with
        | h :: _, r :: _ => h :: rdfListTerms g r fuel
        | _, _ => []
    | _ => []

/-- A shape reference from a term: an IRI's string, or `"_:" ++ label`.
Literals and triple terms are not shape references. -/
def termToShapeRef : Term → Option ShapeRef
  | .iri i   => some i.val
  | .bnode b => some ("_:" ++ b)
  | _        => none

def subjectToShapeRef : Subject → ShapeRef
  | .iri i   => i.val
  | .bnode b => "_:" ++ b

/-- Inverse of `termToShapeRef` / `subjectToShapeRef`: the term a
shape reference denotes, for sh:sourceShape in the report. -/
def shapeRefToTerm (r : ShapeRef) : Term :=
  if r.startsWith "_:" then .bnode (String.ofList (r.toList.drop 2))
  else if h : isIri r = true then .iri ⟨r, h⟩
  else .bnode r

/-- The lexical form of a term for the string-based components
(§4.4: "the string representation of the value node" — literals and
IRIs have one; blank nodes do not). -/
def termLexical : Term → Option String
  | .literal l => some l.val.lexicalForm
  | .iri i     => some i.val
  | _          => none

/-- A non-negative integer parameter (sh:minCount 1 …): the first
literal's lexical form read as a natural number. -/
def firstNat : List Term → Option Nat
  | .literal l :: _ => l.val.lexicalForm.toNat?
  | _               => none

/-- A boolean parameter, matched LEXICALLY against `"true"` — the
suite's own reading (core/property/uniqueLang-002-shapes.ttl:
`"1"^^xsd:boolean` is deliberately not `"true"^^xsd:boolean` for a
SHACL parameter). -/
def firstBool : List Term → Option Bool
  | .literal l :: _ => some (l.val.lexicalForm == "true")
  | _               => none

def nodeKindOfIri (i : WfIri) : Option NodeKind :=
  if i == shNkBlankNode then some .blankNode
  else if i == shNkIRI then some .iri
  else if i == shNkLiteral then some .literal
  else if i == shNkBlankNodeOrIRI then some .blankNodeOrIri
  else if i == shNkBlankNodeOrLiteral then some .blankNodeOrLiteral
  else if i == shNkIRIOrLiteral then some .iriOrLiteral
  else none

def severityOfIri (i : WfIri) : Severity :=
  if i == shViolation then .violation
  else if i == shWarning then .warning
  else if i == shInfo then .info
  else .custom i

/-! ## §2.3.1 path decoding

The seven forms: a predicate path is an IRI; the others are blank
nodes carrying one of sh:inversePath / sh:alternativePath /
sh:zeroOrMorePath / sh:oneOrMorePath / sh:zeroOrOnePath, or an RDF
list (sequence). An rdf:first/rdf:rest list is read FIRST, so a node
that is both a list and carries a sh:*Path triple reads as a sequence
(core/path/path-strange-001/002: the suite expects the list reading;
for well-formed paths, which satisfy exactly one rule, the order is
unobservable). Mutual structural recursion on fuel, as F*
`parse_path` / `parse_path_list`. -/

mutual
  def decodePath (g : Graph) : Term → Nat → Path
    | _, 0 => .seq []
    | t, fuel + 1 =>
      match t with
      | .iri i => .pred i
      | .bnode _ =>
        match objectsOfTerm g t rdfFirst with
        | _ :: _ => .seq (decodePathList g (rdfListTerms g t fuel) fuel)
        | [] =>
          match objectsOfTerm g t shInversePath with
          | [.iri ip] => .inverse (.pred ip)
          | _ =>
            match objectsOfTerm g t shAlternativePath with
            | altHead :: _ => .alt (decodePathList g (rdfListTerms g altHead fuel) fuel)
            | [] =>
              match objectsOfTerm g t shZeroOrMorePath with
              | zp :: _ => .zeroOrMore (decodePath g zp fuel)
              | [] =>
                match objectsOfTerm g t shOneOrMorePath with
                | op :: _ => .oneOrMore (decodePath g op fuel)
                | [] =>
                  match objectsOfTerm g t shZeroOrOnePath with
                  | zop :: _ => .zeroOrOne (decodePath g zop fuel)
                  | [] => .seq []
      | _ => .seq []

  def decodePathList (g : Graph) : List Term → Nat → List Path
    | _, 0 => []
    | [], _ + 1 => []
    | t :: rest, fuel + 1 => decodePath g t fuel :: decodePathList g rest fuel
end

/-! ## §2.1 target decoding -/

/-- The targets declared on a shape node (F* `build_targets`). The
implicit class target (§2.1.3.1) applies to an IRI that is both a
shape (`rdf:type sh:NodeShape`, or any SHACL-vocabulary subject —
see `isShapeEstablishing`) and a class (`rdf:type rdfs:Class` or
`owl:Class`). -/
def decodeTargets (g : Graph) (s : Subject) : List Target :=
  let viaClass := (objectsOf g s shTargetClass).filterMap fun t =>
    match t with | .iri i => some (Target.cls i) | _ => none
  let viaNode := (objectsOf g s shTargetNode).map Target.node
  let viaSubjOf := (objectsOf g s shTargetSubjectsOf).filterMap fun t =>
    match t with | .iri i => some (Target.subjectsOf i) | _ => none
  let viaObjOf := (objectsOf g s shTargetObjectsOf).filterMap fun t =>
    match t with | .iri i => some (Target.objectsOf i) | _ => none
  let implicit :=
    match s with
    | .iri i =>
      let types := objectsOf g s rdfType
      let isClass := types.any (fun t => t == .iri rdfsClass || t == .iri owlClass)
      let isNodeShape := types.any (fun t => t == .iri shNodeShape)
      if isClass && isNodeShape then [Target.implicitClass i] else []
    | .bnode _ => []
  viaClass ++ viaNode ++ viaSubjOf ++ viaObjOf ++ implicit

/-! ## §4 constraint decoding -/

/-- The shape references in an RDF list (sh:and / sh:or / sh:xone). -/
def shapeRefList (g : Graph) (head : Term) (fuel : Nat) : List ShapeRef :=
  (rdfListTerms g head fuel).filterMap termToShapeRef

/-- §4.7.2 / §4.7.3: sh:qualifiedMinCount / sh:qualifiedMaxCount apply
only together with sh:qualifiedValueShape (core/node/qualified-001:
the counts without a qualified shape impose nothing). -/
def decodeQualified (g : Graph) (s : Subject) : List Constraint :=
  match objectsOf g s shQualifiedValueShape with
  | qvs :: _ =>
    match termToShapeRef qvs with
    | some qref =>
      let qdisjoint := (firstBool (objectsOf g s shQualifiedValueShapesDisjoint)).getD false
      let qmin := match firstNat (objectsOf g s shQualifiedMinCount) with
        | some n => [Constraint.qualifiedMinCount qref n qdisjoint] | none => []
      let qmax := match firstNat (objectsOf g s shQualifiedMaxCount) with
        | some n => [Constraint.qualifiedMaxCount qref n qdisjoint] | none => []
      qmin ++ qmax
    | none => []
  | [] => []

/-- Every Core constraint component whose parameters occur on the
shape node `s` (F* `build_constraints`, restricted to Core). The
order is the F* order, which the report comparison does not observe
(reports compare up to isomorphism). -/
def decodeConstraints (g : Graph) (s : Subject) : List Constraint :=
  let fuel := g.length + 1
  let minCount := match firstNat (objectsOf g s shMinCount) with
    | some n => [Constraint.minCount n] | none => []
  let maxCount := match firstNat (objectsOf g s shMaxCount) with
    | some n => [Constraint.maxCount n] | none => []
  let datatype := (objectsOf g s shDatatype).filterMap fun t =>
    match t with | .iri i => some (Constraint.datatype i) | _ => none
  let nodeKind := (objectsOf g s shNodeKind).filterMap fun t =>
    match t with
    | .iri i => (nodeKindOfIri i).map Constraint.nodeKind
    | _ => none
  let cls := (objectsOf g s shClass).filterMap fun t =>
    match t with | .iri i => some (Constraint.cls i) | _ => none
  let inSet := match objectsOf g s shIn with
    | head :: _ => [Constraint.inSet (rdfListTerms g head fuel)] | [] => []
  let hasValue := (objectsOf g s shHasValue).map Constraint.hasValue
  let pattern := match objectsOf g s shPattern with
    | .literal l :: _ =>
      let flags := match objectsOf g s shFlags with
        | .literal fl :: _ => fl.val.lexicalForm | _ => ""
      [Constraint.pattern l.val.lexicalForm flags]
    | _ => []
  let minLength := match firstNat (objectsOf g s shMinLength) with
    | some n => [Constraint.minLength n] | none => []
  let maxLength := match firstNat (objectsOf g s shMaxLength) with
    | some n => [Constraint.maxLength n] | none => []
  let languageIn := match objectsOf g s shLanguageIn with
    | head :: _ =>
      [Constraint.languageIn ((rdfListTerms g head fuel).filterMap fun t =>
        match t with | .literal l => some l.val.lexicalForm | _ => none)]
    | [] => []
  let uniqueLang := match firstBool (objectsOf g s shUniqueLang) with
    | some b => [Constraint.uniqueLang b] | none => []
  let minInc := (objectsOf g s shMinInclusive).map Constraint.minInclusive
  let maxInc := (objectsOf g s shMaxInclusive).map Constraint.maxInclusive
  let minExc := (objectsOf g s shMinExclusive).map Constraint.minExclusive
  let maxExc := (objectsOf g s shMaxExclusive).map Constraint.maxExclusive
  let nots := (objectsOf g s shNot).filterMap fun t => (termToShapeRef t).map Constraint.notOf
  let ands := match objectsOf g s shAnd with
    | head :: _ => [Constraint.andOf (shapeRefList g head fuel)] | [] => []
  let ors := match objectsOf g s shOr with
    | head :: _ => [Constraint.orOf (shapeRefList g head fuel)] | [] => []
  let xones := match objectsOf g s shXone with
    | head :: _ => [Constraint.xoneOf (shapeRefList g head fuel)] | [] => []
  let nodes := (objectsOf g s shNode).filterMap fun t => (termToShapeRef t).map Constraint.nodeOf
  let qualified := decodeQualified g s
  let equals := (objectsOf g s shEquals).map fun t => Constraint.equals (decodePath g t fuel)
  let disjoint := (objectsOf g s shDisjoint).map fun t => Constraint.disjoint (decodePath g t fuel)
  let lessThan := (objectsOf g s shLessThan).map fun t => Constraint.lessThan (decodePath g t fuel)
  let lessThanOrEquals := (objectsOf g s shLessThanOrEquals).map fun t =>
    Constraint.lessThanOrEquals (decodePath g t fuel)
  let closed :=
    let ignored := match objectsOf g s shIgnoredProperties with
      | head :: _ => (rdfListTerms g head fuel).filterMap fun t =>
          match t with | .iri i => some i | _ => none
      | [] => []
    match firstBool (objectsOf g s shClosed) with
    | some true => [Constraint.closed ignored]
    | _ => []
  minCount ++ maxCount ++ datatype ++ nodeKind ++ cls ++ inSet ++ hasValue ++ pattern ++
  minLength ++ maxLength ++ languageIn ++ uniqueLang ++ minInc ++ maxInc ++ minExc ++ maxExc ++
  nots ++ ands ++ ors ++ xones ++ nodes ++ qualified ++ equals ++ disjoint ++ lessThan ++
  lessThanOrEquals ++ closed

/-! ## §2 shape decoding -/

/-- A triple that makes its subject a shape: any sh: predicate, or
`rdf:type sh:NodeShape` / `rdf:type sh:PropertyShape`. §2: "every
subject of a SHACL-vocabulary triple" is the F* criterion; it covers
named shapes and the anonymous nested shapes reached through
sh:property / sh:node / sh:not / sh:and / sh:or / sh:xone alike, each
of which carries at least one sh: triple of its own. -/
def isShapeTriggerTriple (t : Triple) : Bool :=
  t.p.val.startsWith shNs ||
  (t.p == rdfType && (t.o == .iri shNodeShape || t.o == .iri shPropertyShape))

/-- §3.6.1: `sh:deactivated true` switches a shape off. -/
def isDeactivated (g : Graph) (s : Subject) : Bool :=
  firstBool (objectsOf g s shDeactivated) == some true

def isShapeEstablishing (g : Graph) (s : Subject) : Bool :=
  g.any (fun t => t.s == s && isShapeTriggerTriple t) && !isDeactivated g s

/-- Decode one shape node (F* `build_shape`). -/
def decodeShape (g : Graph) (s : Subject) : Shape :=
  let pathObjs := objectsOf g s shPath
  let path := match pathObjs with
    | head :: _ => some (decodePath g head (g.length + 1))
    | [] => none
  let severity := match objectsOf g s shSeverity with
    | .iri i :: _ => severityOfIri i
    | _ => .violation
  let message := match objectsOf g s shMessage with
    | .literal l :: _ => some l
    | _ => none
  { id := subjectToShapeRef s,
    isProperty := !pathObjs.isEmpty,
    path := path,
    targets := decodeTargets g s,
    severity := severity,
    message := message,
    constraints := decodeConstraints g s,
    propertyRefs := (objectsOf g s shProperty).filterMap termToShapeRef }

/-- The SHACL-SPARQL feature names a graph uses (predicates only). -/
def sparqlFeaturesUsed (g : Graph) : List String :=
  sparqlFeaturePredicates.filterMap fun (p, name) =>
    if g.any (fun t => t.p == p) then some name else none

/-- Decode a shapes graph (F* `parse_shape_from_graph_pure`): every
shape-establishing, non-deactivated subject becomes a `Shape`. -/
def decodeShapesGraph (g : Graph) : ShapesGraph :=
  { shapes := ((distinctSubjects g).filter (isShapeEstablishing g)).map (decodeShape g),
    unsupported := sparqlFeaturesUsed g }

end L4Factoidal.SHACL
