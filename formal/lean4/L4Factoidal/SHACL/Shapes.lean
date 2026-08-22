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
`build_constraints`, `build_shape`, `parse_shape_from_graph_pure`),
plus the SHACL-SPARQL decoders of section 11b (`prefix_header_for`,
`build_sparql_constraints`, `build_custom_constraints`) — Part 2 §5.1
sh:sparql constraints (`Constraint.sparql`) and §6 constraint
components (`Constraint.custom`), whose SPARQL text is kept as a
string here and parsed at validation time (`Sparql.lean`), as the F*
does. The F* constructors for SHACL 1.2 (list-valued sh:datatype,
sh:singleLine, sh:memberShape, …), SHACL-AF (sh:values, sh:targetWhere)
and the SPARQL-based target (T_Sparql) are not ported — see
`Vocabulary.lean`'s header. A shapes graph that uses the SPARQL-based
target predicate is recorded in `ShapesGraph.unsupported` so the
harness can name it.

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

mutual
  /-- Structural equality on paths (written out because `Path` nests a
  `List`; used by the build-time guards). -/
  def Path.beq : Path → Path → Bool
    | .pred a, .pred b => a == b
    | .inverse a, .inverse b => Path.beq a b
    | .seq as, .seq bs => Path.beqList as bs
    | .alt as, .alt bs => Path.beqList as bs
    | .zeroOrMore a, .zeroOrMore b => Path.beq a b
    | .oneOrMore a, .oneOrMore b => Path.beq a b
    | .zeroOrOne a, .zeroOrOne b => Path.beq a b
    | _, _ => false
  def Path.beqList : List Path → List Path → Bool
    | [], [] => true
    | a :: as, b :: bs => Path.beq a b && Path.beqList as bs
    | _, _ => false
end

instance : BEq Path := ⟨Path.beq⟩

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
  -- SHACL-SPARQL Part 2 §5.1: a sh:sparql constraint. `node` is the
  -- constraint node (reported as sh:sourceConstraint, distinct from the
  -- owning shape's sh:sourceShape); `query` is the sh:select text with
  -- its §5.2 `PREFIX` header already prepended (`$this`, `$PATH`, … are
  -- substituted at validation time); `message` / `severity` are the
  -- constraint node's own sh:message / sh:severity, which take priority
  -- over the owning shape's (node/sparql-001, node/sparql-003).
  | sparql (node : ShapeRef) (query : String) (message : Option WfLiteral)
           (severity : Option Severity)
  -- SHACL-SPARQL Part 2 §6: a use of a SPARQL-based constraint
  -- component. `component` is the component IRI (reported as
  -- sh:sourceConstraintComponent); `isAsk` says whether the chosen
  -- validator (§6.2, node/property validator before the generic one)
  -- is a SPARQLAskValidator (run per value node) or a
  -- SPARQLSelectValidator (run per focus node); `query` is its
  -- sh:ask / sh:select text with the `PREFIX` header prepended;
  -- `params` are the §6.1 parameter bindings read off the shape (SPARQL
  -- variable = local name of the parameter's sh:path); `msgTemplate` is
  -- the validator's sh:message with `{?x}` / `{$x}` placeholders (§6.3).
  | custom (component : WfIri) (isAsk : Bool) (query : String)
           (params : List (String × Term)) (msgTemplate : Option String)
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

/-! ## SHACL-SPARQL §5.2 prefix declarations

`sh:prefixes` names one or more nodes carrying `sh:declare` prefix
declarations (each with `sh:prefix` and `sh:namespace`); the vendored
suite links declaration nodes with `owl:imports` (node/prefixes-001),
so the walk follows it transitively, cycle-safe. The result is the
`PREFIX p: <ns>` header the SPARQL parser needs in the query text (the
parser has no ambient prefix map, unlike Turtle's `@prefix`). Port of
`declares_to_header` / `collect_declares` / `prefix_header_for`. -/

/-- One `PREFIX` line per declaration node that has both parts. -/
def declaresToHeader (g : Graph) (decls : List Term) : String :=
  decls.foldl (fun acc d =>
    let pfx := match objectsOfTerm g d shDeclPrefix with
      | .literal l :: _ => some l.val.lexicalForm | _ => none
    let ns := match objectsOfTerm g d shDeclNamespace with
      | .literal l :: _ => some l.val.lexicalForm | _ => none
    match pfx, ns with
    | some p, some n => acc ++ "PREFIX " ++ p ++ ": <" ++ n ++ ">\n"
    | _, _ => acc) ""

/-- Every sh:declare node reachable from `frontier` through owl:imports
(fuel-bounded, `visited` keeps cycles finite). -/
def collectDeclares (g : Graph) : List Term → List Term → Nat → List Term
  | _, _, 0 => []
  | [], _, _ + 1 => []
  | n :: rest, visited, fuel + 1 =>
    if visited.contains n then collectDeclares g rest visited fuel
    else
      objectsOfTerm g n shDeclare ++
      collectDeclares g (objectsOfTerm g n owlImports ++ rest) (n :: visited) fuel

/-- The `PREFIX` header for the query text of constraint / validator
node `s`: its sh:prefixes nodes' declarations; with no sh:prefixes, the
declarations of every `sh:ShapesGraph` node (the SHACL 1.2 default the
F* applies). -/
def prefixHeaderFor (g : Graph) (s : Subject) : String :=
  let viaNodes := objectsOf g s shPrefixes
  let nodes := if viaNodes.isEmpty then subjectsOf g rdfType (.iri shShapesGraph) else viaNodes
  declaresToHeader g (collectDeclares g nodes [] (g.length + 10))

/-! ## SHACL-SPARQL §5.1 sh:sparql constraints -/

/-- Every sh:sparql value of `s` that carries a sh:select (F*
`build_sparql_constraints`). The constraint node's own sh:message and
sh:severity are read here; the query text gets its prefix header. -/
def decodeSparqlConstraints (g : Graph) (s : Subject) : List Constraint :=
  (objectsOf g s shSparql).filterMap fun t =>
    match t.toSubject? with
    | none => none
    | some cs =>
      match objectsOf g cs shSelect with
      | .literal l :: _ =>
        let msg := match objectsOf g cs shMessage with
          | .literal ml :: _ => some ml | _ => none
        let sev := match objectsOf g cs shSeverity with
          | .iri i :: _ => some (severityOfIri i) | _ => none
        some (Constraint.sparql (subjectToShapeRef cs)
          (prefixHeaderFor g cs ++ l.val.lexicalForm) msg sev)
      | _ => none

/-! ## SHACL-SPARQL §6 SPARQL-based constraint components

A constraint component is recognised STRUCTURALLY — a subject with at
least one sh:parameter and one of sh:validator / sh:nodeValidator /
sh:propertyValidator — not through rdf:type / rdfs:subClassOf
sh:ConstraintComponent (component/validator-001 routes the typing
through user-defined subclasses that no Core-level reading follows;
the structural signature is unambiguous). A shape USES a component
(§6.1) when every non-optional parameter has a value on the shape node
and at least one parameter is bound at all (component/optional-001:
`ex:IncompleteShape` has only the optional parameter and must not
trigger the component). Port of `is_custom_component_def`,
`parse_custom_param`, `custom_params_applicable`, `choose_validator`,
`build_custom_constraints`. -/

/-- §6.1: the SPARQL variable of a parameter is the local name of its
sh:path IRI — the text after the last `#` or `/`. -/
def localNameOfIri (iri : String) : String :=
  String.ofList ((iri.toList.reverse.takeWhile (fun c => c != '#' && c != '/')).reverse)

structure CustomParam where
  path     : WfIri
  name     : String
  optional : Bool
  deriving Repr

def isCustomComponentDef (g : Graph) (subj : Subject) : Bool :=
  !(objectsOf g subj shParameter).isEmpty &&
  (!(objectsOf g subj shValidator).isEmpty ||
   !(objectsOf g subj shNodeValidator).isEmpty ||
   !(objectsOf g subj shPropertyValidator).isEmpty)

def decodeCustomParam (g : Graph) (t : Term) : Option CustomParam :=
  match t.toSubject? with
  | none => none
  | some ps =>
    match objectsOf g ps shPath with
    | .iri p :: _ =>
      some { path := p, name := localNameOfIri p.val,
             optional := (firstBool (objectsOf g ps shOptional)).getD false }
    | _ => none

/-- The (variable, value) bindings of the parameters on shape node `s`,
with the "some parameter is bound" flag; `none` when a non-optional
parameter is missing. -/
def customParamsApplicable (g : Graph) (s : Subject) :
    List CustomParam → Bool → Option (List (String × Term) × Bool)
  | [], anyBound => some ([], anyBound)
  | p :: rest, anyBound =>
    match objectsOf g s p.path with
    | v :: _ =>
      (customParamsApplicable g s rest true).map fun (acc, ab) => ((p.name, v) :: acc, ab)
    | [] => if p.optional then customParamsApplicable g s rest anyBound else none

def componentParams (g : Graph) (s : Subject) (params : List CustomParam) :
    Option (List (String × Term)) :=
  match customParamsApplicable g s params false with
  | some (binds, true) => some binds
  | _ => none

/-- A validator node's kind (sh:ask → ASK validator, else sh:select →
SELECT validator), its prefix-headered query text, and its sh:message
template. -/
def validatorQueryOf (g : Graph) (v : Term) : Option (Bool × String × Option String) :=
  match v.toSubject? with
  | none => none
  | some vs =>
    let tmpl := match objectsOf g vs shMessage with
      | .literal l :: _ => some l.val.lexicalForm | _ => none
    match objectsOf g vs shAsk with
    | .literal l :: _ => some (true, prefixHeaderFor g vs ++ l.val.lexicalForm, tmpl)
    | _ =>
      match objectsOf g vs shSelect with
      | .literal l :: _ => some (false, prefixHeaderFor g vs ++ l.val.lexicalForm, tmpl)
      | _ => none

/-- §6.2: sh:nodeValidator (node shapes) / sh:propertyValidator
(property shapes) before the generic sh:validator. -/
def chooseValidator (g : Graph) (comp : Subject) (isProperty : Bool) :
    Option (Bool × String × Option String) :=
  let generic := match objectsOf g comp shValidator with
    | v :: _ => validatorQueryOf g v | [] => none
  let specific := if isProperty then objectsOf g comp shPropertyValidator
                  else objectsOf g comp shNodeValidator
  match specific with
  | v :: _ => match validatorQueryOf g v with | some r => some r | none => generic
  | [] => generic

/-- Every IRI-named component definition in the shapes graph that
shape node `s` uses, as a `Constraint.custom`. -/
def decodeCustomConstraints (g : Graph) (s : Subject) (isProperty : Bool) : List Constraint :=
  ((distinctSubjects g).filter (isCustomComponentDef g)).filterMap fun comp =>
    match comp with
    | .bnode _ => none
    | .iri ci =>
      let params := (objectsOf g comp shParameter).filterMap (decodeCustomParam g)
      if params.isEmpty then none
      else
        match componentParams g s params with
        | none => none
        | some binds =>
          (chooseValidator g comp isProperty).map fun (isAsk, q, tmpl) =>
            Constraint.custom ci isAsk q binds tmpl

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
    constraints := decodeConstraints g s ++ decodeSparqlConstraints g s ++
                   decodeCustomConstraints g s (!pathObjs.isEmpty),
    propertyRefs := (objectsOf g s shProperty).filterMap termToShapeRef }

/-- The unsupported SHACL-SPARQL feature names a graph uses (predicates
only; today only the SPARQL-based target). -/
def sparqlFeaturesUsed (g : Graph) : List String :=
  sparqlFeaturePredicates.filterMap fun (p, name) =>
    if g.any (fun t => t.p == p) then some name else none

/-- Decode a shapes graph (F* `parse_shape_from_graph_pure`): every
shape-establishing, non-deactivated subject becomes a `Shape`. -/
def decodeShapesGraph (g : Graph) : ShapesGraph :=
  { shapes := ((distinctSubjects g).filter (isShapeEstablishing g)).map (decodeShape g),
    unsupported := sparqlFeaturesUsed g }

end L4Factoidal.SHACL
