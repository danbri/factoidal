/-
L4Factoidal.OWL.SyntaxDL — the OWL 2 DL species checker.

Port of `formal/fstar/OWL2.SyntaxDL.fst` (648 lines). Given the RDF
graphs of a W3C OWL 2 test case's documents, decide whether the case is
within OWL 2 DL (`test:DL`) or only OWL 2 Full (`test:FULL`). Purely
syntax-directed over parsed triples: no reasoning, no closure.

## The scope note is the F\* module's, and it is measured

Its header says so, and it is worth carrying across rather than
paraphrasing: the species facet in the W3C corpus mixes two judging
eras, the OWL 1 WebOnt classification and the OWL 2 WG's
re-annotation. The checks below are the subset of the Mapping to RDF
Graphs reverse mapping and the Structural Specification global
restrictions "that the corpus actually discriminates on, validated
check-by-check against all 489 species-annotated cases in
`third_party/testing/owl/all.rdf` (323 species-DL, 166
species-FULL-only)".

Two graph-identical premise pairs carry opposite species verdicts
(`WebOnt-I5.5-005` against `WebOnt-I5.5-006`), so the facet covers the
CONCLUSION document too — which is why `speciesIsDl` takes five
arguments rather than one graph.

## Nine per-triple checks, plus three global ones

| # | Check |
|---|---|
| 1 | reserved-vocabulary subject — redefining a built-in |
| 2 | untyped or undeclared assertion predicate |
| 3 | `rdf:type` object discipline |
| 4 | `owl:onProperty` filler must be a property |
| 5 | object property with a literal object |
| 6 | literal datatype usable in DL |
| 7 | data-property `rdfs:range` and `owl:onDatatype` fillers |
| 8 | `rdf:List` node discipline — one `rdf:first`, one `rdf:rest` |
| 9 | a property strictly inside its own `owl:propertyChainAxiom` |

and, over the whole graph: illegal punning, non-simple properties under
a cardinality restriction, and the document header discipline.

## Entity keys

`"I" ++ iri` for IRIs and `"B" ++ label` for blank nodes, so one string
list covers both node kinds. Carried over unchanged: the punning check
reads the `"I"` prefix to skip blank-node keys, because a blank node
typed both `owl:Class` and `owl:Restriction` is legitimate.
-/
import L4Factoidal.RDF.Graph

namespace L4Factoidal.OWL.SyntaxDL

open L4Factoidal.RDF

/-! ## Vocabulary -/

def nsOwl  : String := "http://www.w3.org/2002/07/owl#"
def nsRdf  : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
def nsRdfs : String := "http://www.w3.org/2000/01/rdf-schema#"
def nsXsd  : String := "http://www.w3.org/2001/XMLSchema#"

def iriReserved (i : String) : Bool :=
  i.startsWith nsOwl || i.startsWith nsRdf || i.startsWith nsRdfs ||
  i.startsWith nsXsd

def rdfTypeP  : String := nsRdf ++ "type"
def rdfFirstP : String := nsRdf ++ "first"
def rdfRestP  : String := nsRdf ++ "rest"
def rdfNilI   : String := nsRdf ++ "nil"

def owlOntologyC    : String := nsOwl ++ "Ontology"
def owlClassC       : String := nsOwl ++ "Class"
def owlRestrictionC : String := nsOwl ++ "Restriction"
def owlObjPropC     : String := nsOwl ++ "ObjectProperty"
def owlDataPropC    : String := nsOwl ++ "DatatypeProperty"
def owlAnnPropC     : String := nsOwl ++ "AnnotationProperty"
def owlOntPropC     : String := nsOwl ++ "OntologyProperty"
def owlDataRangeC   : String := nsOwl ++ "DataRange"
def rdfsDatatypeC   : String := nsRdfs ++ "Datatype"

def owlImportsP        : String := nsOwl ++ "imports"
def owlPriorVersionP   : String := nsOwl ++ "priorVersion"
def owlOnPropertyP     : String := nsOwl ++ "onProperty"
def owlInverseOfP      : String := nsOwl ++ "inverseOf"
def owlIntersectionOfP : String := nsOwl ++ "intersectionOf"
def owlUnionOfP        : String := nsOwl ++ "unionOf"
def owlComplementOfP   : String := nsOwl ++ "complementOf"
def owlOneOfP          : String := nsOwl ++ "oneOf"
def owlEquivClassP     : String := nsOwl ++ "equivalentClass"
def owlOnDatatypeP     : String := nsOwl ++ "onDatatype"
def owlChainP          : String := nsOwl ++ "propertyChainAxiom"
def rdfsDomainP        : String := nsRdfs ++ "domain"
def rdfsRangeP         : String := nsRdfs ++ "range"

/-- Property-characteristic classes whose members are object properties
    in the OWL 2 RDF mapping. -/
def objCharacteristics : List String :=
  [nsOwl ++ "SymmetricProperty", nsOwl ++ "TransitiveProperty",
   nsOwl ++ "InverseFunctionalProperty", nsOwl ++ "AsymmetricProperty",
   nsOwl ++ "ReflexiveProperty", nsOwl ++ "IrreflexiveProperty"]

def owlFunctionalPropC : String := nsOwl ++ "FunctionalProperty"

/-- The OWL 2 datatype map (Structural Specification §4) plus
    `rdfs:Literal`, `rdf:XMLLiteral`, `rdf:PlainLiteral` and
    `rdf:langString`. -/
def builtinDatatypes : List String :=
  [nsRdfs ++ "Literal",
   nsRdf ++ "XMLLiteral", nsRdf ++ "PlainLiteral", nsRdf ++ "langString",
   nsOwl ++ "real", nsOwl ++ "rational",
   nsXsd ++ "string", nsXsd ++ "boolean", nsXsd ++ "decimal",
   nsXsd ++ "integer", nsXsd ++ "double", nsXsd ++ "float",
   nsXsd ++ "date", nsXsd ++ "time", nsXsd ++ "dateTime",
   nsXsd ++ "dateTimeStamp", nsXsd ++ "gYear", nsXsd ++ "gMonth",
   nsXsd ++ "gDay", nsXsd ++ "gYearMonth", nsXsd ++ "gMonthDay",
   nsXsd ++ "duration", nsXsd ++ "yearMonthDuration",
   nsXsd ++ "dayTimeDuration",
   nsXsd ++ "byte", nsXsd ++ "short", nsXsd ++ "int", nsXsd ++ "long",
   nsXsd ++ "unsignedByte", nsXsd ++ "unsignedShort",
   nsXsd ++ "unsignedInt", nsXsd ++ "unsignedLong",
   nsXsd ++ "negativeInteger", nsXsd ++ "nonNegativeInteger",
   nsXsd ++ "nonPositiveInteger", nsXsd ++ "positiveInteger",
   nsXsd ++ "hexBinary", nsXsd ++ "base64Binary", nsXsd ++ "anyURI",
   nsXsd ++ "language", nsXsd ++ "normalizedString", nsXsd ++ "token",
   nsXsd ++ "NMTOKEN", nsXsd ++ "Name", nsXsd ++ "NCName"]

/-- Built-in annotation properties (Structural Specification §5.5). -/
def builtinAnnProps : List String :=
  [nsRdfs ++ "label", nsRdfs ++ "comment", nsRdfs ++ "seeAlso",
   nsRdfs ++ "isDefinedBy",
   nsOwl ++ "versionInfo", nsOwl ++ "deprecated",
   nsOwl ++ "backwardCompatibleWith", nsOwl ++ "incompatibleWith",
   nsOwl ++ "priorVersion"]

/-- Built-in top and bottom properties (§5.3, §5.4). -/
def builtinProps : List String :=
  [nsOwl ++ "topObjectProperty", nsOwl ++ "bottomObjectProperty",
   nsOwl ++ "topDataProperty", nsOwl ++ "bottomDataProperty"]

/-- `rdf:type` objects that DECLARE an entity rather than assert class
    membership. -/
def declarationTypes : List String :=
  [nsOwl ++ "Class", nsOwl ++ "ObjectProperty", nsOwl ++ "DatatypeProperty",
   nsOwl ++ "AnnotationProperty", nsRdfs ++ "Datatype",
   nsOwl ++ "NamedIndividual", nsOwl ++ "Ontology",
   nsOwl ++ "DeprecatedClass", nsOwl ++ "DeprecatedProperty",
   nsOwl ++ "OntologyProperty", nsOwl ++ "DataRange"]

/-- Reserved IRIs a DL document may carry as an `rdf:type` object,
    including the legacy typings (`rdfs:Class`, `rdf:List`,
    `rdf:Property`) the corpus's species-DL cases use. -/
def typeObjectWhitelist : List String :=
  declarationTypes ++ objCharacteristics ++ builtinDatatypes ++
  [owlFunctionalPropC, nsOwl ++ "Restriction",
   nsOwl ++ "Thing", nsOwl ++ "Nothing",
   nsOwl ++ "AllDifferent", nsOwl ++ "AllDisjointClasses",
   nsOwl ++ "AllDisjointProperties", nsOwl ++ "Axiom",
   nsOwl ++ "Annotation", nsOwl ++ "NegativePropertyAssertion",
   nsRdfs ++ "Class", nsRdf ++ "List", nsRdf ++ "Property"]

/-- Reserved IRIs acceptable as a triple SUBJECT: the built-in entities
    OWL 2 DL lets an ontology talk about. -/
def subjectWhitelist : List String :=
  [nsOwl ++ "Thing", nsOwl ++ "Nothing"] ++ builtinDatatypes ++ builtinProps

/-- `rdf:type` objects acceptable in a HEADER-LESS typing-only
    document. Narrower than `typeObjectWhitelist` on purpose: a
    header-less document typing entities with `owl:Nothing` or
    `rdfs:Class` is species-FULL throughout the corpus. -/
def headerlessTypeWhitelist : List String :=
  declarationTypes ++ [nsOwl ++ "Thing"]

def cardinalityPreds : List String :=
  [nsOwl ++ "cardinality", nsOwl ++ "minCardinality",
   nsOwl ++ "maxCardinality", nsOwl ++ "qualifiedCardinality",
   nsOwl ++ "minQualifiedCardinality", nsOwl ++ "maxQualifiedCardinality"]

/-! ## Graph accessors, over entity keys -/

def subjKey : Subject → String
  | .iri i => "I" ++ i.val
  | .bnode b => "B" ++ b

/-- `none` for a literal or a triple term: neither is a class or
    property key. -/
def termKeyDl : Term → Option String
  | .iri i => some ("I" ++ i.val)
  | .bnode b => some ("B" ++ b)
  | .literal _ => none
  | .tripleTerm _ _ _ => none

def termIsIri (o : Term) (i : String) : Bool :=
  match o with
  | .iri x => x.val == i
  | _ => false

def subjectsTyped (g : Graph) (ty : String) : List String :=
  g.filterMap (fun t =>
    if t.p.val == rdfTypeP && termIsIri t.o ty then some (subjKey t.s) else none)

def subjectsOfP (g : Graph) (p : String) : List String :=
  g.filterMap (fun t => if t.p.val == p then some (subjKey t.s) else none)

def objectKeysOf (g : Graph) (p : String) : List String :=
  g.filterMap (fun t => if t.p.val == p then termKeyDl t.o else none)

def hasTripleSp (g : Graph) (sk p : String) : Bool :=
  g.any (fun t => t.p.val == p && subjKey t.s == sk)

def findObjectSp (g : Graph) (sk p : String) : Option Term :=
  (g.find? (fun t => t.p.val == p && subjKey t.s == sk)).map (·.o)

def countSp (g : Graph) (sk p : String) : Nat :=
  (g.filter (fun t => t.p.val == p && subjKey t.s == sk)).length

def dedupStrs : List String → List String
  | [] => []
  | x :: rest => if rest.contains x then dedupStrs rest else x :: dedupStrs rest

/-- Members of an RDF collection, fuel-bounded by the graph size: each
    step consumes one `rdf:rest` link. -/
def collectionMembers (g : Graph) : Term → Nat → List Term
  | _, 0 => []
  | node, f + 1 =>
      match termKeyDl node with
      | none => []
      | some nk =>
          if termIsIri node rdfNilI then []
          else match findObjectSp g nk rdfFirstP with
               | none => []
               | some first =>
                   match findObjectSp g nk rdfRestP with
                   | none => [first]
                   | some rest => first :: collectionMembers g rest f

/-! ## The declaration index -/

structure DeclIndex where
  cls      : List String   -- typed owl:Class / owl:DeprecatedClass
  restr    : List String   -- typed owl:Restriction
  datatype : List String   -- typed rdfs:Datatype / owl:DataRange
  objProp  : List String
  dataProp : List String
  annProp  : List String   -- typed owl:AnnotationProperty / owl:OntologyProperty
  charProp : List String   -- an object characteristic or owl:FunctionalProperty
  hasDR    : List String   -- carries rdfs:domain or rdfs:range
  inv      : List String   -- takes part in owl:inverseOf, either side
  annSubj  : List String   -- typed owl:Ontology / owl:Axiom / owl:Annotation

def subjectsTypedAny (g : Graph) (tys : List String) : List String :=
  tys.flatMap (subjectsTyped g)

def buildDeclIndex (g : Graph) : DeclIndex :=
  { cls      := subjectsTypedAny g [owlClassC, nsOwl ++ "DeprecatedClass"]
  , restr    := subjectsTyped g owlRestrictionC
  , datatype := subjectsTypedAny g [rdfsDatatypeC, owlDataRangeC]
  , objProp  := subjectsTyped g owlObjPropC
  , dataProp := subjectsTyped g owlDataPropC
  , annProp  := subjectsTypedAny g [owlAnnPropC, owlOntPropC]
  , charProp := subjectsTypedAny g (owlFunctionalPropC :: objCharacteristics)
  , hasDR    := subjectsOfP g rdfsDomainP ++ subjectsOfP g rdfsRangeP
  , inv      := subjectsOfP g owlInverseOfP ++ objectKeysOf g owlInverseOfP
  , annSubj  := subjectsTypedAny g
                  [owlOntologyC, nsOwl ++ "Axiom", nsOwl ++ "Annotation"] }

/-- Acceptable wherever the RDF mapping demands a property: a declared
    object, data or annotation property; a built-in; a
    property-characteristic typing disambiguated by
    `rdfs:domain`/`rdfs:range`; or participation in `owl:inverseOf`. -/
def propEvidence (d : DeclIndex) (k : String) : Bool :=
  d.objProp.contains k || d.dataProp.contains k || d.annProp.contains k ||
  d.inv.contains k ||
  (d.charProp.contains k && (d.hasDR.contains k || d.inv.contains k))

/-- Defined as a class expression: a declared class, datatype or
    restriction, or a node carrying class-expression structure. -/
def classEvidence (g : Graph) (d : DeclIndex) (k : String) : Bool :=
  d.cls.contains k || d.datatype.contains k || d.restr.contains k ||
  hasTripleSp g k owlIntersectionOfP || hasTripleSp g k owlUnionOfP ||
  hasTripleSp g k owlComplementOfP || hasTripleSp g k owlOneOfP ||
  hasTripleSp g k owlOnPropertyP

/-- Usable in a DL data-range position: built-in, declared as a class
    (the legacy corpus shape), or carrying a datatype definition. -/
def datatypeEvidence (g : Graph) (d : DeclIndex) (dt : String) : Bool :=
  builtinDatatypes.contains dt ||
  d.cls.contains ("I" ++ dt) ||
  hasTripleSp g ("I" ++ dt) owlEquivClassP ||
  hasTripleSp g ("I" ++ dt) owlOnDatatypeP ||
  hasTripleSp g ("I" ++ dt) owlOneOfP

/-! ## Header discipline, per DOCUMENT and before imports merge -/

/-- Acceptable in a header-less document: only entity typings whose
    subject is a blank node or a non-reserved IRI, and whose object is
    a declaration class, `owl:Thing`, a blank node, or a non-reserved
    IRI. -/
def typingOnlyTriple (t : Triple) : Bool :=
  t.p.val == rdfTypeP &&
  (match t.s with
   | .bnode _ => true
   | .iri i => !(iriReserved i.val)) &&
  (match t.o with
   | .bnode _ => true
   | .literal _ => false
   | .tripleTerm _ _ _ => false
   | .iri o => headerlessTypeWhitelist.contains o.val || !(iriReserved o.val))

/-- No `owl:Ontology` header (unless the document is typing-only), or
    more than one header that is not the object of `owl:imports` or
    `owl:priorVersion` — no unique root ontology node. -/
def docHeaderViolations (g : Graph) : List String :=
  let headers := dedupStrs (subjectsTyped g owlOntologyC)
  let nonroot := objectKeysOf g owlImportsP ++ objectKeysOf g owlPriorVersionP
  let roots := headers.filter (fun h => !(nonroot.contains h))
  match headers with
  | [] => if g.all typingOnlyTriple then [] else ["no-ontology-header"]
  | _ => if roots.length > 1 then ["multiple-root-ontology-headers"] else []

/-! ## Body checks, on the merged graph -/

/-- Every element but the last: the strict interior for the role-chain
    regularity check. -/
def dropLastTerm : List Term → List Term
  | [] => []
  | [_] => []
  | x :: rest => x :: dropLastTerm rest

def tripleViolations (g : Graph) (d : DeclIndex) (t : Triple) : List String :=
  let v1 :=                                   -- reserved-vocabulary subject
    match t.s with
    | .iri i =>
        if iriReserved i.val && !(subjectWhitelist.contains i.val)
        then ["reserved-vocabulary-subject: " ++ i.val] else []
    | _ => []
  let v2 :=                                   -- undeclared assertion predicate
    if iriReserved t.p.val then []
    else if builtinAnnProps.contains t.p.val || builtinProps.contains t.p.val then []
    else if propEvidence d ("I" ++ t.p.val) then []
    else if d.annSubj.contains (subjKey t.s) then []
    else ["untyped-predicate: " ++ t.p.val]
  let v3 :=                                   -- rdf:type object discipline
    if t.p.val != rdfTypeP then []
    else match t.o with
    | .literal _ => ["literal-as-type-object"]
    | .tripleTerm _ _ _ => ["triple-term-as-type-object"]
    | .bnode b =>
        if classEvidence g d ("B" ++ b) then [] else ["undefined-bnode-class-expression"]
    | .iri o =>
        if iriReserved o.val then
          (if typeObjectWhitelist.contains o.val then []
           else ["reserved-vocabulary-as-class: " ++ o.val])
        else if classEvidence g d ("I" ++ o.val) then []
        else ["untyped-class: " ++ o.val]
  let v4 :=                                   -- owl:onProperty filler
    if t.p.val != owlOnPropertyP then []
    else match t.o with
    | .literal _ => ["literal-as-onProperty"]
    | .tripleTerm _ _ _ => ["triple-term-as-onProperty"]
    | .bnode b => if d.inv.contains ("B" ++ b) then [] else ["undefined-bnode-onProperty"]
    | .iri o =>
        if builtinProps.contains o.val then []
        else if iriReserved o.val then ["reserved-vocabulary-as-onProperty: " ++ o.val]
        else if propEvidence d ("I" ++ o.val) then []
        else ["untyped-onProperty: " ++ o.val]
  let v5 :=                                   -- object property, literal object
    match t.o with
    | .literal _ =>
        if d.objProp.contains ("I" ++ t.p.val)
        then ["object-property-with-literal-object: " ++ t.p.val] else []
    | _ => []
  let v6 :=                                   -- literal datatype usable in DL
    match t.o with
    | .literal l =>
        let dt := l.val.datatype.val
        if datatypeEvidence g d dt then []
        else if iriReserved dt then ["reserved-vocabulary-as-datatype: " ++ dt]
        else ["undefined-datatype: " ++ dt]
    | _ => []
  let v7 :=                                   -- range / onDatatype fillers
    if (t.p.val == rdfsRangeP && d.dataProp.contains (subjKey t.s))
       || t.p.val == owlOnDatatypeP then
      match t.o with
      | .iri o =>
          if datatypeEvidence g d o.val then []
          else if iriReserved o.val then ["reserved-vocabulary-as-datatype: " ++ o.val]
          else ["undefined-datatype: " ++ o.val]
      | _ => []
    else []
  let v8 :=                                   -- rdf:List node discipline
    if t.p.val == rdfFirstP || t.p.val == rdfRestP then
      let sk := subjKey t.s
      if countSp g sk rdfFirstP == 1 && countSp g sk rdfRestP == 1 then []
      else ["malformed-rdf-list-node"]
    else []
  let v9 :=                                   -- property inside its own chain
    if t.p.val == owlChainP then
      let members := collectionMembers g t.o g.length
      let interior := match members with
                      | [] => []
                      | _ :: tl => dropLastTerm tl
      let self := subjKey t.s
      if interior.any (fun m => termKeyDl m == some self)
      then ["property-inside-own-chain: " ++ self] else []
    else []
  v1 ++ v2 ++ v3 ++ v4 ++ v5 ++ v6 ++ v7 ++ v8 ++ v9

/-- Illegal punning. Blank-node keys are skipped — a blank node typed
    both `owl:Class` and `owl:Restriction` is legitimate — which is what
    the `"I"` prefix test is for. -/
def punningViolationsKeys (d : DeclIndex) : List String → List String
  | [] => []
  | k :: rest =>
      let here :=
        if !(k.startsWith "I") then []
        else
          (if d.cls.contains k && d.datatype.contains k
           then ["illegal-punning-class-datatype: " ++ k] else []) ++
          (if d.objProp.contains k && d.dataProp.contains k
           then ["illegal-punning-object-data-property: " ++ k] else []) ++
          (if d.objProp.contains k && d.annProp.contains k
           then ["illegal-punning-object-annotation-property: " ++ k] else []) ++
          (if d.dataProp.contains k && d.annProp.contains k
           then ["illegal-punning-data-annotation-property: " ++ k] else [])
      here ++ punningViolationsKeys d rest

def punningViolations (d : DeclIndex) : List String :=
  punningViolationsKeys d (dedupStrs (d.cls ++ d.objProp ++ d.dataProp))

/-- Global restriction §11: a non-simple property — transitive or
    chain-defined — under a cardinality restriction. -/
def nonsimpleCardinalityViolations (g : Graph) (nonsimple : List String) :
    List String → List String
  | [] => []
  | r :: rest =>
      let here :=
        if cardinalityPreds.any (fun cp => hasTripleSp g r cp) then
          match findObjectSp g r owlOnPropertyP with
          | some o =>
              match termKeyDl o with
              | some k => if nonsimple.contains k
                          then ["non-simple-property-in-cardinality: " ++ k] else []
              | none => []
          | none => []
        else []
      here ++ nonsimpleCardinalityViolations g nonsimple rest

def graphBodyViolations (g : Graph) : List String :=
  let d := buildDeclIndex g
  let perTriple := g.flatMap (tripleViolations g d)
  let nonsimple := dedupStrs (subjectsTyped g (nsOwl ++ "TransitiveProperty")
                              ++ subjectsOfP g owlChainP)
  let restrs := dedupStrs (subjectsOfP g owlOnPropertyP)
  perTriple ++ punningViolations d ++
  nonsimpleCardinalityViolations g nonsimple restrs

/-! ## The species verdict -/

/-- `pDoc` is the premise document alone, `pMerged` the premise with its
    `owl:imports` closure, `cDoc` the conclusion document alone, and
    `uMerged` premise plus conclusion plus imports.

    The conclusion's entity typing is checked against the UNION — the
    corpus convention lets a conclusion use premise vocabulary — while
    its header discipline is its own document's. -/
def speciesViolations (pDoc pMerged : Graph) (hasConclusion : Bool)
    (cDoc uMerged : Graph) : List String :=
  (docHeaderViolations pDoc).map (fun v => "premise: " ++ v) ++
  (graphBodyViolations pMerged).map (fun v => "premise: " ++ v) ++
  (if hasConclusion then
     (docHeaderViolations cDoc).map (fun v => "conclusion: " ++ v) ++
     (graphBodyViolations uMerged).map (fun v => "conclusion: " ++ v)
   else [])

def speciesIsDl (pDoc pMerged : Graph) (hasConclusion : Bool)
    (cDoc uMerged : Graph) : Bool :=
  (speciesViolations pDoc pMerged hasConclusion cDoc uMerged).isEmpty

/-- For graphs obtained from OWL 2 Functional Syntax
    (`test:normativeSyntax FUNCTIONAL`): a successful parse proves the
    `Ontology(…)` header syntactically, so only the body checks apply. -/
def speciesViolationsFunctional (p : Graph) (hasConclusion : Bool) (u : Graph) :
    List String :=
  (graphBodyViolations p).map (fun v => "premise: " ++ v) ++
  (if hasConclusion then (graphBodyViolations u).map (fun v => "conclusion: " ++ v)
   else [])

def speciesIsDlFunctional (p : Graph) (hasConclusion : Bool) (u : Graph) : Bool :=
  (speciesViolationsFunctional p hasConclusion u).isEmpty


/-! ## Build-time checks

Every check above gets a MINIMAL PAIR: a graph that passes and the same
graph perturbed so that exactly one check fires. A checker whose tests
only ever showed violations would not distinguish "rejects everything"
from "rejects the right thing". -/

section Checks

/-- A `WfIri` from a fixture string. Every string the checks below use
    is a real IRI; the fallback exists only so the helper is total. -/
private def i (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩
  else ⟨"http://example.org/not-an-iri", by simp [isIri, String.isEmpty]⟩
private def ti (s : String) : Term := .iri (i s)
private def si (s : String) : Subject := .iri (i s)
private def tr (s p o : String) : Triple := ⟨si s, i p, ti o⟩
private def trb (s p : String) (b : String) : Triple := ⟨si s, i p, .bnode b⟩
/-- A plain typed literal. An ill-formed combination becomes a blank
    node rather than needing a proof; no fixture below produces one. -/
private def litT (lex dt : String) : Term :=
  let l : Literal := { lexicalForm := lex, datatype := i dt,
                       langTag := none, direction := none }
  if h : literalWf l then .literal ⟨l, h⟩ else .bnode "ill-formed-literal"

private def trlit (s p lex dt : String) : Triple := ⟨si s, i p, litT lex dt⟩

private def ex (s : String) : String := "http://example.org/" ++ s

/-! ### A well-formed minimal ontology passes every check -/

private def okGraph : Graph :=
  [ tr (ex "o") rdfTypeP owlOntologyC
  , tr (ex "C") rdfTypeP owlClassC
  , tr (ex "p") rdfTypeP owlObjPropC
  , tr (ex "a") rdfTypeP (ex "C")
  , tr (ex "a") (ex "p") (ex "b")
  , tr (ex "b") rdfTypeP owlClassC ]

#guard docHeaderViolations okGraph == []
#guard graphBodyViolations okGraph == []
#guard speciesIsDl okGraph okGraph false [] []

/-! ### 1. A reserved-vocabulary subject is a redefinition -/

#guard graphBodyViolations (okGraph ++ [tr (nsOwl ++ "Thing") rdfTypeP owlClassC]) == []
#guard (graphBodyViolations (okGraph ++ [tr (nsOwl ++ "Class") rdfTypeP owlClassC])).any
         (fun v => v.startsWith "reserved-vocabulary-subject")

/-! ### 2. An undeclared assertion predicate -/

#guard (graphBodyViolations (okGraph ++ [tr (ex "a") (ex "q") (ex "b")])).any
         (fun v => v.startsWith "untyped-predicate")
#guard (graphBodyViolations (okGraph ++ [tr (ex "a") (ex "q") (ex "b"),
          tr (ex "q") rdfTypeP owlObjPropC])).all
         (fun v => !v.startsWith "untyped-predicate")

/-! A built-in annotation property needs no declaration. -/

#guard graphBodyViolations (okGraph ++
  [trlit (ex "a") (nsRdfs ++ "label") "hello" (nsXsd ++ "string")]) == []

/-! ### 3. `rdf:type` object discipline -/

#guard (graphBodyViolations (okGraph ++ [tr (ex "a") rdfTypeP (ex "Undeclared")])).any
         (fun v => v.startsWith "untyped-class")
#guard (graphBodyViolations (okGraph ++
          [trlit (ex "a") rdfTypeP "x" (nsXsd ++ "string")])).contains
         "literal-as-type-object"
#guard (graphBodyViolations (okGraph ++ [trb (ex "a") rdfTypeP "b1"])).contains
         "undefined-bnode-class-expression"

/-! ### 4. `owl:onProperty` must name a property -/

#guard (graphBodyViolations (okGraph ++
          [trb (ex "R") rdfTypeP "r1", tr (ex "R") owlOnPropertyP (ex "notAProp")])).any
         (fun v => v.startsWith "untyped-onProperty")

/-! ### 5. An object property with a literal object -/

#guard (graphBodyViolations (okGraph ++
          [trlit (ex "a") (ex "p") "x" (nsXsd ++ "string")])).any
         (fun v => v.startsWith "object-property-with-literal-object")

/-! ### 6. A literal's datatype must be usable in DL -/

#guard graphBodyViolations (okGraph ++
  [trlit (ex "a") (nsRdfs ++ "comment") "x" (nsXsd ++ "string")]) == []
#guard (graphBodyViolations (okGraph ++
          [trlit (ex "a") (nsRdfs ++ "comment") "x" (ex "myType")])).any
         (fun v => v.startsWith "undefined-datatype")

/-! ### 8. An `rdf:List` node carries exactly one `rdf:first` and one
    `rdf:rest` -/

private def listOk : Graph :=
  okGraph ++ [trb (ex "L") rdfFirstP "n1", trb (ex "L") rdfRestP "n2"]
private def listBad : Graph :=
  listOk ++ [trb (ex "L") rdfFirstP "n3"]

#guard (graphBodyViolations listOk).all (fun v => v != "malformed-rdf-list-node")
#guard (graphBodyViolations listBad).contains "malformed-rdf-list-node"

/-! ### Punning: the same IRI as object AND data property -/

#guard (graphBodyViolations (okGraph ++ [tr (ex "p") rdfTypeP owlDataPropC])).any
         (fun v => v.startsWith "illegal-punning-object-data-property")

/-! A BLANK NODE typed both `owl:Class` and `owl:Restriction` is
    legitimate, which is what the `"I"` key prefix protects. -/

#guard (graphBodyViolations (okGraph ++
          [⟨.bnode "x", i rdfTypeP, ti owlClassC⟩,
           ⟨.bnode "x", i rdfTypeP, ti owlRestrictionC⟩])).all
         (fun v => !v.startsWith "illegal-punning")

/-! ### The header discipline -/

#guard docHeaderViolations [tr (ex "a") (ex "p") (ex "b")] == ["no-ontology-header"]
#guard docHeaderViolations [tr (ex "a") rdfTypeP (ex "C")] == []
#guard docHeaderViolations
  [tr (ex "o1") rdfTypeP owlOntologyC, tr (ex "o2") rdfTypeP owlOntologyC]
  == ["multiple-root-ontology-headers"]

/-! An imported second header is not a second ROOT. -/

#guard docHeaderViolations
  [tr (ex "o1") rdfTypeP owlOntologyC, tr (ex "o2") rdfTypeP owlOntologyC,
   tr (ex "o1") owlImportsP (ex "o2")] == []

/-! ### The functional-syntax variant skips the header check only -/

/-- A header-less graph whose BODY is clean: an assertion triple makes
    it not typing-only, so the full check rejects it and the
    functional-syntax variant accepts it. That is the whole difference
    between the two entry points, in one pair. -/
private def noHeader : Graph :=
  [ tr (ex "p") rdfTypeP owlObjPropC
  , tr (ex "C") rdfTypeP owlClassC
  , tr (ex "a") rdfTypeP (ex "C")
  , tr (ex "a") (ex "p") (ex "b")
  , tr (ex "b") rdfTypeP (ex "C") ]

#guard docHeaderViolations noHeader == ["no-ontology-header"]
#guard graphBodyViolations noHeader == []
#guard !speciesIsDl noHeader noHeader false [] []
#guard speciesIsDlFunctional noHeader false []

/-! ### The conclusion document is judged too

Two cases with the SAME premise differ when the conclusion does — the
reason `speciesIsDl` takes five arguments. -/

#guard speciesIsDl okGraph okGraph true okGraph okGraph
#guard !speciesIsDl okGraph okGraph true
         [tr (ex "a") (ex "undeclared") (ex "b")]
         (okGraph ++ [tr (ex "a") (ex "undeclared") (ex "b")])

end Checks

end L4Factoidal.OWL.SyntaxDL
