/-
L4Factoidal.SHACL.Report — the validation report as an RDF graph
(§3.6 of the SHACL Recommendation, https://www.w3.org/TR/shacl/).

Port of `formal/fstar/SHACL.Validation.fst` section 13
(`validation_report_to_graph`, `result_to_triples`, `path_to_rdf`).

One `sh:ValidationReport` blank node with `sh:conforms`, and one
`sh:ValidationResult` blank node per result (§3.6.2) carrying exactly
the predicates the W3C test suite's "full compliance" comparison keeps:
rdf:type, sh:focusNode, sh:resultPath (with its own freshly-minted
blank-node path structure — the suite requires that "blank node
structures representing property paths ... must not be shared among
multiple results"), sh:resultSeverity, sh:sourceConstraintComponent,
sh:sourceShape, sh:value, sh:resultMessage. Every blank node comes from
one counter threaded through the serialisation.
-/
import L4Factoidal.SHACL.Validation

namespace L4Factoidal.SHACL

open L4Factoidal.RDF

/-- §4: the constraint component IRI of each Core component. -/
def constraintComponentIri : Constraint → WfIri
  | .cls _ => shClassCC
  | .datatype _ => shDatatypeCC
  | .nodeKind _ => shNodeKindCC
  | .minCount _ => shMinCountCC
  | .maxCount _ => shMaxCountCC
  | .minExclusive _ => shMinExclusiveCC
  | .minInclusive _ => shMinInclusiveCC
  | .maxExclusive _ => shMaxExclusiveCC
  | .maxInclusive _ => shMaxInclusiveCC
  | .minLength _ => shMinLengthCC
  | .maxLength _ => shMaxLengthCC
  | .pattern _ _ => shPatternCC
  | .languageIn _ => shLanguageInCC
  | .uniqueLang _ => shUniqueLangCC
  | .equals _ => shEqualsCC
  | .disjoint _ => shDisjointCC
  | .lessThan _ => shLessThanCC
  | .lessThanOrEquals _ => shLessThanOrEqualsCC
  | .notOf _ => shNotCC
  | .andOf _ => shAndCC
  | .orOf _ => shOrCC
  | .xoneOf _ => shXoneCC
  | .nodeOf _ => shNodeCC
  | .qualifiedMinCount _ _ _ => shQualifiedMinCountCC
  | .qualifiedMaxCount _ _ _ => shQualifiedMaxCountCC
  | .closed _ => shClosedCC
  | .hasValue _ => shHasValueCC
  | .inSet _ => shInCC

def severityToIri : Severity → WfIri
  | .info => shInfo
  | .warning => shWarning
  | .violation => shViolation
  | .custom i => i

/-- A fresh blank-node label from the counter. -/
def freshBnode (pre : String) (ctr : Nat) : BNodeId × Nat :=
  (pre ++ toString ctr, ctr + 1)

mutual
  /-- §2.3.1 in reverse: the RDF term for a path and the triples that
  describe it, minting fresh blank nodes for every composite node. -/
  def pathToRdf : Path → Nat → Term × List Triple × Nat
    | .pred i, ctr => (.iri i, [], ctr)
    | .inverse p, ctr =>
      let (inner, its, ctr1) := pathToRdf p ctr
      let (bid, ctr2) := freshBnode "_shacl_rpi" ctr1
      (.bnode bid, { s := .bnode bid, p := shInversePath, o := inner } :: its, ctr2)
    | .seq ps, ctr => pathListToRdf ps ctr
    | .alt ps, ctr =>
      let (listTerm, listTs, ctr1) := pathListToRdf ps ctr
      let (bid, ctr2) := freshBnode "_shacl_rpa" ctr1
      (.bnode bid, { s := .bnode bid, p := shAlternativePath, o := listTerm } :: listTs, ctr2)
    | .zeroOrMore p, ctr =>
      let (inner, its, ctr1) := pathToRdf p ctr
      let (bid, ctr2) := freshBnode "_shacl_rpzm" ctr1
      (.bnode bid, { s := .bnode bid, p := shZeroOrMorePath, o := inner } :: its, ctr2)
    | .oneOrMore p, ctr =>
      let (inner, its, ctr1) := pathToRdf p ctr
      let (bid, ctr2) := freshBnode "_shacl_rpom" ctr1
      (.bnode bid, { s := .bnode bid, p := shOneOrMorePath, o := inner } :: its, ctr2)
    | .zeroOrOne p, ctr =>
      let (inner, its, ctr1) := pathToRdf p ctr
      let (bid, ctr2) := freshBnode "_shacl_rpzo" ctr1
      (.bnode bid, { s := .bnode bid, p := shZeroOrOnePath, o := inner } :: its, ctr2)

  def pathListToRdf : List Path → Nat → Term × List Triple × Nat
    | [], ctr => (.iri rdfNil, [], ctr)
    | p :: rest, ctr =>
      let (pTerm, pTs, ctr1) := pathToRdf p ctr
      let (restTerm, restTs, ctr2) := pathListToRdf rest ctr1
      let (bid, ctr3) := freshBnode "_shacl_rpl" ctr2
      (.bnode bid,
       { s := .bnode bid, p := rdfFirst, o := pTerm } ::
       { s := .bnode bid, p := rdfRest, o := restTerm } :: (pTs ++ restTs),
       ctr3)
end

/-- §3.6.2: one validation result's triples, linked from the report. -/
def resultToTriples (report : Subject) (v : Violation) (ctr : Nat) : List Triple × Nat :=
  let (bid, ctr1) := freshBnode "_shacl_result" ctr
  let rsubj : Subject := .bnode bid
  let base : List Triple :=
    [ { s := rsubj, p := rdfType, o := .iri shValidationResult },
      { s := report, p := shResult, o := .bnode bid },
      { s := rsubj, p := shFocusNode, o := v.focus },
      { s := rsubj, p := shResultSeverity, o := .iri (severityToIri v.severity) },
      { s := rsubj, p := shSourceConstraintComponent, o := .iri (constraintComponentIri v.constraint) },
      { s := rsubj, p := shSourceShape, o := shapeRefToTerm v.sourceShape } ]
  let (pathTs, ctr2) : List Triple × Nat :=
    match v.path with
    | none => ([], ctr1)
    | some p =>
      let (pterm, pts, ctr2') := pathToRdf p ctr1
      (({ s := rsubj, p := shResultPath, o := pterm } : Triple) :: pts, ctr2')
  let valueTs : List Triple :=
    match v.value with
    | some vv => [{ s := rsubj, p := shValue, o := vv }]
    | none => []
  let msgTs : List Triple :=
    match v.message with
    | some m => [{ s := rsubj, p := shResultMessage, o := .literal m }]
    | none => []
  (base ++ pathTs ++ valueTs ++ msgTs, ctr2)

def resultsToTriples (report : Subject) : List Violation → Nat → List Triple × Nat
  | [], ctr => ([], ctr)
  | v :: rest, ctr =>
    let (ts, ctr1) := resultToTriples report v ctr
    let (restTs, ctr2) := resultsToTriples report rest ctr1
    (ts ++ restTs, ctr2)

/-- `"true"^^xsd:boolean` / `"false"^^xsd:boolean`. -/
def boolLiteral (b : Bool) : WfLiteral :=
  ⟨{ lexicalForm := if b then "true" else "false", datatype := xsdBoolean,
     langTag := none, direction := none }, rfl⟩

/-- §3.6.1: the report graph — one `sh:ValidationReport` blank node
with `sh:conforms`, one `sh:result` per validation result. -/
def reportToGraph (r : ValidationReport) : Graph :=
  let report : Subject := .bnode "_shacl_report0"
  let header : List Triple :=
    [ { s := report, p := rdfType, o := .iri shValidationReport },
      { s := report, p := shConforms, o := .literal (boolLiteral r.conforms) } ]
  header ++ (resultsToTriples report r.results 0).1

end L4Factoidal.SHACL
