/-
L4Factoidal.CSVW.Emit — turning converted cells into RDF triples,
the output half of `formal/fstar/CSVW.Conversion.fst`.

Spec: https://www.w3.org/TR/csv2rdf/ §5 (minimal mode) and §6
(standard mode).

MINIMAL mode emits only the cell triples. STANDARD mode adds the
row/table/table-group description scaffolding (`csvw:row`,
`csvw:rownum`, `csvw:url`, `csvw:describes`, `csvw:table`). Both are
here because the W3C manifest tests each mode separately, and a port
that only did one would score half the suite while looking complete.

An IRI produced by template expansion is CHECKED before it becomes a
term: `isIri` gates it, and a reference that fails simply produces no
triple, matching the F* module's behaviour of dropping a cell whose
predicate does not resolve rather than emitting a malformed term.
-/
import L4Factoidal.CSVW.Conversion
import L4Factoidal.RDF.Core

namespace L4Factoidal.CSVW

open L4Factoidal.RDF

/-- Build a checked IRI from an expanded template, or nothing. -/
def toIri? (s : String) : Option WfIri :=
  if h : isIri s then some ⟨s, h⟩ else none

/-- A typed literal from a datatype only known at runtime.

    `literalWf` forbids `rdf:langString` / `rdf:dirLangString` on an
    UNTAGGED literal, and a datatype coming out of metadata could be
    either. Rather than assume it is not, this checks and falls back
    to a plain string literal — the alternative would be an
    unprovable obligation or, worse, a `sorry`. -/
def typedLiteral (dt : WfIri) (lex : String) : WfLiteral :=
  if h : (dt != rdfLangString && dt != rdfDirLangString) = true then
    ⟨{ lexicalForm := lex, datatype := dt, langTag := none, direction := none },
     by simpa [literalWf] using h⟩
  else Literal.string lex

/-- CSVW vocabulary terms used by standard mode. -/
def csvwIri? (local' : String) : Option WfIri := toIri? (csvwNs ++ local')

/-! ### The standard-mode vocabulary, as CHECKED constants

These are written as `WfIri` literals with `rfl` proofs rather than
routed through `csvwIri?`, because the scaffolding must not be
silently droppable. `csvwIri?` returns an `Option`, and a `none`
there would make a table lose its `csvw:Table` node with no error —
exactly the failure mode that produced a third of each expected graph
before this landing. A constant that cannot fail to typecheck cannot
fail at runtime either. -/

def rdfTypeIri     : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#type", rfl⟩
def csvwTableGroup : WfIri := ⟨"http://www.w3.org/ns/csvw#TableGroup", rfl⟩
def csvwTableCls   : WfIri := ⟨"http://www.w3.org/ns/csvw#Table", rfl⟩
def csvwRowCls     : WfIri := ⟨"http://www.w3.org/ns/csvw#Row", rfl⟩
def csvwTableProp  : WfIri := ⟨"http://www.w3.org/ns/csvw#table", rfl⟩
def csvwRowProp    : WfIri := ⟨"http://www.w3.org/ns/csvw#row", rfl⟩
def csvwUrlProp    : WfIri := ⟨"http://www.w3.org/ns/csvw#url", rfl⟩
def csvwRownumProp : WfIri := ⟨"http://www.w3.org/ns/csvw#rownum", rfl⟩
def csvwDescribes  : WfIri := ⟨"http://www.w3.org/ns/csvw#describes", rfl⟩

/-- A row's subject: the aboutUrl if it resolves, else a blank node
    keyed by the row number so every cell of a row shares it. -/
def rowSubject (aboutRef : Option String) (rowNum : Nat) : Subject :=
  match aboutRef.bind toIri? with
  | some i => .iri i
  | none   => .bnode ("row" ++ toString rowNum)

/-- The IRI a CSVW datatype NAME denotes (tabular-metadata §5.11.1).
    Most names are XSD local names, but not all: `number`, `binary`,
    `datetime` and `any` are CSVW ALIASES, and `xml`, `html` and
    `json` are not XSD types at all.

    Treating every name as `xsd:<name>` mints datatypes that do not
    exist — `xsd:number` appeared on twelve triples of the csv2rdf
    corpus before this table, where the value space is `xsd:double`
    (measured 2026-08-22). -/
def datatypeIriFor (base : String) : Option String :=
  let xsd := fun (n : String) => some ("http://www.w3.org/2001/XMLSchema#" ++ n)
  if base == "number" then xsd "double"
  else if base == "binary" then xsd "base64Binary"
  else if base == "datetime" then xsd "dateTime"
  else if base == "any" then xsd "anyAtomicType"
  else if base == "xml" then some "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral"
  else if base == "html" then some "http://www.w3.org/1999/02/22-rdf-syntax-ns#HTML"
  else if base == "json" then some "http://www.w3.org/ns/csvw#JSON"
  else xsd base

/-- The object terms a cell contributes: value IRIs when `valueUrl`
    applied, else literals carrying the column's datatype and
    language. A language tag wins over a datatype, per RDF 1.1 (a
    language-tagged literal is always `rdf:langString`). -/
def cellObjects (inh : Inherited) (r : CellResult) : List Term :=
  let fromUrls := r.valueRefs.filterMap (fun u => (toIri? u).map Term.iri)
  let fromLits := r.literals.map (fun lex =>
    match inh.lang with
    | some tag => Term.literal (Literal.langString lex tag)
    | none =>
        match ((inh.datatype.bind Datatype.baseName).bind datatypeIriFor).bind toIri? with
        | some dt => Term.literal (typedLiteral dt lex)
        | none    => Term.literal (Literal.string lex))
  fromUrls ++ fromLits

/-- Triples for one cell. Nothing is emitted when the predicate does
    not resolve to a valid IRI — the F* module's rule, kept because a
    malformed predicate is a metadata error, not a licence to invent
    a term. -/
def cellTriples (inh : Inherited) (subj : Subject) (r : CellResult) : List Triple :=
  match r.propertyRef.bind toIri? with
  | none   => []
  | some p => (cellObjects inh r).map (fun o => ⟨subj, p, o⟩)

/-- Minimal mode, one row: the cell triples only. `cells` pairs each
    column's effective inherited properties with its converted
    result. -/
def rowTriplesMinimal (rowNum : Nat) (cells : List (Inherited × CellResult))
    : List Triple :=
  let subj := rowSubject (cells.findSome? (fun (_, r) => r.aboutRef)) rowNum
  cells.flatMap (fun (inh, r) => cellTriples inh subj r)

/-- The blank node that carries one row's description. Named, and
    exported, because the enclosing table must link the SAME node
    with `csvw:row` — a table that mints its own label would produce
    a graph with orphan row nodes that no isomorphism check can
    repair.

    `tag` scopes the label to one table. A metadata document may
    describe several tables, and keying row nodes by row NUMBER alone
    would silently merge row 1 of every table into one blank node. -/
def rowNode (tag : String) (rowNum : Nat) : Subject :=
  .bnode ("rownode" ++ tag ++ "_" ++ toString rowNum)

/-- Standard mode, one row: the cell triples plus the row description
    — `rdf:type csvw:Row`, `csvw:describes` linking the row node to
    the cell subject, `csvw:rownum` and `csvw:url`. -/
def rowTriplesStandard (tag tableUrl : String) (rowNum sourceRow : Nat)
    (cells : List (Inherited × CellResult)) : List Triple :=
  let subj := rowSubject (cells.findSome? (fun (_, r) => r.aboutRef)) rowNum
  let node := rowNode tag rowNum
  let core := cells.flatMap (fun (inh, r) => cellTriples inh subj r)
  let rowUrl := tableUrl ++ "#row=" ++ toString sourceRow
  let urlTriples := match toIri? rowUrl with
    | some u => [(⟨node, csvwUrlProp, .iri u⟩ : Triple)]
    | none   => []
  [ ⟨node, rdfTypeIri, .iri csvwRowCls⟩,
    ⟨node, csvwDescribes, subj.toTerm⟩,
    ⟨node, csvwRownumProp, .literal (typedLiteral xsdInteger (toString rowNum))⟩ ]
  ++ urlTriples ++ core

/-- One row's converted cells, with both row numbers it needs: the
    1-based position within the table (`rowNum`, which `csvw:rownum`
    reports and which keys the blank nodes) and the line number in
    the source file (`sourceRow`, which the `#row=` fragment
    reports). They differ whenever the file has a header.

    `subject` overrides the subject derived from the cells' `aboutUrl`
    when the caller has already computed it (the metadata path
    expands one row-level `aboutUrl` template rather than reading it
    back off each cell). -/
structure RowInput where
  rowNum    : Nat
  sourceRow : Nat
  cells     : List (Inherited × CellResult)
  subject   : Option Subject := none

/-- The subject a row's cells hang from. -/
def RowInput.subj (r : RowInput) : Subject :=
  match r.subject with
  | some s => s
  | none   => rowSubject (r.cells.findSome? (fun (_, c) => c.aboutRef)) r.rowNum

/-- Minimal mode, one row, honouring an explicit subject. -/
def rowTriplesMinimalOf (r : RowInput) : List Triple :=
  let subj := r.subj
  r.cells.flatMap (fun (inh, c) => cellTriples inh subj c)

/-- Standard mode, one row, honouring an explicit subject. -/
def rowTriplesStandardOf (tag tableUrl : String) (r : RowInput) : List Triple :=
  let subj := r.subj
  let node := rowNode tag r.rowNum
  let rowUrl := tableUrl ++ "#row=" ++ toString r.sourceRow
  let urlTriples := match toIri? rowUrl with
    | some u => [(⟨node, csvwUrlProp, .iri u⟩ : Triple)]
    | none   => []
  [ ⟨node, rdfTypeIri, .iri csvwRowCls⟩,
    ⟨node, csvwDescribes, subj.toTerm⟩,
    ⟨node, csvwRownumProp, .literal (typedLiteral xsdInteger (toString r.rowNum))⟩ ]
  ++ urlTriples ++ rowTriplesMinimalOf r

/-- Standard mode, one table: a `csvw:Table` node carrying
    `csvw:url` and one `csvw:row` link per row, above the row
    descriptions. csv2rdf §6. `extra` carries whatever the caller
    attaches to the table node itself (its common properties). -/
def tableTriplesStandard (tag tableNodeId tableUrl : String)
    (rows : List RowInput) (extra : Subject → List Triple := fun _ => []) : List Triple :=
  let node : Subject := .bnode tableNodeId
  let urlTriples := match toIri? tableUrl with
    | some u => [(⟨node, csvwUrlProp, .iri u⟩ : Triple)]
    | none   => []
  let rowLinks := rows.map (fun r =>
    (⟨node, csvwRowProp, (rowNode tag r.rowNum).toTerm⟩ : Triple))
  let rowTs := rows.flatMap (rowTriplesStandardOf tag tableUrl)
  (⟨node, rdfTypeIri, .iri csvwTableCls⟩ : Triple)
    :: (extra node ++ urlTriples ++ rowLinks ++ rowTs)

/-- Standard mode, whole output for ONE table. csv2rdf emits the
    `csvw:TableGroup` even for a single table — the no-metadata tests
    in the W3C suite all expect it, and omitting it is why this path
    scored zero before the group and table nodes existed. -/
def tableGroupTriplesStandard (tableUrl : String) (rows : List RowInput)
    : List Triple :=
  let group : Subject := .bnode "tablegroup"
  let tableNodeId := "table"
  [ ⟨group, rdfTypeIri, .iri csvwTableGroup⟩,
    ⟨group, csvwTableProp, (Subject.bnode tableNodeId).toTerm⟩ ]
  ++ tableTriplesStandard "" tableNodeId tableUrl rows

end L4Factoidal.CSVW
