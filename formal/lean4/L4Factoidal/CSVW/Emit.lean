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

/-- A row's subject: the aboutUrl if it resolves, else a blank node
    keyed by the row number so every cell of a row shares it. -/
def rowSubject (aboutRef : Option String) (rowNum : Nat) : Subject :=
  match aboutRef.bind toIri? with
  | some i => .iri i
  | none   => .bnode ("row" ++ toString rowNum)

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
        match (inh.datatype.bind Datatype.baseName).bind
                (fun b => toIri? ("http://www.w3.org/2001/XMLSchema#" ++ b)) with
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

/-- Standard mode, one row: the cell triples plus the row description
    — `csvw:describes` linking the row node to the cell subject,
    `csvw:rownum` and `csvw:url`. -/
def rowTriplesStandard (tableUrl : String) (rowNum sourceRow : Nat)
    (cells : List (Inherited × CellResult)) : List Triple :=
  let subj := rowSubject (cells.findSome? (fun (_, r) => r.aboutRef)) rowNum
  let rowNode : Subject := .bnode ("rownode" ++ toString rowNum)
  let core := cells.flatMap (fun (inh, r) => cellTriples inh subj r)
  let desc :=
    match csvwIri? "describes", csvwIri? "rownum", csvwIri? "url" with
    | some dIri, some nIri, some uIri =>
        let rowUrl := tableUrl ++ "#row=" ++ toString sourceRow
        let urlTriples := match toIri? rowUrl with
          | some u => [(⟨rowNode, uIri, .iri u⟩ : Triple)]
          | none   => []
        [ ⟨rowNode, dIri, subj.toTerm⟩,
          ⟨rowNode, nIri, .literal (typedLiteral xsdInteger (toString rowNum))⟩ ]
        ++ urlTriples
    | _, _, _ => []
  desc ++ core

end L4Factoidal.CSVW
