/-
L4Factoidal.SPARQL.ResultsRdf — decode the DAWG RDF result-set
vocabulary into the common SPARQL query-results model.

Vocabulary: http://www.w3.org/2001/sw/DataAccess/tests/result-set# .
The W3C SPARQL 1.0 test suite uses this RDF graph form for SELECT and
ASK expected results. A `rs:ResultSet` has either `rs:boolean`, or a
sequence of `rs:solution` nodes. Each solution contains `rs:binding`
nodes with one `rs:variable` literal and one RDF-term `rs:value`.
`rs:index` records solution order for ORDER BY tests.

The decoder is strict at the result-set boundary. It rejects malformed
boolean values, non-literal variable names and indexes, incomplete
bindings, and graphs that combine the boolean and solution forms. It
keeps RDF terms unchanged, including blank-node identity, literal
datatype IRIs, and language tags.

No parser lives here. Turtle and RDF/XML produce the same `RDF.Graph`;
their callers then use this reusable graph decoder.
-/
import L4Factoidal.SPARQL.Results

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-- Namespace of the DAWG RDF result-set vocabulary. -/
def rdfResultSetNs : String :=
  "http://www.w3.org/2001/sw/DataAccess/tests/result-set#"

private def rdfTypeIri : String :=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

private def resultSubjectOfTerm : Term → Option Subject
  | .iri i   => some (.iri i)
  | .bnode b => some (.bnode b)
  | _        => none

private structure RdfResultGraphIndex where
  resultSetsRev : List Subject := []
  objectsRev : Std.HashMap (Subject × String) (List Term) := ∅
  seen : Std.HashSet Triple := ∅

/-- Index the result vocabulary in one graph pass. `seen` enforces the RDF
graph's set semantics when a caller supplies a list with repeated triples.
Objects are accumulated in reverse order so the fold remains tail recursive. -/
private def indexRdfResultGraph (g : Graph) : RdfResultGraphIndex :=
  g.foldl (fun index triple =>
    if index.seen.contains triple then index
    else
      let resultSetsRev :=
        if triple.p.val == rdfTypeIri then
          match triple.o with
          | .iri i =>
              if i.val == rdfResultSetNs ++ "ResultSet" then
                triple.s :: index.resultSetsRev
              else index.resultSetsRev
          | _ => index.resultSetsRev
        else index.resultSetsRev
      let key := (triple.s, triple.p.val)
      let objectsRev :=
        if triple.p.val.startsWith rdfResultSetNs then
          index.objectsRev.insert key (triple.o :: index.objectsRev.getD key [])
        else index.objectsRev
      { resultSetsRev, objectsRev, seen := index.seen.insert triple }) {}

private def resultObjects (index : RdfResultGraphIndex) (s : Subject)
    (p : String) : List Term :=
  (index.objectsRev.getD (s, p) []).reverse

private def resultSetSubjects (index : RdfResultGraphIndex) : List Subject :=
  index.resultSetsRev.reverse

/-- True when the graph contains a subject typed `rs:ResultSet`. -/
def isRdfResultSet (g : Graph) : Bool :=
  !(indexRdfResultGraph g).resultSetsRev.isEmpty

private def oneResultObject (context : String) : List Term → Except ResultsError Term
  | [x] => .ok x
  | []  => .error ⟨s!"RDF result set: missing {context}"⟩
  | _   => .error ⟨s!"RDF result set: multiple {context} values"⟩

private def oneOptionalResultObject (context : String) : List Term →
    Except ResultsError (Option Term)
  | []  => .ok none
  | [x] => .ok (some x)
  | _   => .error ⟨s!"RDF result set: multiple {context} values"⟩

private def resultLiteralText (context : String) : Term → Except ResultsError String
  | .literal l => .ok l.val.lexicalForm
  | _ => .error ⟨s!"RDF result set: {context} is not a literal"⟩

private def resultSubject (context : String) (t : Term) : Except ResultsError Subject :=
  match resultSubjectOfTerm t with
  | some s => .ok s
  | none   => .error ⟨s!"RDF result set: {context} is not an IRI or blank node"⟩

/-- Decode one `rs:boolean` value. Its range is `xsd:boolean`, whose
lexical space contains `true`, `false`, `1`, and `0`. -/
def decodeRdfResultBoolean : Term → Except ResultsError Bool
  | .literal l =>
      if l.val.datatype != xsdBoolean then
        .error ⟨"RDF result set: rs:boolean is not an xsd:boolean literal"⟩
      else if l.val.lexicalForm == "true" || l.val.lexicalForm == "1" then .ok true
      else if l.val.lexicalForm == "false" || l.val.lexicalForm == "0" then .ok false
      else .error ⟨s!"RDF result set: invalid xsd:boolean lexical form '{l.val.lexicalForm}'"⟩
  | _ => .error ⟨"RDF result set: rs:boolean is not a literal"⟩

private def decodeRdfResultBinding (index : RdfResultGraphIndex) (bindingTerm : Term) :
    Except ResultsError (VarName × Term) := do
  let binding ← resultSubject "rs:binding object" bindingTerm
  let variableTerm ← oneResultObject "rs:variable"
    (resultObjects index binding (rdfResultSetNs ++ "variable"))
  let variableName ← resultLiteralText "rs:variable" variableTerm
  let value ← oneResultObject "rs:value"
    (resultObjects index binding (rdfResultSetNs ++ "value"))
  return (variableName, value)

private def decodeRdfResultIndex (index : RdfResultGraphIndex) (solution : Subject) :
    Except ResultsError (Option Nat) := do
  let indexTerm ← oneOptionalResultObject "rs:index"
    (resultObjects index solution (rdfResultSetNs ++ "index"))
  match indexTerm with
  | none => return none
  | some term =>
      let lexical ← resultLiteralText "rs:index" term
      match lexical.toNat? with
      | some index => return some index
      | none => throw ⟨s!"RDF result set: rs:index '{lexical}' is not a natural number"⟩

private def decodeRdfResultSolution (index : RdfResultGraphIndex) (solutionTerm : Term) :
    Except ResultsError (Option Nat × Binding) := do
  let solution ← resultSubject "rs:solution object" solutionTerm
  let position ← decodeRdfResultIndex index solution
  let bindings ← (resultObjects index solution (rdfResultSetNs ++ "binding")).mapM
    (decodeRdfResultBinding index)
  return (position, bindings)

private def sortRdfResultsByIndex (rows : List (Nat × Binding)) :
    List (Nat × Binding) :=
  rows.mergeSort (fun left right => left.1 ≤ right.1)

private def decodeRdfResultVariables (terms : List Term) :
    Except ResultsError (List VarName) :=
  terms.mapM (resultLiteralText "rs:resultVariable")

/-- Decode one graph in the DAWG RDF result-set vocabulary.

The result is ASK-shaped when the result-set subject has exactly one
`rs:boolean`. Otherwise it is SELECT-shaped. SELECT rows are sorted by
`rs:index` when every solution supplies an index; without a complete
index they keep the graph's order. -/
def decodeRdfResultSet (g : Graph) : Except ResultsError QueryResult := do
  let index := indexRdfResultGraph g
  let resultSet ← match resultSetSubjects index with
    | [s] => .ok s
    | []  => .error ⟨"RDF result set: no rs:ResultSet subject"⟩
    | _   => .error ⟨"RDF result set: multiple rs:ResultSet subjects"⟩
  let booleans := resultObjects index resultSet (rdfResultSetNs ++ "boolean")
  let variables := resultObjects index resultSet (rdfResultSetNs ++ "resultVariable")
  let solutions := resultObjects index resultSet (rdfResultSetNs ++ "solution")
  match booleans with
  | [] =>
      let vars ← decodeRdfResultVariables variables
      let decoded ← solutions.mapM (decodeRdfResultSolution index)
      let indexed := decoded.filterMap (fun row => row.1.map (fun i => (i, row.2)))
      let rows :=
        if !decoded.isEmpty && indexed.length == decoded.length then
          (sortRdfResultsByIndex indexed).map Prod.snd
        else decoded.map Prod.snd
      return .bindings vars rows
  | [booleanTerm] =>
      if !variables.isEmpty || !solutions.isEmpty then
        throw ⟨"RDF result set: rs:boolean cannot be combined with SELECT result properties"⟩
      return .boolean (← decodeRdfResultBoolean booleanTerm)
  | _ => throw ⟨"RDF result set: multiple rs:boolean values"⟩

end L4Factoidal.SPARQL
