/-
L4Factoidal.OWL.QueryEvalRegimeTests — an end-to-end pin for the
entailment-regime query path.

The fixture is the W3C SPARQL 1.1 entailment test `parent7`
(`third_party/testing/w3c/sparql/sparql11/entailment/`): data
`parent.ttl` (trimmed to the individuals the answer turns on), query
"which individuals are in (≤ 1 hasChild.Female)?", expected answer
exactly `:Dudley`.

Why this pin exists: on 2026-08-24 this query returned 0 rows through
`evalSelectOwl` and NOTHING caught it — the harness skips
entailment-regime tests, and the rewrite's shape search expected a
canonical restriction node the Lean closure never materialised. The
repair is `QueryMaterialise.augmentForQuery`. This file is the test
that was missing.

The two wrong answers this guards against:
* 0 rows — the pre-repair behaviour (no canonical node to match);
* extra rows — the F\* route's failure mode (closure over-types
  individuals into the restriction; `Bob` has a `hasChild` successor of
  unknown class and must NOT appear).

Whole-pipeline evaluation (Turtle parse → RL closure → SPARQL parse →
rewrite → eval) runs at build time; the fixture is small on purpose.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.OWL.QueryEval
import L4Factoidal.OWL.RLClosure
import L4Factoidal.Syntax.Turtle
import L4Factoidal.SPARQL.Parser

namespace L4Factoidal.OWL.QueryEvalRegimeTests

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.SPARQL
open L4Factoidal.OWL

private def parent7Data : String :=
"@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix : <http://example.org/test#> .
:hasChild rdf:type owl:ObjectProperty .
:Female rdf:type owl:Class .
:Male rdf:type owl:Class .
:Alice rdf:type :Female , owl:NamedIndividual .
:Bob rdf:type :Male , owl:NamedIndividual ; :hasChild :Charlie .
:Charlie rdf:type owl:NamedIndividual .
:Dudley rdf:type owl:NamedIndividual ,
    [ rdf:type owl:Restriction ; owl:onProperty :hasChild ;
      owl:allValuesFrom [ rdf:type owl:Class ; owl:oneOf ( :Alice ) ] ] ;
    :hasChild :Alice .
"

private def parent7Query : String :=
"PREFIX owl: <http://www.w3.org/2002/07/owl#>
PREFIX : <http://example.org/test#>
PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>
SELECT * WHERE { ?parent a [ a owl:Restriction ;
   owl:onProperty :hasChild ;
   owl:maxQualifiedCardinality \"1\"^^xsd:nonNegativeInteger ;
   owl:onClass :Female ] . }"

private def parent7Rows : List (List (VarName × Term)) :=
  match parseTurtle parent7Data, parseSparql parent7Query with
  | .ok g, .ok q =>
      let ds : Dataset := { Dataset.empty with default := RL.closureFix g }
      QueryEval.evalSelectOwl emptyEnv ds q
  | _, _ => [[("parse-failed", Term.bnode "x")]]

private def dudley : Term :=
  Term.iri ⟨"http://example.org/test#Dudley", rfl⟩

/-! Exactly one row, and it binds `?parent` to `:Dudley`. One row is
what rules out both wrong answers at once. -/
#guard parent7Rows.length == 1
#guard parent7Rows == [[("parent", dudley)]]

end L4Factoidal.OWL.QueryEvalRegimeTests
