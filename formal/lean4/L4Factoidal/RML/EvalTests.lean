/-
L4Factoidal.RML.EvalTests — build-time checks for the parts of RML
evaluation whose defaults are decided by POSITION rather than by the
map itself.
-/
import L4Factoidal.RML.Eval

namespace L4Factoidal.RML

open L4Factoidal.RDF
open L4Factoidal.JSON

/-! ## The JSONPath subset -/

#guard parseJsonPath "$.students[*]" == some [.field "students", .wildcard]
#guard parseJsonPath "$[*]" == some [JStep.wildcard]
#guard parseJsonPath "$.a.b" == some [.field "a", .field "b"]
#guard parseJsonPath "$['a b']" == some [JStep.field "a b"]
#guard parseJsonPath "$.a[2]" == some [.field "a", .index 2]
-- Outside the subset: NOT a guess. The corpus writes one malformed
-- path (`$.students[*]]`) and it is a negative case.
#guard parseJsonPath "$.students[*]]" == none
#guard parseJsonPath "students" == none

private def doc : Json :=
  .object [("students", .array [
    .object [("ID", .number "10"), ("Name", .string "Venus")],
    .object [("ID", .number "20"), ("Name", .string "Demi")]])]

#guard (evalPath "$.students[*]" doc).length == 2
#guard evalPath "$.students[*].Name" doc == [.string "Venus", .string "Demi"]
#guard evalPath "$.missing" doc == []

/-! ## A source value carries its own datatype

`10` is an `xsd:integer`, and the corpus states it: `RMLTC0002a-JSON`
expects `"10"^^xsd:integer`. Flattening a record to strings at the
door throws that away before the term is built. -/

#guard rvalOf (.number "10") == some { lexical := "10", natural := some (xsdNs ++ "integer") }
#guard rvalOf (.number "1.5") == some { lexical := "1.5", natural := some (xsdNs ++ "double") }
#guard rvalOf (.string "s") == some { lexical := "s" }
#guard rvalOf (.bool true) == some { lexical := "true", natural := some (xsdNs ++ "boolean") }
-- A container and `null` denote no value, and inventing one would put
-- something in the output that the source does not hold.
#guard rvalOf .null == none
#guard rvalOf (.array []) == none

/-! ## POSITION decides the default term type

`defaultTermType` reads the FORM only. A subject map written
`rml:subjectMap [ rml:reference "$.FirstName" ]` is a reference, so it
defaulted to a literal and produced no subject at all
(`RMLTC0019a`). A language map is the opposite case: a template there
defaults to `iri`, and a language tag is not an IRI
(`RMLTC0031c`). -/

#guard (asIri { form := .reference "$.x" }).termType == some .iri
#guard (asLiteral { form := .template "{$.a}-{$.b}" }).termType == some .literal
-- An EXPLICIT term type is never overridden by either.
#guard (asIri { form := .reference "$.x", termType := some .literal }).termType
       == some .literal

/-! ## Graph maps UNION, they do not override -/

private def gA : Term := .iri ⟨"http://ex/a", by rfl⟩
private def gB : Term := .iri ⟨"http://ex/b", by rfl⟩

#guard graphsFor [] [] == [none]
#guard graphsFor [gA] [] == [some gA]
#guard graphsFor [gA] [gB] == [some gA, some gB]
-- The same graph named at both levels is one graph, not two.
#guard graphsFor [gA] [gA] == [some gA]

end L4Factoidal.RML
