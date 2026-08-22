/-
L4Factoidal.CSVW.PipelineTests — build-time checks for the metadata
parse, the common-property emitter and the metadata-driven pipeline.

Every `#guard` here is a claim the csv2rdf corpus made concrete: each
one names a mistake that produced a graph with the RIGHT number of
triples and the wrong content, which is the failure mode a count
check cannot see.
-/
import L4Factoidal.CSVW.Pipeline

namespace L4Factoidal.CSVW

open L4Factoidal.JSON
open L4Factoidal.RDF

/-! ## Prefix expansion (§5.8) -/

#guard expandPrefixed "dc:title" == "http://purl.org/dc/terms/title"
#guard expandPrefixed "schema:name" == "http://schema.org/name"
-- An ABSOLUTE IRI passes through: its scheme reads as a prefix, and
-- rewriting it would produce a term the document never stated.
#guard expandPrefixed "http://example.org/p" == "http://example.org/p"
-- An unrecognised prefix is left ALONE rather than given a guessed
-- namespace; the emitter then declines to build an IRI from it.
#guard expandPrefixed "zz:thing" == "zz:thing"

/-! ## `@context` -/

private def ctxDoc : String :=
  "{\"@context\": [\"http://www.w3.org/ns/csvw\", {\"@language\": \"en\"}], \"url\": \"t.csv\"}"

#guard match parseMetadataText ctxDoc with
       | some (_, c) => c.lang == some "en"
       | none => false

-- A single-table document is lifted into a one-table group, so
-- downstream code sees ONE shape.
#guard match parseMetadataText ctxDoc with
       | some (g, _) => g.tables.length == 1 && g.tables.head!.url == "t.csv"
       | none => false

/-! ## Titles, in all four shapes (§5.6) -/

private def titlesJson (body : String) : List (String × Option String) :=
  match parseJson? body with
  | some j => titlesOf (some "en") j
  | none   => []

#guard titlesJson "\"A\"" == [("A", some "en")]
#guard titlesJson "[\"A\", \"B\"]" == [("A", some "en"), ("B", some "en")]
#guard titlesJson "{\"fr\": \"A\"}" == [("A", some "fr")]
#guard titlesJson "{\"fr\": [\"A\", \"B\"]}" == [("A", some "fr"), ("B", some "fr")]

/-! ## Datatype names (§5.11.1)

`number`, `binary`, `datetime` and `any` are CSVW ALIASES, and `xml` /
`html` / `json` are not XSD types at all. Reading every name as
`xsd:<name>` minted `xsd:number` on real corpus output. -/

#guard datatypeIriFor "number" == some "http://www.w3.org/2001/XMLSchema#double"
#guard datatypeIriFor "string" == some "http://www.w3.org/2001/XMLSchema#string"
#guard datatypeIriFor "datetime" == some "http://www.w3.org/2001/XMLSchema#dateTime"
#guard datatypeIriFor "xml"
       == some "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral"
#guard datatypeIriFor "json" == some "http://www.w3.org/ns/csvw#JSON"

/-! ## Column-scoped template variables

`{_name}` in a `propertyUrl` is what gives each column its own
predicate. Without it every column of a table collapses onto one. -/

private def look0 : String → Option String := rowLookup [("c", "v")] 1 2

#guard UriTemplate.expand (cellLookup look0 "name" 3 3) "http://schema.org/{_name}"
       == "http://schema.org/name"
#guard UriTemplate.expand (cellLookup look0 "name" 3 3) "http://ex/{_column}"
       == "http://ex/3"
-- The row-scoped variables still show through the column-scoped
-- layer.
#guard UriTemplate.expand (cellLookup look0 "name" 3 3) "http://ex/{_row}"
       == "http://ex/1"

/-! ## Common properties (§5.8) -/

private def cpTriples (body : String) : List Triple :=
  match parseJson? body with
  | some j => commonTriples "http://ex/base" none 8 "p" (.bnode "s") "http://ex/prop" j
  | none   => []

#guard (cpTriples "\"hello\"").length == 1
#guard match cpTriples "\"hello\"" with
       | [⟨_, _, .literal l⟩] => l.val.lexicalForm == "hello"
       | _ => false
-- An `@id` value is an IRI object, not a literal that happens to look
-- like one.
#guard match cpTriples "{\"@id\": \"http://example.org/x\"}" with
       | [⟨_, _, .iri i⟩] => i.val == "http://example.org/x"
       | _ => false
-- `@value` with `@type` is a typed literal.
#guard match cpTriples "{\"@value\": \"2010-12-31\", \"@type\": \"xsd:date\"}" with
       | [⟨_, _, .literal l⟩] =>
           l.val.datatype.val == "http://www.w3.org/2001/XMLSchema#date"
       | _ => false
-- An ARRAY is one triple per element, sharing subject and predicate.
#guard (cpTriples "[\"a\", \"b\", \"c\"]").length == 3
-- A nested node becomes a blank node, and its own members hang off
-- THAT node rather than off the outer subject.
#guard (cpTriples "{\"schema:name\": \"X\"}").length == 2
#guard match cpTriples "{\"schema:name\": \"X\"}" with
       | ⟨_, _, .bnode b⟩ :: ⟨.bnode b2, p, _⟩ :: [] =>
           b == b2 && p.val == "http://schema.org/name"
       | _ => false
-- A value shape this module does not model emits NOTHING rather than
-- a guessed triple.
#guard (cpTriples "null").isEmpty

end L4Factoidal.CSVW
