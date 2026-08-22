/-
L4Factoidal.JSONLD.Tests — compile-time executable checks.

Every `#guard` below is evaluated during `lake build`: a wrong answer is
a BUILD FAILURE (the same discipline as `L4Factoidal/Tests.lean`).

Cases are taken from the JSON-LD 1.1 specification's own examples
(https://www.w3.org/TR/json-ld11/ and
https://www.w3.org/TR/json-ld11-api/) — context processing, compact
IRIs, `@base`/`@vocab`, lists, value objects, language maps, type and
index maps, `@reverse`, `@json` literals, RFC 8785 number formatting,
and the term-definition error conditions.

These are UNIT checks on named algorithm steps. The conformance
measurement is the separate real-corpus run
(`lake exe l4jsonld-probe`, the W3C toRdf manifest) — a `#guard` file is
never a conformance claim (CLAUDE.md iron rule #6).
-/
import L4Factoidal.JSONLD.ToRdf

namespace L4Factoidal.JSONLD.Tests

open L4Factoidal.JSON
open L4Factoidal.JSONLD

/-! ### Helpers

All of these run with `Loader.none`: none of the cases below reference a
remote context, so an unresolvable reference would be a `loading remote
context failed` error and the guard would fail — never a silent
empty-context substitution. -/

/-- Process a `@context` value given as JSON text. -/
def ctx? (s : String) : Option ActiveContext :=
  match parseJson s with
  | .ok j    => (activeContextFromJson Loader.none j).toOption
  | .error _ => none

/-- The same, keeping only the error code. -/
def ctxErr (s : String) : Option String :=
  match parseJson s with
  | .ok j =>
    match activeContextFromJson Loader.none j with
    | .error e => some e.code
    | .ok _    => none
  | .error _ => some "not JSON"

/-- An active context, or the empty one if the text does not process. -/
def ctx! (s : String) : ActiveContext := (ctx? s).getD emptyActiveContext

/-- Expand a document and render it in RFC 8785 canonical form, so a
guard can be written as one readable string comparison. -/
def expandJcs (input : String) (base : Option String := none) : Option String :=
  (expandDocument Loader.none input base none none).toOption.map jcsDocument

/-- The error code expansion produces, if it fails. -/
def expandErr (input : String) (base : Option String := none) : Option String :=
  match expandDocument Loader.none input base none none with
  | .error e => some e.code
  | .ok _    => none

/-- Convert to RDF and render as RDFC-1.0 canonical N-Quads. -/
def toRdfNq (input : String) (base : Option String := none)
    (rdfDirection : Option String := none) : Option String :=
  (parseJsonLd Loader.none input base rdfDirection none none).toOption.map
    (fun ds => ds.canonicalNQuads)

/-- Number of quads produced. -/
def toRdfCount (input : String) (base : Option String := none) : Option Nat :=
  (parseJsonLd Loader.none input base none none none).toOption.map
    (fun ds => ds.default.length + (ds.named.map (fun g => g.graph.length)).foldl (· + ·) 0)

/-! ### §5.2.2 IRI Expansion — absolute IRIs, terms, compact IRIs -/

-- An absolute IRI expands to itself, in either mode.
#guard expandIri emptyActiveContext "http://example.org/x" false == some "http://example.org/x"
#guard expandIri emptyActiveContext "http://example.org/x" true == some "http://example.org/x"

-- A keyword expands to itself.
#guard expandIri emptyActiveContext "@type" true == some "@type"

-- A term maps to its IRI, vocab-relative only.
#guard expandIri (ctx! "{\"name\": \"http://schema.org/name\"}") "name" true
       == some "http://schema.org/name"
-- §5.2.2: terms are ignored in `@id` (document-relative) position.
#guard expandIri (ctx! "{\"name\": \"http://schema.org/name\", \"@base\": \"http://ex/\"}")
         "name" false == some "http://ex/name"

-- Compact IRI through a prefix term (JSON-LD 1.1 §4.1.5). The simple
-- string form gets the prefix flag because the IRI ends in a gen-delim.
#guard expandIri (ctx! "{\"foaf\": \"http://xmlns.com/foaf/0.1/\"}") "foaf:name" true
       == some "http://xmlns.com/foaf/0.1/name"
-- The object form does NOT, unless it asks (§4.2 step 24).
#guard expandIri (ctx! "{\"foaf\": {\"@id\": \"http://xmlns.com/foaf/0.1/\"}}") "foaf:name" true
       == some "foaf:name"
#guard expandIri (ctx! "{\"foaf\": {\"@id\": \"http://xmlns.com/foaf/0.1/\", \"@prefix\": true}}")
         "foaf:name" true == some "http://xmlns.com/foaf/0.1/name"

-- `_:` is a blank node identifier, never a compact-IRI prefix.
#guard expandIri emptyActiveContext "_:b0" true == some "_:b0"

-- A colon inside a fragment is not a scheme delimiter, so the value
-- stays relative and falls through to the base.
#guard expandIri (ctx! "{\"@base\": \"http://ex/doc\"}") "#Test:2" false
       == some "http://ex/doc#Test:2"

-- `@vocab` is a plain concatenation, `@base` a full RFC 3986 resolution.
#guard expandIri (ctx! "{\"@vocab\": \"http://ex/v#\"}") "term" true == some "http://ex/v#term"
#guard expandIri (ctx! "{\"@base\": \"http://ex/a/b/c\"}") "../d" false == some "http://ex/a/d"
-- RFC 3986 §5.4: the empty reference resolves to the base itself.
#guard expandIri (ctx! "{\"@base\": \"http://ex/a/b?q\"}") "" false == some "http://ex/a/b?q"

-- With neither mapping in scope, a bare term does not resolve.
#guard expandIri emptyActiveContext "term" true == none
#guard expandIri emptyActiveContext "term" false == none

/-! ### §4.1 / §4.2 Context Processing -/

-- A keyword alias is stored as a term whose IRI mapping IS the keyword.
#guard (findTerm (ctx! "{\"id\": \"@id\"}").terms "id").map TermDef.iri == some "@id"
#guard (findTerm (ctx! "{\"a\": \"@type\"}").terms "a").map TermDef.iri == some "@type"

-- `@base`, `@vocab`, `@language`, `@direction`.
#guard (ctx! "{\"@base\": \"http://ex/\"}").base == some "http://ex/"
#guard (ctx! "{\"@vocab\": \"http://ex/v#\"}").vocab == some "http://ex/v#"
#guard (ctx! "{\"@language\": \"en\"}").language == some "en"
#guard (ctx! "{\"@direction\": \"rtl\"}").direction == some "rtl"

-- An array of contexts folds left to right; a later entry wins.
#guard (ctx! "[{\"@vocab\": \"http://a/\"}, {\"@vocab\": \"http://b/\"}]").vocab
       == some "http://b/"

-- `"@context": null` resets terms and restores the ORIGINAL base
-- (§4.1: "setting both base IRI and original base URL to the value of
-- original base URL"), which is `none` for a bare context here.
#guard (ctx! "[{\"@vocab\": \"http://a/\", \"p\": \"http://a/p\"}, null]").vocab == none
#guard (ctx! "[{\"p\": \"http://a/p\"}, null]").terms.length == 0

-- Term definition members: `@type` coercion, `@container`, `@language`.
#guard (findTerm (ctx! "{\"d\": {\"@id\": \"http://ex/d\", \"@type\": \"@id\"}}").terms "d").map
         TermDef.typeMapping == some (some "@id")
#guard (findTerm (ctx! "{\"l\": {\"@id\": \"http://ex/l\", \"@container\": \"@list\"}}").terms "l").map
         TermDef.container == some ContainerKind.list
#guard (findTerm (ctx! "{\"g\": {\"@id\": \"http://ex/g\", \"@container\": [\"@graph\", \"@id\"]}}").terms "g").map
         TermDef.container == some ContainerKind.graphId
#guard (findTerm (ctx! "{\"t\": {\"@id\": \"http://ex/t\", \"@language\": null}}").terms "t").map
         TermDef.language == some (some none)

-- A forward reference to a simple-string prefix declared LATER in the
-- same context object still resolves (§4.2's `defined` map, narrowed to
-- the common case — see `previewPrefixes`).
#guard (findTerm (ctx! "{\"date\": {\"@id\": \"xsd:date\"}, \"xsd\": \"http://www.w3.org/2001/XMLSchema#\"}").terms
         "date").map TermDef.iri == some "http://www.w3.org/2001/XMLSchema#date"

/-! ### §4.2 error conditions — errors are VALUES, carrying the code -/

#guard ctxErr "[{\"@protected\": true, \"p\": \"http://a/p\"}, {\"p\": \"http://b/p\"}]"
       == some "protected term redefinition"
-- Redefining a protected term IDENTICALLY is allowed.
#guard ctxErr "[{\"@protected\": true, \"p\": \"http://a/p\"}, {\"p\": \"http://a/p\"}]" == none
-- A null context that would silently drop a protected term is itself an
-- error (§4.1).
#guard ctxErr "[{\"@protected\": true, \"p\": \"http://a/p\"}, null]"
       == some "invalid context nullification"
#guard ctxErr "{\"@type\": \"http://ex/t\"}" == some "keyword redefinition"
#guard ctxErr "{\"term\": {\"@id\": \"term:term\"}}" == some "cyclic IRI mapping"
#guard ctxErr "{\"t\": {\"@id\": \"http://ex/t\", \"@type\": \"_:not-an-iri\"}}"
       == some "invalid type mapping"
#guard ctxErr "{\"t\": {\"@id\": \"http://ex/t\", \"@nest\": \"@id\"}}" == some "invalid @nest value"
#guard ctxErr "{\"@version\": 1.0}" == some "invalid @version value"
#guard ctxErr "{\"t\": {\"@id\": \"@context\"}}" == some "invalid keyword alias"
#guard ctxErr "{\"\": {\"@id\": \"http://ex/e\"}}" == some "invalid term definition"
#guard ctxErr "{\"@base\": true}" == some "invalid base IRI"
#guard ctxErr "{\"@direction\": \"sideways\"}" == some "invalid base direction"
-- A reverse property may only carry a set- or index-container (§4.2).
#guard ctxErr "{\"r\": {\"@reverse\": \"http://ex/r\", \"@container\": \"@list\"}}"
       == some "invalid reverse property"

-- The banned fallback: an unresolvable remote context is an ERROR, not
-- an empty context (see `JSONLD/Loader.lean`).
#guard ctxErr "\"http://example.org/missing.jsonld\"" == some "loading remote context failed"

/-! ### §5.1 Expansion -/

-- A term key becomes an absolute IRI and its value is array-wrapped and
-- turned into a value object (JSON-LD 1.1 §3.1's running example shape).
#guard expandJcs "{\"@context\":{\"name\":\"http://schema.org/name\"},\"name\":\"Manu\"}"
       == some "[{\"http://schema.org/name\":[{\"@value\":\"Manu\"}]}]"

-- An unmapped key is DROPPED (§5.1: IRI expansion returns null).
#guard expandJcs "{\"nomap\":\"x\"}" == some "[]"

-- `@id` resolves document-relative against the base.
#guard expandJcs "{\"@id\":\"rel\",\"http://ex/p\":\"v\"}" (some "http://ex/base/doc")
       == some "[{\"@id\":\"http://ex/base/rel\",\"http://ex/p\":[{\"@value\":\"v\"}]}]"

-- The context default `@language` reaches a plain string value (§5.2).
#guard expandJcs "{\"@context\":{\"@language\":\"en\",\"p\":\"http://ex/p\"},\"p\":\"hi\"}"
       == some "[{\"http://ex/p\":[{\"@language\":\"en\",\"@value\":\"hi\"}]}]"

-- `"@type": "@id"` coercion turns a string into a node reference.
#guard expandJcs "{\"@context\":{\"p\":{\"@id\":\"http://ex/p\",\"@type\":\"@id\"}},\"p\":\"http://ex/o\"}"
       == some "[{\"http://ex/p\":[{\"@id\":\"http://ex/o\"}]}]"

-- A datatype coercion stamps `@type` on the value object.
#guard expandJcs "{\"@context\":{\"p\":{\"@id\":\"http://ex/p\",\"@type\":\"http://ex/dt\"}},\"p\":\"v\"}"
       == some "[{\"http://ex/p\":[{\"@type\":\"http://ex/dt\",\"@value\":\"v\"}]}]"

-- `"@container": "@list"` wraps the value array in a list object.
#guard expandJcs "{\"@context\":{\"p\":{\"@id\":\"http://ex/p\",\"@container\":\"@list\"}},\"p\":[\"a\",\"b\"]}"
       == some "[{\"http://ex/p\":[{\"@list\":[{\"@value\":\"a\"},{\"@value\":\"b\"}]}]}]"

-- An explicit `@set` is transparent — its contents splice in.
#guard expandJcs "{\"http://ex/p\":{\"@set\":[\"a\",\"b\"]}}"
       == some "[{\"http://ex/p\":[{\"@value\":\"a\"},{\"@value\":\"b\"}]}]"

-- A language map keys each entry by its tag; `@none` yields no tag.
#guard expandJcs "{\"@context\":{\"p\":{\"@id\":\"http://ex/p\",\"@container\":\"@language\"}},\"p\":{\"en\":\"hi\",\"de\":\"hallo\"}}"
       == some "[{\"http://ex/p\":[{\"@language\":\"de\",\"@value\":\"hallo\"},{\"@language\":\"en\",\"@value\":\"hi\"}]}]"

-- `@reverse` used forward folds into the `@reverse` bucket.
#guard expandJcs "{\"@context\":{\"r\":{\"@reverse\":\"http://ex/r\"}},\"@id\":\"http://ex/s\",\"r\":{\"@id\":\"http://ex/o\"}}"
       == some "[{\"@id\":\"http://ex/s\",\"@reverse\":{\"http://ex/r\":[{\"@id\":\"http://ex/o\"}]}}]"

-- `@nest` is transparent: its members expand as members of the
-- enclosing node object (§5.1 step 14).
#guard expandJcs "{\"@context\":{\"n\":\"@nest\"},\"http://ex/a\":\"1\",\"n\":{\"http://ex/b\":\"2\"}}"
       == some "[{\"http://ex/a\":[{\"@value\":\"1\"}],\"http://ex/b\":[{\"@value\":\"2\"}]}]"

-- A free-floating value object at the top level produces nothing.
#guard expandJcs "{\"@value\":\"free-floating\"}" == some "[]"

-- Expansion error conditions.
#guard expandErr "{\"@id\":\"http://ex/s\",\"@type\":true}" == some "invalid type value"
#guard expandErr "{\"http://ex/p\":{\"@value\":\"v\",\"@language\":\"en\",\"@type\":\"http://ex/t\"}}"
       == some "invalid value object"
#guard expandErr "{\"http://ex/p\":{\"@list\":[\"a\"],\"@id\":\"http://ex/x\"}}"
       == some "invalid set or list object"

/-! ### §8.2–§8.4 to RDF -/

-- One triple, both terms given as full IRIs (toRdf/0001's shape).
#guard toRdfNq "{\"@id\":\"http://ex/s\",\"http://ex/p\":\"v\"}"
       == some "<http://ex/s> <http://ex/p> \"v\" .\n"

-- `@type` becomes `rdf:type`.
#guard toRdfNq "{\"@id\":\"http://ex/s\",\"@type\":\"http://ex/C\"}"
       == some "<http://ex/s> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://ex/C> .\n"

-- A language-tagged literal.
#guard toRdfNq "{\"@id\":\"http://ex/s\",\"http://ex/p\":{\"@value\":\"hi\",\"@language\":\"en\"}}"
       == some "<http://ex/s> <http://ex/p> \"hi\"@en .\n"

-- §8.4: an empty `@list` is `rdf:nil`; an n-item list makes n cells,
-- so 2n triples.
#guard toRdfCount "{\"@id\":\"http://ex/s\",\"http://ex/p\":{\"@list\":[]}}" == some 1
#guard toRdfCount "{\"@id\":\"http://ex/s\",\"http://ex/p\":{\"@list\":[\"a\",\"b\"]}}" == some 5

-- A relative IRI with no base cannot become a subject, so no triple.
#guard toRdfCount "{\"@id\":\"rel\",\"http://ex/p\":\"v\"}" == some 0

-- Generalized RDF: a blank-node PREDICATE is dropped (see
-- `JSONLD/ToRdf.lean`'s header).
#guard toRdfCount "{\"@id\":\"http://ex/s\",\"_:p\":\"v\"}" == some 0

-- A top-level `@graph` wrapper feeds the DEFAULT graph; a named node
-- carrying `@graph` makes a named graph.
#guard toRdfCount "{\"@graph\":[{\"@id\":\"http://ex/s\",\"http://ex/p\":\"v\"}]}" == some 1
#guard toRdfNq "{\"@id\":\"http://ex/g\",\"@graph\":[{\"@id\":\"http://ex/s\",\"http://ex/p\":\"v\"}]}"
       == some "<http://ex/s> <http://ex/p> \"v\" <http://ex/g> .\n"

/-! ### §8.6 Data Round Tripping — the number decisions -/

-- A bare integer stays `xsd:integer`; a fractional value promotes to
-- `xsd:double` in the canonical scientific form.
#guard numberCanonicalize "5" false == ("5", false)
#guard numberCanonicalize "5.3" false == ("5.3E0", true)
-- `-0e0` LOOKS double-shaped but its VALUE is the integer zero.
#guard numberCanonicalize "-0e0" false == ("0", false)
-- A `xsd:double` coercion makes even a plain integer double-shaped.
#guard numberCanonicalize "1" true == ("1.0E0", true)
-- Magnitude ≥ 1e21 is double-shaped regardless of coercion.
#guard numberCanonicalize "1e21" false == ("1.0E21", true)

/-! ### RFC 8785 (JCS) number and document canonicalization -/

#guard jcsNumber "1" == "1"
#guard jcsNumber "1.0" == "1"
#guard jcsNumber "4.50" == "4.5"
#guard jcsNumber "1E30" == "1e+30"
#guard jcsNumber "2e-3" == "0.002"
#guard jcsNumber "-0" == "0"
#guard jcsNumber "1e-27" == "1e-27"
-- 17 significant digits: more than distinguish adjacent binary64
-- doubles, so the canonical form is the shortest decimal of the NEAREST
-- double (the path `dtoaShortest` exists for).
#guard jcsNumber "333333333.33333329" == "333333333.3333333"
-- Object members are sorted by key; arrays keep their order.
#guard jcsDocument (.object [("b", .number "1"), ("a", .number "2")]) == "{\"a\":2,\"b\":1}"
#guard jcsDocument (.array [.number "2", .number "1"]) == "[2,1]"

-- A `@json`-coerced value becomes an `rdf:JSON` literal carrying the
-- canonical form.
#guard toRdfNq "{\"@context\":{\"p\":{\"@id\":\"http://ex/p\",\"@type\":\"@json\"}},\"@id\":\"http://ex/s\",\"p\":{\"b\":1,\"a\":2}}"
       == some "<http://ex/s> <http://ex/p> \"{\\\"a\\\":2,\\\"b\\\":1}\"^^<http://www.w3.org/1999/02/22-rdf-syntax-ns#JSON> .\n"

/-! ### §8.6 `rdfDirection` -/

-- Default: the direction is dropped and the literal is language-tagged.
#guard toRdfNq "{\"@id\":\"http://ex/s\",\"http://ex/p\":{\"@value\":\"v\",\"@language\":\"en\",\"@direction\":\"rtl\"}}"
       == some "<http://ex/s> <http://ex/p> \"v\"@en .\n"
-- `i18n-datatype`: the datatype encodes language and direction.
#guard toRdfNq "{\"@id\":\"http://ex/s\",\"http://ex/p\":{\"@value\":\"v\",\"@language\":\"en-US\",\"@direction\":\"rtl\"}}"
         none (some "i18n-datatype")
       == some "<http://ex/s> <http://ex/p> \"v\"^^<https://www.w3.org/ns/i18n#en-us_rtl> .\n"
-- `compound-literal`: a fresh blank node with three triples.
#guard toRdfCount "{\"@id\":\"http://ex/s\",\"http://ex/p\":{\"@value\":\"v\",\"@language\":\"en\",\"@direction\":\"rtl\"}}"
       == some 1

end L4Factoidal.JSONLD.Tests
