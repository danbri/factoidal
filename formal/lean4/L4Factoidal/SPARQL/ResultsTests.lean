/-
L4Factoidal.SPARQL.ResultsTests — compile-time executable checks for
the SPARQL Query Results format port (SRX/SRJ/CSV/TSV).

Every `#guard` below is evaluated during `lake build`: a wrong answer
is a BUILD FAILURE, so these are unit tests with no separate runner —
same convention as `XML.Tests`/`JSON.Tests`/`Syntax.SyntaxTests`.

Three groups per format:
  1. round-trips (`parse ∘ serialise = id`) over hand-built
     `QueryResult` values — unbound variables, language-tagged and
     directional literals, typed literals, blank nodes, RDF 1.2 triple
     terms, booleans, empty results;
  2. parsing REAL W3C fixture text, copied verbatim from
     `third_party/testing/w3c/sparql/` (iron rule #6: no synthetic
     "inspired by" fixtures);
  3. negative cases (malformed/ill-shaped input).

Conformance discipline: nothing here is a conformance SCORE — hand
-picked fixtures exercising each parser/serialiser. A W3C-suite
harness reading manifests from disk is a later rung (see
`docs/designissues/2026-08-22-lean4-w3c-harness.md`). -/
import L4Factoidal.SPARQL.ResultsXml
import L4Factoidal.SPARQL.ResultsJson
import L4Factoidal.SPARQL.ResultsCsvTsv

namespace L4Factoidal.SPARQL.ResultsTests

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-! ## Term-building helpers (test-local — `RDF.Core` exports only
`Literal.string`/`Literal.langString`, not a datatype-generic or
directional constructor). Follows the project's autoparam convention
(`skills/factoidal-lean-basics`): the well-formedness witness is
computed by `rfl` at each concrete call site. -/

def uri (s : String) (h : isIri s := by rfl) : Term := Term.iri ⟨s, h⟩

def bnodeT (s : String) : Term := Term.bnode s

def plainLit (lex : String)
    (h : literalWf { lexicalForm := lex, datatype := xsdString, langTag := none, direction := none } := by rfl) :
    Term :=
  Term.literal ⟨{ lexicalForm := lex, datatype := xsdString, langTag := none, direction := none }, h⟩

def typedLit (lex : String) (dt : WfIri)
    (h : literalWf { lexicalForm := lex, datatype := dt, langTag := none, direction := none } := by rfl) :
    Term :=
  Term.literal ⟨{ lexicalForm := lex, datatype := dt, langTag := none, direction := none }, h⟩

def langLit (lex tag : String)
    (h : literalWf { lexicalForm := lex, datatype := rdfLangString, langTag := some tag, direction := none } :=
      by rfl) :
    Term :=
  Term.literal ⟨{ lexicalForm := lex, datatype := rdfLangString, langTag := some tag, direction := none }, h⟩

def dirLit (lex tag : String) (dir : TextDirection)
    (h : literalWf { lexicalForm := lex, datatype := rdfDirLangString, langTag := some tag,
                      direction := some dir } := by rfl) :
    Term :=
  Term.literal
    ⟨{ lexicalForm := lex, datatype := rdfDirLangString, langTag := some tag, direction := some dir }, h⟩

def wfIri (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

def tripleT (s p : String) (o' : Term) (hs : isIri s := by rfl) (hp : isIri p := by rfl) : Term :=
  Term.tripleTerm (.iri ⟨s, hs⟩) ⟨p, hp⟩ o'

/-! ## §1 SRX — round-trips (SPARQL 1.1 Query Results XML Format) -/

#guard parseSrx ((QueryResult.bindings ["x"] [[("x", uri "http://example.org/a")]]).toSrx) =
  .ok (QueryResult.bindings ["x"] [[("x", uri "http://example.org/a")]])

#guard parseSrx ((QueryResult.bindings ["x", "y"]
    [[("x", uri "http://example.org/a"), ("y", typedLit "1" xsdInteger)],
     [("x", uri "http://example.org/b"), ("y", typedLit "2" xsdInteger)]]).toSrx) =
  .ok (QueryResult.bindings ["x", "y"]
    [[("x", uri "http://example.org/a"), ("y", typedLit "1" xsdInteger)],
     [("x", uri "http://example.org/b"), ("y", typedLit "2" xsdInteger)]])

-- Unbound variable: `y` is declared but absent from the row (SRX §3.1).
#guard parseSrx ((QueryResult.bindings ["x", "y"] [[("x", uri "http://example.org/a")]]).toSrx) =
  .ok (QueryResult.bindings ["x", "y"] [[("x", uri "http://example.org/a")]])

#guard parseSrx ((QueryResult.bindings ["l"] [[("l", langLit "chat" "fr")]]).toSrx) =
  .ok (QueryResult.bindings ["l"] [[("l", langLit "chat" "fr")]])

#guard parseSrx ((QueryResult.bindings ["b"] [[("b", bnodeT "b0")]]).toSrx) =
  .ok (QueryResult.bindings ["b"] [[("b", bnodeT "b0")]])

-- Escaping: '&' / '<' / '>' inside a literal's lexical form.
#guard parseSrx ((QueryResult.bindings ["p"] [[("p", plainLit "hello & <world>")]]).toSrx) =
  .ok (QueryResult.bindings ["p"] [[("p", plainLit "hello & <world>")]])

#guard parseSrx ((QueryResult.boolean true).toSrx) = .ok (QueryResult.boolean true)
#guard parseSrx ((QueryResult.boolean false).toSrx) = .ok (QueryResult.boolean false)

-- Empty results: declared variables, zero rows; and no variables at all.
#guard parseSrx ((QueryResult.bindings ["x"] []).toSrx) = .ok (QueryResult.bindings ["x"] [])
#guard parseSrx ((QueryResult.bindings [] []).toSrx) = .ok (QueryResult.bindings [] [])

-- RDF 1.2 triple-term binding (SPARQL 1.2 Results-XML Working Draft).
#guard parseSrx ((QueryResult.bindings ["t"]
    [[("t", tripleT "http://example.org/s" "http://example.org/p" (uri "http://example.org/o"))]]).toSrx) =
  .ok (QueryResult.bindings ["t"]
    [[("t", tripleT "http://example.org/s" "http://example.org/p" (uri "http://example.org/o"))]])

/-! ## §2 SRX — real W3C fixtures, copied verbatim -/

/-- `third_party/testing/w3c/sparql/sparql11/property-path/pp08.srx`. -/
def pp08Srx : String :=
  "<sparql xmlns='http://www.w3.org/2005/sparql-results#'>\n" ++
  "<head>\n" ++
  "</head>\n" ++
  "<boolean>true</boolean>\n" ++
  "</sparql>\n"

#guard parseSrx pp08Srx = .ok (QueryResult.boolean true)

/-- `third_party/testing/w3c/sparql/sparql11/project-expression/projexp04.srx`. -/
def projexp04Srx : String :=
  "<sparql xmlns='http://www.w3.org/2005/sparql-results#'>\n" ++
  "<head>\n" ++
  "<variable name='x'/>\n" ++
  "<variable name='y'/>\n" ++
  "<variable name='sum'/>\n" ++
  "</head>\n" ++
  "<results>\n" ++
  "<result>\n" ++
  "<binding name='x'><uri>http://www.example.org/instance#a</uri></binding>\n" ++
  "<binding name='y'><literal datatype='http://www.w3.org/2001/XMLSchema#integer'>1</literal></binding>\n" ++
  "<binding name='sum'><literal datatype='http://www.w3.org/2001/XMLSchema#integer'>2</literal></binding>\n" ++
  "</result>\n" ++
  "<result>\n" ++
  "<binding name='x'><uri>http://www.example.org/instance#a</uri></binding>\n" ++
  "<binding name='y'><literal datatype='http://www.w3.org/2001/XMLSchema#integer'>2</literal></binding>\n" ++
  "<binding name='sum'><literal datatype='http://www.w3.org/2001/XMLSchema#integer'>4</literal></binding>\n" ++
  "</result>\n" ++
  "</results>\n" ++
  "</sparql>\n"

#guard parseSrx projexp04Srx = .ok (QueryResult.bindings ["x", "y", "sum"]
  [[("x", uri "http://www.example.org/instance#a"), ("y", typedLit "1" xsdInteger),
    ("sum", typedLit "2" xsdInteger)],
   [("x", uri "http://www.example.org/instance#a"), ("y", typedLit "2" xsdInteger),
    ("sum", typedLit "4" xsdInteger)]])

/-! ## §3 SRX — negative cases -/

-- Wrong root element (this port's deliberate strengthening — see
-- `ResultsXml.lean`'s module header).
#guard match parseSrx "<notsparql><head></head></notsparql>" with
  | .error _ => true | .ok _ => false

-- Malformed XML (unterminated element).
#guard match parseSrx "<sparql><head>" with | .error _ => true | .ok _ => false

-- <boolean> content is neither "true" nor "false".
#guard match parseSrx "<sparql><head></head><boolean>maybe</boolean></sparql>" with
  | .error _ => true | .ok _ => false

/-! ## §4 SRJ — round-trips (SPARQL 1.1 Query Results JSON Format) -/

#guard parseSrj ((QueryResult.bindings ["x"] [[("x", uri "http://example.org/a")]]).toSrj) =
  .ok (QueryResult.bindings ["x"] [[("x", uri "http://example.org/a")]])

#guard parseSrj ((QueryResult.bindings ["x", "y"]
    [[("x", uri "http://example.org/a"), ("y", typedLit "1" xsdInteger)],
     [("x", uri "http://example.org/b"), ("y", typedLit "2" xsdInteger)]]).toSrj) =
  .ok (QueryResult.bindings ["x", "y"]
    [[("x", uri "http://example.org/a"), ("y", typedLit "1" xsdInteger)],
     [("x", uri "http://example.org/b"), ("y", typedLit "2" xsdInteger)]])

#guard parseSrj ((QueryResult.bindings ["x", "y"] [[("x", uri "http://example.org/a")]]).toSrj) =
  .ok (QueryResult.bindings ["x", "y"] [[("x", uri "http://example.org/a")]])

#guard parseSrj ((QueryResult.bindings ["l"] [[("l", langLit "chat" "fr")]]).toSrj) =
  .ok (QueryResult.bindings ["l"] [[("l", langLit "chat" "fr")]])

#guard parseSrj ((QueryResult.bindings ["b"] [[("b", bnodeT "b0")]]).toSrj) =
  .ok (QueryResult.bindings ["b"] [[("b", bnodeT "b0")]])

-- Escaping: an embedded '"' inside a literal's lexical form.
#guard parseSrj ((QueryResult.bindings ["p"] [[("p", plainLit "hello \"world\"")]]).toSrj) =
  .ok (QueryResult.bindings ["p"] [[("p", plainLit "hello \"world\"")]])

#guard parseSrj ((QueryResult.boolean true).toSrj) = .ok (QueryResult.boolean true)
#guard parseSrj ((QueryResult.boolean false).toSrj) = .ok (QueryResult.boolean false)

#guard parseSrj ((QueryResult.bindings ["x"] []).toSrj) = .ok (QueryResult.bindings ["x"] [])
#guard parseSrj ((QueryResult.bindings [] []).toSrj) = .ok (QueryResult.bindings [] [])

-- RDF 1.2 triple-term binding (SPARQL 1.2 Results-JSON Working Draft).
#guard parseSrj ((QueryResult.bindings ["t"]
    [[("t", tripleT "http://example.org/s" "http://example.org/p" (uri "http://example.org/o"))]]).toSrj) =
  .ok (QueryResult.bindings ["t"]
    [[("t", tripleT "http://example.org/s" "http://example.org/p" (uri "http://example.org/o"))]])

-- RDF 1.2 directional literal (`its:dir`).
#guard parseSrj ((QueryResult.bindings ["d"] [[("d", dirLit "hello" "en" .ltr)]]).toSrj) =
  .ok (QueryResult.bindings ["d"] [[("d", dirLit "hello" "en" .ltr)]])

/-! ## §5 SRJ — real W3C fixtures, copied verbatim -/

/-- `third_party/testing/w3c/sparql/sparql12/rdf11/langstring-datatype.srj`. -/
def langstringDatatypeSrj : String :=
  "{\n" ++
  "  \"head\": {\n" ++
  "    \"vars\": [ \"dt\" ]\n" ++
  "  },\n" ++
  "  \"results\": {\n" ++
  "    \"bindings\": [\n" ++
  "      {\n" ++
  "        \"dt\": { \"type\": \"uri\", \"value\": \"http://www.w3.org/1999/02/22-rdf-syntax-ns#langString\" }\n" ++
  "      }\n" ++
  "    ]\n" ++
  "  }\n" ++
  "}\n"

#guard parseSrj langstringDatatypeSrj =
  .ok (QueryResult.bindings ["dt"] [[("dt", uri "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString")]])

/-- `third_party/testing/w3c/sparql/sparql12/rdf11/plain-string-same.srj`. -/
def plainStringSameSrj : String :=
  "{\n" ++
  "  \"head\": {},\n" ++
  "  \"boolean\": true\n" ++
  "}\n"

#guard parseSrj plainStringSameSrj = .ok (QueryResult.boolean true)

/-! ## §6 SRJ — negative cases -/

-- Missing 'head' (this port's deliberate strengthening — see
-- `ResultsJson.lean`'s module header).
#guard match parseSrj "{\"results\":{\"bindings\":[]}}" with | .error _ => true | .ok _ => false

-- Unparseable JSON syntax.
#guard match parseSrj "{not valid json" with | .error _ => true | .ok _ => false

-- Top-level value is an array, not an object.
#guard match parseSrj "[1,2,3]" with | .error _ => true | .ok _ => false

/-! ## §7 CSV — real W3C fixture + round-trips (SPARQL 1.1 Query
Results CSV Format, §2) -/

/-- `third_party/testing/w3c/sparql/sparql11/csv-tsv-res/csvtsv01.csv`. -/
def csvtsv01Csv : String :=
  "s,p,o\n" ++
  "http://example.org/s1,http://example.org/p1,http://example.org/s2\n" ++
  "http://example.org/s2,http://example.org/p2,foo\n" ++
  "http://example.org/s3,http://example.org/p3,bar\n" ++
  "http://example.org/s4,http://example.org/p4,4\n" ++
  "http://example.org/s5,http://example.org/p5,5.5\n" ++
  "http://example.org/s6,http://example.org/p6,_:a\n"

-- CSV is lossy (§2): bare numerals and plain words alike come back as
-- xsd:string, never xsd:integer/xsd:decimal.
#guard parseCsv csvtsv01Csv = .ok (QueryResult.bindings ["s", "p", "o"]
  [[("s", uri "http://example.org/s1"), ("p", uri "http://example.org/p1"),
    ("o", uri "http://example.org/s2")],
   [("s", uri "http://example.org/s2"), ("p", uri "http://example.org/p2"), ("o", plainLit "foo")],
   [("s", uri "http://example.org/s3"), ("p", uri "http://example.org/p3"), ("o", plainLit "bar")],
   [("s", uri "http://example.org/s4"), ("p", uri "http://example.org/p4"), ("o", plainLit "4")],
   [("s", uri "http://example.org/s5"), ("p", uri "http://example.org/p5"), ("o", plainLit "5.5")],
   [("s", uri "http://example.org/s6"), ("p", uri "http://example.org/p6"), ("o", bnodeT "a")]])

/-- Unwrap `toCsv` for a `.bindings` result (never `.error` there). -/
def csvOf (r : QueryResult) : String :=
  match r.toCsv with | .ok s => s | .error _ => ""

-- Round-trips only hold for CSV-native (xsd:string) content — CSV is
-- lossy for anything else (§2), so this is the honest round-trip claim
-- for this format, not a general one.
#guard parseCsv (csvOf (QueryResult.bindings ["s"] [[("s", plainLit "foo")]])) =
  .ok (QueryResult.bindings ["s"] [[("s", plainLit "foo")]])

-- RFC 4180 quoting: a comma inside a value.
#guard parseCsv (csvOf (QueryResult.bindings ["s"] [[("s", plainLit "a,b")]])) =
  .ok (QueryResult.bindings ["s"] [[("s", plainLit "a,b")]])

-- RFC 4180 quoting: an embedded double quote.
#guard parseCsv (csvOf (QueryResult.bindings ["s"] [[("s", plainLit "a\"b")]])) =
  .ok (QueryResult.bindings ["s"] [[("s", plainLit "a\"b")]])

/-! ## §8 CSV — negative cases -/

-- CSV/TSV define no boolean encoding at all (§1).
#guard match (QueryResult.boolean true).toCsv with | .error _ => true | .ok _ => false

-- No header line at all.
#guard match parseCsv "" with | .error _ => true | .ok _ => false

/-! ## §9 TSV — real W3C fixture + round-trips (SPARQL 1.1 Query
Results TSV Format, §3) -/

/-- `third_party/testing/w3c/sparql/sparql11/csv-tsv-res/csvtsv01.tsv`. -/
def csvtsv01Tsv : String :=
  "?s\t?p\t?o\n" ++
  "<http://example.org/s1>\t<http://example.org/p1>\t<http://example.org/s2>\n" ++
  "<http://example.org/s2>\t<http://example.org/p2>\t\"foo\"\n" ++
  "<http://example.org/s3>\t<http://example.org/p3>\t\"bar\"\n" ++
  "<http://example.org/s4>\t<http://example.org/p4>\t4\n" ++
  "<http://example.org/s5>\t<http://example.org/p5>\t5.5\n" ++
  "<http://example.org/s6>\t<http://example.org/p6>\t_:b0\n"

-- TSV, unlike CSV, preserves full typing.
#guard parseTsv csvtsv01Tsv = .ok (QueryResult.bindings ["s", "p", "o"]
  [[("s", uri "http://example.org/s1"), ("p", uri "http://example.org/p1"),
    ("o", uri "http://example.org/s2")],
   [("s", uri "http://example.org/s2"), ("p", uri "http://example.org/p2"), ("o", plainLit "foo")],
   [("s", uri "http://example.org/s3"), ("p", uri "http://example.org/p3"), ("o", plainLit "bar")],
   [("s", uri "http://example.org/s4"), ("p", uri "http://example.org/p4"),
    ("o", typedLit "4" xsdInteger)],
   [("s", uri "http://example.org/s5"), ("p", uri "http://example.org/p5"),
    ("o", typedLit "5.5" xsdDecimal)],
   [("s", uri "http://example.org/s6"), ("p", uri "http://example.org/p6"), ("o", bnodeT "b0")]])

/-- Unwrap `toTsv` for a `.bindings` result (never `.error` there). -/
def tsvOf (r : QueryResult) : String :=
  match r.toTsv with | .ok s => s | .error _ => ""

#guard parseTsv (tsvOf (QueryResult.bindings ["x"] [[("x", uri "http://example.org/a")]])) =
  .ok (QueryResult.bindings ["x"] [[("x", uri "http://example.org/a")]])

#guard parseTsv (tsvOf (QueryResult.bindings ["x"] [[("x", typedLit "42" xsdInteger)]])) =
  .ok (QueryResult.bindings ["x"] [[("x", typedLit "42" xsdInteger)]])

#guard parseTsv (tsvOf (QueryResult.bindings ["x"] [[("x", langLit "chat" "fr")]])) =
  .ok (QueryResult.bindings ["x"] [[("x", langLit "chat" "fr")]])

#guard parseTsv (tsvOf (QueryResult.bindings ["x"] [[("x", bnodeT "b0")]])) =
  .ok (QueryResult.bindings ["x"] [[("x", bnodeT "b0")]])

-- Unbound variable round-trips (an empty TSV cell).
#guard parseTsv (tsvOf (QueryResult.bindings ["x", "y"] [[("x", uri "http://example.org/a")]])) =
  .ok (QueryResult.bindings ["x", "y"] [[("x", uri "http://example.org/a")]])

#guard parseTsv (tsvOf (QueryResult.bindings ["x"] [])) = .ok (QueryResult.bindings ["x"] [])

-- RDF 1.2 directional literal round-trips through TSV's N-Triples-style
-- cell syntax (`Term.toNTriples`/`readLiteral` under `.rdf12`).
#guard parseTsv (tsvOf (QueryResult.bindings ["d"] [[("d", dirLit "hello" "en" .ltr)]])) =
  .ok (QueryResult.bindings ["d"] [[("d", dirLit "hello" "en" .ltr)]])

/-! ## §10 TSV — negative cases -/

#guard match (QueryResult.boolean true).toTsv with | .error _ => true | .ok _ => false

-- Malformed IRIREF (unterminated).
#guard match parseTsv "?x\n<http://example.org\n" with | .error _ => true | .ok _ => false

-- KNOWN GAP inherited from `Parser.CSVResults.fst`: `tsv_term`
-- SERIALISES an RDF 1.2 triple term as `<<( s <p> o )>>`, but
-- `parse_tsv_value` has NO case for `<<(` at all — the F* source's TSV
-- reader and writer are asymmetric for this one term shape. This port
-- reproduces that gap faithfully (see `PORT_NOTES.md`) rather than
-- silently adding parsing support the F* source lacks; the field is
-- rejected (the leading `<<` is not a legal IRIREF start) rather than
-- mis-parsed.
#guard match parseTsv "?t\n<<( <http://example.org/s> <http://example.org/p> <http://example.org/o> )>>\n" with
  | .error _ => true | .ok _ => false

/-! ## §11 The CSV-lenient comparison rule (`Term.eqbCsvLenient`) -/

#guard Term.eqbCsvLenient (plainLit "4") (typedLit "4" xsdInteger) = true
#guard Term.eqb (plainLit "4") (typedLit "4" xsdInteger) = false
#guard Term.eqbCsvLenient (typedLit "4" xsdInteger) (typedLit "5" xsdInteger) = false
#guard Term.eqbCsvLenient (bnodeT "a") (bnodeT "xyz") = true
#guard Term.eqbCsvLenient (uri "http://example.org/a") (uri "http://example.org/a") = true
#guard Term.eqbCsvLenient (uri "http://example.org/a") (uri "http://example.org/b") = false

end L4Factoidal.SPARQL.ResultsTests
