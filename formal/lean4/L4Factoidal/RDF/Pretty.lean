/-
L4Factoidal.RDF.Pretty — abbreviated, display-only rendering.

Port of `formal/fstar/RDF.Pretty.fst` (235 lines).

The F\* module exists to stop a drift: `factoidal_cli.ml` and
`factoidal_explain.ml` each implemented the same algorithm with its own
hand-maintained prefix table (a general-purpose foaf/dc/schema flavour
and a parliament-corpus flavour). The algorithm is here and both tables
are constants.

## What is NOT here, and why it is worth saying

The module used to carry `term_to_ntriples`, a SECOND N-Triples term
renderer that wrote a literal's lexical form verbatim. It was described
as "for display, not wire", and every consumer treated its output as
wire: `factoidal --dump` and the COTTAS store's object column both went
through it.

That produced issue #339 (dump emitted output the project's own parser
rejected) and issue #443 (import then query DESTROYED any literal
containing a quote, a newline or a backslash — the store cell did not
re-parse and the reader returned a sentinel).

The F\* tree deleted the function rather than fixing it: making it
escape would have made it byte-identical to
`RDF.NQuads.Serialize.nq_term_to_string`, and a second name for the same
rendering is what let the two drift apart. This port carries the same
absence. A caller wanting an N-Triples term uses
`L4Factoidal.Syntax.Term.toNTriples`.

What remains is the abbreviated rendering, which is display-only and
has no wire consumer. It keeps the verbatim lexical form on purpose.
-/
import L4Factoidal.RDF.Graph
import L4Factoidal.SPARQL.Algebra

namespace L4Factoidal.RDF

open L4Factoidal.SPARQL

/-! ## Prefix tables

A `(namespace, abbreviation)` list. First match wins on overlap, which
is the legacy behaviour. -/

abbrev PrefixTable := List (String × String)

/-- A STRICT prefix: `pfx` is a prefix of `s` and shorter than it.
    Strictness avoids matching the whole IRI, which would leave an empty
    rest and produce nonsense like `"rdf:"` for the namespace IRI
    itself. -/
def startsWithStrict (s pfx : String) : Bool :=
  pfx.length < s.length && s.startsWith pfx

def findPrefix (table : PrefixTable) (iri : String) : Option (String × String) :=
  table.find? (fun p => startsWithStrict iri p.1)

def abbreviateIri (table : PrefixTable) (iri : String) : String :=
  match findPrefix table iri with
  | some (ns, abbr) =>
      if ns.length < iri.length then abbr ++ iri.drop ns.length
      else "<" ++ iri ++ ">"
  | none => "<" ++ iri ++ ">"

/-! ## Term rendering

IRIs are abbreviated through the table; blank nodes and literals render
as in N-Triples. Literal DATATYPES are deliberately not abbreviated —
that is a Turtle 1.1 nicety neither OCaml caller did, and the legacy
behaviour is preserved. -/

/-- RDF 1.2 base-direction suffix. Empty for every RDF 1.1 literal, so
    output stays byte-identical for pre-1.2 data. -/
def dirSuffix : Option TextDirection → String
  | some .ltr => "--ltr"
  | some .rtl => "--rtl"
  | none      => ""

def termWithPrefixes (table : PrefixTable) : Term → String
  | .iri i   => abbreviateIri table i.val
  | .bnode b => "_:" ++ b
  | .literal wl =>
      let l := wl.val
      match l.langTag with
      | some tag => "\"" ++ l.lexicalForm ++ "\"@" ++ tag ++ dirSuffix l.direction
      | none =>
          if l.datatype == xsdString then "\"" ++ l.lexicalForm ++ "\""
          else "\"" ++ l.lexicalForm ++ "\"^^<" ++ l.datatype.val ++ ">"
  | .tripleTerm s p o =>
      let subjStr := match s with
        | .iri i   => abbreviateIri table i.val
        | .bnode b => "_:" ++ b
      "<<( " ++ subjStr ++ " <" ++ p.val ++ "> " ++ termWithPrefixes table o ++ " )>>"

def subjectWithPrefixes (table : PrefixTable) : Subject → String
  | .iri i   => abbreviateIri table i.val
  | .bnode b => "_:" ++ b

/-! ## The two tables

They overlap on rdf, rdfs, xsd and owl, and diverge after that. Adding a
prefix means extending one of these lists, here — which is what stops
the drift between the two consumers. -/

/-- CLI Turtle output, general purpose. -/
def cliTurtlePrefixes : PrefixTable :=
  [ ("http://www.w3.org/1999/02/22-rdf-syntax-ns#", "rdf:"),
    ("http://www.w3.org/2000/01/rdf-schema#",       "rdfs:"),
    ("http://www.w3.org/2001/XMLSchema#",           "xsd:"),
    ("http://www.w3.org/2002/07/owl#",              "owl:"),
    ("http://xmlns.com/foaf/0.1/",                  "foaf:"),
    ("http://purl.org/dc/terms/",                   "dcterms:"),
    ("http://purl.org/dc/elements/1.1/",            "dc:"),
    ("http://schema.org/",                          "schema:") ]

/-- The `--explain` dump, parliament-corpus aware. -/
def explainPrefixes : PrefixTable :=
  [ ("http://www.w3.org/1999/02/22-rdf-syntax-ns#", "rdf:"),
    ("http://www.w3.org/2000/01/rdf-schema#",       "rdfs:"),
    ("http://www.w3.org/2001/XMLSchema#",           "xsd:"),
    ("http://www.w3.org/2002/07/owl#",              "owl:"),
    ("http://www.opengis.net/ont/geosparql#",       "geo:"),
    ("https://id.parliament.uk/schema/",            ":") ]

def termToTurtle (t : Term) : String := termWithPrefixes cliTurtlePrefixes t
def subjectToTurtle (s : Subject) : String := subjectWithPrefixes cliTurtlePrefixes s
def termShortExplain (t : Term) : String := termWithPrefixes explainPrefixes t

/-! ## SPARQL pattern-term rendering -/

def patternTermShort (table : PrefixTable) : PatternTerm → String
  | .var v     => "?" ++ v
  | .iri i     => abbreviateIri table i.val
  | .bnode b   => "_:" ++ b
  | .literal l => termWithPrefixes table (.literal l)
  | .tripleTerm s p o =>
      "<<( " ++ patternTermShort table s ++ " " ++ patternTermShort table p
             ++ " " ++ patternTermShort table o ++ " )>>"

def patternSubjectShort (table : PrefixTable) : PatternSubject → String
  | .var v   => "?" ++ v
  | .iri i   => abbreviateIri table i.val
  | .bnode b => "_:" ++ b
  | .tripleTerm s p o =>
      "<<( " ++ patternTermShort table s ++ " " ++ patternTermShort table p
             ++ " " ++ patternTermShort table o ++ " )>>"

def triplePatternShort (table : PrefixTable) (tp : TriplePattern) : String :=
  patternSubjectShort table tp.s ++ " " ++
  patternTermShort table tp.p ++ " " ++
  patternTermShort table tp.o

def patternTermShortExplain (pt : PatternTerm) : String :=
  patternTermShort explainPrefixes pt
def patternSubjectShortExplain (ps : PatternSubject) : String :=
  patternSubjectShort explainPrefixes ps
def triplePatternShortExplain (tp : TriplePattern) : String :=
  triplePatternShort explainPrefixes tp

/-! ## Build-time checks

### Strictness is the point

`startsWithStrict` must REJECT the namespace IRI itself. Without that,
`abbreviateIri` renders `rdf:` — a prefix with no local name — which is
not a term. -/

#guard startsWithStrict "http://www.w3.org/2001/XMLSchema#int"
                        "http://www.w3.org/2001/XMLSchema#"
#guard !startsWithStrict "http://www.w3.org/2001/XMLSchema#"
                         "http://www.w3.org/2001/XMLSchema#"
#guard abbreviateIri cliTurtlePrefixes "http://www.w3.org/2001/XMLSchema#int" == "xsd:int"
#guard abbreviateIri cliTurtlePrefixes "http://www.w3.org/2001/XMLSchema#"
        == "<http://www.w3.org/2001/XMLSchema#>"

/-! An IRI in no table renders bracketed, not bare. -/

#guard abbreviateIri cliTurtlePrefixes "http://example.org/x" == "<http://example.org/x>"

/-! ### The two tables really differ

`geo:` is in the explain table only; `foaf:` in the CLI table only. A
port that used one table for both would pass every other check here. -/

#guard abbreviateIri explainPrefixes "http://www.opengis.net/ont/geosparql#asWKT" == "geo:asWKT"
#guard abbreviateIri cliTurtlePrefixes "http://www.opengis.net/ont/geosparql#asWKT"
        == "<http://www.opengis.net/ont/geosparql#asWKT>"
#guard abbreviateIri cliTurtlePrefixes "http://xmlns.com/foaf/0.1/name" == "foaf:name"
#guard abbreviateIri explainPrefixes "http://xmlns.com/foaf/0.1/name"
        == "<http://xmlns.com/foaf/0.1/name>"

/-! ### First match wins on overlap

The explain table's `:` for the parliament schema comes last, so a
geosparql IRI takes `geo:` and not `:`. -/

#guard abbreviateIri explainPrefixes "https://id.parliament.uk/schema/Member" == ":Member"

/-! ### Terms -/

private theorem exIri (s : String) : isIri ("http://e/" ++ s) = true := by
  simp [isIri, String.isEmpty]

private def yi (s : String) : WfIri := ⟨"http://e/" ++ s, exIri s⟩

#guard termToTurtle (.bnode "b1") == "_:b1"
#guard termToTurtle (.iri (yi "x")) == "<http://e/x>"
#guard termToTurtle (.literal (Literal.string "hi")) == "\"hi\""
#guard termToTurtle (.literal (Literal.langString "hi" "en")) == "\"hi\"@en"

/-! An `xsd:string` literal renders WITHOUT its datatype; any other
    datatype renders WITH it, unabbreviated. Both halves matter: the
    first is RDF 1.1's default datatype, the second is the deliberate
    non-abbreviation. -/

#guard termToTurtle (.literal ⟨{ lexicalForm := "1", datatype := xsdInteger,
                                 langTag := none, direction := none }, by rfl⟩)
        == "\"1\"^^<http://www.w3.org/2001/XMLSchema#integer>"

/-! ### The lexical form is VERBATIM — display only

A literal holding a quote renders with that quote unescaped. That is
what makes this rendering unusable as wire format, and it is the
behaviour issues #339 and #443 were caused by trusting. Stated as a
check so nobody "fixes" it into a second serialiser. -/

#guard termToTurtle (.literal (Literal.string "a\"b")) == "\"a\"b\""

/-! ### Pattern terms -/

#guard patternTermShortExplain (.var "s") == "?s"
#guard patternTermShortExplain (.iri (yi "p")) == "<http://e/p>"
#guard triplePatternShortExplain { s := .var "s", p := .iri (yi "p"), o := .var "o" }
        == "?s <http://e/p> ?o"

end L4Factoidal.RDF
