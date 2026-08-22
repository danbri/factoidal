/-
L4Factoidal.SPARQL.Results — the SPARQL query-results model shared by
the four wire formats (SRX/SRJ/CSV/TSV).

Port of the *shape* `SPARQL.Protocol.fst` builds its four serialisers
(`serialise_response_json`/`_xml`/`_csv`/`_tsv`) and their `Parser.SRX`/
`Parser.JSONResults`/`Parser.CSVResults` counterparts around, factored
into one Lean type so `ResultsXml.lean`/`ResultsJson.lean`/
`ResultsCsvTsv.lean` share it instead of each inventing their own.

Specs (cited again in each format-specific module at the point they
matter):
  * SPARQL 1.1 Query Results XML Format, https://www.w3.org/TR/rdf-sparql-XMLres/
  * SPARQL 1.1 Query Results JSON Format, https://www.w3.org/TR/sparql11-results-json/
  * SPARQL 1.1 Query Results CSV and TSV Formats, https://www.w3.org/TR/sparql11-results-csv-tsv/

## `QueryResult` — what these formats can hold

SPARQL 1.1 §10 draws query results as one of three shapes: a set of
variable bindings (SELECT), a boolean (ASK), or an RDF graph
(CONSTRUCT/DESCRIBE). The four formats ported here (XML/JSON/CSV/TSV)
are defined ONLY over the first two — §1 of both the XML and JSON
specs, and §1 of the CSV/TSV spec, scope themselves to "variable
bindings, or a boolean". A CONSTRUCT/DESCRIBE result is an RDF graph
and is serialised by `Syntax.NTriples`/a Turtle writer, not by any
format in this directory; `QueryResult` therefore has no graph
constructor, and `ResultsCsvTsv.lean`'s serialisers reject `.boolean`
explicitly (CSV/TSV, unlike XML/JSON, defines no boolean encoding at
all — see that module's header).

## Term ↔ results-format value mapping — shared constructors

Every format's wire form for one bound value is one of:
  IRI | blank node | literal (plain / language-tagged / datatype) |
  RDF 1.2 triple-term (`{"type":"triple",...}` in JSON,
  `<triple>...</triple>` in XML — the SPARQL 1.2 Query Results
  formats Working Draft; `SPARQL.Protocol.fst`'s `json_term`/`xml_term`
  already emit this shape, so the Lean port follows). The
  CONSTRUCTORS below are the shared "build a `Term` from wire parts"
  half of that mapping (port of `Parser.JSONResults.fst`'s `mk_literal`/
  `mk_dir_literal` and `Parser.SRX.fst`'s inline literal-building code,
  which the two F* modules duplicate almost verbatim — collapsed into
  one place here). The DESTRUCTORS (`Term → wire form`) are
  format-specific (JSON needs a `Json` tree, XML needs escaped
  strings, CSV/TSV need their own lossy/N-Triples-style renderings)
  and live in each format's own module.
-/
import L4Factoidal.SPARQL.Algebra

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## The result model -/

/-- A SPARQL query result in one of the two forms the XML/JSON/CSV/TSV
Query Results formats can hold (see the module header for why
CONSTRUCT/DESCRIBE graphs are out of scope here). `vars` is the
declared `head` variable list — SEPARATE from which variables a given
row actually binds (SPARQL 1.1 §18.1.7.2 XML §3.1: a row may omit a
declared variable when it is unbound in that solution). -/
inductive QueryResult where
  /-- A SELECT-shaped result: the declared variables and the solution
  sequence (`SPARQL.Algebra.SolutionSeq` — reuses the same `Binding`
  the algebra evaluator produces, so a `GraphPattern.eval` result can
  be handed straight to a serialiser with no conversion step). -/
  | bindings (vars : List VarName) (rows : SolutionSeq)
  /-- An ASK-shaped result. -/
  | boolean (b : Bool)
  deriving DecidableEq, Repr

/-! ## Parse errors — shared across the four formats

Each format's own parser (XML, JSON) already reports failures typed to
that layer (`XML.XmlError`, `JSON.JsonError`); a `ResultsError` wraps
whichever underlying message applies (via each format's `ToString`
instance) plus failures specific to the RESULTS-FORMAT layer itself
(wrong root element, missing required member, malformed row). -/

/-- A results-format parse failure: a human-readable message. Unlike
`XmlError`/`JsonError`/`Syntax.ParseError` this carries no numeric
position, because a results-format failure is usually "this JSON/XML
parsed fine but does not have SPARQL-results SHAPE" — a structural
complaint over an already-built tree, not a lexical one; the
underlying lexical position (when there is one) is folded into `msg`
via the wrapped error's own `ToString` instance. -/
structure ResultsError where
  msg : String
  deriving DecidableEq, Repr

instance : ToString ResultsError := ⟨fun e => e.msg⟩

/-! ## Shared term ↔ wire-value constructors

Ported from `Parser.JSONResults.fst`'s `mk_literal`/`mk_dir_literal`
and the equivalent inline code in `Parser.SRX.fst`. All four return
`Option`/plain values (never fail on a well-formed IRI datatype, which
every caller here supplies as one of the fixed `RDF.Core` XSD/RDF
constants or an already-validated parsed IRIREF) so that a malformed
datatype IRI or an ill-formed literal combination surfaces as `none`
rather than corrupting the term. -/

/-- Build a URI-typed term, or `none` if `iri` fails RDF's minimal
well-formedness gate (`RDF.isIri`). Port of the `T_IRI`/`is_iri` guard
repeated at every `uri`/IRI wire-value site in both F* source modules. -/
def mkResultUri (iri : String) : Option Term :=
  if h : isIri iri then some (Term.iri ⟨iri, h⟩) else none

/-- Build a blank-node term. Never fails — a results-format blank-node
label is an opaque string, RDF 1.1 Concepts §3.4. -/
def mkResultBnode (label : String) : Term :=
  Term.bnode label

/-- Build a literal term from its lexical form, a RAW datatype IRI
string, and an optional language tag — `none` if the datatype string
is not a well-formed IRI or the resulting literal fails
`RDF.literalWf` (e.g. a language tag paired with a non-`rdf:langString`
datatype). Port of `Parser.JSONResults.fst`'s `mk_literal` /
`Parser.CSVResults.fst`'s `mk_literal` (the two F* modules define the
identical function independently; this is the one shared copy). -/
def mkResultLiteral (lexical : String) (dt : String) (lang : Option String) :
    Option Term :=
  if h : isIri dt then
    let l : Literal :=
      { lexicalForm := lexical, datatype := ⟨dt, h⟩, langTag := lang, direction := none }
    if hwf : literalWf l then some (Term.literal ⟨l, hwf⟩) else none
  else none

/-- Build an `rdf:dirLangString` (RDF 1.2 directional language-tagged
string) literal term, or `none` if the (lang, direction) combination
fails `literalWf` (it never does, since `rdfDirLangString` +
`some lang` is exactly `literalWf`'s third case — kept `Option`-typed
for parity with the sibling constructors and honesty about the
partial-function shape). Port of `Parser.JSONResults.fst`'s
`mk_dir_literal` — SPARQL 1.2 Query Results JSON Format Working Draft,
the `its:dir` member. -/
def mkResultDirLiteral (lexical lang : String) (dir : TextDirection) : Option Term :=
  let l : Literal :=
    { lexicalForm := lexical, datatype := rdfDirLangString,
      langTag := some lang, direction := some dir }
  if h : literalWf l then some (Term.literal ⟨l, h⟩) else none

/-- Parse an `its:dir` / RDF 1.2 base-direction wire value: `"ltr"` or
`"rtl"` only (strict, lowercase — an unrecognised value is "no
direction", never a hard parse error, matching
`SPARQL11.Algebra.parse_text_direction`'s degrade-gracefully
convention). Port of `Parser.JSONResults.fst`'s
`json_parse_text_direction`. -/
def parseResultDirection (s : String) : Option TextDirection :=
  if s == "ltr" then some .ltr
  else if s == "rtl" then some .rtl
  else none

/-- Build an RDF 1.2 triple-term binding from its three already-decoded
sub-values: the subject must be an IRI- or blank-node-shaped term (data
subjects are never literals or triple terms — RDF 1.1 Concepts §3.1),
the predicate must be IRI-shaped, and the object is any term. `none` on
any shape mismatch or if a sub-value itself failed to decode. Port of
the `T_TripleTerm` case shared, near-verbatim, by
`Parser.SRX.fst`'s `parse_binding_value_fuel` and
`Parser.JSONResults.fst`'s `parse_binding_value_fuel` (SPARQL 1.2
Results-XML and Results-JSON Working Drafts). -/
def mkResultTriple (s p o : Option Term) : Option Term :=
  match s, p, o with
  | some (.iri si),   some (.iri pi), some ot => some (Term.tripleTerm (.iri si) pi ot)
  | some (.bnode sb), some (.iri pi), some ot => some (Term.tripleTerm (.bnode sb) pi ot)
  | _, _, _ => none

end L4Factoidal.SPARQL
