/-
L4Factoidal.Syntax.SyntaxTests — compile-time executable checks for the
N-Triples / N-Quads port.

Every `#guard` below is evaluated during `lake build` (same discipline as
`L4Factoidal.Tests`): a wrong answer is a BUILD FAILURE. Fixtures are
written inline as Lean strings in the style of the W3C RDF 1.1 N-Triples
syntax test suite (`rdf-n-triples/nt-syntax-*`, `nt-syntax-bad-*`) and the
RDF 1.2 c14n / syntax suites — this worktree has no `third_party/testing`
checkout (submodules absent), so the fixtures below are written BY HAND
against the same grammar the W3C suite exercises, not copied from disk.

Local helpers below (`isOk`/`isErr`/`okEq`) exist ONLY because `Except`
has no core `BEq`/`isOk`. `RDF.NamedGraph` and `RDF.Dataset` derive
`DecidableEq`, so `==` compares them directly — the earlier local
`namedGraphsEq` workaround is gone.
-/

import L4Factoidal.Syntax.NQuads

namespace L4Factoidal.Syntax.SyntaxTests

open L4Factoidal.RDF L4Factoidal.Syntax

/-! ### Local test helpers (not part of the port; see module header) -/

def isOk {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

def isErr {ε α : Type} : Except ε α → Bool
  | .ok _ => false
  | .error _ => true

def okEq {ε α : Type} [BEq α] (x : Except ε α) (v : α) : Bool :=
  match x with
  | .ok a => a == v
  | .error _ => false

/-! ### Positive N-Triples fixtures (RDF 1.1) -/

-- nt-syntax-file-01-style: a single plain-literal triple.
#guard isOk (parseNTriples "<http://example.org/s> <http://example.org/p> \"o\" .\n")

-- nt-syntax-uri-04-style: an IRI object.
#guard isOk (parseNTriples
  "<http://example.org/s> <http://example.org/p> <http://example.org/o> .\n")

-- nt-syntax-bnode-01-style: blank-node subject and object.
#guard isOk (parseNTriples
  "_:a <http://example.org/p> _:b .\n")

-- nt-syntax-str-esc-01-style: every ECHAR plus a UCHAR.
#guard isOk (parseNTriples
  "<http://example.org/s> <http://example.org/p> \"tab:\\t nl:\\n cr:\\r bs:\\\\ q:\\\" u:\\u00E9\" .\n")

-- nt-syntax-string-with-lang: language-tagged literal.
#guard isOk (parseNTriples
  "<http://example.org/s> <http://example.org/p> \"chat\"@en .\n")

-- BCP47 subtag language tag.
#guard isOk (parseNTriples
  "<http://example.org/s> <http://example.org/p> \"chat\"@en-US .\n")

-- nt-syntax-datatypes-01-style: a datatyped literal.
#guard isOk (parseNTriples
  "<http://example.org/s> <http://example.org/p> \"42\"^^<http://www.w3.org/2001/XMLSchema#integer> .\n")

-- nt-syntax-bnode-with-digits: a blank-node label starting with a digit
-- (BLANK_NODE_LABEL start char is PN_CHARS_U | [0-9]).
#guard isOk (parseNTriples "_:0a <http://example.org/p> _:1 .\n")

-- nt-syntax-bnode-with-internal-dot: an internal dot is legal; the label
-- is `a.b`, not truncated at the dot.
#guard isOk (parseNTriples "_:a.b <http://example.org/p> _:c .\n")

-- nt-syntax-comment-01-style: comment lines and blank lines are skipped.
#guard isOk (parseNTriples
  "# a comment\n\n<http://example.org/s> <http://example.org/p> \"o\" .\n# trailing\n")

-- Multiple triples, one per line.
#guard okEq (Except.map List.length (parseNTriples
  "<http://example.org/s> <http://example.org/p> \"1\" .\n\
   <http://example.org/s> <http://example.org/p> \"2\" .\n")) 2

/-! ### Negative N-Triples fixtures (RDF 1.1) -/

-- nt-syntax-bad-uri-04-style: a raw space inside an IRIREF.
#guard isErr (parseNTriples "<http://example.org/s p> <http://example.org/p> \"o\" .\n")

-- nt-syntax-bad-string-04-style: an unescaped raw newline inside a string.
#guard isErr (parseNTriples "<http://example.org/s> <http://example.org/p> \"o\no\" .\n")

-- nt-syntax-bad-esc-01-style: an unknown escape.
#guard isErr (parseNTriples "<http://example.org/s> <http://example.org/p> \"\\q\" .\n")

-- Missing terminating '.'.
#guard isErr (parseNTriples "<http://example.org/s> <http://example.org/p> \"o\"\n")

-- A literal used as the subject is not legal.
#guard isErr (parseNTriples "\"s\" <http://example.org/p> \"o\" .\n")

-- A surrogate codepoint in a \u escape is rejected, not silently replaced.
#guard isErr (parseNTriples "<http://example.org/s> <http://example.org/p> \"\\uD800\" .\n")

-- An empty blank-node label ("_:" with nothing after it).
#guard isErr (parseNTriples "_: <http://example.org/p> \"o\" .\n")

-- Mode_11 rejects a triple term in object position (RDF 1.2 syntax).
#guard isErr (parseNTriples
  "<http://example.org/s> <http://example.org/p> <<( <http://example.org/a> <http://example.org/b> <http://example.org/c> )>> .\n"
  .rdf11)

-- Mode_11 rejects the retired RDF-star quoted-triple form too.
#guard isErr (parseNTriples
  "<http://example.org/s> <http://example.org/p> << <http://example.org/a> <http://example.org/b> <http://example.org/c> >> .\n"
  .rdf11)

/-! ### RDF 1.2 fixtures -/

-- A directional language-tagged literal, Mode_12.
#guard isOk (parseNTriples
  "<http://example.org/s> <http://example.org/p> \"hello\"@en--ltr .\n"
  .rdf12)

#guard isOk (parseNTriples
  "<http://example.org/s> <http://example.org/p> \"hello\"@ar--rtl .\n"
  .rdf12)

-- Uppercase direction token is rejected (only lowercase ltr/rtl).
#guard isErr (parseNTriples
  "<http://example.org/s> <http://example.org/p> \"hello\"@en--LTR .\n"
  .rdf12)

-- A triple term in object position, Mode_12.
#guard isOk (parseNTriples
  "<http://example.org/s> <http://example.org/p> <<( <http://example.org/a> <http://example.org/b> <http://example.org/c> )>> .\n"
  .rdf12)

-- Nested triple terms.
#guard isOk (parseNTriples
  "<http://example.org/s> <http://example.org/p> \
   <<( <http://example.org/a> <http://example.org/b> \
       <<( <http://example.org/x> <http://example.org/y> <http://example.org/z> )>> )>> .\n"
  .rdf12)

-- The legacy RDF-star `<< s p o >>` quoted-triple form is rejected even
-- under Mode_12 (only the `<<( )>>` triple-TERM form is RDF 1.2 syntax).
#guard isErr (parseNTriples
  "<http://example.org/s> <http://example.org/p> << <http://example.org/a> <http://example.org/b> <http://example.org/c> >> .\n"
  .rdf12)

-- A literal subject inside a triple term is rejected (triple-term subject
-- is `subject`, i.e. IRIREF | BLANK_NODE_LABEL — never a literal).
#guard isErr (parseNTriples
  "<http://example.org/s> <http://example.org/p> <<( \"lit\" <http://example.org/b> <http://example.org/c> )>> .\n"
  .rdf12)

/-! ### Serialise-then-parse round trips (N-Triples) -/

def rtCheck (mode : Mode) (g : Graph) : Bool :=
  match Graph.toNTriples g mode with
  | .error _ => false
  | .ok text =>
      match parseNTriples text mode with
      | .error _ => false
      | .ok g' => g' == g

def iri! (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

def exS : WfIri := iri! "http://example.org/s"
def exP : WfIri := iri! "http://example.org/p"
def exO : WfIri := iri! "http://example.org/o"

def rtGraphPlain : Graph :=
  [{ s := .iri exS, p := exP, o := .literal (Literal.string "hello") }]
#guard rtCheck .rdf11 rtGraphPlain

def rtGraphEscapes : Graph :=
  [{ s := .iri exS, p := exP,
     o := .literal (Literal.string "tab\tquote\"backslash\\newline\ncr\r") }]
#guard rtCheck .rdf11 rtGraphEscapes

def rtGraphLang : Graph :=
  [{ s := .iri exS, p := exP, o := .literal (Literal.langString "chat" "en-US") }]
#guard rtCheck .rdf11 rtGraphLang

def rtGraphDatatype : Graph :=
  [{ s := .iri exS, p := exP,
     o := .literal ⟨{ lexicalForm := "42", datatype := xsdInteger,
                       langTag := none, direction := none }, rfl⟩ }]
#guard rtCheck .rdf11 rtGraphDatatype

def rtGraphBnode : Graph :=
  [{ s := .bnode "b0", p := exP, o := .bnode "b1" }]
#guard rtCheck .rdf11 rtGraphBnode

def rtGraphMulti : Graph :=
  [{ s := .iri exS, p := exP, o := .literal (Literal.string "one") },
   { s := .iri exS, p := exP, o := .iri exO }]
#guard rtCheck .rdf11 rtGraphMulti

-- RDF 1.2: a directional literal round-trips only under .rdf12.
def rtGraphDir : Graph :=
  [{ s := .iri exS, p := exP,
     o := .literal ⟨{ lexicalForm := "hello", datatype := rdfDirLangString,
                       langTag := some "en", direction := some .ltr }, rfl⟩ }]
#guard rtCheck .rdf12 rtGraphDir
#guard isErr (Graph.toNTriples rtGraphDir .rdf11)

-- RDF 1.2: a triple term round-trips only under .rdf12.
def rtGraphTripleTerm : Graph :=
  [{ s := .iri exS, p := exP,
     o := .tripleTerm (.iri exS) exP (.literal (Literal.string "claimed")) }]
#guard rtCheck .rdf12 rtGraphTripleTerm
#guard isErr (Graph.toNTriples rtGraphTripleTerm .rdf11)

/-! ### N-Quads: default graph, two named graphs -/

#guard isOk (parseNQuads
  "<http://example.org/s> <http://example.org/p> \"default\" .\n\
   <http://example.org/s> <http://example.org/p> \"g1\" <http://example.org/g1> .\n\
   <http://example.org/s> <http://example.org/p> \"g2\" <http://example.org/g2> .\n\
   <http://example.org/s2> <http://example.org/p> \"g1-again\" <http://example.org/g1> .\n")

def dsCheck : Except ParseError Dataset :=
  parseNQuads
    "<http://example.org/s> <http://example.org/p> \"default\" .\n\
     <http://example.org/s> <http://example.org/p> \"g1\" <http://example.org/g1> .\n\
     <http://example.org/s> <http://example.org/p> \"g2\" <http://example.org/g2> .\n\
     <http://example.org/s2> <http://example.org/p> \"g1-again\" <http://example.org/g1> .\n"

#guard okEq (Except.map (fun ds => ds.default.length) dsCheck) 1
#guard okEq (Except.map (fun ds => ds.named.length) dsCheck) 2
-- Insertion order of named graphs is preserved (g1 first, g2 second).
#guard okEq (Except.map (fun ds => ds.named.map (·.name)) dsCheck)
  [Subject.iri (iri! "http://example.org/g1"), Subject.iri (iri! "http://example.org/g2")]
#guard okEq
  (Except.map (fun ds => (ds.lookupNamedIri "http://example.org/g1").map (·.length)) dsCheck)
  (some 2)

-- A blank-node graph label: parsed as `Subject.bnode`, NOT as an IRI
-- and NOT as a `"_:"`-prefixed string (RDF 1.1 Concepts §4).
#guard isOk (parseNQuads
  "<http://example.org/s> <http://example.org/p> \"o\" _:g .\n")
#guard okEq (Except.map (fun ds => ds.named.map (·.name)) (parseNQuads
  "<http://example.org/s> <http://example.org/p> \"o\" _:g .\n")) [Subject.bnode "g"]

-- A literal graph label is rejected.
#guard isErr (parseNQuads
  "<http://example.org/s> <http://example.org/p> \"o\" \"not-a-graph\" .\n")

-- RDF 1.2 triple term in N-Quads object position.
#guard isOk (parseNQuads
  "<http://example.org/s> <http://example.org/p> <<( <http://example.org/a> <http://example.org/b> <http://example.org/c> )>> <http://example.org/g> .\n"
  .rdf12)

/-! ### N-Quads serialise-then-parse round trip -/

def rtDsCheck (mode : Mode) (ds : Dataset) : Bool :=
  match Dataset.toNQuads ds mode with
  | .error _ => false
  | .ok text =>
      match parseNQuads text mode with
      | .error _ => false
      | .ok ds' => ds' == ds

def exG1 : WfIri := iri! "http://example.org/g1"
def exG2 : WfIri := iri! "http://example.org/g2"

def rtDataset : Dataset :=
  { default := [{ s := .iri exS, p := exP, o := .literal (Literal.string "d") }],
    named := [{ name := .iri exG1,
                graph := [{ s := .iri exS, p := exP, o := .literal (Literal.string "n1") }] },
              { name := .iri exG2,
                graph := [{ s := .iri exS, p := exP, o := .iri exO }] }] }
#guard rtDsCheck .rdf11 rtDataset

-- RDF 1.1 Concepts §4: a graph name may be a BLANK NODE. It survives
-- the serialise-then-parse round trip as `_:g`, not as an IRI.
def rtBnodeNamedDataset : Dataset :=
  { default := [],
    named := [{ name := .bnode "g",
                graph := [{ s := .iri exS, p := exP, o := .literal (Literal.string "in-g") }] }] }
#guard rtDsCheck .rdf11 rtBnodeNamedDataset
#guard (Dataset.toNQuads rtBnodeNamedDataset).toOption
  == some "<http://example.org/s> <http://example.org/p> \"in-g\" _:g .\n"

/-! ### Canonical N-Triples / N-Quads (RDF 1.2 §canonical form)

https://www.w3.org/TR/rdf12-n-triples/#canonical-ntriples. One guard per
rule the canonical form fixes, each named after the
`rdf12/rdf-n-{triples,quads}/c14n` entry whose shape it reproduces. The
fixtures are written by hand against the grammar (module header), so the
guard checks the RULE, and the W3C files themselves are read off disk by
`lake exe l4w3c` on the two c14n manifests. -/

/-- Parse in RDF 1.2 mode, then render canonically. -/
def canonOf (s : String) : Option String :=
  (parseNTriples s .rdf12).toOption.map Graph.toCanonicalNTriples

/-- Same, for a dataset. -/
def canonDsOf (s : String) : Option String :=
  (parseNQuads s .rdf12).toOption.map Dataset.toCanonicalNQuads

-- `literal_with_BACKSPACE`: the SHORTEST escape wins over `\u0008`.
#guard canonOf "<http://a.example/s> <http://a.example/p> \"\\u0008\" .\n"
  == some "<http://a.example/s> <http://a.example/p> \"\\b\" .\n"

-- `literal_with_FORM_FEED` / `_CARRIAGE_RETURN` / `_CHARACTER_TABULATION`.
#guard canonOf "<http://a.example/s> <http://a.example/p> \"\\u000C\\u000D\\u0009\" .\n"
  == some "<http://a.example/s> <http://a.example/p> \"\\f\\r\\t\" .\n"

-- `literal_all_controls`: a control with no short escape becomes an
-- UPPERCASE-hex `\u00XX`, and DEL (U+007F) is escaped too.
#guard canonOf "<http://a.example/s> <http://a.example/p> \"\\u0001\\u000B\\u001F\\u007F\" .\n"
  == some "<http://a.example/s> <http://a.example/p> \"\\u0001\\u000B\\u001F\\u007F\" .\n"

-- `literal_with_dquote` / `_REVERSE_SOLIDUS`.
#guard canonOf "<http://a.example/s> <http://a.example/p> \"a\\\"b\\\\c\" .\n"
  == some "<http://a.example/s> <http://a.example/p> \"a\\\"b\\\\c\" .\n"

-- `extra_whitespace-01` / `minimal_whitespace-01`: exactly one space
-- between terms, whatever the input spacing was.
#guard canonOf "  <http://a.example/s>\t<http://a.example/p>   <http://a.example/o>   .  \n"
  == some "<http://a.example/s> <http://a.example/p> <http://a.example/o> .\n"

-- `literal_with_string_dt`: an explicit `xsd:string` datatype is dropped.
#guard canonOf ("<http://a.example/s> <http://a.example/p> " ++
    "\"x\"^^<http://www.w3.org/2001/XMLSchema#string> .\n")
  == some "<http://a.example/s> <http://a.example/p> \"x\" .\n"

-- `langtagged_string`: the language tag is lowercased.
#guard canonOf "<http://a.example/s> <http://a.example/p> \"chat\"@EN-UK .\n"
  == some "<http://a.example/s> <http://a.example/p> \"chat\"@en-uk .\n"

-- `dirlangtagged_string`: lowercased tag, base direction kept.
#guard canonOf "<http://a.example/s> <http://a.example/p> \"chat\"@EN--ltr .\n"
  == some "<http://a.example/s> <http://a.example/p> \"chat\"@en--ltr .\n"

-- `triple-term-01`: `<<( s p o )>>` with one space inside each delimiter.
#guard canonOf ("<http://a.example/s> <http://a.example/p> " ++
    "<<(<http://a.example/s2> <http://a.example/p2> \"o2\")>> .\n")
  == some ("<http://a.example/s> <http://a.example/p> " ++
    "<<( <http://a.example/s2> <http://a.example/p2> \"o2\" )>> .\n")

-- Blank-node labels and statement ORDER survive: canonical
-- SERIALISATION, not RDFC-1.0 relabelling.
#guard canonOf ("_:b1 <http://a.example/p> \"2\" .\n_:b0 <http://a.example/p> \"1\" .\n")
  == some ("_:b1 <http://a.example/p> \"2\" .\n_:b0 <http://a.example/p> \"1\" .\n")

-- N-Quads: the graph slot follows the object, same term rules.
#guard canonDsOf ("<http://a.example/s>  <http://a.example/p>  \"chat\"@EN " ++
    "<http://a.example/g> .\n")
  == some "<http://a.example/s> <http://a.example/p> \"chat\"@en <http://a.example/g> .\n"

end L4Factoidal.Syntax.SyntaxTests
