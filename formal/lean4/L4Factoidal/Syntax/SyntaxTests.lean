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
-/

import L4Factoidal.Syntax.NQuads

namespace L4Factoidal.Syntax.SyntaxTests

open L4Factoidal.RDF L4Factoidal.Syntax

/-! ### Positive N-Triples fixtures (RDF 1.1) -/

-- nt-syntax-file-01-style: a single plain-literal triple.
#guard (parseNTriples "<http://example.org/s> <http://example.org/p> \"o\" .\n").isOk

-- nt-syntax-uri-04-style: an IRI object.
#guard (parseNTriples
  "<http://example.org/s> <http://example.org/p> <http://example.org/o> .\n").isOk

-- nt-syntax-bnode-01-style: blank-node subject and object.
#guard (parseNTriples
  "_:a <http://example.org/p> _:b .\n").isOk

-- nt-syntax-str-esc-01-style: every ECHAR plus a UCHAR.
#guard (parseNTriples
  "<http://example.org/s> <http://example.org/p> \"tab:\\t nl:\\n cr:\\r bs:\\\\ q:\\\" u:\\u00E9\" .\n").isOk

-- nt-syntax-string-with-lang: language-tagged literal.
#guard (parseNTriples
  "<http://example.org/s> <http://example.org/p> \"chat\"@en .\n").isOk

-- BCP47 subtag language tag.
#guard (parseNTriples
  "<http://example.org/s> <http://example.org/p> \"chat\"@en-US .\n").isOk

-- nt-syntax-datatypes-01-style: a datatyped literal.
#guard (parseNTriples
  "<http://example.org/s> <http://example.org/p> \"42\"^^<http://www.w3.org/2001/XMLSchema#integer> .\n").isOk

-- nt-syntax-bnode-with-digits: a blank-node label starting with a digit
-- (BLANK_NODE_LABEL start char is PN_CHARS_U | [0-9]).
#guard (parseNTriples "_:0a <http://example.org/p> _:1 .\n").isOk

-- nt-syntax-bnode-with-internal-dot: an internal dot is legal; the label
-- is `a.b`, not truncated at the dot.
#guard (parseNTriples "_:a.b <http://example.org/p> _:c .\n").isOk

-- nt-syntax-comment-01-style: comment lines and blank lines are skipped.
#guard (parseNTriples
  "# a comment\n\n<http://example.org/s> <http://example.org/p> \"o\" .\n# trailing\n").isOk

-- Multiple triples, one per line.
#guard ((parseNTriples
  "<http://example.org/s> <http://example.org/p> \"1\" .\n\
   <http://example.org/s> <http://example.org/p> \"2\" .\n").map (·.length)) == .ok 2

/-! ### Negative N-Triples fixtures (RDF 1.1) -/

-- nt-syntax-bad-uri-04-style: a raw space inside an IRIREF.
#guard (parseNTriples "<http://example.org/s p> <http://example.org/p> \"o\" .\n").isError

-- nt-syntax-bad-string-04-style: an unescaped raw newline inside a string.
#guard (parseNTriples "<http://example.org/s> <http://example.org/p> \"o\no\" .\n").isError

-- nt-syntax-bad-esc-01-style: an unknown escape.
#guard (parseNTriples "<http://example.org/s> <http://example.org/p> \"\\q\" .\n").isError

-- Missing terminating '.'.
#guard (parseNTriples "<http://example.org/s> <http://example.org/p> \"o\"\n").isError

-- A literal used as the subject is not legal.
#guard (parseNTriples "\"s\" <http://example.org/p> \"o\" .\n").isError

-- A surrogate codepoint in a \u escape is rejected, not silently replaced.
#guard (parseNTriples "<http://example.org/s> <http://example.org/p> \"\\uD800\" .\n").isError

-- An empty blank-node label ("_:" with nothing after it).
#guard (parseNTriples "_: <http://example.org/p> \"o\" .\n").isError

-- Mode_11 rejects a triple term in object position (RDF 1.2 syntax).
#guard (parseNTriples
  "<http://example.org/s> <http://example.org/p> <<( <http://example.org/a> <http://example.org/b> <http://example.org/c> )>> .\n"
  (mode := .rdf11)).isError

-- Mode_11 rejects the retired RDF-star quoted-triple form too.
#guard (parseNTriples
  "<http://example.org/s> <http://example.org/p> << <http://example.org/a> <http://example.org/b> <http://example.org/c> >> .\n"
  (mode := .rdf11)).isError

/-! ### RDF 1.2 fixtures -/

-- A directional language-tagged literal, Mode_12.
#guard (parseNTriples
  "<http://example.org/s> <http://example.org/p> \"hello\"@en--ltr .\n"
  (mode := .rdf12)).isOk

#guard (parseNTriples
  "<http://example.org/s> <http://example.org/p> \"hello\"@ar--rtl .\n"
  (mode := .rdf12)).isOk

-- Uppercase direction token is rejected (only lowercase ltr/rtl).
#guard (parseNTriples
  "<http://example.org/s> <http://example.org/p> \"hello\"@en--LTR .\n"
  (mode := .rdf12)).isError

-- A triple term in object position, Mode_12.
#guard (parseNTriples
  "<http://example.org/s> <http://example.org/p> <<( <http://example.org/a> <http://example.org/b> <http://example.org/c> )>> .\n"
  (mode := .rdf12)).isOk

-- Nested triple terms.
#guard (parseNTriples
  "<http://example.org/s> <http://example.org/p> \
   <<( <http://example.org/a> <http://example.org/b> \
       <<( <http://example.org/x> <http://example.org/y> <http://example.org/z> )>> )>> .\n"
  (mode := .rdf12)).isOk

-- The legacy RDF-star `<< s p o >>` quoted-triple form is rejected even
-- under Mode_12 (only the `<<( )>>` triple-TERM form is RDF 1.2 syntax).
#guard (parseNTriples
  "<http://example.org/s> <http://example.org/p> << <http://example.org/a> <http://example.org/b> <http://example.org/c> >> .\n"
  (mode := .rdf12)).isError

-- A literal subject inside a triple term is rejected (triple-term subject
-- is `subject`, i.e. IRIREF | BLANK_NODE_LABEL — never a literal).
#guard (parseNTriples
  "<http://example.org/s> <http://example.org/p> <<( \"lit\" <http://example.org/b> <http://example.org/c> )>> .\n"
  (mode := .rdf12)).isError

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
#guard (Graph.toNTriples rtGraphDir .rdf11).isError

-- RDF 1.2: a triple term round-trips only under .rdf12.
def rtGraphTripleTerm : Graph :=
  [{ s := .iri exS, p := exP,
     o := .tripleTerm (.iri exS) exP (.literal (Literal.string "claimed")) }]
#guard rtCheck .rdf12 rtGraphTripleTerm
#guard (Graph.toNTriples rtGraphTripleTerm .rdf11).isError

/-! ### N-Quads: default graph, two named graphs -/

#guard (parseNQuads
  "<http://example.org/s> <http://example.org/p> \"default\" .\n\
   <http://example.org/s> <http://example.org/p> \"g1\" <http://example.org/g1> .\n\
   <http://example.org/s> <http://example.org/p> \"g2\" <http://example.org/g2> .\n\
   <http://example.org/s2> <http://example.org/p> \"g1-again\" <http://example.org/g1> .\n").isOk

def dsCheck : Except ParseError Dataset :=
  parseNQuads
    "<http://example.org/s> <http://example.org/p> \"default\" .\n\
     <http://example.org/s> <http://example.org/p> \"g1\" <http://example.org/g1> .\n\
     <http://example.org/s> <http://example.org/p> \"g2\" <http://example.org/g2> .\n\
     <http://example.org/s2> <http://example.org/p> \"g1-again\" <http://example.org/g1> .\n"

#guard (dsCheck.map (·.default.length)) == .ok 1
#guard (dsCheck.map (·.named.length)) == .ok 2
-- Insertion order of named graphs is preserved (g1 first, g2 second).
#guard (dsCheck.map (fun ds => ds.named.map (·.name))) ==
  .ok ["http://example.org/g1", "http://example.org/g2"]
#guard (dsCheck.map (fun ds => (ds.lookupNamed "http://example.org/g1").map (·.length))) ==
  .ok (some 2)

-- A blank-node graph label.
#guard (parseNQuads
  "<http://example.org/s> <http://example.org/p> \"o\" _:g .\n").isOk

-- A literal graph label is rejected.
#guard (parseNQuads
  "<http://example.org/s> <http://example.org/p> \"o\" \"not-a-graph\" .\n").isError

-- RDF 1.2 triple term in N-Quads object position.
#guard (parseNQuads
  "<http://example.org/s> <http://example.org/p> <<( <http://example.org/a> <http://example.org/b> <http://example.org/c> )>> <http://example.org/g> .\n"
  (mode := .rdf12)).isOk

/-! ### N-Quads serialise-then-parse round trip -/

def rtDsCheck (mode : Mode) (ds : Dataset) : Bool :=
  match Dataset.toNQuads ds mode with
  | .error _ => false
  | .ok text =>
      match parseNQuads text mode with
      | .error _ => false
      | .ok ds' => ds'.default == ds.default && ds'.named == ds.named

def rtDataset : Dataset :=
  { default := [{ s := .iri exS, p := exP, o := .literal (Literal.string "d") }],
    named := [{ name := "http://example.org/g1",
                graph := [{ s := .iri exS, p := exP, o := .literal (Literal.string "n1") }] },
              { name := "http://example.org/g2",
                graph := [{ s := .iri exS, p := exP, o := .iri exO }] }] }
#guard rtDsCheck .rdf11 rtDataset

end L4Factoidal.Syntax.SyntaxTests
