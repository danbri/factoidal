/- Build-time equivalence checks for grammar-validated decoded Turtle chunks. -/
import L4Factoidal.Syntax.TurtleChunkFold

namespace L4Factoidal.Syntax

open L4Factoidal.RDF

def chunkGraph (source : String) (chunks : List String) : Except ParseError Graph := do
  let reversed ← parseTurtleChunksFold (freshBnodePrefix source)
    (fun accRev triples => triples.reverse ++ accRev) [] chunks
  pure reversed.reverse

def chunksMatchParser (source : String) (chunks : List String) : Bool :=
  match chunkGraph source chunks, parseTurtle source with
  | .ok chunked, .ok ordinary => chunked == ordinary
  | .error _, .error _ => true
  | _, _ => false

def charChunks (source : String) : List String := source.toList.map String.singleton

private def basic : String :=
  "@prefix ex: <http://example.org/> .\nex:s ex:p ex:o .\n"
#guard chunksMatchParser basic ["@prefix ex: <http://exa", "mple.org/> .\nex:s ex:p ex:o .", "\n"]

/- The scanner must carry all of these lexical states across chunk cuts; only
`readStatement` establishes the actual Turtle meaning. -/
private def lexical : String :=
  "PREFIX ex: <http://example.org/>\nex:s ex:p \"\"\"dot.\nand []\"\"\" .\n[] ex:p ex:o .\n"
#guard chunksMatchParser lexical [
  "PREFIX ex: <http://example.org/>", "\nex:s ex:p \"\"", "\"dot.\n",
  "and []\"\"\" .\n[", "] ex:p ex:o .\n"]
#guard chunksMatchParser lexical (charChunks lexical)

/- A decimal dot and dots within a prefixed IRI must not become separate
statements when their following chunks arrive. -/
private def dotted : String :=
  "@prefix ex: <http://example.org/a.b/> .\nex:s ex:p 1.0 .\n"
#guard chunksMatchParser dotted ["@prefix ex: <http://example.org/a", ".b/> .\nex:s ex:p 1.", "0 .\n"]


/-! ## Comments and the no-dot directives (owner question, 2026-09-03)

The scanner's directive test reads the first seven characters of the
current candidate after leading whitespace. When a comment precedes a
`PREFIX`/`BASE` line inside the same candidate, the test sees `# ...` and
does not cut at that line end; the directive then stays in the candidate
until the next dot or the end of input. That is safe because a candidate
may hold several statements and `consumeText` runs the grammar in a loop
over it; the test only decides where boundaries fall, never what the text
means. Every two-way split of each source below, plus one-character chunks,
agrees with `parseTurtle` (1,115 chunkings on 2026-09-03). -/

private def allSplits (source : String) : List (List String) :=
  let cs := source.toList
  (List.range (cs.length + 1)).map
    (fun i => [String.ofList (cs.take i), String.ofList (cs.drop i)]) ++ [charChunks source]

private def allSplitsMatch (source : String) : Bool :=
  (allSplits source).all (chunksMatchParser source)

#guard allSplitsMatch "# leading comment\nPREFIX ex: <http://example.org/>\nex:s ex:p ex:o .\n"
#guard allSplitsMatch "PREFIX ex: <http://example.org/>\n# note\nPREFIX ex2: <http://example.org/2/>\nex:s ex:p ex2:o .\n"
#guard allSplitsMatch "# PREFIX not: <http://nope/>\nPREFIX ex: <http://example.org/>\nex:s ex:p ex:o .\n"
#guard allSplitsMatch "PREFIX ex: <http://example.org/>\nex:s ex:p ex:o . # trailing\nBASE <http://base.example/>\n<rel> ex:p ex:o .\n"
#guard allSplitsMatch "\n\n  # c\n   prefix ex: <http://example.org/>\nex:s ex:p ex:o .\n"
#guard allSplitsMatch "PREFIX ex: <http://example.org/>\nex:s ex:p \"\"\"line one\nPREFIX fake: <http://x/>\nline three\"\"\" .\n"
#guard allSplitsMatch "PREFIX ex: <http://example.org/>\nex:s ex:p \"PREFIX ex: <http://x/>\" .\n"
#guard allSplitsMatch "PREFIX ex: <http://example.org/>\nex:s ex:p <http://example.org/doc#PREFIX> .\n"
#guard allSplitsMatch "<http://example.org/s> <http://example.org/p> <http://example.org/o> .\nPREFIX ex: <http://example.org/>"
#guard allSplitsMatch "PREFIX a: <http://a/>\nPREFIX b: <http://b/>\n"
#guard allSplitsMatch "PREFIX ex: <http://example.org/> ex:s ex:p ex:o .\n"
#guard allSplitsMatch "# c\n@prefix ex: <http://example.org/> .\nex:s ex:p ex:o .\n"
#guard allSplitsMatch "# c\r\nPREFIX ex: <http://example.org/>\r\nex:s ex:p ex:o .\r\n"
#guard allSplitsMatch "PREFIX ex: <http://example.org/>\nex:s ex:p ex:o ;\n   ex:q ex:PREFIXED .\n"


/- Dots inside comments are not candidate boundaries: `pendingDot` is set only
when the mode after the character is `normal`, and a comment keeps mode
`comment` until its line end. The directive after such a comment is
therefore deferred past the comment's dots too. -/
#guard allSplitsMatch "# comment with a dot. and more text\nPREFIX ex: <http://example.org/>\nex:s ex:p ex:o .\n"
#guard allSplitsMatch "# note.\nPREFIX ex: <http://example.org/>\nex:s ex:p ex:o .\n"
#guard allSplitsMatch "PREFIX ex: <http://example.org/>\nex:s ex:p ex:o . # ends with a dot.\nex:s ex:q ex:o .\n"
#guard allSplitsMatch "PREFIX ex: <http://example.org/>\nex:s ex:p ex:o ; # mid-statement comment.\n  ex:q ex:o .\n"

end L4Factoidal.Syntax
