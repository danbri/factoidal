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

/- A decimal dot and dots within a prefixed IRI must not become separate
statements when their following chunks arrive. -/
private def dotted : String :=
  "@prefix ex: <http://example.org/a.b/> .\nex:s ex:p 1.0 .\n"
#guard chunksMatchParser dotted ["@prefix ex: <http://example.org/a", ".b/> .\nex:s ex:p 1.", "0 .\n"]

end L4Factoidal.Syntax
