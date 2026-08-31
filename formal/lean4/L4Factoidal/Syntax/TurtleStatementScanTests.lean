/- Build-time checks for chunk-stable Turtle dotted-candidate scanning. -/
import L4Factoidal.Syntax.TurtleStatementScan

namespace L4Factoidal.Syntax

def scanChunks (chunks : List String) : StatementScan :=
  chunks.foldl StatementScan.feed StatementScan.init

def candidates (chunks : List String) : List String :=
  (scanChunks chunks).completed

/- IRIREF and comment dots are not candidates; the final statement dot is. -/
#guard candidates ["<http://example.org/a.b> <http://example.org/p> <http://example.org/o> .\n# c.d\n"] ==
  ["<http://example.org/a.b> <http://example.org/p> <http://example.org/o> ."]

/- The dot / whitespace boundary can cross byte-decoded string chunks. -/
#guard candidates ["<s> <p> <o> .", "\n<s2> <p> <o> .\n"] ==
  ["<s> <p> <o> .", "\n<s2> <p> <o> ."]

/- Short and long strings may contain dots and line breaks. -/
#guard candidates ["<s> <p> \"a. b\" .\n", "<s2> <p> \"\"\"a.\nb\"\"\" .\n"] ==
  ["<s> <p> \"a. b\" .", "\n<s2> <p> \"\"\"a.\nb\"\"\" ."]

/- A decimal's internal dot is left to the grammar; only its later terminal
dot becomes a candidate. -/
#guard candidates ["<s> <p> 1.0 .\n"] == ["<s> <p> 1.0 ."]

/- Standard no-dot SPARQL-style directives are candidates only at a
normal-mode line boundary, not because every newline is split. -/
#guard candidates ["PREFIX ex: <http://example.org/>\n", "ex:s ex:p ex:o .\n"] ==
  ["PREFIX ex: <http://example.org/>", "\nex:s ex:p ex:o ."]

end L4Factoidal.Syntax
