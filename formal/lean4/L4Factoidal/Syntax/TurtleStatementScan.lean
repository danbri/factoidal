/-
L4Factoidal.Syntax.TurtleStatementScan — chunk-stable Turtle statement
candidate scanner.

This is deliberately below the Turtle grammar and above byte decoding. It
only finds `.` candidates that occur outside IRIREFs, comments and short/long
strings; `readStatement` remains the authority that validates a candidate.
In particular, it does not split lines, interpret prefixes, or claim that a
dot is a statement terminator until the grammar layer accepts it.
-/

namespace L4Factoidal.Syntax

/-- Lexical contexts in which a dot cannot terminate a Turtle statement. -/
inductive ScanMode where
  | normal
  | iri
  | comment
  | openingQuote (quote : Char) (count : Nat)
  | shortString (quote : Char) (escaped : Bool)
  | longString (quote : Char) (escaped : Bool) (closing : Nat)
deriving Repr, BEq

/-- A completed dotted candidate plus the uncommitted suffix. The candidates
    retain their original source order. -/
structure StatementScan where
  mode : ScanMode := .normal
  /-- The last current character was a `.` in normal mode. Its following
      character determines whether it is worth offering to `readStatement`. -/
  pendingDot : Bool := false
  /-- Current characters in reverse order, including whitespace following a
      previous candidate. -/
  currentRev : List Char := []
  /-- Completed candidate strings in reverse source order. -/
  completedRev : List String := []

def StatementScan.init : StatementScan := {}

private def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

private def dropWs : List Char → List Char
  | c :: cs => if isWs c then dropWs cs else c :: cs
  | [] => []

private def startsCi : List Char → List Char → Bool
  | [], _ => true
  | a :: as, b :: bs => a.toLower == b.toLower && startsCi as bs
  | _, _ => false

/-- The three SPARQL-style Turtle directives omit the terminating dot. Their
    ordinary layout is one directive per line, which gives the scanner a safe
    candidate boundary without treating arbitrary newlines as statement ends.
    The Turtle grammar still validates their full syntax and IRI. -/
private def beginsNoDotDirective (currentRev : List Char) : Bool :=
  let chars := dropWs currentRev.reverse
  startsCi "PREFIX".toList chars || startsCi "BASE".toList chars || startsCi "VERSION".toList chars

private def append (scan : StatementScan) (c : Char) : StatementScan :=
  { scan with currentRev := c :: scan.currentRev }

private def beginNext (scan : StatementScan) (c : Char) : StatementScan :=
  { scan with
    pendingDot := false
    currentRev := [c]
    completedRev := String.ofList scan.currentRev.reverse :: scan.completedRev }

private def stepMode (mode : ScanMode) (c : Char) : ScanMode :=
  match mode with
  | .normal =>
      if c == '<' then .iri
      else if c == '#' then .comment
      else if c == '"' || c == '\'' then .openingQuote c 1
      else .normal
  | .iri => if c == '>' then .normal else .iri
  | .comment => if c == '\n' || c == '\r' then .normal else .comment
  | .openingQuote quote 1 =>
      if c == quote then .openingQuote quote 2
      else if c == '\\' then .shortString quote true
      else .shortString quote false
  | .openingQuote quote _ =>
      if c == quote then .longString quote false 0 else .normal
  | .shortString quote escaped =>
      if escaped then .shortString quote false
      else if c == '\\' then .shortString quote true
      else if c == quote then .normal
      else .shortString quote false
  | .longString quote escaped closing =>
      if escaped then .longString quote false 0
      else if c == '\\' then .longString quote true 0
      else if c == quote then
        if closing + 1 == 3 then .normal else .longString quote false (closing + 1)
      else .longString quote false 0

/-- Feed one decoded character. A candidate is completed only when a dot in
    normal mode is followed by whitespace or a comment introducer. Numeric and
    prefixed-name dots merely clear `pendingDot`; the grammar validates every
    completed candidate before it can affect Turtle state. -/
def StatementScan.feedChar (scan : StatementScan) (c : Char) : StatementScan :=
  if scan.pendingDot && (isWs c || c == '#') then
    let next := beginNext scan c
    { next with mode := stepMode .normal c }
  else if scan.mode == .normal && !scan.pendingDot && (c == '\n' || c == '\r') &&
      beginsNoDotDirective scan.currentRev then
    beginNext scan c
  else
    let mode := stepMode scan.mode c
    let next := (append scan c)
    { next with mode, pendingDot := mode == .normal && c == '.' }

def StatementScan.feedChars (scan : StatementScan) : List Char → StatementScan
  | [] => scan
  | c :: cs => feedChars (scan.feedChar c) cs

/-- Feed a decoded string chunk. -/
def StatementScan.feed (scan : StatementScan) (chunk : String) : StatementScan :=
  scan.feedChars chunk.toList

/-- Completed candidates in source order. The final suffix is intentionally
    not emitted: callers must let the grammar decide whether its final dot (or
    a SPARQL-style directive without a dot) forms a complete statement. -/
def StatementScan.completed (scan : StatementScan) : List String := scan.completedRev.reverse

/-- Return currently completed candidates in source order and clear just that
    queue. A streaming parser drains this after each decoded input chunk, so
    it retains only the current unfinished statement rather than all earlier
    statements. -/
def StatementScan.drain (scan : StatementScan) : List String × StatementScan :=
  (scan.completed, { scan with completedRev := [] })

/-- Current uncommitted decoded text. -/
def StatementScan.remainder (scan : StatementScan) : String := String.ofList scan.currentRev.reverse

end L4Factoidal.Syntax
