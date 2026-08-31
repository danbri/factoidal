/-
L4Factoidal.Syntax.TurtleChunkFold — grammar-validated Turtle event folding
over decoded input chunks.

`TurtleStatementScan` supplies only lexical candidate boundaries. Every
candidate is then parsed by the landed `readStatement` implementation, so
prefix/base state, RDF version and generated blank-node state stay identical
to the ordinary Turtle parser. The caller supplies the already-established
collision-free blank-node prefix; a file loader obtains it during its bounded
pre-pass.
-/
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.TurtleStatementScan

namespace L4Factoidal.Syntax

open L4Factoidal.RDF

/-- State retained by a decoded-chunk Turtle fold. Completed statements are
    folded immediately; `scanner` holds only the current unfinished lexical
    segment. -/
structure TurtleChunkFoldState (α : Type) where
  turtle : TurtleState
  acc : α
  pos : Nat := 0
  scanner : StatementScan := StatementScan.init

private def consumeText (step : α → List RDF.Triple → α) :
    Nat → TurtleState → α → Nat → List Char → Except ParseError (TurtleState × α × Nat)
  | 0, _turtle, _acc, pos, _ => .error ⟨"Turtle statement fuel exhausted", pos⟩
  | fuel + 1, turtle, acc, pos, chars =>
      let (p1, r1) := tws pos chars
      match r1 with
      | [] => .ok (turtle, acc, p1)
      | _ =>
          match readStatement (r1.length + 2) turtle p1 r1 with
          | .error error => .error error
          | .ok (triples, nextTurtle, p2, r2) =>
              if p2 ≤ p1 then .error ⟨"Turtle statement made no progress", p1⟩
              else consumeText step fuel nextTurtle (step acc triples) p2 r2

private def consumeCandidates (step : α → List RDF.Triple → α) :
    TurtleState → α → Nat → List String → Except ParseError (TurtleState × α × Nat)
  | turtle, acc, pos, [] => .ok (turtle, acc, pos)
  | turtle, acc, pos, text :: texts =>
      match consumeText step (text.toList.length + 2) turtle acc pos text.toList with
      | .error error => .error error
      | .ok (nextTurtle, nextAcc, nextPos) =>
          consumeCandidates step nextTurtle nextAcc nextPos texts

/-- Begin a chunk fold after a pre-pass has supplied the generated blank-node
    prefix. -/
def TurtleChunkFoldState.init (bnodePrefix : String) (_step : α → List RDF.Triple → α) (acc : α)
    (base : Option String := none) (mode : Mode := .rdf11) : TurtleChunkFoldState α :=
  { turtle := TurtleState.initWithBnodePrefix bnodePrefix base mode, acc }

/-- Feed one decoded UTF-8 chunk. Candidates are drained and grammar-validated
    immediately rather than retained for the whole document. -/
def TurtleChunkFoldState.feed (step : α → List RDF.Triple → α) (state : TurtleChunkFoldState α)
    (chunk : String) : Except ParseError (TurtleChunkFoldState α) :=
  let scanned := state.scanner.feed chunk
  let (candidates, scanner) := scanned.drain
  match consumeCandidates step state.turtle state.acc state.pos candidates with
  | .error error => .error error
  | .ok (turtle, acc, pos) => .ok { turtle, acc, pos, scanner }

/-- Finish a chunk fold. The final suffix is submitted to the same grammar
    path, covering a terminal dot with no trailing whitespace and a final
    no-dot SPARQL-style directive. -/
def TurtleChunkFoldState.finish (step : α → List RDF.Triple → α) (state : TurtleChunkFoldState α) :
    Except ParseError α :=
  match consumeText step (state.scanner.remainder.toList.length + 2)
      state.turtle state.acc state.pos state.scanner.remainder.toList with
  | .error error => .error error
  | .ok (_, acc, _) => .ok acc

/-- Fold complete decoded chunks using an externally precomputed blank-node
    prefix. The result is independent of chunk boundaries for valid Turtle
    whose statement candidates the scanner exposes. -/
def parseTurtleChunksFold (bnodePrefix : String) (step : α → List RDF.Triple → α) (init : α)
    (chunks : List String) (base : Option String := none) (mode : Mode := .rdf11) :
    Except ParseError α :=
  let initial : Except ParseError (TurtleChunkFoldState α) :=
    .ok (TurtleChunkFoldState.init bnodePrefix step init base mode)
  match chunks.foldl (fun result chunk => do
      let state ← result
      TurtleChunkFoldState.feed step state chunk) initial with
  | .error error => .error error
  | .ok state => state.finish step

end L4Factoidal.Syntax
