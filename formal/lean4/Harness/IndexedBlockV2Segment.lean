/- Predicate-segment differential probe: source graph versus IBK2 selected scan. -/
import L4Factoidal.Storage.IndexedBlockWireV2
import L4Factoidal.Syntax.Turtle

namespace Harness.IndexedBlockV2Segment

open L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.Syntax
open L4Factoidal.Storage.IndexedBlock L4Factoidal.Storage.IndexedBlockWireV2

private def predicate? (text : String) : Option WfIri :=
  if h : isIri text then some ⟨text, h⟩ else none

private def check (path iri : String) (graph : Graph) : IO UInt32 :=
  match predicate? iri with
  | none => do
      IO.eprintln s!"l4block-id-v2-segment invalid predicate IRI: {iri}"
      return 2
  | some predicate =>
      let bound : PatternBound := { p := some predicate }
      let source := fromGraph graph
      match encode? source with
      | none => do
          IO.eprintln "l4block-id-v2-segment refused: unsupported RDF term or ID"
          return 1
      | some bytes =>
          let expected := tripleMatchesBound bound graph
          let actual := scanPredicateDecoded bound bytes
          if expected == actual then do
            IO.println s!"l4block-id-v2-segment pass path={path} triples={graph.length} bytes={bytes.size} segments={source.byPredicate.toList.length} selected-triples={actual.length}"
            return 0
          else do
            IO.eprintln s!"l4block-id-v2-segment mismatch expected={repr expected} actual={repr actual}"
            return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [path, iri] => try
      let text ← IO.FS.readFile path
      match parseTurtle text (some ("file://" ++ path)) with
      | .error e => IO.eprintln s!"l4block-id-v2-segment Turtle parse error at {e.pos}: {e.msg}"; return 1
      | .ok graph => check path iri graph
    catch e => IO.eprintln s!"l4block-id-v2-segment read failure: {e}"; return 1
  | _ => IO.eprintln "usage: l4block-id-v2-segment INPUT.ttl PREDICATE-IRI"; return 2

end Harness.IndexedBlockV2Segment

def main (args : List String) : IO UInt32 := Harness.IndexedBlockV2Segment.main args
