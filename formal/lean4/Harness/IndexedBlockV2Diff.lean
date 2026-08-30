/- Executable differential gate for the segmented IBK2 codec. -/
import L4Factoidal.Storage.IndexedBlockWireV2
import L4Factoidal.Syntax.Turtle
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.StoreDataset

namespace Harness.IndexedBlockV2Diff

open L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.Syntax
open L4Factoidal.Storage.IndexedBlock L4Factoidal.Storage.IndexedBlockWireV2
open L4Factoidal.SPARQL.StoreDataset

private def listDataset (graph : Graph) : DatasetBackend := { default := .list graph, named := [] }
private def indexedDataset (block : Block) : DatasetBackend := { default := .hdt (readOps block), named := [] }

private def check (path queryText : String) (graph : Graph) : IO UInt32 := do
  match parseSparql queryText with
  | .error e => IO.eprintln s!"l4block-id-v2-diff query parse error at {e.pos}: {e.msg}"; return 1
  | .ok q =>
      let expected := runSelectQueryBackendDataset emptyEnv q (listDataset graph)
      let source := fromGraph graph
      match encode? source with
      | none => IO.eprintln "l4block-id-v2-diff refused: unsupported RDF term or ID"; return 1
      | some bytes =>
          match decode bytes with
          | none => IO.eprintln "l4block-id-v2-diff failed: IBK2 did not decode its own bytes"; return 1
          | some decoded =>
              let actual := runSelectQueryBackendDataset emptyEnv q (indexedDataset decoded)
              if expected == actual then
                IO.println s!"l4block-id-v2-diff pass path={path} triples={graph.length} bytes={bytes.size} segments={source.byPredicate.toList.length} rows={(actual.getD []).length}"
                IO.println s!"l4block-id-v2-diff sse={q.toSse}"
                return 0
              else IO.eprintln s!"l4block-id-v2-diff mismatch expected={repr expected} actual={repr actual}"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | path :: "--query" :: queryParts =>
      if queryParts.isEmpty then IO.eprintln "l4block-id-v2-diff requires a query after --query"; return 2
      else try
        let text ← IO.FS.readFile path
        match parseTurtle text (some ("file://" ++ path)) with
        | .error e => IO.eprintln s!"l4block-id-v2-diff Turtle parse error at {e.pos}: {e.msg}"; return 1
        | .ok graph => check path (String.intercalate " " queryParts) graph
      catch e => IO.eprintln s!"l4block-id-v2-diff read failure: {e}"; return 1
  | _ => IO.eprintln "usage: l4block-id-v2-diff INPUT.ttl --query SELECT..."; return 2

end Harness.IndexedBlockV2Diff

def main (args : List String) : IO UInt32 := Harness.IndexedBlockV2Diff.main args
