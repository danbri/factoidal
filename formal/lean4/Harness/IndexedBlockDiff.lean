/-
Harness.IndexedBlockDiff — differential gate for direct ID block execution.

For one Turtle graph and parsed SELECT, compare the existing list-backed
dataset path with `IndexedBlockWireV1.encode?/decode` plus the indexed backend.
This is an executable regression gate, not a substitute for the general codec
theorem.
-/
import L4Factoidal.Storage.IndexedBlockWireV1
import L4Factoidal.Syntax.Turtle
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.StoreDataset

namespace Harness.IndexedBlockDiff

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Syntax
open L4Factoidal.Storage.IndexedBlock
open L4Factoidal.Storage.IndexedBlockWireV1
open L4Factoidal.SPARQL.StoreDataset

private def listDataset (graph : Graph) : DatasetBackend :=
  { default := .list graph, named := [] }

private def indexedDataset (block : Block) : DatasetBackend :=
  { default := .hdt (readOps block), named := [] }

private def check (path queryText : String) (graph : Graph) : IO UInt32 := do
  match parseSparql queryText with
  | .error e =>
      IO.eprintln s!"l4block-id-diff query parse error at {e.pos}: {e.msg}"
      return 1
  | .ok q =>
      let expected := runSelectQueryBackendDataset emptyEnv q (listDataset graph)
      let sourceBlock := fromGraph graph
      match encode? sourceBlock with
      | none =>
          IO.eprintln "l4block-id-diff refused: V1 does not support one or more RDF terms or IDs"
          return 1
      | some bytes =>
          match decode bytes with
          | none =>
              IO.eprintln "l4block-id-diff failed: V1 did not decode its own bytes"
              return 1
          | some decoded =>
              let actual := runSelectQueryBackendDataset emptyEnv q (indexedDataset decoded)
              if expected == actual then
                IO.println s!"l4block-id-diff pass path={path} triples={graph.length} bytes={bytes.size} rows={(actual.getD []).length}"
                IO.println s!"l4block-id-diff sse={q.toSse}"
                return 0
              else
                IO.eprintln s!"l4block-id-diff mismatch expected={repr expected} actual={repr actual}"
                return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | path :: "--query" :: queryParts =>
      if queryParts.isEmpty then
        IO.eprintln "l4block-id-diff requires a query after --query"
        return 2
      else try
        let text ← IO.FS.readFile path
        match parseTurtle text (some ("file://" ++ path)) with
        | .error e =>
            IO.eprintln s!"l4block-id-diff Turtle parse error at {e.pos}: {e.msg}"
            return 1
        | .ok graph => check path (String.intercalate " " queryParts) graph
      catch e =>
        IO.eprintln s!"l4block-id-diff read failure: {e}"
        return 1
  | _ =>
      IO.eprintln "usage: l4block-id-diff INPUT.ttl --query SELECT..."
      return 2

end Harness.IndexedBlockDiff

def main (args : List String) : IO UInt32 := Harness.IndexedBlockDiff.main args
