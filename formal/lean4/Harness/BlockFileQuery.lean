/-
Harness.BlockFileQuery — query one framed block file without Turtle parsing.

The file reader validates BLK0 before forming an `IndexedBlock`; parsed SELECT
evaluation then receives the indexed backend through the established dataset
seam. This gives the present MVP a durable file-to-query vertical while the
canonical TermId byte format is still being designed.
-/
import L4Factoidal.Storage.BlockWireV0
import L4Factoidal.Storage.IndexedBlock
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.StoreDataset

namespace Harness.BlockFileQuery

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.BlockWireV0
open L4Factoidal.Storage.IndexedBlock
open L4Factoidal.SPARQL.StoreDataset

private def run (path queryText : String) : IO UInt32 := do
  try
    let bytes ← IO.FS.readBinFile path
    match decode bytes with
    | none =>
        IO.eprintln "l4block-file-query rejected: malformed or unsupported BLK0 file"
        return 1
    | some directBlock =>
        let block := fromGraph directBlock.rows
        let dataset : DatasetBackend := { default := .hdt (readOps block), named := [] }
        match parseSparql queryText with
        | .error e =>
            IO.eprintln s!"l4block-file-query query parse error at {e.pos}: {e.msg}"
            return 1
        | .ok q =>
            match runSelectQueryBackendDataset emptyEnv q dataset with
            | none =>
                IO.eprintln "l4block-file-query failed: query was not evaluated as SELECT"
                return 1
            | some rows =>
                IO.println s!"l4block-file-query file={path} bytes={bytes.size} triples={directBlock.rows.length} terms={block.dict.size}"
                IO.println s!"l4block-file-query sse={q.toSse}"
                IO.println s!"l4block-file-query rows={rows.length} result={toString (repr rows)}"
                return 0
  catch e =>
    IO.eprintln s!"l4block-file-query read failure: {e}"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | path :: "--query" :: queryParts =>
      if queryParts.isEmpty then
        IO.eprintln "l4block-file-query requires a query after --query"
        return 2
      else run path (String.intercalate " " queryParts)
  | _ =>
      IO.eprintln "usage: l4block-file-query BLOCK.blk0 --query SELECT..."
      return 2

end Harness.BlockFileQuery

def main (args : List String) : IO UInt32 := Harness.BlockFileQuery.main args
