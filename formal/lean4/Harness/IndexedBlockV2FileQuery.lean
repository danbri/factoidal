/- Execute SELECT over an integrity-checked IBK2 artifact through its range-aware backend. -/
import L4Factoidal.Storage.IndexedBlockWireV2
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.StoreDataset

namespace Harness.IndexedBlockV2FileQuery

open L4Factoidal.SPARQL
open L4Factoidal.Storage.IndexedBlockWireV2
open L4Factoidal.SPARQL.StoreDataset

private def run (path queryText : String) : IO UInt32 := do
  try
    let bytes ← IO.FS.readBinFile path
    match open? bytes with
    | none =>
        IO.eprintln "l4block-id-v2-file-query rejected: malformed, unsupported, or checksum-failing IBK2 file"
        return 1
    | some opened =>
        let dataset : DatasetBackend := { default := .hdt (readOpsRange opened), named := [] }
        match parseSparql queryText with
        | .error e =>
            IO.eprintln s!"l4block-id-v2-file-query query parse error at {e.pos}: {e.msg}"
            return 1
        | .ok q =>
            match runSelectQueryBackendDataset emptyEnv q dataset with
            | none =>
                IO.eprintln "l4block-id-v2-file-query failed: query was not evaluated as SELECT"
                return 1
            | some rows =>
                IO.println s!"l4block-id-v2-file-query file={path} bytes={bytes.size} terms={opened.decoded.dict.size} id-rows={opened.decoded.rows.size}"
                IO.println s!"l4block-id-v2-file-query sse={q.toSse}"
                IO.println s!"l4block-id-v2-file-query rows={rows.length} result={toString (repr rows)}"
                return 0
  catch e =>
    IO.eprintln s!"l4block-id-v2-file-query read failure: {e}"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | path :: "--query" :: queryParts =>
      if queryParts.isEmpty then
        IO.eprintln "l4block-id-v2-file-query requires a query after --query"
        return 2
      else run path (String.intercalate " " queryParts)
  | _ =>
      IO.eprintln "usage: l4block-id-v2-file-query BLOCK.ibk2 --query SELECT..."
      return 2

end Harness.IndexedBlockV2FileQuery

def main (args : List String) : IO UInt32 := Harness.IndexedBlockV2FileQuery.main args
