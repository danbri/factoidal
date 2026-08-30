/- Query a direct IndexedBlockWireV1 file through the SPARQL backend. -/
import L4Factoidal.Storage.IndexedBlockWireV1
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.StoreDataset

namespace Harness.IndexedBlockFileQuery

open L4Factoidal.SPARQL
open L4Factoidal.Storage.IndexedBlock
open L4Factoidal.Storage.IndexedBlockWireV1
open L4Factoidal.Storage.BlockArtifact
open L4Factoidal.SPARQL.StoreDataset

private def run (path queryText : String) (trustedDigest : Option Digest256 := none) : IO UInt32 := do
  try
    let bytes ← IO.FS.readBinFile path
    let decoded := match trustedDigest with
      | none => decode bytes
      | some digest => decodeVerified digest bytes
    match decoded with
    | none =>
        IO.eprintln "l4block-id-file-query rejected: digest mismatch, malformed, unsupported, or checksum-failing IBK1 file"
        return 1
    | some block =>
        let dataset : DatasetBackend := { default := .hdt (readOps block), named := [] }
        match parseSparql queryText with
        | .error e =>
            IO.eprintln s!"l4block-id-file-query query parse error at {e.pos}: {e.msg}"
            return 1
        | .ok q =>
            match runSelectQueryBackendDataset emptyEnv q dataset with
            | none =>
                IO.eprintln "l4block-id-file-query failed: query was not evaluated as SELECT"
                return 1
            | some rows =>
                IO.println s!"l4block-id-file-query file={path} bytes={bytes.size} terms={block.dict.size} id-rows={block.rows.size}"
                IO.println s!"l4block-id-file-query sse={q.toSse}"
                IO.println s!"l4block-id-file-query rows={rows.length} result={toString (repr rows)}"
                return 0
  catch e =>
    IO.eprintln s!"l4block-id-file-query read failure: {e}"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | path :: "--query" :: queryParts =>
      if queryParts.isEmpty then
        IO.eprintln "l4block-id-file-query requires a query after --query"
        return 2
      else run path (String.intercalate " " queryParts)
  | path :: "--digest-file" :: digestPath :: "--query" :: queryParts =>
      if queryParts.isEmpty then
        IO.eprintln "l4block-id-file-query requires a query after --query"
        return 2
      else try
        let digest ← IO.FS.readBinFile digestPath
        run path (String.intercalate " " queryParts) (some digest)
      catch e =>
        IO.eprintln s!"l4block-id-file-query digest read failure: {e}"
        return 1
  | _ =>
      IO.eprintln "usage: l4block-id-file-query BLOCK.ibk1 [--digest-file SHA256.bin] --query SELECT..."
      return 2

end Harness.IndexedBlockFileQuery

def main (args : List String) : IO UInt32 := Harness.IndexedBlockFileQuery.main args
