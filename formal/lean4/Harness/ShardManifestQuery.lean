/- Execute ordinary parsed SELECT queries over a checked SBM0 Shardborough
   collection rooted at a local directory.  The host loader deliberately
   accepts only packer-produced leaf names; broader host key policies belong
   behind the same pure `ShardManifest.Reader` boundary. -/
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.StoreDataset

namespace Harness.ShardManifestQuery

open L4Factoidal.Storage.ShardManifest
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreDataset

private def safeLeafKey (key : ArtifactKey) : Bool :=
  !key.value.isEmpty && !(key.value.contains '/') && !(key.value.contains '\\')

private def run (directory : System.FilePath) (queryText : String) : IO UInt32 := do
  try
    let manifestBytes ← IO.FS.readBinFile (directory / "manifest.sbm0")
    match decode? manifestBytes with
    | none =>
        IO.eprintln "l4block-shard-query rejected: malformed or unsupported SBM0 manifest"
        return 1
    | some manifest =>
        match parseSparql queryText with
        | .error e =>
            IO.eprintln s!"l4block-shard-query query parse error at {e.pos}: {e.msg}"
            return 1
        | .ok q =>
        /- A partial opened store is sound only for native algebra shapes where
           every search carries a syntactically constant predicate.  All other
           parsed SPARQL remains on the full verified-manifest path. -/
        let selectedPredicates := queryNativeConstantPredicates? q
        let entries := match selectedPredicates with
          | some predicates => entriesForPredicates manifest predicates
          | none => manifest.entries
        let loaded ← entries.mapM fun entry => do
          if !safeLeafKey entry.artifact.key then
            throw <| IO.userError s!"unsafe manifest artifact key: {entry.artifact.key.value}"
          let bytes ← IO.FS.readBinFile (directory / entry.artifact.key.value)
          pure (entry.artifact.key, bytes)
        let loadedBytes := loaded.foldl (fun total pair => total + pair.2.size) 0
        let totalBytes := manifest.entries.foldl (fun total entry => total + entry.artifact.bytes) 0
        let reader : Reader := fun key =>
          (loaded.find? fun pair => pair.1 == key).map Prod.snd
        let opened := match selectedPredicates with
          | some predicates => openStoreForPredicates? reader manifest predicates
          | none => openStore? reader manifest
        match opened with
        | none =>
            IO.eprintln "l4block-shard-query rejected: unavailable, changed, or malformed child artifact"
            return 1
        | some store =>
            let dataset : DatasetBackend := { default := .hdt (readOps store), named := [] }
            match runSelectQueryBackendDataset emptyEnv q dataset with
            | none =>
                IO.eprintln "l4block-shard-query failed: query was not evaluated as SELECT"
                return 1
            | some rows =>
                let mode := match selectedPredicates with
                  | some predicates => s!"predicate-selective({predicates.length})"
                  | none => "full-manifest"
                IO.println s!"l4block-shard-query manifest={directory / "manifest.sbm0"} shards={store.blocks.length} open-mode={mode} artifact-bytes={loadedBytes}/{totalBytes}"
                IO.println s!"l4block-shard-query sse={q.toSse}"
                IO.println s!"l4block-shard-query rows={rows.length} preview={toString (repr (rows.take 10))}"
                return 0
  catch e =>
    IO.eprintln s!"l4block-shard-query read failure: {e}"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | directory :: "--query" :: queryParts =>
      if queryParts.isEmpty then
        IO.eprintln "l4block-shard-query requires a query after --query"
        return 2
      else run (System.FilePath.mk directory) (String.intercalate " " queryParts)
  | _ =>
      IO.eprintln "usage: l4block-shard-query SHARD-DIR --query SELECT..."
      return 2

end Harness.ShardManifestQuery

def main (args : List String) : IO UInt32 := Harness.ShardManifestQuery.main args
