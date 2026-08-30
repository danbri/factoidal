/- Bounded warm session for parsed constant-predicate SELECT queries over SBM1
   Merkle-verified ranges. Once admitted, immutable decoded triples are cached
   in process memory; no later query consults unchecked disk bytes. -/
import Harness.ShardMerkleMaterialize
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.StoreDataset

namespace Harness.ShardMerkleSession

open Harness.ShardMerkleMaterialize
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.Storage.ShardManifest

structure CachedArtifact where
  key : ArtifactKey
  triples : List L4Factoidal.RDF.Triple

structure Loaded where
  triples : List L4Factoidal.RDF.Triple
  hits : Nat
  misses : Nat
  newlyVerifiedBytes : Nat

private def emptyLoaded : Loaded := { triples := [], hits := 0, misses := 0, newlyVerifiedBytes := 0 }

private def readOne (directory : System.FilePath) (cache : IO.Ref (List CachedArtifact))
    (entry : Entry) : IO (Option (List L4Factoidal.RDF.Triple × Bool × Nat)) := do
  match (← cache.get).find? (fun cached => cached.key == entry.artifact.key) with
  | some cached => pure (some (cached.triples, true, 0))
  | none =>
      match ← scanEntry directory entry with
      | none => pure none
      | some (triples, logicalBytes) =>
          cache.modify fun entries => { key := entry.artifact.key, triples } :: entries
          pure (some (triples, false, logicalBytes))

private def readEntries (directory : System.FilePath) (cache : IO.Ref (List CachedArtifact)) :
    List Entry → IO (Option Loaded)
  | [] => pure (some emptyLoaded)
  | entry :: rest => do
      match ← readOne directory cache entry, ← readEntries directory cache rest with
      | some (triples, hit, bytes), some tail =>
          pure (some {
            triples := triples ++ tail.triples
            hits := tail.hits + if hit then 1 else 0
            misses := tail.misses + if hit then 0 else 1
            newlyVerifiedBytes := tail.newlyVerifiedBytes + bytes })
      | _, _ => pure none

private def execute (directory : System.FilePath) (manifest : Manifest)
    (cache : IO.Ref (List CachedArtifact)) (queryNumber : Nat) (queryText : String) : IO Bool := do
  match parseSparql queryText with
  | .error e =>
      IO.eprintln s!"l4block-shard-merkle-session query={queryNumber} parse-error at {e.pos}: {e.msg}"
      pure false
  | .ok query =>
      match queryNativeConstantPredicates? query with
      | none =>
          IO.eprintln s!"l4block-shard-merkle-session query={queryNumber} rejected: requires full-manifest backend"
          pure false
      | some predicates =>
          let entries := entriesForPredicates manifest predicates
          match ← readEntries directory cache entries with
          | none =>
              IO.eprintln s!"l4block-shard-merkle-session query={queryNumber} rejected: unavailable, changed, or malformed proof-carrying child artifact"
              pure false
          | some loaded =>
              let dataset : DatasetBackend := { default := .hdt (readOpsOf loaded.triples), named := [] }
              match runSelectQueryBackendDataset emptyEnv query dataset with
              | none =>
                  IO.eprintln s!"l4block-shard-merkle-session query={queryNumber} failed: query was not evaluated as SELECT"
                  pure false
              | some rows =>
                  let cacheArtifacts := (← cache.get).length
                  IO.println s!"l4block-shard-merkle-session query={queryNumber} shards={entries.length} open-mode=predicate-selective-merkle({predicates.length}) cache-hit={loaded.hits} cache-miss={loaded.misses} newly-verified-bytes={loaded.newlyVerifiedBytes} cache-artifacts={cacheArtifacts}"
                  IO.println s!"l4block-shard-merkle-session rows={rows.length} preview={toString (repr (rows.take 10))}"
                  pure true

private def run (directory : System.FilePath) : IO UInt32 := do
  try
    let manifestBytes ← IO.FS.readBinFile (directory / "manifest.sbm1")
    match decode? manifestBytes with
    | none => IO.eprintln "l4block-shard-merkle-session rejected: malformed or unsupported SBM1 manifest"; return 1
    | some manifest =>
        if manifest.version != 1 then
          IO.eprintln "l4block-shard-merkle-session rejected: manifest has no SBM1 range commitment"
          return 1
        let stdin ← IO.getStdin
        let input ← stdin.readToEnd
        let queries := input.splitOn "\n" |>.map (fun query => query.trimAscii.toString) |>.filter fun query => !query.isEmpty
        if queries.isEmpty then
          IO.eprintln "l4block-shard-merkle-session requires one newline-delimited SELECT query on stdin"
          return 2
        let cache ← IO.mkRef ([] : List CachedArtifact)
        let results : List Bool ← (queries.zip (List.range queries.length)).mapM fun (query, i) =>
          execute directory manifest cache (i + 1) query
        let passed := results.filter id |>.length
        IO.println s!"l4block-shard-merkle-session summary queries={queries.length} succeeded={passed} failed={queries.length - passed}"
        return if passed == queries.length then 0 else 1
  catch e => IO.eprintln s!"l4block-shard-merkle-session read failure: {e}"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [directory] => run (System.FilePath.mk directory)
  | _ => IO.eprintln "usage: l4block-shard-merkle-session SHARD-DIR < newline-delimited-select-queries.rq"; return 2

end Harness.ShardMerkleSession

def main (args : List String) : IO UInt32 := Harness.ShardMerkleSession.main args
