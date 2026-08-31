/- Bounded warm session for parsed constant-predicate SELECT queries over SBM1
   Merkle-verified ranges. Once admitted, immutable decoded triples are cached
   in process memory; no later query consults unchecked disk bytes. -/
import Harness.ShardMerkleMaterialize
import Harness.ShardMerkleProfile
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.StoreDataset

namespace Harness.ShardMerkleSession

open Harness.ShardMerkleMaterialize
open Harness.ShardMerkleProfile
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.Storage.ShardManifest

private def readManifest (directory : System.FilePath) : IO ByteArray := do
  try IO.FS.readBinFile (directory / "manifest.sbm2")
  catch _ => IO.FS.readBinFile (directory / "manifest.sbm1")

structure CachedArtifact where
  key : ArtifactKey
  materialized : Materialized

structure Loaded where
  triples : List L4Factoidal.RDF.Triple
  nodes : List Node
  hits : Nat
  misses : Nat
  newlyLogicalBytes : Nat
  newlyRequestedBytes : Nat
  newlyFetchedBytes : Nat
  newlyVerifiedChunks : Nat
  newlyRangeRequests : Nat

private def emptyLoaded : Loaded :=
  { triples := [], nodes := [], hits := 0, misses := 0, newlyLogicalBytes := 0,
    newlyRequestedBytes := 0, newlyFetchedBytes := 0, newlyVerifiedChunks := 0,
    newlyRangeRequests := 0 }

private def readOne (directory : System.FilePath) (cache : IO.Ref (List CachedArtifact))
    (entry : Entry) : IO (Option (Materialized × Bool × Nat)) := do
  let t0 ← IO.monoMsNow
  match (← cache.get).find? (fun cached => cached.key == entry.artifact.key) with
  | some cached =>
      let t1 ← IO.monoMsNow
      pure (some (cached.materialized, true, t1 - t0))
  | none =>
      match ← scanEntryProfile directory entry with
      | none => pure none
      | some materialized =>
          cache.modify fun entries => { key := entry.artifact.key, materialized } :: entries
          let t1 ← IO.monoMsNow
          pure (some (materialized, false, t1 - t0))

private def readEntries (directory : System.FilePath) (cache : IO.Ref (List CachedArtifact)) :
    List Entry → IO (Option Loaded)
  | [] => pure (some emptyLoaded)
  | entry :: rest => do
      match ← readOne directory cache entry, ← readEntries directory cache rest with
      | some (materialized, hit, elapsedMs), some tail =>
          pure (some {
            triples := materialized.triples ++ tail.triples
            nodes := { entry, materialized, cacheHit := hit, elapsedMs } :: tail.nodes
            hits := tail.hits + if hit then 1 else 0
            misses := tail.misses + if hit then 0 else 1
            newlyLogicalBytes := tail.newlyLogicalBytes + if hit then 0 else materialized.logicalBytes
            newlyRequestedBytes := tail.newlyRequestedBytes + if hit then 0 else materialized.requestedBytes
            newlyFetchedBytes := tail.newlyFetchedBytes + if hit then 0 else materialized.fetchedBytes
            newlyVerifiedChunks := tail.newlyVerifiedChunks + if hit then 0 else materialized.verifiedChunks
            newlyRangeRequests := tail.newlyRangeRequests + if hit then 0 else materialized.rangeRequests })
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
              let evalStart ← IO.monoMsNow
              match runSelectQueryBackendDataset emptyEnv query dataset with
              | none =>
                  IO.eprintln s!"l4block-shard-merkle-session query={queryNumber} failed: query was not evaluated as SELECT"
                  pure false
              | some rows =>
                  let evalEnd ← IO.monoMsNow
                  let cacheArtifacts := (← cache.get).length
                  IO.println s!"l4block-shard-merkle-session query={queryNumber} shards={entries.length} open-mode=predicate-selective-merkle({predicates.length}) cache-hit={loaded.hits} cache-miss={loaded.misses} logical-bytes={loaded.newlyLogicalBytes} requested-range-bytes={loaded.newlyRequestedBytes} fetched-chunk-bytes={loaded.newlyFetchedBytes} verified-chunks={loaded.newlyVerifiedChunks} range-requests={loaded.newlyRangeRequests} cache-artifacts={cacheArtifacts} integrity=sbm1-merkle-verified"
                  IO.println s!"l4block-shard-merkle-session profile format=sexp query={queryNumber}"
                  IO.println (profileSse s!"query-{queryNumber}" query loaded.nodes rows.length (evalEnd - evalStart))
                  IO.println s!"l4block-shard-merkle-session rows={rows.length} preview={toString (repr (rows.take 10))}"
                  pure true

private def run (directory : System.FilePath) : IO UInt32 := do
  try
    let manifestBytes ← readManifest directory
    match decode? manifestBytes with
    | none => IO.eprintln "l4block-shard-merkle-session rejected: malformed or unsupported SBM1 manifest"; return 1
    | some manifest =>
        if !rangeCommitted manifest then
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
