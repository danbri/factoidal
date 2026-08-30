/- A bounded native Shardborough query session.  It accepts newline-delimited
   parsed-SPARQL requests on stdin, keeping only successfully verified IBK2
   blocks in memory between requests.  This is intentionally a finite batch,
   rather than an unbounded partial-def daemon: callers may keep the native
   process alive through their ordinary process supervisor while Lean's
   executable core stays total apart from its explicit I/O edge. -/
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.StoreDataset

namespace Harness.ShardManifestSession

open L4Factoidal.Storage.ShardManifest
open L4Factoidal.Storage
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreDataset

private def safeLeafKey (key : ArtifactKey) : Bool :=
  !key.value.isEmpty && !(key.value.contains '/') && !(key.value.contains '\\')

structure CachedBlock where
  key : ArtifactKey
  block : IndexedBlockWireV2.OpenBlock

structure Loaded where
  blocks : List (Entry × IndexedBlockWireV2.OpenBlock)
  hits : Nat
  misses : Nat
  newlyReadBytes : Nat

private def emptyLoaded : Loaded := { blocks := [], hits := 0, misses := 0, newlyReadBytes := 0 }

private def readOne (directory : System.FilePath) (cache : IO.Ref (List CachedBlock))
    (entry : Entry) : IO (Option (IndexedBlockWireV2.OpenBlock × Bool × Nat)) := do
  match (← cache.get).find? (fun cached => cached.key == entry.artifact.key) with
  | some cached => pure (some (cached.block, true, 0))
  | none =>
      if !safeLeafKey entry.artifact.key then
        throw <| IO.userError s!"unsafe manifest artifact key: {entry.artifact.key.value}"
      let bytes ← IO.FS.readBinFile (directory / entry.artifact.key.value)
      let reader : Reader := fun key => if key == entry.artifact.key then some bytes else none
      match openVerified? reader entry with
      | none => pure none
      | some block =>
          cache.modify fun blocks => { key := entry.artifact.key, block } :: blocks
          pure (some (block, false, bytes.size))

private def readEntries (directory : System.FilePath) (cache : IO.Ref (List CachedBlock)) :
    List Entry → IO (Option Loaded)
  | [] => pure (some emptyLoaded)
  | entry :: rest => do
      match (← readOne directory cache entry), (← readEntries directory cache rest) with
      | some (block, hit, bytes), some tail =>
          pure (some {
            blocks := (entry, block) :: tail.blocks
            hits := tail.hits + if hit then 1 else 0
            misses := tail.misses + if hit then 0 else 1
            newlyReadBytes := tail.newlyReadBytes + bytes
          })
      | _, _ => pure none

private def execute (directory : System.FilePath) (manifest : Manifest)
    (cache : IO.Ref (List CachedBlock)) (queryNumber : Nat) (queryText : String) : IO Bool := do
  match parseSparql queryText with
  | .error e =>
      IO.eprintln s!"l4block-shard-session query={queryNumber} parse-error at {e.pos}: {e.msg}"
      pure false
  | .ok query =>
      /- Partial manifests are only built for the conservatively admitted
         constant-predicate subset.  Every other parsed query receives the
         complete current manifest, preserving ordinary evaluator semantics. -/
      let selectedPredicates := queryNativeConstantPredicates? query
      let entries := match selectedPredicates with
        | some predicates => entriesForPredicates manifest predicates
        | none => manifest.entries
      match ← readEntries directory cache entries with
      | none =>
          IO.eprintln s!"l4block-shard-session query={queryNumber} rejected: unavailable, changed, or malformed child artifact"
          pure false
      | some loaded =>
          let store : OpenStore := { manifest, blocks := loaded.blocks }
          let dataset : DatasetBackend := { default := .hdt (readOps store), named := [] }
          match runSelectQueryBackendDataset emptyEnv query dataset with
          | none =>
              IO.eprintln s!"l4block-shard-session query={queryNumber} failed: query was not evaluated as SELECT"
              pure false
          | some rows =>
              let mode := match selectedPredicates with
                | some predicates => s!"predicate-selective({predicates.length})"
                | none => "full-manifest"
              let cacheBlocks := (← cache.get).length
              IO.println s!"l4block-shard-session query={queryNumber} shards={store.blocks.length} open-mode={mode} cache-hit={loaded.hits} cache-miss={loaded.misses} newly-read-bytes={loaded.newlyReadBytes} cache-blocks={cacheBlocks}"
              IO.println s!"l4block-shard-session rows={rows.length} preview={toString (repr (rows.take 10))}"
              pure true

private def run (directory : System.FilePath) : IO UInt32 := do
  try
    let manifestBytes ← IO.FS.readBinFile (directory / "manifest.sbm0")
    match decode? manifestBytes with
    | none =>
        IO.eprintln "l4block-shard-session rejected: malformed or unsupported SBM0 manifest"
        return 1
    | some manifest =>
        let stdin ← IO.getStdin
        let input ← stdin.readToEnd
        let queries := input.splitOn "\n" |>.map (fun query => query.trimAscii.toString) |>.filter fun query => !query.isEmpty
        if queries.isEmpty then
          IO.eprintln "l4block-shard-session requires one newline-delimited SELECT query on stdin"
          return 2
        let cache ← IO.mkRef ([] : List CachedBlock)
        let results : List Bool ← (queries.zip (List.range queries.length)).mapM fun (query, i) =>
          execute directory manifest cache (i + 1) query
        let passed := results.filter id |>.length
        IO.println s!"l4block-shard-session summary queries={queries.length} succeeded={passed} failed={queries.length - passed}"
        return if passed == queries.length then 0 else 1
  catch e =>
    IO.eprintln s!"l4block-shard-session read failure: {e}"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [directory] => run (System.FilePath.mk directory)
  | _ =>
      IO.eprintln "usage: l4block-shard-session SHARD-DIR < newline-delimited-select-queries.rq"
      return 2

end Harness.ShardManifestSession

def main (args : List String) : IO UInt32 := Harness.ShardManifestSession.main args
