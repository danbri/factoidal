/- Ordinary parsed SELECT over the conservative constant-predicate fragment,
   with every selected IBK2 range admitted through an SBM1 Merkle root before
   it reaches the existing SPARQL evaluator. -/
import Harness.ShardMerkleMaterialize
import Harness.ShardMerkleProfile
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.StoreDataset

namespace Harness.ShardMerkleQuery

open Harness.ShardMerkleMaterialize
open Harness.ShardMerkleProfile
open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.Storage.ShardManifest

/-- A planned, non-executing S-expression view. It deliberately exposes only
    the manifest-selected artifacts and their declared row estimates: no child
    file is opened, decoded, or trusted by `EXPLAIN`. -/
private def explain (asJson : Bool) (directory : System.FilePath) (queryText : String) : IO UInt32 := do
  try
    let manifestPath := directory / "manifest.sbm1"
    let manifestBytes ← IO.FS.readBinFile manifestPath
    match decode? manifestBytes, parseSparql queryText with
    | none, _ => IO.eprintln "l4block-shard-merkle-query rejected: malformed or unsupported SBM1 manifest"; return 1
    | _, .error e => IO.eprintln s!"l4block-shard-merkle-query query parse error at {e.pos}: {e.msg}"; return 1
    | some manifest, .ok query =>
        if !rangeCommitted manifest then
          IO.eprintln "l4block-shard-merkle-query rejected: manifest has no SBM1 range commitment"
          return 1
        match queryNativeConstantPredicates? query with
        | none =>
            IO.eprintln "l4block-shard-merkle-query rejected: query requires the full-manifest backend (not constant-predicate fragment)"
            return 1
        | some predicates =>
            let entries := entriesForPredicates manifest predicates
            let format := if asJson then "json" else "sexp"
            IO.println s!"l4block-shard-merkle-query explain format={format} manifest={manifestPath} shards={entries.length} open-mode=predicate-selective-merkle({predicates.length}) executes=false"
            if asJson then IO.println (jsonString (explainJson query entries))
            else IO.println (explainSse query entries)
            return 0
  catch e => IO.eprintln s!"l4block-shard-merkle-query explain failure: {e}"; return 1

private def materializeProfiled (directory : System.FilePath) : List Entry →
    IO (Option (List Node))
  | [] => pure (some [])
  | entry :: rest => do
      let t0 ← IO.monoMsNow
      match ← scanEntryProfile directory entry with
      | some materialized =>
          let t1 ← IO.monoMsNow
          match ← materializeProfiled directory rest with
          | some nodes => pure (some ({ entry, materialized, cacheHit := false, elapsedMs := t1 - t0 } :: nodes))
          | none => pure none
      | none => pure none

/-- Explicit `EXPLAIN ANALYZE` analogue for one read-only query. Unlike
    `--explain`, this opens the selected artifacts and reports observed scan
    and evaluator measurements in the same S-expression node family. -/
private def explainAnalyze (asJson : Bool) (directory : System.FilePath) (queryText : String) : IO UInt32 := do
  try
    let manifestPath := directory / "manifest.sbm1"
    let manifestBytes ← IO.FS.readBinFile manifestPath
    match decode? manifestBytes, parseSparql queryText with
    | none, _ => IO.eprintln "l4block-shard-merkle-query rejected: malformed or unsupported SBM1 manifest"; return 1
    | _, .error e => IO.eprintln s!"l4block-shard-merkle-query query parse error at {e.pos}: {e.msg}"; return 1
    | some manifest, .ok query =>
        if !rangeCommitted manifest then
          IO.eprintln "l4block-shard-merkle-query rejected: manifest has no SBM1 range commitment"
          return 1
        match queryNativeConstantPredicates? query with
        | none =>
            IO.eprintln "l4block-shard-merkle-query rejected: query requires the full-manifest backend (not constant-predicate fragment)"
            return 1
        | some predicates =>
            let entries := entriesForPredicates manifest predicates
            match ← materializeProfiled directory entries with
            | none =>
                IO.eprintln "l4block-shard-merkle-query rejected: unavailable, changed, or malformed proof-carrying child artifact"
                return 1
            | some nodes =>
                let triples := nodes.flatMap fun node => node.materialized.triples
                let dataset : DatasetBackend := { default := .hdt (readOpsOf triples), named := [] }
                let t0 ← IO.monoMsNow
                match runSelectQueryBackendDataset emptyEnv query dataset with
                | none => IO.eprintln "l4block-shard-merkle-query failed: query was not evaluated as SELECT"; return 1
                | some rows =>
                    let t1 ← IO.monoMsNow
                    let format := if asJson then "json" else "sexp"
                    IO.println s!"l4block-shard-merkle-query explain-analyze format={format} manifest={manifestPath} shards={entries.length} open-mode=predicate-selective-merkle({predicates.length}) executes=true"
                    if asJson then IO.println (jsonString (profileJson "query-1" query nodes rows.length (t1 - t0)) )
                    else IO.println (profileSse "query-1" query nodes rows.length (t1 - t0))
                    return 0
  catch e => IO.eprintln s!"l4block-shard-merkle-query explain-analyze failure: {e}"; return 1

private def run (directory : System.FilePath) (queryText : String) : IO UInt32 := do
  try
    let manifestPath := directory / "manifest.sbm1"
    let manifestBytes ← IO.FS.readBinFile manifestPath
    match decode? manifestBytes, parseSparql queryText with
    | none, _ => IO.eprintln "l4block-shard-merkle-query rejected: malformed or unsupported SBM1 manifest"; return 1
    | _, .error e => IO.eprintln s!"l4block-shard-merkle-query query parse error at {e.pos}: {e.msg}"; return 1
    | some manifest, .ok query =>
        if !rangeCommitted manifest then
          IO.eprintln "l4block-shard-merkle-query rejected: manifest has no SBM1 range commitment"
          return 1
        match queryNativeConstantPredicates? query with
        | none =>
            IO.eprintln "l4block-shard-merkle-query rejected: query requires the full-manifest backend (not constant-predicate fragment)"
            return 1
        | some predicates =>
            let entries := entriesForPredicates manifest predicates
            match ← scanEntries directory entries with
            | none =>
                IO.eprintln "l4block-shard-merkle-query rejected: unavailable, changed, or malformed proof-carrying child artifact"
                return 1
            | some (triples, logicalBytes) =>
                let dataset : DatasetBackend := { default := .hdt (readOpsOf triples), named := [] }
                match runSelectQueryBackendDataset emptyEnv query dataset with
                | none => IO.eprintln "l4block-shard-merkle-query failed: query was not evaluated as SELECT"; return 1
                | some rows =>
                    IO.println s!"l4block-shard-merkle-query manifest={manifestPath} shards={entries.length} open-mode=predicate-selective-merkle({predicates.length}) logical-read-bytes={logicalBytes}"
                    IO.println s!"l4block-shard-merkle-query sse={query.toSse}"
                    IO.println s!"l4block-shard-merkle-query rows={rows.length} preview={toString (repr (rows.take 10))}"
                    return 0
  catch e => IO.eprintln s!"l4block-shard-merkle-query read failure: {e}"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | directory :: "--explain-analyze-json" :: queryParts =>
      if queryParts.isEmpty then IO.eprintln "l4block-shard-merkle-query requires a query after --explain-analyze-json"; return 2
      else explainAnalyze true (System.FilePath.mk directory) (String.intercalate " " queryParts)
  | directory :: "--explain-analyze" :: queryParts =>
      if queryParts.isEmpty then IO.eprintln "l4block-shard-merkle-query requires a query after --explain-analyze"; return 2
      else explainAnalyze false (System.FilePath.mk directory) (String.intercalate " " queryParts)
  | directory :: "--explain-json" :: queryParts =>
      if queryParts.isEmpty then IO.eprintln "l4block-shard-merkle-query requires a query after --explain-json"; return 2
      else explain true (System.FilePath.mk directory) (String.intercalate " " queryParts)
  | directory :: "--explain" :: queryParts =>
      if queryParts.isEmpty then IO.eprintln "l4block-shard-merkle-query requires a query after --explain"; return 2
      else explain false (System.FilePath.mk directory) (String.intercalate " " queryParts)
  | directory :: "--query" :: queryParts =>
      if queryParts.isEmpty then IO.eprintln "l4block-shard-merkle-query requires a query after --query"; return 2
      else run (System.FilePath.mk directory) (String.intercalate " " queryParts)
  | _ => IO.eprintln "usage: l4block-shard-merkle-query SHARD-DIR --explain|--explain-json|--explain-analyze|--explain-analyze-json|--query SELECT..."; return 2

end Harness.ShardMerkleQuery

def main (args : List String) : IO UInt32 := Harness.ShardMerkleQuery.main args
