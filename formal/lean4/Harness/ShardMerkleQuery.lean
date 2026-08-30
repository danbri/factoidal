/- Ordinary parsed SELECT over the conservative constant-predicate fragment,
   with every selected IBK2 range admitted through an SBM1 Merkle root before
   it reaches the existing SPARQL evaluator. -/
import Harness.ShardMerkleMaterialize
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.StoreDataset

namespace Harness.ShardMerkleQuery

open Harness.ShardMerkleMaterialize
open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.Storage.ShardManifest

private def scanNodeSse (entry : Entry) : String :=
  s!"(node scan-{entry.ordinal}\n    (scan :predicate <{entry.predicate.val}>)\n    (placement local-file)\n    (estimate :rows {entry.rows})\n    (artifact :ordinal {entry.ordinal} :bytes {entry.artifact.bytes})\n    (integrity :manifest SBM1 :merkle required))"

/-- A planned, non-executing S-expression view. It deliberately exposes only
    the manifest-selected artifacts and their declared row estimates: no child
    file is opened, decoded, or trusted by `EXPLAIN`. -/
private def explainSse (query : Query) (entries : List Entry) : String :=
  let scans := String.intercalate "\n  " (entries.map scanNodeSse)
  let inputs := String.intercalate " " (entries.map fun entry => s!"@scan-{entry.ordinal}")
  s!"(explain\n  (logical {query.toSse})\n  (flow\n  {scans}\n  (node sparql-eval\n    (sparql-select :inputs ({inputs}))\n    (placement lean-native)\n    (integrity :manifest SBM1 :merkle required))))"

private def explain (directory : System.FilePath) (queryText : String) : IO UInt32 := do
  try
    let manifestPath := directory / "manifest.sbm1"
    let manifestBytes ← IO.FS.readBinFile manifestPath
    match decode? manifestBytes, parseSparql queryText with
    | none, _ => IO.eprintln "l4block-shard-merkle-query rejected: malformed or unsupported SBM1 manifest"; return 1
    | _, .error e => IO.eprintln s!"l4block-shard-merkle-query query parse error at {e.pos}: {e.msg}"; return 1
    | some manifest, .ok query =>
        if manifest.version != 1 then
          IO.eprintln "l4block-shard-merkle-query rejected: manifest has no SBM1 range commitment"
          return 1
        match queryNativeConstantPredicates? query with
        | none =>
            IO.eprintln "l4block-shard-merkle-query rejected: query requires the full-manifest backend (not constant-predicate fragment)"
            return 1
        | some predicates =>
            let entries := entriesForPredicates manifest predicates
            IO.println s!"l4block-shard-merkle-query explain format=sexp manifest={manifestPath} shards={entries.length} open-mode=predicate-selective-merkle({predicates.length}) executes=false"
            IO.println (explainSse query entries)
            return 0
  catch e => IO.eprintln s!"l4block-shard-merkle-query explain failure: {e}"; return 1

private def run (directory : System.FilePath) (queryText : String) : IO UInt32 := do
  try
    let manifestPath := directory / "manifest.sbm1"
    let manifestBytes ← IO.FS.readBinFile manifestPath
    match decode? manifestBytes, parseSparql queryText with
    | none, _ => IO.eprintln "l4block-shard-merkle-query rejected: malformed or unsupported SBM1 manifest"; return 1
    | _, .error e => IO.eprintln s!"l4block-shard-merkle-query query parse error at {e.pos}: {e.msg}"; return 1
    | some manifest, .ok query =>
        if manifest.version != 1 then
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
  | directory :: "--explain" :: queryParts =>
      if queryParts.isEmpty then IO.eprintln "l4block-shard-merkle-query requires a query after --explain"; return 2
      else explain (System.FilePath.mk directory) (String.intercalate " " queryParts)
  | directory :: "--query" :: queryParts =>
      if queryParts.isEmpty then IO.eprintln "l4block-shard-merkle-query requires a query after --query"; return 2
      else run (System.FilePath.mk directory) (String.intercalate " " queryParts)
  | _ => IO.eprintln "usage: l4block-shard-merkle-query SHARD-DIR --explain|--query SELECT..."; return 2

end Harness.ShardMerkleQuery

def main (args : List String) : IO UInt32 := Harness.ShardMerkleQuery.main args
