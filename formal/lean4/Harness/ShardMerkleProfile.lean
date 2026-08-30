/- Shared S-expression projection for planned and observed Shardborough work.
   This is intentionally a rendering seam, not a second physical-plan model:
   its node IDs are the manifest ordinals used by the native materializer. -/
import Harness.ShardMerkleMaterialize
import L4Factoidal.SPARQL.Parser
import L4Factoidal.Storage.ShardManifest

namespace Harness.ShardMerkleProfile

open Harness.ShardMerkleMaterialize
open L4Factoidal.SPARQL
open L4Factoidal.Storage.ShardManifest

structure Node where
  entry : Entry
  materialized : Materialized
  cacheHit : Bool
  elapsedMs : Nat

def scanNodeSse (entry : Entry) : String :=
  s!"(node scan-{entry.ordinal}\n    (scan :predicate <{entry.predicate.val}>)\n    (placement local-file)\n    (estimate :rows {entry.rows})\n    (artifact :ordinal {entry.ordinal} :bytes {entry.artifact.bytes})\n    (integrity :manifest SBM1 :merkle required))"

def explainSse (query : Query) (entries : List Entry) : String :=
  let scans := String.intercalate "\n  " (entries.map scanNodeSse)
  let inputs := String.intercalate " " (entries.map fun entry => s!"@scan-{entry.ordinal}")
  s!"(explain\n  (logical {query.toSse})\n  (flow\n  {scans}\n  (node sparql-eval\n    (sparql-select :inputs ({inputs}))\n    (placement lean-native)\n    (integrity :manifest SBM1 :merkle required))))"

def scanProfileSse (node : Node) : String :=
  let materialized := node.materialized
  let logicalBytes := if node.cacheHit then 0 else materialized.logicalBytes
  let fetchedBytes := if node.cacheHit then 0 else materialized.fetchedBytes
  let chunks := if node.cacheHit then 0 else materialized.verifiedChunks
  let requests := if node.cacheHit then 0 else materialized.rangeRequests
  let cacheState := if node.cacheHit then "hit" else "miss"
  s!"(node scan-{node.entry.ordinal}\n    (scan :predicate <{node.entry.predicate.val}>)\n    (placement local-file)\n    (estimate :rows {node.entry.rows})\n    (actual :rows {materialized.triples.length} :elapsed-ms {node.elapsedMs})\n    (io :logical-bytes {logicalBytes} :physical-bytes {fetchedBytes} :chunks {chunks} :range-requests {requests} :cache {cacheState})\n    (integrity :manifest SBM1 :merkle verified))"

def profileSse (queryId : String) (query : Query) (nodes : List Node)
    (rowCount evalMs : Nat) : String :=
  let scans := String.intercalate "\n  " (nodes.map scanProfileSse)
  let inputs := String.intercalate " " (nodes.map fun node => s!"@scan-{node.entry.ordinal}")
  s!"(profile {queryId}\n  (logical {query.toSse})\n  (flow\n  {scans}\n  (node sparql-eval\n    (sparql-select :inputs ({inputs}))\n    (placement lean-native)\n    (actual :rows {rowCount} :elapsed-ms {evalMs})\n    (integrity :manifest SBM1 :merkle verified))))"

end Harness.ShardMerkleProfile
