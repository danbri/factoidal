/- Shared S-expression projection for planned and observed Shardborough work.
   This is intentionally a rendering seam, not a second physical-plan model:
   its node IDs are the manifest ordinals used by the native materializer. -/
import Harness.ShardMerkleMaterialize
import L4Factoidal.JSON.Serialize
import L4Factoidal.SPARQL.Parser
import L4Factoidal.Storage.ShardManifest

namespace Harness.ShardMerkleProfile

open Harness.ShardMerkleMaterialize
open L4Factoidal.JSON
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

private def natJson (n : Nat) : Json := .number (toString n)

def planNodeJson (entry : Entry) : Json := .object
  [("plan_node", .string s!"scan-{entry.ordinal}"),
   ("operation", .string "ibk2.predicate_scan"),
   ("predicate", .string entry.predicate.val),
   ("placement", .string "local-file"),
   ("estimated_rows", natJson entry.rows),
   ("artifact_ordinal", natJson entry.ordinal),
   ("artifact_bytes", natJson entry.artifact.bytes),
   ("integrity", .string "sbm1-merkle-required")]

def explainJson (query : Query) (entries : List Entry) : Json := .object
  [("mode", .string "explain"),
   ("executes", .bool false),
   ("logical_sse", .string query.toSse),
   ("nodes", .array (entries.map planNodeJson))]

def profileNodeJson (node : Node) : Json :=
  let materialized := node.materialized
  let logicalBytes := if node.cacheHit then 0 else materialized.logicalBytes
  let fetchedBytes := if node.cacheHit then 0 else materialized.fetchedBytes
  let chunks := if node.cacheHit then 0 else materialized.verifiedChunks
  let requests := if node.cacheHit then 0 else materialized.rangeRequests
  .object
    [("plan_node", .string s!"scan-{node.entry.ordinal}"),
     ("operation", .string "ibk2.predicate_scan"),
     ("predicate", .string node.entry.predicate.val),
     ("placement", .string "local-file"),
     ("estimated_rows", natJson node.entry.rows),
     ("actual_rows", natJson materialized.triples.length),
     ("elapsed_ms", natJson node.elapsedMs),
     ("logical_bytes", natJson logicalBytes),
     ("physical_bytes", natJson fetchedBytes),
     ("chunks_verified", natJson chunks),
     ("range_requests", natJson requests),
     ("cache", .string (if node.cacheHit then "hit" else "miss")),
     ("integrity", .string "sbm1-merkle-verified")]

def profileJson (queryId : String) (query : Query) (nodes : List Node)
    (rowCount evalMs : Nat) : Json := .object
  [("mode", .string "explain-analyze"),
   ("executes", .bool true),
   ("query_id", .string queryId),
   ("logical_sse", .string query.toSse),
   ("nodes", .array (nodes.map profileNodeJson ++
      [.object [("plan_node", .string "sparql-eval"),
                ("operation", .string "sparql.select"),
                ("placement", .string "lean-native"),
                ("actual_rows", natJson rowCount),
                ("elapsed_ms", natJson evalMs),
                ("integrity", .string "sbm1-merkle-verified")]]))]

def jsonString (value : Json) : String := toStringCompact value

end Harness.ShardMerkleProfile
