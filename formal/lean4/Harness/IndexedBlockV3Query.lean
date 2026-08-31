/- Parsed SELECT over constant-predicate IBK3 fragments: physical bytes are
   admitted by the shared Merkle/paged materializer, then ordinary Lean SPARQL
   evaluates the parsed algebra. -/
import Harness.IndexedBlockV3Materialize
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.StoreDataset
import L4Factoidal.SPARQL.StoreFastPath
import L4Factoidal.Storage.ShardManifest

namespace Harness.IndexedBlockV3Query

open Harness.IndexedBlockV3Materialize
open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.SPARQL.StoreFastPath
open L4Factoidal.Storage.ShardManifest

private def readOpsOf (triples : List Triple) : BackendReadOps :=
  { search := fun bound => tripleMatchesBound bound triples
    estimate := fun bound => (tripleMatchesBound bound triples).length
    predicatePresent := fun predicate => !(tripleMatchesBound { p := some predicate } triples).isEmpty }

private def run (directoryText queryText : String) : IO UInt32 := do
  try
    let directory := System.FilePath.mk directoryText
    let manifestBytes ← IO.FS.readBinFile (directory / "manifest.sbm2")
    match decode? manifestBytes, parseSparql queryText with
    | none, _ => IO.eprintln "l4block-id-v3-query rejected: malformed SBM2 manifest"; return 1
    | _, .error error => IO.eprintln s!"l4block-id-v3-query query parse error at {error.pos}: {error.msg}"; return 1
    | some manifest, .ok query =>
        if !rangeCommitted manifest || manifest.layout != "predicate-ibk3-ptd1-merkle-v0" then
          IO.eprintln "l4block-id-v3-query rejected: not an IBK3 range-committed manifest"; return 1
        match queryNativeConstantPredicates? query with
        | none => IO.eprintln "l4block-id-v3-query rejected: query requires an unbound/full-manifest physical plan"; return 1
        | some predicates =>
            let entries := entriesForPredicates manifest predicates
            match ← materializeEntries directory entries with
            | none => IO.eprintln "l4block-id-v3-query rejected: malformed or unavailable committed artifact"; return 1
            | some (triples, counters) =>
                let dataset : DatasetBackend := { default := .hdt (readOpsOf triples), named := [] }
                match runSelectQueryBackendDataset emptyEnv query dataset with
                | none => IO.eprintln "l4block-id-v3-query failed: query was not evaluated as SELECT"; return 1
                | some rows =>
                    IO.println s!"l4block-id-v3-query shards={entries.length} open-mode=ibk3-paged-merkle({predicates.length}) logical-read-bytes={counters.requestedBytes} fetched-bytes={counters.fetchedBytes}"
                    IO.println s!"l4block-id-v3-query sse={query.toSse}"
                    IO.println s!"l4block-id-v3-query rows={rows.length} preview={toString (repr (rows.take 10))}"
                    return 0
  catch error => IO.eprintln s!"l4block-id-v3-query failure: {error}"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | directory :: "--query" :: queryParts =>
      if queryParts.isEmpty then IO.eprintln "l4block-id-v3-query requires a query"; return 2
      else run directory (String.intercalate " " queryParts)
  | _ => IO.eprintln "usage: l4block-id-v3-query SHARD-DIR --query SELECT..."; return 2

end Harness.IndexedBlockV3Query

def main (args : List String) : IO UInt32 := Harness.IndexedBlockV3Query.main args
