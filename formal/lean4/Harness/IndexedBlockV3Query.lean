/- Parsed SELECT over constant-predicate IBK3 fragments: physical bytes are
   admitted by the shared Merkle/paged materializer, then ordinary Lean SPARQL
   evaluates the parsed algebra. -/
import Harness.IndexedBlockV3Materialize
import Harness.ShardMerkleMaterialize
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.StoreDataset
import L4Factoidal.SPARQL.StoreFastPath
import L4Factoidal.Storage.ShardManifest

namespace Harness.IndexedBlockV3Query

open Harness.IndexedBlockV3Materialize
open Harness.ShardMerkleMaterialize
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

/-- A physically safe bounded-prefix shape. Subject/object must be distinct
    variables: constants or repeated variables could make early rows fail the
    SPARQL pattern and would need continued scanning. -/
private def prefixPredicate? (tp : TriplePattern) : Option WfIri :=
  match tp.s, tp.p, tp.o with
  | .var subject, .iri predicate, .var object =>
      if subject == object then none else some predicate
  | _, _, _ => none

private def finish (query : Query) (entries : List Entry) (predicates : List WfIri)
    (triples : List Triple) (counters : Counters) (delta : DeltaResolved) : IO UInt32 := do
  let dataset : DatasetBackend := { default := .hdt (readOpsOfDelta triples delta), named := [] }
  match runSelectQueryBackendDataset emptyEnv query dataset with
  | none => IO.eprintln "l4block-id-v3-query failed: query was not evaluated as SELECT"; return 1
  | some rows =>
      let deltaMode := if deltaResolvedIsEmpty delta then "base" else "base-plus-delta"
      IO.println s!"l4block-id-v3-query shards={entries.length} open-mode=ibk3-paged-merkle({predicates.length}) delta={deltaMode} logical-read-bytes={counters.requestedBytes} fetched-bytes={counters.fetchedBytes}"
      IO.println s!"l4block-id-v3-query sse={query.toSse}"
      IO.println s!"l4block-id-v3-query rows={rows.length} preview={toString (repr (rows.take 10))}"
      return 0

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
            match ← readDefaultDelta? directory with
            | none => IO.eprintln "l4block-id-v3-query rejected: malformed DLOG sidecar"; return 1
            | some delta =>
                match detectLimitSingleTp query with
                | some (tp, limit) =>
                    match prefixPredicate? tp with
                    | some predicate =>
                        if !deltaResolvedIsEmpty delta then
                          match ← materializeEntries directory entries with
                          | some (triples, counters) => finish query entries predicates triples counters delta
                          | none => IO.eprintln "l4block-id-v3-query rejected: malformed or unavailable committed artifact"; return 1
                        else
                          let prefixEntries := selectAll manifest predicate
                          match ← scanEntries directory predicate limit prefixEntries [] {} 0 with
                          | some (triples, counters, _) => finish query prefixEntries predicates triples counters delta
                          | none => IO.eprintln "l4block-id-v3-query rejected: malformed or unavailable committed artifact"; return 1
                    | none =>
                        match ← materializeEntries directory entries with
                        | some (triples, counters) => finish query entries predicates triples counters delta
                        | none => IO.eprintln "l4block-id-v3-query rejected: malformed or unavailable committed artifact"; return 1
                | none =>
                    match ← materializeEntries directory entries with
                    | some (triples, counters) => finish query entries predicates triples counters delta
                    | none => IO.eprintln "l4block-id-v3-query rejected: malformed or unavailable committed artifact"; return 1
  catch error => IO.eprintln s!"l4block-id-v3-query failure: {error}"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | directory :: "--query" :: queryParts =>
      if queryParts.isEmpty then IO.eprintln "l4block-id-v3-query requires a query"; return 2
      else run directory (String.intercalate " " queryParts)
  | _ => IO.eprintln "usage: l4block-id-v3-query SHARD-DIR --query SELECT..."; return 2

end Harness.IndexedBlockV3Query

def main (args : List String) : IO UInt32 := Harness.IndexedBlockV3Query.main args
