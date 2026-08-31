/- Shared native-only admission edge for predicate-local SBM1 artifacts.
   It turns the four required IBK2 ranges into triples only after every range
   has been verified to the artifact's committed Merkle root. -/
import Harness.PosixRangeIO
import Harness.CompactedEpoch
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.Storage.DeltaLog
import L4Factoidal.SPARQL.StorePlan

namespace Harness.ShardMerkleMaterialize

open Harness.PosixRangeIO
open Harness.CompactedEpoch
open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StorePlan
open L4Factoidal.Storage.IndexedBlockWireV2
open L4Factoidal.Storage.ShardManifest
open L4Factoidal.Storage

def safeLeafKey (key : ArtifactKey) : Bool :=
  !key.value.isEmpty && !(key.value.contains '/') && !(key.value.contains '\\')

/- The three byte counts deliberately have different meanings:
   `logicalBytes` is the non-overlapping IBK2 plan, `requestedBytes` includes
   the prefix discovery request, and `fetchedBytes` is full native chunks. -/
structure Materialized where
  triples : List Triple
  logicalBytes : Nat
  requestedBytes : Nat
  fetchedBytes : Nat
  verifiedChunks : Nat
  rangeRequests : Nat
  deriving Repr

/-- Materialise exactly the selected predicate-local artifact through four
    Merkle-verified IBK2 ranges. -/
def scanEntryProfile (directory : System.FilePath) (entry : Entry) :
    IO (Option Materialized) := do
  if !safeLeafKey entry.artifact.key then
    throw <| IO.userError s!"unsafe manifest artifact key: {entry.artifact.key.value}"
  match entry.artifact.chunked with
  | none => pure none
  | some chunked =>
      let path := (directory / entry.artifact.key.value).toString
      let leafBytes ← IO.FS.readBinFile (path ++ ".merkle")
      match leaves? chunked.chunkCount leafBytes with
      | none => pure none
      | some leaves =>
          let prefixRange := { offset := 0, length := prefixBytes }
          let cache ← newVerifiedChunkCache
          match ← readVerifiedRangeCached? path chunked leaves cache prefixRange with
          | some (prefixRead, prefixFootprint) =>
              match decodePrefix prefixRead with
              | none => pure none
              | some header =>
                  /- IBK2 makes the framing, dictionary and directory one
                     contiguous planning extent. Coalesce it into one verified
                     range rather than re-fetching its shared chunks three
                     times; the short prefix above only discovers this extent. -/
                  let planning := planningRange header
                  match ← readVerifiedRangeCached? path chunked leaves cache planning with
                  | some (planningBytes, planningFootprint) =>
                      let dictionaryRange := dictionaryRange header
                      let directoryRange := directoryRange header
                      let dictionary := planningBytes.extract dictionaryRange.offset
                        (dictionaryRange.offset + dictionaryRange.length)
                      let directory := planningBytes.extract directoryRange.offset
                        (directoryRange.offset + directoryRange.length)
                      match predicateRange? header dictionary directory entry.predicate with
                      | none => pure (some {
                          triples := []
                          logicalBytes := planningBytes.size
                          requestedBytes := prefixFootprint.requestedBytes + planningFootprint.requestedBytes
                          fetchedBytes := prefixFootprint.fetchedBytes + planningFootprint.fetchedBytes
                          verifiedChunks := prefixFootprint.chunks + planningFootprint.chunks
                          rangeRequests := 2 })
                      | some segmentRange =>
                          match ← readVerifiedRangeCached? path chunked leaves cache segmentRange with
                          | some (segment, segmentFootprint) =>
                              let prefixRead := planningBytes.extract 0 prefixBytes
                              let triples := scanPredicateRanges { p := some entry.predicate }
                                prefixRead dictionary directory segment
                              if triples.length == entry.rows then
                                pure (some {
                                  triples
                                  logicalBytes := planningBytes.size + segment.size
                                  requestedBytes := prefixFootprint.requestedBytes + planningFootprint.requestedBytes + segmentFootprint.requestedBytes
                                  fetchedBytes := prefixFootprint.fetchedBytes + planningFootprint.fetchedBytes + segmentFootprint.fetchedBytes
                                  verifiedChunks := prefixFootprint.chunks + planningFootprint.chunks + segmentFootprint.chunks
                                  rangeRequests := 3 })
                              else pure none
                          | none => pure none
                  | none => pure none
          | none => pure none

def scanEntry (directory : System.FilePath) (entry : Entry) :
    IO (Option (List Triple × Nat)) := do
  match ← scanEntryProfile directory entry with
  | some materialized => pure (some (materialized.triples, materialized.logicalBytes))
  | none => pure none

/-- Read only a row-aligned prefix of one selected predicate segment.  Each
    range is admitted to the manifest root before it is decoded; the cache
    means increasing the prefix verifies only newly needed chunks.  `tpMatch`
    is applied here (rather than trusting a bound alone) so repeated variables
    such as `?x p ?x` cannot make a LIMIT stop before a later real match.

    This is deliberately an execution acceleration, not a new SPARQL
    evaluator: callers feed the exact candidate prefix back through the
    existing StoreDataset path for projection and result construction. -/
def scanEntryPrefixForLimit (directory : System.FilePath) (entry : Entry)
    (tp : TriplePattern) (limit : Nat) (delta : DeltaResolved) : IO (Option Materialized) := do
  if !safeLeafKey entry.artifact.key then
    throw <| IO.userError s!"unsafe manifest artifact key: {entry.artifact.key.value}"
  if limit == 0 then
    return some {
      triples := []
      logicalBytes := 0
      requestedBytes := 0
      fetchedBytes := 0
      verifiedChunks := 0
      rangeRequests := 0 }
  /- A CLEAR/DROP leaves no base triples to inspect.  Delta additions are
     supplied by `readOpsOfDelta` after this physical stage. -/
  if delta.cleared then
    return some {
      triples := []
      logicalBytes := 0
      requestedBytes := 0
      fetchedBytes := 0
      verifiedChunks := 0
      rangeRequests := 0 }
  match entry.artifact.chunked with
  | none => pure none
  | some chunked =>
      let path := (directory / entry.artifact.key.value).toString
      let leafBytes ← IO.FS.readBinFile (path ++ ".merkle")
      match leaves? chunked.chunkCount leafBytes with
      | none => pure none
      | some leaves =>
          let cache ← newVerifiedChunkCache
          let prefixRange := { offset := 0, length := prefixBytes }
          match ← readVerifiedRangeCached? path chunked leaves cache prefixRange with
          | none => pure none
          | some (prefixRead, prefixFootprint) =>
              match decodePrefix prefixRead with
              | none => pure none
              | some header =>
                  let planning := planningRange header
                  match ← readVerifiedRangeCached? path chunked leaves cache planning with
                  | none => pure none
                  | some (planningBytes, planningFootprint) =>
                      let dictionaryRange := dictionaryRange header
                      let directoryRange := directoryRange header
                      let dictionary := planningBytes.extract dictionaryRange.offset
                        (dictionaryRange.offset + dictionaryRange.length)
                      let directory := planningBytes.extract directoryRange.offset
                        (directoryRange.offset + directoryRange.length)
                      match predicateRange? header dictionary directory entry.predicate with
                      | none =>
                          pure (some {
                            triples := []
                            logicalBytes := planningBytes.size
                            requestedBytes := prefixFootprint.requestedBytes + planningFootprint.requestedBytes
                            fetchedBytes := prefixFootprint.fetchedBytes + planningFootprint.fetchedBytes
                            verifiedChunks := prefixFootprint.chunks + planningFootprint.chunks
                            rangeRequests := 2 })
                      | some segmentRange =>
                          /- A bounded scan cannot count every decoded row,
                             but the canonical fixed-width segment length must
                             still agree with the manifest's exact planning
                             cardinality before any prefix is admitted. -/
                          if segmentRange.length / 16 != entry.rows then pure none else
                          let rowBytes := 16
                          let step := max rowBytes ((chunked.chunkBytes / rowBytes) * rowBytes)
                          let initial := min segmentRange.length step
                          let bound := patternBoundFor tp Binding.empty
                          let rec readUntil : Nat → Nat → Nat → Nat → Nat → IO (Option Materialized)
                            | 0, _, _, _, _ => pure none
                            | fuel + 1, prefixLength, requests, fetched, chunks => do
                            let segmentPrefix := { offset := segmentRange.offset, length := prefixLength }
                            match ← readVerifiedRangeCached? path chunked leaves cache segmentPrefix with
                            | none => pure none
                            | some (segmentBytes, footprint) =>
                                let candidates := (scanPredicateSegmentPrefix bound prefixRead dictionary directory segmentBytes)
                                  |>.filter fun triple => (tpMatch tp triple Binding.empty).isSome
                                /- A tombstoned base row cannot satisfy LIMIT.
                                   Keep scanning until this surviving prefix is
                                   sufficient; additions stay in the normal
                                   merge-on-read path and therefore cannot
                                   cause an incomplete early stop. -/
                                let surviving := candidates.filter fun triple => !Graph.mem triple delta.removed
                                if surviving.length >= limit || prefixLength == segmentRange.length then
                                  pure (some {
                                    triples := surviving.take limit
                                    logicalBytes := planningBytes.size + prefixLength
                                    requestedBytes := prefixFootprint.requestedBytes + planningFootprint.requestedBytes + requests + footprint.requestedBytes
                                    fetchedBytes := prefixFootprint.fetchedBytes + planningFootprint.fetchedBytes + fetched + footprint.fetchedBytes
                                    verifiedChunks := prefixFootprint.chunks + planningFootprint.chunks + chunks + footprint.chunks
                                    rangeRequests := 2 + requests + 1 })
                                else
                                  readUntil fuel (min segmentRange.length (prefixLength + step))
                                    (requests + 1) (fetched + footprint.fetchedBytes) (chunks + footprint.chunks)
                          if initial == 0 then pure none
                          else readUntil (segmentRange.length / step + 1) initial 0 0 0

/-- Manifest-order limited counterpart of `scanEntries`.  The per-entry
    prefix reader is only asked for the rows still needed, so a LIMIT satisfied
    in an early artifact never opens later selected artifacts. -/
def scanEntriesPrefixForLimit (directory : System.FilePath) (tp : TriplePattern)
    (limit : Nat) (delta : DeltaResolved) : List Entry → List Triple → Materialized → IO (Option Materialized)
  | [], triples, totals => pure (some { totals with triples := triples })
  | entry :: rest, triples, totals =>
      if triples.length >= limit then pure (some { totals with triples := triples.take limit })
      else do
        let remaining := limit - triples.length
        match ← scanEntryPrefixForLimit directory entry tp remaining delta with
        | none => pure none
        | some materialized =>
            scanEntriesPrefixForLimit directory tp limit delta rest (triples ++ materialized.triples)
              { triples := []
                logicalBytes := totals.logicalBytes + materialized.logicalBytes
                requestedBytes := totals.requestedBytes + materialized.requestedBytes
                fetchedBytes := totals.fetchedBytes + materialized.fetchedBytes
                verifiedChunks := totals.verifiedChunks + materialized.verifiedChunks
                rangeRequests := totals.rangeRequests + materialized.rangeRequests }

def scanEntries (directory : System.FilePath) : List Entry →
    IO (Option (List Triple × Nat))
  | [] => pure (some ([], 0))
  | entry :: rest => do
      match ← scanEntry directory entry, ← scanEntries directory rest with
      | some (head, headBytes), some (tail, tailBytes) => pure (some (head ++ tail, headBytes + tailBytes))
      | _, _ => pure none

def readOpsOf (triples : List Triple) : BackendReadOps :=
  { search := fun bound => tripleMatchesBound bound triples
    estimate := fun bound => (tripleMatchesBound bound triples).length
    predicatePresent := fun predicate => !(tripleMatchesBound { p := some predicate } triples).isEmpty }

/-- Read the default-graph DLOG sidecar.  No sidecar means an empty delta;
    a malformed header or torn suffix is an admission failure, never a
    best-effort query over a potentially stale prefix. -/
def readDefaultDelta? (directory : System.FilePath) : IO (Option DeltaResolved) := do
  let baseEpoch ← CompactedEpoch.read? directory
  let path := directory / "deltas.dlog"
  try
    let bytes ← IO.FS.readBinFile path
    match parseLog bytes.toList with
    | some (batches, []) =>
        pure (some (foldDeltaBatches (filterBatchesSinceEpoch baseEpoch batches) none))
    | _ => pure none
  catch _ =>
    if (← path.pathExists) then pure none else pure (some deltaResolvedEmpty)

/-- The same compact backend seam used for a base-only materialisation, but
    composed with the already-replayed default-graph delta.  The merge itself
    is the existing Lean `mergeOnRead` definition whose membership theorem is
    in `RDF.StoreDeltaMerge`; this wrapper deliberately adds no second update
    semantics. -/
def readOpsOfDelta (triples : List Triple) (delta : DeltaResolved) : BackendReadOps :=
  let base := readOpsOf triples
  { search := fun bound => mergeOnRead (base.search bound) delta bound
    estimate := fun bound => (mergeOnRead (base.search bound) delta bound).length
    predicatePresent := fun predicate =>
      base.predicatePresent predicate || deltaAddedHasPredicate delta.added predicate }

end Harness.ShardMerkleMaterialize
