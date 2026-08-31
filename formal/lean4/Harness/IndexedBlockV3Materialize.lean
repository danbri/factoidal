/- Importable native physical reader for IBK3 predicate-local manifest entries.
   Host I/O is here; the byte layout and range executor remain pure Lean in
   L4Factoidal.Storage.IndexedBlockWireV3. -/
import Harness.PosixRangeIO
import L4Factoidal.Storage.IndexedBlockWireV3
import L4Factoidal.Storage.ShardManifest

namespace Harness.IndexedBlockV3Materialize

open Harness.PosixRangeIO
open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.ChunkedArtifact
open L4Factoidal.Storage.ShardManifest
open L4Factoidal.Storage.BlockMerkle

structure Counters where
  requestedBytes : Nat := 0
  fetchedBytes : Nat := 0
  chunks : Nat := 0
  requests : Nat := 0

def addCounters (left right : Counters) : Counters :=
  { requestedBytes := left.requestedBytes + right.requestedBytes
    fetchedBytes := left.fetchedBytes + right.fetchedBytes
    chunks := left.chunks + right.chunks
    requests := left.requests + right.requests }

private def addRead (total : Counters) (read : VerifiedReadFootprint) : Counters :=
  { requestedBytes := total.requestedBytes + read.requestedBytes
    fetchedBytes := total.fetchedBytes + read.fetchedBytes
    chunks := total.chunks + read.chunks
    requests := total.requests + 1 }

structure ScanResult where
  triples : List Triple
  counters : Counters
  artifactBytes : Nat

/-- Manifest artifact keys denote leaf files, never paths supplied by a query.
    Keep the same admission rule as the earlier IBK2 range materializer. -/
def safeLeafKey (key : ArtifactKey) : Bool :=
  !key.value.isEmpty && !(key.value.contains '/') && !(key.value.contains '\\')

private def ioRange (range : L4Factoidal.Storage.IndexedBlockWireV3.ByteRange) :
    L4Factoidal.Storage.IndexedBlockWireV2.ByteRange :=
  { offset := range.offset, length := range.length }

private def readPages (path : String) (ref : Ref) (leaves : List Digest)
    (cache : IO.Ref (List VerifiedChunk)) : List L4Factoidal.Storage.IndexedBlockWireV3.ByteRange → Counters →
    IO (Option (List (L4Factoidal.Storage.IndexedBlockWireV3.ByteRange × ByteArray) × Counters))
  | [], total => pure (some ([], total))
  | range :: rest, total => do
      match ← readVerifiedRangeCached? path ref leaves cache (ioRange range) with
      | none => pure none
      | some (bytes, footprint) =>
          match ← readPages path ref leaves cache rest (addRead total footprint) with
          | none => pure none
          | some (tail, counters) => pure (some ((range, bytes) :: tail, counters))

def scanEntry (directory : System.FilePath) (predicate : WfIri) (rowLimit : Nat)
    (entry : Entry) : IO (Option ScanResult) := do
  if !safeLeafKey entry.artifact.key then return none
  match entry.artifact.chunked with
  | none => pure none
  | some ref =>
      let path := (directory / entry.artifact.key.value).toString
      let leafBytes ← IO.FS.readBinFile (path ++ ".merkle")
      match leaves? ref.chunkCount leafBytes with
      | none => pure none
      | some leaves =>
          let cache ← newVerifiedChunkCache
          let headerRange : L4Factoidal.Storage.IndexedBlockWireV3.ByteRange :=
            { offset := 0, length := L4Factoidal.Storage.IndexedBlockWireV3.prefixBytes }
          match ← readVerifiedRangeCached? path ref leaves cache (ioRange headerRange) with
          | some (headerBytes, headerFootprint) =>
              match L4Factoidal.Storage.IndexedBlockWireV3.decodePrefix headerBytes with
              | some header =>
                  match L4Factoidal.Storage.IndexedBlockWireV3.dictionaryPrefixRange header with
                  | some ptdRange =>
                      match ← readVerifiedRangeCached? path ref leaves cache (ioRange ptdRange) with
                      | some (ptdPrefix, ptdFootprint) =>
                          match L4Factoidal.Storage.IndexedBlockWireV3.dictionaryDirectoryRange? header ptdPrefix with
                          | some directoryRange =>
                              match ← readVerifiedRangeCached? path ref leaves cache (ioRange directoryRange) with
                              | some (directoryBytes, directoryFootprint) =>
                                  let wantedRows := min header.rowCount rowLimit
                                  let rowRange := L4Factoidal.Storage.IndexedBlockWireV3.rowsRange header
                                  let rowPrefix : L4Factoidal.Storage.IndexedBlockWireV3.ByteRange :=
                                    { offset := rowRange.offset, length := wantedRows * L4Factoidal.Storage.IndexedBlockWireV3.rowBytes }
                                  match ← readVerifiedRangeCached? path ref leaves cache (ioRange rowPrefix) with
                                  | some (rowBytes, rowFootprint) =>
                                      let initial := addRead (addRead (addRead (addRead {} headerFootprint) ptdFootprint) directoryFootprint) rowFootprint
                                      match L4Factoidal.Storage.IndexedBlockWireV3.dictionaryPagesForRowPrefix? header ptdPrefix directoryBytes rowBytes with
                                      | some ranges =>
                                          match ← readPages path ref leaves cache ranges initial with
                                          | some (pages, counters) =>
                                              match L4Factoidal.Storage.IndexedBlockWireV3.scanRowPrefixPages { p := some predicate }
                                                  headerBytes rowBytes ptdPrefix directoryBytes pages with
                                              | some triples =>
                                                  if triples.length == wantedRows then
                                                    pure (some { triples, counters, artifactBytes := entry.artifact.bytes })
                                                  else pure none
                                              | none => pure none
                                          | none => pure none
                                      | none => pure none
                                  | none => pure none
                              | none => pure none
                          | none => pure none
                      | none => pure none
                  | none => pure none
              | none => pure none
          | none => pure none

def scanEntries (directory : System.FilePath) (predicate : WfIri) (limit : Nat) :
    List Entry → List Triple → Counters → Nat → IO (Option (List Triple × Counters × Nat))
  | [], triples, counters, opened => pure (some (triples, counters, opened))
  | entry :: rest, triples, counters, opened =>
      if triples.length >= limit then pure (some (triples.take limit, counters, opened)) else do
        match ← scanEntry directory predicate (limit - triples.length) entry with
        | none => pure none
        | some result =>
            scanEntries directory predicate limit rest (triples ++ result.triples)
              (addCounters counters result.counters) (opened + 1)

/-- Materialise every row from the entries selected by a constant-predicate
    physical plan. This is the conservative bridge for the general SPARQL
    evaluator; bounded predicate scans use `scanEntries` directly. -/
def materializeEntries (directory : System.FilePath) : List Entry → IO (Option (List Triple × Counters))
  | [] => pure (some ([], {}))
  | entry :: rest => do
      match ← scanEntry directory entry.predicate entry.rows entry,
          ← materializeEntries directory rest with
      | some current, some (later, counters) =>
          pure (some (current.triples ++ later, addCounters current.counters counters))
      | _, _ => pure none

end Harness.IndexedBlockV3Materialize
