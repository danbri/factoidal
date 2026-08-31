/- Merkle-verified, paged IBK3 predicate scan.

   This executable is the narrow native reference for a future Shardborough
   Push Worker. It reads only the IBK3 header, a bounded row prefix, PTD1
   planning bytes, and the term pages referenced by that prefix. Each file
   range is admitted through the SBM2 chunk commitment before pure Lean turns
   it into RDF triples. -/
import Harness.PosixRangeIO
import L4Factoidal.Storage.IndexedBlockWireV3
import L4Factoidal.Storage.ShardManifest

namespace Harness.IndexedBlockV3MerkleScan

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

private def addRead (total : Counters) (read : VerifiedReadFootprint) : Counters :=
  { requestedBytes := total.requestedBytes + read.requestedBytes
    fetchedBytes := total.fetchedBytes + read.fetchedBytes
    chunks := total.chunks + read.chunks
    requests := total.requests + 1 }

private def addCounters (left right : Counters) : Counters :=
  { requestedBytes := left.requestedBytes + right.requestedBytes
    fetchedBytes := left.fetchedBytes + right.fetchedBytes
    chunks := left.chunks + right.chunks
    requests := left.requests + right.requests }

structure ScanResult where
  triples : List Triple
  counters : Counters
  artifactBytes : Nat

private def ioRange (range : L4Factoidal.Storage.IndexedBlockWireV3.ByteRange) :
    L4Factoidal.Storage.IndexedBlockWireV2.ByteRange :=
  { offset := range.offset, length := range.length }

private def predicate? (text : String) : Option WfIri :=
  if h : isIri text then some ⟨text, h⟩ else none

private def readManifest (directory : System.FilePath) : IO ByteArray :=
  IO.FS.readBinFile (directory / "manifest.sbm2")

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

private def scanEntry (directory : System.FilePath) (predicate : WfIri) (rowLimit : Nat)
    (entry : Entry) : IO (Option ScanResult) := do
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

private def scanEntries (directory : System.FilePath) (predicate : WfIri) (limit : Nat) :
    List Entry → List Triple → Counters → Nat → IO (Option (List Triple × Counters × Nat))
  | [], triples, counters, opened => pure (some (triples, counters, opened))
  | entry :: rest, triples, counters, opened =>
      if triples.length >= limit then pure (some (triples.take limit, counters, opened)) else do
        match ← scanEntry directory predicate (limit - triples.length) entry with
        | none => pure none
        | some result =>
            scanEntries directory predicate limit rest (triples ++ result.triples)
              (addCounters counters result.counters) (opened + 1)

private def run (directoryText iriText limit : String) : IO UInt32 := do
  match predicate? iriText, limit.toNat? with
  | some predicate, some rowLimit =>
      let directory := System.FilePath.mk directoryText
      let manifestBytes ← readManifest directory
      match decode? manifestBytes with
      | none => IO.eprintln "l4block-id-v3-merkle-scan rejected: malformed SBM2 manifest"; return 1
      | some manifest =>
          if !rangeCommitted manifest || manifest.layout != "predicate-ibk3-ptd1-merkle-v0" then
            IO.eprintln "l4block-id-v3-merkle-scan rejected: not an IBK3 range-committed manifest"; return 1
          let entries := selectAll manifest predicate
          if entries.isEmpty then IO.println s!"l4block-id-v3-merkle-scan rows=0 predicate={iriText} artifacts=0"; return 0
          match ← scanEntries directory predicate rowLimit entries [] {} 0 with
          | none => IO.eprintln "l4block-id-v3-merkle-scan rejected: manifest entry or verified range"; return 1
          | some (triples, counters, opened) =>
              IO.println s!"l4block-id-v3-merkle-scan rows={triples.length} predicate={iriText} artifacts={opened}/{entries.length} logical-read-bytes={counters.requestedBytes} fetched-bytes={counters.fetchedBytes} verified-chunks={counters.chunks} range-requests={counters.requests}"
              return 0
  | none, _ => IO.eprintln s!"l4block-id-v3-merkle-scan invalid predicate IRI: {iriText}"; return 2
  | _, none => IO.eprintln "l4block-id-v3-merkle-scan LIMIT must be a natural number"; return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | [directory, predicate, limit] =>
      try run directory predicate limit
      catch error => IO.eprintln s!"l4block-id-v3-merkle-scan failure: {error}"; return 1
  | _ => IO.eprintln "usage: l4block-id-v3-merkle-scan SHARD-DIR PREDICATE-IRI LIMIT"; return 2

end Harness.IndexedBlockV3MerkleScan

def main (args : List String) : IO UInt32 := Harness.IndexedBlockV3MerkleScan.main args
