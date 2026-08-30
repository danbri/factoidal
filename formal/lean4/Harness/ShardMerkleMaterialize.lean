/- Shared native-only admission edge for predicate-local SBM1 artifacts.
   It turns the four required IBK2 ranges into triples only after every range
   has been verified to the artifact's committed Merkle root. -/
import Harness.PosixRangeIO
import L4Factoidal.Storage.ShardManifest

namespace Harness.ShardMerkleMaterialize

open Harness.PosixRangeIO
open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.Storage.IndexedBlockWireV2
open L4Factoidal.Storage.ShardManifest

def safeLeafKey (key : ArtifactKey) : Bool :=
  !key.value.isEmpty && !(key.value.contains '/') && !(key.value.contains '\\')

/-- Materialise exactly the selected predicate-local artifact through four
    Merkle-verified IBK2 ranges. -/
def scanEntry (directory : System.FilePath) (entry : Entry) :
    IO (Option (List Triple × Nat)) := do
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
          match ← readVerifiedRange? path chunked leaves { offset := 0, length := prefixBytes } with
          | none => pure none
          | some prefixRead =>
              match decodePrefix prefixRead with
              | none => pure none
              | some header =>
                  /- IBK2 makes the framing, dictionary and directory one
                     contiguous planning extent. Coalesce it into one verified
                     range rather than re-fetching its shared chunks three
                     times; the short prefix above only discovers this extent. -/
                  let planning := planningRange header
                  match ← readVerifiedRange? path chunked leaves planning with
                  | none => pure none
                  | some planningBytes =>
                      let dictionaryRange := dictionaryRange header
                      let directoryRange := directoryRange header
                      let dictionary := planningBytes.extract dictionaryRange.offset
                        (dictionaryRange.offset + dictionaryRange.length)
                      let directory := planningBytes.extract directoryRange.offset
                        (directoryRange.offset + directoryRange.length)
                      match predicateRange? header dictionary directory entry.predicate with
                      | none => pure (some ([], planningBytes.size))
                      | some segmentRange =>
                          match ← readVerifiedRange? path chunked leaves segmentRange with
                          | none => pure none
                          | some segment =>
                              let prefixRead := planningBytes.extract 0 prefixBytes
                              let triples := scanPredicateRanges { p := some entry.predicate }
                                prefixRead dictionary directory segment
                              if triples.length == entry.rows then
                                pure (some (triples, planningBytes.size + segment.size))
                              else pure none

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

end Harness.ShardMerkleMaterialize
