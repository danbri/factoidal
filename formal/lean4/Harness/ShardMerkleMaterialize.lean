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
                  match ← readVerifiedRange? path chunked leaves (dictionaryRange header),
                      ← readVerifiedRange? path chunked leaves (directoryRange header) with
                  | some dictionary, some directory =>
                      match predicateRange? header dictionary directory entry.predicate with
                      | none => pure (some ([], prefixRead.size + dictionary.size + directory.size))
                      | some segmentRange =>
                          match ← readVerifiedRange? path chunked leaves segmentRange with
                          | none => pure none
                          | some segment =>
                              let triples := scanPredicateRanges { p := some entry.predicate }
                                prefixRead dictionary directory segment
                              if triples.length == entry.rows then
                                pure (some (triples, prefixRead.size + dictionary.size + directory.size + segment.size))
                              else pure none
                  | _, _ => pure none

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
