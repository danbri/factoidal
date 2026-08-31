/- Reusable physical publication of an already-admitted RDF graph as fresh
   predicate-local IBK2 or IBK3 artifacts and an SBM2 Merkle manifest. -/
import L4Factoidal.Storage.PredicateBlocks
import L4Factoidal.Storage.IndexedBlockWireV2
import L4Factoidal.Storage.IndexedBlockWireV3
import L4Factoidal.Storage.SubjectRowIndexWire
import L4Factoidal.Storage.SubjectRowIndexWireV2
import L4Factoidal.Storage.TermLocalIndex
import L4Factoidal.Storage.TermLocalIndexWire
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.Storage.ChunkedArtifact
import L4Factoidal.Crypto.SHA2

namespace Harness.ShardPublish

open L4Factoidal.Storage.PredicateBlocks
open L4Factoidal.Storage.IndexedBlockWireV2
open L4Factoidal.Storage.ShardManifest
open L4Factoidal.Storage.ChunkedArtifact
open L4Factoidal.Crypto

private def chunkBytes : Nat := 65536

private inductive PublishFormat where
  | ibk2
  | ibk3

private def artifactName : PublishFormat → Nat → String
  | .ibk2, ordinal => s!"predicate-{ordinal}.ibk2"
  | .ibk3, ordinal => s!"predicate-{ordinal}.ibk3"

private def encodeBlock? : PublishFormat → L4Factoidal.Storage.IndexedBlock.Block → Option ByteArray
  | .ibk2, block => L4Factoidal.Storage.IndexedBlockWireV2.encode? block
  | .ibk3, block => L4Factoidal.Storage.IndexedBlockWireV3.encode? block

private structure PublishState where
  tripleCount : Nat := 0
  nextOrdinal : Nat := 0
  entriesRev : List Entry := []
  linesRev : List String := []

private def publishBlocks (format : PublishFormat) (output : String) : PublishState →
    List (L4Factoidal.RDF.WfIri × L4Factoidal.Storage.IndexedBlock.Block) → IO PublishState
  | state, [] => pure state
  | state, (predicate, block) :: rest => do
      match encodeBlock? format block with
      | none => throw <| IO.userError s!"unsupported block for {predicate.val}"
      | some bytes =>
          let ordinal := state.nextOrdinal
          let name := artifactName format ordinal
          IO.FS.writeBinFile (output ++ "/" ++ name) bytes
          let digest := sha256 bytes
          let chunked ← match fromChunks? chunkBytes (chunksOf chunkBytes bytes) with
            | some value => pure value
            | none => throw <| IO.userError s!"could not commit fixed chunks for {predicate.val}"
          let leaves := (chunksOf chunkBytes bytes).map L4Factoidal.Storage.BlockMerkle.leaf
          let proofBytes := ByteArray.mk (leaves.flatMap (fun value => value.data.toList) |>.toArray)
          IO.FS.writeBinFile (output ++ "/" ++ name ++ ".merkle") proofBytes
          let subjectIndex ← match format with
            | .ibk2 => pure none
            | .ibk3 =>
                let index : L4Factoidal.Storage.SubjectRowIndexWireV2.Index :=
                  { targetIBKSha256 := digest
                    rowCount := block.rows.size
                    pairs := L4Factoidal.Storage.SubjectRowIndexWire.pairsOfRows block.rows |>.toArray }
                match L4Factoidal.Storage.SubjectRowIndexWireV2.encode? index with
                | none => throw <| IO.userError s!"could not encode SRI2 index for {predicate.val}"
                | some indexBytes =>
                    let indexName := name ++ ".sri2"
                    IO.FS.writeBinFile (output ++ "/" ++ indexName) indexBytes
                    let indexDigest := sha256 indexBytes
                    let indexChunked ← match fromChunks? chunkBytes (chunksOf chunkBytes indexBytes) with
                      | some value => pure value
                      | none => throw <| IO.userError s!"could not commit SRI2 chunks for {predicate.val}"
                    let indexLeaves := (chunksOf chunkBytes indexBytes).map L4Factoidal.Storage.BlockMerkle.leaf
                    IO.FS.writeBinFile (output ++ "/" ++ indexName ++ ".merkle")
                      (ByteArray.mk (indexLeaves.flatMap (fun value => value.data.toList) |>.toArray))
                    pure (some
                      { key := { value := indexName }
                        bytes := indexBytes.size
                        sha256 := indexDigest
                        chunked := some indexChunked })
          let termIndex ← match format with
            | .ibk2 => pure none
            | .ibk3 =>
                let index : L4Factoidal.Storage.TermLocalIndexWire.Index :=
                  { targetIBKSha256 := digest
                    entries := L4Factoidal.Storage.TermLocalIndex.entriesOf block.dict }
                match L4Factoidal.Storage.TermLocalIndexWire.encode? index with
                | none => throw <| IO.userError s!"could not encode TLI1 index for {predicate.val}"
                | some indexBytes =>
                    let indexName := name ++ ".tli1"
                    IO.FS.writeBinFile (output ++ "/" ++ indexName) indexBytes
                    let indexDigest := sha256 indexBytes
                    let indexChunked ← match fromChunks? chunkBytes (chunksOf chunkBytes indexBytes) with
                      | some value => pure value
                      | none => throw <| IO.userError s!"could not commit TLI1 chunks for {predicate.val}"
                    let indexLeaves := (chunksOf chunkBytes indexBytes).map L4Factoidal.Storage.BlockMerkle.leaf
                    IO.FS.writeBinFile (output ++ "/" ++ indexName ++ ".merkle")
                      (ByteArray.mk (indexLeaves.flatMap (fun value => value.data.toList) |>.toArray))
                    pure (some
                      { key := { value := indexName }
                        bytes := indexBytes.size
                        sha256 := indexDigest
                        chunked := some indexChunked })
          let entry : Entry :=
            { predicate
              artifact := { key := { value := name }, bytes := bytes.size, sha256 := digest, chunked := some chunked }
              subjectIndex
              termIndex
              rows := block.rows.size
              ordinal }
          publishBlocks format output
            { tripleCount := state.tripleCount + block.rows.size
              nextOrdinal := ordinal + 1
              entriesRev := entry :: state.entriesRev
              linesRev := s!"{ordinal}\t{predicate.val}\t{name}\t{block.rows.size}\t{bytes.size}\t{bytesToHex digest}\t{name}.merkle" :: state.linesRev }
            rest

/-- Publish an already-admitted graph without routing it back through a text
    syntax.  The target must be fresh: a failed publish has no manifest and
    cannot be opened as a collection. -/
private def publishTriplesAs (format : PublishFormat) (registryVersion : String)
    (output : String) (sourceIdentity : ByteArray) (layout : String)
    (triples : List L4Factoidal.RDF.Triple) : IO Nat := do
  let outputPath := System.FilePath.mk output
  if ← (outputPath / "manifest.sbm2").pathExists then
    throw <| IO.userError s!"refusing to replace committed collection at {output}; choose a fresh output directory"
  if ← (outputPath / "manifest.sbm1").pathExists then
    throw <| IO.userError s!"refusing to replace committed legacy collection at {output}; choose a fresh output directory"
  IO.FS.createDirAll outputPath
  let published ← publishBlocks format output {} (blocksOfBuckets (addTriples {} triples))
  let entries := published.entriesRev.reverse
  let lines := published.linesRev.reverse
  let version := match format with | .ibk2 => 2 | .ibk3 => 5
  let manifest : Manifest :=
    { version, sourceIdentity, termRegistryVersion := registryVersion, layout, entries }
  match L4Factoidal.Storage.ShardManifest.encode? manifest with
  | none => throw <| IO.userError "could not encode structurally valid SBM2 manifest"
  | some manifestBytes => IO.FS.writeBinFile (output ++ "/manifest.sbm2") manifestBytes
  IO.FS.writeFile (output ++ "/manifest.tsv")
    ("# index\tpredicate\tfile\trows\tbytes\tsha256\tmerkle-leaves\n" ++ String.intercalate "\n" lines ++ "\n")
  pure published.tripleCount

/-- Publish an already-admitted graph in the IBK2 physical layout. -/
def publishTriples (output : String) (sourceIdentity : ByteArray)
    (layout : String) (triples : List L4Factoidal.RDF.Triple) : IO Nat :=
  publishTriplesAs .ibk2 "local-ibk2-dict-v0" output sourceIdentity layout triples

/-- Publish an already-admitted graph in the paged IBK3 physical layout.
    This keeps a compacted IBK3 generation queryable by the same selective
    reader as its source generation; no Turtle reparse or format downgrade is
    involved. -/
def publishTriplesV3 (output : String) (sourceIdentity : ByteArray)
    (layout : String) (triples : List L4Factoidal.RDF.Triple) : IO Nat :=
  publishTriplesAs .ibk3 "local-ibk3-ptd1-v0" output sourceIdentity layout triples

end Harness.ShardPublish
