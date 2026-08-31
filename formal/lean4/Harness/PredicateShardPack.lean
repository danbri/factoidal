/- Persist one independently decodable IBK2 artifact per predicate, with both
   a human-inspectable TSV and a strict host-neutral SBM0 Shardborough
   manifest. -/
import L4Factoidal.Storage.PredicateBlocks
import L4Factoidal.Storage.IndexedBlockWireV2
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.Storage.ChunkedArtifact
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.Utf8Stream
import L4Factoidal.Syntax.TurtleChunkFold
import L4Factoidal.Crypto.SHA2

namespace Harness.PredicateShardPack

open L4Factoidal.Syntax
open L4Factoidal.Storage.PredicateBlocks
open L4Factoidal.Storage.IndexedBlockWireV2
open L4Factoidal.Storage.ShardManifest
open L4Factoidal.Storage.ChunkedArtifact
open L4Factoidal.Crypto

private def chunkBytes : Nat := 65536
private def inputChunkBytes : USize := 65536
/-- Keep decoding latency small while publishing roughly four MiB batches.
    This is a bounded first block-sizing policy; later compaction may use
    measured encoded-byte targets rather than source-byte batches. -/
private def publicationChunkCount : Nat := 64

/-- Bounded first-pass information needed to preserve the reference packer's
    generated-blank-node and source-identity contracts. -/
private structure SourcePrepass where
  bnodePrefix : String
  sourceIdentity : ByteArray

/-- Host I/O is deliberately tail-recursive/`partial`; it is not semantic
    parser recursion. Each iteration retains only UTF-8 carry, underscore-run
    state and SHA-256 state. -/
private partial def prepassHandle (handle : IO.FS.Handle) (utf8 : Utf8Stream)
    (underscores : UnderscoreRun) (digest : Sha256Stream) : IO SourcePrepass := do
  let bytes ← handle.read inputChunkBytes
  if bytes.isEmpty then
    match utf8.finish with
    | .error message => throw <| IO.userError s!"l4block-shard-pack UTF-8 error: {message}"
    | .ok _ =>
        pure { bnodePrefix := freshBnodePrefixOfLongest underscores.longest
               sourceIdentity := digest.finish }
  else
    match utf8.feed bytes with
    | .error message => throw <| IO.userError s!"l4block-shard-pack UTF-8 error: {message}"
    | .ok (text, nextUtf8) =>
        prepassHandle handle nextUtf8 (underscores.feedChars text.toList) (digest.update bytes)

private def prepassFile (input : System.FilePath) : IO SourcePrepass :=
  IO.FS.withFile input .read fun handle => prepassHandle handle Utf8Stream.init {} Sha256Stream.init

/- The fold accumulator is deliberately a reverse list of triples completed
   since the current decoded input chunk.  It is reset after publication, so
   the packer never builds a graph-wide predicate map in memory. -/
private def ingestStep (accRev : List L4Factoidal.RDF.Triple)
    (triples : List L4Factoidal.RDF.Triple) : List L4Factoidal.RDF.Triple :=
  triples.reverse ++ accRev

/-- Publication metadata is small even for a large source: one manifest row
    and one TSV row per immutable output block, never the source triples. -/
private structure PackState where
  tripleCount : Nat := 0
  nextOrdinal : Nat := 0
  entriesRev : List Entry := []
  linesRev : List String := []

private def publishBlocks (output : String) : PackState → List (L4Factoidal.RDF.WfIri × L4Factoidal.Storage.IndexedBlock.Block) → IO PackState
  | state, [] => pure state
  | state, (predicate, block) :: rest => do
      match L4Factoidal.Storage.IndexedBlockWireV2.encode? block with
      | none => throw <| IO.userError s!"unsupported block for {predicate.val}"
      | some bytes =>
          let ordinal := state.nextOrdinal
          let name := s!"predicate-{ordinal}.ibk2"
          IO.FS.writeBinFile (output ++ "/" ++ name) bytes
          let digest := sha256 bytes
          let chunked ← match fromChunks? chunkBytes (chunksOf chunkBytes bytes) with
            | some value => pure value
            | none => throw <| IO.userError s!"could not commit fixed chunks for {predicate.val}"
          let leaves := (chunksOf chunkBytes bytes).map L4Factoidal.Storage.BlockMerkle.leaf
          let proofBytes := ByteArray.mk (leaves.flatMap (fun value => value.data.toList) |>.toArray)
          IO.FS.writeBinFile (output ++ "/" ++ name ++ ".merkle") proofBytes
          let entry : Entry :=
            { predicate
              artifact := { key := { value := name }, bytes := bytes.size, sha256 := digest, chunked := some chunked }
              rows := block.rows.size
              ordinal }
          publishBlocks output
            { tripleCount := state.tripleCount + block.rows.size
              nextOrdinal := ordinal + 1
              entriesRev := entry :: state.entriesRev
              linesRev := s!"{ordinal}\t{predicate.val}\t{name}\t{block.rows.size}\t{bytes.size}\t{bytesToHex digest}\t{name}.merkle" :: state.linesRev }
            rest

/-- Commit all complete statements seen since the prior decoded input chunk.
    A single very large Turtle statement remains an intentional bounded-input
    exception: its grammar requires retaining the unfinished statement. -/
private def publishBatch (output : String) (state : PackState)
    (triples : List L4Factoidal.RDF.Triple) : IO PackState :=
  publishBlocks output state (blocksOfBuckets (addTriples {} triples))

/-- Second bounded pass: decoded chunks are handed to the grammar-validated
    fold and their completed batches are published immediately. Its
    independently streamed source digest must equal the first-pass commitment
    before the manifest commits any such artifacts into a readable store. -/
private partial def ingestHandle (output : String) (handle : IO.FS.Handle) (expected : ByteArray) (utf8 : Utf8Stream)
    (fold : TurtleChunkFoldState (List L4Factoidal.RDF.Triple)) (digest : Sha256Stream)
    (published : PackState) (chunksSincePublish : Nat) : IO PackState := do
  let bytes ← handle.read inputChunkBytes
  if bytes.isEmpty then
    match utf8.finish with
    | .error message => throw <| IO.userError s!"l4block-shard-pack UTF-8 error: {message}"
    | .ok _ =>
        if digest.finish != expected then
          throw <| IO.userError "l4block-shard-pack input changed between pre-pass and parse pass"
        match fold.finish ingestStep with
        | .error error => throw <| IO.userError s!"l4block-shard-pack Turtle parse error at {error.pos}: {error.msg}"
        | .ok triples => publishBatch output published triples.reverse
  else
    match utf8.feed bytes with
    | .error message => throw <| IO.userError s!"l4block-shard-pack UTF-8 error: {message}"
    | .ok (text, nextUtf8) =>
        match fold.feed ingestStep text with
        | .error error => throw <| IO.userError s!"l4block-shard-pack Turtle parse error at {error.pos}: {error.msg}"
        | .ok nextFold =>
            let nextCount := chunksSincePublish + 1
            if nextCount < publicationChunkCount then
              ingestHandle output handle expected nextUtf8 nextFold (digest.update bytes) published nextCount
            else
              let published ← publishBatch output published nextFold.acc.reverse
              ingestHandle output handle expected nextUtf8 { nextFold with acc := [] }
                (digest.update bytes) published 0

private def ingestFile (input output : System.FilePath) (prepass : SourcePrepass) : IO PackState :=
  IO.FS.withFile input .read fun handle =>
    let fold := TurtleChunkFoldState.init prepass.bnodePrefix ingestStep []
      (some ("file://" ++ input.toString))
    ingestHandle output.toString handle prepass.sourceIdentity Utf8Stream.init fold Sha256Stream.init {} 0

private def pack (input output : String) : IO UInt32 := do
  try
    let prepass ← prepassFile input
    let outputPath := System.FilePath.mk output
    if ← (outputPath / "manifest.sbm2").pathExists then
      throw <| IO.userError s!"refusing to replace committed collection at {output}; choose a fresh output directory"
    if ← (outputPath / "manifest.sbm1").pathExists then
      throw <| IO.userError s!"refusing to replace committed legacy collection at {output}; choose a fresh output directory"
    IO.FS.createDirAll outputPath
    let published ← ingestFile input output prepass
    let entries := published.entriesRev.reverse
    let lines := published.linesRev.reverse
    let manifest : Manifest :=
      { version := 2
        sourceIdentity := prepass.sourceIdentity
        termRegistryVersion := "local-ibk2-dict-v0"
        layout := "predicate-ibk2-merkle-v2-streaming"
        entries }
    match L4Factoidal.Storage.ShardManifest.encode? manifest with
    | none => throw <| IO.userError "could not encode structurally valid SBM2 manifest"
    | some manifestBytes => IO.FS.writeBinFile (output ++ "/manifest.sbm2") manifestBytes
    IO.FS.writeFile (output ++ "/manifest.tsv")
      ("# index\tpredicate\tfile\trows\tbytes\tsha256\tmerkle-leaves\n" ++ String.intercalate "\n" lines ++ "\n")
    IO.println s!"l4block-shard-pack input={input} triples={published.tripleCount} blocks={entries.length} output={output} manifest=manifest.sbm2 chunk-bytes={chunkBytes}"
    return 0
  catch error =>
    IO.eprintln s!"l4block-shard-pack failure: {error}"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [input, output] => try pack input output catch e => IO.eprintln s!"l4block-shard-pack failure: {e}"; return 1
  | _ => IO.eprintln "usage: l4block-shard-pack INPUT.ttl OUTPUT-DIR"; return 2

end Harness.PredicateShardPack
def main (args : List String) : IO UInt32 := Harness.PredicateShardPack.main args
