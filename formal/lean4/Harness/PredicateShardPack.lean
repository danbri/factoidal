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

private def ingestStep (state : Nat × Buckets) (triples : List L4Factoidal.RDF.Triple) : Nat × Buckets :=
  (state.1 + triples.length, addTriples state.2 triples)

/-- Second bounded pass: decoded chunks are handed to the grammar-validated
    fold immediately. Its independently streamed source digest must equal the
    first-pass commitment before any IBK2 artifact is published. -/
private partial def ingestHandle (handle : IO.FS.Handle) (expected : ByteArray) (utf8 : Utf8Stream)
    (fold : TurtleChunkFoldState (Nat × Buckets)) (digest : Sha256Stream) : IO (Nat × Buckets) := do
  let bytes ← handle.read inputChunkBytes
  if bytes.isEmpty then
    match utf8.finish with
    | .error message => throw <| IO.userError s!"l4block-shard-pack UTF-8 error: {message}"
    | .ok _ =>
        if digest.finish != expected then
          throw <| IO.userError "l4block-shard-pack input changed between pre-pass and parse pass"
        match fold.finish ingestStep with
        | .error error => throw <| IO.userError s!"l4block-shard-pack Turtle parse error at {error.pos}: {error.msg}"
        | .ok state => pure state
  else
    match utf8.feed bytes with
    | .error message => throw <| IO.userError s!"l4block-shard-pack UTF-8 error: {message}"
    | .ok (text, nextUtf8) =>
        match fold.feed ingestStep text with
        | .error error => throw <| IO.userError s!"l4block-shard-pack Turtle parse error at {error.pos}: {error.msg}"
        | .ok nextFold => ingestHandle handle expected nextUtf8 nextFold (digest.update bytes)

private def ingestFile (input : System.FilePath) (prepass : SourcePrepass) : IO (Nat × Buckets) :=
  IO.FS.withFile input .read fun handle =>
    let fold := TurtleChunkFoldState.init prepass.bnodePrefix ingestStep (0, {})
      (some ("file://" ++ input.toString))
    ingestHandle handle prepass.sourceIdentity Utf8Stream.init fold Sha256Stream.init

private def pack (input output : String) : IO UInt32 := do
  try
    let prepass ← prepassFile input
    let (tripleCount, buckets) ← ingestFile input prepass
    let blocks := blocksOfBuckets buckets
    IO.FS.createDirAll output
    let packed ← blocks.zipIdx.mapM fun ((predicate, block), index) => do
      match encode? block with
      | none => throw <| IO.userError s!"unsupported block for {predicate.val}"
      | some bytes =>
          let name := s!"predicate-{index}.ibk2"
          IO.FS.writeBinFile (output ++ "/" ++ name) bytes
          let digest := sha256 bytes
          let chunked ← match fromChunks? chunkBytes (chunksOf chunkBytes bytes) with
            | some value => pure value
            | none => throw <| IO.userError s!"could not commit fixed chunks for {predicate.val}"
          let leaves := (chunksOf chunkBytes bytes).map L4Factoidal.Storage.BlockMerkle.leaf
          let proofBytes := ByteArray.mk (leaves.flatMap (fun digest => digest.data.toList) |>.toArray)
          IO.FS.writeBinFile (output ++ "/" ++ name ++ ".merkle") proofBytes
          let entry : Entry :=
            { predicate
              artifact := { key := { value := name }, bytes := bytes.size, sha256 := digest, chunked := some chunked }
              rows := block.rows.size
              ordinal := index }
          pure (entry, s!"{index}\t{predicate.val}\t{name}\t{block.rows.size}\t{bytes.size}\t{bytesToHex digest}\t{name}.merkle")
    let entries := packed.map Prod.fst
    let lines := packed.map Prod.snd
    let manifest : Manifest :=
      { version := 1
        sourceIdentity := prepass.sourceIdentity
        termRegistryVersion := "local-ibk2-dict-v0"
        layout := "predicate-ibk2-merkle-v1"
        entries }
    let legacyEntries := entries.map fun entry => { entry with artifact := { entry.artifact with chunked := none } }
    let legacyManifest : Manifest := { manifest with version := 0, layout := "predicate-ibk2-v0", entries := legacyEntries }
    match L4Factoidal.Storage.ShardManifest.encode? manifest with
    | none => throw <| IO.userError "could not encode structurally valid SBM1 manifest"
    | some manifestBytes => IO.FS.writeBinFile (output ++ "/manifest.sbm1") manifestBytes
    match L4Factoidal.Storage.ShardManifest.encode? legacyManifest with
    | none => throw <| IO.userError "could not encode compatibility SBM0 manifest"
    | some manifestBytes => IO.FS.writeBinFile (output ++ "/manifest.sbm0") manifestBytes
    IO.FS.writeFile (output ++ "/manifest.tsv")
      ("# index\tpredicate\tfile\trows\tbytes\tsha256\tmerkle-leaves\n" ++ String.intercalate "\n" lines ++ "\n")
    IO.println s!"l4block-shard-pack input={input} triples={tripleCount} shards={blocks.length} output={output} manifests=manifest.sbm1,manifest.sbm0 chunk-bytes={chunkBytes}"
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
