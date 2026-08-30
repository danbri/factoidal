/- Persist one independently decodable IBK2 artifact per predicate, with both
   a human-inspectable TSV and a strict host-neutral SBM0 Shardborough
   manifest. -/
import L4Factoidal.Storage.PredicateBlocks
import L4Factoidal.Storage.IndexedBlockWireV2
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.Storage.ChunkedArtifact
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Crypto.SHA2

namespace Harness.PredicateShardPack

open L4Factoidal.Syntax
open L4Factoidal.Storage.PredicateBlocks
open L4Factoidal.Storage.IndexedBlockWireV2
open L4Factoidal.Storage.ShardManifest
open L4Factoidal.Storage.ChunkedArtifact
open L4Factoidal.Crypto

private def chunkBytes : Nat := 65536

private def pack (input output : String) : IO UInt32 := do
  let text ← IO.FS.readFile input
  match parseTurtle text (some ("file://" ++ input)) with
  | .error e => IO.eprintln s!"l4block-shard-pack Turtle parse error at {e.pos}: {e.msg}"; return 1
  | .ok graph =>
      let store := fromGraph graph
      IO.FS.createDirAll output
      let packed ← store.blocks.zipIdx.mapM fun ((predicate, block), index) => do
        match encode? block with
        | none => throw <| IO.userError s!"unsupported block for {predicate.val}"
        | some bytes =>
            let name := s!"predicate-{index}.ibk2"
            IO.FS.writeBinFile (output ++ "/" ++ name) bytes
            let digest := sha256 bytes
            let chunked ← match fromChunks? chunkBytes (chunksOf chunkBytes bytes) with
              | some value => pure value
              | none => throw <| IO.userError s!"could not commit fixed chunks for {predicate.val}"
            let entry : Entry :=
              { predicate
                artifact := { key := { value := name }, bytes := bytes.size, sha256 := digest, chunked := some chunked }
                rows := block.rows.size
                ordinal := index }
            pure (entry, s!"{index}\t{predicate.val}\t{name}\t{block.rows.size}\t{bytes.size}\t{bytesToHex digest}")
      let entries := packed.map Prod.fst
      let lines := packed.map Prod.snd
      let manifest : Manifest :=
        { version := 1
          sourceIdentity := sha256 text.toUTF8
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
        ("# index\tpredicate\tfile\trows\tbytes\tsha256\n" ++ String.intercalate "\n" lines ++ "\n")
      IO.println s!"l4block-shard-pack input={input} triples={graph.length} shards={store.blocks.length} output={output} manifests=manifest.sbm1,manifest.sbm0 chunk-bytes={chunkBytes}"
      return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [input, output] => try pack input output catch e => IO.eprintln s!"l4block-shard-pack failure: {e}"; return 1
  | _ => IO.eprintln "usage: l4block-shard-pack INPUT.ttl OUTPUT-DIR"; return 2

end Harness.PredicateShardPack
def main (args : List String) : IO UInt32 := Harness.PredicateShardPack.main args
