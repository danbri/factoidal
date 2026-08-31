/- Native proof-carrying positioned-read probe for an SBM1 artifact range. -/
import Harness.PosixRangeIO
import L4Factoidal.Storage.ShardManifest

namespace Harness.ShardMerklePread

open Harness.PosixRangeIO
open L4Factoidal.Storage.ShardManifest

private def readManifest (directory : System.FilePath) : IO ByteArray := do
  try IO.FS.readBinFile (directory / "manifest.sbm2")
  catch _ => IO.FS.readBinFile (directory / "manifest.sbm1")

private def predicate? (text : String) : Option L4Factoidal.RDF.WfIri :=
  if h : L4Factoidal.RDF.isIri text then some ⟨text, h⟩ else none

private def run (directory iri : String) (requested : Option (Nat × Nat)) : IO UInt32 := do
  match predicate? iri with
  | none => IO.eprintln s!"l4block-shard-merkle-pread invalid predicate IRI: {iri}"; return 2
  | some predicate =>
      let manifestBytes ← readManifest (System.FilePath.mk directory)
      match decode? manifestBytes with
      | some manifest =>
          match select? manifest predicate with
          | some entry =>
              match entry.artifact.chunked with
              | some chunked =>
                  let artifactPath := directory ++ "/" ++ entry.artifact.key.value
                  let sidecar ← IO.FS.readBinFile (artifactPath ++ ".merkle")
                  match leaves? chunked.chunkCount sidecar with
                  | some hashes =>
                      let range := match requested with
                        | some (offset, length) => { offset, length }
                        | none => { offset := 0, length := min chunked.chunkBytes entry.artifact.bytes }
                      match ← readVerifiedRange? artifactPath chunked hashes range with
                      | some bytes =>
                          let firstChunk := range.offset / chunked.chunkBytes
                          let lastChunk := (range.offset + range.length - 1) / chunked.chunkBytes
                          IO.println s!"l4block-shard-merkle-pread predicate={iri} verified-bytes={bytes.size} offset={range.offset} chunks={firstChunk}-{lastChunk} root-bytes={chunked.root.size}"
                          return 0
                      | none => IO.eprintln "l4block-shard-merkle-pread rejected: chunk/proof/range verification failed"; return 1
                  | none => IO.eprintln "l4block-shard-merkle-pread rejected: malformed leaf-hash sidecar"; return 1
              | none => IO.eprintln "l4block-shard-merkle-pread rejected: SBM1 entry lacks chunk commitment"; return 1
          | none => IO.eprintln "l4block-shard-merkle-pread predicate absent from manifest"; return 1
      | none => IO.eprintln "l4block-shard-merkle-pread rejected: malformed SBM1 manifest"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [directory, iri] => try run directory iri none catch e => IO.eprintln s!"l4block-shard-merkle-pread failure: {e}"; return 1
  | [directory, iri, offset, length] =>
      match offset.toNat?, length.toNat? with
      | some start, some count =>
          try run directory iri (some (start, count)) catch e => IO.eprintln s!"l4block-shard-merkle-pread failure: {e}"; return 1
      | _, _ => IO.eprintln "l4block-shard-merkle-pread offset and length must be natural numbers"; return 2
  | _ => IO.eprintln "usage: l4block-shard-merkle-pread SHARD-DIR PREDICATE-IRI [OFFSET LENGTH]"; return 2

end Harness.ShardMerklePread

def main (args : List String) : IO UInt32 := Harness.ShardMerklePread.main args
