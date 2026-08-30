/- Native proof-carrying positioned-read probe for one SBM1 artifact chunk. -/
import Harness.PosixRangeIO
import L4Factoidal.Storage.ShardManifest

namespace Harness.ShardMerklePread

open Harness.PosixRangeIO
open L4Factoidal.Storage.ShardManifest

private def predicate? (text : String) : Option L4Factoidal.RDF.WfIri :=
  if h : L4Factoidal.RDF.isIri text then some ⟨text, h⟩ else none

private def run (directory iri : String) : IO UInt32 := do
  match predicate? iri with
  | none => IO.eprintln s!"l4block-shard-merkle-pread invalid predicate IRI: {iri}"; return 2
  | some predicate =>
      let manifestBytes ← IO.FS.readBinFile (System.FilePath.mk directory / "manifest.sbm1")
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
                      let wanted := min chunked.chunkBytes entry.artifact.bytes
                      match ← readVerifiedSingleChunkRange? artifactPath chunked hashes { offset := 0, length := wanted } with
                      | some bytes => IO.println s!"l4block-shard-merkle-pread predicate={iri} verified-bytes={bytes.size} chunk=0 root-bytes={chunked.root.size}"; return 0
                      | none => IO.eprintln "l4block-shard-merkle-pread rejected: chunk/proof/range verification failed"; return 1
                  | none => IO.eprintln "l4block-shard-merkle-pread rejected: malformed leaf-hash sidecar"; return 1
              | none => IO.eprintln "l4block-shard-merkle-pread rejected: SBM1 entry lacks chunk commitment"; return 1
          | none => IO.eprintln "l4block-shard-merkle-pread predicate absent from manifest"; return 1
      | none => IO.eprintln "l4block-shard-merkle-pread rejected: malformed SBM1 manifest"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [directory, iri] => try run directory iri catch e => IO.eprintln s!"l4block-shard-merkle-pread failure: {e}"; return 1
  | _ => IO.eprintln "usage: l4block-shard-merkle-pread SHARD-DIR PREDICATE-IRI"; return 2

end Harness.ShardMerklePread

def main (args : List String) : IO UInt32 := Harness.ShardMerklePread.main args
