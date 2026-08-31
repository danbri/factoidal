/- Execute one predicate-local IBK2 scan from SBM1-root-verified positioned
   ranges.  No whole-artifact read or SHA admission is used on this path: every
   byte passed to the IBK2 range decoder was checked through the artifact's
   committed fixed-chunk Merkle root. -/
import Harness.PosixRangeIO
import L4Factoidal.Storage.ShardManifest

namespace Harness.ShardMerkleScan

open Harness.PosixRangeIO
open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.IndexedBlockWireV2
open L4Factoidal.Storage.ShardManifest

private def readManifest (directory : System.FilePath) : IO ByteArray := do
  try IO.FS.readBinFile (directory / "manifest.sbm2")
  catch _ => IO.FS.readBinFile (directory / "manifest.sbm1")

private def predicate? (text : String) : Option WfIri :=
  if h : isIri text then some ⟨text, h⟩ else none

private def run (directory iri : String) : IO UInt32 := do
  match predicate? iri with
  | none => IO.eprintln s!"l4block-shard-merkle-scan invalid predicate IRI: {iri}"; return 2
  | some predicate =>
      let manifestBytes ← readManifest (System.FilePath.mk directory)
      match decode? manifestBytes with
      | none => IO.eprintln "l4block-shard-merkle-scan rejected: malformed SBM1 manifest"; return 1
      | some manifest =>
          match select? manifest predicate with
          | none => IO.println s!"l4block-shard-merkle-scan rows=0 predicate={iri} artifact=absent"; return 0
          | some entry =>
              match entry.artifact.chunked with
              | none => IO.eprintln "l4block-shard-merkle-scan rejected: SBM1 entry lacks chunk commitment"; return 1
              | some chunked =>
                  let path := directory ++ "/" ++ entry.artifact.key.value
                  let leafBytes ← IO.FS.readBinFile (path ++ ".merkle")
                  match leaves? chunked.chunkCount leafBytes with
                  | none => IO.eprintln "l4block-shard-merkle-scan rejected: malformed leaf-hash sidecar"; return 1
                  | some leaves =>
                      match ← readVerifiedRange? path chunked leaves { offset := 0, length := prefixBytes } with
                      | none => IO.eprintln "l4block-shard-merkle-scan rejected: invalid verified IBK2 prefix"; return 1
                      | some prefixRead =>
                          match decodePrefix prefixRead with
                          | none => IO.eprintln "l4block-shard-merkle-scan rejected: invalid IBK2 prefix"; return 1
                          | some header =>
                              match ← readVerifiedRange? path chunked leaves (dictionaryRange header),
                                  ← readVerifiedRange? path chunked leaves (directoryRange header) with
                              | some dictionary, some directory =>
                                  match predicateRange? header dictionary directory predicate with
                                  | none => IO.println s!"l4block-shard-merkle-scan rows=0 predicate={iri} logical-read-bytes={prefixRead.size + dictionary.size + directory.size}"; return 0
                                  | some segmentRange =>
                                      match ← readVerifiedRange? path chunked leaves segmentRange with
                                      | none => IO.eprintln "l4block-shard-merkle-scan rejected: selected segment verification failed"; return 1
                                      | some segment =>
                                          let triples := scanPredicateRanges { p := some predicate } prefixRead dictionary directory segment
                                          let logicalBytes := prefixRead.size + dictionary.size + directory.size + segment.size
                                          IO.println s!"l4block-shard-merkle-scan rows={triples.length} predicate={iri} logical-read-bytes={logicalBytes} artifact-bytes={entry.artifact.bytes} root-bytes={chunked.root.size}"
                                          return 0
                              | _, _ => IO.eprintln "l4block-shard-merkle-scan rejected: verified planning range failed"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [directory, iri] => try run directory iri catch e => IO.eprintln s!"l4block-shard-merkle-scan failure: {e}"; return 1
  | _ => IO.eprintln "usage: l4block-shard-merkle-scan SHARD-DIR PREDICATE-IRI"; return 2

end Harness.ShardMerkleScan

def main (args : List String) : IO UInt32 := Harness.ShardMerkleScan.main args
