/- Convert one existing predicate-local IBK2 artifact into a self-contained
   one-entry IBK3 SBM2 store.  This is a migration/testing publisher, not the
   eventual streaming Turtle publisher: it lets the native Push Worker exercise
   IBK3 against the already-published gene corpus. -/
import L4Factoidal.Storage.IndexedBlockWireV2
import L4Factoidal.Storage.IndexedBlockWireV3
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.Storage.ChunkedArtifact
import L4Factoidal.Crypto.SHA2

namespace Harness.IndexedBlockV3Convert

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.IndexedBlock
open L4Factoidal.Storage.ChunkedArtifact
open L4Factoidal.Storage.ShardManifest
open L4Factoidal.Crypto

private def chunkBytes : Nat := 65536

private def predicate? (text : String) : Option WfIri :=
  if h : isIri text then some ⟨text, h⟩ else none

private def leavesBytes (bytes : ByteArray) : ByteArray :=
  ByteArray.mk ((chunksOf chunkBytes bytes).map L4Factoidal.Storage.BlockMerkle.leaf |>.flatMap
    (fun leaf => leaf.data.toList) |>.toArray)

private def convert (input output predicateText : String) : IO UInt32 := do
  match predicate? predicateText with
  | none => IO.eprintln s!"l4block-id-v3-convert invalid predicate IRI: {predicateText}"; return 2
  | some predicate =>
      try
        let inputBytes ← IO.FS.readBinFile input
        match L4Factoidal.Storage.IndexedBlockWireV2.decode inputBytes with
        | none => IO.eprintln "l4block-id-v3-convert rejected: malformed IBK2 input"; return 1
        | some block =>
            let selected := scanBound { p := some predicate } block
            if selected.length != block.rows.size then
              IO.eprintln "l4block-id-v3-convert rejected: input is not predicate-local for supplied predicate"
              return 1
            match L4Factoidal.Storage.IndexedBlockWireV3.encode? block with
            | none => IO.eprintln "l4block-id-v3-convert rejected: IBK3 admission failed"; return 1
            | some bytes =>
                let outputPath := System.FilePath.mk output
                if ← outputPath.pathExists then
                  IO.eprintln s!"l4block-id-v3-convert refused: output already exists: {output}"
                  return 1
                IO.FS.createDirAll outputPath
                let name := "predicate-0.ibk3"
                IO.FS.writeBinFile (outputPath / name) bytes
                IO.FS.writeBinFile (outputPath / (name ++ ".merkle")) (leavesBytes bytes)
                match fromChunks? chunkBytes (chunksOf chunkBytes bytes) with
                | none => IO.eprintln "l4block-id-v3-convert failed: could not commit chunks"; return 1
                | some chunked =>
                    let entry : Entry :=
                      { predicate
                        artifact := { key := { value := name }, bytes := bytes.size, sha256 := sha256 bytes, chunked := some chunked }
                        rows := block.rows.size
                        ordinal := 0 }
                    let manifest : Manifest :=
                      { version := 2
                        sourceIdentity := sha256 inputBytes
                        termRegistryVersion := "local-ibk3-ptd1-v0"
                        layout := "predicate-ibk3-ptd1-merkle-v0"
                        entries := [entry] }
                    match encode? manifest with
                    | none => IO.eprintln "l4block-id-v3-convert failed: manifest admission"; return 1
                    | some manifestBytes =>
                        IO.FS.writeBinFile (outputPath / "manifest.sbm2") manifestBytes
                        IO.println s!"l4block-id-v3-convert input={input} predicate={predicateText} rows={block.rows.size} output={output} bytes={bytes.size}"
                        return 0
      catch error => IO.eprintln s!"l4block-id-v3-convert failure: {error}"; return 1

def main (args : List String) : IO UInt32 :=
  match args with
  | [input, output, predicate] => convert input output predicate
  | _ => do
      IO.eprintln "usage: l4block-id-v3-convert INPUT.ibk2 OUTPUT-DIR PREDICATE-IRI"
      pure 2

end Harness.IndexedBlockV3Convert

def main (args : List String) : IO UInt32 := Harness.IndexedBlockV3Convert.main args
