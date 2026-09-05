/-
Harness.QuadDump — write the quads of an IBK4 generation back out as
N-Quads, one block at a time.

    l4block-quad-dump <collection-root-or-generation-dir> <output.nq>

Why this exists: a generation is the only copy of some corpora here, and a
format change needs the SAME data packed again under the new format so that
the two can be compared. Re-packing the dump reproduces the corpus rather
than approximating it with a different one.

Each block is decoded, denoted and serialised on its own, so the whole
dataset is never one value. The output is canonical N-Quads, so re-packing it
is a well-defined operation and not a guess about the writer's choices.

This reads blocks; it applies no delta log. A generation with a non-empty
DLOG overlay is not the base generation, and dumping the base as though it
were current would be wrong — so the delta log is refused rather than
ignored.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.Storage.IndexedBlockWireV4
import L4Factoidal.Storage.QuadDataset
import L4Factoidal.Syntax.NQuads

namespace Harness.QuadDump

open L4Factoidal.RDF
open L4Factoidal.Storage.ShardManifest
open L4Factoidal.Storage.QuadDataset
open L4Factoidal.Syntax

def resolveGeneration (root : System.FilePath) : IO System.FilePath := do
  if ← (root / "manifest.sbm2").pathExists then pure root
  else do
    let current := root / "CURRENT"
    if ← current.pathExists then
      pure (root / (← IO.FS.readFile current).trim)
    else throw (IO.userError s!"no manifest.sbm2 and no CURRENT under {root}")

def usage : String :=
  "usage: l4block-quad-dump COLLECTION-ROOT OUTPUT.nq"

def run (args : List String) : IO UInt32 := do
  match args with
  | [root, output] => do
      try
        let directory ← resolveGeneration (System.FilePath.mk root)
        let deltas := directory / "deltas.dlog"
        if ← deltas.pathExists then
          throw (IO.userError "this generation carries a delta log; compact it before dumping")
        let manifestBytes ← IO.FS.readBinFile (directory / "manifest.sbm2")
        match decode? manifestBytes with
        | none => throw (IO.userError "manifest.sbm2 is malformed or unsupported")
        | some manifest => do
            if !isIbk4Layout manifest.layout then
              throw (IO.userError s!"layout '{manifest.layout}' is not an IBK4 generation")
            IO.FS.withFile output .write fun handle => do
              let mut quads := 0
              for entry in manifest.entries do
                let bytes ← IO.FS.readBinFile (directory / entry.artifact.key.value)
                match L4Factoidal.Storage.IndexedBlockWireV4.decode bytes with
                | none =>
                    throw (IO.userError s!"{entry.artifact.key.value} is not a decodable IBK4 block")
                | some block => do
                    let rows := block.denotes
                    quads := quads + rows.length
                    handle.putStr (Dataset.toCanonicalNQuads (datasetOfQuads rows))
              IO.println s!"l4block-quad-dump generation={directory} blocks={manifest.entries.length} quads={quads} output={output}"
            pure 0
      catch e => do IO.eprintln s!"l4block-quad-dump failure: {e}"; pure 1
  | _ => do IO.eprintln usage; pure 2

end Harness.QuadDump

def main (args : List String) : IO UInt32 := Harness.QuadDump.run args
