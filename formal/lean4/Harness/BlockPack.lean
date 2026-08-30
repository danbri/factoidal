/-
Harness.BlockPack — build one framed BLK0 file from Turtle.

This is an executable-edge utility for the persistence vertical. BLK0 remains
the restricted direct-term transition format; the later canonical TermId codec
will replace it without changing the query-side `IndexedBlock` interface.
-/
import L4Factoidal.Storage.BlockWireV0
import L4Factoidal.Syntax.Turtle

namespace Harness.BlockPack

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.Storage.BlockMvp
open L4Factoidal.Storage.BlockWireV0

def main (args : List String) : IO UInt32 := do
  match args with
  | [input, output] =>
      try
        let text ← IO.FS.readFile input
        match parseTurtle text (some ("file://" ++ input)) with
        | .error e =>
            IO.eprintln s!"l4block-pack Turtle parse error at {e.pos}: {e.msg}"
            return 1
        | .ok graph =>
            let block : Block := { rows := graph }
            match encode? block with
            | none =>
                IO.eprintln "l4block-pack refused: BLK0 does not support one or more RDF terms"
                return 1
            | some bytes =>
                IO.FS.writeBinFile output bytes
                IO.println s!"l4block-pack input={input} triples={graph.length} output={output} bytes={bytes.size}"
                return 0
      catch e =>
        IO.eprintln s!"l4block-pack failure: {e}"
        return 1
  | _ =>
      IO.eprintln "usage: l4block-pack INPUT.ttl OUTPUT.blk0"
      return 2

end Harness.BlockPack

def main (args : List String) : IO UInt32 := Harness.BlockPack.main args
