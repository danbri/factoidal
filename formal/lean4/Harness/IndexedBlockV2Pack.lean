/- Build a predicate-segmented IBK2 file directly from Turtle. -/
import L4Factoidal.Storage.IndexedBlockWireV2
import L4Factoidal.Syntax.Turtle

namespace Harness.IndexedBlockV2Pack

open L4Factoidal.Syntax
open L4Factoidal.Storage.IndexedBlock
open L4Factoidal.Storage.IndexedBlockWireV2

def main (args : List String) : IO UInt32 := do
  match args with
  | [input, output] =>
      try
        let text ← IO.FS.readFile input
        match parseTurtle text (some ("file://" ++ input)) with
        | .error e =>
            IO.eprintln s!"l4block-id-v2-pack Turtle parse error at {e.pos}: {e.msg}"
            return 1
        | .ok graph =>
            let block := fromGraph graph
            match encode? block with
            | none =>
                IO.eprintln "l4block-id-v2-pack refused: unsupported RDF terms or IDs"
                return 1
            | some bytes =>
                IO.FS.writeBinFile output bytes
                IO.println s!"l4block-id-v2-pack input={input} triples={graph.length} terms={block.dict.size} segments={block.byPredicate.toList.length} output={output} bytes={bytes.size}"
                return 0
      catch e =>
        IO.eprintln s!"l4block-id-v2-pack failure: {e}"
        return 1
  | _ =>
      IO.eprintln "usage: l4block-id-v2-pack INPUT.ttl OUTPUT.ibk2"
      return 2

end Harness.IndexedBlockV2Pack

def main (args : List String) : IO UInt32 := Harness.IndexedBlockV2Pack.main args
