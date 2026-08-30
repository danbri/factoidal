/- Persist one independently decodable IBK2 artifact per predicate.  The
   accompanying TSV manifest is deliberately human-inspectable during this
   transitional stage; a checked binary manifest follows once its row-order
   contract is settled. -/
import L4Factoidal.Storage.PredicateBlocks
import L4Factoidal.Storage.IndexedBlockWireV2
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Crypto.SHA2

namespace Harness.PredicateShardPack

open L4Factoidal.Syntax
open L4Factoidal.Storage.PredicateBlocks
open L4Factoidal.Storage.IndexedBlockWireV2
open L4Factoidal.Crypto

private def pack (input output : String) : IO UInt32 := do
  let text ← IO.FS.readFile input
  match parseTurtle text (some ("file://" ++ input)) with
  | .error e => IO.eprintln s!"l4block-shard-pack Turtle parse error at {e.pos}: {e.msg}"; return 1
  | .ok graph =>
      let store := fromGraph graph
      IO.FS.createDirAll output
      let lines ← store.blocks.zipIdx.mapM fun ((predicate, block), index) => do
        match encode? block with
        | none => throw <| IO.userError s!"unsupported block for {predicate.val}"
        | some bytes =>
            let name := s!"predicate-{index}.ibk2"
            IO.FS.writeBinFile (output ++ "/" ++ name) bytes
            pure s!"{index}\t{predicate.val}\t{name}\t{block.rows.size}\t{bytes.size}\t{bytesToHex (sha256 bytes)}"
      IO.FS.writeFile (output ++ "/manifest.tsv")
        ("# index\tpredicate\tfile\trows\tbytes\tsha256\n" ++ String.intercalate "\n" lines ++ "\n")
      IO.println s!"l4block-shard-pack input={input} triples={graph.length} shards={store.blocks.length} output={output}"
      return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [input, output] => try pack input output catch e => IO.eprintln s!"l4block-shard-pack failure: {e}"; return 1
  | _ => IO.eprintln "usage: l4block-shard-pack INPUT.ttl OUTPUT-DIR"; return 2

end Harness.PredicateShardPack
def main (args : List String) : IO UInt32 := Harness.PredicateShardPack.main args
