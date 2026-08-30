/- Compare a shared-dictionary IBK2 artifact with its independently decodable
   predicate-local shard for one real Turtle predicate. -/
import L4Factoidal.Storage.PredicateBlocks
import L4Factoidal.Storage.IndexedBlockWireV2
import L4Factoidal.Syntax.Turtle

namespace Harness.PredicateBlocksProbe

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.Storage.IndexedBlock
open L4Factoidal.Storage.PredicateBlocks
open L4Factoidal.Storage.IndexedBlockWireV2

private def predicate? (text : String) : Option WfIri :=
  if h : isIri text then some ⟨text, h⟩ else none

private def encodedBytes (block : Block) : Nat :=
  match encode? block with
  | some bytes => bytes.size
  | none => 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [input, iri] => try
      let text ← IO.FS.readFile input
      match parseTurtle text (some ("file://" ++ input)), predicate? iri with
      | .error e, _ =>
          IO.eprintln s!"l4block-predicate-shards Turtle parse error at {e.pos}: {e.msg}"; return 1
      | _, none => IO.eprintln s!"l4block-predicate-shards invalid predicate IRI: {iri}"; return 2
      | .ok graph, some predicate =>
          let whole := L4Factoidal.Storage.IndexedBlock.fromGraph graph
          let store := L4Factoidal.Storage.PredicateBlocks.fromGraph graph
          match blockFor? predicate store with
          | none =>
              IO.println s!"l4block-predicate-shards input={input} predicates={store.blocks.length} selected=0"; return 0
          | some shard =>
              let rows := scanBound { p := some predicate } store
              IO.println s!"l4block-predicate-shards input={input} triples={graph.length} predicates={store.blocks.length}"
              IO.println s!"l4block-predicate-shards predicate={iri} rows={rows.length} local-terms={shard.dict.size} local-ibk2-bytes={encodedBytes shard} shared-ibk2-bytes={encodedBytes whole}"
              return 0
    catch e => IO.eprintln s!"l4block-predicate-shards failure: {e}"; return 1
  | _ => IO.eprintln "usage: l4block-predicate-shards INPUT.ttl PREDICATE-IRI"; return 2

end Harness.PredicateBlocksProbe

def main (args : List String) : IO UInt32 := Harness.PredicateBlocksProbe.main args
