import L4Factoidal.Storage.IndexedBlockWireV1

namespace L4Factoidal.Storage.IndexedBlockWireV1Tests

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.IndexedBlock
open L4Factoidal.Storage.IndexedBlockWireV1
open L4Factoidal.Storage.BlockArtifact

private def p : WfIri := ⟨"http://example.org/name", by simp [isIri]⟩
private def graph : Graph :=
  [{ s := .iri ⟨"http://example.org/alice", by simp [isIri]⟩
   , p := p, o := .literal (Literal.langString "Alice" "en") },
   { s := .iri ⟨"http://example.org/bob", by simp [isIri]⟩
   , p := p, o := .literal (Literal.langString "Bob" "en") }]

private def block := fromGraph graph
private def bytes : ByteArray := (encode? block).getD ByteArray.empty
private def checksumCorrupt : ByteArray :=
  let raw := encodeList block
  let last := raw.reverse.head?.getD 0
  let altered : UInt8 := if last == 0 then 1 else 0
  ByteArray.mk ((raw.take (raw.length - 1) ++ [altered]).toArray)

#guard supported block
#guard match decode bytes with | some b => b.denotes == graph | none => false
#guard match decode bytes with
  | some b => scanBound { p := some p } b == tripleMatchesBound { p := some p } graph
  | none => false
#guard (decode checksumCorrupt).isNone
#guard (decodeVerified (digest bytes) bytes).isSome
#guard (decodeVerified (digest bytes) checksumCorrupt).isNone

end L4Factoidal.Storage.IndexedBlockWireV1Tests
