import L4Factoidal.Storage.IndexedBlockWireV2

namespace L4Factoidal.Storage.IndexedBlockWireV2Tests

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.IndexedBlock
open L4Factoidal.Storage.IndexedBlockWireV2

private def pName : WfIri := ⟨"http://example.org/name", by simp [isIri]⟩
private def pAge : WfIri := ⟨"http://example.org/age", by simp [isIri]⟩
private def alice : Subject := .iri ⟨"http://example.org/alice", by simp [isIri]⟩
private def bob : Subject := .iri ⟨"http://example.org/bob", by simp [isIri]⟩
private def graph : Graph :=
  [{ s := alice, p := pName, o := .literal (Literal.langString "Alice" "en") },
   { s := alice, p := pAge, o := .literal (Literal.langString "30" "en") },
   { s := bob, p := pName, o := .literal (Literal.langString "Bob" "en") }]

private def block := fromGraph graph
private def bytes : ByteArray := (encode? block).getD ByteArray.empty
private def corrupt : ByteArray := ByteArray.mk ((encodeList block).drop 1 |>.toArray)
private def byteRange (offset length : Nat) : ByteArray :=
  ByteArray.mk ((bytes.data.toList.drop offset).take length |>.toArray)
private def headerBytes : ByteArray := byteRange 0 prefixBytes

private def rangeScanName : List Triple :=
  match decodePrefix headerBytes with
  | none => []
  | some header =>
      let dictionary := dictionaryRange header
      let directory := directoryRange header
      match predicateRange? header (byteRange dictionary.offset dictionary.length)
          (byteRange directory.offset directory.length) pName with
      | none => []
      | some segment =>
          scanPredicateRanges { p := some pName } headerBytes
            (byteRange dictionary.offset dictionary.length)
            (byteRange directory.offset directory.length)
            (byteRange segment.offset segment.length)

#guard supported block
#guard match decodePrefix bytes with
  | some header => header.dictCount == block.dict.size && header.rowCount == block.rows.size && header.segmentCount == 2
  | none => false
#guard match decode bytes with | some decoded => decoded.denotes == graph | none => false
#guard match decode bytes with
  | some decoded => scanBound { p := some pName } decoded == tripleMatchesBound { p := some pName } graph
  | none => false
#guard scanPredicateDecoded { p := some pName } bytes == tripleMatchesBound { p := some pName } graph
#guard scanPredicateDecoded { p := some pAge } bytes == tripleMatchesBound { p := some pAge } graph
#guard rangeScanName == tripleMatchesBound { p := some pName } graph
#guard (decode corrupt).isNone

end L4Factoidal.Storage.IndexedBlockWireV2Tests
