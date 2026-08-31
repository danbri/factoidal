import L4Factoidal.Storage.IndexedBlockWireV3

namespace L4Factoidal.Storage.IndexedBlockWireV3Tests

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.IndexedBlock
open L4Factoidal.Storage.IndexedBlockWireV3

private def pName : WfIri := ⟨"http://example.org/name", by simp [isIri]⟩
private def pAge : WfIri := ⟨"http://example.org/age", by simp [isIri]⟩
private def alice : Subject := .iri ⟨"http://example.org/alice", by simp [isIri]⟩
private def bob : Subject := .iri ⟨"http://example.org/bob", by simp [isIri]⟩
private def names : Graph :=
  [{ s := alice, p := pName, o := .literal (Literal.langString "Alice" "en") },
   { s := bob, p := pName, o := .literal (Literal.langString "Bob" "en") }]
private def mixed : Graph :=
  names ++ [{ s := alice, p := pAge, o := .literal (Literal.string "30") }]

private def block := fromGraph names
private def bytes : ByteArray := (encode? block).getD ByteArray.empty
private def corrupt : ByteArray := ByteArray.mk ((encodeList block).drop 1 |>.toArray)

private def pagePlanWorks : Bool :=
  match decodePrefix bytes with
  | none => false
  | some header =>
      match dictionaryPrefixRange header with
      | none => false
      | some ptdPrefixRange =>
          let ptdPrefix := bytes.extract ptdPrefixRange.offset (ptdPrefixRange.offset + ptdPrefixRange.length)
          match dictionaryDirectoryRange? header ptdPrefix with
          | none => false
          | some directoryRange =>
              let directory := bytes.extract directoryRange.offset (directoryRange.offset + directoryRange.length)
              let rows := rowsRange header
              let rowPrefix := bytes.extract rows.offset (rows.offset + rowBytes)
              match dictionaryPagesForRowPrefix? header ptdPrefix directory rowPrefix with
              | some [page] => page.offset >= (dictionaryRange header).offset &&
                  page.offset + page.length <= (dictionaryRange header).offset + (dictionaryRange header).length
              | _ => false

private def rangeScan : List Triple :=
  match decodePrefix bytes with
  | none => []
  | some header =>
      match dictionaryPrefixRange header with
      | none => []
      | some ptdPrefixRange =>
          let ptdPrefix := bytes.extract ptdPrefixRange.offset (ptdPrefixRange.offset + ptdPrefixRange.length)
          match dictionaryDirectoryRange? header ptdPrefix with
          | none => []
          | some directoryRange =>
              let directory := bytes.extract directoryRange.offset (directoryRange.offset + directoryRange.length)
              let rows := rowsRange header
              let rowPrefix := bytes.extract rows.offset (rows.offset + rows.length)
              match dictionaryPagesForRowPrefix? header ptdPrefix directory rowPrefix with
              | none => []
              | some ranges =>
                  let pages := ranges.map fun range =>
                    (range, bytes.extract range.offset (range.offset + range.length))
                  (scanRowPrefixPages { p := some pName }
                    (bytes.extract 0 prefixBytes) rowPrefix ptdPrefix directory pages).getD []

private def missingPageRejected : Bool :=
  match decodePrefix bytes with
  | none => false
  | some header =>
      match dictionaryPrefixRange header with
      | none => false
      | some ptdPrefixRange =>
          let ptdPrefix := bytes.extract ptdPrefixRange.offset (ptdPrefixRange.offset + ptdPrefixRange.length)
          match dictionaryDirectoryRange? header ptdPrefix with
          | none => false
          | some directoryRange =>
              let directory := bytes.extract directoryRange.offset (directoryRange.offset + directoryRange.length)
              let rows := rowsRange header
              let rowPrefix := bytes.extract rows.offset (rows.offset + rows.length)
              (scanRowPrefixPages { p := some pName }
                (bytes.extract 0 prefixBytes) rowPrefix ptdPrefix directory []).isNone

#guard supported block
#guard !(supported (fromGraph mixed))
#guard match decodePrefix bytes with
  | some header => header.rowCount == block.rows.size &&
      rowsRange header == { offset := prefixBytes, length := block.rows.size * rowBytes } &&
      (dictionaryRange header).offset == prefixBytes + block.rows.size * rowBytes
  | none => false
#guard match decode bytes with
  | some decoded => decoded.denotes == names &&
      scanBound { p := some pName } decoded == tripleMatchesBound { p := some pName } names
  | none => false
#guard pagePlanWorks
#guard rangeScan == tripleMatchesBound { p := some pName } names
#guard missingPageRejected
#guard (scanRowPrefixPages {} ByteArray.empty ByteArray.empty ByteArray.empty ByteArray.empty []).isNone
#guard (decode corrupt).isNone

end L4Factoidal.Storage.IndexedBlockWireV3Tests
