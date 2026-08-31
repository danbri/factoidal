/- Measure the pageable-dictionary opportunity on an existing IBK2 artifact.
   This is a diagnostic executable only: it fully opens IBK2 to establish the
   comparison, then asks PTD1 how many pages the first N ID rows would need. -/
import L4Factoidal.Storage.IndexedBlockWireV2
import L4Factoidal.Storage.PagedTermDictionary

namespace Harness.PagedDictionaryProbe

open L4Factoidal.Storage.IndexedBlockWireV2
open L4Factoidal.Storage.IndexedBlock

private def idsOfRows (rows : List IdTriple) : List Nat :=
  rows.flatMap fun row => [row.s, row.p, row.o]

private def run (path : System.FilePath) (rowCount : Nat) : IO UInt32 := do
  try
    let ibk2Bytes ← IO.FS.readBinFile path
    match L4Factoidal.Storage.IndexedBlockWireV2.open? ibk2Bytes with
    | none => IO.eprintln "l4block-paged-dictionary-probe rejected: malformed IBK2"; return 1
    | some opened =>
        match L4Factoidal.Storage.PagedTermDictionary.encode? opened.decoded.dict with
        | none => IO.eprintln "l4block-paged-dictionary-probe rejected: unsupported dictionary term"; return 1
        | some pagedBytes =>
            match L4Factoidal.Storage.PagedTermDictionary.decodePrefix
                (pagedBytes.extract 0 L4Factoidal.Storage.PagedTermDictionary.prefixBytes) with
            | none => IO.eprintln "l4block-paged-dictionary-probe rejected: malformed PTD1 prefix"; return 1
            | some header =>
                let directoryEnd := L4Factoidal.Storage.PagedTermDictionary.prefixBytes + header.pageCount * 8
                match L4Factoidal.Storage.PagedTermDictionary.decodeDirectory? header
                    (pagedBytes.extract L4Factoidal.Storage.PagedTermDictionary.prefixBytes directoryEnd) with
                | none => IO.eprintln "l4block-paged-dictionary-probe rejected: malformed PTD1 directory"; return 1
                | some directory =>
                    let rows := opened.decoded.rows.toList.take rowCount
                    let ids := idsOfRows rows
                    match L4Factoidal.Storage.PagedTermDictionary.pageRangesForTerms? header directory ids with
                    | none => IO.eprintln "l4block-paged-dictionary-probe rejected: row refers outside PTD1 dictionary"; return 1
                    | some ranges =>
                        let pageBytes := ranges.foldl (fun total range => total + range.length) 0
                        IO.println s!"l4block-paged-dictionary-probe ibk2-bytes={ibk2Bytes.size} dictionary-terms={opened.decoded.dict.size} rows-sampled={rows.length} term-ids={ids.length} ptd1-bytes={pagedBytes.size} ptd1-planning-bytes={directoryEnd} pages={ranges.length} ptd1-page-bytes={pageBytes} projected-bytes={directoryEnd + pageBytes}"
                        return 0
  catch error => IO.eprintln s!"l4block-paged-dictionary-probe failure: {error}"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [path, rows] =>
      match rows.toNat? with
      | some count => run (System.FilePath.mk path) count
      | none => IO.eprintln "l4block-paged-dictionary-probe ROWS must be a natural number"; return 2
  | _ => IO.eprintln "usage: l4block-paged-dictionary-probe ARTIFACT.ibk2 ROWS"; return 2

end Harness.PagedDictionaryProbe

def main (args : List String) : IO UInt32 := Harness.PagedDictionaryProbe.main args
