/- Inspect the exact logical byte ranges an IBK2 predicate scan requires. -/
import L4Factoidal.Storage.IndexedBlockWireV2

namespace Harness.IndexedBlockV2RangePlan

open L4Factoidal.RDF
open L4Factoidal.Storage.IndexedBlockWireV2

private def predicate? (text : String) : Option WfIri :=
  if h : isIri text then some ⟨text, h⟩ else none

def main (args : List String) : IO UInt32 := do
  match args with
  | [path, iri] => try
      let bytes ← IO.FS.readBinFile path
      match predicate? iri, open? bytes with
      | none, _ => IO.eprintln s!"l4block-id-v2-range-plan invalid predicate IRI: {iri}"; return 2
      | _, none => IO.eprintln "l4block-id-v2-range-plan rejected IBK2 artifact"; return 1
      | some predicate, some opened =>
          let dictionary := dictionaryRange opened.header
          let directory := directoryRange opened.header
          let dictBytes := bytes.extract dictionary.offset (dictionary.offset + dictionary.length)
          let dirBytes := bytes.extract directory.offset (directory.offset + directory.length)
          match predicateReadRanges? opened.header dictBytes dirBytes predicate with
          | none => IO.println s!"l4block-id-v2-range-plan file={path} predicate={iri} ranges=0 bytes=0 artifact-bytes={bytes.size}"; return 0
          | some ranges =>
              IO.println s!"l4block-id-v2-range-plan file={path} predicate={iri} ranges={repr ranges} planned-bytes={rangeBytes ranges} artifact-bytes={bytes.size}"
              return 0
    catch e => IO.eprintln s!"l4block-id-v2-range-plan failure: {e}"; return 1
  | _ => IO.eprintln "usage: l4block-id-v2-range-plan BLOCK.ibk2 PREDICATE-IRI"; return 2

end Harness.IndexedBlockV2RangePlan

def main (args : List String) : IO UInt32 := Harness.IndexedBlockV2RangePlan.main args
