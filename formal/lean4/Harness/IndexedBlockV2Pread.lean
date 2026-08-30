/- Physically bounded POSIX-file execution of the pure IBK2 predicate plan. -/
import Harness.PosixRangeIO

namespace Harness.IndexedBlockV2Pread

open L4Factoidal.RDF L4Factoidal.SPARQL
open L4Factoidal.Storage.IndexedBlockWireV2
open Harness.PosixRangeIO

private def predicate? (text : String) : Option WfIri :=
  if h : isIri text then some ⟨text, h⟩ else none

private def run (path iri : String) : IO UInt32 := do
  match predicate? iri with
  | none => IO.eprintln s!"l4block-id-v2-pread invalid predicate IRI: {iri}"; return 2
  | some predicate =>
      match ← readRange? path { offset := 0, length := prefixBytes } with
      | none => IO.eprintln "l4block-id-v2-pread rejected: could not read IBK2 prefix"; return 1
      | some prefixBytesRead =>
          match decodePrefix prefixBytesRead with
          | none => IO.eprintln "l4block-id-v2-pread rejected: invalid IBK2 prefix"; return 1
          | some header =>
              let dictionaryResult ← readRange? path (dictionaryRange header)
              let directoryResult ← readRange? path (directoryRange header)
              match dictionaryResult, directoryResult with
              | some dictionary, some directory =>
                  match predicateRange? header dictionary directory predicate with
                  | none =>
                      IO.println s!"l4block-id-v2-pread rows=0 read-bytes={prefixBytes + dictionary.size + directory.size} predicate={iri}"
                      return 0
                  | some segment =>
                      match ← readRange? path segment with
                      | none => IO.eprintln "l4block-id-v2-pread rejected: could not read selected segment"; return 1
                      | some rows =>
                          let triples := scanPredicateRanges { p := some predicate } prefixBytesRead dictionary directory rows
                          let readBytes := prefixBytes + dictionary.size + directory.size + rows.size
                          IO.println s!"l4block-id-v2-pread rows={triples.length} read-bytes={readBytes} predicate={iri}"
                          return 0
              | _, _ => IO.eprintln "l4block-id-v2-pread rejected: could not read IBK2 planning ranges"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [path, iri] => try run path iri catch e => IO.eprintln s!"l4block-id-v2-pread failure: {e}"; return 1
  | _ => IO.eprintln "usage: l4block-id-v2-pread BLOCK.ibk2 PREDICATE-IRI"; return 2

end Harness.IndexedBlockV2Pread

def main (args : List String) : IO UInt32 := Harness.IndexedBlockV2Pread.main args
