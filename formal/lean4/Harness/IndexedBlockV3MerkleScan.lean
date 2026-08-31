/- CLI for bounded, manifest-wide IBK3 predicate scans. The importable range
   materializer is deliberately separate so parsed-SPARQL execution reuses the
   identical physical reader. -/
import Harness.IndexedBlockV3Materialize
import L4Factoidal.Storage.ShardManifest

namespace Harness.IndexedBlockV3MerkleScan

open Harness.IndexedBlockV3Materialize
open L4Factoidal.RDF
open L4Factoidal.Storage.ShardManifest

private def predicate? (text : String) : Option WfIri :=
  if h : isIri text then some ⟨text, h⟩ else none

private def run (directoryText iriText limit : String) : IO UInt32 := do
  match predicate? iriText, limit.toNat? with
  | some predicate, some rowLimit =>
      let directory := System.FilePath.mk directoryText
      let manifestBytes ← IO.FS.readBinFile (directory / "manifest.sbm2")
      match decode? manifestBytes with
      | none => IO.eprintln "l4block-id-v3-merkle-scan rejected: malformed SBM2 manifest"; return 1
      | some manifest =>
          if !rangeCommitted manifest || manifest.layout != "predicate-ibk3-ptd1-merkle-v0" then
            IO.eprintln "l4block-id-v3-merkle-scan rejected: not an IBK3 range-committed manifest"; return 1
          let entries := selectAll manifest predicate
          if entries.isEmpty then IO.println s!"l4block-id-v3-merkle-scan rows=0 predicate={iriText} artifacts=0"; return 0
          match ← scanEntries directory predicate rowLimit entries [] {} 0 with
          | none => IO.eprintln "l4block-id-v3-merkle-scan rejected: manifest entry or verified range"; return 1
          | some (triples, counters, opened) =>
              IO.println s!"l4block-id-v3-merkle-scan rows={triples.length} predicate={iriText} artifacts={opened}/{entries.length} logical-read-bytes={counters.requestedBytes} fetched-bytes={counters.fetchedBytes} verified-chunks={counters.chunks} range-requests={counters.requests}"
              return 0
  | none, _ => IO.eprintln s!"l4block-id-v3-merkle-scan invalid predicate IRI: {iriText}"; return 2
  | _, none => IO.eprintln "l4block-id-v3-merkle-scan LIMIT must be a natural number"; return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | [directory, predicate, limit] =>
      try run directory predicate limit
      catch error => IO.eprintln s!"l4block-id-v3-merkle-scan failure: {error}"; return 1
  | _ => IO.eprintln "usage: l4block-id-v3-merkle-scan SHARD-DIR PREDICATE-IRI LIMIT"; return 2

end Harness.IndexedBlockV3MerkleScan

def main (args : List String) : IO UInt32 := Harness.IndexedBlockV3MerkleScan.main args
