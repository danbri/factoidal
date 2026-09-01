/- CLI for bounded, manifest-wide IBK3 predicate scans. The importable range
   materializer is deliberately separate so parsed-SPARQL execution reuses the
   identical physical reader. -/
import Harness.IndexedBlockV3Materialize
import Harness.GenerationPointer
import L4Factoidal.Storage.ShardManifest

namespace Harness.IndexedBlockV3MerkleScan

open Harness.IndexedBlockV3Materialize
open Harness.GenerationPointer
open L4Factoidal.RDF
open L4Factoidal.Storage.ShardManifest

private def predicate? (text : String) : Option WfIri :=
  if h : isIri text then some ⟨text, h⟩ else none

private def isIbk3RangeLayout (layout : String) : Bool :=
  layout == "predicate-ibk3-ptd1-merkle-v0" ||
  layout == "predicate-ibk3-ptd1-merkle-v0-compacted-default-dlog-v1" ||
  layout == "predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0" ||
  layout == "predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0-compacted-default-dlog-v1"

private def readManifest? (directoryText : String) : IO (Option (System.FilePath × Manifest)) := do
  let directory ← resolveStoreDirectory (System.FilePath.mk directoryText)
  let manifestBytes ← IO.FS.readBinFile (directory / "manifest.sbm2")
  match decode? manifestBytes with
  | some manifest =>
      if rangeCommitted manifest && isIbk3RangeLayout manifest.layout then pure (some (directory, manifest))
      else pure none
  | none => pure none

private def run (directoryText iriText limit : String) : IO UInt32 := do
  match predicate? iriText, limit.toNat? with
  | some predicate, some rowLimit =>
      match ← readManifest? directoryText with
      | none => IO.eprintln "l4block-id-v3-merkle-scan rejected: not an IBK3 range-committed manifest"; return 1
      | some (directory, manifest) =>
          let entries := selectAll manifest predicate
          if entries.isEmpty then IO.println s!"l4block-id-v3-merkle-scan rows=0 predicate={iriText} artifacts=0"; return 0
          match ← scanEntries directory predicate rowLimit entries [] {} 0 with
          | none => IO.eprintln "l4block-id-v3-merkle-scan rejected: manifest entry or verified range"; return 1
          | some (triples, counters, opened) =>
              IO.println s!"l4block-id-v3-merkle-scan rows={triples.length} predicate={iriText} artifacts={opened}/{entries.length} logical-read-bytes={counters.requestedBytes} fetched-bytes={counters.fetchedBytes} verified-chunks={counters.chunks} range-requests={counters.requests}"
              return 0
  | none, _ => IO.eprintln s!"l4block-id-v3-merkle-scan invalid predicate IRI: {iriText}"; return 2
  | _, none => IO.eprintln "l4block-id-v3-merkle-scan LIMIT must be a natural number"; return 2

/-- Diagnostic cursor primitive over one predicate artifact.  It is purposefully
    not a SPARQL LIMIT path yet: this command establishes that an arbitrary
    row window is Merkle-verified, dictionary-planned and decoded before a
    future cursor executor attaches an unordered-result contract. -/
private def runRange (directoryText iriText startText countText : String) : IO UInt32 := do
  match predicate? iriText, startText.toNat?, countText.toNat?, ← readManifest? directoryText with
  | some predicate, some start, some count, some (directory, manifest) =>
      match selectAll manifest predicate with
      | [entry] =>
          match ← scanEntryRange directory predicate start count entry with
          | none => IO.eprintln "l4block-id-v3-merkle-scan rejected: manifest entry or verified row range"; return 1
          | some result =>
              IO.println s!"l4block-id-v3-merkle-scan rows={result.triples.length} predicate={iriText} row-start={start} row-count={count} logical-read-bytes={result.counters.requestedBytes} fetched-bytes={result.counters.fetchedBytes} verified-chunks={result.counters.chunks} range-requests={result.counters.requests}"
              return 0
      | _ => IO.eprintln "l4block-id-v3-merkle-scan --range requires exactly one predicate artifact"; return 2
  | none, _, _, _ => IO.eprintln s!"l4block-id-v3-merkle-scan invalid predicate IRI: {iriText}"; return 2
  | _, none, _, _ | _, _, none, _ =>
      IO.eprintln "l4block-id-v3-merkle-scan --range START and COUNT must be natural numbers"; return 2
  | _, _, _, none =>
      IO.eprintln "l4block-id-v3-merkle-scan rejected: not an IBK3 range-committed manifest"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [directory, predicate, limit] =>
      try run directory predicate limit
      catch error => IO.eprintln s!"l4block-id-v3-merkle-scan failure: {error}"; return 1
  | [directory, predicate, "--range", start, count] =>
      try runRange directory predicate start count
      catch error => IO.eprintln s!"l4block-id-v3-merkle-scan failure: {error}"; return 1
  | _ => IO.eprintln "usage: l4block-id-v3-merkle-scan SHARD-DIR PREDICATE-IRI LIMIT | SHARD-DIR PREDICATE-IRI --range START COUNT"; return 2

end Harness.IndexedBlockV3MerkleScan

def main (args : List String) : IO UInt32 := Harness.IndexedBlockV3MerkleScan.main args
