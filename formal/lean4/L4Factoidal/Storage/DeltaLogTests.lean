/-
L4Factoidal.Storage.DeltaLogTests — build-time checks for the delta
log's crash-safety behaviour.
-/
import L4Factoidal.Storage.DeltaLog

namespace L4Factoidal.Storage

open L4Factoidal.RDF

private def pay : List UInt8 := [10, 20, 30]

-- Round trip.
#guard parseEntry (frameEntry pay) == some (pay, [])
#guard (frameEntry pay).length == entryFrameSize 3

-- Magic numbers are the documented ASCII, little-endian.
#guard writeU32LE deltaEntryMagic == [68, 76, 69, 49]      -- 'D','L','E','1'
#guard writeU32LE deltaBatchMagic == [68, 76, 66, 49]      -- 'D','L','B','1'
#guard writeU32LE deltaLogMagic == [68, 76, 79, 71]        -- 'D','L','O','G'
#guard writeU32LE compactedEpochMagic == [67, 69, 80, 49]  -- 'C','E','P','1'

-- EVERY failure mode returns none, and each is a distinct reason a
-- replay must stop rather than continue.
-- Wrong magic: not a record boundary.
#guard parseEntry ([0, 0, 0, 0] ++ (frameEntry pay).drop 4) == none
-- Unknown version: a newer writer produced this.
#guard parseEntry ((frameEntry pay).set 4 99) == none
-- Corrupt payload: the append was torn.
#guard parseEntry ((frameEntry pay).set 12 99) == none
-- Short buffer: torn mid-record.
#guard parseEntry ((frameEntry pay).take 7) == none
#guard parseEntry [] == none

-- Replay of a clean log recovers every record and reports CLEAN.
private def twoEntries : List UInt8 := frameEntry pay ++ frameEntry [1, 2, 3]
#guard (replay twoEntries).1 == [pay, [1, 2, 3]]
#guard (replay twoEntries).2 == true

-- A TORN TAIL is not an error: take every record that verifies,
-- discard from the first that does not. This is the expected shape
-- after a crash mid-append.
private def tornLog : List UInt8 := frameEntry pay ++ (frameEntry [1, 2, 3]).take 6
#guard (replay tornLog).1 == [pay]
#guard (replay tornLog).2 == false      -- ...and the caller is told

-- An empty log is clean, not torn.
#guard (replay []).2 == true

-- The checksum is additive, and it changes when the payload does.
#guard simpleChecksum [1, 2, 3] == 6
#guard simpleChecksum [1, 2, 3] != simpleChecksum [1, 2, 4]

-- Entry kind tags round-trip.
#guard EntryKind.ofTag EntryKind.insert.tag == some .insert
#guard EntryKind.ofTag EntryKind.delete.tag == some .delete
#guard EntryKind.ofTag 99 == none

-- The epoch marker, and the guard it exists for: only records
-- STRICTLY NEWER than the compacted base may be replayed, or a
-- compaction's own folded-in updates get applied twice.
#guard parseEpoch (frameEpoch ⟨7⟩) == some ⟨7⟩
#guard parseEpoch [0, 0, 0, 0, 0, 0, 0, 0] == none
#guard parseEpoch ((frameEpoch ⟨7⟩).take 13) == none
#guard parseEpoch ((frameEpoch ⟨7⟩).set 12 99) == none
#guard shouldReplay 5 6
#guard !(shouldReplay 5 5)
#guard !(shouldReplay 5 4)

private def exIri : WfIri := ⟨"http://example.org/s", by decide⟩
private def exP   : WfIri := ⟨"http://example.org/p", by decide⟩
private def batch : DeltaBatch := {
  seq := 7, epoch := 3,
  ops := [.add ⟨.iri exIri, exP, .literal (Literal.string "hello")⟩ none,
          .remove ⟨.iri exIri, exP, .iri exIri⟩ (some "http://example.org/g")] }

-- A compacted base through epoch 3 replays only the later request.
#guard (filterBatchesSinceEpoch (some 3) [batch, { batch with seq := 8, epoch := 4 }]).map (·.seq) == [8]
#guard (filterBatchesSinceEpoch none [batch]).map (·.seq) == [7]

-- A committed batch carries variable-size entry frames, its own checksum,
-- and round-trips with an arbitrary following batch untouched.
#guard parseDeltaBatch (serializeDeltaBatch batch ++ [0xAA]) == some (batch, [0xAA])
#guard parseLog (serializeLog [batch]) == some ([batch], [])
#guard serializeDeltaBatch? batch == some (serializeDeltaBatch batch)
#guard serializeLog? [batch] == some (serializeLog [batch])
#guard (serializeDeltaBatch? { batch with seq := UInt64.size }).isNone
#guard (serializeLog? [{ batch with epoch := UInt64.size }]).isNone
-- A currently unsupported RDF-star term is rejected on the durable writer
-- path rather than emitted as a frame that replay would later refuse.
#guard (serializeDeltaEntryPayload?
  (.add ⟨.iri exIri, exP, .tripleTerm (.iri exIri) exP (.iri exIri)⟩ none)).isNone
#guard parseLog (serializeLog [batch] ++ (serializeDeltaBatch { batch with seq := 8 }).take 11)
  == some ([batch], (serializeDeltaBatch { batch with seq := 8 }).take 11)

end L4Factoidal.Storage
