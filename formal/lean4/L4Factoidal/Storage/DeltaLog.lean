/-
L4Factoidal.Storage.DeltaLog — the durable-UPDATE delta log framing,
ported from `formal/fstar/RDF.Store.Columnar.DeltaLog.fst`.

The COTTAS store's base file is immutable; a SPARQL UPDATE appends to
an append-only delta log beside it, and a later compaction folds the
log into a new base. That makes the log's framing the crash-safety
boundary of the whole store, which is why it is specified in the
formal source rather than left to a writer — iron rule 11 again.

Framing, per record:

    [ magic : u32 'DLE1' ][ version : u8 ][ payload ][ checksum : u32 ]

The checksum is a plain ADDITIVE mod-2^32 check, deliberately NOT a
cryptographic digest. Its only job is to let a replay reject a TORN
record — one whose append was interrupted by a crash — without
decoding it. Whole-log drift detection is a separate mechanism (the
sha256 hash-witness pattern); conflating the two would put a
cryptographic cost on every append for a property appends do not
need.
-/
import L4Factoidal.Storage.Bytes

namespace L4Factoidal.Storage

/-- `'DLE1'` little-endian. -/
def deltaEntryMagic : UInt32 := 0x31454C44
def deltaEntryVersion : UInt8 := 1

/-- `'DLB1'` — a batch of entries written atomically. -/
def deltaBatchMagic : UInt32 := 0x31424C44
/-- `'DLOG'` — the log file header. -/
def deltaLogMagic : UInt32 := 0x474F4C44
/-- `'CEP1'` — the compacted-epoch marker. -/
def compactedEpochMagic : UInt32 := 0x31504543

/-- Term tags. Each tag space is disjoint and under 256, so one byte
    suffices. -/
def termTagIri : UInt8 := 0
def termTagBnode : UInt8 := 1
def termTagLiteral : UInt8 := 2
def termTagTripleTerm : UInt8 := 3

/-- Entry kinds: what an UPDATE did. -/
inductive EntryKind where
  | insert | delete
deriving Repr, DecidableEq, Inhabited

def EntryKind.tag : EntryKind → UInt8
  | .insert => 0
  | .delete => 1

def EntryKind.ofTag : UInt8 → Option EntryKind
  | 0 => some .insert
  | 1 => some .delete
  | _ => none

/-- The additive mod-2^32 checksum. -/
def simpleChecksum (bs : List UInt8) : UInt32 :=
  bs.foldl (fun acc b => acc + b.toUInt32) 0

/-- One log record, framed. -/
def frameEntry (payload : List UInt8) : List UInt8 :=
  writeU32LE deltaEntryMagic ++ [deltaEntryVersion] ++ payload ++
  writeU32LE (simpleChecksum payload)

/-- Read one record back, given its payload length.

    Every failure mode returns `none` and they are DISTINCT reasons a
    replay must stop rather than continue: a wrong magic means this is
    not a record boundary, an unknown version means a newer writer
    produced it, a short buffer or a bad checksum means the append was
    TORN by a crash. In every case the correct behaviour is to
    truncate the log here — reading on would replay a half-written
    update. -/
def parseEntry (bs : List UInt8) (payloadLen : Nat) : Option (List UInt8) :=
  match readU32LE bs 0 with
  | none => none
  | some magic =>
      if magic != deltaEntryMagic then none
      else match (bs.drop 4).head? with
        | none => none
        | some ver =>
            if ver != deltaEntryVersion then none
            else
              let rest := bs.drop 5
              let payload := rest.take payloadLen
              if payload.length != payloadLen then none
              else match readU32LE rest payloadLen with
                | none => none
                | some stored =>
                    if stored != simpleChecksum payload then none
                    else some payload

/-- The bytes one framed record occupies. -/
def entryFrameSize (payloadLen : Nat) : Nat := 4 + 1 + payloadLen + 4

/-- Replay a log: read records until one fails, returning the payloads
    recovered and whether the log ended CLEANLY.

    A torn tail is NOT an error — a crash mid-append is expected, and
    the recovery rule is "take every record that verifies, discard
    from the first that does not". Returning the clean flag lets the
    caller distinguish a tidy shutdown from a crash without changing
    what it recovered. -/
partial def replay (bs : List UInt8) (payloadLen : Nat) : List (List UInt8) × Bool :=
  let rec go (bs : List UInt8) (acc : List (List UInt8)) : List (List UInt8) × Bool :=
    if bs.isEmpty then (acc, true)
    else match parseEntry bs payloadLen with
      | none => (acc, false)          -- torn tail: stop here
      | some p => go (bs.drop (entryFrameSize payloadLen)) (acc ++ [p])
  go bs []

/-- The compacted-epoch marker. A store whose base file was rebuilt
    at epoch `n` must IGNORE log records from an earlier epoch, or a
    replay would re-apply updates the compaction already folded in —
    the double-apply bug this marker exists to prevent. -/
structure EpochMarker where
  epoch : UInt32
deriving Repr, DecidableEq, Inhabited

def frameEpoch (m : EpochMarker) : List UInt8 :=
  writeU32LE compactedEpochMagic ++ writeU32LE m.epoch

def parseEpoch (bs : List UInt8) : Option EpochMarker :=
  match readU32LE bs 0, readU32LE bs 4 with
  | some magic, some e =>
      if magic == compactedEpochMagic then some ⟨e⟩ else none
  | _, _ => none

/-- Should a record from `recordEpoch` be replayed against a base
    compacted at `baseEpoch`? Only records STRICTLY NEWER than the
    base survive. -/
def shouldReplay (baseEpoch recordEpoch : UInt32) : Bool := recordEpoch > baseEpoch

end L4Factoidal.Storage
