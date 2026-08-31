/-
L4Factoidal.Storage.DeltaLog — the durable-UPDATE delta log framing,
ported from `formal/fstar/RDF.Store.Columnar.DeltaLog.fst`.

The COTTAS store's base file is immutable; a SPARQL UPDATE appends to
an append-only delta log beside it, and a later compaction folds the
log into a new base. That makes the log's framing the crash-safety
boundary of the whole store, which is why it is specified in the
formal source rather than left to a writer — iron rule 11 again.

Framing, per record (matching the established F* `DLE1` format):

    [ magic : u32 'DLE1' ][ version : u32 ][ payload length : u32 ]
    [ payload ][ checksum : u32 ]

The checksum is a plain ADDITIVE mod-2^32 check, deliberately NOT a
cryptographic digest. Its only job is to let a replay reject a TORN
record — one whose append was interrupted by a crash — without
decoding it. Whole-log drift detection is a separate mechanism (the
sha256 hash-witness pattern); conflating the two would put a
cryptographic cost on every append for a property appends do not
need.
-/
import L4Factoidal.Storage.Bytes
import L4Factoidal.RDF.Core
import Init.Omega

namespace L4Factoidal.Storage

open L4Factoidal.RDF

/-- `'DLE1'` little-endian. -/
def deltaEntryMagic : UInt32 := 0x31454C44
def deltaEntryVersion : UInt32 := 1

/-- `'DLB1'` — a batch of entries written atomically. -/
def deltaBatchMagic : UInt32 := 0x31424C44
def deltaBatchVersion : UInt32 := 1
/-- `'DLOG'` — the log file header. -/
def deltaLogMagic : UInt32 := 0x474F4C44
def deltaLogVersion : UInt32 := 1
/-- `'CEP1'` — the compacted-epoch marker. -/
def compactedEpochMagic : UInt32 := 0x31504543
def compactedEpochVersion : UInt32 := 1

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

/-- The log's sequence and epoch fields have the same u64 representation.
Keeping these primitives near the epoch marker makes the companion format
match the established F* `CEP1` framing rather than accidentally introducing
a Lean-only u32 variant. -/
def writeU64LE (n : UInt64) : List UInt8 :=
  writeU32LE n.toUInt32 ++ writeU32LE (n >>> 32).toUInt32

@[simp] theorem writeU64LE_length (n : UInt64) : (writeU64LE n).length = 8 := by
  simp [writeU64LE]

def readU64LE (bs : List UInt8) (pos : Nat) : Option UInt64 := do
  let lo ← readU32LE bs pos
  let hi ← readU32LE bs (pos + 4)
  pure (lo.toUInt64 ||| (hi.toUInt64 <<< 32))

/-- The u64 framing primitive is an inverse in front of arbitrary subsequent
    bytes. It is expressed as two proved u32 fields and a checked bit-vector
    reconstruction, matching the F* DLOG/CEP1 representation. -/
theorem readU64LE_writeU64LE_append (n : UInt64) (rest : List UInt8) :
    readU64LE (writeU64LE n ++ rest) 0 = some n := by
  unfold readU64LE writeU64LE
  rw [List.append_assoc]
  rw [readU32LE_writeU32LE_append]
  simp only [Nat.zero_add]
  have hi : readU32LE
      (writeU32LE n.toUInt32 ++ (writeU32LE (n >>> 32).toUInt32 ++ rest)) 4 =
      some (n >>> 32).toUInt32 := by
    simpa only [writeU32LE_length, List.append_assoc] using
      (readU32LE_append_writeU32LE (writeU32LE n.toUInt32)
        (n >>> 32).toUInt32 rest)
  rw [hi]
  simp
  bv_decide

def natFitsU64 (n : Nat) : Bool := n.toUInt64.toNat == n

/-- One log record, framed.  The length is part of the record, so a replay
    can safely move across records of different kinds and sizes. -/
def frameEntry (payload : List UInt8) : List UInt8 :=
  writeU32LE deltaEntryMagic ++ writeU32LE deltaEntryVersion ++
  writeU32LE (UInt32.ofNat payload.length) ++ payload ++
  writeU32LE (simpleChecksum payload)

/-- Read one record back, given its payload length.

    Every failure mode returns `none` and they are DISTINCT reasons a
    replay must stop rather than continue: a wrong magic means this is
    not a record boundary, an unknown version means a newer writer
    produced it, a short buffer or a bad checksum means the append was
    TORN by a crash. In every case the correct behaviour is to
    truncate the log here — reading on would replay a half-written
    update. -/
def parseEntry (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  match readU32LE bs 0 with
  | none => none
  | some magic =>
      if magic != deltaEntryMagic then none
      else match readU32LE bs 4 with
        | none => none
        | some ver =>
            if ver != deltaEntryVersion then none
            else match readU32LE bs 8 with
              | none => none
              | some payloadLen =>
                  let n := payloadLen.toNat
                  let afterHeader := bs.drop 12
                  let payload := afterHeader.take n
                  if payload.length != n then none
                  else match readU32LE afterHeader n with
                    | none => none
                    | some stored =>
                        if stored != simpleChecksum payload then none
                        else some (payload, (afterHeader.drop n).drop 4)

/-- The bytes one framed record occupies. -/
def entryFrameSize (payloadLen : Nat) : Nat := 4 + 4 + 4 + payloadLen + 4

private theorem readEntryVersion (payload rest : List UInt8) :
    readU32LE (frameEntry payload ++ rest) 4 = some deltaEntryVersion := by
  unfold frameEntry
  exact readU32LE_append_writeU32LE (writeU32LE deltaEntryMagic) _ _

private theorem readEntryLength (payload rest : List UInt8) :
    readU32LE (frameEntry payload ++ rest) 8 = some (UInt32.ofNat payload.length) := by
  unfold frameEntry
  exact readU32LE_append_writeU32LE
    (writeU32LE deltaEntryMagic ++ writeU32LE deltaEntryVersion) _ _

private theorem dropEntryHeader (payload rest : List UInt8) :
    (frameEntry payload ++ rest).drop 12 =
      payload ++ writeU32LE (simpleChecksum payload) ++ rest := by
  simp [frameEntry, writeU32LE, List.append_assoc]

private theorem dropEntryFrame (payload rest : List UInt8) :
    (frameEntry payload ++ rest).drop (12 + payload.length + 4) = rest := by
  have hFrame : frameEntry payload ++ rest =
      (writeU32LE deltaEntryMagic ++ writeU32LE deltaEntryVersion ++
        writeU32LE (UInt32.ofNat payload.length)) ++
        (payload ++ writeU32LE (simpleChecksum payload) ++ rest) := by
    simp [frameEntry, List.append_assoc]
  rw [hFrame]
  have hHeaderLength :
      (writeU32LE deltaEntryMagic ++ writeU32LE deltaEntryVersion ++
        writeU32LE (UInt32.ofNat payload.length)).length = 12 := by simp
  rw [show 12 + payload.length + 4 =
      (writeU32LE deltaEntryMagic ++ writeU32LE deltaEntryVersion ++
        writeU32LE (UInt32.ofNat payload.length)).length + (payload.length + 4) by
      rw [hHeaderLength]
      simp [Nat.add_assoc]]
  rw [drop_append_length_add]
  rw [List.append_assoc payload (writeU32LE (simpleChecksum payload)) rest]
  rw [drop_append_length_add payload (writeU32LE (simpleChecksum payload) ++ rest) 4]
  simpa using drop_append_length_add (writeU32LE (simpleChecksum payload)) rest 0

/-- A well-sized DLE1 payload parses back to itself and leaves a following
    record untouched. The size premise is material: a u32 length field cannot
    faithfully represent an arbitrarily large Lean list. -/
theorem parseEntry_frameEntry_append (payload rest : List UInt8)
    (hSize : payload.length < UInt32.size) :
    parseEntry (frameEntry payload ++ rest) = some (payload, rest) := by
  unfold parseEntry
  rw [show readU32LE (frameEntry payload ++ rest) 0 = some deltaEntryMagic by
    unfold frameEntry
    exact readU32LE_writeU32LE_append _ _]
  rw [readEntryVersion, readEntryLength]
  simp
  rw [dropEntryHeader, Nat.mod_eq_of_lt hSize]
  constructor
  · apply Nat.min_eq_left
    have hFrameLength : (frameEntry payload).length = 16 + payload.length := by
      simp [frameEntry]
      omega
    rw [hFrameLength]
    apply Nat.le_sub_of_add_le
    calc
      payload.length + 12 ≤ payload.length + 16 :=
        Nat.add_le_add_left (by decide) _
      _ = 16 + payload.length := Nat.add_comm _ _
      _ ≤ (16 + payload.length) + rest.length := Nat.le_add_right _ _
  · rw [readU32LE_append_writeU32LE payload (simpleChecksum payload) rest]
    simp [dropEntryFrame]

/-- Replay a log: read records until one fails, returning the payloads
    recovered and whether the log ended CLEANLY.

    A torn tail is NOT an error — a crash mid-append is expected, and
    the recovery rule is "take every record that verifies, discard
    from the first that does not". Returning the clean flag lets the
    caller distinguish a tidy shutdown from a crash without changing
    what it recovered. -/
def replay (bs : List UInt8) : List (List UInt8) × Bool :=
  let rec go : Nat → List UInt8 → List (List UInt8) → List (List UInt8) × Bool
    | 0, remaining, acc => (acc, remaining.isEmpty)
    | fuel + 1, remaining, acc =>
      if remaining.isEmpty then (acc, true)
      else match parseEntry remaining with
        | none => (acc, false)          -- torn tail: stop here
        | some (payload, rest) => go fuel rest (acc ++ [payload])
  go bs.length bs []

/-- The compacted-epoch marker. A store whose base file was rebuilt
    at epoch `n` must IGNORE log records from an earlier epoch, or a
    replay would re-apply updates the compaction already folded in —
    the double-apply bug this marker exists to prevent. -/
structure EpochMarker where
  epoch : Nat
deriving Repr, DecidableEq, Inhabited

/-- `CEP1` has the same explicit magic/version/length/checksum framing as a
delta record. It records the largest epoch already folded into this immutable
base. An empty result is an explicit refusal of an unrepresentable epoch. -/
def frameEpoch (m : EpochMarker) : List UInt8 :=
  if !natFitsU64 m.epoch then [] else
  let body := writeU64LE m.epoch.toUInt64
  writeU32LE compactedEpochMagic ++ writeU32LE compactedEpochVersion ++
    writeU32LE (UInt32.ofNat body.length) ++ body ++ writeU32LE (simpleChecksum body)

def parseEpoch (bs : List UInt8) : Option EpochMarker :=
  do
    let magic ← readU32LE bs 0
    if magic != compactedEpochMagic then none else
    let version ← readU32LE bs 4
    if version != compactedEpochVersion then none else
    let bodyLen ← readU32LE bs 8
    if bodyLen != 8 then none else
    let afterHeader := bs.drop 12
    let body := afterHeader.take bodyLen.toNat
    if body.length != bodyLen.toNat then none else
    let checksum ← readU32LE afterHeader bodyLen.toNat
    let tail := (afterHeader.drop bodyLen.toNat).drop 4
    if checksum != simpleChecksum body || !tail.isEmpty then none else
    let epoch ← readU64LE body 0
    some ⟨epoch.toNat⟩

private theorem readEpochMagic (n : Nat) (h : natFitsU64 n = true) :
    readU32LE (frameEpoch ⟨n⟩) 0 = some compactedEpochMagic := by
  unfold frameEpoch
  simp only [h, Bool.not_true]
  exact readU32LE_writeU32LE_append _ _

private theorem readEpochVersion (n : Nat) (h : natFitsU64 n = true) :
    readU32LE (frameEpoch ⟨n⟩) 4 = some compactedEpochVersion := by
  unfold frameEpoch
  simp only [h, Bool.not_true]
  exact readU32LE_append_writeU32LE (writeU32LE compactedEpochMagic) _ _

private theorem readEpochLength (n : Nat) (h : natFitsU64 n = true) :
    readU32LE (frameEpoch ⟨n⟩) 8 = some 8 := by
  unfold frameEpoch
  simp only [h, Bool.not_true, writeU64LE_length]
  simpa using
    (readU32LE_append_writeU32LE
      (writeU32LE compactedEpochMagic ++ writeU32LE compactedEpochVersion) 8 _)

private theorem dropEpochHeader (n : Nat) (h : natFitsU64 n = true) :
    (frameEpoch ⟨n⟩).drop 12 =
      writeU64LE n.toUInt64 ++ writeU32LE (simpleChecksum (writeU64LE n.toUInt64)) := by
  simp [frameEpoch, h, writeU32LE]

private theorem frameEpoch_length (n : Nat) (h : natFitsU64 n = true) :
    (frameEpoch ⟨n⟩).length = 24 := by
  simp [frameEpoch, h, writeU32LE]

/-- The CEP1 companion codec preserves a representable compacted epoch.
    This is the first Lean theorem for the crash-window marker; the parallel
    F* result is `lemma_compacted_epoch_roundtrip` in
    `RDF.Store.Columnar.DeltaLog.fst`. -/
theorem parseEpoch_frameEpoch (n : Nat) (h : natFitsU64 n = true) :
    parseEpoch (frameEpoch ⟨n⟩) = some ⟨n⟩ := by
  have hnBound : n < UInt64.size := by
    simpa [natFitsU64] using h
  have hn : n.toUInt64.toNat = n := by
    change (UInt64.ofNat n).toNat = n
    rw [← UInt64.ofNatClamp_eq_ofNat n hnBound]
    exact UInt64.toNat_ofNatClamp_of_lt hnBound
  unfold parseEpoch
  rw [readEpochMagic n h]
  simp
  rw [readEpochVersion n h]
  simp
  rw [readEpochLength n h]
  simp
  rw [dropEpochHeader n h]
  simp [writeU64LE_length, frameEpoch_length n h]
  have hchecksum : readU32LE
      (writeU64LE n.toUInt64 ++ writeU32LE (simpleChecksum (writeU64LE n.toUInt64))) 8 =
      some (simpleChecksum (writeU64LE n.toUInt64)) := by
    simpa only [writeU64LE_length, List.append_assoc, List.append_nil] using
      (readU32LE_append_writeU32LE (writeU64LE n.toUInt64)
        (simpleChecksum (writeU64LE n.toUInt64)) [])
  rw [hchecksum]
  simp
  rw [show readU64LE (writeU64LE n.toUInt64) 0 = some n.toUInt64 by
    simpa using readU64LE_writeU64LE_append n.toUInt64 []]
  simp [hn]

/-- Should a record from `recordEpoch` be replayed against a base
    compacted at `baseEpoch`? Only records STRICTLY NEWER than the
    base survive. -/
def shouldReplay (baseEpoch recordEpoch : Nat) : Bool := recordEpoch > baseEpoch

/-! ## The delta entry itself

The framing above carries an opaque payload. This section gives the
payload its type and its bytes — the port of sections 3 and 4 of
`RDF.Store.Columnar.DeltaLog.fst`, which the first landing of this
module left out. An UPDATE's effect on the store is one of five
things, and each is what a replay re-applies. -/

/-- What one committed UPDATE operation did.

    `clear` takes `none` for the default graph; `drop` and `create`
    always name a graph, so they carry a bare `Iri`. -/
inductive DeltaEntry where
  | add    (t : Triple) (graph : Option Iri)
  | remove (t : Triple) (graph : Option Iri)
  | clear  (graph : Option Iri)
  | drop   (graph : Iri)
  | create (graph : Iri)
  deriving Repr, DecidableEq

def deTagAdd    : UInt8 := 0
def deTagRemove : UInt8 := 1
def deTagClear  : UInt8 := 2
def deTagDrop   : UInt8 := 3
def deTagCreate : UInt8 := 4

def subjTagIri   : UInt8 := 0
def subjTagBnode : UInt8 := 1

/-! ### Length-prefixed strings

A u32 little-endian BYTE length, then the UTF-8 bytes. The length
counts bytes, not characters, which is what makes the parse a plain
`take`/`drop` and keeps it independent of Lean's `String` internals. -/

def bytesOfString (s : String) : List UInt8 := s.toUTF8.toList

def stringOfBytes? (bs : List UInt8) : Option String :=
  String.fromUTF8? ⟨bs.toArray⟩

def serializeLString (s : String) : List UInt8 :=
  let b := bytesOfString s
  writeU32LE (UInt32.ofNat b.length) ++ b

/-- Admission-preserving length-prefixed string encoding. The list-returning
    compatibility encoder above remains useful for pure legacy code, but a
    durable DLOG writer must refuse a string whose byte length would truncate
    in its u32 prefix. -/
def serializeLString? (s : String) : Option (List UInt8) :=
  let b := bytesOfString s
  if b.length >= UInt32.size then none else some (writeU32LE (UInt32.ofNat b.length) ++ b)

def parseU8 (bs : List UInt8) : Option (UInt8 × List UInt8) :=
  match bs with
  | []      => none
  | b :: rest => some (b, rest)

def parseLString (bs : List UInt8) : Option (String × List UInt8) :=
  match readU32LE bs 0 with
  | none => none
  | some n =>
      let n := n.toNat
      let body := (bs.drop 4).take n
      if body.length != n then none
      else (stringOfBytes? body).map (fun s => (s, (bs.drop 4).drop n))

/-! ### Terms, subjects, triples

Two limits are inherited from the F\* module rather than repaired
here, and both are REFUSALS, never silent corruption.

**Triple terms.** `serializeTerm` emits a bare tag byte for an RDF 1.2
triple term and `parseTerm` refuses tag 3, so a triple term written to
a delta log cannot be read back. The F\* banner says the same and
points at its own follow-up phase. Nothing in either tree claims a
triple term round-trips through the log.

**Base direction.** A `rdf:dirLangString` literal serialises its
language tag but not its direction, so the parsed literal has a tag
and no direction. `literalWf` rejects exactly that combination, so
`parseTerm` returns `none`. The direction is not dropped into a
wrong-but-accepted literal; the record is refused. -/

def serializeTerm (t : Term) : List UInt8 :=
  match t with
  | .iri i   => termTagIri :: serializeLString i.val
  | .bnode b => termTagBnode :: serializeLString b
  | .literal l =>
      termTagLiteral :: (serializeLString l.val.lexicalForm ++
        serializeLString l.val.datatype.val ++
        (match l.val.langTag with
         | none     => [(0 : UInt8)]
         | some tag => (1 : UInt8) :: serializeLString tag))
  | .tripleTerm _ _ _ => [termTagTripleTerm]

/-- Durable delta-term admission. RDF-star triple terms are deliberately
    refused because the current DLOG reader refuses their tag too; emitting one
    would otherwise create a committed record that no replay can decode. -/
def serializeTerm? (t : Term) : Option (List UInt8) :=
  match t with
  | .iri i => (serializeLString? i.val).map (termTagIri :: ·)
  | .bnode b => (serializeLString? b).map (termTagBnode :: ·)
  | .literal l => do
      let lexical ← serializeLString? l.val.lexicalForm
      let datatype ← serializeLString? l.val.datatype.val
      match l.val.langTag with
      | none => some (termTagLiteral :: (lexical ++ datatype ++ [(0 : UInt8)]))
      | some tag => do
          let language ← serializeLString? tag
          some (termTagLiteral :: (lexical ++ datatype ++ (1 : UInt8) :: language))
  | .tripleTerm _ _ _ => none

private def mkLiteral? (lex dt : String) (tag : Option String) : Option Term :=
  if h : isIri dt then
    let l : Literal := { lexicalForm := lex, datatype := ⟨dt, h⟩,
                         langTag := tag, direction := none }
    if hw : literalWf l then some (.literal ⟨l, hw⟩) else none
  else none

def parseTerm (bs : List UInt8) : Option (Term × List UInt8) := do
  let (tag, afterTag) ← parseU8 bs
  if tag == termTagIri then
    let (i, rest) ← parseLString afterTag
    if h : isIri i then some (.iri ⟨i, h⟩, rest) else none
  else if tag == termTagBnode then
    let (b, rest) ← parseLString afterTag
    some (.bnode b, rest)
  else if tag == termTagLiteral then
    let (lex, afterLex) ← parseLString afterTag
    let (dt, afterDt)   ← parseLString afterLex
    let (flag, afterFlag) ← parseU8 afterDt
    if flag == 0 then
      (mkLiteral? lex dt none).map (fun t => (t, afterFlag))
    else if flag == 1 then do
      let (tagStr, rest) ← parseLString afterFlag
      (mkLiteral? lex dt (some tagStr)).map (fun t => (t, rest))
    else none
  else none

def serializeSubject (s : Subject) : List UInt8 :=
  match s with
  | .iri i   => subjTagIri :: serializeLString i.val
  | .bnode b => subjTagBnode :: serializeLString b

def serializeSubject? (s : Subject) : Option (List UInt8) :=
  match s with
  | .iri i => (serializeLString? i.val).map (subjTagIri :: ·)
  | .bnode b => (serializeLString? b).map (subjTagBnode :: ·)

def parseSubject (bs : List UInt8) : Option (Subject × List UInt8) := do
  let (tag, afterTag) ← parseU8 bs
  if tag == subjTagIri then
    let (i, rest) ← parseLString afterTag
    if h : isIri i then some (.iri ⟨i, h⟩, rest) else none
  else if tag == subjTagBnode then
    let (b, rest) ← parseLString afterTag
    some (.bnode b, rest)
  else none

def serializeTriple (t : Triple) : List UInt8 :=
  serializeSubject t.s ++ serializeLString t.p.val ++ serializeTerm t.o

def serializeTriple? (t : Triple) : Option (List UInt8) := do
  let subject ← serializeSubject? t.s
  let predicate ← serializeLString? t.p.val
  let object ← serializeTerm? t.o
  some (subject ++ predicate ++ object)

def parseTriple (bs : List UInt8) : Option (Triple × List UInt8) := do
  let (s, afterS) ← parseSubject bs
  let (p, afterP) ← parseLString afterS
  if h : isIri p then do
    let (o, rest) ← parseTerm afterP
    some ({ s := s, p := ⟨p, h⟩, o := o }, rest)
  else none

/-! ### Graph names

A graph name is a plain `Iri`, NOT a `WfIri`. The F\* module says why:
the default graph and the graph-management targets are not required to
satisfy the IRI grammar, so there is no well-formedness check on the
parse side either. -/

def serializeGraphOpt (g : Option Iri) : List UInt8 :=
  match g with
  | none   => [(0 : UInt8)]
  | some i => (1 : UInt8) :: serializeLString i

def serializeGraphOpt? (g : Option Iri) : Option (List UInt8) :=
  match g with
  | none => some [(0 : UInt8)]
  | some i => (serializeLString? i).map ((1 : UInt8) :: ·)

def parseGraphOpt (bs : List UInt8) : Option (Option Iri × List UInt8) := do
  let (tag, after) ← parseU8 bs
  if tag == 0 then some (none, after)
  else if tag == 1 then do
    let (i, rest) ← parseLString after
    some (some i, rest)
  else none

/-! ### The payload -/

def serializeDeltaEntryPayload (e : DeltaEntry) : List UInt8 :=
  match e with
  | .add t g    => deTagAdd :: (serializeTriple t ++ serializeGraphOpt g)
  | .remove t g => deTagRemove :: (serializeTriple t ++ serializeGraphOpt g)
  | .clear g    => deTagClear :: serializeGraphOpt g
  | .drop g     => deTagDrop :: serializeLString g
  | .create g   => deTagCreate :: serializeLString g

/-- Admission-preserving payload encoding used by durable DLB1/DLOG writers.
    Every nested length prefix is checked, and unsupported triple terms are
    rejected before framing rather than becoming a replay-time parse failure. -/
def serializeDeltaEntryPayload? (e : DeltaEntry) : Option (List UInt8) :=
  match e with
  | .add t g => do
      let triple ← serializeTriple? t
      let graph ← serializeGraphOpt? g
      some (deTagAdd :: (triple ++ graph))
  | .remove t g => do
      let triple ← serializeTriple? t
      let graph ← serializeGraphOpt? g
      some (deTagRemove :: (triple ++ graph))
  | .clear g => (serializeGraphOpt? g).map (deTagClear :: ·)
  | .drop g => (serializeLString? g).map (deTagDrop :: ·)
  | .create g => (serializeLString? g).map (deTagCreate :: ·)

def parseDeltaEntryPayload (bs : List UInt8) : Option (DeltaEntry × List UInt8) := do
  let (tag, afterTag) ← parseU8 bs
  if tag == deTagAdd then do
    let (t, afterT) ← parseTriple afterTag
    let (g, rest)   ← parseGraphOpt afterT
    some (.add t g, rest)
  else if tag == deTagRemove then do
    let (t, afterT) ← parseTriple afterTag
    let (g, rest)   ← parseGraphOpt afterT
    some (.remove t g, rest)
  else if tag == deTagClear then do
    let (g, rest) ← parseGraphOpt afterTag
    some (.clear g, rest)
  else if tag == deTagDrop then do
    let (g, rest) ← parseLString afterTag
    some (.drop g, rest)
  else if tag == deTagCreate then do
    let (g, rest) ← parseLString afterTag
    some (.create g, rest)
  else none

/-! ### Batches

One committed UPDATE request's worth of entries. `seq` is the commit
order and `epoch` is the base-file generation the batch was written
against — the epoch guard above decides whether a replay applies it. -/

structure DeltaBatch where
  seq : Nat
  epoch : Nat
  ops : List DeltaEntry
  deriving Repr, DecidableEq

/-- Remove batches whose effects are already included in the immutable base.
    A missing marker means a never-compacted collection, so every committed
    batch remains visible. -/
def filterBatchesSinceEpoch : Option Nat → List DeltaBatch → List DeltaBatch
  | none, batches => batches
  | some baseEpoch, batches => batches.filter fun batch => shouldReplay baseEpoch batch.epoch

/-! ### DLB1 committed batches and DLOG files

`DeltaEntry` is intentionally framed on its own: a batch can therefore hold
mixed add/remove/graph-management operations without an out-of-band payload
size.  A `DLB1` frame commits the complete SPARQL Update request as one unit;
the enclosing `DLOG` file is a header followed by such frames.  On recovery we
accept only the valid prefix and return the untouched suffix, which is the
expected result of a process dying during its final append. -/

def serializeFramedDeltaEntry (e : DeltaEntry) : List UInt8 :=
  frameEntry (serializeDeltaEntryPayload e)

def serializeFramedDeltaEntry? (e : DeltaEntry) : Option (List UInt8) :=
  frameEntry <$> serializeDeltaEntryPayload? e

def parseFramedDeltaEntry (bs : List UInt8) : Option (DeltaEntry × List UInt8) := do
  let (payload, rest) ← parseEntry bs
  let (entry, payloadRest) ← parseDeltaEntryPayload payload
  if payloadRest.isEmpty then some (entry, rest) else none

def serializeDeltaBatchBody? (b : DeltaBatch) : Option (List UInt8) :=
  if !natFitsU64 b.seq || !natFitsU64 b.epoch || b.ops.length >= UInt32.size then none
  else do
    let entries ← b.ops.mapM serializeFramedDeltaEntry?
    some (writeU64LE b.seq.toUInt64 ++ writeU64LE b.epoch.toUInt64 ++
      writeU32LE (UInt32.ofNat b.ops.length) ++ entries.flatten)

def parseNFramedDeltaEntries : Nat → List UInt8 → Option (List DeltaEntry × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs => do
      let (entry, afterEntry) ← parseFramedDeltaEntry bs
      let (rest, tail) ← parseNFramedDeltaEntries n afterEntry
      some (entry :: rest, tail)

def parseDeltaBatchBody (bs : List UInt8) : Option DeltaBatch := do
  let seq ← readU64LE bs 0
  let epoch ← readU64LE bs 8
  let count ← readU32LE bs 16
  let (ops, tail) ← parseNFramedDeltaEntries count.toNat (bs.drop 20)
  if tail.isEmpty then some { seq := seq.toNat, epoch := epoch.toNat, ops } else none

/-- Total DLB1 writer admission. A caller that cannot encode a batch receives
    `none`, rather than an empty frame that could be silently omitted by a
    whole-log writer. -/
def serializeDeltaBatch? (b : DeltaBatch) : Option (List UInt8) := do
  let body ← serializeDeltaBatchBody? b
  if body.length >= UInt32.size then none else
  some (writeU32LE deltaBatchMagic ++ writeU32LE deltaBatchVersion ++
    writeU32LE (UInt32.ofNat body.length) ++ body ++ writeU32LE (simpleChecksum body))

/-- Compatibility writer for existing in-memory callers. Durable writers must
    use `serializeDeltaBatch?` and reject `none`; this legacy total projection
    is retained only so older pure call sites do not acquire an unsound
    implicit fallback. -/
def serializeDeltaBatch (b : DeltaBatch) : List UInt8 :=
  (serializeDeltaBatch? b).getD []

def parseDeltaBatch (bs : List UInt8) : Option (DeltaBatch × List UInt8) := do
  let magic ← readU32LE bs 0
  if magic != deltaBatchMagic then none else
  let version ← readU32LE bs 4
  if version != deltaBatchVersion then none else
  let bodyLen ← readU32LE bs 8
  let afterHeader := bs.drop 12
  let body := afterHeader.take bodyLen.toNat
  if body.length != bodyLen.toNat then none else
  let checksum ← readU32LE afterHeader bodyLen.toNat
  if checksum != simpleChecksum body then none else
  let batch ← parseDeltaBatchBody body
  some (batch, (afterHeader.drop bodyLen.toNat).drop 4)

def replayDeltaBatches (bs : List UInt8) : List DeltaBatch × List UInt8 :=
  let rec go : Nat → List UInt8 → List DeltaBatch → List DeltaBatch × List UInt8
    | 0, remaining, acc => (acc, remaining)
    | fuel + 1, remaining, acc =>
      if remaining.isEmpty then (acc, [])
      else match parseDeltaBatch remaining with
        | none => (acc, remaining)
        | some (batch, rest) => go fuel rest (acc ++ [batch])
  go bs.length bs []

/-- Total DLOG writer admission: all committed batches must be representable.
    Unlike `List.flatMap serializeDeltaBatch`, this cannot turn one rejected
    batch into a log that silently lacks an UPDATE. -/
def serializeLog? (batches : List DeltaBatch) : Option (List UInt8) := do
  let frames ← batches.mapM serializeDeltaBatch?
  pure (writeU32LE deltaLogMagic ++ writeU32LE deltaLogVersion ++ frames.flatten)

/-- Compatibility writer for existing pure callers. New durable paths must use
    `serializeLog?` and surface encoding refusal. -/
def serializeLog (batches : List DeltaBatch) : List UInt8 :=
  (serializeLog? batches).getD []

def parseLog (bs : List UInt8) : Option (List DeltaBatch × List UInt8) := do
  let magic ← readU32LE bs 0
  if magic != deltaLogMagic then none else
  let version ← readU32LE bs 4
  if version != deltaLogVersion then none else
  some (replayDeltaBatches (bs.drop 8))

/-! ### Build-time checks

Every round trip is checked with a NON-EMPTY tail, so a parser that
consumed the wrong number of bytes fails the check instead of passing
on a buffer that happened to end exactly where it stopped. -/

private def tail : List UInt8 := [0xAA, 0xBB, 0xCC]

private def rtEntry (e : DeltaEntry) : Bool :=
  parseDeltaEntryPayload (serializeDeltaEntryPayload e ++ tail) == some (e, tail)

private def exIri : WfIri := ⟨"http://example.org/s", by decide⟩
private def exP   : WfIri := ⟨"http://example.org/p", by decide⟩

#guard rtEntry (.clear none)
#guard rtEntry (.clear (some "http://example.org/g"))
#guard rtEntry (.drop "http://example.org/g")
#guard rtEntry (.create "")
#guard rtEntry (.add ⟨.iri exIri, exP, .iri exIri⟩ none)
#guard rtEntry (.add ⟨.bnode "b0", exP, .bnode "b1"⟩ (some "http://example.org/g"))
#guard rtEntry (.remove ⟨.iri exIri, exP, .literal (Literal.string "plain")⟩ none)
#guard rtEntry (.remove ⟨.iri exIri, exP, .literal (Literal.langString "hi" "en")⟩ none)

/-! A multi-byte UTF-8 lexical form round-trips: the length prefix
counts BYTES, and a character count would be wrong here. -/

#guard rtEntry (.add ⟨.iri exIri, exP, .literal (Literal.string "héllo — ☃")⟩ none)
#guard (serializeLString "é").length == 6      -- 4 length bytes + 2 UTF-8 bytes

/-! A triple term is REFUSED, not misread. -/

#guard (parseTerm (serializeTerm (.tripleTerm (.iri exIri) exP (.iri exIri)))).isNone

/-! An unknown entry tag is refused. -/

#guard (parseDeltaEntryPayload [9, 0, 0, 0, 0]).isNone

/-! A TRUNCATED length-prefixed string is refused rather than
    returning a short string: the prefix claims 9 bytes and 3 follow. -/

#guard (parseLString (writeU32LE 9 ++ [97, 98, 99])).isNone

end L4Factoidal.Storage
