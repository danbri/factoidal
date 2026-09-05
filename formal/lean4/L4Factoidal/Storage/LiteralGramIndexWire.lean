/-
L4Factoidal.Storage.LiteralGramIndexWire — LGI1 literal search index bytes.

Design record: `docs/designissues/2026-09-04-literal-token-index.md`, section 3.

LGI1 is an immutable companion to one IBK3 or IBK4 block. It stores, for every
character 3-gram of the case-folded lexical form of every literal in the block
dictionary, the ascending local term IDs that carry that gram. The local IDs
are the PTD1 dictionary positions TLI1 uses, so a candidate reaches rows
through the existing OLI2 object index and no second identity scheme appears.

    magic "LGI1", version 1
    prefix   u32 magic, u8 version, [32] targetIBKSha256,
             u32 gramLength, u32 dictCount, u32 literalCount,
             u32 gramCount, u32 directoryBytes, u32 postingsBytes
    directory  gramCount entries, ascending by gram bytes:
             u32 gramByteLength, gram UTF-8, u32 offset, u32 length,
             u32 postingCount
    postings per gram: the first ID as u32, then each later ID as the u32 gap
             from the previous one
    u32      crc32c(payload)

The directory holds one entry per gram rather than a page of grams, because a
lookup wants one posting run and nothing else: a range reader fetches the
prefix, then the directory, then only the runs its needle names.

## Encoder admission equals decoder admission

`supported` is the encoder gate and `decode?` re-runs every one of its
conditions on what it reads back: the gram order is strictly ascending, each
posting list is strictly ascending and non-empty, every ID is below the
dictionary bound `dictCount`, each gram is `gramLength` characters, and
the directory extents are contiguous and cover the posting area exactly. An
encoder that emitted bytes its own decoder refuses would be a defect, and
`#guard`s below pin the round trip and four rejections.

## LGI2

Version 2 changes two things and keeps every other byte rule.

    magic "LGI2", version 2
    prefix   u32 magic, u8 version, [32] targetIBKSha256,
             u32 gramLength, u32 dictCount, u32 literalCount,
             u32 gramCount, u32 directoryBytes, u32 postingsBytes,
             u32 opaqueCount
    opaque   opaqueCount ascending distinct u32 local IDs
    directory  as LGI1, except that a run's `length` is its byte length and is
             no longer four times its posting count
    postings per gram: the first ID as an unsigned LEB128 varint, then each
             later ID as the LEB128 gap from the previous one
    u32      crc32c(payload)

The gaps were fixed-width `u32` in LGI1. On the SKOS `skos:prefLabel` block
that is 3,018,141 bytes against a 5,571,302 byte block, 54%.

The opaque list holds the dictionary positions of the literals the index did
NOT gram: the out-of-line (tag 4) literals of the version-2 term codec, whose
lexical form is not in the block. `LiteralGramIndex.candidatesOpaque?` returns
them for every needle it serves, and
`LiteralGramIndex.mem_candidatesOpaque_of_opaque` states that they are always
candidates, so the filter stays a superset when a block holds blob literals.

LGI1 bytes are unchanged. An LGI1 artifact carrying a non-empty opaque list is
refused by `supported`, because LGI1 has nowhere to write it.

## Theorem status

`decodeLeb128_encodeLeb128` and `parsePostings2_encodePostings2` are proved:
the varint and one posting run round-trip. The END-TO-END LGI2 round trip is
pinned by the `#guard`s below and NOT by a theorem, which is the position LGI1
is in for the same reason: `decode?` reads through `ByteArray.extract` and a
crc32c over a slice, and no lemma relates those to the encoder's list
assembly yet.

There is ONE decoder here. `TermLocalIndexWire` carries a `decodeSpec?` beside
its `decode?` because its byte-indexed reader is an optimisation of a list
reader and the two must be proved equal; LGI1 has no such pair yet, so there
is nothing to prove equal and no theorem is claimed.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.LiteralGramIndex
import L4Factoidal.Storage.BlockWireV0

namespace L4Factoidal.Storage.LiteralGramIndexWire

open L4Factoidal.RDF
open L4Factoidal.Storage
open L4Factoidal.Storage.BlockWireV0
open L4Factoidal.Storage.LiteralGramIndex

def magic : UInt32 := 0x3149474C /-- `LGI1` little endian. -/
def version : UInt8 := 1
def prefixBytes : Nat := 4 + 1 + 32 + 4 + 4 + 4 + 4 + 4 + 4
def crcBytes : Nat := 4

def magic2 : UInt32 := 0x3249474C /-- `LGI2` little endian. -/
def version2 : UInt8 := 2
/-- LGI1's prefix plus the u32 `opaqueCount`. -/
def prefixBytes2 : Nat := prefixBytes + 4

/-- The fixed LGI1 prefix. A range reader obtains this before it fetches the
directory or any posting run. -/
structure Prefix where
  targetIBKSha256 : ByteArray
  gramLength : Nat
  dictCount : Nat
  literalCount : Nat
  gramCount : Nat
  directoryBytes : Nat
  postingsBytes : Nat
  deriving DecidableEq

/-- The fixed LGI2 prefix: LGI1's fields plus the count of opaque local IDs. -/
structure Prefix2 where
  targetIBKSha256 : ByteArray
  gramLength : Nat
  dictCount : Nat
  literalCount : Nat
  gramCount : Nat
  directoryBytes : Nat
  postingsBytes : Nat
  opaqueCount : Nat
  deriving DecidableEq

structure DirectoryEntry where
  gram : List Char
  offset : Nat
  length : Nat
  postingCount : Nat
  deriving DecidableEq

structure Artifact where
  targetIBKSha256 : ByteArray
  index : Index
  deriving DecidableEq

def byteArrayOfList (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray
def listOfByteArray (xs : ByteArray) : List UInt8 := xs.data.toList
def fitsU32 (n : Nat) : Bool := n < UInt32.size

def gramBytes (gram : List Char) : List UInt8 := (String.ofList gram).toUTF8.data.toList

def takeExact (n : Nat) (xs : List UInt8) : Option (List UInt8 × List UInt8) :=
  let taken := xs.take n
  if taken.length == n then some (taken, xs.drop n) else none

/-! ## 1. Admission -/

/-- Strictly ascending local IDs. An equal pair is refused: a posting list is
a set, and a repeated ID would make a candidate list report a term twice. -/
def idsAscending : List Nat → Bool
  | [] | [_] => true
  | a :: b :: rest => a < b && idsAscending (b :: rest)

def gramsAscending : List Posting → Bool
  | [] | [_] => true
  | a :: b :: rest => lessGram a.gram b.gram && gramsAscending (b :: rest)

/-- The encoder gate. `decode?` re-runs every conjunct on what it reads. -/
def supported (artifact : Artifact) : Bool :=
  artifact.targetIBKSha256.size == 32 &&
    artifact.index.gramLength == gramLength &&
    fitsU32 artifact.index.dictCount && fitsU32 artifact.index.literalCount &&
    fitsU32 artifact.index.postings.size &&
    artifact.index.postings.toList.all (fun posting =>
      posting.gram.length == gramLength &&
        fitsU32 (gramBytes posting.gram).length &&
        !posting.ids.isEmpty &&
        idsAscending posting.ids &&
        fitsU32 posting.ids.length &&
        posting.ids.all (fun id => id < artifact.index.dictCount)) &&
    gramsAscending artifact.index.postings.toList &&
    /- LGI1 has no field for the opaque list, so an artifact carrying one is
       refused rather than written without it. -/
    artifact.index.opaqueIds.isEmpty

/-! ## 2. Encoding -/

/-- One posting run: the first ID, then the gap to each later ID. -/
def encodePostings : List Nat → Nat → List UInt8
  | [], _ => []
  | id :: rest, previous => writeU32LE (UInt32.ofNat (id - previous)) ++ encodePostings rest id

def postingRunBytes (posting : Posting) : List UInt8 := encodePostings posting.ids 0

def encodeDirectoryEntry (posting : Posting) (offset length : Nat) : List UInt8 :=
  let g := gramBytes posting.gram
  writeU32LE (UInt32.ofNat g.length) ++ g ++
    writeU32LE (UInt32.ofNat offset) ++ writeU32LE (UInt32.ofNat length) ++
    writeU32LE (UInt32.ofNat posting.ids.length)

/-- The directory and the posting area, built in one pass so the offsets and
lengths in the directory are the extents of the runs beside them.

The accumulators hold the per-gram CHUNKS in reverse, reversed and flattened
once at the end. They held one flat list appended forward until 2026-09-05,
which is quadratic in the encoded size: packing the SKOS `skos:prefLabel`
block took 4 seconds before the sidecar existed and 520 seconds after it, for
21,843 grams and 3,018,145 encoded bytes. The bytes are unchanged — a list of
chunks reversed and flattened is the same sequence the forward appends
produced — and the round-trip `#guard`s below pin that. -/
def encodeBody : List Posting → Nat → List (List UInt8) → List (List UInt8) →
    (List UInt8 × List UInt8)
  | [], _, directory, runs => (directory.reverse.flatten, runs.reverse.flatten)
  | posting :: rest, offset, directory, runs =>
      let run := postingRunBytes posting
      encodeBody rest (offset + run.length)
        (encodeDirectoryEntry posting offset run.length :: directory) (run :: runs)

def encode? (artifact : Artifact) : Option ByteArray := do
  if !supported artifact then none else
  let (directory, runs) := encodeBody artifact.index.postings.toList 0 [] []
  if !fitsU32 directory.length || !fitsU32 runs.length then none else
  let payload := artifact.targetIBKSha256.data.toList ++
    writeU32LE (UInt32.ofNat gramLength) ++
    writeU32LE (UInt32.ofNat artifact.index.dictCount) ++
    writeU32LE (UInt32.ofNat artifact.index.literalCount) ++
    writeU32LE (UInt32.ofNat artifact.index.postings.size) ++
    writeU32LE (UInt32.ofNat directory.length) ++
    writeU32LE (UInt32.ofNat runs.length) ++ directory ++ runs
  some <| byteArrayOfList (writeU32LE magic ++ [version] ++ payload ++ writeU32LE (crc32c payload))

/-! ## 3. Decoding -/

/-- Strictly decode just the fixed-length LGI1 prefix. -/
def decodePrefix? (bytes : ByteArray) : Option Prefix := do
  if bytes.size != prefixBytes then none else do
  let input := listOfByteArray bytes
  let foundMagic ← readU32LE input 0
  if foundMagic != magic then none else do
  let (foundVersion, afterVersion) ← parseU8 (input.drop 4)
  if foundVersion != version then none else do
  let (target, afterTarget) ← takeExact 32 afterVersion
  let foundGramLength ← readU32LE afterTarget 0
  let dictCount ← readU32LE afterTarget 4
  let literalCount ← readU32LE afterTarget 8
  let gramCount ← readU32LE afterTarget 12
  let directoryBytes ← readU32LE afterTarget 16
  let postingsBytes ← readU32LE afterTarget 20
  if foundGramLength.toNat != gramLength then none else
    some { targetIBKSha256 := byteArrayOfList target, gramLength := foundGramLength.toNat,
           dictCount := dictCount.toNat, literalCount := literalCount.toNat,
           gramCount := gramCount.toNat,
           directoryBytes := directoryBytes.toNat, postingsBytes := postingsBytes.toNat }

def parseDirectoryEntry (xs : List UInt8) : Option (DirectoryEntry × List UInt8) := do
  let gramLen ← readU32LE xs 0
  let (raw, afterGram) ← takeExact gramLen.toNat (xs.drop 4)
  let text ← String.fromUTF8? (ByteArray.mk raw.toArray)
  let offset ← readU32LE afterGram 0
  let length ← readU32LE afterGram 4
  let postingCount ← readU32LE afterGram 8
  if gramBytes text.toList != raw then none else
    some ({ gram := text.toList, offset := offset.toNat, length := length.toNat,
            postingCount := postingCount.toNat }, afterGram.drop 12)

def parseDirectory : Nat → List UInt8 → List DirectoryEntry →
    Option (List DirectoryEntry × List UInt8)
  | 0, xs, reversed => some (reversed.reverse, xs)
  | count + 1, xs, reversed => do
      let (entry, rest) ← parseDirectoryEntry xs
      parseDirectory count rest (entry :: reversed)

/-- Read one posting run, undoing the gaps. -/
def parsePostings : Nat → List UInt8 → Nat → List Nat → Option (List Nat)
  | 0, xs, _, reversed => if xs.isEmpty then some reversed.reverse else none
  | count + 1, xs, previous, reversed => do
      let gap ← readU32LE xs 0
      let id := previous + gap.toNat
      parsePostings count (xs.drop 4) id (id :: reversed)

/-- The directory extents must be contiguous from zero and cover the posting
area exactly. A gap or an overlap would let two grams disagree about the same
bytes. -/
def entriesContiguous : List DirectoryEntry → Nat → Bool
  | [], _ => true
  | entry :: rest, expected =>
      entry.length > 0 && entry.offset == expected && entry.length == 4 * entry.postingCount &&
        entriesContiguous rest (expected + entry.length)

def entriesAscending : List DirectoryEntry → Bool
  | [] | [_] => true
  | a :: b :: rest => lessGram a.gram b.gram && entriesAscending (b :: rest)

def decodeRuns (dictCount : Nat) (runs : ByteArray) :
    List DirectoryEntry → List Posting → Option (List Posting)
  | [], reversed => some reversed.reverse
  | entry :: rest, reversed => do
      if entry.offset + entry.length > runs.size then none else do
      let slice := runs.extract entry.offset (entry.offset + entry.length)
      let ids ← parsePostings entry.postingCount (listOfByteArray slice) 0 []
      if ids.isEmpty || !idsAscending ids || !ids.all (fun id => id < dictCount) ||
          entry.gram.length != gramLength then none else
        decodeRuns dictCount runs rest ({ gram := entry.gram, ids } :: reversed)

/-- The LGI1 admission decoder. Every encoder condition is re-run here. -/
def decode? (bytes : ByteArray) : Option Artifact := do
  if bytes.size < prefixBytes + crcBytes then none else do
  let header ← decodePrefix? (bytes.extract 0 prefixBytes)
  let payloadLength := 32 + 24 + header.directoryBytes + header.postingsBytes
  if bytes.size != 5 + payloadLength + crcBytes then none else do
  let storedCrc ← readU32LE (listOfByteArray (bytes.extract (bytes.size - crcBytes) bytes.size)) 0
  if storedCrc !=
      (crc32cAppendArray 0xFFFFFFFF (bytes.extract 5 (5 + payloadLength)) ^^^ 0xFFFFFFFF) then
    none else do
  let directory := bytes.extract prefixBytes (prefixBytes + header.directoryBytes)
  let runs := bytes.extract (prefixBytes + header.directoryBytes)
    (prefixBytes + header.directoryBytes + header.postingsBytes)
  let (entries, trailing) ← parseDirectory header.gramCount (listOfByteArray directory) []
  if !trailing.isEmpty || !entriesContiguous entries 0 || !entriesAscending entries ||
      entries.foldl (fun total entry => total + entry.length) 0 != runs.size then none else do
  let postings ← decodeRuns header.dictCount runs entries []
  some { targetIBKSha256 := header.targetIBKSha256
         index := { gramLength := gramLength, dictCount := header.dictCount,
                    literalCount := header.literalCount,
                    postings := postings.toArray } }

/-- The one candidate posting run for a gram, by its directory entry. -/
def entryFor? (entries : List DirectoryEntry) (wanted : List Char) : Option DirectoryEntry :=
  entries.find? (fun entry => entry.gram == wanted)

/-! ## 4. LGI2

### 4.1 Unsigned LEB128

Seven bits of the value per byte, the low group first, the continuation bit
set on every byte except the last. A gap below 128 therefore costs one byte
where LGI1 spends four. -/

def encodeLeb128 (n : Nat) : List UInt8 :=
  if h : n < 128 then [UInt8.ofNat n]
  else UInt8.ofNat (128 + n % 128) :: encodeLeb128 (n / 128)
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- Read one varint. `fuel` bounds the byte count, so a run of continuation
bytes cannot make the reader walk the rest of the artifact. -/
def decodeLeb128Go : Nat → List UInt8 → Nat → Nat → Option (Nat × List UInt8)
  | 0, _, _, _ => none
  | _ + 1, [], _, _ => none
  | fuel + 1, b :: rest, shift, acc =>
      let value := acc + (b.toNat % 128) * shift
      if b.toNat < 128 then some (value, rest)
      else decodeLeb128Go fuel rest (shift * 128) value

/-- Five bytes carry thirty-five bits, which covers every u32 local ID and
gap. A sixth byte is refused. -/
def leb128Fuel : Nat := 5

def decodeLeb128 (bytes : List UInt8) : Option (Nat × List UInt8) :=
  decodeLeb128Go leb128Fuel bytes 1 0

private theorem u8_toNat_ofNat {n : Nat} (h : n < 256) : (UInt8.ofNat n).toNat = n := by
  simp [UInt8.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem leb_step (n shift : Nat) :
    n % 128 * shift + n / 128 * (shift * 128) = n * shift := by
  have h : 128 * (n / 128) + n % 128 = n := Nat.div_add_mod n 128
  calc n % 128 * shift + n / 128 * (shift * 128)
      = n % 128 * shift + 128 * (n / 128) * shift := by
        rw [Nat.mul_comm shift 128, ← Nat.mul_assoc, Nat.mul_comm (n / 128) 128]
    _ = (128 * (n / 128) + n % 128) * shift := by
        rw [Nat.add_mul]; exact Nat.add_comm _ _
    _ = n * shift := by rw [h]

theorem decodeLeb128Go_encodeLeb128 : ∀ (fuel n : Nat), n < 128 ^ (fuel + 1) →
    ∀ (shift acc : Nat) (rest : List UInt8),
      decodeLeb128Go (fuel + 1) (encodeLeb128 n ++ rest) shift acc =
        some (acc + n * shift, rest) := by
  intro fuel
  induction fuel with
  | zero =>
      intro n hn shift acc rest
      have hlt : n < 128 := by simpa using hn
      rw [encodeLeb128, dif_pos hlt]
      simp only [List.cons_append, List.nil_append, decodeLeb128Go]
      rw [u8_toNat_ofNat (by omega), Nat.mod_eq_of_lt hlt, if_pos hlt]
  | succ fuel ih =>
      intro n hn shift acc rest
      by_cases hlt : n < 128
      · rw [encodeLeb128, dif_pos hlt]
        simp only [List.cons_append, List.nil_append, decodeLeb128Go]
        rw [u8_toNat_ofNat (by omega), Nat.mod_eq_of_lt hlt, if_pos hlt]
      · rw [encodeLeb128, dif_neg hlt]
        simp only [List.cons_append, decodeLeb128Go]
        have hmodlt : n % 128 < 128 := Nat.mod_lt _ (by omega)
        rw [u8_toNat_ofNat (by omega)]
        have hmod : (128 + n % 128) % 128 = n % 128 := by omega
        rw [hmod, if_neg (by omega)]
        have hdiv : n / 128 < 128 ^ (fuel + 1) := by
          rw [Nat.div_lt_iff_lt_mul (by omega)]
          calc n < 128 ^ (fuel + 1 + 1) := hn
            _ = 128 ^ (fuel + 1) * 128 := by rw [Nat.pow_succ]
        rw [ih (n / 128) hdiv (shift * 128) (acc + n % 128 * shift) rest]
        rw [Nat.add_assoc, leb_step n shift]

/-- The varint round trip for every value a u32 local ID or gap can take. -/
theorem decodeLeb128_encodeLeb128 (n : Nat) (h : n < 4294967296) (rest : List UInt8) :
    decodeLeb128 (encodeLeb128 n ++ rest) = some (n, rest) := by
  have hpow : (128 : Nat) ^ 5 = 34359738368 := by decide +kernel
  have hb : n < 128 ^ (4 + 1) := by rw [show 4 + 1 = 5 from rfl, hpow]; omega
  have hgo := decodeLeb128Go_encodeLeb128 4 n hb 1 0 rest
  simpa [decodeLeb128, leb128Fuel] using hgo

/-! ### 4.2 Posting runs -/

/-- One posting run: the first ID, then the gap to each later ID, each as a
varint. -/
def encodePostings2 : List Nat → Nat → List UInt8
  | [], _ => []
  | id :: rest, previous => encodeLeb128 (id - previous) ++ encodePostings2 rest id

def postingRunBytes2 (posting : Posting) : List UInt8 := encodePostings2 posting.ids 0

/-- Read one posting run, undoing the varint gaps. -/
def parsePostings2 : Nat → List UInt8 → Nat → List Nat → Option (List Nat)
  | 0, xs, _, reversed => if xs.isEmpty then some reversed.reverse else none
  | count + 1, xs, previous, reversed => do
      let (gap, rest) ← decodeLeb128 xs
      let id := previous + gap
      parsePostings2 count rest id (id :: reversed)

/-- Non-decreasing from a starting point. `idsAscending` gives this with the
first ID at or above zero, which every ID is. -/
def gapsFrom (previous : Nat) : List Nat → Bool
  | [] => true
  | id :: rest => previous ≤ id && gapsFrom id rest

/-- Every member of an ascending list is at or above its head. -/
theorem le_of_mem_idsAscending : ∀ (head : Nat) (tail : List Nat) (j : Nat),
    idsAscending (head :: tail) = true → j ∈ head :: tail → head ≤ j := by
  intro head tail
  induction tail generalizing head with
  | nil => intro j _ hj; simp only [List.mem_singleton] at hj; omega
  | cons next rest ih =>
      intro j hasc hj
      simp only [idsAscending, Bool.and_eq_true, decide_eq_true_eq] at hasc
      rcases List.mem_cons.mp hj with rfl | hj'
      · omega
      · have := ih next j hasc.2 hj'
        omega

theorem gapsFrom_of_idsAscending : ∀ (ids : List Nat) (previous : Nat),
    idsAscending ids = true → (∀ id ∈ ids, previous ≤ id) → gapsFrom previous ids = true := by
  intro ids
  induction ids with
  | nil => intro previous _ _; simp [gapsFrom]
  | cons id rest ih =>
      intro previous hasc hle
      have hrest : idsAscending rest = true := by
        cases rest with
        | nil => simp [idsAscending]
        | cons next tail => exact (Bool.and_eq_true _ _).mp hasc |>.2
      simp only [gapsFrom, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨hle id (by simp), ih id hrest ?_⟩
      intro j hj
      exact le_of_mem_idsAscending id rest j hasc (List.mem_cons_of_mem _ hj)

/-- One posting run round-trips: the varint gaps read back as the ascending
IDs that produced them. -/
theorem parsePostings2_encodePostings2 : ∀ (ids : List Nat) (previous : Nat)
    (reversed : List Nat), gapsFrom previous ids = true →
    (∀ id ∈ ids, id < 4294967296) →
    parsePostings2 ids.length (encodePostings2 ids previous) previous reversed =
      some (reversed.reverse ++ ids) := by
  intro ids
  induction ids with
  | nil => intro previous reversed _ _; simp [parsePostings2, encodePostings2]
  | cons id rest ih =>
      intro previous reversed hgaps hbound
      simp only [gapsFrom, Bool.and_eq_true, decide_eq_true_eq] at hgaps
      have hid : id < 4294967296 := hbound id (by simp)
      have hgap : id - previous < 4294967296 := by omega
      simp only [List.length_cons, encodePostings2, parsePostings2]
      rw [decodeLeb128_encodeLeb128 _ hgap]
      simp only [bind, Option.bind]
      have hsum : previous + (id - previous) = id := by omega
      rw [hsum, ih id (id :: reversed) hgaps.2 (fun j hj => hbound j (by simp [hj]))]
      simp

/-- The whole run of one posting list round-trips. -/
theorem parsePostings2_postingRunBytes2 (posting : Posting)
    (hasc : idsAscending posting.ids = true)
    (hbound : ∀ id ∈ posting.ids, id < 4294967296) :
    parsePostings2 posting.ids.length (postingRunBytes2 posting) 0 [] = some posting.ids := by
  have hgaps := gapsFrom_of_idsAscending posting.ids 0 hasc (by intro id _; omega)
  simpa [postingRunBytes2] using
    parsePostings2_encodePostings2 posting.ids 0 [] hgaps hbound

/-! ### 4.3 The LGI2 artifact -/

/-- The LGI2 encoder gate. `decode2?` re-runs every conjunct on what it
reads. -/
def supported2 (artifact : Artifact) : Bool :=
  artifact.targetIBKSha256.size == 32 &&
    artifact.index.gramLength == gramLength &&
    fitsU32 artifact.index.dictCount && fitsU32 artifact.index.literalCount &&
    fitsU32 artifact.index.postings.size &&
    artifact.index.postings.toList.all (fun posting =>
      posting.gram.length == gramLength &&
        fitsU32 (gramBytes posting.gram).length &&
        !posting.ids.isEmpty &&
        idsAscending posting.ids &&
        fitsU32 posting.ids.length &&
        posting.ids.all (fun id => id < artifact.index.dictCount)) &&
    gramsAscending artifact.index.postings.toList &&
    fitsU32 artifact.index.opaqueIds.length &&
    idsAscending artifact.index.opaqueIds &&
    artifact.index.opaqueIds.all (fun id => id < artifact.index.dictCount)

def encodeBody2 : List Posting → Nat → List (List UInt8) → List (List UInt8) →
    (List UInt8 × List UInt8)
  | [], _, directory, runs => (directory.reverse.flatten, runs.reverse.flatten)
  | posting :: rest, offset, directory, runs =>
      let run := postingRunBytes2 posting
      encodeBody2 rest (offset + run.length)
        (encodeDirectoryEntry posting offset run.length :: directory) (run :: runs)

def encodeOpaque (ids : List Nat) : List UInt8 :=
  ids.flatMap (fun id => writeU32LE (UInt32.ofNat id))

def encode2? (artifact : Artifact) : Option ByteArray := do
  if !supported2 artifact then none else
  let (directory, runs) := encodeBody2 artifact.index.postings.toList 0 [] []
  if !fitsU32 directory.length || !fitsU32 runs.length then none else
  let payload := artifact.targetIBKSha256.data.toList ++
    writeU32LE (UInt32.ofNat gramLength) ++
    writeU32LE (UInt32.ofNat artifact.index.dictCount) ++
    writeU32LE (UInt32.ofNat artifact.index.literalCount) ++
    writeU32LE (UInt32.ofNat artifact.index.postings.size) ++
    writeU32LE (UInt32.ofNat directory.length) ++
    writeU32LE (UInt32.ofNat runs.length) ++
    writeU32LE (UInt32.ofNat artifact.index.opaqueIds.length) ++
    encodeOpaque artifact.index.opaqueIds ++ directory ++ runs
  some <| byteArrayOfList (writeU32LE magic2 ++ [version2] ++ payload ++ writeU32LE (crc32c payload))

/-- Strictly decode just the fixed-length LGI2 prefix. -/
def decodePrefix2? (bytes : ByteArray) : Option Prefix2 := do
  if bytes.size != prefixBytes2 then none else do
  let input := listOfByteArray bytes
  let foundMagic ← readU32LE input 0
  if foundMagic != magic2 then none else do
  let (foundVersion, afterVersion) ← parseU8 (input.drop 4)
  if foundVersion != version2 then none else do
  let (target, afterTarget) ← takeExact 32 afterVersion
  let foundGramLength ← readU32LE afterTarget 0
  let dictCount ← readU32LE afterTarget 4
  let literalCount ← readU32LE afterTarget 8
  let gramCount ← readU32LE afterTarget 12
  let directoryBytes ← readU32LE afterTarget 16
  let postingsBytes ← readU32LE afterTarget 20
  let opaqueCount ← readU32LE afterTarget 24
  if foundGramLength.toNat != gramLength then none else
    some { targetIBKSha256 := byteArrayOfList target, gramLength := foundGramLength.toNat,
           dictCount := dictCount.toNat, literalCount := literalCount.toNat,
           gramCount := gramCount.toNat,
           directoryBytes := directoryBytes.toNat, postingsBytes := postingsBytes.toNat,
           opaqueCount := opaqueCount.toNat }

def parseOpaque : Nat → List UInt8 → List Nat → Option (List Nat)
  | 0, xs, reversed => if xs.isEmpty then some reversed.reverse else none
  | count + 1, xs, reversed => do
      let value ← readU32LE xs 0
      parseOpaque count (xs.drop 4) (value.toNat :: reversed)

/-- The LGI2 form of `entriesContiguous`. A run's byte length is no longer four
times its posting count, because the gaps are varints, so the test is that the
extents are contiguous from zero and that a run holds at least one ID. -/
def entriesContiguous2 : List DirectoryEntry → Nat → Bool
  | [], _ => true
  | entry :: rest, expected =>
      entry.length > 0 && entry.offset == expected && entry.postingCount > 0 &&
        entriesContiguous2 rest (expected + entry.length)

def decodeRuns2 (dictCount : Nat) (runs : ByteArray) :
    List DirectoryEntry → List Posting → Option (List Posting)
  | [], reversed => some reversed.reverse
  | entry :: rest, reversed => do
      if entry.offset + entry.length > runs.size then none else do
      let slice := runs.extract entry.offset (entry.offset + entry.length)
      let ids ← parsePostings2 entry.postingCount (listOfByteArray slice) 0 []
      if ids.isEmpty || !idsAscending ids || !ids.all (fun id => id < dictCount) ||
          entry.gram.length != gramLength then none else
        decodeRuns2 dictCount runs rest ({ gram := entry.gram, ids } :: reversed)

/-- The LGI2 admission decoder. Every encoder condition is re-run here. -/
def decode2? (bytes : ByteArray) : Option Artifact := do
  if bytes.size < prefixBytes2 + crcBytes then none else do
  let header ← decodePrefix2? (bytes.extract 0 prefixBytes2)
  let opaqueBytes := 4 * header.opaqueCount
  let payloadLength := 32 + 28 + opaqueBytes + header.directoryBytes + header.postingsBytes
  if bytes.size != 5 + payloadLength + crcBytes then none else do
  let storedCrc ← readU32LE (listOfByteArray (bytes.extract (bytes.size - crcBytes) bytes.size)) 0
  if storedCrc !=
      (crc32cAppendArray 0xFFFFFFFF (bytes.extract 5 (5 + payloadLength)) ^^^ 0xFFFFFFFF) then
    none else do
  let opaqueArea := bytes.extract prefixBytes2 (prefixBytes2 + opaqueBytes)
  let directoryStart := prefixBytes2 + opaqueBytes
  let directory := bytes.extract directoryStart (directoryStart + header.directoryBytes)
  let runs := bytes.extract (directoryStart + header.directoryBytes)
    (directoryStart + header.directoryBytes + header.postingsBytes)
  let opaqueIds ← parseOpaque header.opaqueCount (listOfByteArray opaqueArea) []
  if !idsAscending opaqueIds || !opaqueIds.all (fun id => id < header.dictCount) then none else do
  let (entries, trailing) ← parseDirectory header.gramCount (listOfByteArray directory) []
  if !trailing.isEmpty || !entriesContiguous2 entries 0 || !entriesAscending entries ||
      entries.foldl (fun total entry => total + entry.length) 0 != runs.size then none else do
  let postings ← decodeRuns2 header.dictCount runs entries []
  some { targetIBKSha256 := header.targetIBKSha256
         index := { gramLength := gramLength, dictCount := header.dictCount,
                    literalCount := header.literalCount,
                    postings := postings.toArray, opaqueIds := opaqueIds } }

/-- The encoded byte count of one index in each version, for the size
measurement of the design record. -/
def encodedBytes1 (artifact : Artifact) : Option Nat := (encode? artifact).map ByteArray.size
def encodedBytes2 (artifact : Artifact) : Option Nat := (encode2? artifact).map ByteArray.size

private def lit (s : String) : Term := .literal (Literal.string s)
private def ex : WfIri := ⟨"https://example.test/a", by decide⟩
private def sampleDict : Array Term :=
  #[lit "Water", lit "Underwater vehicle", lit "Glacier lagoon", .iri ex, lit "waterfall"]
private def sample : Artifact :=
  { targetIBKSha256 := ByteArray.mk (Array.replicate 32 7), index := build sampleDict }
private def sampleBytes : ByteArray := (encode? sample).getD ByteArray.empty
private def corrupt (bytes : ByteArray) : ByteArray :=
  if bytes.size == 0 then bytes else bytes.set! (bytes.size - 1) 0
private def wrongTarget : Artifact :=
  { sample with targetIBKSha256 := ByteArray.mk (Array.replicate 32 8) }
private def unsortedGrams : Artifact :=
  { sample with index := { sample.index with postings := sample.index.postings.reverse } }
private def outOfRange : Artifact :=
  { sample with index := { sample.index with dictCount := 0 } }

#guard supported sample
#guard sampleBytes.size > prefixBytes + crcBytes
#guard decode? sampleBytes == some sample
#guard decode? ((encode? wrongTarget).getD ByteArray.empty) == some wrongTarget
#guard (decode? (corrupt sampleBytes)).isNone
#guard (decode? (sampleBytes.extract 0 (sampleBytes.size - 1))).isNone
#guard (encode? unsortedGrams).isNone
#guard (encode? outOfRange).isNone
#guard (decodePrefix? (sampleBytes.extract 0 prefixBytes)).map Prefix.gramCount
  == some sample.index.postings.size
#guard ((decode? sampleBytes).map (fun a => candidates? a.index "water"))
  == some (candidatesSpec sampleDict "water")
#guard ((decode? sampleBytes).map (fun a => candidates? a.index "glacier"))
  == some (candidatesSpec sampleDict "glacier")

/-! ## LGI2 samples

The same fixture with an opaque list, through the version-2 codec. LGI1 bytes
are untouched: every `#guard` above still runs against `encode?`/`decode?`. -/

private def sample2 : Artifact :=
  { sample with index := { sample.index with opaqueIds := [3] } }
private def sample2Bytes : ByteArray := (encode2? sample2).getD ByteArray.empty
private def sample2NoOpaque : Artifact := sample
private def unsortedOpaque : Artifact :=
  { sample with index := { sample.index with opaqueIds := [3, 3] } }
private def outOfRangeOpaque : Artifact :=
  { sample with index := { sample.index with opaqueIds := [99] } }

#guard supported2 sample2
#guard decode2? sample2Bytes == some sample2
#guard decode2? ((encode2? sample2NoOpaque).getD ByteArray.empty) == some sample2NoOpaque
#guard (decode2? (corrupt sample2Bytes)).isNone
#guard (decode2? (sample2Bytes.extract 0 (sample2Bytes.size - 1))).isNone
#guard (encode2? unsortedOpaque).isNone
#guard (encode2? outOfRangeOpaque).isNone
-- LGI1 has no field for the opaque list, so it refuses an artifact with one.
#guard (encode? sample2).isNone
#guard supported sample
-- Neither decoder reads the other's bytes: the magic and the version differ.
#guard (decode? sample2Bytes).isNone
#guard (decode2? sampleBytes).isNone
#guard (decodePrefix2? (sample2Bytes.extract 0 prefixBytes2)).map Prefix2.opaqueCount == some 1
#guard prefixBytes2 == prefixBytes + 4
-- The candidate set of the decoded LGI2 index is the specification's union.
#guard ((decode2? sample2Bytes).map (fun a => candidatesOpaque? a.index "water"))
  == some (candidatesSpecOpaque sampleDict [3] "water")
#guard ((decode2? sample2Bytes).map (fun a => candidatesOpaque? a.index "bicycle"))
  == some (candidatesSpecOpaque sampleDict [3] "bicycle")
-- The varint. 127 is one byte, 128 is two, 16,383 is two, 16,384 is three.
#guard encodeLeb128 0 == [0]
#guard encodeLeb128 127 == [127]
#guard (encodeLeb128 128).length == 2
#guard (encodeLeb128 16383).length == 2
#guard (encodeLeb128 16384).length == 3
#guard (encodeLeb128 4294967295).length == 5
#guard decodeLeb128 (encodeLeb128 4294967295 ++ [9]) == some (4294967295, [9])
#guard decodeLeb128 (encodeLeb128 300) == some (300, [])
-- LGI2 is smaller than LGI1 on this fixture, which has small gaps.
#guard match encodedBytes1 sample, encodedBytes2 sample with
  | some one, some two => two < one
  | _, _ => false

#print axioms decodeLeb128_encodeLeb128
#print axioms parsePostings2_encodePostings2
#print axioms parsePostings2_postingRunBytes2

end L4Factoidal.Storage.LiteralGramIndexWire
