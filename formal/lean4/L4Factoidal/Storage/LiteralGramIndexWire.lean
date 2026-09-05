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

## What version 1 does not do

The gaps are fixed-width `u32`. On the SKOS `skos:prefLabel` block that is
3,018,141 bytes against a 5,571,302 byte block, 54%. A variable-length gap
encoding brings the same postings to roughly a third of that and is a version
2 decision, because it needs a round-trip theorem of its own.

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
    gramsAscending artifact.index.postings.toList

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

end L4Factoidal.Storage.LiteralGramIndexWire
