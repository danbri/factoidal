/-
L4Factoidal.HDT.Dictionary — the Plain Front Coding dictionary.

Port of `formal/fstar/HDT.Dictionary.fst` (519 lines). Stage 2 of the
HDT program plan, on top of `L4Factoidal.HDT.Container`'s section
boundaries. It turns the container skeleton into strings and then into
RDF terms:

- CRC8 (poly 0x07, init 0x00, unreflected, MSB-first) over every PFC
  and log-array preamble, and CRC32C Castagnoli (reflected 0x82F63B78,
  init and final xor 0xFFFFFFFF) over every log-array data payload and
  every packed-string block. Stage 1's CRC16 covers control blocks
  only, so these are the two flavours it does not reach.
- Log-array unpacking: entry `i` is `numbits` bits at bit offset
  `i * numbits`, LSB-first within the byte stream.
- PFC block decode: the first string of a block whole and NUL
  terminated, the rest as `vbyte(common-prefix-length) suffix NUL`.
  The block-start log-array has `⌈numstrings/blocksize⌉ + 1` entries —
  one per block plus a trailing sentinel equal to the packed-byte
  count.
- Both access patterns: `decodeSection` (full dump, for testing) and
  `pfcExtract` / `pfcLocate` (single ID lookup and reverse lookup by
  binary search over block heads).
- The four-section ID space: shared IDs 1..Nshared serve both the
  subject and object spaces, subject and object IDs continue at
  Nshared+1 into their own sections, predicates are a space of their
  own.
- Dictionary string ↔ `Term`: a `_:` prefix is a blank node, a `"`
  prefix is an N-Triples literal, anything else is an unbracketed IRI.

## Differences from the F* module

1. **`nat_sub` is gone.** The F* module defines a saturating
   subtraction because its offsets are `nat` and Z3 cannot re-derive
   the container invariants that keep them non-negative. Lean's `Nat`
   subtraction already truncates at zero, so `a - b` IS `nat_sub a b`.
2. **CRC registers are `UInt8` / `UInt32`, not `nat`.** The F* module
   works in unbounded naturals with `HC.nat_xor` because
   `FStar.UInt32`'s stdint externals have no js_of_ocaml realisation.
   Lean has the fixed-width operations as primitives.
3. **`bit_divisor` is `2 ^ shift`.** The F* module enumerates the
   eight cases to give Z3 a positive-literal divisor; Lean needs no
   such help.
4. **Front coding is done in BYTES, and this is a correction.**
   `pfc_read_suffix` in F* takes the common prefix with
   `FStar.String.sub prev 0 plen`, where `plen` is a count of BYTES
   from the file but `String.sub` counts CHARACTERS. The two agree on
   ASCII and diverge above 0x7F. `pfcReadSuffix` below splices the
   prefix and the suffix as `ByteArray`s and decodes the result, which
   is what the format specifies. Both vendored fixtures are pure ASCII
   in every dictionary section, so no test distinguishes the two yet.
-/
import L4Factoidal.HDT.Container
import L4Factoidal.Syntax.NTriples

namespace L4Factoidal.HDT

open L4Factoidal.RDF

/-! ## CRC8 — poly 0x07, init 0x00, unreflected (MSB-first)

Every PFC-section preamble and every log-array preamble carries one. -/

def crc8Step (c : UInt8) : UInt8 :=
  if (c >>> 7) &&& 1 == 1 then (c <<< 1) ^^^ 0x07 else c <<< 1

def crc8Byte (crc b : UInt8) : UInt8 :=
  let c0 := crc ^^^ b
  crc8Step (crc8Step (crc8Step (crc8Step
    (crc8Step (crc8Step (crc8Step (crc8Step c0)))))))

def crc8Range (a : Bytes) (pos count : Nat) (crc : UInt8) : Option UInt8 :=
  match count with
  | 0     => some crc
  | n + 1 =>
      match byteAt a pos with
      | none   => none
      | some b => crc8Range a (pos + 1) n (crc8Byte crc b)

/-! ## CRC32C (Castagnoli) — poly 0x1EDC6F41, reflected 0x82F63B78

Init 0xFFFFFFFF, final xor 0xFFFFFFFF. Every log-array data payload
and every packed-string block carries one. -/

def crc32cStep (c : UInt32) : UInt32 :=
  if c &&& 1 == 1 then (c >>> 1) ^^^ 0x82F63B78 else c >>> 1

def crc32cByte (crc : UInt32) (b : UInt8) : UInt32 :=
  let c0 := crc ^^^ b.toUInt32
  crc32cStep (crc32cStep (crc32cStep (crc32cStep
    (crc32cStep (crc32cStep (crc32cStep (crc32cStep c0)))))))

def crc32cRange (a : Bytes) (pos count : Nat) (crc : UInt32) : Option UInt32 :=
  match count with
  | 0     => some crc
  | n + 1 =>
      match byteAt a pos with
      | none   => none
      | some b => crc32cRange a (pos + 1) n (crc32cByte crc b)

def crc32cOfRange (a : Bytes) (pos count : Nat) : Option UInt32 :=
  (crc32cRange a pos count 0xFFFFFFFF).map (· ^^^ 0xFFFFFFFF)

/-! ## Stored CRC readers -/

def readU8 (a : Bytes) (pos : Nat) : Option UInt8 := byteAt a pos

def readU32LE (a : Bytes) (pos : Nat) : Option UInt32 := do
  let b0 ← byteAt a pos
  let b1 ← byteAt a (pos + 1)
  let b2 ← byteAt a (pos + 2)
  let b3 ← byteAt a (pos + 3)
  some (b0.toUInt32 ||| (b1.toUInt32 <<< 8) |||
        (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24))

/-! ## CRC validation over a decoded PFC section

Every checked range is located from stage 1's `LogArrayInfo` and
`PfcSection` offset records, never re-derived. -/

def laPreambleLen (la : LogArrayInfo) : Nat := (la.dataStart - 1) - la.start
def laPreambleCrc8Pos (la : LogArrayInfo) : Nat := la.dataStart - 1
def laCrc32Pos (la : LogArrayInfo) : Nat := la.end - 4

def laPreambleCrc8Ok (a : Bytes) (la : LogArrayInfo) : Bool :=
  match crc8Range a la.start (laPreambleLen la) 0, readU8 a (laPreambleCrc8Pos la) with
  | some c, some stored => c == stored
  | _, _ => false

def laDataCrc32Ok (a : Bytes) (la : LogArrayInfo) : Bool :=
  match crc32cOfRange a la.dataStart la.dataBytes, readU32LE a (laCrc32Pos la) with
  | some c, some stored => c == stored
  | _, _ => false

def pfcPreambleLen (sec : PfcSection) : Nat := (sec.blocks.start - 1) - sec.start
def pfcPreambleCrc8Pos (sec : PfcSection) : Nat := sec.blocks.start - 1

def pfcPreambleCrc8Ok (a : Bytes) (sec : PfcSection) : Bool :=
  match crc8Range a sec.start (pfcPreambleLen sec) 0, readU8 a (pfcPreambleCrc8Pos sec) with
  | some c, some stored => c == stored
  | _, _ => false

def pfcPackedCrc32Ok (a : Bytes) (sec : PfcSection) : Bool :=
  match crc32cOfRange a sec.packedStart sec.packedBytes, readU32LE a (sec.end - 4) with
  | some c, some stored => c == stored
  | _, _ => false

/-- All four CRCs a PFC section carries: its own preamble (CRC8), its
    block-start log-array's preamble (CRC8) and data (CRC32C), and its
    packed string bytes (CRC32C). -/
def pfcSectionCrcOk (a : Bytes) (sec : PfcSection) : Bool :=
  pfcPreambleCrc8Ok a sec && laPreambleCrc8Ok a sec.blocks &&
  laDataCrc32Ok a sec.blocks && pfcPackedCrc32Ok a sec

/-! ## Log-array unpacking

Entry `idx` is `numbits` bits starting at global bit offset
`idx * numbits` within the data range, LSB-first (bit 0 is the low bit
of the first data byte). -/

def laBitsAcc (a : Bytes) (dataStart bitpos : Nat) : Nat → Nat → Nat → Option Nat
  | 0,      _,    acc => some acc
  | n + 1,  mult, acc =>
      match byteNat a (dataStart + bitpos / 8) with
      | none   => none
      | some b =>
          let bitval := (b / (2 ^ (bitpos % 8))) % 2
          laBitsAcc a dataStart (bitpos + 1) n (mult * 2) (acc + bitval * mult)

/-- Entry `idx` (0-based), or `none` past the end of the data. -/
def laEntry (a : Bytes) (la : LogArrayInfo) (idx : Nat) : Option Nat :=
  laBitsAcc a la.dataStart (idx * la.numbits) la.numbits 1 0

/-- One entry per block plus a trailing sentinel equal to the total
    packed-byte count. -/
def pfcNumBlocks (sec : PfcSection) : Nat :=
  if sec.blocks.numentries == 0 then 0 else sec.blocks.numentries - 1

/-- Absolute byte offset of PFC block `b`. -/
def pfcBlockAbsStart (a : Bytes) (sec : PfcSection) (b : Nat) : Option Nat :=
  (laEntry a sec.blocks b).map (sec.packedStart + ·)

/-! ## Single-string decode -/

/-- Decode a `ByteArray` as text, UTF-8 first and per byte otherwise —
    the same convention as `Container.bytesToString`, over a byte range
    that has already been spliced. -/
def decodeBytes (bs : ByteArray) : String :=
  match String.fromUTF8? bs with
  | some s => s
  | none   => String.ofList (bs.toList.map (fun b => Char.ofNat b.toNat))

/-- The first (whole, NUL-terminated) string of a block. -/
def pfcReadFirst (a : Bytes) (pos : Nat) : Option (String × Nat) := do
  let nulPos ← scanNul a pos a.size
  let str ← bytesToString a pos (nulPos - pos)
  some (str, nulPos + 1)

/-- A front-coded entry: `vbyte(common-prefix-length) suffix NUL`. The
    prefix length counts BYTES (see difference 4 in the module
    header), so the splice is done on `ByteArray`s. -/
def pfcReadSuffix (a : Bytes) (pos : Nat) (prev : String) : Option (String × Nat) := do
  let (plen, p1) ← vbyteDecode a pos
  let prevBytes := prev.toUTF8
  if plen > prevBytes.size then none
  else do
    let nulPos ← scanNul a p1 a.size
    if nulPos > a.size then none
    else
      let suffix := a.extract p1 nulPos
      some (decodeBytes (prevBytes.extract 0 plen ++ suffix), nulPos + 1)

/-- Walk `remaining` suffix entries and return the LAST decoded. -/
def pfcWalkSuffixes (a : Bytes) (at' : Nat) (prev : String) : Nat → Option String
  | 0      => none
  | n + 1  =>
      match pfcReadSuffix a at' prev with
      | none => none
      | some (str, at'') => if n == 0 then some str else pfcWalkSuffixes a at'' str n

/-! ## Whole-block decode -/

def decodeBlockAcc (a : Bytes) (pos : Nat) (prev : String) :
    Nat → List String → Option (List String)
  | 0,     acc => some acc.reverse
  | n + 1, acc =>
      match pfcReadSuffix a pos prev with
      | none => none
      | some (str, pos') => decodeBlockAcc a pos' str n (str :: acc)

/-- Decode `count` strings (at least 1) of one block, from its
    absolute byte offset. -/
def decodeBlock (a : Bytes) (blockStart count : Nat) : Option (List String) :=
  match count with
  | 0     => none
  | n + 1 =>
      match pfcReadFirst a blockStart with
      | none => none
      | some (first, pos1) => decodeBlockAcc a pos1 first n [first]

/-! ## Full-section decode

For testing. `pfcExtract` and `pfcLocate` below are the lookup API.

The F* `decode_section_acc` appends with `acc @ strs`, which is
quadratic in the block count. This accumulates reversed and reverses
once. -/

def blockStringCount (sec : PfcSection) (numblocks b : Nat) : Nat :=
  if b + 1 == numblocks then sec.numstrings - (b * sec.blocksize) else sec.blocksize

def decodeSectionAcc (a : Bytes) (sec : PfcSection) (numblocks : Nat) :
    Nat → List String → Option (List String)
  | 0,     acc => some acc.reverse
  | n + 1, acc =>
      let blockIdx := numblocks - (n + 1)
      match pfcBlockAbsStart a sec blockIdx with
      | none => none
      | some bstart =>
          match decodeBlock a bstart (blockStringCount sec numblocks blockIdx) with
          | none => none
          | some strs => decodeSectionAcc a sec numblocks n (strs.reverse ++ acc)

/-- Every string of the section in ID order. ID `i` is at index
    `i - 1`. -/
def decodeSection (a : Bytes) (sec : PfcSection) : Option (List String) :=
  if sec.numstrings == 0 then some []
  else decodeSectionAcc a sec (pfcNumBlocks sec) (pfcNumBlocks sec) []

/-! ## Locate by ID — the single-lookup API. IDs are 1-based. -/

def pfcExtract (a : Bytes) (sec : PfcSection) (id : Nat) : Option String :=
  if id == 0 || id > sec.numstrings || sec.blocksize == 0 then none
  else
    let rank := id - 1
    let blockIdx := rank / sec.blocksize
    let offset := rank % sec.blocksize
    match pfcBlockAbsStart a sec blockIdx with
    | none => none
    | some bstart =>
        match pfcReadFirst a bstart with
        | none => none
        | some (first, pos1) =>
            if offset == 0 then some first else pfcWalkSuffixes a pos1 first offset

/-! ## Locate by string — reverse lookup

PFC blocks are stored in ascending order, so a predecessor search over
the block-head strings finds the block, then a linear scan finds the
string within it.

The order is the format's byte-wise order. Lean's `String` `<` compares
codepoint sequences; the two agree on ASCII and can differ above 0x7F,
where UTF-8 byte order and codepoint order part company for
surrogate-range-adjacent values. Both vendored fixtures are pure ASCII,
so nothing here distinguishes them yet — the same caveat as the front
coding above. -/

def pfcBlockFirstString (a : Bytes) (sec : PfcSection) (blockIdx : Nat) : Option String :=
  (pfcBlockAbsStart a sec blockIdx).bind (fun bstart =>
    (pfcReadFirst a bstart).map (·.1))

def pfcIndexOf (target : String) : List String → Nat → Option Nat
  | [],        _   => none
  | x :: rest, idx => if x == target then some idx else pfcIndexOf target rest (idx + 1)

/-- Largest block index in `[lo, hi]` whose first string is at most
    `target`. -/
def pfcFindBlock (a : Bytes) (sec : PfcSection) (target : String) (lo hi : Nat) :
    Option Nat :=
  if _h : lo ≥ hi then some lo
  else
    let mid := (lo + hi + 1) / 2
    match pfcBlockFirstString a sec mid with
    | none => none
    | some head =>
        if head == target || head < target then
          pfcFindBlock a sec target mid hi
        else
          pfcFindBlock a sec target lo (mid - 1)
  termination_by hi - lo
  decreasing_by
    · simp_wf; omega
    · simp_wf; omega

def pfcLocate (a : Bytes) (sec : PfcSection) (target : String) : Option Nat :=
  let numblocks := pfcNumBlocks sec
  if numblocks == 0 then none
  else
    match pfcFindBlock a sec target 0 (numblocks - 1) with
    | none => none
    | some blockIdx =>
        match pfcBlockAbsStart a sec blockIdx with
        | none => none
        | some bstart =>
            match decodeBlock a bstart (blockStringCount sec numblocks blockIdx) with
            | none => none
            | some strs =>
                (pfcIndexOf target strs 0).map (fun k => blockIdx * sec.blocksize + k + 1)

/-! ## Dictionary string ↔ `Term`

HDT stores terms in N-Triples surface syntax except that a plain IRI is
unbracketed; the leading byte tells the three cases apart. The grammar
comes from `Syntax.NTriples`, not from a second derivation here. -/

def termOfString (dstr : String) : Option Term :=
  let cs := dstr.toList
  match cs with
  | [] => none
  | '_' :: ':' :: _ =>
      match Syntax.readSubject 0 cs with
      | .ok (.bnode b, pos, _) => if pos == cs.length then some (.bnode b) else none
      | _ => none
  | '"' :: _ =>
      match Syntax.readLiteral .rdf11 0 cs with
      | .ok (l, pos, _) => if pos == cs.length then some (.literal l) else none
      | _ => none
  | _ => (Syntax.mkIri 0 dstr).toOption.map Term.iri

/-- The dictionary surface form of a term. `Syntax.Term.toNTriples` supplies
    the quoting and escaping for literals and blank nodes; an IRI is
    unbracketed here, unlike the `<iri>` that serialiser emits.

    The F* `hdt_string_of_term` is total because its serialiser is.
    Lean's returns `Except`, since an RDF 1.2 triple term or directional
    literal has no RDF 1.1 form — those cannot appear in an HDT v1
    dictionary, and the `none` says so rather than emitting something
    that would not parse back. -/
def stringOfTerm : Term → Option String
  | .iri i => some i.val
  | t      => (Syntax.Term.toNTriples .rdf11 t).toOption

/-! ## The four-section ID space

Shared IDs 1..Nshared serve both the subject and object spaces; subject
and object IDs continue at Nshared+1 into their own sections;
predicates are a separate space. -/

inductive Role where
  | subject | predicate | object
  deriving Repr, DecidableEq, Inhabited

def idToTerm (a : Bytes) (inv : Inventory) (role : Role) (id : Nat) : Option Term :=
  let nshared := inv.dictShared.numstrings
  let extracted := match role with
    | .predicate => pfcExtract a inv.dictPredicates id
    | .subject =>
        if id ≤ nshared then pfcExtract a inv.dictShared id
        else pfcExtract a inv.dictSubjects (id - nshared)
    | .object =>
        if id ≤ nshared then pfcExtract a inv.dictShared id
        else pfcExtract a inv.dictObjects (id - nshared)
  extracted.bind termOfString

def termToId (a : Bytes) (inv : Inventory) (role : Role) (term : Term) : Option Nat := do
  let dstr ← stringOfTerm term
  let nshared := inv.dictShared.numstrings
  match role with
  | .predicate => pfcLocate a inv.dictPredicates dstr
  | .subject =>
      match pfcLocate a inv.dictShared dstr with
      | some id => some id
      | none    => (pfcLocate a inv.dictSubjects dstr).map (nshared + ·)
  | .object =>
      match pfcLocate a inv.dictShared dstr with
      | some id => some id
      | none    => (pfcLocate a inv.dictObjects dstr).map (nshared + ·)

/-- Highest valid ID in a role's space — the loop bound for a
    full-space round-trip check. -/
def roleMaxId (inv : Inventory) (role : Role) : Nat :=
  let nshared := inv.dictShared.numstrings
  match role with
  | .predicate => inv.dictPredicates.numstrings
  | .subject   => nshared + inv.dictSubjects.numstrings
  | .object    => nshared + inv.dictObjects.numstrings

/-! ## Build-time checks

### CRC8 and CRC32C against their published check values

Both catalogue entries carry the CRC of the nine ASCII bytes
`123456789`: 0xF4 for CRC-8/SMBUS (poly 0x07, init 0x00, unreflected)
and 0xE3069283 for CRC-32/ISCSI (Castagnoli). Checking against those
checks the PARAMETERS, not the code's agreement with itself. -/

def crc8OfString (s : String) : Option UInt8 :=
  let bs : Bytes := ⟨s.toUTF8.data⟩
  crc8Range bs 0 bs.size 0

def crc32cOfString (s : String) : Option UInt32 :=
  let bs : Bytes := ⟨s.toUTF8.data⟩
  crc32cOfRange bs 0 bs.size

#guard crc8OfString "123456789" == some 0xF4
#guard crc32cOfString "123456789" == some 0xE3069283
#guard crc32cOfString "" == some 0

/-! ### Dictionary strings map to terms

The three leading-byte cases, and the rejections. A bracketed IRI is
NOT a dictionary string — HDT stores IRIs unbracketed, so `<x>` must
fail rather than silently produce the IRI `x`. -/

#guard termOfString "http://example.org/a" == some (.iri ⟨"http://example.org/a", by rfl⟩)
#guard (termOfString "_:b1").isSome
#guard (termOfString "\"t\"").isSome
#guard (termOfString "\"t\"@en").isSome
#guard (termOfString "\"1\"^^<http://www.w3.org/2001/XMLSchema#integer>").isSome
#guard (termOfString "").isNone


/-! ### And back, unbracketed for IRIs -/

#guard stringOfTerm (.iri ⟨"http://example.org/a", by rfl⟩) == some "http://example.org/a"
#guard stringOfTerm (.bnode "b1") == some "_:b1"

/-! ### The round trip on every form the dictionary can hold -/

def dictRoundTrips (s : String) : Bool :=
  match termOfString s with
  | none   => false
  | some t => stringOfTerm t == some s

#guard dictRoundTrips "http://example.org/a"
#guard dictRoundTrips "_:b1"
#guard dictRoundTrips "\"t\""
#guard dictRoundTrips "\"t\"@en"
#guard dictRoundTrips "\"1\"^^<http://www.w3.org/2001/XMLSchema#integer>"

/-! A BRACKETED IRI is not rejected, and that is the F* module's
    behaviour too. `isIri` (port of `RDF.Term.is_iri`) is the minimal
    gate the whole tree applies — non-empty and contains a colon — so
    `<x:y>` reads as an IRI whose text carries the brackets. hdt-cpp
    never writes one, and the round trip below still holds for it, so
    this is recorded rather than guarded against. -/

#guard termOfString "<http://example.org/a>"
        == some (.iri ⟨"<http://example.org/a>", by rfl⟩)
#guard dictRoundTrips "<http://example.org/a>"

/-! ### String order is the one the block search assumes -/

#guard "a" < "b"
#guard "ab" < "b"
#guard !("b" < "ab")
#guard !("a" < "a")

end L4Factoidal.HDT
